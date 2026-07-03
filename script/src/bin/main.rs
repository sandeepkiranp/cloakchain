//! CloakChain IVC orchestrator — Noir/bb backend.
//!
//! Drives the full proving chain:
//!   coinproof_base (slot 0) → coinproof_step (slot 1, receipt) → spend (bob → carol)
//!
//! Requires nargo and bb to be on $PATH.
//! Run from the workspace root: `cargo run --release`

use std::path::Path;
use std::process::Command;
use std::time::Instant;

use blake2::{Blake2s256, Digest};
use cloakkchain_lib::{
    append_proof_for, build_note_enc, ciphertext_hash, derive_pk,
    encrypt_tx,
    BoardEntry, Coin, Transaction, EK_SALT, GENESIS_SK,
};
use sha2::Sha256;

// ── circuit names ────────────────────────────────────────────────────────────

const TARGET: &str = "noir-recursive-no-zk";
const VK_FIELDS:    usize = 115;
const PROOF_FIELDS: usize = 457;

// ── TOML formatting helpers ───────────────────────────────────────────────────

fn b32(b: &[u8; 32]) -> String {
    let parts: Vec<String> = b.iter().map(|x| format!("\"0x{x:02x}\"")).collect();
    format!("[{}]", parts.join(", "))
}

fn b32_arr(bs: &[[u8; 32]]) -> String {
    let parts: Vec<String> = bs.iter().map(|b| b32(b)).collect();
    format!("[{}]", parts.join(", "))
}

fn b32_pad8(bs: &[[u8; 32]]) -> String {
    let mut padded = [[0u8; 32]; 8];
    for (i, b) in bs.iter().take(8).enumerate() { padded[i] = *b; }
    b32_arr(&padded)
}

fn b32_pad32(bs: &[[u8; 32]]) -> String {
    let mut padded = [[0u8; 32]; 32];
    for (i, b) in bs.iter().take(32).enumerate() { padded[i] = *b; }
    b32_arr(&padded)
}

fn u64hex(x: u64) -> String { format!("\"0x{x:016x}\"") }

fn fhex(b: &[u8; 32]) -> String { format!("\"0x{}\"", hex::encode(b)) }

fn farr(fields: &[[u8; 32]]) -> String {
    let parts: Vec<String> = fields.iter().map(|f| fhex(f)).collect();
    format!("[{}]", parts.join(", "))
}

fn boolstr(b: bool) -> &'static str { if b { "true" } else { "false" } }

fn vals8(vs: &[u64]) -> String {
    let mut a = [0u64; 8];
    for (i, v) in vs.iter().take(8).enumerate() { a[i] = *v; }
    let parts: Vec<String> = a.iter().map(|v| u64hex(*v)).collect();
    format!("[{}]", parts.join(", "))
}

// ── Crypto ───────────────────────────────────────────────────────────────────

fn blake2s_pair(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32] {
    let mut buf = [0u8; 64];
    buf[..32].copy_from_slice(a);
    buf[32..].copy_from_slice(b);
    Blake2s256::digest(buf).into()
}

/// Spending nullifier = Blake2s(coin_commitment || sk_p). Matches circuits.
fn spend_nullifier(cn: &[u8; 32], sk: &[u8; 32]) -> [u8; 32] {
    blake2s_pair(cn, sk)
}

/// Transaction input_nullifier. Matches make_tx() convention below.
/// Uses Blake2s (same as circuits) NOT Sha256 (old SP1 script had sha256 bug).
fn tx_input_nullifier(primary_cn: &[u8; 32], sender_sk: &[u8; 32]) -> [u8; 32] {
    blake2s_pair(primary_cn, sender_sk)
}

/// Coinproof state hash — must match state_hash() in both coinproof circuits.
/// Layout (147 bytes): owner_pk(32)|coin_cn(32)|board_root(32)|board_size_le8(8)|
///   rcv_valid(1)|rcv_at_le8(8)|spent(1)|parent_null(32)|parent_null_seen(1)
fn cp_state_hash(
    owner_pk: &[u8; 32], cn: &[u8; 32], board_root: &[u8; 32],
    board_size: u64, rcv_valid: bool, rcv_at: u64,
    spent: bool, parent_null: &[u8; 32], parent_null_seen: bool,
) -> [u8; 32] {
    let mut buf = [0u8; 147];
    buf[..32].copy_from_slice(owner_pk);
    buf[32..64].copy_from_slice(cn);
    buf[64..96].copy_from_slice(board_root);
    buf[96..104].copy_from_slice(&board_size.to_le_bytes());
    buf[104] = u8::from(rcv_valid);
    buf[105..113].copy_from_slice(&rcv_at.to_le_bytes());
    buf[113] = u8::from(spent);
    buf[114..146].copy_from_slice(parent_null);
    buf[146] = u8::from(parent_null_seen);
    Blake2s256::digest(buf).into()
}

// ── Coin state ────────────────────────────────────────────────────────────────

#[derive(Clone, Debug)]
struct CoinState {
    board_root:       [u8; 32],
    board_size:       u64,
    rcv_valid:        bool,
    rcv_at:           u64,
    spent:            bool,
    parent_null:      [u8; 32],
    parent_null_seen: bool,
}

impl CoinState {
    fn hash(&self, owner_pk: &[u8; 32], cn: &[u8; 32]) -> [u8; 32] {
        cp_state_hash(owner_pk, cn, &self.board_root,
            self.board_size, self.rcv_valid, self.rcv_at,
            self.spent, &self.parent_null, self.parent_null_seen)
    }
}

/// Simulate coinproof_base: returns the expected CoinState after slot 0.
fn coinproof_base_state(
    _owner_pk: &[u8; 32], cn: &[u8; 32],
    entry: &BoardEntry, entries_so_far: &[BoardEntry],
    parent_null: &[u8; 32], own_null: &[u8; 32],
) -> (CoinState, bool) {
    let path = append_proof_for(entries_so_far);
    let leaf = cloakkchain_lib::merkle_leaf(0, entry);
    let new_root = cloakkchain_lib::compute_root_from_path(leaf, 0, &path);

    let coin_in = entry.output_commitments.contains(cn);
    let parent_null_seen = entry.nullifier == *parent_null;
    let spent = entry.nullifier == *own_null;

    let state = CoinState {
        board_root: new_root, board_size: 1,
        rcv_valid: coin_in, rcv_at: 0,
        spent, parent_null: *parent_null, parent_null_seen,
    };
    (state, coin_in)
}

/// Simulate coinproof_step: returns the expected CoinState after slot `slot`.
fn coinproof_step_state(
    cn: &[u8; 32], slot: usize,
    entry: &BoardEntry, entries_so_far: &[BoardEntry],
    parent_null: &[u8; 32], own_null: &[u8; 32],
    inner: &CoinState,
) -> (CoinState, bool) {
    let path = append_proof_for(entries_so_far);
    let leaf = cloakkchain_lib::merkle_leaf(slot, entry);
    let new_root = cloakkchain_lib::compute_root_from_path(leaf, slot, &path);

    let coin_in = entry.output_commitments.contains(cn);
    let is_receipt = coin_in && !inner.rcv_valid && !inner.parent_null_seen;

    let parent_null_seen = inner.parent_null_seen
        || (!inner.rcv_valid && entry.nullifier == *parent_null);
    let spent = inner.spent || (entry.nullifier == *own_null);
    let rcv_valid = inner.rcv_valid || is_receipt;
    let rcv_at = if is_receipt && !inner.rcv_valid { slot as u64 } else { inner.rcv_at };

    let state = CoinState {
        board_root: new_root, board_size: slot as u64 + 1,
        rcv_valid, rcv_at, spent, parent_null: *parent_null, parent_null_seen,
    };
    (state, is_receipt)
}

// ── Proof artifact I/O ────────────────────────────────────────────────────────

/// Read `n` 32-byte field elements (big-endian) from a bb binary file.
fn read_fields(path: &Path, n: usize) -> Vec<[u8; 32]> {
    let data = std::fs::read(path)
        .unwrap_or_else(|e| panic!("read {path:?}: {e}"));
    assert!(data.len() >= n * 32, "{path:?}: expected ≥{} bytes, got {}", n*32, data.len());
    (0..n).map(|i| {
        let mut f = [0u8; 32];
        f.copy_from_slice(&data[i*32..(i+1)*32]);
        f
    }).collect()
}

/// Read a 32-byte VK hash (binary or hex string).
fn read_vk_hash(path: &Path) -> [u8; 32] {
    let raw = std::fs::read(path)
        .unwrap_or_else(|e| panic!("read {path:?}: {e}"));
    if raw.len() == 32 {
        let mut out = [0u8; 32]; out.copy_from_slice(&raw); return out;
    }
    let s = String::from_utf8_lossy(&raw).trim().to_string();
    let hex_str = s.strip_prefix("0x").unwrap_or(&s);
    let v = hex::decode(hex_str)
        .unwrap_or_else(|e| panic!("vk_hash decode {path:?}: {e}"));
    assert_eq!(v.len(), 32, "vk_hash must be 32 bytes");
    let mut out = [0u8; 32]; out.copy_from_slice(&v); out
}

/// Read the state_hash [u8;32] from a coinproof public_inputs file.
/// Layout: [0..32] owner_pk | [32..64] cn | [64] slot | [65..97] parent_null | [97..129] state_hash
/// Each field element is 32 bytes BE; u8 byte value is in the last byte.
fn read_state_hash(path: &Path) -> [u8; 32] {
    let data = std::fs::read(path)
        .unwrap_or_else(|e| panic!("read public_inputs {path:?}: {e}"));
    let mut sh = [0u8; 32];
    for i in 0..32 {
        sh[i] = data[(97 + i) * 32 + 31];
    }
    sh
}

// ── Shell-out helpers ─────────────────────────────────────────────────────────

fn run(program: &str, args: &[&str], cwd: &Path) {
    let out = Command::new(program)
        .args(args)
        .current_dir(cwd)
        .output()
        .unwrap_or_else(|e| panic!("{program} failed to start: {e}"));
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    if !stdout.trim().is_empty() { print!("{stdout}"); }
    if !out.status.success() {
        panic!("{program} {} failed:\n{stderr}", args.join(" "));
    }
}

fn do_nargo_execute(cwd: &Path) { run("nargo", &["execute"], cwd); }

fn do_bb_write_vk(cwd: &Path, json: &str) {
    let b = format!("target/{json}.json");
    run("bb", &["write_vk", "-b", &b, "-o", "target/vk", "-t", TARGET], cwd);
}

fn do_bb_prove(cwd: &Path, json: &str, witness: &str) {
    let b = format!("target/{json}.json");
    let w = format!("target/{witness}.gz");
    run("bb", &["prove", "-b", &b, "-w", &w, "-k", "target/vk/vk", "-o", "target/proof", "-t", TARGET], cwd);
}

fn do_bb_verify(cwd: &Path) {
    run("bb", &["verify", "-k", "target/vk/vk", "-i", "target/proof/public_inputs",
                "-p", "target/proof/proof", "-t", TARGET], cwd);
}

// ── Prover.toml generators ────────────────────────────────────────────────────

fn coinproof_base_toml(
    owner_pk: &[u8; 32], cn: &[u8; 32],
    entry: &BoardEntry, path: &[[u8; 32]],
    parent_null: &[u8; 32], own_null: &[u8; 32],
    is_receipt: bool,
) -> String {
    let ct = ciphertext_hash(entry);
    let num_out = entry.output_commitments.len().min(8) as u64;
    format!(
        "owner_pk = {op}\n\
         coin_commitment = {cn}\n\
         slot = {sl}\n\
         parent_nullifier = {pn}\n\
         entry_output_commitments = {oc}\n\
         entry_num_outputs = {no}\n\
         entry_nullifier = {en}\n\
         entry_ciphertext_hash = {ct}\n\
         own_nullifier = {on}\n\
         append_path = {ap}\n\
         is_receipt_hint = {ir}\n",
        op = b32(owner_pk), cn = b32(cn), sl = u64hex(0),
        pn = b32(parent_null),
        oc = b32_pad8(&entry.output_commitments),
        no = u64hex(num_out),
        en = b32(&entry.nullifier), ct = b32(&ct),
        on = b32(own_null), ap = b32_pad32(path),
        ir = boolstr(is_receipt),
    )
}

fn coinproof_step_toml(
    owner_pk: &[u8; 32], cn: &[u8; 32], slot: u64,
    entry: &BoardEntry, path: &[[u8; 32]],
    parent_null: &[u8; 32], own_null: &[u8; 32],
    inner: &CoinState, inner_sh: &[u8; 32],
    inner_vk: &[[u8; 32]], inner_proof: &[[u8; 32]], inner_vk_hash: &[u8; 32],
    is_receipt: bool,
) -> String {
    let ct = ciphertext_hash(entry);
    let num_out = entry.output_commitments.len().min(8) as u64;
    format!(
        "owner_pk = {op}\n\
         coin_commitment = {cn}\n\
         slot = {sl}\n\
         entry_output_commitments = {oc}\n\
         entry_num_outputs = {no}\n\
         entry_nullifier = {en}\n\
         entry_ciphertext_hash = {ct}\n\
         append_path = {ap}\n\
         parent_nullifier = {pn}\n\
         own_nullifier = {on}\n\
         inner_vk = {ivk}\n\
         inner_proof = {ip}\n\
         inner_vk_hash = {ivkh}\n\
         inner_state_hash = {ish}\n\
         inner_owner_pk = {iop}\n\
         inner_coin_commitment = {icn}\n\
         inner_board_root = {ibr}\n\
         inner_board_size = {ibs}\n\
         inner_received_at_valid = {irv}\n\
         inner_received_at = {ira}\n\
         inner_spent = {isp}\n\
         inner_parent_nullifier = {ipn}\n\
         inner_parent_nullifier_seen = {ipns}\n\
         is_receipt_hint = {ir}\n",
        op = b32(owner_pk), cn = b32(cn), sl = u64hex(slot),
        oc = b32_pad8(&entry.output_commitments),
        no = u64hex(num_out),
        en = b32(&entry.nullifier), ct = b32(&ct),
        ap = b32_pad32(path), pn = b32(parent_null), on = b32(own_null),
        ivk = farr(inner_vk), ip = farr(inner_proof), ivkh = fhex(inner_vk_hash),
        ish = b32(inner_sh),
        iop = b32(owner_pk), icn = b32(cn),
        ibr = b32(&inner.board_root), ibs = u64hex(inner.board_size),
        irv = boolstr(inner.rcv_valid), ira = u64hex(inner.rcv_at),
        isp = boolstr(inner.spent), ipn = b32(parent_null),
        ipns = boolstr(inner.parent_null_seen),
        ir = boolstr(is_receipt),
    )
}

fn spend_toml(
    sk_p: &[u8; 32], pk_p: &[u8; 32],
    cn_in: &[u8; 32], board_root: &[u8; 32], input_null: &[u8; 32],
    in_coins: &[Coin], out_coins: &[Coin],
    tx_in_cns: &[[u8; 32]], tx_out_cns: &[[u8; 32]],
    is_genesis: bool,
    cp_vk: Option<&[[u8; 32]]>, cp_proof: Option<&[[u8; 32]]>,
    cp_vk_hash: Option<&[u8; 32]>, cp_slot: u64,
    cp_state: Option<&CoinState>, cp_sh: Option<&[u8; 32]>,
    cp_owner_pk: &[u8; 32], cp_cn: &[u8; 32],
) -> String {
    let z32 = [0u8; 32];
    let has_cp = cp_vk.is_some();
    let zvk   = vec![[0u8; 32]; VK_FIELDS];
    let zpr   = vec![[0u8; 32]; PROOF_FIELDS];
    let zero_state = CoinState {
        board_root: z32, board_size: 0, rcv_valid: false, rcv_at: 0,
        spent: false, parent_null: z32, parent_null_seen: false,
    };
    let vk  = cp_vk.unwrap_or(&zvk);
    let prf = cp_proof.unwrap_or(&zpr);
    let vkh = cp_vk_hash.unwrap_or(&z32);
    let cs  = cp_state.unwrap_or(&zero_state);
    let csh = cp_sh.unwrap_or(&z32);

    let in_tags:   Vec<[u8;32]> = pad8_coins_tag(in_coins);
    let in_vals:   Vec<u64>     = pad8_coins_val(in_coins);
    let in_rands:  Vec<[u8;32]> = pad8_coins_rand(in_coins);
    let in_owners: Vec<[u8;32]> = pad8_coins_owner(in_coins);
    let out_tags:   Vec<[u8;32]> = pad8_coins_tag(out_coins);
    let out_vals:   Vec<u64>     = pad8_coins_val(out_coins);
    let out_rands:  Vec<[u8;32]> = pad8_coins_rand(out_coins);
    let out_owners: Vec<[u8;32]> = pad8_coins_owner(out_coins);

    format!(
        "sk_p = {sk}\n\
         pk_p = {pk}\n\
         coin_commitment_in = {ci}\n\
         board_root = {br}\n\
         input_nullifier = {inl}\n\
         input_tags = {itag}\n\
         input_values = {ival}\n\
         input_rands = {ird}\n\
         input_owner_pks = {iop}\n\
         num_inputs = {ni}\n\
         output_tags = {otag}\n\
         output_values = {oval}\n\
         output_rands = {ord}\n\
         output_owner_pks = {oop}\n\
         num_outputs = {no}\n\
         tx_input_commitments = {txin}\n\
         tx_output_commitments = {txout}\n\
         is_genesis = {ig}\n\
         has_coin_proof = {hcp}\n\
         coinproof_vk = {cvk}\n\
         coinproof_proof = {cprf}\n\
         coinproof_vk_hash = {cvkh}\n\
         cp_slot = {csl}\n\
         cp_state_hash = {csh}\n\
         cp_owner_pk = {cop}\n\
         cp_coin_commitment = {ccn}\n\
         cp_board_root = {cbr}\n\
         cp_board_size = {cbs}\n\
         cp_received_at_valid = {crv}\n\
         cp_received_at = {cra}\n\
         cp_spent = {csp}\n\
         cp_parent_nullifier = {cpn}\n\
         cp_parent_nullifier_seen = {cpns}\n",
        sk = b32(sk_p), pk = b32(pk_p),
        ci = b32(cn_in), br = b32(board_root), inl = b32(input_null),
        itag = b32_arr(&in_tags), ival = vals8(&in_vals),
        ird  = b32_arr(&in_rands), iop = b32_arr(&in_owners),
        ni = u64hex(in_coins.len().min(8) as u64),
        otag = b32_arr(&out_tags), oval = vals8(&out_vals),
        ord  = b32_arr(&out_rands), oop = b32_arr(&out_owners),
        no = u64hex(out_coins.len().min(8) as u64),
        txin = b32_pad8(tx_in_cns), txout = b32_pad8(tx_out_cns),
        ig = boolstr(is_genesis), hcp = boolstr(has_cp),
        cvk = farr(vk), cprf = farr(prf), cvkh = fhex(vkh),
        csl = u64hex(cp_slot),
        csh = b32(csh), cop = b32(cp_owner_pk), ccn = b32(cp_cn),
        cbr = b32(&cs.board_root), cbs = u64hex(cs.board_size),
        crv = boolstr(cs.rcv_valid), cra = u64hex(cs.rcv_at),
        csp = boolstr(cs.spent), cpn = b32(&cs.parent_null),
        cpns = boolstr(cs.parent_null_seen),
    )
}

// Helper pads for coin field extraction
fn pad8_coins_tag(coins: &[Coin])   -> Vec<[u8;32]> { pad8(coins, |c| c.tag) }
fn pad8_coins_rand(coins: &[Coin])  -> Vec<[u8;32]> { pad8(coins, |c| c.rand) }
fn pad8_coins_owner(coins: &[Coin]) -> Vec<[u8;32]> { pad8(coins, |c| c.owner_pk) }
fn pad8_coins_val(coins: &[Coin])   -> Vec<u64>     { (0..8).map(|i| coins.get(i).map_or(0, |c| c.value)).collect() }
fn pad8<T: Default + Copy>(coins: &[Coin], f: fn(&Coin) -> T) -> Vec<T> {
    (0..8).map(|i| coins.get(i).map_or(T::default(), |c| f(c))).collect()
}

// ── Coin / transaction builders ───────────────────────────────────────────────

fn coin(seed: u8, value: u64, owner_pk: [u8; 32]) -> Coin {
    let mut tag = [0u8; 32];  tag[0] = seed;
    let mut rand = [0u8; 32]; rand[1] = seed;
    Coin { tag, value, rand, owner_pk }
}

fn make_tx(
    id: u64, sender_sk: [u8; 32],
    input_coins: &[Coin], outputs: &[(Coin, [u8; 32])],
) -> (Transaction, [u8; 32], Vec<[u8; 32]>) {
    // Deterministic session key: Sha256(sender_sk || id || EK_SALT)
    let session_key: [u8; 32] = {
        let mut h = Sha256::new();
        h.update(sender_sk);
        h.update((id as u64).to_le_bytes());
        h.update(EK_SALT);
        h.finalize().into()
    };
    let input_commitments: Vec<[u8; 32]>  = input_coins.iter().map(|c| c.commitment()).collect();
    let recipient_pks: Vec<[u8; 32]>      = outputs.iter().map(|(_, pk)| *pk).collect();
    let output_commitments: Vec<[u8; 32]> = outputs.iter().map(|(c, _)| c.commitment()).collect();
    let note_encs: Vec<Vec<u8>>           = outputs.iter().enumerate()
        .map(|(i, (c, _))| build_note_enc(&session_key, i, c)).collect();
    let input_nullifier = tx_input_nullifier(&input_commitments[0], &sender_sk);
    let tx = Transaction {
        id, input_commitments, output_commitments, note_encs,
        input_nullifier, spend_proof: vec![],
    };
    (tx, session_key, recipient_pks)
}

// ── Stats ─────────────────────────────────────────────────────────────────────

struct StepStats {
    label:      String,
    user:       String,
    board_size: usize,
    exec_s:     f64,
    prove_s:    f64,
    verify_s:   f64,
}

fn print_stats(stats: &[StepStats]) {
    let w = 74;
    println!("\n{}", "=".repeat(w));
    println!("  Proof Statistics");
    println!("{}", "=".repeat(w));
    println!("{:<36} {:>5}  {:<12}  {:>7}  {:>7}  {:>7}",
        "Step", "Board", "User", "Execute", "Prove", "Verify");
    println!("{}", "-".repeat(w));
    let (mut tp, mut tv) = (0f64, 0f64);
    for s in stats {
        println!("{:<36} {:>5}  {:<12}  {:>6.1}s  {:>6.1}s  {:>6.1}s",
            s.label, s.board_size, s.user, s.exec_s, s.prove_s, s.verify_s);
        tp += s.prove_s;
        tv += s.verify_s;
    }
    println!("{}", "-".repeat(w));
    println!("{:<36} {:>5}  {:<12}  {:>7}  {:>6.1}s  {:>6.1}s",
        "TOTAL", "", "", "", tp, tv);
    println!("{}", "=".repeat(w));
}

// ── Full proving flow ─────────────────────────────────────────────────────────

fn write_toml(dir: &Path, content: &str) {
    let path = dir.join("Prover.toml");
    std::fs::write(&path, content)
        .unwrap_or_else(|e| panic!("write {path:?}: {e}"));
}

fn secs(t: Instant) -> f64 { t.elapsed().as_secs_f64() }

fn main() {
    let ws = std::env::current_dir().expect("cwd");
    let cp_base_dir  = ws.join("circuits/coinproof_base");
    let cp_step_dir  = ws.join("circuits/coinproof");
    let spend_dir    = ws.join("circuits/spend");

    let alice   = Party::new("alice",   1);
    let bob     = Party::new("bob",     2);
    let carol   = Party::new("carol",   3);
    let genesis = Party { name: "genesis", sk: GENESIS_SK, pk: derive_pk(&GENESIS_SK) };

    // Coins
    let genesis_coin  = coin(0xA1, 100, genesis.pk);
    let alice_coin    = coin(0xA2, 100, alice.pk);
    let bob_coin      = coin(0xB1,  40, bob.pk);
    let alice_change  = coin(0xB2,  60, alice.pk);
    let carol_coin    = coin(0xC1,  40, carol.pk);

    let _cn_genesis = genesis_coin.commitment();
    let cn_alice   = alice_coin.commitment();
    let cn_bob     = bob_coin.commitment();
    let cn_carol   = carol_coin.commitment();

    // ── Build the 2-entry board ────────────────────────────────────────────
    println!("\n=== Building demo board ===");

    // Entry 0: genesis mints 100 to alice
    let (tx0, s0, r0) = make_tx(0, GENESIS_SK,
        &[genesis_coin.clone()], &[(alice_coin.clone(), alice.pk)]);
    let entry0 = encrypt_tx(&tx0, &r0, s0);

    // Entry 1: alice sends 40 to bob + 60 change to herself
    let (tx1, s1, r1) = make_tx(1, alice.sk,
        &[alice_coin.clone()], &[(bob_coin.clone(), bob.pk), (alice_change.clone(), alice.pk)]);
    let entry1 = encrypt_tx(&tx1, &r1, s1);

    let entries = vec![entry0.clone(), entry1.clone()];

    println!("entry[0] output_commitments: {} coins", entry0.output_commitments.len());
    println!("  [0] = {} (alice_coin)", hex2(&cn_alice));
    println!("entry[1] output_commitments: {} coins", entry1.output_commitments.len());
    println!("  [0] = {} (bob_coin)", hex2(&cn_bob));
    println!("  [1] = {} (alice_change)", hex2(&alice_coin.commitment()));

    // Nullifiers
    let alice_null = tx_input_nullifier(&cn_alice, &alice.sk);
    let bob_null   = spend_nullifier(&cn_bob,   &bob.sk);

    // For bob's coinproof, parent_nullifier = alice's tx input_nullifier
    // (the nullifier that appears in entry[1], where bob's coin is received).
    let bob_parent_null = alice_null;

    let mut stats: Vec<StepStats> = Vec::new();

    // ── VK generation ─────────────────────────────────────────────────────
    println!("\n=== Generating VKs ===");

    let circuits = [
        ("coinproof_base", &cp_base_dir as &std::path::PathBuf, "coinproof_base"),
        ("coinproof_step", &cp_step_dir, "coinproof"),
        ("spend",          &spend_dir,   "spend"),
    ];
    for (label, dir, json) in &circuits {
        print!("  {label} write_vk... ");
        let t = Instant::now();
        do_bb_write_vk(dir, json);
        let vk_s = secs(t);
        println!("done ({vk_s:.1}s)");
        stats.push(StepStats {
            label: format!("VK: {label}"),
            user: "-".into(), board_size: 0,
            exec_s: 0.0, prove_s: vk_s, verify_s: 0.0,
        });
    }

    // ── coinproof_base (slot 0): bob tracking entry[0] ────────────────────
    println!("\n=== coinproof_base: bob tracking slot 0 ===");

    let entries_0 = &entries[..1];
    let path_0 = append_proof_for(entries_0);
    let (base_state, base_receipt) = coinproof_base_state(
        &bob.pk, &cn_bob, &entry0, entries_0, &bob_parent_null, &bob_null,
    );
    println!("  rcv_valid={} spent={} parent_null_seen={} receipt={}",
        base_state.rcv_valid, base_state.spent, base_state.parent_null_seen, base_receipt);

    write_toml(&cp_base_dir, &coinproof_base_toml(
        &bob.pk, &cn_bob, &entry0, &path_0,
        &bob_parent_null, &bob_null, base_receipt,
    ));

    print!("  nargo execute... "); let t = Instant::now();
    do_nargo_execute(&cp_base_dir);
    let base_exec_s = secs(t); println!("done ({base_exec_s:.1}s)");

    print!("  bb prove...      "); let t = Instant::now();
    do_bb_prove(&cp_base_dir, "coinproof_base", "coinproof_base");
    let base_prove_s = secs(t); println!("done ({base_prove_s:.1}s)");

    print!("  bb verify...     "); let t = Instant::now();
    do_bb_verify(&cp_base_dir);
    let base_verify_s = secs(t); println!("✓ ({base_verify_s:.2}s)");

    let base_sh_actual = read_state_hash(&cp_base_dir.join("target/proof/public_inputs"));
    let base_sh_computed = base_state.hash(&bob.pk, &cn_bob);
    if base_sh_actual != base_sh_computed {
        println!("  WARNING: base state_hash mismatch — using circuit output");
    } else {
        println!("  ✓ state_hash matches");
    }
    stats.push(StepStats {
        label: "coinproof_base (slot 0)".into(), user: "bob".into(), board_size: 1,
        exec_s: base_exec_s, prove_s: base_prove_s, verify_s: base_verify_s,
    });

    let base_vk      = read_fields(&cp_base_dir.join("target/vk/vk"),      VK_FIELDS);
    let base_proof   = read_fields(&cp_base_dir.join("target/proof/proof"), PROOF_FIELDS);
    let base_vk_hash = read_vk_hash(&cp_base_dir.join("target/vk/vk_hash"));

    // ── coinproof_step (slot 1): bob receives bob_coin ─────────────────────
    println!("\n=== coinproof_step: bob receiving at slot 1 ===");

    let entries_1 = &entries[..2];
    let path_1 = append_proof_for(entries_1);
    let (step_state, step_receipt) = coinproof_step_state(
        &cn_bob, 1, &entry1, entries_1, &bob_parent_null, &bob_null, &base_state,
    );
    println!("  rcv_valid={} rcv_at={} spent={} parent_null_seen={} receipt={}",
        step_state.rcv_valid, step_state.rcv_at, step_state.spent,
        step_state.parent_null_seen, step_receipt);
    assert!(step_receipt, "bob should receive bob_coin at slot 1");

    write_toml(&cp_step_dir, &coinproof_step_toml(
        &bob.pk, &cn_bob, 1, &entry1, &path_1,
        &bob_parent_null, &bob_null,
        &base_state, &base_sh_actual,
        &base_vk, &base_proof, &base_vk_hash,
        step_receipt,
    ));

    print!("  nargo execute... "); let t = Instant::now();
    do_nargo_execute(&cp_step_dir);
    let step_exec_s = secs(t); println!("done ({step_exec_s:.1}s)");

    print!("  bb prove...      "); let t = Instant::now();
    do_bb_prove(&cp_step_dir, "coinproof", "coinproof");
    let step_prove_s = secs(t); println!("done ({step_prove_s:.1}s)");

    print!("  bb verify...     "); let t = Instant::now();
    do_bb_verify(&cp_step_dir);
    let step_verify_s = secs(t); println!("✓ ({step_verify_s:.2}s)");

    let step_sh_actual = read_state_hash(&cp_step_dir.join("target/proof/public_inputs"));
    if step_sh_actual != step_state.hash(&bob.pk, &cn_bob) {
        println!("  WARNING: step state_hash mismatch — using circuit output");
    } else {
        println!("  ✓ state_hash matches");
    }
    stats.push(StepStats {
        label: "coinproof_step (slot 1, receipt)".into(), user: "bob".into(), board_size: 2,
        exec_s: step_exec_s, prove_s: step_prove_s, verify_s: step_verify_s,
    });

    // ── spend (bob → carol) ────────────────────────────────────────────────
    println!("\n=== spend: bob → carol ===");

    let board_root = cloakkchain_lib::merkle_root_of(entries_1);
    assert_eq!(board_root, step_state.board_root, "board_root must match coinproof_step");

    let step_vk      = read_fields(&cp_step_dir.join("target/vk/vk"),      VK_FIELDS);
    let step_proof   = read_fields(&cp_step_dir.join("target/proof/proof"), PROOF_FIELDS);
    let step_vk_hash = read_vk_hash(&cp_step_dir.join("target/vk/vk_hash"));

    let bob_spend_null = spend_nullifier(&cn_bob, &bob.sk);
    let tx_in_cns  = [cn_bob];
    let tx_out_cns = [cn_carol];

    write_toml(&spend_dir, &spend_toml(
        &bob.sk, &bob.pk, &cn_bob, &board_root, &bob_spend_null,
        &[bob_coin.clone()], &[carol_coin.clone()],
        &tx_in_cns, &tx_out_cns, false,
        Some(&step_vk), Some(&step_proof), Some(&step_vk_hash), 1,
        Some(&step_state), Some(&step_sh_actual),
        &bob.pk, &cn_bob,
    ));

    print!("  nargo execute... "); let t = Instant::now();
    do_nargo_execute(&spend_dir);
    let spend_exec_s = secs(t); println!("done ({spend_exec_s:.1}s)");

    print!("  bb prove...      "); let t = Instant::now();
    do_bb_prove(&spend_dir, "spend", "spend");
    let spend_prove_s = secs(t); println!("done ({spend_prove_s:.1}s)");

    print!("  bb verify...     "); let t = Instant::now();
    do_bb_verify(&spend_dir);
    let spend_verify_s = secs(t); println!("✓ ({spend_verify_s:.2}s)");

    stats.push(StepStats {
        label: "spend bob→carol".into(), user: "bob/carol".into(), board_size: 2,
        exec_s: spend_exec_s, prove_s: spend_prove_s, verify_s: spend_verify_s,
    });

    println!("\n=== Full IVC chain proved and verified ===");
    println!("  coinproof_base (slot 0) → coinproof_step (slot 1, receipt) → spend (bob → carol)");
    print_stats(&stats);
}

// ── Party ─────────────────────────────────────────────────────────────────────

struct Party {
    name: &'static str,
    sk:   [u8; 32],
    pk:   [u8; 32],
}

impl Party {
    fn new(name: &'static str, seed: u8) -> Self {
        let mut sk = [0u8; 32]; sk[1] = seed;
        Self { name, sk, pk: derive_pk(&sk) }
    }
}

fn hex2(b: &[u8; 32]) -> String {
    format!("{}..{}", hex::encode(&b[..4]), hex::encode(&b[28..]))
}
