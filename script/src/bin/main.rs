//! Host driver for the `cloakkchain` IVC `CoinProof` + `Valid` (spend) relations.
//!
//! Models a realistic wallet per party. Transactions now support multiple inputs
//! and outputs; only commitments appear in the transaction body. Each output's
//! coin data is encrypted separately for its recipient (`note_encs`), so no
//! recipient can see another's coin value. A session key allows all authorised
//! parties (sender + all recipients) to decrypt the transaction itself.
//!
//! ```shell
//! RUST_LOG=info cargo run --release -- --execute   # mock execution, no ZK proofs
//! RUST_LOG=info cargo run --release -- --prove     # full recursive chain (expensive)
//! ```

use std::collections::HashMap;
use std::time::Instant;

use clap::Parser;
use cloakkchain_lib::{
    append_proof_for, build_note_enc, decrypt_note, derive_pk, encrypt_tx, genesis_pk,
    merkle_root_of, recover_session_key, scan_entry as lib_scan_entry,
    BoardEntry, Coin, CoinProofPublicValues, SpendProofPackage, Transaction, ValidPublicValues,
    EK_SALT, GENESIS_SK,
};
use sp1_sdk::{
    blocking::{MockProver, ProveRequest, Prover, ProverClient},
    include_elf, Elf, HashableKey, ProvingKey, SP1Proof, SP1ProofWithPublicValues, SP1Stdin,
};

const CLOAKKCHAIN_SPEND_ELF: Elf = include_elf!("cloakkchain-program-spend");
const CLOAKKCHAIN_COINPROOF_ELF: Elf = include_elf!("cloakkchain-program-coinproof");

// ---- CLI args ---------------------------------------------------------------

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(long)]
    execute: bool,
    #[arg(long)]
    prove: bool,
}

// ---- Party ------------------------------------------------------------------

struct Party {
    name: &'static str,
    sk: [u8; 32],
    pk: [u8; 32],
}

impl Party {
    fn new(name: &'static str, seed: u8) -> Self {
        let mut sk = [0u8; 32];
        sk[1] = seed; // byte 0 is clamped by X25519 (sk[0] &= 248); seeds 1-7 all
                      // collapse to the same scalar as genesis. Use byte 1 instead.
        Self { name, sk, pk: derive_pk(&sk) }
    }
}

// ---- Wallet -----------------------------------------------------------------

struct CoinRecord {
    pv: CoinProofPublicValues,
    proof: SP1ProofWithPublicValues,
}

impl CoinRecord {
    fn slot_covered(&self) -> usize { self.pv.board_size - 1 }
}

struct Wallet<'a> {
    party: &'a Party,
    coins: HashMap<[u8; 32], CoinRecord>,
}

impl<'a> Wallet<'a> {
    fn new(party: &'a Party) -> Self {
        Self { party, coins: HashMap::new() }
    }

    fn process_slot<C: Prover>(
        &mut self,
        slot: usize,
        all_entries: &[BoardEntry],
        spend_pk: &C::ProvingKey,
        coinproof_pk: &C::ProvingKey,
        coinproof_vkey: &[u32; 8],
        client: &C,
        stats: &mut Vec<ProveStats>,
    ) {
        assert_eq!(all_entries.len(), slot + 1);
        let entry = &all_entries[slot];
        let ap = append_proof_for(all_entries);

        let tracked: Vec<[u8; 32]> = self.coins.keys().cloned().collect();
        for cn in &tracked {
            let record = self.coins.get(cn).unwrap();
            if record.slot_covered() >= slot { continue; }
            let inner_pv = record.pv.clone();
            let parent_null = inner_pv.parent_nullifier;
            let own_null    = nullifier(*cn, self.party.sk);
            let SP1Proof::Compressed(inner_c) = record.proof.proof.clone()
                else { panic!("compressed required") };
            let mut stdin = build_coinproof_stdin(
                coinproof_vkey, self.party.sk, *cn, entry, slot, &ap,
                Some(&inner_pv), parent_null, own_null,
            );
            stdin.write_proof(*inner_c, coinproof_pk.verifying_key().vk.clone());
            let label = format!("{} coin-proof slot {} (step)", self.party.name, slot);
            let rec = self.run_coinproof_step(stdin, &label, slot + 1, coinproof_pk, client, stats);
            self.coins.insert(*cn, rec);
        }

        // Discover new coins: decrypt transaction and try each note by index.
        if let Some(tx) = lib_scan_entry(&self.party.sk, entry) {
            if let Some(session_key) = recover_session_key(&self.party.sk, entry) {
                for (i, note_enc) in tx.note_encs.iter().enumerate() {
                    if let Some(note_coin) = decrypt_note(&session_key, i, note_enc) {
                        if note_coin.owner_pk != self.party.pk { continue; }
                        let cn = note_coin.commitment();
                        if !self.coins.contains_key(&cn) {
                            println!("  [{}] discovered coin (value={}) at slot {} — bootstrapping",
                                self.party.name, note_coin.value, slot);
                            let parent_null = tx.input_nullifier;
                            self.bootstrap(cn, slot, all_entries,
                                spend_pk, coinproof_pk, coinproof_vkey, client, stats, parent_null);
                        }
                    }
                }
            }
        }
    }

    fn bootstrap<C: Prover>(
        &mut self,
        cn: [u8; 32],
        up_to_slot: usize,
        all_entries: &[BoardEntry],
        spend_pk: &C::ProvingKey,
        coinproof_pk: &C::ProvingKey,
        coinproof_vkey: &[u32; 8],
        client: &C,
        stats: &mut Vec<ProveStats>,
        parent_nullifier: [u8; 32],
    ) {
        let own_null = nullifier(cn, self.party.sk);

        // Helper: extract the compressed spend proof hint from a receipt entry.
        let spend_hint = |entry: &BoardEntry| {
            let tx = lib_scan_entry(&self.party.sk, entry)
                .expect("bootstrap: cannot decrypt receipt entry");
            let pkg: SpendProofPackage = bincode::deserialize(&tx.spend_proof)
                .expect("bootstrap: tx.spend_proof is not a SpendProofPackage");
            let proof_with_pv: SP1ProofWithPublicValues =
                bincode::deserialize(&pkg.compressed_proof_bytes)
                .expect("bootstrap: cannot deserialize compressed spend proof");
            let SP1Proof::Compressed(c) = proof_with_pv.proof.clone()
                else { panic!("spend proof must be compressed") };
            *c
        };

        // Slot 0: base case.
        let ap0 = append_proof_for(&all_entries[..1]);
        let mut stdin = build_coinproof_stdin(
            coinproof_vkey, self.party.sk, cn, &all_entries[0], 0, &ap0,
            None, parent_nullifier, own_null,
        );
        // If the coin is received at slot 0, also pass the spend proof hint.
        if up_to_slot == 0 {
            stdin.write_proof(spend_hint(&all_entries[0]), spend_pk.verifying_key().vk.clone());
        }
        let label = format!("{} coin-proof slot 0 (base)", self.party.name);
        let rec = self.run_coinproof_step(stdin, &label, 1, coinproof_pk, client, stats);
        self.coins.insert(cn, rec);

        for s in 1..=up_to_slot {
            let aps = append_proof_for(&all_entries[..=s]);
            let rec = self.coins.get(&cn).unwrap();
            let inner_pv = rec.pv.clone();
            let SP1Proof::Compressed(inner_c) = rec.proof.proof.clone()
                else { panic!("compressed required") };
            let mut stdin = build_coinproof_stdin(
                coinproof_vkey, self.party.sk, cn, &all_entries[s], s, &aps,
                Some(&inner_pv), parent_nullifier, own_null,
            );
            // Inner coin-proof hint (always for s > 0).
            stdin.write_proof(*inner_c, coinproof_pk.verifying_key().vk.clone());
            // At the receipt slot, also pass the spend proof hint.
            if s == up_to_slot {
                stdin.write_proof(spend_hint(&all_entries[s]), spend_pk.verifying_key().vk.clone());
            }
            let label = if s == up_to_slot {
                format!("{} coin-proof slot {} (received)", self.party.name, s)
            } else {
                format!("{} coin-proof slot {} (scanning)", self.party.name, s)
            };
            let rec = self.run_coinproof_step(stdin, &label, s + 1, coinproof_pk, client, stats);
            self.coins.insert(cn, rec);
        }
    }

    fn run_coinproof_step<C: Prover>(
        &self,
        stdin: SP1Stdin,
        label: &str,
        board_size: usize,
        coinproof_pk: &C::ProvingKey,
        client: &C,
        stats: &mut Vec<ProveStats>,
    ) -> CoinRecord {
        let t = Instant::now();
        let proof = client.prove(coinproof_pk, stdin).compressed().run()
            .unwrap_or_else(|e| panic!("coin-proof step failed: {e}"));
        let prove_secs = t.elapsed().as_secs_f64();
        let t = Instant::now();
        client.verify(&proof, coinproof_pk.verifying_key(), None).expect("coin-proof verify failed");
        let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
        let pv: CoinProofPublicValues = bincode::deserialize(proof.public_values.as_slice())
            .expect("decode coin-proof pv");
        let proof_bytes = bincode::serialize(&proof).map(|v| v.len()).ok();
        println!("  [{}]  received_at={:?}  spent={}  ({:.1}s)", label, pv.received_at, pv.spent, prove_secs);
        stats.push(ProveStats { name: label.to_string(), board_size, prove_secs, verify_ms, proof_bytes, entry_bytes: None });
        CoinRecord { pv, proof }
    }

    fn get(&self, cn: &[u8; 32]) -> Option<&CoinRecord> { self.coins.get(cn) }

    fn print_state(&self) {
        println!("  {}:", self.party.name);
        if self.coins.is_empty() { println!("    (no coins tracked)"); return; }
        for (cn, rec) in &self.coins {
            println!("    cn={}..{}  received_at={:?}  spent={}  slot_covered={}",
                hex(&cn[..2]), hex(&cn[30..]),
                rec.pv.received_at, rec.pv.spent, rec.slot_covered());
        }
    }
}

fn hex(b: &[u8]) -> String { b.iter().map(|x| format!("{:02x}", x)).collect() }

// ---- Statistics -------------------------------------------------------------

struct ProveStats {
    name: String,
    board_size: usize,
    prove_secs: f64,
    verify_ms: f64,
    proof_bytes: Option<usize>,   // serialized proof size
    entry_bytes: Option<usize>,   // full serialized BoardEntry size (on-board cost)
}
struct ExecStats  { name: String, board_size: usize, exec_ms: u128, cycles: u64 }

fn fmt_bytes(b: usize) -> String {
    if b >= 1_048_576 { format!("{:.2} MB", b as f64 / 1_048_576.0) }
    else if b >= 1024  { format!("{:.1} KB", b as f64 / 1024.0) }
    else               { format!("{} B", b) }
}

fn print_prove_table(stats: &[ProveStats]) {
    let w = 96;
    println!("\n{}", "=".repeat(w));
    println!("  Proof Statistics  (compressed recursive SP1 STARKs)");
    println!("{}", "=".repeat(w));
    println!("{:<44} {:>5}  {:>9}  {:>10}  {:>11}  {:>11}",
             "Step", "Board", "Prove", "Verify", "Proof", "Entry");
    println!("{}", "-".repeat(w));
    let (mut tp, mut tv) = (0f64, 0f64);
    for s in stats {
        let proof_col = s.proof_bytes.map_or("          —".into(), |b| format!("{:>11}", fmt_bytes(b)));
        let entry_col = s.entry_bytes.map_or("          —".into(), |b| format!("{:>11}", fmt_bytes(b)));
        println!("{:<44} {:>5}  {:>7.1} s  {:>8.1} ms  {}  {}",
                 s.name, s.board_size, s.prove_secs, s.verify_ms, proof_col, entry_col);
        tp += s.prove_secs; tv += s.verify_ms;
    }
    println!("{}", "-".repeat(w));
    println!("{:<44} {:>5}  {:>7.1} s  {:>8.1} ms", "TOTAL", "", tp, tv);
    println!("{}", "=".repeat(w));
}

fn print_exec_table(stats: &[ExecStats]) {
    println!("\n{}", "=".repeat(70));
    println!("  Execution Statistics  (mock prover — no ZK proofs)");
    println!("{}", "=".repeat(70));
    println!("{:<44} {:>5}  {:>14}  {:>8}", "Step", "Board", "Cycles", "Time");
    println!("{}", "-".repeat(70));
    for s in stats {
        println!("{:<44} {:>5}  {:>14}  {:>6} ms", s.name, s.board_size, fmt_cycles(s.cycles), s.exec_ms);
    }
    println!("{}", "=".repeat(70));
}

fn fmt_cycles(c: u64) -> String {
    let s = c.to_string();
    let mut out = String::new();
    for (i, ch) in s.chars().rev().enumerate() {
        if i > 0 && i % 3 == 0 { out.push(','); }
        out.push(ch);
    }
    out.chars().rev().collect()
}

// ---- Coin / chain helpers ---------------------------------------------------

fn coin(seed: u8, value: u64, owner_pk: [u8; 32]) -> Coin {
    let mut tag = [0u8; 32];  tag[0] = seed;
    let mut rand = [0u8; 32]; rand[1] = seed;
    Coin { tag, value, rand, owner_pk }
}

/// Compute `H(coin_commitment || sk)` — the spending nullifier.
fn nullifier(cn: [u8; 32], sk: [u8; 32]) -> [u8; 32] {
    use sha2::{Digest, Sha256};
    let mut h = Sha256::new(); h.update(cn); h.update(sk);
    let mut out = [0u8; 32]; out.copy_from_slice(&h.finalize()); out
}

/// Build the `SpendProofPackage` stored in `tx.spend_proof`.
/// Packages everything the coin-proof IVC needs to verify the spend proof at receipt.
fn build_spend_proof_package(
    proof: &SP1ProofWithPublicValues,
    spend_vkey: &[u32; 8],
) -> SpendProofPackage {
    let compressed_proof_bytes = bincode::serialize(proof).expect("serialize compressed proof");
    let pv_encode = proof.public_values.as_slice().to_vec();
    SpendProofPackage { compressed_proof_bytes, pv_encode, spend_vkey: *spend_vkey }
}

/// Build a Transaction using X25519 note encryption via session_key.
/// Returns `(tx, session_key, recipient_pks)` — pass to `encrypt_tx` as
/// `encrypt_tx(&tx, &recipient_pks, session_key)`.
fn make_tx(
    id: u64,
    sender_sk: [u8; 32],
    input_coins: &[Coin],
    outputs: &[(Coin, [u8; 32])],
) -> (Transaction, [u8; 32], Vec<[u8; 32]>) {
    use sha2::{Digest, Sha256};
    // Derive session key deterministically (same as encrypt_tx will use).
    let session_key: [u8; 32] = {
        let mut h = Sha256::new();
        h.update(sender_sk); h.update((id as u64).to_le_bytes()); h.update(EK_SALT);
        let mut out = [0u8; 32]; out.copy_from_slice(&h.finalize()); out
    };
    let input_commitments: Vec<[u8; 32]>  = input_coins.iter().map(|c| c.commitment()).collect();
    let recipient_pks: Vec<[u8; 32]>      = outputs.iter().map(|(_, rpk)| *rpk).collect();
    let output_commitments: Vec<[u8; 32]> = outputs.iter().map(|(c, _)| c.commitment()).collect();
    let note_encs: Vec<Vec<u8>>           = outputs.iter().enumerate()
        .map(|(i, (c, _))| build_note_enc(&session_key, i, c)).collect();
    let input_nullifier = nullifier(input_commitments[0], sender_sk);
    let tx = Transaction { id, input_commitments, output_commitments, note_encs, input_nullifier, spend_proof: vec![] };
    (tx, session_key, recipient_pks)
}

// ---- stdin builders ---------------------------------------------------------

fn build_coinproof_stdin(
    coinproof_vkey: &[u32; 8], owner_sk: [u8; 32], coin_commitment: [u8; 32],
    entry_k: &BoardEntry, slot: usize, append_path: &[[u8; 32]],
    inner: Option<&CoinProofPublicValues>,
    parent_nullifier: [u8; 32], own_nullifier: [u8; 32],
) -> SP1Stdin {
    let mut stdin = SP1Stdin::new();
    stdin.write(coinproof_vkey);
    stdin.write(&owner_sk);
    stdin.write(&coin_commitment);
    stdin.write(entry_k);
    stdin.write(&slot);
    stdin.write(&append_path.to_vec());
    stdin.write(&inner.is_some());
    if let Some(pv) = inner { stdin.write(pv); }
    stdin.write(&parent_nullifier);
    stdin.write(&own_nullifier);
    stdin
}

fn build_spend_stdin(
    spend_vkey: &[u32; 8], coinproof_vkey: &[u32; 8],
    sender: &Party, coin_commitment: [u8; 32],
    prior_entries: &[BoardEntry], tx_star: &Transaction,
    input_coins: &[Coin], output_coins: &[Coin],
    is_genesis: bool, coin_proof: Option<&CoinProofPublicValues>,
) -> SP1Stdin {
    let mut stdin = SP1Stdin::new();
    stdin.write(spend_vkey);
    stdin.write(coinproof_vkey);
    stdin.write(&sender.sk);
    stdin.write(&sender.pk);
    stdin.write(&coin_commitment);
    stdin.write(&prior_entries.to_vec());
    stdin.write(tx_star);
    stdin.write(&input_coins.to_vec());
    stdin.write(&output_coins.to_vec());
    stdin.write(&is_genesis);
    if let Some(cp) = coin_proof { stdin.write(cp); }
    stdin
}


// ---- main -------------------------------------------------------------------

fn main() {
    sp1_sdk::utils::setup_logger();
    dotenv::dotenv().ok();

    let args = Args::parse();
    if args.execute == args.prove {
        eprintln!("Error: specify either --execute or --prove");
        std::process::exit(1);
    }

    let alice   = Party::new("Alice",   1);
    let bob     = Party::new("Bob",     2);
    let carol   = Party::new("Carol",   3);
    let genesis = Party { name: "Genesis", sk: GENESIS_SK, pk: genesis_pk() };

    // Demo chain coins.
    let genesis_coin  = coin(0xA1, 100, genesis.pk);
    let alice_coin    = coin(0xA2, 100, alice.pk);
    let bob_coin      = coin(0xB1,  40, bob.pk);
    let alice_change  = coin(0xB2,  60, alice.pk);
    let carol_coin    = coin(0xC1,  40, carol.pk);

    // Coin commitments derived directly from coin data — no transactions needed yet.
    let cn_genesis = genesis_coin.commitment();
    let cn_alice   = alice_coin.commitment();
    let cn_bob     = bob_coin.commitment();

    // The board starts empty. Entries are pushed one at a time as each spend
    // is proved and the sender posts their transaction — mirroring the real
    // sequential flow where no future transactions exist until their sender acts.
    let mut entries: Vec<BoardEntry> = vec![];

    // ---- --execute ----------------------------------------------------------
    if args.execute {
        let client       = MockProver::new();
        let spend_pk     = client.setup(CLOAKKCHAIN_SPEND_ELF).expect("setup spend elf");
        let coinproof_pk = client.setup(CLOAKKCHAIN_COINPROOF_ELF).expect("setup coinproof elf");
        let spend_vkey     = spend_pk.verifying_key().hash_u32();
        let coinproof_vkey = coinproof_pk.verifying_key().hash_u32();
        println!("spend vkey:     {}", spend_pk.verifying_key().bytes32());
        println!("coinproof vkey: {}", coinproof_pk.verifying_key().bytes32());

        let mut stats: Vec<ExecStats> = Vec::new();

        // Slot 0: genesis mint — tx0 is built here, not upfront.
        let (mut tx0, s0, r0) = make_tx(0, GENESIS_SK, &[genesis_coin.clone()], &[(alice_coin.clone(), alice.pk)]);
        let stdin = build_spend_stdin(&spend_vkey, &coinproof_vkey, &genesis, cn_genesis,
            &entries, &tx0, &[genesis_coin.clone()], &[alice_coin.clone()], true, None);
        let t = Instant::now();
        let (output, report) = client.execute(CLOAKKCHAIN_SPEND_ELF, stdin).run().unwrap();
        let exec_ms = t.elapsed().as_millis();
        let pv: ValidPublicValues = bincode::deserialize(output.as_slice()).expect("decode");
        assert_eq!(pv.board_root, merkle_root_of(&entries));
        // In execute mode there is no real compressed proof. Store a mock package
        // with empty compressed_proof_bytes so check_coin_proof_step validates
        // output_commitments but skips the verify_sp1_proof cryptographic check.
        let mock_pkg = SpendProofPackage {
            compressed_proof_bytes: vec![],
            pv_encode: pv.encode(),
            spend_vkey: [0u32; 8],
        };
        tx0.spend_proof = bincode::serialize(&mock_pkg).expect("serialize mock pkg");
        entries.push(encrypt_tx(&tx0, &r0, s0)); // board now has slot 0
        stats.push(ExecStats { name: "Slot 0: genesis mint (spend)".into(), board_size: 1, exec_ms, cycles: report.total_instruction_count() });

        let ap0 = append_proof_for(&entries[..1]);
        for (owner_sk, label) in [(alice.sk, "Alice"), (bob.sk, "Bob  "), (carol.sk, "Carol")] {
            let pn = [0u8; 32];
            let on = nullifier(cn_alice, owner_sk);
            let stdin = build_coinproof_stdin(
                &coinproof_vkey, owner_sk, cn_alice,
                &entries[0], 0, &ap0, None, pn, on,
            );
            let t = Instant::now();
            let (output, report) = client.execute(CLOAKKCHAIN_COINPROOF_ELF, stdin).run().unwrap();
            let exec_ms = t.elapsed().as_millis();
            let cp: CoinProofPublicValues = bincode::deserialize(output.as_slice()).expect("decode");
            stats.push(ExecStats { name: format!("{label} coin-proof slot 0"), board_size: 1, exec_ms, cycles: report.total_instruction_count() });
            println!("  [{label} slot 0] received_at={:?} spent={}", cp.received_at, cp.spent);
        }

        print_exec_table(&stats);
        println!("\nRun --prove for the full recursive chain.");
        return;
    }

    // ---- --prove ------------------------------------------------------------
    let client       = ProverClient::from_env();
    let spend_pk     = client.setup(CLOAKKCHAIN_SPEND_ELF).expect("setup spend elf");
    let coinproof_pk = client.setup(CLOAKKCHAIN_COINPROOF_ELF).expect("setup coinproof elf");
    let spend_vkey     = spend_pk.verifying_key().hash_u32();
    let coinproof_vkey = coinproof_pk.verifying_key().hash_u32();
    println!("spend vkey:     {}", spend_pk.verifying_key().bytes32());
    println!("coinproof vkey: {}", coinproof_pk.verifying_key().bytes32());

    let mut alice_wallet = Wallet::new(&alice);
    let mut bob_wallet   = Wallet::new(&bob);
    let mut carol_wallet = Wallet::new(&carol);
    let mut stats: Vec<ProveStats> = Vec::new();

    // =========================================================================
    // Slot 0: genesis mints 100 units to Alice
    // =========================================================================
    println!("\n--- Slot 0: genesis mint (1 input → 1 output) ---");
    let (mut tx0, s0, r0) = make_tx(0, GENESIS_SK, &[genesis_coin.clone()], &[(alice_coin.clone(), alice.pk)]);
    let stdin = build_spend_stdin(&spend_vkey, &coinproof_vkey, &genesis, cn_genesis,
        &entries, &tx0, &[genesis_coin.clone()], &[alice_coin.clone()], true, None);
    let t = Instant::now();
    let genesis_proof = client.prove(&spend_pk, stdin).compressed().run().expect("genesis prove");
    let prove_secs = t.elapsed().as_secs_f64();
    let t = Instant::now();
    client.verify(&genesis_proof, spend_pk.verifying_key(), None).expect("genesis verify");
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let pv: ValidPublicValues = bincode::deserialize(genesis_proof.public_values.as_slice()).expect("decode");
    assert_eq!(pv.board_root, merkle_root_of(&entries));
    let genesis_pkg = build_spend_proof_package(&genesis_proof, &spend_vkey);
    let genesis_proof_size = bincode::serialize(&genesis_pkg).map(|v| v.len()).unwrap_or(0);
    tx0.spend_proof = bincode::serialize(&genesis_pkg).expect("serialize spend proof package");
    entries.push(encrypt_tx(&tx0, &r0, s0));
    let e0_bytes = bincode::serialize(&entries[0]).map(|v| v.len()).unwrap_or(0);
    stats.push(ProveStats { name: "Slot 0: genesis mint".into(), board_size: 1, prove_secs, verify_ms, proof_bytes: Some(genesis_proof_size), entry_bytes: Some(e0_bytes) });
    println!("  Proved & verified ({prove_secs:.1} s) — proof {} — entry {}", fmt_bytes(genesis_proof_size), fmt_bytes(e0_bytes));

    println!("--- Wallets scanning slot 0 ---");
    alice_wallet.process_slot(0, &entries, &spend_pk, &coinproof_pk, &coinproof_vkey, &client, &mut stats);
    bob_wallet  .process_slot(0, &entries, &spend_pk, &coinproof_pk, &coinproof_vkey, &client, &mut stats);
    carol_wallet.process_slot(0, &entries, &spend_pk, &coinproof_pk, &coinproof_vkey, &client, &mut stats);

    // =========================================================================
    // Slot 1: Alice sends 40 to Bob + 60 change — built after Alice received her coin
    // =========================================================================
    println!("\n--- Slot 1: Alice spends to Bob + change (1 input → 2 outputs) ---");
    let (mut tx1, s1, r1) = make_tx(1, alice.sk, &[alice_coin.clone()],
        &[(bob_coin.clone(), bob.pk), (alice_change.clone(), alice.pk)]);
    let alice_record = alice_wallet.get(&cn_alice).expect("Alice must have cn_alice proof");
    let mut stdin = build_spend_stdin(&spend_vkey, &coinproof_vkey, &alice, cn_alice,
        &entries, &tx1,
        &[alice_coin.clone()], &[bob_coin.clone(), alice_change.clone()],
        false, Some(&alice_record.pv));
    {
        let SP1Proof::Compressed(inner) = alice_record.proof.proof.clone() else { panic!() };
        stdin.write_proof(*inner, coinproof_pk.verifying_key().vk.clone());
    }
    let t = Instant::now();
    let alice_spend_proof = client.prove(&spend_pk, stdin).compressed().run().expect("alice spend prove");
    let prove_secs = t.elapsed().as_secs_f64();
    let t = Instant::now();
    client.verify(&alice_spend_proof, spend_pk.verifying_key(), None).expect("alice spend verify");
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let pv: ValidPublicValues = bincode::deserialize(alice_spend_proof.public_values.as_slice()).expect("decode");
    assert_eq!(pv.board_root, merkle_root_of(&entries));
    let alice_pkg = build_spend_proof_package(&alice_spend_proof, &spend_vkey);
    let alice_proof_size = bincode::serialize(&alice_pkg).map(|v| v.len()).unwrap_or(0);
    tx1.spend_proof = bincode::serialize(&alice_pkg).expect("serialize spend proof package");
    entries.push(encrypt_tx(&tx1, &r1, s1));
    let e1_bytes = bincode::serialize(&entries[1]).map(|v| v.len()).unwrap_or(0);
    stats.push(ProveStats { name: "Slot 1: Alice's spend (compressed)".into(), board_size: 2, prove_secs, verify_ms, proof_bytes: Some(alice_proof_size), entry_bytes: Some(e1_bytes) });
    println!("  Proved & verified ({prove_secs:.1} s) — proof {} — entry {}", fmt_bytes(alice_proof_size), fmt_bytes(e1_bytes));

    println!("--- Wallets scanning slot 1 ---");
    alice_wallet.process_slot(1, &entries, &spend_pk, &coinproof_pk, &coinproof_vkey, &client, &mut stats);
    bob_wallet  .process_slot(1, &entries, &spend_pk, &coinproof_pk, &coinproof_vkey, &client, &mut stats);
    carol_wallet.process_slot(1, &entries, &spend_pk, &coinproof_pk, &coinproof_vkey, &client, &mut stats);

    // =========================================================================
    // Slot 2: Bob sends 40 to Carol — built after Bob received his coin
    // =========================================================================
    println!("\n--- Slot 2: Bob spends to Carol (1 input → 1 output) ---");
    let (mut tx2, s2, r2) = make_tx(2, bob.sk, &[bob_coin.clone()], &[(carol_coin.clone(), carol.pk)]);
    let bob_record = bob_wallet.get(&cn_bob).expect("Bob must have cn_bob proof");
    let mut stdin = build_spend_stdin(&spend_vkey, &coinproof_vkey, &bob, cn_bob,
        &entries, &tx2,
        &[bob_coin.clone()], &[carol_coin.clone()],
        false, Some(&bob_record.pv));
    {
        let SP1Proof::Compressed(inner) = bob_record.proof.proof.clone() else { panic!() };
        stdin.write_proof(*inner, coinproof_pk.verifying_key().vk.clone());
    }
    let t = Instant::now();
    let bob_spend_proof = client.prove(&spend_pk, stdin).compressed().run().expect("bob spend prove");
    let prove_secs = t.elapsed().as_secs_f64();
    let t = Instant::now();
    client.verify(&bob_spend_proof, spend_pk.verifying_key(), None).expect("bob spend verify");
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let pv: ValidPublicValues = bincode::deserialize(bob_spend_proof.public_values.as_slice()).expect("decode");
    assert_eq!(pv.board_root, merkle_root_of(&entries));
    let bob_pkg = build_spend_proof_package(&bob_spend_proof, &spend_vkey);
    let bob_proof_size = bincode::serialize(&bob_pkg).map(|v| v.len()).unwrap_or(0);
    tx2.spend_proof = bincode::serialize(&bob_pkg).expect("serialize spend proof package");
    entries.push(encrypt_tx(&tx2, &r2, s2));
    let e2_bytes = bincode::serialize(&entries[2]).map(|v| v.len()).unwrap_or(0);
    stats.push(ProveStats { name: "Slot 2: Bob's spend (compressed)".into(), board_size: 3, prove_secs, verify_ms, proof_bytes: Some(bob_proof_size), entry_bytes: Some(e2_bytes) });
    println!("  Proved & verified ({prove_secs:.1} s) — proof {} — entry {}", fmt_bytes(bob_proof_size), fmt_bytes(e2_bytes));

    println!("--- Wallets scanning slot 2 ---");
    alice_wallet.process_slot(2, &entries, &spend_pk, &coinproof_pk, &coinproof_vkey, &client, &mut stats);
    bob_wallet  .process_slot(2, &entries, &spend_pk, &coinproof_pk, &coinproof_vkey, &client, &mut stats);
    carol_wallet.process_slot(2, &entries, &spend_pk, &coinproof_pk, &coinproof_vkey, &client, &mut stats);

    println!("\n=== Wallet States ===");
    alice_wallet.print_state();
    bob_wallet.print_state();
    carol_wallet.print_state();

    print_prove_table(&stats);
}
