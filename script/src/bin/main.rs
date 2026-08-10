//! Host driver for the MNT-native cloakkchain relations (Phase 4 of the
//! MNT-native port, extended with multi-input/output support and the full
//! genesis->Alice->Bob->Carol chain).
//!
//! Demo chain: genesis mints to Alice, Alice's receipt is built
//! (recursively verifying the wrapped genesis proof), Alice spends 1-in/
//! 2-out (40 to Bob, 60 change back to herself — real value conservation
//! over a genuine sum, not just equality), Bob's receipt is built
//! (recursively verifying the *wrapped spend* proof — a "second
//! generation" `ReceiptStepCircuit` setup, since `check_coin_receipt`
//! circuits are fixed to one specific wrapped VK; see circuit-coinproof's
//! module doc comment), then Bob spends his 40 units to Carol.
//!
//! `--prove` runs each of the nine proving steps in its own fresh
//! subprocess (`--internal-prove-step`/`--internal-prove-output`, hidden
//! flags) so the peak-memory column reflects that step's own footprint via
//! the kernel's `VmHWM` tracker, not a same-process running high-water
//! mark. The whole chain is deterministic (fixed RNG seed, fixed demo
//! data), so each subprocess just silently redoes the real proving for
//! every step before its target and only reports the target step's stats —
//! no proving keys/proofs need to cross the process boundary, only the
//! small `ProveStats` struct.
//!
//! ```shell
//! RUST_LOG=info cargo run --release -- --execute   # genesis circuit's constraint check only, no proving
//! RUST_LOG=info cargo run --release -- --prove     # full chain, nine real Groth16 proofs
//! ```

use std::time::Instant;

use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
use ark_std::rand::{rngs::StdRng, SeedableRng};
use clap::Parser;
use cloakkchain_circuit_coinproof::ReceiptStepCircuit;
use cloakkchain_circuit_spend::{GenesisSpendCircuit, SpendStepCircuit, MAX_OUTPUTS};
use cloakkchain_circuit_wrap::WrapCircuit;
use cloakkchain_lib::{
    append_path_for_next, compute_root_from_path, derive_enc_pk, derive_owner_pk,
    entry_ciphertext_commitment, fold_owner_scalar, genesis_pk, genesis_sk, merkle_leaf,
    owner_pk_to_field_pair, poseidon_hash, scan_entry, BoardEntry, Coin, Fr, NullifierTree,
    OwnerPk, OwnerScalar, Transaction, EK_SALT,
};

const GENESIS_SPEND_PUBLIC_INPUTS: usize = 6; // 2 (pk) + MAX_OUTPUTS(2) + 2 (board_root, nullifier_root)
const RECEIPT_PUBLIC_INPUTS: usize = 5;
const NUM_STEPS: usize = 9;

// ---- CLI args ---------------------------------------------------------------

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(long)]
    execute: bool,
    #[arg(long)]
    prove: bool,
    /// Hidden: re-invokes this binary as a single proving-step subprocess
    /// (see the module doc comment). Not for direct use.
    #[arg(long, hide = true)]
    internal_prove_step: Option<usize>,
    /// Hidden: where `--internal-prove-step` writes its `ProveStats`.
    #[arg(long, hide = true)]
    internal_prove_output: Option<String>,
}

// ---- Party / coin helpers ---------------------------------------------------

/// Each party holds two independent keypairs: an X25519 pair for
/// encryption (unchanged from the pre-port design) and a native MNT6-753
/// pair for coin ownership (see `cloakkchain_lib::OwnerPk`'s doc comment for
/// why they're on separate curves/fields).
struct Party {
    name: &'static str,
    enc_sk: [u8; 32],
    enc_pk: [u8; 32],
    sk_p: OwnerScalar,
    pk_p: OwnerPk,
}

impl Party {
    fn new(name: &'static str, seed: u8) -> Self {
        let mut enc_sk = [0u8; 32];
        enc_sk[1] = seed; // byte 0 is X25519-clamped; seeds 1-7 in byte 0 would collapse together
        let enc_pk = derive_enc_pk(&enc_sk);
        let sk_p = OwnerScalar::from(seed as u64 + 100); // +100: stay well clear of genesis_sk()==1
        let pk_p = derive_owner_pk(&sk_p);
        Self { name, enc_sk, enc_pk, sk_p, pk_p }
    }

    fn genesis() -> Self {
        Self { name: "Genesis", enc_sk: [0u8; 32], enc_pk: [0u8; 32], sk_p: genesis_sk(), pk_p: genesis_pk() }
    }
}

fn coin(seed: u8, value: u64, owner_pk: OwnerPk) -> Coin {
    Coin { tag: Fr::from(seed as u64 + 1), value, rand: Fr::from(seed as u64 + 1000), owner_pk }
}

/// Pads a variable-length list of real output commitments out to
/// `MAX_OUTPUTS` with a zero sentinel — both the spend circuit's fixed-size
/// public output and any `BoardEntry` built from the same transaction must
/// agree on this padding, or the entry's leaf hash won't match what the
/// circuit computed.
fn pad_outputs(real: &[Fr]) -> [Fr; MAX_OUTPUTS] {
    let mut out = [Fr::from(0u64); MAX_OUTPUTS];
    out[..real.len()].copy_from_slice(real);
    out
}

/// Build a Transaction using X25519 note encryption derived from a
/// per-transaction session key. Returns `(tx, session_key, recipient_enc_pks)`
/// — pass to `encrypt_tx` as `encrypt_tx(&tx, &recipient_enc_pks, session_key)`.
fn make_tx(
    id: u64,
    sender_enc_sk: [u8; 32],
    sender_sk_p: &OwnerScalar,
    input_coins: &[Coin],
    outputs: &[(Coin, [u8; 32])], // (coin, recipient's X25519 enc_pk)
) -> (Transaction, [u8; 32], Vec<[u8; 32]>) {
    use sha2::{Digest, Sha256};
    let session_key: [u8; 32] = {
        let mut h = Sha256::new();
        h.update(sender_enc_sk);
        h.update(id.to_le_bytes());
        h.update(EK_SALT);
        let mut out = [0u8; 32];
        out.copy_from_slice(&h.finalize());
        out
    };
    let input_commitments: Vec<Fr> = input_coins.iter().map(|c| c.commitment()).collect();
    let recipient_enc_pks: Vec<[u8; 32]> = outputs.iter().map(|(_, rpk)| *rpk).collect();
    let output_commitments: Vec<Fr> = outputs.iter().map(|(c, _)| c.commitment()).collect();
    let note_encs: Vec<Vec<u8>> = outputs
        .iter()
        .enumerate()
        .map(|(i, (c, _))| cloakkchain_lib::build_note_enc(&session_key, i, c))
        .collect();
    let input_nullifier = poseidon_hash(&[input_commitments[0], fold_owner_scalar(sender_sk_p)]);
    let tx = Transaction { id, input_commitments, output_commitments, note_encs, input_nullifier, spend_proof: vec![] };
    (tx, session_key, recipient_enc_pks)
}

// ---- Subprocess isolation + peak-memory tracking -----------------------------
//
// Each proving step runs in a fresh child process so its peak-memory
// reading reflects only that step's own working set, not a same-process
// running high-water mark carried over from earlier steps (proving/
// verifying keys held alive for later chaining, allocator pages the
// allocator doesn't return to the OS, etc.). This mirrors `main` branch's
// SP1-subprocess isolation, but polls the kernel's own `VmHWM` (peak RSS)
// counter for the child rather than sampling `VmRSS` from a background
// thread — `VmHWM` can't miss a spike between polls the way a fixed-interval
// sample can.

/// Poll `/proc/<pid>/status` for `VmHWM` (the kernel's own running peak
/// resident-set-size tracker) while `child` runs, returning the highest
/// value observed (in KB) alongside its exit status. Linux-only — silently
/// yields `None` for the memory reading anywhere `/proc` isn't available.
fn wait_tracking_peak_memory(mut child: std::process::Child) -> (std::process::ExitStatus, Option<u64>) {
    let pid = child.id();
    let mut peak_kb: Option<u64> = None;
    loop {
        if let Ok(status_text) = std::fs::read_to_string(format!("/proc/{pid}/status")) {
            for line in status_text.lines() {
                if let Some(rest) = line.strip_prefix("VmHWM:") {
                    if let Some(kb) = rest.split_whitespace().next().and_then(|s| s.parse::<u64>().ok()) {
                        peak_kb = Some(peak_kb.map_or(kb, |p: u64| p.max(kb)));
                    }
                }
            }
        }
        match child.try_wait().expect("poll proving subprocess") {
            Some(status) => return (status, peak_kb),
            None => std::thread::sleep(std::time::Duration::from_millis(50)),
        }
    }
}

/// Spawn a fresh copy of this binary to (re-)compute the chain up through
/// `step_idx` and report just that step's stats, tracking its peak RSS from
/// the outside via `wait_tracking_peak_memory`.
fn run_step_in_subprocess(step_idx: usize) -> ProveStats {
    let out_path = std::env::temp_dir().join(format!("cloakkchain_step{step_idx}_stats.bin"));
    let exe = std::env::current_exe().expect("current_exe");
    let mut cmd = std::process::Command::new(&exe);
    cmd.args([
        "--internal-prove-step",
        &step_idx.to_string(),
        "--internal-prove-output",
        out_path.to_str().expect("temp path is valid UTF-8"),
    ]);
    let child = cmd.spawn().expect("spawn proving subprocess");
    let (status, peak_mem_kb) = wait_tracking_peak_memory(child);
    assert!(status.success(), "proving subprocess for step {step_idx} exited with {status}");

    let bytes = std::fs::read(&out_path).expect("read stats file");
    let mut stat: ProveStats = bincode::deserialize(&bytes).expect("deserialize stats");
    let _ = std::fs::remove_file(&out_path);
    stat.peak_mem_kb = peak_mem_kb.unwrap_or(0);
    stat
}

// ---- Statistics --------------------------------------------------------------

#[derive(serde::Serialize, serde::Deserialize)]
struct ProveStats {
    name: String,
    board_size: usize,
    prove_secs: f64,
    verify_ms: f64,
    proof_bytes: usize,
    entry_bytes: Option<usize>,
    peak_mem_kb: u64,
}

fn fmt_bytes(b: usize) -> String {
    if b >= 1_048_576 {
        format!("{:.2} MB", b as f64 / 1_048_576.0)
    } else if b >= 1024 {
        format!("{:.1} KB", b as f64 / 1024.0)
    } else {
        format!("{b} B")
    }
}

fn fmt_mem_kb(kb: u64) -> String {
    fmt_bytes(kb as usize * 1024)
}

fn print_prove_table(stats: &[ProveStats]) {
    let w = 108;
    println!("\n{}", "=".repeat(w));
    println!("  Proof Statistics");
    println!("{}", "=".repeat(w));
    println!(
        "{:<28} {:>5}  {:>9}  {:>10}  {:>11}  {:>11}  {:>11}",
        "Step", "Board", "Prove", "Verify", "Proof", "Entry", "Peak Mem"
    );
    println!("{}", "-".repeat(w));
    let (mut tp, mut tv) = (0f64, 0f64);
    for s in stats {
        let entry_col = s.entry_bytes.map_or("          —".into(), |b| format!("{:>11}", fmt_bytes(b)));
        println!(
            "{:<28} {:>5} {:>7.1} s  {:>8.1} ms  {:>11}  {}  {:>11}",
            s.name,
            s.board_size,
            s.prove_secs,
            s.verify_ms,
            fmt_bytes(s.proof_bytes),
            entry_col,
            fmt_mem_kb(s.peak_mem_kb)
        );
        tp += s.prove_secs;
        tv += s.verify_ms;
    }
    println!("{}", "-".repeat(w));
    println!("{:<28} {:>5} {:>7.1} s  {:>8.1} ms", "TOTAL", "", tp, tv);
    println!("{}", "=".repeat(w));
}

fn ark_serialize_bytes<T: ark_serialize::CanonicalSerialize>(v: &T) -> Vec<u8> {
    let mut out = Vec::new();
    v.serialize_compressed(&mut out).expect("serialize proof");
    out
}

fn ark_serialize_len<T: ark_serialize::CanonicalSerialize>(v: &T) -> usize {
    v.compressed_size()
}

// ---- main ---------------------------------------------------------------

fn main() {
    let args = Args::parse();

    if let Some(step_idx) = args.internal_prove_step {
        let out_path = args.internal_prove_output.expect("--internal-prove-output required with --internal-prove-step");
        let stat = run_chain_step(step_idx);
        std::fs::write(&out_path, bincode::serialize(&stat).expect("serialize stats")).expect("write stats file");
        return;
    }

    let mode_count = [args.execute, args.prove].iter().filter(|&&b| b).count();
    if mode_count != 1 {
        eprintln!("Error: specify exactly one of --execute, --prove");
        std::process::exit(1);
    }

    let genesis = Party::genesis();
    let alice = Party::new("Alice", 1);
    let genesis_coin = coin(0xA1, 100, genesis.pk_p);
    let alice_coin = coin(0xA2, 100, alice.pk_p);

    if args.execute {
        run_execute(&genesis, &genesis_coin, &alice_coin);
        return;
    }

    run_prove();
}

/// Cheap sanity check: build the genesis-mint witness and confirm it
/// satisfies `GenesisSpendCircuit`'s constraints, with no Groth16 setup or
/// proving. This is the only circuit in the chain that doesn't recursively
/// verify another proof, so it's the only one a "no real proving" mode can
/// meaningfully check in isolation — `ReceiptStepCircuit`/`SpendStepCircuit`
/// need a genuine inner proof to exist as a witness regardless (there's no
/// zkVM-style mock-mode equivalent for a Groth16 recursive-verification
/// gadget), so exercising them for real is what `--prove` is for.
fn run_execute(genesis: &Party, genesis_coin: &Coin, alice_coin: &Coin) {
    println!("--execute: checking GenesisSpendCircuit's constraints only (no proving)");

    let output_commitments = pad_outputs(&[alice_coin.commitment()]);
    let append_path = append_path_for_next(&[]);
    let board_root = compute_root_from_path(Fr::from(0u64), 0, &append_path);
    let own_nullifier = poseidon_hash(&[genesis_coin.commitment(), fold_owner_scalar(&genesis.sk_p)]);
    let tree = NullifierTree::new();

    let circuit = GenesisSpendCircuit {
        pk_p: Some(genesis.pk_p),
        output_commitments: Some(output_commitments),
        board_root: Some(board_root),
        current_nullifier_root: Some(tree.root()),
        sk_p: Some(genesis.sk_p),
        input_coins: [Some(genesis_coin.clone()), None],
        output_coins: [Some(alice_coin.clone()), None],
        entry_position: Some(0),
        append_path: Some(append_path),
        own_nullifier_nonmembership: [Some(tree.prove_non_membership(own_nullifier)), None],
    };

    let cs = ConstraintSystem::<Fr>::new_ref();
    circuit.generate_constraints(cs.clone()).expect("synthesize constraints");
    let satisfied = cs.is_satisfied().expect("check satisfiability");
    println!("  constraints: {}", cs.num_constraints());
    println!("  satisfied:   {satisfied}");
    assert!(satisfied);
    println!("\nRun --prove for the full chain (nine real Groth16 proofs).");
}

/// Orchestrator: runs each of the nine proving steps in its own subprocess
/// (see the module doc comment) and prints the combined stats table.
fn run_prove() {
    let mut stats: Vec<ProveStats> = Vec::new();
    for step_idx in 0..NUM_STEPS {
        println!("--- Step {}/{NUM_STEPS} ---", step_idx + 1);
        println!("  [subprocess] proving step {step_idx} in child process …");
        let stat = run_step_in_subprocess(step_idx);
        println!("  {}: proved & verified ({:.1}s)", stat.name, stat.prove_secs);
        stats.push(stat);
    }
    print_prove_table(&stats);
}

/// (Re-)computes the demo chain up through `target_step` and returns that
/// step's stats. Every step before `target_step` is real proving (needed
/// so later steps have genuine proofs to recursively verify) but is
/// otherwise silent — narration and stats collection only happen for
/// `target_step` itself. Since the RNG is freshly re-seeded with a fixed
/// value on every invocation, re-deriving the prefix here is bit-for-bit
/// identical to what an earlier subprocess already computed for it.
fn run_chain_step(target_step: usize) -> ProveStats {
    let mut rng = StdRng::seed_from_u64(0x636c6f616b); // "cloak" — deterministic demo, not a security-relevant seed
    let mut entries: Vec<BoardEntry> = vec![];

    let genesis = Party::genesis();
    let alice = Party::new("Alice", 1);
    let bob = Party::new("Bob", 2);
    let carol = Party::new("Carol", 3);

    // =========================================================================
    // Step 0: genesis mints 100 units to Alice
    // =========================================================================
    if target_step == 0 {
        println!("--- Slot 0: genesis mint ---");
    }
    let genesis_coin = coin(0xA1, 100, genesis.pk_p);
    let alice_coin = coin(0xA2, 100, alice.pk_p);
    let genesis_outputs = pad_outputs(&[alice_coin.commitment()]);
    let genesis_append_path = append_path_for_next(&entries);
    let genesis_board_root = compute_root_from_path(Fr::from(0u64), entries.len(), &genesis_append_path);
    let genesis_own_nullifier = poseidon_hash(&[genesis_coin.commitment(), fold_owner_scalar(&genesis.sk_p)]);
    let empty_tree = NullifierTree::new();

    let genesis_circuit = GenesisSpendCircuit {
        pk_p: Some(genesis.pk_p),
        output_commitments: Some(genesis_outputs),
        board_root: Some(genesis_board_root),
        current_nullifier_root: Some(empty_tree.root()),
        sk_p: Some(genesis.sk_p),
        input_coins: [Some(genesis_coin.clone()), None],
        output_coins: [Some(alice_coin.clone()), None],
        entry_position: Some(entries.len() as u64),
        append_path: Some(genesis_append_path.clone()),
        own_nullifier_nonmembership: [Some(empty_tree.prove_non_membership(genesis_own_nullifier)), None],
    };
    let genesis_public_inputs: [Fr; GENESIS_SPEND_PUBLIC_INPUTS] =
        GenesisSpendCircuit::public_inputs(genesis.pk_p, genesis_outputs, genesis_board_root, empty_tree.root())
            .try_into()
            .unwrap();

    let t = Instant::now();
    let (genesis_pk_data, genesis_vk) = cloakkchain_circuit_spend::setup(&mut rng).unwrap();
    let genesis_proof = cloakkchain_circuit_spend::prove(&genesis_pk_data, genesis_circuit, &mut rng).unwrap();
    let prove_secs = t.elapsed().as_secs_f64();
    let t = Instant::now();
    assert!(cloakkchain_circuit_spend::verify(&genesis_vk, &genesis_public_inputs, &genesis_proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    if target_step == 0 {
        println!("  proved & verified ({prove_secs:.1}s)");
    }
    let stat0 = ProveStats {
        name: "Genesis mint".into(),
        board_size: entries.len() + 1,
        prove_secs,
        verify_ms,
        proof_bytes: ark_serialize_len(&genesis_proof),
        entry_bytes: None,
        peak_mem_kb: 0,
    };
    if target_step == 0 {
        return stat0;
    }

    let (mut tx0, s0, r0) =
        make_tx(0, genesis.enc_sk, &genesis.sk_p, &[genesis_coin.clone()], &[(alice_coin.clone(), alice.enc_pk)]);
    tx0.spend_proof = ark_serialize_bytes(&genesis_proof);
    let genesis_entry = cloakkchain_lib::encrypt_tx(&tx0, &r0, s0);
    entries.push(genesis_entry.clone());
    let entry0_bytes = bincode::serialize(&genesis_entry).map(|v| v.len()).ok();

    // =========================================================================
    // Step 1: wrap the genesis proof so Alice's receipt circuit can verify it
    // =========================================================================
    let t = Instant::now();
    let (wrap_genesis_pk, wrap_genesis_vk) =
        cloakkchain_circuit_wrap::setup::<GENESIS_SPEND_PUBLIC_INPUTS, _>(genesis_vk, &mut rng).unwrap();
    let wrap_genesis_proof = cloakkchain_circuit_wrap::prove::<GENESIS_SPEND_PUBLIC_INPUTS, _>(
        &wrap_genesis_pk,
        WrapCircuit::<GENESIS_SPEND_PUBLIC_INPUTS> {
            inner_vk: genesis_pk_data.vk.clone(),
            inner_proof: Some(genesis_proof),
            inner_public_inputs: Some(genesis_public_inputs),
        },
        &mut rng,
    )
    .unwrap();
    let prove_secs = t.elapsed().as_secs_f64();
    let wrap_genesis_public_inputs = cloakkchain_circuit_wrap::public_input_chunks(&genesis_public_inputs);
    let t = Instant::now();
    assert!(cloakkchain_circuit_wrap::verify(&wrap_genesis_vk, &wrap_genesis_public_inputs, &wrap_genesis_proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    if target_step == 1 {
        println!("  wrapped genesis proof ({prove_secs:.1}s)");
    }
    let stat1 = ProveStats {
        name: "Wrap genesis proof".into(),
        board_size: entries.len(),
        prove_secs,
        verify_ms,
        proof_bytes: ark_serialize_len(&wrap_genesis_proof),
        entry_bytes: entry0_bytes,
        peak_mem_kb: 0,
    };
    if target_step == 1 {
        return stat1;
    }

    // =========================================================================
    // Step 2: Alice discovers her coin and builds her receipt
    // =========================================================================
    if target_step == 2 {
        println!("\n--- Alice scans slot 0, builds her receipt ---");
        let alice_tx = scan_entry(&alice.enc_sk, &genesis_entry).expect("Alice must be able to decrypt slot 0");
        assert!(alice_tx.receives_coin(&alice_coin.commitment()), "Alice's tx must transfer her coin");
        println!("  [{}] discovered coin (value={}) at slot 0", alice.name, alice_coin.value);
    }

    let alice_receipt_board_root =
        compute_root_from_path(merkle_leaf(0, &genesis_entry), 0, &genesis_append_path);
    let (apx, apy) = owner_pk_to_field_pair(&alice.pk_p);

    let alice_receipt_circuit = ReceiptStepCircuit {
        owner_pk_x: Some(apx),
        owner_pk_y: Some(apy),
        coin_commitment: Some(alice_coin.commitment()),
        board_root: Some(alice_receipt_board_root),
        received_at: Some(0),
        wrap_vk: wrap_genesis_vk.clone(),
        wrap_proof: Some(wrap_genesis_proof),
        wrap_public_inputs: Some(genesis_public_inputs),
        entry_nullifier: Some(genesis_entry.nullifier),
        entry_output_commitments: Some(genesis_outputs),
        entry_ciphertext_commitment: Some(entry_ciphertext_commitment(&genesis_entry)),
        received_slot: Some(0),
        append_path: Some(genesis_append_path.clone()),
        parent_nonmembership: Some(empty_tree.prove_non_membership(genesis_entry.nullifier)),
        nullifier_root_at_parent_slot: Some(empty_tree.root()),
    };
    let alice_receipt_public_inputs: [Fr; RECEIPT_PUBLIC_INPUTS] =
        ReceiptStepCircuit::public_inputs(apx, apy, alice_coin.commitment(), alice_receipt_board_root, 0)
            .try_into()
            .unwrap();

    let t = Instant::now();
    let (alice_receipt_pk, alice_receipt_vk) = cloakkchain_circuit_coinproof::setup(wrap_genesis_vk, &mut rng).unwrap();
    let alice_receipt_proof =
        cloakkchain_circuit_coinproof::prove(&alice_receipt_pk, alice_receipt_circuit, &mut rng).unwrap();
    let prove_secs = t.elapsed().as_secs_f64();
    let t = Instant::now();
    assert!(cloakkchain_circuit_coinproof::verify(&alice_receipt_vk, &alice_receipt_public_inputs, &alice_receipt_proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    if target_step == 2 {
        println!("  proved & verified Alice's receipt ({prove_secs:.1}s)");
    }
    let stat2 = ProveStats {
        name: "Alice's receipt".into(),
        board_size: entries.len(),
        prove_secs,
        verify_ms,
        proof_bytes: ark_serialize_len(&alice_receipt_proof),
        entry_bytes: None,
        peak_mem_kb: 0,
    };
    if target_step == 2 {
        return stat2;
    }

    // =========================================================================
    // Step 3: wrap Alice's receipt so her spend circuit can verify it
    // =========================================================================
    let t = Instant::now();
    let (wrap_alice_receipt_pk, wrap_alice_receipt_vk) =
        cloakkchain_circuit_wrap::setup::<RECEIPT_PUBLIC_INPUTS, _>(alice_receipt_vk, &mut rng).unwrap();
    let wrap_alice_receipt_proof = cloakkchain_circuit_wrap::prove::<RECEIPT_PUBLIC_INPUTS, _>(
        &wrap_alice_receipt_pk,
        WrapCircuit::<RECEIPT_PUBLIC_INPUTS> {
            inner_vk: alice_receipt_pk.vk.clone(),
            inner_proof: Some(alice_receipt_proof),
            inner_public_inputs: Some(alice_receipt_public_inputs),
        },
        &mut rng,
    )
    .unwrap();
    let prove_secs = t.elapsed().as_secs_f64();
    let wrap_alice_receipt_public_inputs = cloakkchain_circuit_wrap::public_input_chunks(&alice_receipt_public_inputs);
    let t = Instant::now();
    assert!(cloakkchain_circuit_wrap::verify(&wrap_alice_receipt_vk, &wrap_alice_receipt_public_inputs, &wrap_alice_receipt_proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    if target_step == 3 {
        println!("  wrapped Alice's receipt ({prove_secs:.1}s)");
    }
    let stat3 = ProveStats {
        name: "Wrap Alice's receipt".into(),
        board_size: entries.len(),
        prove_secs,
        verify_ms,
        proof_bytes: ark_serialize_len(&wrap_alice_receipt_proof),
        entry_bytes: None,
        peak_mem_kb: 0,
    };
    if target_step == 3 {
        return stat3;
    }

    // =========================================================================
    // Step 4: Alice spends 1-in-2-out — 40 to Bob, 60 change to herself
    // =========================================================================
    if target_step == 4 {
        println!("\n--- Slot 1: Alice spends to Bob + change ---");
    }
    let bob_coin = coin(0xB1, 40, bob.pk_p);
    let change_coin = coin(0xB2, 60, alice.pk_p);
    let alice_spend_outputs = pad_outputs(&[bob_coin.commitment(), change_coin.commitment()]);

    let alice_spend_append_path = append_path_for_next(&entries);
    let alice_spend_board_root = compute_root_from_path(Fr::from(0u64), entries.len(), &alice_spend_append_path);
    let alice_own_nullifier = poseidon_hash(&[alice_coin.commitment(), fold_owner_scalar(&alice.sk_p)]);
    let mut tree_after_genesis = NullifierTree::new();
    tree_after_genesis.insert(genesis_own_nullifier);

    let alice_spend_circuit = SpendStepCircuit {
        pk_p: Some(alice.pk_p),
        output_commitments: Some(alice_spend_outputs),
        board_root: Some(alice_spend_board_root),
        current_nullifier_root: Some(tree_after_genesis.root()),
        sk_p: Some(alice.sk_p),
        input_coins: [Some(alice_coin.clone()), None],
        output_coins: [Some(bob_coin.clone()), Some(change_coin.clone())],
        entry_position: Some(entries.len() as u64),
        append_path: Some(alice_spend_append_path.clone()),
        own_nullifier_nonmembership: [Some(tree_after_genesis.prove_non_membership(alice_own_nullifier)), None],
        wrap_vk: wrap_alice_receipt_vk.clone(),
        input_receipt_proofs: [Some(wrap_alice_receipt_proof), None],
        input_receipt_public_inputs: [Some(alice_receipt_public_inputs), None],
    };
    let alice_spend_public_inputs: [Fr; GENESIS_SPEND_PUBLIC_INPUTS] = SpendStepCircuit::public_inputs(
        alice.pk_p,
        alice_spend_outputs,
        alice_spend_board_root,
        tree_after_genesis.root(),
    )
    .try_into()
    .unwrap();

    let t = Instant::now();
    let (alice_spend_pk, alice_spend_vk) =
        cloakkchain_circuit_spend::setup_non_genesis(wrap_alice_receipt_vk, &mut rng).unwrap();
    let alice_spend_proof =
        cloakkchain_circuit_spend::prove_non_genesis(&alice_spend_pk, alice_spend_circuit, &mut rng).unwrap();
    let prove_secs = t.elapsed().as_secs_f64();
    let t = Instant::now();
    assert!(cloakkchain_circuit_spend::verify_non_genesis(&alice_spend_vk, &alice_spend_public_inputs, &alice_spend_proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    if target_step == 4 {
        println!("  proved & verified Alice's spend ({prove_secs:.1}s)");
    }
    let stat4 = ProveStats {
        name: "Alice -> Bob + change".into(),
        board_size: entries.len() + 1,
        prove_secs,
        verify_ms,
        proof_bytes: ark_serialize_len(&alice_spend_proof),
        entry_bytes: None,
        peak_mem_kb: 0,
    };
    if target_step == 4 {
        return stat4;
    }

    let (mut tx1, s1, r1) = make_tx(
        1,
        alice.enc_sk,
        &alice.sk_p,
        &[alice_coin.clone()],
        &[(bob_coin.clone(), bob.enc_pk), (change_coin.clone(), alice.enc_pk)],
    );
    tx1.spend_proof = ark_serialize_bytes(&alice_spend_proof);
    let alice_entry = cloakkchain_lib::encrypt_tx(&tx1, &r1, s1);
    entries.push(alice_entry.clone());
    let entry1_bytes = bincode::serialize(&alice_entry).map(|v| v.len()).ok();

    // =========================================================================
    // Step 5: wrap Alice's spend so Bob's receipt circuit can verify it
    // =========================================================================
    let t = Instant::now();
    let (wrap_alice_spend_pk, wrap_alice_spend_vk) =
        cloakkchain_circuit_wrap::setup::<GENESIS_SPEND_PUBLIC_INPUTS, _>(alice_spend_vk, &mut rng).unwrap();
    let wrap_alice_spend_proof = cloakkchain_circuit_wrap::prove::<GENESIS_SPEND_PUBLIC_INPUTS, _>(
        &wrap_alice_spend_pk,
        WrapCircuit::<GENESIS_SPEND_PUBLIC_INPUTS> {
            inner_vk: alice_spend_pk.vk.clone(),
            inner_proof: Some(alice_spend_proof),
            inner_public_inputs: Some(alice_spend_public_inputs),
        },
        &mut rng,
    )
    .unwrap();
    let prove_secs = t.elapsed().as_secs_f64();
    let wrap_alice_spend_public_inputs = cloakkchain_circuit_wrap::public_input_chunks(&alice_spend_public_inputs);
    let t = Instant::now();
    assert!(cloakkchain_circuit_wrap::verify(&wrap_alice_spend_vk, &wrap_alice_spend_public_inputs, &wrap_alice_spend_proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    if target_step == 5 {
        println!("  wrapped Alice's spend ({prove_secs:.1}s)");
    }
    let stat5 = ProveStats {
        name: "Wrap Alice's spend".into(),
        board_size: entries.len(),
        prove_secs,
        verify_ms,
        proof_bytes: ark_serialize_len(&wrap_alice_spend_proof),
        entry_bytes: entry1_bytes,
        peak_mem_kb: 0,
    };
    if target_step == 5 {
        return stat5;
    }

    // =========================================================================
    // Step 6: Bob discovers his coin and builds his receipt — a "second
    // generation" ReceiptStepCircuit setup: it recursively verifies a
    // wrapped *spend* proof (Alice's), not a wrapped genesis proof. Same
    // Rust circuit type as Alice's receipt, just keyed to a different
    // wrap_vk (see circuit-coinproof's module doc comment).
    // =========================================================================
    if target_step == 6 {
        println!("\n--- Bob scans slot 1, builds his receipt ---");
        let bob_tx = scan_entry(&bob.enc_sk, &alice_entry).expect("Bob must be able to decrypt slot 1");
        assert!(bob_tx.receives_coin(&bob_coin.commitment()));
        println!("  [{}] discovered coin (value={}) at slot 1", bob.name, bob_coin.value);
    }

    let bob_receipt_board_root =
        compute_root_from_path(merkle_leaf(1, &alice_entry), 1, &alice_spend_append_path);
    let (bpx, bpy) = owner_pk_to_field_pair(&bob.pk_p);

    let bob_receipt_circuit = ReceiptStepCircuit {
        owner_pk_x: Some(bpx),
        owner_pk_y: Some(bpy),
        coin_commitment: Some(bob_coin.commitment()),
        board_root: Some(bob_receipt_board_root),
        received_at: Some(1),
        wrap_vk: wrap_alice_spend_vk.clone(),
        wrap_proof: Some(wrap_alice_spend_proof),
        wrap_public_inputs: Some(alice_spend_public_inputs),
        entry_nullifier: Some(alice_entry.nullifier),
        entry_output_commitments: Some(alice_spend_outputs),
        entry_ciphertext_commitment: Some(entry_ciphertext_commitment(&alice_entry)),
        received_slot: Some(1),
        append_path: Some(alice_spend_append_path.clone()),
        parent_nonmembership: Some(tree_after_genesis.prove_non_membership(alice_entry.nullifier)),
        nullifier_root_at_parent_slot: Some(tree_after_genesis.root()),
    };
    let bob_receipt_public_inputs: [Fr; RECEIPT_PUBLIC_INPUTS] =
        ReceiptStepCircuit::public_inputs(bpx, bpy, bob_coin.commitment(), bob_receipt_board_root, 1)
            .try_into()
            .unwrap();

    let t = Instant::now();
    let (bob_receipt_pk, bob_receipt_vk) = cloakkchain_circuit_coinproof::setup(wrap_alice_spend_vk, &mut rng).unwrap();
    let bob_receipt_proof =
        cloakkchain_circuit_coinproof::prove(&bob_receipt_pk, bob_receipt_circuit, &mut rng).unwrap();
    let prove_secs = t.elapsed().as_secs_f64();
    let t = Instant::now();
    assert!(cloakkchain_circuit_coinproof::verify(&bob_receipt_vk, &bob_receipt_public_inputs, &bob_receipt_proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    if target_step == 6 {
        println!("  proved & verified Bob's receipt ({prove_secs:.1}s)");
    }
    let stat6 = ProveStats {
        name: "Bob's receipt (gen 2)".into(),
        board_size: entries.len(),
        prove_secs,
        verify_ms,
        proof_bytes: ark_serialize_len(&bob_receipt_proof),
        entry_bytes: None,
        peak_mem_kb: 0,
    };
    if target_step == 6 {
        return stat6;
    }

    // =========================================================================
    // Step 7: wrap Bob's receipt so his spend circuit can verify it
    // =========================================================================
    let t = Instant::now();
    let (wrap_bob_receipt_pk, wrap_bob_receipt_vk) =
        cloakkchain_circuit_wrap::setup::<RECEIPT_PUBLIC_INPUTS, _>(bob_receipt_vk, &mut rng).unwrap();
    let wrap_bob_receipt_proof = cloakkchain_circuit_wrap::prove::<RECEIPT_PUBLIC_INPUTS, _>(
        &wrap_bob_receipt_pk,
        WrapCircuit::<RECEIPT_PUBLIC_INPUTS> {
            inner_vk: bob_receipt_pk.vk.clone(),
            inner_proof: Some(bob_receipt_proof),
            inner_public_inputs: Some(bob_receipt_public_inputs),
        },
        &mut rng,
    )
    .unwrap();
    let prove_secs = t.elapsed().as_secs_f64();
    let wrap_bob_receipt_public_inputs = cloakkchain_circuit_wrap::public_input_chunks(&bob_receipt_public_inputs);
    let t = Instant::now();
    assert!(cloakkchain_circuit_wrap::verify(&wrap_bob_receipt_vk, &wrap_bob_receipt_public_inputs, &wrap_bob_receipt_proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    if target_step == 7 {
        println!("  wrapped Bob's receipt ({prove_secs:.1}s)");
    }
    let stat7 = ProveStats {
        name: "Wrap Bob's receipt".into(),
        board_size: entries.len(),
        prove_secs,
        verify_ms,
        proof_bytes: ark_serialize_len(&wrap_bob_receipt_proof),
        entry_bytes: None,
        peak_mem_kb: 0,
    };
    if target_step == 7 {
        return stat7;
    }

    // =========================================================================
    // Step 8: Bob spends his 40 units to Carol
    // =========================================================================
    if target_step == 8 {
        println!("\n--- Slot 2: Bob spends to Carol ---");
    }
    let carol_coin = coin(0xC1, 40, carol.pk_p);
    let bob_spend_outputs = pad_outputs(&[carol_coin.commitment()]);

    let bob_spend_append_path = append_path_for_next(&entries);
    let bob_spend_board_root = compute_root_from_path(Fr::from(0u64), entries.len(), &bob_spend_append_path);
    let bob_own_nullifier = poseidon_hash(&[bob_coin.commitment(), fold_owner_scalar(&bob.sk_p)]);
    let mut tree_after_alice_spend = tree_after_genesis.clone();
    tree_after_alice_spend.insert(alice_own_nullifier);

    let bob_spend_circuit = SpendStepCircuit {
        pk_p: Some(bob.pk_p),
        output_commitments: Some(bob_spend_outputs),
        board_root: Some(bob_spend_board_root),
        current_nullifier_root: Some(tree_after_alice_spend.root()),
        sk_p: Some(bob.sk_p),
        input_coins: [Some(bob_coin.clone()), None],
        output_coins: [Some(carol_coin.clone()), None],
        entry_position: Some(entries.len() as u64),
        append_path: Some(bob_spend_append_path),
        own_nullifier_nonmembership: [Some(tree_after_alice_spend.prove_non_membership(bob_own_nullifier)), None],
        wrap_vk: wrap_bob_receipt_vk.clone(),
        input_receipt_proofs: [Some(wrap_bob_receipt_proof), None],
        input_receipt_public_inputs: [Some(bob_receipt_public_inputs), None],
    };
    let bob_spend_public_inputs = SpendStepCircuit::public_inputs(
        bob.pk_p,
        bob_spend_outputs,
        bob_spend_board_root,
        tree_after_alice_spend.root(),
    );

    let t = Instant::now();
    let (bob_spend_pk, bob_spend_vk) =
        cloakkchain_circuit_spend::setup_non_genesis(wrap_bob_receipt_vk, &mut rng).unwrap();
    let bob_spend_proof =
        cloakkchain_circuit_spend::prove_non_genesis(&bob_spend_pk, bob_spend_circuit, &mut rng).unwrap();
    let prove_secs = t.elapsed().as_secs_f64();
    let t = Instant::now();
    assert!(cloakkchain_circuit_spend::verify_non_genesis(&bob_spend_vk, &bob_spend_public_inputs, &bob_spend_proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    if target_step == 8 {
        println!("  proved & verified Bob's spend ({prove_secs:.1}s)");
    }
    let stat8 = ProveStats {
        name: "Bob -> Carol (gen 2)".into(),
        board_size: entries.len() + 1,
        prove_secs,
        verify_ms,
        proof_bytes: ark_serialize_len(&bob_spend_proof),
        entry_bytes: None,
        peak_mem_kb: 0,
    };
    if target_step == 8 {
        let (mut tx2, s2, r2) =
            make_tx(2, bob.enc_sk, &bob.sk_p, &[bob_coin.clone()], &[(carol_coin.clone(), carol.enc_pk)]);
        tx2.spend_proof = ark_serialize_bytes(&bob_spend_proof);
        let bob_entry = cloakkchain_lib::encrypt_tx(&tx2, &r2, s2);

        println!("\n--- Carol scans slot 2 ---");
        let carol_tx = scan_entry(&carol.enc_sk, &bob_entry).expect("Carol must be able to decrypt slot 2");
        assert!(carol_tx.receives_coin(&carol_coin.commitment()));
        println!("  [{}] discovered coin (value={}) at slot 2 — end of chain (no further receipt built)", carol.name, carol_coin.value);

        return stat8;
    }

    unreachable!("target_step out of range: {target_step}");
}
