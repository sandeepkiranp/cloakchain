//! Host driver for the MNT-native cloakkchain relations (Phase 4 of the
//! MNT-native port, extended with the full genesis->Alice->Bob->Carol chain and
//! the serial-number copy fix below).
//!
//! Demo chain: genesis mints to Alice, Alice spends 1-in/2-out (40 to Bob,
//! 60 change back to herself — real value conservation over a genuine sum,
//! not just equality) directly recursively verifying genesis's own wrapped
//! proof, then Bob spends his 40 units to Carol directly recursively
//! verifying Alice's own wrapped spend proof. There is no separate
//! "receipt" proof/step: each spend proves, against its own anchor (a state
//! from before it was posted), that the entry which created its input coin is
//! genuinely included and that nothing in that entry's window spoils it — see
//! `circuit-spend`'s module doc comment.
//!
//! The chain runs under the reviewers' attack: after Alice has proved but before
//! her carrier lands, a third party gets a copy of her serial number ordered
//! first. Her proof stays valid, since it's anchored before the copy; Bob
//! accepts her carrier regardless, and opens the copy in his own proof.
//!
//! Every wallet's view is a [`History`] replayed blindly from the board: the
//! roots a leaf embeds are computed there, and are never posted.
//!
//! `--prove` still builds the whole chain once, in order, in this process
//! (exactly like a non-isolated driver would) — but each step's actual
//! `setup`+`prove` call is farmed out to a fresh subprocess
//! (`--internal-kind`/`--internal-witness`/`--internal-output`, hidden
//! flags), so the peak-memory column reflects that step's own footprint
//! via the kernel's `VmHWM` tracker rather than a same-process running
//! high-water mark. Only the small, already-`CanonicalSerialize`-able
//! witness circuit struct crosses into the subprocess and only the
//! resulting `(VerifyingKey, Proof)` crosses back — the parent still holds
//! every other piece of state (board entries, history, prior proofs) exactly
//! as it always did, so nothing is ever recomputed twice.
//!
//! ```shell
//! RUST_LOG=info cargo run --release -- --execute   # genesis circuit's constraint check only, no proving
//! RUST_LOG=info cargo run --release -- --prove     # full chain, five real GM17 proofs
//! ```

use std::time::Instant;

use ark_ec::pairing::Pairing;
use ark_gm17::{Proof, VerifyingKey};
use ark_mnt4_753::MNT4_753;
use ark_mnt6_753::MNT6_753;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::{rngs::StdRng, SeedableRng};
use clap::Parser;
use cloakkchain_circuit_spend::{
    spend_public_inputs, GenesisSpendCircuit, SpendCoreWitness, SpendStepCircuit, MAX_INPUTS, MAX_OUTPUTS,
    SPEND_PUBLIC_INPUT_COUNT,
};
use cloakkchain_circuit_wrap::WrapCircuit;
use cloakkchain_lib::{
    check_receipt, derive_coin_vpk, derive_enc_pk, derive_nullifier, derive_owner_pk, encrypt_tx, genesis_pk,
    genesis_sk, scan_entry, Anchor, BoardEntry, Coin, CoinSignature, Fr, History, OwnerPk, OwnerScalar,
    SpendPublicValues, Transaction, EK_SALT,
};

// ---- CLI args ---------------------------------------------------------------

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(long)]
    execute: bool,
    #[arg(long)]
    prove: bool,
    /// Ad hoc: real GM17 setup+prove+verify at whichever MAX_INPUTS/
    /// MAX_OUTPUTS shape circuit-spend is currently compiled with — for
    /// filling in the paper's 2x2 grid cells. See `run_prove_grid_cell`'s
    /// doc comment. Not part of the normal demo.
    #[arg(long)]
    grid_cell: bool,
    /// Hidden: re-invokes this binary as a single setup+prove subprocess
    /// (see the module doc comment). One of "genesis", "spend_non_genesis",
    /// "wrap". Not for direct use.
    #[arg(long, hide = true)]
    internal_kind: Option<String>,
    /// Hidden: path to the serialized witness circuit struct.
    #[arg(long, hide = true)]
    internal_witness: Option<String>,
    /// Hidden: where to write the resulting (VerifyingKey, Proof) pair.
    #[arg(long, hide = true)]
    internal_output: Option<String>,
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
    Coin { value, rand: Fr::from(seed as u64 + 1000), owner_pk }
}

/// Build a Transaction using X25519 note encryption derived from a
/// per-transaction session key. Returns `(tx, session_key, recipient_enc_pks)`
/// — pass to `encrypt_tx`, which signs the result. `vpk` and `anchor` go inside
/// the ciphertext, never on the wire.
fn make_tx(
    id: u64,
    sender_enc_sk: [u8; 32],
    vpk: OwnerPk,
    anchor: Anchor,
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
    let recipient_enc_pks: Vec<[u8; 32]> = outputs.iter().map(|(_, rpk)| *rpk).collect();
    let output_commitments: Vec<Fr> = outputs.iter().map(|(c, _)| c.commitment()).collect();
    let note_encs: Vec<Vec<u8>> = outputs
        .iter()
        .enumerate()
        .map(|(i, (c, _))| cloakkchain_lib::build_note_enc(&session_key, i, c))
        .collect();
    let tx = Transaction { id, output_commitments, note_encs, vpk, anchor, spend_proof: vec![] };
    (tx, session_key, recipient_enc_pks)
}

// ---- Subprocess isolation + peak-memory tracking -----------------------------
//
// Each step's `setup`+`prove` call runs in a fresh child process so its
// peak-memory reading reflects only that step's own working set, not a
// same-process running high-water mark carried over from earlier steps.
// Only the witness circuit struct crosses into the child and only the
// resulting `(VerifyingKey, Proof)` crosses back — everything else (board
// state, history, prior proofs) stays in this parent process for the
// whole run, so no step is ever computed twice.

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

/// Synthesizes `circuit` on a fresh `ConstraintSystem` in the same
/// `SynthesisMode::Setup` mode `GM17::circuit_specific_setup` itself
/// uses, and returns the resulting constraint count. Cheap — synthesis
/// alone is native field arithmetic (no FFTs/pairings/proving), so this
/// runs in a few seconds even for the ~600K-constraint spend circuit.
fn count_constraints<F: ark_ff::Field, C: ConstraintSynthesizer<F> + Clone>(circuit: &C) -> usize {
    let cs = ConstraintSystem::<F>::new_ref();
    cs.set_mode(ark_relations::r1cs::SynthesisMode::Setup);
    circuit.clone().generate_constraints(cs.clone()).expect("synthesize constraints for counting");
    cs.num_constraints()
}

fn write_vk_proof<E: Pairing>(vk: &VerifyingKey<E>, proof: &Proof<E>, path: &std::path::Path) {
    let mut buf = Vec::new();
    vk.serialize_compressed(&mut buf).expect("serialize verifying key");
    proof.serialize_compressed(&mut buf).expect("serialize proof");
    std::fs::write(path, buf).expect("write output file");
}

fn read_vk_proof<E: Pairing>(path: &std::path::Path) -> (VerifyingKey<E>, Proof<E>) {
    let bytes = std::fs::read(path).expect("read output file");
    let mut cursor = &bytes[..];
    let vk = VerifyingKey::<E>::deserialize_compressed(&mut cursor).expect("deserialize verifying key");
    let proof = Proof::<E>::deserialize_compressed(&mut cursor).expect("deserialize proof");
    (vk, proof)
}

/// Spawn a fresh copy of this binary to run one step's `setup`+`prove` in
/// isolation. `circuit` is serialized to a temp file, the child deserializes
/// it, calls the appropriate crate's `setup`/`prove` (dispatched by `kind`
/// in `main`'s hidden-flag branch below), and writes back `(VerifyingKey,
/// Proof)`. Returns that pair plus the wall-clock time and peak RSS of the
/// whole subprocess.
fn run_step_subprocess<C: CanonicalSerialize, E: Pairing>(
    kind: &str,
    circuit: &C,
) -> (VerifyingKey<E>, Proof<E>, f64, u64) {
    let witness_path = std::env::temp_dir().join(format!("cloakkchain_{kind}_witness.bin"));
    let output_path = std::env::temp_dir().join(format!("cloakkchain_{kind}_output.bin"));

    let mut witness_buf = Vec::new();
    circuit.serialize_compressed(&mut witness_buf).expect("serialize witness");
    std::fs::write(&witness_path, witness_buf).expect("write witness file");

    let exe = std::env::current_exe().expect("current_exe");
    let mut cmd = std::process::Command::new(&exe);
    cmd.args([
        "--internal-kind",
        kind,
        "--internal-witness",
        witness_path.to_str().expect("temp path is valid UTF-8"),
        "--internal-output",
        output_path.to_str().expect("temp path is valid UTF-8"),
    ]);

    let t = Instant::now();
    let child = cmd.spawn().expect("spawn proving subprocess");
    let (status, peak_mem_kb) = wait_tracking_peak_memory(child);
    let prove_secs = t.elapsed().as_secs_f64();
    assert!(status.success(), "subprocess for {kind} exited with {status}");

    let (vk, proof) = read_vk_proof::<E>(&output_path);
    let _ = std::fs::remove_file(&witness_path);
    let _ = std::fs::remove_file(&output_path);
    (vk, proof, prove_secs, peak_mem_kb.unwrap_or(0))
}

/// Entry point when this binary is re-invoked as a `--internal-kind`
/// subprocess: deserialize the witness, run the matching crate's
/// `setup`+`prove`, write back `(VerifyingKey, Proof)`. Each circuit
/// already carries whatever "setup key" it needs (`wrap_vk`/`inner_vk`) as
/// one of its own fields, so no separate parameter needs to travel
/// alongside the witness.
fn run_internal_step(kind: &str, witness_path: &str, output_path: &str) {
    let witness_bytes = std::fs::read(witness_path).expect("read witness file");
    let mut rng = StdRng::seed_from_u64(0x636c6f616b);
    let output_path = std::path::Path::new(output_path);

    match kind {
        "genesis" => {
            let circuit = GenesisSpendCircuit::deserialize_compressed(&witness_bytes[..]).expect("deserialize witness");
            let (pk, vk) = cloakkchain_circuit_spend::setup(&mut rng).unwrap();
            let proof = cloakkchain_circuit_spend::prove(&pk, circuit, &mut rng).unwrap();
            write_vk_proof::<MNT4_753>(&vk, &proof, output_path);
        }
        "spend_non_genesis" => {
            let circuit = SpendStepCircuit::deserialize_compressed(&witness_bytes[..]).expect("deserialize witness");
            let wrap_vk = circuit.wrap_vk.clone();
            let (pk, vk) = cloakkchain_circuit_spend::setup_non_genesis(wrap_vk, &mut rng).unwrap();
            let proof = cloakkchain_circuit_spend::prove_non_genesis(&pk, circuit, &mut rng).unwrap();
            write_vk_proof::<MNT4_753>(&vk, &proof, output_path);
        }
        "wrap" => {
            let circuit = WrapCircuit::<SPEND_PUBLIC_INPUT_COUNT>::deserialize_compressed(&witness_bytes[..])
                .expect("deserialize witness");
            let inner_vk = circuit.inner_vk.clone();
            let (pk, vk) = cloakkchain_circuit_wrap::setup::<SPEND_PUBLIC_INPUT_COUNT, _>(inner_vk, &mut rng).unwrap();
            let proof = cloakkchain_circuit_wrap::prove::<SPEND_PUBLIC_INPUT_COUNT, _>(&pk, circuit, &mut rng).unwrap();
            write_vk_proof::<MNT6_753>(&vk, &proof, output_path);
        }
        other => panic!("unknown --internal-kind {other}"),
    }
}

// ---- Statistics --------------------------------------------------------------

struct ProveStats {
    name: String,
    board_size: usize,
    constraints: usize,
    prove_secs: f64,
    verify_ms: f64,
    proof_bytes: usize,
    entry_bytes: Option<usize>,
    peak_mem_kb: u64,
}

fn fmt_constraints(c: usize) -> String {
    if c >= 1_000_000 {
        format!("{:.2}M", c as f64 / 1_000_000.0)
    } else if c >= 1_000 {
        format!("{:.1}K", c as f64 / 1_000.0)
    } else {
        format!("{c}")
    }
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
    let w = 122;
    println!("\n{}", "=".repeat(w));
    println!("  Proof Statistics");
    println!("{}", "=".repeat(w));
    println!(
        "{:<28} {:>5}  {:>11}  {:>9}  {:>10}  {:>11}  {:>11}  {:>11}",
        "Step", "Board", "Constraints", "Prove", "Verify", "Proof", "Entry", "Peak Mem"
    );
    println!("{}", "-".repeat(w));
    let (mut tp, mut tv) = (0f64, 0f64);
    for s in stats {
        // Exact byte count, not `fmt_bytes`'s rounded KB/MB — entry size is
        // small enough (low KB) that rounding loses precision worth keeping
        // (e.g. distinguishing 1043 B from 1050 B), unlike proof size
        // (already sub-1KB, so `fmt_bytes` prints it exactly anyway) or peak
        // memory (large enough that KB/MB rounding doesn't matter).
        let entry_col = s.entry_bytes.map_or("          —".into(), |b| format!("{:>8} B", b));
        println!(
            "{:<28} {:>5}  {:>11} {:>7.1} s  {:>8.1} ms  {:>11}  {}  {:>11}",
            s.name,
            s.board_size,
            fmt_constraints(s.constraints),
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

    if let Some(kind) = args.internal_kind {
        let witness_path = args.internal_witness.expect("--internal-witness required with --internal-kind");
        let output_path = args.internal_output.expect("--internal-output required with --internal-kind");
        run_internal_step(&kind, &witness_path, &output_path);
        return;
    }

    if args.grid_cell {
        run_prove_grid_cell();
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
/// satisfies `GenesisSpendCircuit`'s constraints, with no GM17 setup or
/// proving. This is the only circuit in the chain that doesn't recursively
/// verify another proof, so it's the only one a "no real proving" mode can
/// meaningfully check in isolation — `SpendStepCircuit` needs a genuine
/// inner (parent) proof to exist as a witness regardless (there's no
/// zkVM-style mock-mode equivalent for a GM17 recursive-verification
/// gadget), so exercising it for real is what `--prove` is for.
fn run_execute(genesis: &Party, genesis_coin: &Coin, alice_coin: &Coin) {
    println!("--execute: checking GenesisSpendCircuit's constraints only (no proving)");

    let history = History::new();
    let circuit = GenesisSpendCircuit {
        core: core_witness(&history, genesis, genesis_coin, std::slice::from_ref(alice_coin)),
    };

    let cs = ConstraintSystem::<Fr>::new_ref();
    circuit.generate_constraints(cs.clone()).expect("synthesize constraints");
    let satisfied = cs.is_satisfied().expect("check satisfiability");
    println!("  constraints: {}", cs.num_constraints());
    println!("  satisfied:   {satisfied}");
    assert!(satisfied);
    println!("\nRun --prove for the full chain (five real GM17 proofs).");
}

// ---- One step of the chain ---------------------------------------------------

/// A spend whose proof exists, as both the poster and its recipients see it.
struct ProvenSpend {
    entry: BoardEntry,
    tx: Transaction,
    public_values: SpendPublicValues,
    vk: VerifyingKey<MNT4_753>,
    proof: Proof<MNT4_753>,
}

/// A spend's proof re-proved on the other curve, for the next spend to verify.
struct WrappedSpend {
    vk: VerifyingKey<MNT6_753>,
    proof: Proof<MNT6_753>,
}

/// The spend relation's witness, anchored at `history`'s current state.
fn core_witness(history: &History, sender: &Party, input: &Coin, outputs: &[Coin]) -> SpendCoreWitness {
    let size = history.len();
    let nullifier = derive_nullifier(input.commitment(), &sender.sk_p);
    SpendCoreWitness::new(
        sender.sk_p,
        input.clone(),
        outputs,
        history.anchor_at(size).expect("the current state exists"),
        history.nullifier_tree_at(size).prove_non_membership(nullifier),
    )
}

/// Prove `sender`'s spend at `history`'s current state and build its entry,
/// without posting it: nothing here depends on where it ends up landing.
/// `parent` is the coin's creating spend, its slot, and its wrapped proof; `None`
/// is a genesis mint. Construction order matters: prove, encrypt the proof into
/// the ciphertext, then sign last (inside `encrypt_tx`).
fn prove_spend(
    name: &str,
    history: &History,
    sender: &Party,
    input: &Coin,
    outputs: &[(Coin, [u8; 32])],
    parent: Option<(&ProvenSpend, usize, &WrappedSpend)>,
    stats: &mut Vec<ProveStats>,
) -> ProvenSpend {
    let output_coins: Vec<Coin> = outputs.iter().map(|(c, _)| c.clone()).collect();
    let core = core_witness(history, sender, input, &output_coins);
    let public_values = core.public_values().expect("core_witness sets every public value");
    let public_inputs = spend_public_inputs(&public_values);

    let (vk, proof, prove_secs, peak_mem_kb, constraints) = match parent {
        None => {
            let circuit = GenesisSpendCircuit { core };
            let (vk, proof, secs, mem) = run_step_subprocess::<_, MNT4_753>("genesis", &circuit);
            (vk, proof, secs, mem, count_constraints(&circuit))
        }
        Some((parent, slot, wrapped)) => {
            let witness = history.parent_witness(slot, &parent.public_values, &parent.tx.vpk, history.len());
            let circuit = SpendStepCircuit {
                core,
                wrap_vk: wrapped.vk.clone(),
                input_parent_proofs: [Some(wrapped.proof.clone())],
                input_parents: [Some(witness)],
            };
            let (vk, proof, secs, mem) = run_step_subprocess::<_, MNT4_753>("spend_non_genesis", &circuit);
            (vk, proof, secs, mem, count_constraints(&circuit))
        }
    };
    let t = Instant::now();
    assert!(cloakkchain_circuit_spend::verify(&vk, &public_inputs, &proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    println!("  Proved in {prove_secs:.1}s, verified in {verify_ms:.1}ms.");

    let commitment = input.commitment();
    let (mut tx, session_key, recipients) = make_tx(
        stats.len() as u64,
        sender.enc_sk,
        derive_coin_vpk(&sender.sk_p, commitment),
        public_values.anchor.clone(),
        outputs,
    );
    tx.spend_proof = ark_serialize_bytes(&proof);
    let entry = encrypt_tx(&tx, commitment, &sender.sk_p, &recipients, session_key);

    stats.push(ProveStats {
        name: name.into(),
        board_size: history.len(),
        constraints,
        prove_secs,
        verify_ms,
        proof_bytes: ark_serialize_len(&proof),
        entry_bytes: bincode::serialize(&entry).map(|v| v.len()).ok(),
        peak_mem_kb,
    });
    ProvenSpend { entry, tx, public_values, vk, proof }
}

/// Wrap `spend`'s proof so the next spend, back on MNT4-753, can recursively
/// verify it directly — no receipt layer.
fn wrap_spend(name: &str, spend: &ProvenSpend, history: &History, stats: &mut Vec<ProveStats>) -> WrappedSpend {
    let public_inputs = spend_public_inputs(&spend.public_values);
    let circuit = WrapCircuit::<SPEND_PUBLIC_INPUT_COUNT> {
        inner_vk: spend.vk.clone(),
        inner_proof: Some(spend.proof.clone()),
        inner_public_inputs: Some(public_inputs),
    };
    let (vk, proof, prove_secs, peak_mem_kb) = run_step_subprocess::<_, MNT6_753>("wrap", &circuit);
    let chunks = cloakkchain_circuit_wrap::public_input_chunks(&public_inputs);
    let t = Instant::now();
    assert!(cloakkchain_circuit_wrap::verify(&vk, &chunks, &proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    println!("  Wrapped in {prove_secs:.1}s, verified in {verify_ms:.1}ms.");
    stats.push(ProveStats {
        name: name.into(),
        board_size: history.len(),
        constraints: count_constraints(&circuit),
        prove_secs,
        verify_ms,
        proof_bytes: ark_serialize_len(&proof),
        entry_bytes: None,
        peak_mem_kb,
    });
    WrappedSpend { vk, proof }
}

/// `recipient` finds its coin in the carrier at `slot` and runs the off-circuit
/// acceptance check against its own replay, verifying the real proof.
fn receive(recipient: &Party, coin: &Coin, spend: &ProvenSpend, slot: usize, history: &History) {
    println!("\n--- {} scans slot {slot} ---", recipient.name);
    let tx = scan_entry(&recipient.enc_sk, &spend.entry).expect("the recipient must be able to decrypt its carrier");
    assert!(tx.receives_coin(&coin.commitment()), "the carrier must transfer the recipient's coin");
    check_receipt(history, slot, &spend.entry, &tx, |public_values, proof_bytes| {
        let proof = Proof::<MNT4_753>::deserialize_compressed(proof_bytes).expect("deserialize proof");
        cloakkchain_circuit_spend::verify(&spend.vk, &spend_public_inputs(public_values), &proof).unwrap()
    })
    .expect("the recipient must accept its carrier");
    println!("  [{}] accepted coin (value={}) at slot {slot}", recipient.name, coin.value);
}

/// What the reviewers' attack posts: someone else's serial number on an entry
/// of the attacker's own. Needs no secrets, and every wallet inserts it blindly.
fn copy_of_serial_number(nullifier: Fr) -> BoardEntry {
    BoardEntry {
        ciphertext: vec![0xCC; 64],
        ek_pk: [0xCC; 32],
        key_encs: vec![[0xCC; 32]],
        nullifier,
        output_commitments: vec![Fr::from(999u64)],
        signature: CoinSignature { c: Fr::from(1u64), s: OwnerScalar::from(1u64) },
    }
}

fn run_prove() {
    let mut stats: Vec<ProveStats> = Vec::new();
    let mut history = History::new();

    let genesis = Party::genesis();
    let alice = Party::new("Alice", 1);
    let bob = Party::new("Bob", 2);
    let carol = Party::new("Carol", 3);

    // =========================================================================
    // Slot 0: genesis mints 100 units to Alice
    // =========================================================================
    println!("--- Slot 0: Genesis mints 100 units to Alice ---");
    println!("  Proving: pk_p is the fixed genesis key, the mint's serial number and per-coin key are correctly derived, and the serial number is absent at the anchor.");
    let genesis_coin = coin(0xA1, 100, genesis.pk_p);
    let alice_coin = coin(0xA2, 100, alice.pk_p);
    let mint = prove_spend(
        "Genesis mint",
        &history,
        &genesis,
        &genesis_coin,
        &[(alice_coin.clone(), alice.enc_pk)],
        None,
        &mut stats,
    );
    let mint_slot = history.append(&mint.entry);

    println!("  Wrapping the genesis proof: re-verifies it on the other curve (MNT6-753) and re-exposes its public inputs as small chunks, so Alice's spend circuit (back on MNT4-753) can recursively check it.");
    let wrapped_mint = wrap_spend("Wrap genesis proof", &mint, &history, &mut stats);
    receive(&alice, &alice_coin, &mint, mint_slot, &history);

    // =========================================================================
    // Alice spends 1-in-2-out — 40 to Bob, 60 change to herself
    // =========================================================================
    println!("\n--- Alice spends to Bob (40) + change back to herself (60), anchored at the current state ---");
    println!("  Proving: Alice owns the input coin, its serial number is absent at her anchor, value conservation holds (100 in = 40 + 60 out), and the mint under her anchor is genuine: its anchor is real, its signature valid, and its window clean.");
    let bob_coin = coin(0xB1, 40, bob.pk_p);
    let change_coin = coin(0xB2, 60, alice.pk_p);
    let alice_spend = prove_spend(
        "Alice -> Bob + change",
        &history,
        &alice,
        &alice_coin,
        &[(bob_coin.clone(), bob.enc_pk), (change_coin.clone(), alice.enc_pk)],
        Some((&mint, mint_slot, &wrapped_mint)),
        &mut stats,
    );

    // =========================================================================
    // The reviewers' attack: a copy of Alice's serial number gets ordered first
    // =========================================================================
    println!("\n--- Slot 1: a third party posts a copy of Alice's serial number ---");
    let copy_slot = history.append(&copy_of_serial_number(alice_spend.entry.nullifier));
    println!("  Landed at slot {copy_slot}, ahead of Alice's carrier. Her proof doesn't need redoing: it's anchored before the copy.");

    println!("\n--- Slot 2: Alice's carrier lands ---");
    let alice_slot = history.append(&alice_spend.entry);
    println!("  Wrapping Alice's spend so Bob's spend circuit (back on MNT4-753) can recursively verify it.");
    let wrapped_alice = wrap_spend("Wrap Alice's spend", &alice_spend, &history, &mut stats);
    receive(&bob, &bob_coin, &alice_spend, alice_slot, &history);

    // =========================================================================
    // Slot 3: Bob spends his 40 units to Carol
    // =========================================================================
    println!("\n--- Slot 3: Bob spends his 40 units to Carol ---");
    println!("  Proving: Bob owns the input coin, its serial number is absent at his anchor, value conservation holds (40 in = 40 out), and Alice's spend under his anchor is genuine: in particular, the copy in her window carries an invalid signature.");
    let carol_coin = coin(0xC1, 40, carol.pk_p);
    let bob_spend = prove_spend(
        "Bob -> Carol",
        &history,
        &bob,
        &bob_coin,
        &[(carol_coin.clone(), carol.enc_pk)],
        Some((&alice_spend, alice_slot, &wrapped_alice)),
        &mut stats,
    );
    let bob_slot = history.append(&bob_spend.entry);
    receive(&carol, &carol_coin, &bob_spend, bob_slot, &history);
    println!("  End of chain.");

    print_prove_table(&stats);
}

// ---- Grid-cell diagnostic (paper results) ------------------------------------
//
// Ad hoc scenario for measuring *real* GM17 proving stats (constraints,
// prove time, verify time, proof size, subprocess-isolated peak memory) at
// whichever MAX_OUTPUTS shape circuit-spend currently happens to be compiled
// with. `run_prove`'s demo chain only ever exercises one compiled shape at a
// time (the committed baseline); this function exists so the same measurement
// methodology (real proving, subprocess-isolated memory) can be pointed at the
// other cells of the grid by temporarily editing that crate's MAX_OUTPUTS const
// (never committed) and rerunning `--grid-cell`. MAX_INPUTS stays 1 until
// `BoardEntry` holds one serial number and signature per input: `circuit-spend`
// refuses to compile otherwise.
//
// Scenario: Alice receives one coin from a genesis mint, then spends it into
// MAX_OUTPUTS outputs (Bob gets 40 plus change back to herself if
// MAX_OUTPUTS>1, otherwise Bob gets the full 100).
//
// Alice's spend isn't posted, since nothing downstream spends her new outputs.
fn run_prove_grid_cell() {
    println!("=== Grid cell: MAX_INPUTS={MAX_INPUTS} MAX_OUTPUTS={MAX_OUTPUTS} ===");

    let mut stats: Vec<ProveStats> = Vec::new();
    let mut history = History::new();

    let genesis = Party::genesis();
    let alice = Party::new("Alice", 1);
    let bob = Party::new("Bob", 2);

    println!("\n--- Genesis mint: 100 units to Alice ---");
    let alice_coin = coin(0xB0, 100, alice.pk_p);
    let mint = prove_spend(
        "Genesis mint",
        &history,
        &genesis,
        &coin(0xA0, 100, genesis.pk_p),
        &[(alice_coin.clone(), alice.enc_pk)],
        None,
        &mut stats,
    );
    let mint_slot = history.append(&mint.entry);
    let wrapped_mint = wrap_spend("Wrap genesis mint", &mint, &history, &mut stats);

    println!("\n--- Alice spends {MAX_INPUTS} input(s) into {MAX_OUTPUTS} output(s) ---");
    let bob_val = if MAX_OUTPUTS > 1 { 40 } else { 100 };
    let mut outputs = vec![(coin(0xC0, bob_val, bob.pk_p), bob.enc_pk)];
    if MAX_OUTPUTS > 1 {
        outputs.push((coin(0xC1, 100 - bob_val, alice.pk_p), alice.enc_pk));
    }
    prove_spend(
        &format!("Alice's spend ({MAX_INPUTS}-in-{MAX_OUTPUTS}-out)"),
        &history,
        &alice,
        &alice_coin,
        &outputs,
        Some((&mint, mint_slot, &wrapped_mint)),
        &mut stats,
    );

    print_prove_table(&stats);
    println!("\n=== Grid cell done: MAX_INPUTS={MAX_INPUTS} MAX_OUTPUTS={MAX_OUTPUTS} ===");
}
