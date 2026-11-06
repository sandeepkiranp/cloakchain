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
//! her carrier lands, a third party gets `--copies` copies of her serial number
//! ordered first. Her proof stays valid, since it's anchored before them; Bob
//! accepts her carrier regardless, folds the copies into her proof's statement
//! (one fold proof per `FOLD_BATCH` copies, no cap), and spends onward from the
//! last fold.
//!
//! Every wallet's view is a [`History`] replayed blindly from the board: the
//! roots a leaf embeds are computed there, and are never posted.
//!
//! One setup per circuit serves the whole chain, and it runs once, up front, in
//! its own subprocess: that subprocess keeps the proving key on disk and hands
//! back only the verifying key. Every key hash is therefore known before any
//! witness is built, and each recipient checks its proof's `vk_hash` against the
//! deployment's.
//!
//! `--prove` builds the whole chain once, in order, in this process — but each
//! proof is farmed out to a fresh subprocess (`--internal-kind`/
//! `--internal-witness`/`--internal-output`, hidden flags) that loads its proving
//! key and proves, so the peak-memory column reflects that step's own footprint
//! via the kernel's `VmHWM` tracker rather than a same-process running
//! high-water mark. The Prove column is timed inside that subprocess, around
//! proving alone: setup and loading the key are excluded. Only the small,
//! already-`CanonicalSerialize`-able witness crosses into the subprocess and only
//! the proof crosses back — the parent holds every other piece of state (board
//! entries, history, prior proofs), so nothing is ever recomputed twice.
//!
//! ```shell
//! RUST_LOG=info cargo run --release -- --execute   # genesis circuit's constraint check only, no proving
//! RUST_LOG=info cargo run --release -- --prove     # full chain; --copies N copies to fold (default 1)
//! RUST_LOG=info cargo run --release --features groth16 -- --prove   # the same, with Groth16
//! ```

use std::time::Instant;

use ark_ec::pairing::Pairing;
use cloakkchain_circuit_wrap::snark::{self, Proof, ProvingKey, VerifyingKey};
use ark_mnt4_753::MNT4_753;
use ark_mnt6_753::MNT6_753;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::{rngs::StdRng, SeedableRng};
use clap::Parser;
use cloakkchain_circuit_spend::{
    spend_public_inputs, FoldCircuit, GenesisSpendCircuit, SpendCoreWitness, SpendStepCircuit, StepStatement,
    FOLD_BATCH, MAX_INPUTS, MAX_OUTPUTS, SPEND_PUBLIC_INPUT_COUNT,
};
use cloakkchain_circuit_wrap::{inner_vk_hash, WrapCircuit};
use cloakkchain_lib::{
    check_receipt, derive_coin_vpk, derive_enc_pk, derive_nullifier, derive_owner_pk, encrypt_tx, genesis_pk,
    genesis_sk, scan_entry, Anchor, BoardEntry, Coin, CoinSignature, Fr, History, NonMembershipWitness, OwnerPk,
    OwnerScalar, Transaction, EK_SALT,
};

// ---- CLI args ---------------------------------------------------------------

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(long)]
    execute: bool,
    #[arg(long)]
    prove: bool,
    /// Ad hoc: real setup+prove+verify at whichever MAX_INPUTS/
    /// MAX_OUTPUTS shape circuit-spend is currently compiled with — for
    /// filling in the paper's 2x2 grid cells. See `run_prove_grid_cell`'s
    /// doc comment. Not part of the normal demo.
    #[arg(long)]
    grid_cell: bool,
    /// How many copies of Alice's serial number the `--prove` attacker gets
    /// ordered ahead of her carrier. Bob folds them, `FOLD_BATCH` per fold
    /// proof (plus its wrap).
    #[arg(long, default_value_t = 1)]
    copies: u32,
    /// Hidden: re-invokes this binary as a single setup or proving subprocess
    /// (see the module doc comment). One of "genesis", "wrap", "fold",
    /// "spend". Not for direct use.
    #[arg(long, hide = true)]
    internal_kind: Option<String>,
    /// Hidden: run that circuit's setup rather than prove with it.
    #[arg(long, hide = true)]
    internal_setup: bool,
    /// Hidden: path to the serialized witness circuit struct, or the setup's
    /// parameters.
    #[arg(long, hide = true)]
    internal_witness: Option<String>,
    /// Hidden: where to write the proof, or the verifying key.
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
/// — pass to `encrypt_tx`, which signs the result. `vpks` and `anchor` go
/// inside the ciphertext, never on the wire.
fn make_tx(
    id: u64,
    sender_enc_sk: [u8; 32],
    vpks: Vec<OwnerPk>,
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
    let tx = Transaction { id, output_commitments, note_encs, vpks, anchor, spend_proof: vec![] };
    (tx, session_key, recipient_enc_pks)
}

// ---- Subprocess isolation + peak-memory tracking -----------------------------
//
// Each setup and each proof runs in a fresh child process, so its peak-memory
// reading reflects only that step's own working set, not a same-process running
// high-water mark carried over from earlier steps. Setup children write the
// proving key to a file and hand back the verifying key; proving children load
// that file, prove, and report their own proving time. Everything else (board
// state, history, prior proofs) stays in this parent process for the whole run,
// so no step is ever computed twice.

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
/// `SynthesisMode::Setup` mode setup itself uses, and returns the resulting
/// constraint count. Cheap — synthesis alone is native field arithmetic (no
/// FFTs/pairings/proving).
fn count_constraints<F: ark_ff::Field, C: ConstraintSynthesizer<F> + Clone>(circuit: &C) -> usize {
    let cs = ConstraintSystem::<F>::new_ref();
    cs.set_mode(ark_relations::r1cs::SynthesisMode::Setup);
    circuit.clone().generate_constraints(cs.clone()).expect("synthesize constraints for counting");
    cs.num_constraints()
}

fn temp_path(name: &str) -> std::path::PathBuf {
    std::env::temp_dir().join(format!("cloakkchain_{name}.bin"))
}

/// Where `kind`'s proving key lives between its setup and its proofs.
fn pk_path(kind: &str) -> std::path::PathBuf {
    temp_path(&format!("{kind}_pk"))
}

/// Uncompressed and unchecked on the way back in: only ever this binary's own
/// output, and proving keys are large enough for point decompression and
/// subgroup checks to cost noticeable time.
fn write_bin<T: CanonicalSerialize>(path: &std::path::Path, value: &T) {
    let mut buf = Vec::new();
    value.serialize_uncompressed(&mut buf).expect("serialize");
    std::fs::write(path, buf).expect("write file");
}

fn read_bin<T: CanonicalDeserialize>(path: &std::path::Path) -> T {
    let bytes = std::fs::read(path).expect("read file");
    T::deserialize_uncompressed_unchecked(&bytes[..]).expect("deserialize")
}

/// Run this binary as a child with `args`, returning its peak memory.
fn run_child(args: &[&str]) -> u64 {
    let exe = std::env::current_exe().expect("current_exe");
    let child = std::process::Command::new(&exe).args(args).spawn().expect("spawn subprocess");
    let (status, peak_mem_kb) = wait_tracking_peak_memory(child);
    assert!(status.success(), "subprocess {args:?} exited with {status}");
    peak_mem_kb.unwrap_or(0)
}

/// Run `kind`'s setup in a child, which keeps the proving key at
/// [`pk_path`]. Returns the verifying key, the wall-clock time and the peak
/// memory.
fn setup_subprocess<E: Pairing>(kind: &str, params: &impl CanonicalSerialize) -> (VerifyingKey<E>, f64, u64) {
    let input = temp_path(&format!("{kind}_setup_input"));
    let output = temp_path(&format!("{kind}_vk"));
    write_bin(&input, params);
    let t = Instant::now();
    let peak_mem_kb = run_child(&[
        "--internal-kind",
        kind,
        "--internal-setup",
        "--internal-witness",
        input.to_str().expect("temp path is valid UTF-8"),
        "--internal-output",
        output.to_str().expect("temp path is valid UTF-8"),
    ]);
    let secs = t.elapsed().as_secs_f64();
    let vk = read_bin(&output);
    let _ = std::fs::remove_file(&input);
    let _ = std::fs::remove_file(&output);
    (vk, secs, peak_mem_kb)
}

/// Prove `circuit` with `kind`'s proving key in a child. Returns the proof, the
/// proving time as the child measured it, and the peak memory.
fn prove_subprocess<C: CanonicalSerialize, E: Pairing>(kind: &str, circuit: &C) -> (Proof<E>, f64, u64) {
    let input = temp_path(&format!("{kind}_witness"));
    let output = temp_path(&format!("{kind}_proof"));
    write_bin(&input, circuit);
    let peak_mem_kb = run_child(&[
        "--internal-kind",
        kind,
        "--internal-witness",
        input.to_str().expect("temp path is valid UTF-8"),
        "--internal-output",
        output.to_str().expect("temp path is valid UTF-8"),
    ]);
    let (proof, prove_secs): (Proof<E>, u64) = read_bin(&output);
    let _ = std::fs::remove_file(&input);
    let _ = std::fs::remove_file(&output);
    (proof, prove_secs as f64 / 1e9, peak_mem_kb)
}

/// Entry point when this binary is re-invoked as a `--internal-kind`
/// subprocess.
fn run_internal_step(kind: &str, setup: bool, input: &str, output: &str) {
    let mut rng = StdRng::seed_from_u64(0x636c6f616b);
    let (input, output) = (std::path::Path::new(input), std::path::Path::new(output));
    if setup {
        match kind {
            "genesis" => {
                let (pk, vk) = cloakkchain_circuit_spend::setup(&mut rng).unwrap();
                write_bin(&pk_path(kind), &pk);
                write_bin(output, &vk);
            }
            "wrap" => {
                let (pk, vk) = cloakkchain_circuit_wrap::setup::<SPEND_PUBLIC_INPUT_COUNT, _>(&mut rng).unwrap();
                write_bin(&pk_path(kind), &pk);
                write_bin(output, &vk);
            }
            "fold" => {
                let wrap_vk: VerifyingKey<MNT6_753> = read_bin(input);
                let (pk, vk) = cloakkchain_circuit_spend::setup_fold(wrap_vk, &mut rng).unwrap();
                write_bin(&pk_path(kind), &pk);
                write_bin(output, &vk);
            }
            "spend" => {
                let (wrap_vk, genesis_vk_hash, fold_vk_hash): (VerifyingKey<MNT6_753>, Fr, Fr) = read_bin(input);
                let (pk, vk) =
                    cloakkchain_circuit_spend::setup_non_genesis(wrap_vk, genesis_vk_hash, fold_vk_hash, &mut rng)
                        .unwrap();
                write_bin(&pk_path(kind), &pk);
                write_bin(output, &vk);
            }
            other => panic!("unknown --internal-kind {other}"),
        }
        return;
    }

    /// Load the key and the witness, then time proving alone.
    fn prove_timed<E: Pairing, C: CanonicalDeserialize>(
        kind: &str,
        input: &std::path::Path,
        output: &std::path::Path,
        rng: &mut StdRng,
        prove: impl FnOnce(&ProvingKey<E>, C, &mut StdRng) -> Proof<E>,
    ) {
        let pk: ProvingKey<E> = read_bin(&pk_path(kind));
        let circuit: C = read_bin(input);
        let t = Instant::now();
        let proof = prove(&pk, circuit, rng);
        let nanos = t.elapsed().as_nanos() as u64;
        write_bin(output, &(proof, nanos));
    }
    match kind {
        "genesis" => prove_timed::<MNT4_753, GenesisSpendCircuit>(kind, input, output, &mut rng, |pk, c, rng| {
            cloakkchain_circuit_spend::prove(pk, c, rng).unwrap()
        }),
        "spend" => prove_timed::<MNT4_753, SpendStepCircuit>(kind, input, output, &mut rng, |pk, c, rng| {
            cloakkchain_circuit_spend::prove_non_genesis(pk, c, rng).unwrap()
        }),
        "fold" => prove_timed::<MNT4_753, FoldCircuit>(kind, input, output, &mut rng, |pk, c, rng| {
            cloakkchain_circuit_spend::prove_fold(pk, c, rng).unwrap()
        }),
        "wrap" => prove_timed::<MNT6_753, WrapCircuit<SPEND_PUBLIC_INPUT_COUNT>>(kind, input, output, &mut rng, |pk, c, rng| {
            cloakkchain_circuit_wrap::prove::<SPEND_PUBLIC_INPUT_COUNT, _>(pk, c, rng).unwrap()
        }),
        other => panic!("unknown --internal-kind {other}"),
    }
}

// ---- The deployment's keys -----------------------------------------------------

/// One key per circuit, set up once for the whole deployment, in dependency
/// order: genesis and wrap need nothing, fold needs the wrap key, spend needs
/// the wrap key and the genesis and fold keys' hashes.
struct Keys {
    genesis: VerifyingKey<MNT4_753>,
    wrap: VerifyingKey<MNT6_753>,
    fold: VerifyingKey<MNT4_753>,
    spend: VerifyingKey<MNT4_753>,
    genesis_hash: Fr,
    fold_hash: Fr,
    spend_hash: Fr,
}

impl Keys {
    fn setup(stats: &mut Vec<SetupStats>) -> Self {
        println!("--- Setup: one key per circuit, once per deployment ---");
        let mut record = |name: &str, constraints: usize, secs: f64, peak_mem_kb: u64| {
            println!("  {name}: {secs:.1}s");
            stats.push(SetupStats { name: name.into(), constraints, secs, peak_mem_kb });
        };

        let (genesis, secs, mem) = setup_subprocess::<MNT4_753>("genesis", &Vec::<u8>::new());
        record("GenesisSpendCircuit", count_constraints(&GenesisSpendCircuit::default()), secs, mem);

        let (wrap, secs, mem) = setup_subprocess::<MNT6_753>("wrap", &Vec::<u8>::new());
        let wrap_shape = WrapCircuit::<SPEND_PUBLIC_INPUT_COUNT> {
            inner_vk: cloakkchain_circuit_wrap::shaped_inner_vk(SPEND_PUBLIC_INPUT_COUNT),
            inner_proof: Some(Proof { a: genesis.g1_point(), b: genesis.g2_point(), c: genesis.g1_point() }),
            inner_public_inputs: None,
        };
        record("WrapCircuit", count_constraints(&wrap_shape), secs, mem);

        let (fold, secs, mem) = setup_subprocess::<MNT4_753>("fold", &wrap);
        let fold_shape = FoldCircuit {
            wrap_vk: wrap.clone(),
            previous: None,
            previous_proof: Some(SpendStepCircuit::dummy_wrap_proof()),
            input: 0,
            vpk: None,
            occurrences: Vec::new(),
            vk_hash: None,
        };
        record(&format!("FoldCircuit ({FOLD_BATCH} slots)"), count_constraints(&fold_shape), secs, mem);

        let genesis_hash = inner_vk_hash(&genesis);
        let fold_hash = inner_vk_hash(&fold);
        let (spend, secs, mem) = setup_subprocess::<MNT4_753>("spend", &(wrap.clone(), genesis_hash, fold_hash));
        let spend_shape = SpendStepCircuit {
            core: SpendCoreWitness::default(),
            wrap_vk: wrap.clone(),
            genesis_vk_hash: genesis_hash,
            fold_vk_hash: fold_hash,
            input_parent_proofs: std::array::from_fn(|_| Some(SpendStepCircuit::dummy_wrap_proof())),
            input_parent_statements: std::array::from_fn(|_| None),
            input_parents: std::array::from_fn(|_| None),
        };
        record("SpendStepCircuit", count_constraints(&spend_shape), secs, mem);

        let spend_hash = inner_vk_hash(&spend);
        Keys { genesis, wrap, fold, spend, genesis_hash, fold_hash, spend_hash }
    }

    fn remove_proving_keys() {
        for kind in ["genesis", "wrap", "fold", "spend"] {
            let _ = std::fs::remove_file(pk_path(kind));
        }
    }
}

/// Points for a structurally valid dummy proof, which `ProofVar` needs even
/// when nothing about it is checked: any of the VK's own points will do.
trait DummyPoints {
    fn g1_point(&self) -> ark_mnt4_753::G1Affine;
    fn g2_point(&self) -> ark_mnt4_753::G2Affine;
}

impl DummyPoints for VerifyingKey<MNT4_753> {
    fn g1_point(&self) -> ark_mnt4_753::G1Affine {
        snark::vk_points(self).0[0]
    }
    fn g2_point(&self) -> ark_mnt4_753::G2Affine {
        snark::vk_points(self).1[0]
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

struct SetupStats {
    name: String,
    constraints: usize,
    secs: f64,
    peak_mem_kb: u64,
}

fn print_setup_table(stats: &[SetupStats]) {
    let w = 72;
    println!("\n{}", "=".repeat(w));
    println!("  Setup, once per deployment ({})", snark::NAME);
    println!("{}", "=".repeat(w));
    println!("{:<28}  {:>11}  {:>11}  {:>11}", "Circuit", "Constraints", "Setup", "Peak Mem");
    println!("{}", "-".repeat(w));
    for s in stats {
        println!(
            "{:<28}  {:>11}  {:>9.1} s  {:>11}",
            s.name,
            fmt_constraints(s.constraints),
            s.secs,
            fmt_mem_kb(s.peak_mem_kb)
        );
    }
    println!("{}", "=".repeat(w));
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
    println!("  Proof Statistics ({}; Prove excludes setup and loading the key)", snark::NAME);
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
        run_internal_step(&kind, args.internal_setup, &witness_path, &output_path);
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

    run_prove(args.copies);
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
        core: core_witness(&history, genesis, std::slice::from_ref(genesis_coin), std::slice::from_ref(alice_coin), Fr::from(0u64)),
    };

    let cs = ConstraintSystem::<Fr>::new_ref();
    circuit.generate_constraints(cs.clone()).expect("synthesize constraints");
    let satisfied = cs.is_satisfied().expect("check satisfiability");
    println!("  constraints: {}", cs.num_constraints());
    println!("  satisfied:   {satisfied}");
    assert!(satisfied);
    println!("\nRun --prove for the full chain (real {} proofs; --copies sets how many copies Bob has to fold).", snark::NAME);
}

// ---- One step of the chain ---------------------------------------------------

/// A proof of any of the circuits, with what it claims and the key it's for.
#[derive(Clone)]
struct Proven {
    statement: StepStatement,
    vk: VerifyingKey<MNT4_753>,
    proof: Proof<MNT4_753>,
}

/// A spend whose proof exists, as both the poster and its recipients see it.
struct ProvenSpend {
    entry: BoardEntry,
    tx: Transaction,
    proven: Proven,
}

/// A proof re-proved on the other curve, under the deployment's wrap key, for
/// the next step to verify.
struct WrappedSpend {
    proof: Proof<MNT6_753>,
}

/// What a spend verifies about the entry that created its input coin: the
/// entry itself, at `slot`, and the latest proof describing it — its spend
/// proof, or the last fold over it — wrapped.
struct Parent<'a> {
    spend: &'a ProvenSpend,
    slot: usize,
    latest: &'a Proven,
    wrapped: &'a WrappedSpend,
}

/// The spend relation's witness, anchored at `history`'s current state, for
/// the circuit whose key hashes to `vk_hash`.
fn core_witness(history: &History, sender: &Party, inputs: &[Coin], outputs: &[Coin], vk_hash: Fr) -> SpendCoreWitness {
    let size = history.len();
    let tree = history.nullifier_tree_at(size);
    let nonmemberships: Vec<NonMembershipWitness> = inputs
        .iter()
        .map(|input| tree.prove_non_membership(derive_nullifier(input.commitment(), &sender.sk_p)))
        .collect();
    SpendCoreWitness::new(
        sender.sk_p,
        inputs,
        outputs,
        history.anchor_at(size).expect("the current state exists"),
        &nonmemberships,
        vk_hash,
    )
}

/// Prove `sender`'s spend at `history`'s current state and build its entry,
/// without posting it: nothing here depends on where it ends up landing.
/// `parents` has one entry per input, and is empty for a genesis mint.
/// Construction order matters: prove, encrypt the proof into the ciphertext,
/// then sign last (inside `encrypt_tx`).
#[allow(clippy::too_many_arguments)]
fn prove_spend(
    name: &str,
    keys: &Keys,
    history: &History,
    sender: &Party,
    inputs: &[Coin],
    outputs: &[(Coin, [u8; 32])],
    parents: &[Parent],
    stats: &mut Vec<ProveStats>,
) -> ProvenSpend {
    let output_coins: Vec<Coin> = outputs.iter().map(|(c, _)| c.clone()).collect();
    let genesis = parents.is_empty();
    let (vk, vk_hash) = if genesis { (&keys.genesis, keys.genesis_hash) } else { (&keys.spend, keys.spend_hash) };
    let core = core_witness(history, sender, inputs, &output_coins, vk_hash);
    let statement = StepStatement::of_spend(core.public_values().expect("core_witness sets every public value"), vk_hash);

    let (proof, prove_secs, peak_mem_kb, constraints) = if genesis {
        let circuit = GenesisSpendCircuit { core };
        let (proof, secs, mem) = prove_subprocess::<_, MNT4_753>("genesis", &circuit);
        (proof, secs, mem, count_constraints(&circuit))
    } else {
        assert_eq!(parents.len(), inputs.len(), "one parent per input");
        let witness = |parent: &Parent| {
            let created_by = &parent.spend.proven.statement.public_values;
            history.parent_witness(parent.slot, created_by, &parent.spend.tx.vpks, history.len())
        };
        let circuit = SpendStepCircuit {
            core,
            wrap_vk: keys.wrap.clone(),
            genesis_vk_hash: keys.genesis_hash,
            fold_vk_hash: keys.fold_hash,
            // An unused slot still needs a structurally valid proof.
            input_parent_proofs: std::array::from_fn(|i| {
                Some(parents.get(i).map_or_else(SpendStepCircuit::dummy_wrap_proof, |p| p.wrapped.proof.clone()))
            }),
            input_parent_statements: std::array::from_fn(|i| parents.get(i).map(|p| p.latest.statement.clone())),
            input_parents: std::array::from_fn(|i| parents.get(i).map(witness)),
        };
        let (proof, secs, mem) = prove_subprocess::<_, MNT4_753>("spend", &circuit);
        (proof, secs, mem, count_constraints(&circuit))
    };
    let t = Instant::now();
    assert!(cloakkchain_circuit_spend::verify(vk, &statement.public_inputs(), &proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    println!("  Proved in {prove_secs:.1}s, verified in {verify_ms:.1}ms.");

    let commitments: Vec<Fr> = inputs.iter().map(Coin::commitment).collect();
    let (mut tx, session_key, recipients) = make_tx(
        stats.len() as u64,
        sender.enc_sk,
        commitments.iter().map(|cm| derive_coin_vpk(&sender.sk_p, *cm)).collect(),
        statement.public_values.anchor.clone(),
        outputs,
    );
    tx.spend_proof = ark_serialize_bytes(&proof);
    let entry = encrypt_tx(&tx, &commitments, &sender.sk_p, &recipients, session_key);

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
    ProvenSpend { entry, tx, proven: Proven { statement, vk: vk.clone(), proof } }
}

/// Fold every occurrence in the windows of `parent`'s entry — one window per
/// input it spent — into the statement of its spend proof, `FOLD_BATCH` at a
/// time: one fold proof and one wrap per batch, as the next spender must before
/// spending. Returns the last fold and its wrap, or the spend's own when every
/// window is empty.
fn fold_window(
    keys: &Keys,
    history: &History,
    parent: &ProvenSpend,
    slot: usize,
    wrapped: WrappedSpend,
    stats: &mut Vec<ProveStats>,
) -> (Proven, WrappedSpend) {
    let created_by = &parent.proven.statement.public_values;
    let windows = history.parent_witness(slot, created_by, &parent.tx.vpks, history.len()).windows;
    let mut latest = parent.proven.clone();
    let mut wrapped = wrapped;
    for (input, window) in windows.iter().enumerate() {
        let label = if windows.len() > 1 { format!(" of input {}", input + 1) } else { String::new() };
        let mut folded = 0;
        for batch in window.occurrences.chunks(FOLD_BATCH) {
            let range = format!("{}-{}{label}", folded + 1, folded + batch.len());
            println!("  Folding occurrences {range} of {} into the spend's statement.", window.occurrences.len());
            let circuit = FoldCircuit {
                wrap_vk: keys.wrap.clone(),
                previous: Some(latest.statement.clone()),
                previous_proof: Some(wrapped.proof.clone()),
                input,
                vpk: Some(parent.tx.vpks[input]),
                occurrences: batch.to_vec(),
                vk_hash: Some(keys.fold_hash),
            };
            let statement = circuit.statement().expect("every field is set");
            let constraints = count_constraints(&circuit);
            let (proof, prove_secs, peak_mem_kb) = prove_subprocess::<_, MNT4_753>("fold", &circuit);
            let t = Instant::now();
            assert!(cloakkchain_circuit_spend::verify(&keys.fold, &statement.public_inputs(), &proof).unwrap());
            let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
            println!("  Folded in {prove_secs:.1}s, verified in {verify_ms:.1}ms.");
            stats.push(ProveStats {
                name: format!("Fold copies {range}"),
                board_size: history.len(),
                constraints,
                prove_secs,
                verify_ms,
                proof_bytes: ark_serialize_len(&proof),
                entry_bytes: None,
                peak_mem_kb,
            });
            latest = Proven { statement, vk: keys.fold.clone(), proof };
            wrapped = wrap_spend(&format!("Wrap fold {range}"), keys, &latest, history, stats);
            folded += batch.len();
        }
        let head = if window.occurrences.is_empty() { Fr::from(0u64) } else { window.leaf.occ };
        assert_eq!(latest.statement.window_heads[input], head);
    }
    (latest, wrapped)
}

/// Wrap a proof so the next step, back on MNT4-753, can recursively verify it
/// directly — no receipt layer.
fn wrap_spend(name: &str, keys: &Keys, proven: &Proven, history: &History, stats: &mut Vec<ProveStats>) -> WrappedSpend {
    let public_inputs = proven.statement.public_inputs();
    let circuit = WrapCircuit::<SPEND_PUBLIC_INPUT_COUNT> {
        inner_vk: proven.vk.clone(),
        inner_proof: Some(proven.proof.clone()),
        inner_public_inputs: Some(public_inputs),
    };
    let (proof, prove_secs, peak_mem_kb) = prove_subprocess::<_, MNT6_753>("wrap", &circuit);
    let chunks = cloakkchain_circuit_wrap::public_input_chunks(&public_inputs);
    let t = Instant::now();
    assert!(cloakkchain_circuit_wrap::verify(&keys.wrap, &chunks, &proof).unwrap());
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
    WrappedSpend { proof }
}

/// `recipient` finds its coin in the carrier at `slot` and runs the off-circuit
/// acceptance check against its own replay, verifying the real proof under the
/// deployment's key, with `vk_hash` naming it — which, by induction, pins every
/// step back to genesis — and with a zero window head and origin, so that only a
/// spend proof passes.
fn receive(recipient: &Party, coin: &Coin, spend: &ProvenSpend, slot: usize, history: &History) {
    let vk = &spend.proven.vk;
    println!("\n--- {} scans slot {slot} ---", recipient.name);
    let tx = scan_entry(&recipient.enc_sk, &spend.entry).expect("the recipient must be able to decrypt its carrier");
    assert!(tx.receives_coin(&coin.commitment()), "the carrier must transfer the recipient's coin");
    check_receipt(history, slot, &spend.entry, &tx, |public_values, proof_bytes| {
        let proof = Proof::<MNT4_753>::deserialize_compressed(proof_bytes).expect("deserialize proof");
        let inputs = spend_public_inputs(public_values, &[Fr::from(0u64); MAX_INPUTS], Fr::from(0u64), inner_vk_hash(vk));
        cloakkchain_circuit_spend::verify(vk, &inputs, &proof).unwrap()
    })
    .expect("the recipient must accept its carrier");
    println!("  [{}] accepted coin (value={}) at slot {slot}", recipient.name, coin.value);
}

/// What the reviewers' attack posts: someone else's serial number on an entry
/// of the attacker's own. Needs no secrets, and every wallet inserts it blindly.
fn copy_of_serial_number(nullifier: Fr, seed: u32) -> BoardEntry {
    let byte = seed as u8;
    BoardEntry {
        ciphertext: vec![byte; 64],
        ek_pk: [byte; 32],
        key_encs: vec![[byte; 32]],
        nullifiers: vec![nullifier],
        output_commitments: vec![Fr::from(999u64 + seed as u64)],
        signatures: vec![CoinSignature { c: Fr::from(seed as u64 + 1), s: OwnerScalar::from(seed as u64 + 1) }],
    }
}

fn run_prove(copies: u32) {
    let mut setup_stats: Vec<SetupStats> = Vec::new();
    let keys = Keys::setup(&mut setup_stats);

    let mut stats: Vec<ProveStats> = Vec::new();
    let mut history = History::new();

    let genesis = Party::genesis();
    let alice = Party::new("Alice", 1);
    let bob = Party::new("Bob", 2);
    let carol = Party::new("Carol", 3);

    // =========================================================================
    // Slot 0: genesis mints 100 units to Alice
    // =========================================================================
    println!("\n--- Slot 0: Genesis mints 100 units to Alice ---");
    println!("  Proving: pk_p is the fixed genesis key, the mint's serial number and per-coin key are correctly derived, and the serial number is absent at the anchor.");
    let genesis_coin = coin(0xA1, 100, genesis.pk_p);
    let alice_coin = coin(0xA2, 100, alice.pk_p);
    let mint = prove_spend(
        "Genesis mint",
        &keys,
        &history,
        &genesis,
        std::slice::from_ref(&genesis_coin),
        &[(alice_coin.clone(), alice.enc_pk)],
        &[],
        &mut stats,
    );
    let mint_slot = history.append(&mint.entry);

    println!("  Wrapping the genesis proof: re-verifies it on the other curve (MNT6-753) and re-exposes its public inputs as small chunks, so Alice's spend circuit (back on MNT4-753) can recursively check it.");
    let wrapped_mint = wrap_spend("Wrap genesis proof", &keys, &mint.proven, &history, &mut stats);
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
        &keys,
        &history,
        &alice,
        std::slice::from_ref(&alice_coin),
        &[(bob_coin.clone(), bob.enc_pk), (change_coin.clone(), alice.enc_pk)],
        &[Parent { spend: &mint, slot: mint_slot, latest: &mint.proven, wrapped: &wrapped_mint }],
        &mut stats,
    );

    // =========================================================================
    // The reviewers' attack: copies of Alice's serial number get ordered first
    // =========================================================================
    if copies > 0 {
        let first = history.len();
        for seed in 0..copies {
            history.append(&copy_of_serial_number(alice_spend.entry.nullifiers[0], seed));
        }
        println!(
            "\n--- Slots {first}-{}: a third party posts {copies} copies of Alice's serial number ---",
            history.len() - 1
        );
        println!("  All ahead of Alice's carrier. Her proof doesn't need redoing: it's anchored before them.");
    }

    let alice_slot = history.append(&alice_spend.entry);
    println!("\n--- Slot {alice_slot}: Alice's carrier lands ---");
    println!("  Wrapping Alice's spend so the next step (back on MNT4-753) can recursively verify it.");
    let wrapped_alice = wrap_spend("Wrap Alice's spend", &keys, &alice_spend.proven, &history, &mut stats);
    receive(&bob, &bob_coin, &alice_spend, alice_slot, &history);

    // =========================================================================
    // Bob folds the copies, then spends his 40 units to Carol
    // =========================================================================
    println!("\n--- Bob folds the copies in Alice's window into her spend's statement, {FOLD_BATCH} per fold ---");
    println!("  Proving, per fold: the previous proof verifies, its statement carries over unchanged, and every copy in the batch is harmless (its signature fails under Alice's per-coin key).");
    let (latest_alice, wrapped_latest) = fold_window(&keys, &history, &alice_spend, alice_slot, wrapped_alice, &mut stats);

    println!("\n--- Slot {}: Bob spends his 40 units to Carol ---", history.len());
    println!("  Proving: Bob owns the input coin, its serial number is absent at his anchor, value conservation holds (40 in = 40 out), and Alice's spend under his anchor is genuine, its window covered exactly by the folds.");
    let carol_coin = coin(0xC1, 40, carol.pk_p);
    let bob_spend = prove_spend(
        "Bob -> Carol",
        &keys,
        &history,
        &bob,
        std::slice::from_ref(&bob_coin),
        &[(carol_coin.clone(), carol.enc_pk)],
        &[Parent { spend: &alice_spend, slot: alice_slot, latest: &latest_alice, wrapped: &wrapped_latest }],
        &mut stats,
    );
    let bob_slot = history.append(&bob_spend.entry);
    receive(&carol, &carol_coin, &bob_spend, bob_slot, &history);
    println!("  End of chain.");

    print_setup_table(&setup_stats);
    print_prove_table(&stats);
    Keys::remove_proving_keys();
}

// ---- Grid-cell diagnostic (paper results) ------------------------------------
//
// Ad hoc scenario for measuring *real* proving stats (constraints, prove time,
// verify time, proof size, subprocess-isolated peak memory) at whichever
// MAX_INPUTS/MAX_OUTPUTS shape this binary is compiled with. `run_prove`'s demo
// chain only ever spends one input; this function exists so the same
// measurement methodology (real proving, subprocess-isolated memory) can be
// pointed at every cell of the grid: `--features two-inputs` for the 2-input
// rows, `--features single-output` for the 1-output ones (add `groth16` for
// Groth16).
//
// Scenario: genesis mints MAX_INPUTS coins of 100 to Alice, one mint each, then
// Alice spends all of them at once into MAX_OUTPUTS outputs (40 to Bob plus the
// change back to herself if MAX_OUTPUTS>1, otherwise everything to Bob).
//
// Alice's spend isn't posted, since nothing downstream spends her new outputs.
fn run_prove_grid_cell() {
    println!("=== Grid cell: MAX_INPUTS={MAX_INPUTS} MAX_OUTPUTS={MAX_OUTPUTS} ===");

    let mut setup_stats: Vec<SetupStats> = Vec::new();
    let keys = Keys::setup(&mut setup_stats);
    let mut stats: Vec<ProveStats> = Vec::new();
    let mut history = History::new();

    let genesis = Party::genesis();
    let alice = Party::new("Alice", 1);
    let bob = Party::new("Bob", 2);

    let mut alice_coins = Vec::new();
    let mut mints = Vec::new();
    for i in 0..MAX_INPUTS as u8 {
        println!("\n--- Genesis mint {}: 100 units to Alice ---", i + 1);
        let alice_coin = coin(0xB0 + i, 100, alice.pk_p);
        let mint = prove_spend(
            &format!("Genesis mint {}", i + 1),
            &keys,
            &history,
            &genesis,
            &[coin(0xA0 + i, 100, genesis.pk_p)],
            &[(alice_coin.clone(), alice.enc_pk)],
            &[],
            &mut stats,
        );
        let slot = history.append(&mint.entry);
        let wrapped = wrap_spend(&format!("Wrap genesis mint {}", i + 1), &keys, &mint.proven, &history, &mut stats);
        alice_coins.push(alice_coin);
        mints.push((mint, slot, wrapped));
    }

    println!("\n--- Alice spends {MAX_INPUTS} input(s) into {MAX_OUTPUTS} output(s) ---");
    let total = 100 * MAX_INPUTS as u64;
    let bob_val = if MAX_OUTPUTS > 1 { 40 } else { total };
    let mut outputs = vec![(coin(0xC0, bob_val, bob.pk_p), bob.enc_pk)];
    if MAX_OUTPUTS > 1 {
        outputs.push((coin(0xC1, total - bob_val, alice.pk_p), alice.enc_pk));
    }
    let parents: Vec<Parent> = mints
        .iter()
        .map(|(mint, slot, wrapped)| Parent { spend: mint, slot: *slot, latest: &mint.proven, wrapped })
        .collect();
    prove_spend(
        &format!("Alice's spend ({MAX_INPUTS}-in-{MAX_OUTPUTS}-out)"),
        &keys,
        &history,
        &alice,
        &alice_coins,
        &outputs,
        &parents,
        &mut stats,
    );

    print_setup_table(&setup_stats);
    print_prove_table(&stats);
    Keys::remove_proving_keys();
    println!("\n=== Grid cell done: MAX_INPUTS={MAX_INPUTS} MAX_OUTPUTS={MAX_OUTPUTS} ===");
}
