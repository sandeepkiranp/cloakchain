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

const CLOAKKCHAIN_SPEND_ELF: Elf     = include_elf!("cloakkchain-program-spend");
const CLOAKKCHAIN_COINPROOF_ELF: Elf = include_elf!("cloakkchain-program-coinproof");
const VFY_G16_ELF: Elf               = include_elf!("cloakkchain-program-vfy-g16");

// ---- CLI args ---------------------------------------------------------------

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(long)]
    execute: bool,
    #[arg(long)]
    prove: bool,
    #[arg(long, help = "Generate one Groth16 spend proof then execute VFY_G16_ELF to measure cycles — no full proving")]
    bench_vfy_g16: bool,
    // Hidden flags used when this binary re-invokes itself as a proving subprocess.
    // Each proof runs in its own process so the Go/gnark circuit memory is fully
    // returned to the OS between proofs (prevents OOM on machines with ≤64 GB RAM).
    #[arg(long, hide = true)]
    internal_prove_elf: Option<String>,
    #[arg(long, hide = true)]
    internal_prove_stdin: Option<std::path::PathBuf>,
    #[arg(long, hide = true)]
    internal_prove_output: Option<std::path::PathBuf>,
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
    proof: SP1ProofWithPublicValues,   // compressed STARK coin-proof
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
        vfy_g16_pk: &C::ProvingKey,
        vfy_g16_vkey: &[u32; 8],
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
            let inner_pv    = record.pv.clone();
            let inner_proof = record.proof.clone();
            let parent_null = inner_pv.parent_nullifier;
            let own_null    = nullifier(*cn, self.party.sk);
            let mut stdin = build_coinproof_stdin(
                coinproof_vkey, vfy_g16_vkey,
                self.party.sk, *cn, entry, slot, &ap,
                Some(&inner_pv), parent_null, own_null,
            );
            // Inner coin-proof is a compressed STARK — extract inner proof for write_proof.
            let SP1Proof::Compressed(ic) = inner_proof.proof.clone() else { panic!("expected compressed coin-proof") };
            stdin.write_proof(*ic, coinproof_pk.verifying_key().vk.clone());
            // No validation proof: advancing slots past the receipt, not at receipt slot.
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
                                spend_pk, coinproof_pk, coinproof_vkey,
                                vfy_g16_pk, vfy_g16_vkey,
                                client, stats, parent_null);
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
        vfy_g16_pk: &C::ProvingKey,
        vfy_g16_vkey: &[u32; 8],
        client: &C,
        stats: &mut Vec<ProveStats>,
        parent_nullifier: [u8; 32],
    ) {
        let own_null = nullifier(cn, self.party.sk);

        // Prove VFY_G16_ELF on the receipt entry's spend proof — done upfront so the
        // resulting compressed-STARK validation proof is ready when we reach that slot.
        let validation_proof: SP1ProofWithPublicValues = {
            let entry = &all_entries[up_to_slot];
            let tx = lib_scan_entry(&self.party.sk, entry)
                .expect("bootstrap: cannot decrypt receipt entry");
            let pkg: SpendProofPackage = bincode::deserialize(&tx.spend_proof)
                .expect("bootstrap: tx.spend_proof is not a SpendProofPackage");
            let vfy_stdin = build_vfy_g16_stdin(&pkg.proof_bytes, &pkg.pv_encode, &pkg.spend_vkey_hash);
            let vfy_label = format!("{} VFY-G16 slot {}", self.party.name, up_to_slot);
            println!("  [{}] proving VFY-G16 …", vfy_label);
            let t = Instant::now();
            let proof = prove_subprocess("vfy-g16", &vfy_stdin);
            let prove_secs = t.elapsed().as_secs_f64();
            println!("  [{}]  ({:.1}s)", vfy_label, prove_secs);
            stats.push(ProveStats { name: vfy_label, board_size: up_to_slot + 1,
                prove_secs, verify_ms: 0.0, proof_bytes: None, entry_bytes: None });
            proof
        };

        // Slot 0: base case.
        let ap0 = append_proof_for(&all_entries[..1]);
        let mut stdin = build_coinproof_stdin(
            coinproof_vkey, vfy_g16_vkey,
            self.party.sk, cn, &all_entries[0], 0, &ap0,
            None, parent_nullifier, own_null,
        );
        // If received at slot 0, the validation proof is consumed here.
        if up_to_slot == 0 {
            let SP1Proof::Compressed(vc) = validation_proof.proof.clone() else { panic!("expected compressed vfy-g16") };
            stdin.write_proof(*vc, vfy_g16_pk.verifying_key().vk.clone());
        }
        let label = format!("{} coin-proof slot 0 (base)", self.party.name);
        let rec = self.run_coinproof_step(stdin, &label, 1, coinproof_pk, client, stats);
        self.coins.insert(cn, rec);

        for s in 1..=up_to_slot {
            let aps = append_proof_for(&all_entries[..=s]);
            let rec = self.coins.get(&cn).unwrap();
            let inner_pv    = rec.pv.clone();
            let inner_proof = rec.proof.clone();
            let mut stdin = build_coinproof_stdin(
                coinproof_vkey, vfy_g16_vkey,
                self.party.sk, cn, &all_entries[s], s, &aps,
                Some(&inner_pv), parent_nullifier, own_null,
            );
            // Inner coin-proof always present for step case.
            let SP1Proof::Compressed(ic) = inner_proof.proof else { panic!("expected compressed coin-proof") };
            stdin.write_proof(*ic, coinproof_pk.verifying_key().vk.clone());
            // Validation proof consumed only at the receipt slot.
            if s == up_to_slot {
                let SP1Proof::Compressed(vc) = validation_proof.proof.clone() else { panic!("expected compressed vfy-g16") };
                stdin.write_proof(*vc, vfy_g16_pk.verifying_key().vk.clone());
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
        let proof = prove_subprocess("coinproof", &stdin);   // compressed STARK
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
    println!("  Proof Statistics");
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

/// Run a proof (Groth16 or compressed STARK) in a fresh child process.
///
/// The elf_id controls what proof type the subprocess generates:
///   "spend"     → Groth16  (gnark, ~50 GB overhead, needs isolation)
///   "coinproof" → compressed STARK  (tiny STARK trace, isolated for safety)
///   "vfy-g16"   → compressed STARK  (runs Groth16Verifier inside, ~10–15 GB)
///
/// Subprocess isolation means the OS fully reclaims all Go/gnark pages when
/// the child exits, so every proof starts with a clean slate.
fn prove_subprocess(elf_id: &str, stdin: &SP1Stdin) -> SP1ProofWithPublicValues {
    let tmp = std::env::temp_dir();
    let stdin_path  = tmp.join(format!("cloakchain_{elf_id}_stdin.bin"));
    let proof_path  = tmp.join(format!("cloakchain_{elf_id}_proof.bin"));

    let stdin_bytes = bincode::serialize(stdin).expect("serialize SP1Stdin");
    std::fs::write(&stdin_path, stdin_bytes).expect("write stdin file");

    println!("  [subprocess] proving {} in child process …", elf_id);
    let exe = std::env::current_exe().expect("current_exe");
    // For vfy-g16 (636K cycles with BN254 precompiles), the default 16M shard size
    // puts everything in 1 shard, which triggers a BaseAlu padding DivF bug in
    // SP1 6.2.3's recursion circuit when used as an inner proof.  Force a smaller
    // shard size so vfy-g16 spans multiple shards (≥2) and avoids the bug.
    let mut cmd = std::process::Command::new(&exe);
    cmd.args([
        "--internal-prove-elf",    elf_id,
        "--internal-prove-stdin",  stdin_path.to_str().unwrap(),
        "--internal-prove-output", proof_path.to_str().unwrap(),
    ]).envs(std::env::vars());
    // SP1 6.2.3 recursion compress fix: the circuit divides by the combined BN254
    // chip evaluation (address 316465 in the recursion program) loaded from the
    // proof at step 1.  VFY-G16 fires BN254 precompiles (substrate-bn) → eval≠0.
    // coinproof now fires 8 dummy BN254 ecalls → eval≠0 for all BN254 chip types.
    // SHARD_SIZE=262144 kept so both programs span multiple shards; RECURSION_DIAG
    // activates the write-tracker in vendor/sp1-recursion-executor to post-mortem
    // any remaining DivF failure.
    // WITHOUT_VK_VERIFICATION and SP1_CIRCUIT_MODE=dev are set process-wide in main()
    // (inherited here via .envs(std::env::vars()) above) so every subprocess - spend
    // included - consistently agrees on the same (dummy) recursion vk_root; see the
    // comment in main() for why they can't be set per-elf-type only.
    match elf_id {
        "vfy-g16" => {
            cmd.env("SHARD_SIZE", "262144")  // 1<<18; ~636K cycles ≈ 3 shards
               .env("RECURSION_DIAG", "1");  // compare init dump with coinproof
        }
        "coinproof" => {
            cmd.env("SHARD_SIZE", "262144")  // 1<<18; ~3M cycles ≈ 12 shards
               .env("RECURSION_DIAG", "1");  // watch addr 316465 init dump
        }
        _ => {}
    }
    let status = cmd.status().expect("spawn proving subprocess");
    assert!(status.success(), "proving subprocess for {elf_id} exited with {status}");

    let proof_bytes = std::fs::read(&proof_path).expect("read proof file");
    let proof: SP1ProofWithPublicValues =
        bincode::deserialize(&proof_bytes).expect("deserialize SP1ProofWithPublicValues");
    let _ = std::fs::remove_file(&stdin_path);
    let _ = std::fs::remove_file(&proof_path);
    proof
}

/// Entry point when this binary is re-invoked as a proving subprocess.
fn run_internal_prove(elf_id: &str, stdin_path: &std::path::Path, output_path: &std::path::Path) {
    let stdin_bytes = std::fs::read(stdin_path).expect("read stdin file");
    let stdin: SP1Stdin = bincode::deserialize(&stdin_bytes).expect("deserialize SP1Stdin");
    let client = ProverClient::from_env();
    let proof = match elf_id {
        "spend" => {
            let pk = client.setup(CLOAKKCHAIN_SPEND_ELF).expect("setup spend");
            client.prove(&pk, stdin).groth16().run().expect("groth16 prove")
        }
        "coinproof" => {
            // ── Diagnostics ────────────────────────────────────────────────────────
            let shard_size = std::env::var("SHARD_SIZE").unwrap_or_else(|_| "(unset)".into());
            // CRC-32 of the embedded ELF — changes whenever the ELF is rebuilt.
            let elf_crc: u32 = CLOAKKCHAIN_COINPROOF_ELF
                .iter()
                .fold(0u32, |acc, &b| acc.wrapping_add(b as u32));
            eprintln!(
                "[COINPROOF-DIAG] SHARD_SIZE={shard_size}  ELF_bytes={}  ELF_crc={elf_crc:#010x}",
                CLOAKKCHAIN_COINPROOF_ELF.len()
            );
            // Execute (no proof) to get the exact cycle count and confirm the loop
            // output appears.  This also surfaces any execution errors before the
            // (slow) proving step.
            match client.execute(CLOAKKCHAIN_COINPROOF_ELF, stdin.clone()).run() {
                Ok((_, report)) => {
                    let cycles = report.total_instruction_count();
                    eprintln!(
                        "[COINPROOF-DIAG] execute OK: cycles={cycles}  \
                         shards@262144={}",
                        cycles.div_ceil(262144)
                    );
                    // Full opcode + syscall breakdown — shows which precompile chips fired.
                    eprintln!("[COINPROOF-DIAG] full execution report:\n{report}");
                }
                Err(e) => eprintln!("[COINPROOF-DIAG] execute FAILED: {e}"),
            }
            // ── Proof ──────────────────────────────────────────────────────────────
            let pk = client.setup(CLOAKKCHAIN_COINPROOF_ELF).expect("setup coinproof");
            client.prove(&pk, stdin).compressed().run().expect("compressed prove")
        }
        "vfy-g16" => {
            // ── Diagnostics ────────────────────────────────────────────────────────
            // A panic inside the guest (e.g. verify_sp1_spend_proof(...).expect(...))
            // converts to a clean halt(1) rather than a host-visible error, so proving
            // succeeds silently with exit_code=1 - only surfacing much later when
            // coinproof's deferred verifier asserts exit_code==0. Run execute() first
            // (mirroring the coinproof branch above) so any guest panic is visible here.
            match client.execute(VFY_G16_ELF, stdin.clone()).run() {
                Ok((output, report)) => {
                    // execute() returns Ok even when the guest panics (SP1 converts a
                    // panic to a clean halt(1)) - report.exit_code is the only way to
                    // actually see this; cycle count alone doesn't reveal it.
                    eprintln!(
                        "[VFY-G16-DIAG] execute OK: cycles={} exit_code={}",
                        report.total_instruction_count(),
                        report.exit_code
                    );
                    // On exit_code!=0 the guest commits, in order: a length-prefixed dump
                    // of (proof_bytes, pv_encode, spend_vkey_hash) - the exact inputs that
                    // failed verification - followed by the panic hook's own debug message.
                    // Save the dumped fields to disk so they can be pulled off-machine and
                    // replayed against both verifiers locally.
                    if report.exit_code != 0 {
                        let bytes = output.as_slice();
                        let mut offset = 0usize;
                        let mut fields = Vec::new();
                        while offset + 4 <= bytes.len() {
                            let len = u32::from_le_bytes(bytes[offset..offset + 4].try_into().unwrap()) as usize;
                            offset += 4;
                            if offset + len > bytes.len() {
                                offset -= 4; // roll back so the tail print below starts at the right spot
                                break;
                            }
                            fields.push(&bytes[offset..offset + len]);
                            offset += len;
                        }
                        if fields.len() == 3 {
                            let tmp = std::env::temp_dir();
                            std::fs::write(tmp.join("vfy_g16_fail_proof_bytes.bin"), fields[0]).ok();
                            std::fs::write(tmp.join("vfy_g16_fail_pv_encode.bin"), fields[1]).ok();
                            std::fs::write(tmp.join("vfy_g16_fail_vkey_hash.txt"), fields[2]).ok();
                            eprintln!(
                                "[VFY-G16-DIAG] dumped failing inputs to {}/vfy_g16_fail_*",
                                tmp.display()
                            );
                        }
                        eprintln!(
                            "[VFY-G16-DIAG] committed output (exit_code!=0): {}",
                            String::from_utf8_lossy(&bytes[offset..])
                        );
                    }
                }
                Err(e) => eprintln!("[VFY-G16-DIAG] execute FAILED: {e}"),
            }
            // ── Proof ──────────────────────────────────────────────────────────────
            let pk = client.setup(VFY_G16_ELF).expect("setup vfy-g16");
            client.prove(&pk, stdin).compressed().run().expect("compressed prove")
        }
        other => panic!("unknown elf id: {other}"),
    };
    let proof_bytes = bincode::serialize(&proof).expect("serialize proof");
    std::fs::write(output_path, proof_bytes).expect("write proof file");
}

/// Build the `SpendProofPackage` stored in `tx.spend_proof`.
fn build_spend_proof_package(
    proof: &SP1ProofWithPublicValues,
    spend_vkey_hash: String,
) -> SpendProofPackage {
    let proof_bytes = proof.bytes();
    let pv_encode = proof.public_values.as_slice().to_vec();
    SpendProofPackage { proof_bytes, pv_encode, spend_vkey_hash }
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

/// Build stdin for a VFY_G16_ELF proving run.
fn build_vfy_g16_stdin(spend_proof_bytes: &[u8], pv_encode: &[u8], spend_vkey_hash: &str) -> SP1Stdin {
    let mut stdin = SP1Stdin::new();
    stdin.write_vec(spend_proof_bytes.to_vec());
    stdin.write_vec(pv_encode.to_vec());
    stdin.write(&spend_vkey_hash.to_string());
    stdin
}

// ---- stdin builders ---------------------------------------------------------

/// Build the base stdin for a coinproof step (compressed STARK).
/// Proofs for deferred verify_sp1_proof must be added by the caller via write_proof
/// in this order: inner coin-proof (if step case), then validation proof (if receipt slot).
fn build_coinproof_stdin(
    coinproof_vkey: &[u32; 8],
    vfy_g16_vkey: &[u32; 8],
    owner_sk: [u8; 32], coin_commitment: [u8; 32],
    entry_k: &BoardEntry, slot: usize, append_path: &[[u8; 32]],
    inner_pv: Option<&CoinProofPublicValues>,
    parent_nullifier: [u8; 32], own_nullifier: [u8; 32],
) -> SP1Stdin {
    let mut stdin = SP1Stdin::new();
    stdin.write(coinproof_vkey);
    stdin.write(vfy_g16_vkey);
    stdin.write(&owner_sk);
    stdin.write(&coin_commitment);
    stdin.write(entry_k);
    stdin.write(&slot);
    stdin.write(&append_path.to_vec());
    stdin.write(&inner_pv.is_some());
    if let Some(pv) = inner_pv {
        stdin.write(pv);
    }
    stdin.write(&parent_nullifier);
    stdin.write(&own_nullifier);
    stdin
}

/// Build the base stdin for a spend proof (Groth16).
/// The coin-proof (compressed STARK) must be added by the caller via write_proof
/// after this call (for non-genesis spends).
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
    if let Some(cp) = coin_proof {
        stdin.write(cp);
    }
    stdin
}


// ---- main -------------------------------------------------------------------

fn main() {
    sp1_sdk::utils::setup_logger();
    dotenv::dotenv().ok();

    // coinproof/vfy-g16 are custom guest programs whose recursion-circuit shapes aren't in
    // SP1's shipped vk_map.bin, so proving them needs WITHOUT_VK_VERIFICATION=1 (skip the
    // official vk allow-list, use a deterministic dummy root instead) - requires sp1-sdk's
    // "experimental" feature. That dummy root has to be used *consistently* everywhere a
    // vk_root gets checked or produced - including spend, since a non-genesis spend proof
    // folds in a prior coinproof proof as a deferred proof, and the two must agree on the
    // same root. SP1_CIRCUIT_MODE=dev makes spend's Groth16 wrap step rebuild its circuit
    // locally to match that dummy root, instead of expecting Succinct's official one (which
    // it otherwise hardcodes and can never satisfy once vk_verification is off).
    //
    // NOTE: both of these are dev/test-only mechanisms by SP1's own design (the dummy root
    // isn't a registered/audited vk set, and the SP1_CIRCUIT_MODE=dev Groth16 circuit is
    // built with a local, non-ceremony trusted setup rather than SP1's official one) - this
    // makes the pipeline run correctly end-to-end, but the resulting proofs are not
    // production/mainnet-grade until that's addressed separately (e.g. registering these
    // programs' shapes in a real vk_map).
    // FORCE_VK_VERIFICATION=1 skips both of the above (falls back to SP1's default
    // vk_verification=true + release circuit mode) - a temporary diagnostic toggle to
    // reproduce and inspect the original "vk not allowed" error with the new [VK-DIAG]
    // print in vendor/sp1-prover (set RECURSION_DIAG=1 too, to actually see it), without
    // needing to hand-edit/revert this block for a one-off investigative run.
    if std::env::var("FORCE_VK_VERIFICATION").map(|v| v == "1").unwrap_or(false) {
        eprintln!("[main] FORCE_VK_VERIFICATION=1: using default vk_verification=true, release circuit mode");
    } else {
        std::env::set_var("WITHOUT_VK_VERIFICATION", "1");
        std::env::set_var("SP1_CIRCUIT_MODE", "dev");
    }

    let args = Args::parse();

    // Subprocess mode: prove one program and exit.  Memory is fully freed when
    // this process exits, so the parent can start the next proof with clean RAM.
    if let (Some(elf_id), Some(stdin_path), Some(output_path)) = (
        &args.internal_prove_elf,
        &args.internal_prove_stdin,
        &args.internal_prove_output,
    ) {
        run_internal_prove(elf_id, stdin_path, output_path);
        return;
    }

    let mode_count = [args.execute, args.prove, args.bench_vfy_g16].iter().filter(|&&b| b).count();
    if mode_count != 1 {
        eprintln!("Error: specify exactly one of --execute, --prove, --bench-vfy-g16");
        std::process::exit(1);
    }

    // ---- --bench-vfy-g16 -------------------------------------------------------
    if args.bench_vfy_g16 {
        let client       = ProverClient::from_env();
        let spend_pk     = client.setup(CLOAKKCHAIN_SPEND_ELF).expect("setup spend elf");
        let coinproof_pk = client.setup(CLOAKKCHAIN_COINPROOF_ELF).expect("setup coinproof elf");
        let spend_vkey   = spend_pk.verifying_key().hash_u32();
        let coinproof_vkey = coinproof_pk.verifying_key().hash_u32();

        let genesis_b = Party { name: "Genesis", sk: GENESIS_SK, pk: genesis_pk() };
        let alice_b   = Party::new("Alice", 1);
        let genesis_coin_b = coin(0xA1, 100, genesis_b.pk);
        let alice_coin_b   = coin(0xA2, 100, alice_b.pk);
        let cn_genesis_b   = genesis_coin_b.commitment();
        let entries_b: Vec<BoardEntry> = vec![];

        println!("--- Step 1: generating genesis spend proof (Groth16) ---");
        let (tx0_b, _, _) = make_tx(0, GENESIS_SK,
            &[genesis_coin_b.clone()], &[(alice_coin_b.clone(), alice_b.pk)]);
        let stdin = build_spend_stdin(&spend_vkey, &coinproof_vkey, &genesis_b, cn_genesis_b,
            &entries_b, &tx0_b, &[genesis_coin_b.clone()], &[alice_coin_b.clone()], true, None);
        let t = Instant::now();
        let spend_proof = prove_subprocess("spend", &stdin);
        println!("  generated in {:.1}s ({} bytes)", t.elapsed().as_secs_f64(), spend_proof.bytes().len());

        println!("--- Step 2: executing VFY_G16_ELF to measure cycles ---");
        let proof_bytes    = spend_proof.bytes();
        let pv_encode      = spend_proof.public_values.as_slice().to_vec();
        let spend_vkey_hash = spend_pk.verifying_key().bytes32();
        let vfy_stdin = build_vfy_g16_stdin(&proof_bytes, &pv_encode, &spend_vkey_hash);
        let t = Instant::now();
        let (_, report) = client.execute(VFY_G16_ELF, vfy_stdin).run()
            .expect("VFY_G16_ELF execute failed");
        let exec_ms = t.elapsed().as_millis();
        println!("\n  VFY_G16 cycles : {}", fmt_cycles(report.total_instruction_count()));
        println!("  execute time   : {} ms", exec_ms);
        println!("{}", report);
        return;
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

    let mut entries: Vec<BoardEntry> = vec![];

    // ---- --execute ----------------------------------------------------------
    if args.execute {
        let client       = MockProver::new();
        let spend_pk     = client.setup(CLOAKKCHAIN_SPEND_ELF).expect("setup spend elf");
        let coinproof_pk = client.setup(CLOAKKCHAIN_COINPROOF_ELF).expect("setup coinproof elf");
        let vfy_g16_pk   = client.setup(VFY_G16_ELF).expect("setup vfy_g16 elf");
        let spend_vkey      = spend_pk.verifying_key().hash_u32();
        let coinproof_vkey  = coinproof_pk.verifying_key().hash_u32();
        let vfy_g16_vkey    = vfy_g16_pk.verifying_key().hash_u32();
        println!("spend vkey:     {}", spend_pk.verifying_key().bytes32());
        println!("coinproof vkey: {}", coinproof_pk.verifying_key().bytes32());
        println!("vfy_g16 vkey:   {}", vfy_g16_pk.verifying_key().bytes32());

        let mut stats: Vec<ExecStats> = Vec::new();

        // Slot 0: genesis mint.
        let (mut tx0, s0, r0) = make_tx(0, GENESIS_SK, &[genesis_coin.clone()], &[(alice_coin.clone(), alice.pk)]);
        let stdin = build_spend_stdin(&spend_vkey, &coinproof_vkey, &genesis, cn_genesis,
            &entries, &tx0, &[genesis_coin.clone()], &[alice_coin.clone()], true, None);
        let t = Instant::now();
        let (output, report) = client.execute(CLOAKKCHAIN_SPEND_ELF, stdin).run().unwrap();
        let exec_ms = t.elapsed().as_millis();
        let pv: ValidPublicValues = bincode::deserialize(output.as_slice()).expect("decode");
        assert_eq!(pv.board_root, merkle_root_of(&entries));
        let mock_pkg = SpendProofPackage {
            proof_bytes: vec![],
            pv_encode: pv.encode(),
            spend_vkey_hash: String::new(),
        };
        tx0.spend_proof = bincode::serialize(&mock_pkg).expect("serialize mock pkg");
        entries.push(encrypt_tx(&tx0, &r0, s0));
        stats.push(ExecStats { name: "Slot 0: genesis mint (spend)".into(), board_size: 1, exec_ms, cycles: report.total_instruction_count() });

        let ap0 = append_proof_for(&entries[..1]);
        for (owner_sk, label) in [(alice.sk, "Alice"), (bob.sk, "Bob  "), (carol.sk, "Carol")] {
            let pn = [0u8; 32];
            let on = nullifier(cn_alice, owner_sk);
            let stdin = build_coinproof_stdin(
                &coinproof_vkey, &vfy_g16_vkey,
                owner_sk, cn_alice,
                &entries[0], 0, &ap0, None, pn, on,
            );
            // No write_proof in execute mode — verify_sp1_proof is a no-op in native.
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
    let vfy_g16_pk   = client.setup(VFY_G16_ELF).expect("setup vfy_g16 elf");

    let spend_vkey     = spend_pk.verifying_key().hash_u32();
    let coinproof_vkey = coinproof_pk.verifying_key().hash_u32();
    let vfy_g16_vkey   = vfy_g16_pk.verifying_key().hash_u32();
    println!("spend vkey:     {}", spend_pk.verifying_key().bytes32());
    println!("coinproof vkey: {}", coinproof_pk.verifying_key().bytes32());
    println!("vfy_g16 vkey:   {}", vfy_g16_pk.verifying_key().bytes32());

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
    // Genesis is_genesis=true → no coin-proof write_proof needed.
    let t = Instant::now();
    let genesis_proof = prove_subprocess("spend", &stdin);
    let prove_secs = t.elapsed().as_secs_f64();
    let t = Instant::now();
    client.verify(&genesis_proof, spend_pk.verifying_key(), None).expect("genesis verify");
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let pv: ValidPublicValues = bincode::deserialize(genesis_proof.public_values.as_slice()).expect("decode");
    assert_eq!(pv.board_root, merkle_root_of(&entries));
    let genesis_pkg = build_spend_proof_package(&genesis_proof, spend_pk.verifying_key().bytes32());
    let genesis_proof_size = bincode::serialize(&genesis_pkg).map(|v| v.len()).unwrap_or(0);
    tx0.spend_proof = bincode::serialize(&genesis_pkg).expect("serialize spend proof package");
    entries.push(encrypt_tx(&tx0, &r0, s0));
    let e0_bytes = bincode::serialize(&entries[0]).map(|v| v.len()).unwrap_or(0);
    stats.push(ProveStats { name: "Slot 0: genesis mint".into(), board_size: 1, prove_secs, verify_ms, proof_bytes: Some(genesis_proof_size), entry_bytes: Some(e0_bytes) });
    println!("  Proved & verified ({prove_secs:.1} s) — proof {} — entry {}", fmt_bytes(genesis_proof_size), fmt_bytes(e0_bytes));

    println!("--- Wallets scanning slot 0 ---");
    alice_wallet.process_slot(0, &entries, &spend_pk, &coinproof_pk, &coinproof_vkey, &vfy_g16_pk, &vfy_g16_vkey, &client, &mut stats);
    bob_wallet  .process_slot(0, &entries, &spend_pk, &coinproof_pk, &coinproof_vkey, &vfy_g16_pk, &vfy_g16_vkey, &client, &mut stats);
    carol_wallet.process_slot(0, &entries, &spend_pk, &coinproof_pk, &coinproof_vkey, &vfy_g16_pk, &vfy_g16_vkey, &client, &mut stats);

    // =========================================================================
    // Slot 1: Alice sends 40 to Bob + 60 change
    // =========================================================================
    println!("\n--- Slot 1: Alice spends to Bob + change (1 input → 2 outputs) ---");
    let (mut tx1, s1, r1) = make_tx(1, alice.sk, &[alice_coin.clone()],
        &[(bob_coin.clone(), bob.pk), (alice_change.clone(), alice.pk)]);
    let alice_record = alice_wallet.get(&cn_alice).expect("Alice must have cn_alice proof");
    let alice_cp     = alice_record.proof.clone();
    let mut stdin = build_spend_stdin(&spend_vkey, &coinproof_vkey, &alice, cn_alice,
        &entries, &tx1,
        &[alice_coin.clone()], &[bob_coin.clone(), alice_change.clone()],
        false, Some(&alice_record.pv));
    // Alice's coin-proof is a compressed STARK — extract inner proof for write_proof.
    let SP1Proof::Compressed(ac) = alice_cp.proof else { panic!("expected compressed coin-proof") };
    stdin.write_proof(*ac, coinproof_pk.verifying_key().vk.clone());
    let t = Instant::now();
    let alice_spend_proof = prove_subprocess("spend", &stdin);
    let prove_secs = t.elapsed().as_secs_f64();
    let t = Instant::now();
    client.verify(&alice_spend_proof, spend_pk.verifying_key(), None).expect("alice spend verify");
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let pv: ValidPublicValues = bincode::deserialize(alice_spend_proof.public_values.as_slice()).expect("decode");
    assert_eq!(pv.board_root, merkle_root_of(&entries));
    let alice_pkg = build_spend_proof_package(&alice_spend_proof, spend_pk.verifying_key().bytes32());
    let alice_proof_size = bincode::serialize(&alice_pkg).map(|v| v.len()).unwrap_or(0);
    tx1.spend_proof = bincode::serialize(&alice_pkg).expect("serialize spend proof package");
    entries.push(encrypt_tx(&tx1, &r1, s1));
    let e1_bytes = bincode::serialize(&entries[1]).map(|v| v.len()).unwrap_or(0);
    stats.push(ProveStats { name: "Slot 1: Alice's spend (groth16)".into(), board_size: 2, prove_secs, verify_ms, proof_bytes: Some(alice_proof_size), entry_bytes: Some(e1_bytes) });
    println!("  Proved & verified ({prove_secs:.1} s) — proof {} — entry {}", fmt_bytes(alice_proof_size), fmt_bytes(e1_bytes));

    println!("--- Wallets scanning slot 1 ---");
    alice_wallet.process_slot(1, &entries, &spend_pk, &coinproof_pk, &coinproof_vkey, &vfy_g16_pk, &vfy_g16_vkey, &client, &mut stats);
    bob_wallet  .process_slot(1, &entries, &spend_pk, &coinproof_pk, &coinproof_vkey, &vfy_g16_pk, &vfy_g16_vkey, &client, &mut stats);
    carol_wallet.process_slot(1, &entries, &spend_pk, &coinproof_pk, &coinproof_vkey, &vfy_g16_pk, &vfy_g16_vkey, &client, &mut stats);

    // =========================================================================
    // Slot 2: Bob sends 40 to Carol
    // =========================================================================
    println!("\n--- Slot 2: Bob spends to Carol (1 input → 1 output) ---");
    let (mut tx2, s2, r2) = make_tx(2, bob.sk, &[bob_coin.clone()], &[(carol_coin.clone(), carol.pk)]);
    let bob_record = bob_wallet.get(&cn_bob).expect("Bob must have cn_bob proof");
    let bob_cp     = bob_record.proof.clone();
    let mut stdin = build_spend_stdin(&spend_vkey, &coinproof_vkey, &bob, cn_bob,
        &entries, &tx2,
        &[bob_coin.clone()], &[carol_coin.clone()],
        false, Some(&bob_record.pv));
    let SP1Proof::Compressed(bc) = bob_cp.proof else { panic!("expected compressed coin-proof") };
    stdin.write_proof(*bc, coinproof_pk.verifying_key().vk.clone());
    let t = Instant::now();
    let bob_spend_proof = prove_subprocess("spend", &stdin);
    let prove_secs = t.elapsed().as_secs_f64();
    let t = Instant::now();
    client.verify(&bob_spend_proof, spend_pk.verifying_key(), None).expect("bob spend verify");
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let pv: ValidPublicValues = bincode::deserialize(bob_spend_proof.public_values.as_slice()).expect("decode");
    assert_eq!(pv.board_root, merkle_root_of(&entries));
    let bob_pkg = build_spend_proof_package(&bob_spend_proof, spend_pk.verifying_key().bytes32());
    let bob_proof_size = bincode::serialize(&bob_pkg).map(|v| v.len()).unwrap_or(0);
    tx2.spend_proof = bincode::serialize(&bob_pkg).expect("serialize spend proof package");
    entries.push(encrypt_tx(&tx2, &r2, s2));
    let e2_bytes = bincode::serialize(&entries[2]).map(|v| v.len()).unwrap_or(0);
    stats.push(ProveStats { name: "Slot 2: Bob's spend (groth16)".into(), board_size: 3, prove_secs, verify_ms, proof_bytes: Some(bob_proof_size), entry_bytes: Some(e2_bytes) });
    println!("  Proved & verified ({prove_secs:.1} s) — proof {} — entry {}", fmt_bytes(bob_proof_size), fmt_bytes(e2_bytes));

    println!("--- Wallets scanning slot 2 ---");
    alice_wallet.process_slot(2, &entries, &spend_pk, &coinproof_pk, &coinproof_vkey, &vfy_g16_pk, &vfy_g16_vkey, &client, &mut stats);
    bob_wallet  .process_slot(2, &entries, &spend_pk, &coinproof_pk, &coinproof_vkey, &vfy_g16_pk, &vfy_g16_vkey, &client, &mut stats);
    carol_wallet.process_slot(2, &entries, &spend_pk, &coinproof_pk, &coinproof_vkey, &vfy_g16_pk, &vfy_g16_vkey, &client, &mut stats);

    println!("\n=== Wallet States ===");
    alice_wallet.print_state();
    bob_wallet.print_state();
    carol_wallet.print_state();

    print_prove_table(&stats);
}
