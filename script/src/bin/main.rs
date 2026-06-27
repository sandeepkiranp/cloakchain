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
    merkle_root_of, scan_entry as lib_scan_entry, BoardEntry, Coin, CoinProofPublicValues,
    Transaction, ValidPublicValues, GENESIS_SK,
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
        sk[0] = seed;
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
        registry: &[[u8; 32]],
        spend_pk: &C::ProvingKey,
        coinproof_pk: &C::ProvingKey,
        spend_vkey: &[u32; 8],
        coinproof_vkey: &[u32; 8],
        client: &C,
        stats: &mut Vec<ProveStats>,
        proof_registry: &[Option<SP1ProofWithPublicValues>],
    ) {
        assert_eq!(all_entries.len(), slot + 1);
        let entry = &all_entries[slot];
        let ap = append_proof_for(all_entries);

        // Step all existing coins forward.
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
                spend_vkey, coinproof_vkey, self.party.pk, *cn, entry, slot, &ap, registry,
                Some(&inner_pv), parent_null, own_null,
            );
            stdin.write_proof(*inner_c, coinproof_pk.verifying_key().vk.clone());
            let label = format!("{} coin-proof slot {} (step)", self.party.name, slot);
            let rec = self.run_coinproof_step(stdin, &label, slot + 1, coinproof_pk, client, stats);
            self.coins.insert(*cn, rec);
        }

        // Discover new coins via note decryption.
        // scan_entry returns (tx, sender_pk); try decrypting each note_enc.
        if let Some((tx, sender_pk)) = lib_scan_entry(&self.party.pk, registry, entry) {
            for note_enc in tx.note_encs.iter() {
                if let Some(note_coin) = decrypt_note(&sender_pk, &self.party.pk, note_enc) {
                    // Only track coins that actually belong to this wallet owner.
                    // Without this check, the sender could accidentally decrypt a
                    // recipient's note (pair keys are symmetric).
                    if note_coin.owner_pk != self.party.pk { continue; }
                    let cn = note_coin.commitment();
                    if !self.coins.contains_key(&cn) {
                        println!("  [{}] discovered coin (value={}) at slot {} — bootstrapping",
                            self.party.name, note_coin.value, slot);
                        let receipt_proof = proof_registry.get(slot).and_then(|p| p.as_ref());
                        // parent_nullifier = input_nullifier of the creating tx (double-spend guard)
                        let parent_null = tx.input_nullifier;
                        self.bootstrap(cn, slot, all_entries, registry, spend_pk, coinproof_pk,
                            spend_vkey, coinproof_vkey, client, stats, receipt_proof, parent_null);
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
        registry: &[[u8; 32]],
        spend_pk: &C::ProvingKey,
        coinproof_pk: &C::ProvingKey,
        spend_vkey: &[u32; 8],
        coinproof_vkey: &[u32; 8],
        client: &C,
        stats: &mut Vec<ProveStats>,
        receipt_proof: Option<&SP1ProofWithPublicValues>,
        parent_nullifier: [u8; 32],
    ) {
        let own_null = nullifier(cn, self.party.sk);
        let ap0 = append_proof_for(&all_entries[..1]);
        let mut stdin = build_coinproof_stdin(
            spend_vkey, coinproof_vkey, self.party.pk, cn, &all_entries[0], 0, &ap0, registry,
            None, parent_nullifier, own_null,
        );
        // When the coin is received at slot 0 (up_to_slot == 0), the base case
        // IS the receipt step — write the spend proof so verify_sp1_proof can
        // consume it inside the zkVM.
        if up_to_slot == 0 {
            if let Some(proof) = receipt_proof {
                if let SP1Proof::Compressed(inner_spend) = proof.proof.clone() {
                    stdin.write_proof(*inner_spend, spend_pk.verifying_key().vk.clone());
                }
            }
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
                spend_vkey, coinproof_vkey, self.party.pk, cn, &all_entries[s], s, &aps, registry,
                Some(&inner_pv), parent_nullifier, own_null,
            );
            stdin.write_proof(*inner_c, coinproof_pk.verifying_key().vk.clone());

            if s == up_to_slot {
                if let Some(proof) = receipt_proof {
                    if let SP1Proof::Compressed(inner_spend) = proof.proof.clone() {
                        stdin.write_proof(*inner_spend, spend_pk.verifying_key().vk.clone());
                    }
                }
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
        println!("  [{}]  received_at={:?}  spent={}  ({:.1}s)", label, pv.received_at, pv.spent, prove_secs);
        stats.push(ProveStats { name: label.to_string(), board_size, prove_secs, verify_ms, entry_bytes: None });
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

struct ProveStats { name: String, board_size: usize, prove_secs: f64, verify_ms: f64, entry_bytes: Option<usize> }
struct ExecStats  { name: String, board_size: usize, exec_ms: u128, cycles: u64 }

fn print_prove_table(stats: &[ProveStats]) {
    println!("\n{}", "=".repeat(80));
    println!("  Proof Statistics  (compressed recursive SP1 STARKs)");
    println!("{}", "=".repeat(80));
    println!("{:<44} {:>5}  {:>9}  {:>10}  {:>10}", "Step", "Board", "Prove", "Verify", "Entry");
    println!("{}", "-".repeat(80));
    let (mut tp, mut tv) = (0f64, 0f64);
    for s in stats {
        let entry_col = match s.entry_bytes { Some(b) => format!("{:>7} B", b), None => "       —".into() };
        println!("{:<44} {:>5}  {:>7.1} s  {:>8.1} ms  {}", s.name, s.board_size, s.prove_secs, s.verify_ms, entry_col);
        tp += s.prove_secs; tv += s.verify_ms;
    }
    println!("{}", "-".repeat(80));
    println!("{:<44} {:>5}  {:>7.1} s  {:>8.1} ms", "TOTAL", "", tp, tv);
    println!("{}", "=".repeat(80));
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

/// Build a Transaction. Returns `(tx, sender_pk, recipient_pks)` — the last two
/// are needed for `encrypt_tx` but are NOT stored inside the transaction.
fn make_tx(
    id: u64,
    sender_sk: [u8; 32],
    input_coins: &[Coin],
    outputs: &[(Coin, [u8; 32])],
) -> (Transaction, [u8; 32], Vec<[u8; 32]>) {
    let sender_pk = derive_pk(&sender_sk);
    let input_commitments: Vec<[u8; 32]>  = input_coins.iter().map(|c| c.commitment()).collect();
    let recipient_pks: Vec<[u8; 32]>      = outputs.iter().map(|(_, rpk)| *rpk).collect();
    let output_commitments: Vec<[u8; 32]> = outputs.iter().map(|(c, _)| c.commitment()).collect();
    let note_encs: Vec<Vec<u8>>           = outputs.iter()
        .map(|(c, rpk)| build_note_enc(&sender_pk, rpk, c)).collect();
    let input_nullifier = nullifier(input_commitments[0], sender_sk);
    let tx = Transaction { id, input_commitments, output_commitments, note_encs, input_nullifier, spend_proof: vec![] };
    (tx, sender_pk, recipient_pks)
}

// ---- stdin builders ---------------------------------------------------------

fn build_coinproof_stdin(
    spend_vkey: &[u32; 8],
    coinproof_vkey: &[u32; 8], owner_pk: [u8; 32], coin_commitment: [u8; 32],
    entry_k: &BoardEntry, slot: usize, append_path: &[[u8; 32]],
    registry: &[[u8; 32]], inner: Option<&CoinProofPublicValues>,
    parent_nullifier: [u8; 32], own_nullifier: [u8; 32],
) -> SP1Stdin {
    let mut stdin = SP1Stdin::new();
    stdin.write(coinproof_vkey);
    stdin.write(spend_vkey);
    stdin.write(&owner_pk);
    stdin.write(&coin_commitment);
    stdin.write(entry_k);
    stdin.write(&slot);
    stdin.write(&append_path.to_vec());
    stdin.write(&registry.to_vec());
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
    let registry = vec![genesis.pk, alice.pk, bob.pk, carol.pk];

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
        tx0.spend_proof = output.to_vec();
        entries.push(encrypt_tx(&tx0, &s0, &r0)); // board now has slot 0
        stats.push(ExecStats { name: "Slot 0: genesis mint (spend)".into(), board_size: 1, exec_ms, cycles: report.total_instruction_count() });

        let ap0 = append_proof_for(&entries[..1]);
        for (owner_pk, owner_sk, label) in [(&alice.pk, alice.sk, "Alice"), (&bob.pk, bob.sk, "Bob  "), (&carol.pk, carol.sk, "Carol")] {
            let pn = [0u8; 32]; // zero parent nullifier for base case in execute mode
            let on = nullifier(cn_alice, owner_sk);
            let stdin = build_coinproof_stdin(&spend_vkey, &coinproof_vkey, *owner_pk, cn_alice,
                &entries[0], 0, &ap0, &registry, None, pn, on);
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
    // proof_registry[slot] = the spend proof for that board slot, used by
    // wallets to write_proof for the receipt step without embedding large
    // proof bytes (~1 MB) in the encrypted transaction.
    let mut proof_registry: Vec<Option<SP1ProofWithPublicValues>> = vec![];

    // =========================================================================
    // Slot 0: genesis mints 100 units to Alice
    // =========================================================================
    println!("\n--- Slot 0: genesis mint (1 input → 1 output) ---");
    // tx0 is built here — no future transactions exist yet.
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
    tx0.spend_proof = genesis_proof.public_values.to_vec();
    entries.push(encrypt_tx(&tx0, &s0, &r0)); // board: [slot 0]
    proof_registry.push(Some(genesis_proof));
    let e0_bytes = entries[0].ciphertext.len();
    stats.push(ProveStats { name: "Slot 0: genesis mint".into(), board_size: 1, prove_secs, verify_ms, entry_bytes: Some(e0_bytes) });
    println!("  Proved & verified ({prove_secs:.1} s) — entry now {e0_bytes} B");

    println!("--- Wallets scanning slot 0 ---");
    // entries now has exactly 1 element (slot 0) — wallets scan it.
    alice_wallet.process_slot(0, &entries, &registry, &spend_pk, &coinproof_pk, &spend_vkey, &coinproof_vkey, &client, &mut stats, &proof_registry);
    bob_wallet.process_slot(0, &entries, &registry, &spend_pk, &coinproof_pk, &spend_vkey, &coinproof_vkey, &client, &mut stats, &proof_registry);
    carol_wallet.process_slot(0, &entries, &registry, &spend_pk, &coinproof_pk, &spend_vkey, &coinproof_vkey, &client, &mut stats, &proof_registry);

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
    tx1.spend_proof = alice_spend_proof.public_values.to_vec();
    entries.push(encrypt_tx(&tx1, &s1, &r1)); // board: [slot 0, slot 1]
    proof_registry.push(Some(alice_spend_proof));
    let e1_bytes = entries[1].ciphertext.len();
    stats.push(ProveStats { name: "Slot 1: Alice's spend (recursive)".into(), board_size: 2, prove_secs, verify_ms, entry_bytes: Some(e1_bytes) });
    println!("  Proved & verified ({prove_secs:.1} s) — entry now {e1_bytes} B");

    println!("--- Wallets scanning slot 1 ---");
    // entries now has 2 elements (slots 0 and 1).
    alice_wallet.process_slot(1, &entries, &registry, &spend_pk, &coinproof_pk, &spend_vkey, &coinproof_vkey, &client, &mut stats, &proof_registry);
    bob_wallet.process_slot(1, &entries, &registry, &spend_pk, &coinproof_pk, &spend_vkey, &coinproof_vkey, &client, &mut stats, &proof_registry);
    carol_wallet.process_slot(1, &entries, &registry, &spend_pk, &coinproof_pk, &spend_vkey, &coinproof_vkey, &client, &mut stats, &proof_registry);

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
    tx2.spend_proof = bob_spend_proof.public_values.to_vec();
    entries.push(encrypt_tx(&tx2, &s2, &r2)); // board: [slot 0, slot 1, slot 2]
    proof_registry.push(Some(bob_spend_proof));
    let e2_bytes = entries[2].ciphertext.len();
    stats.push(ProveStats { name: "Slot 2: Bob's spend (recursive)".into(), board_size: 3, prove_secs, verify_ms, entry_bytes: Some(e2_bytes) });
    println!("  Proved & verified ({prove_secs:.1} s) — entry now {e2_bytes} B");

    println!("--- Wallets scanning slot 2 ---");
    // entries now has 3 elements (slots 0, 1, and 2).
    alice_wallet.process_slot(2, &entries, &registry, &spend_pk, &coinproof_pk, &spend_vkey, &coinproof_vkey, &client, &mut stats, &proof_registry);
    bob_wallet.process_slot(2, &entries, &registry, &spend_pk, &coinproof_pk, &spend_vkey, &coinproof_vkey, &client, &mut stats, &proof_registry);
    carol_wallet.process_slot(2, &entries, &registry, &spend_pk, &coinproof_pk, &spend_vkey, &coinproof_vkey, &client, &mut stats, &proof_registry);

    println!("\n=== Wallet States ===");
    alice_wallet.print_state();
    bob_wallet.print_state();
    carol_wallet.print_state();

    print_prove_table(&stats);
}
