//! Host driver for the `cloakkchain` IVC `CoinProof` + `Valid` (spend) relations.
//!
//! Models a realistic wallet per party. Each wallet watches the board and
//! updates its coin-proofs incrementally — one IVC step per new slot — instead
//! of hard-coding a fixed Genesis→Alice→Bob→Carol sequence with named local
//! variables. When a coin is first discovered (received as payment or change),
//! the wallet retroactively bootstraps its IVC chain from slot 0.
//!
//! ```shell
//! RUST_LOG=info cargo run --release -- --execute   # mock execution, no ZK proofs
//! RUST_LOG=info cargo run --release -- --prove     # full recursive chain (expensive)
//! ```

use std::collections::HashMap;
use std::time::Instant;

use clap::Parser;
use cloakkchain_lib::{
    append_proof_for, derive_pk, encrypt_tx, genesis_pk, merkle_root_of,
    scan_entry as lib_scan_entry, BoardEntry, Coin, CoinProofPublicValues, Transaction,
    ValidPublicValues, GENESIS_SK,
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
        Self {
            name,
            sk,
            pk: derive_pk(&sk),
        }
    }
}

// ---- Wallet -----------------------------------------------------------------
//
// Each party maintains a wallet: a map from coin_commitment to a CoinRecord
// holding the latest IVC coin-proof for that coin. When a new board entry
// arrives, the wallet:
//   1. Steps all already-tracked coins forward one slot (O(1) per coin via the
//      fixed-depth append proof).
//   2. Scans the new entry for coins the owner received (output or change).
//   3. Bootstraps any newly discovered coin's IVC chain from slot 0.
//
// When spending, the wallet looks up the latest proof for the desired coin and
// hands it to the spend circuit.

struct CoinRecord {
    pv: CoinProofPublicValues,
    proof: SP1ProofWithPublicValues,
}

impl CoinRecord {
    fn slot_covered(&self) -> usize {
        self.pv.board_size - 1
    }
}

struct Wallet<'a> {
    party: &'a Party,
    coins: HashMap<[u8; 32], CoinRecord>,
}

impl<'a> Wallet<'a> {
    fn new(party: &'a Party) -> Self {
        Self {
            party,
            coins: HashMap::new(),
        }
    }

    /// Advance every tracked coin by one IVC step, then discover and bootstrap
    /// any new coins found in `all_entries[slot]`.
    fn process_slot<C: Prover>(
        &mut self,
        slot: usize,
        all_entries: &[BoardEntry],
        registry: &[[u8; 32]],
        coinproof_pk: &C::ProvingKey,
        coinproof_vkey: &[u32; 8],
        client: &C,
        stats: &mut Vec<ProveStats>,
    ) {
        assert_eq!(
            all_entries.len(),
            slot + 1,
            "all_entries must include exactly up to slot"
        );
        let entry = &all_entries[slot];
        let ap = append_proof_for(all_entries);

        // Step 1: advance all existing coins by one slot.
        let tracked: Vec<[u8; 32]> = self.coins.keys().cloned().collect();
        for cn in &tracked {
            let record = self.coins.get(cn).unwrap();
            if record.slot_covered() >= slot {
                continue;
            }

            let inner_pv = record.pv.clone();
            let SP1Proof::Compressed(inner_c) = record.proof.proof.clone() else {
                panic!("coin records must use compressed proofs")
            };

            let mut stdin = build_coinproof_stdin(
                coinproof_vkey,
                self.party.pk,
                *cn,
                entry,
                slot,
                &ap,
                registry,
                Some(&inner_pv),
            );
            stdin.write_proof(*inner_c, coinproof_pk.verifying_key().vk.clone());

            let label = format!("{} coin-proof slot {} (step)", self.party.name, slot);
            let record =
                self.run_coinproof_step(stdin, &label, slot + 1, coinproof_pk, client, stats);
            self.coins.insert(*cn, record);
        }

        // Step 2: scan entry for newly received coins.
        if let Some(tx) = lib_scan_entry(&self.party.pk, registry, entry) {
            let candidates = [
                (tx.output_coin.owner_pk == self.party.pk).then_some(tx.output_coin.commitment()),
                (tx.change_coin.owner_pk == self.party.pk).then_some(tx.change_coin.commitment()),
            ];
            for cn in candidates.into_iter().flatten() {
                if !self.coins.contains_key(&cn) {
                    println!(
                        "  [{}] discovered new coin at slot {} — bootstrapping IVC from slot 0",
                        self.party.name, slot
                    );
                    self.bootstrap(
                        cn,
                        slot,
                        all_entries,
                        registry,
                        coinproof_pk,
                        coinproof_vkey,
                        client,
                        stats,
                    );
                }
            }
        }
    }

    /// Run IVC for a freshly discovered coin from slot 0 up to `up_to_slot`.
    fn bootstrap<C: Prover>(
        &mut self,
        cn: [u8; 32],
        up_to_slot: usize,
        all_entries: &[BoardEntry],
        registry: &[[u8; 32]],
        coinproof_pk: &C::ProvingKey,
        coinproof_vkey: &[u32; 8],
        client: &C,
        stats: &mut Vec<ProveStats>,
    ) {
        // Base case: slot 0.
        let ap0 = append_proof_for(&all_entries[..1]);
        let stdin = build_coinproof_stdin(
            coinproof_vkey,
            self.party.pk,
            cn,
            &all_entries[0],
            0,
            &ap0,
            registry,
            None,
        );
        let label = format!("{} coin-proof slot 0 (base)", self.party.name);
        let record = self.run_coinproof_step(stdin, &label, 1, coinproof_pk, client, stats);
        self.coins.insert(cn, record);

        // Recursive steps: slots 1..=up_to_slot.
        for s in 1..=up_to_slot {
            let aps = append_proof_for(&all_entries[..=s]);
            let rec = self.coins.get(&cn).unwrap();
            let inner_pv = rec.pv.clone();
            let SP1Proof::Compressed(inner_c) = rec.proof.proof.clone() else {
                panic!("compressed required")
            };

            let mut stdin = build_coinproof_stdin(
                coinproof_vkey,
                self.party.pk,
                cn,
                &all_entries[s],
                s,
                &aps,
                registry,
                Some(&inner_pv),
            );
            stdin.write_proof(*inner_c, coinproof_pk.verifying_key().vk.clone());

            let label = format!("{} coin-proof slot {} (bootstrap)", self.party.name, s);
            let record = self.run_coinproof_step(stdin, &label, s + 1, coinproof_pk, client, stats);
            self.coins.insert(cn, record);
        }
    }

    /// Prove one coin-proof step, verify, collect stats, return the record.
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
        let proof = client
            .prove(coinproof_pk, stdin)
            .compressed()
            .run()
            .unwrap_or_else(|e| panic!("coin-proof step failed: {e}"));
        let prove_secs = t.elapsed().as_secs_f64();

        let t = Instant::now();
        client
            .verify(&proof, coinproof_pk.verifying_key(), None)
            .expect("coin-proof verify failed");
        let verify_ms = t.elapsed().as_secs_f64() * 1000.0;

        let pv: CoinProofPublicValues =
            bincode::deserialize(proof.public_values.as_slice()).expect("decode coin-proof pv");

        println!(
            "  [{}]  received_at={:?}  spent={}  ({:.1}s)",
            label, pv.received_at, pv.spent, prove_secs
        );
        stats.push(ProveStats {
            name: label.to_string(),
            board_size,
            prove_secs,
            verify_ms,
            entry_bytes: None,
        });
        CoinRecord { pv, proof }
    }

    /// Return the latest coin-proof for a coin (if tracked).
    fn get(&self, cn: &[u8; 32]) -> Option<&CoinRecord> {
        self.coins.get(cn)
    }

    /// Print a summary of all tracked coins and their current state.
    fn print_state(&self) {
        println!("  {}:", self.party.name);
        if self.coins.is_empty() {
            println!("    (no coins tracked)");
            return;
        }
        for (cn, rec) in &self.coins {
            println!(
                "    cn={}..{}  received_at={:?}  spent={}  slot_covered={}",
                hex(&cn[..2]),
                hex(&cn[30..]),
                rec.pv.received_at,
                rec.pv.spent,
                rec.slot_covered()
            );
        }
    }
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{:02x}", x)).collect()
}

// ---- Statistics -------------------------------------------------------------

struct ProveStats {
    name: String,
    board_size: usize,
    prove_secs: f64,
    verify_ms: f64,
    entry_bytes: Option<usize>,
}

struct ExecStats {
    name: String,
    board_size: usize,
    exec_ms: u128,
    cycles: u64,
}

fn print_prove_table(stats: &[ProveStats]) {
    println!("\n{}", "=".repeat(80));
    println!("  Proof Statistics  (compressed recursive SP1 STARKs)");
    println!("{}", "=".repeat(80));
    println!(
        "{:<44} {:>5}  {:>9}  {:>10}  {:>10}",
        "Step", "Board", "Prove", "Verify", "Entry"
    );
    println!("{}", "-".repeat(80));
    let (mut tp, mut tv) = (0f64, 0f64);
    for s in stats {
        let entry_col = match s.entry_bytes {
            Some(b) => format!("{:>7} B", b),
            None => "       —".into(),
        };
        println!(
            "{:<44} {:>5}  {:>7.1} s  {:>8.1} ms  {}",
            s.name, s.board_size, s.prove_secs, s.verify_ms, entry_col
        );
        tp += s.prove_secs;
        tv += s.verify_ms;
    }
    println!("{}", "-".repeat(80));
    println!("{:<44} {:>5}  {:>7.1} s  {:>8.1} ms", "TOTAL", "", tp, tv);
    println!("{}", "=".repeat(80));
}

fn print_exec_table(stats: &[ExecStats]) {
    println!("\n{}", "=".repeat(70));
    println!("  Execution Statistics  (mock prover — no ZK proofs)");
    println!("{}", "=".repeat(70));
    println!(
        "{:<44} {:>5}  {:>14}  {:>8}",
        "Step", "Board", "Cycles", "Time"
    );
    println!("{}", "-".repeat(70));
    for s in stats {
        println!(
            "{:<44} {:>5}  {:>14}  {:>6} ms",
            s.name,
            s.board_size,
            fmt_cycles(s.cycles),
            s.exec_ms
        );
    }
    println!("{}", "=".repeat(70));
}

fn fmt_cycles(c: u64) -> String {
    let s = c.to_string();
    let mut out = String::new();
    for (i, ch) in s.chars().rev().enumerate() {
        if i > 0 && i % 3 == 0 {
            out.push(',');
        }
        out.push(ch);
    }
    out.chars().rev().collect()
}

// ---- Coin / chain helpers ---------------------------------------------------

fn coin(seed: u8, value: u64, owner_pk: [u8; 32]) -> Coin {
    let mut tag = [0u8; 32];
    tag[0] = seed;
    let mut rand = [0u8; 32];
    rand[1] = seed;
    Coin {
        tag,
        value,
        rand,
        owner_pk,
    }
}

fn demo_chain<'a>(
    alice: &'a Party,
    bob: &'a Party,
    carol: &'a Party,
    genesis: &'a Party,
) -> Vec<(&'a Party, Transaction)> {
    let genesis_coin = coin(0xA1, 100, genesis.pk);
    let alice_coin = coin(0xA2, 100, alice.pk);
    let genesis_change = coin(0xA3, 0, genesis.pk);
    let bob_coin = coin(0xB1, 40, bob.pk);
    let alice_change = coin(0xB2, 60, alice.pk);
    let carol_coin = coin(0xC1, 40, carol.pk);
    let bob_change = coin(0xC2, 0, bob.pk);
    vec![
        (
            genesis,
            Transaction {
                id: 0,
                sender_pk: genesis.pk,
                recipient_pk: alice.pk,
                input_coin: genesis_coin,
                output_coin: alice_coin.clone(),
                change_coin: genesis_change,
                spend_proof: vec![],
            },
        ),
        (
            alice,
            Transaction {
                id: 1,
                sender_pk: alice.pk,
                recipient_pk: bob.pk,
                input_coin: alice_coin,
                output_coin: bob_coin.clone(),
                change_coin: alice_change,
                spend_proof: vec![],
            },
        ),
        (
            bob,
            Transaction {
                id: 2,
                sender_pk: bob.pk,
                recipient_pk: carol.pk,
                input_coin: bob_coin,
                output_coin: carol_coin,
                change_coin: bob_change,
                spend_proof: vec![],
            },
        ),
    ]
}

// ---- stdin builders ---------------------------------------------------------

fn build_coinproof_stdin(
    coinproof_vkey: &[u32; 8],
    owner_pk: [u8; 32],
    coin_commitment: [u8; 32],
    entry_k: &BoardEntry,
    slot: usize,
    append_path: &[[u8; 32]],
    registry: &[[u8; 32]],
    inner: Option<&CoinProofPublicValues>,
) -> SP1Stdin {
    let mut stdin = SP1Stdin::new();
    stdin.write(coinproof_vkey);
    stdin.write(&owner_pk);
    stdin.write(&coin_commitment);
    stdin.write(entry_k);
    stdin.write(&slot);
    stdin.write(&append_path.to_vec());
    stdin.write(&registry.to_vec());
    stdin.write(&inner.is_some());
    if let Some(pv) = inner {
        stdin.write(pv);
    }
    stdin
}

fn build_spend_stdin(
    spend_vkey: &[u32; 8],
    coinproof_vkey: &[u32; 8],
    sender: &Party,
    coin_commitment: [u8; 32],
    prior_entries: &[BoardEntry],
    tx_star: &Transaction,
    is_genesis: bool,
    coin_proof: Option<&CoinProofPublicValues>,
) -> SP1Stdin {
    let mut stdin = SP1Stdin::new();
    stdin.write(spend_vkey);
    stdin.write(coinproof_vkey);
    stdin.write(&sender.sk);
    stdin.write(&sender.pk);
    stdin.write(&coin_commitment);
    stdin.write(&prior_entries.to_vec());
    stdin.write(tx_star);
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

    let args = Args::parse();
    if args.execute == args.prove {
        eprintln!("Error: specify either --execute or --prove");
        std::process::exit(1);
    }

    let alice = Party::new("Alice", 1);
    let bob = Party::new("Bob", 2);
    let carol = Party::new("Carol", 3);
    let genesis = Party {
        name: "Genesis",
        sk: GENESIS_SK,
        pk: genesis_pk(),
    };
    let registry = vec![genesis.pk, alice.pk, bob.pk, carol.pk];

    let mut chain: Vec<(&Party, Transaction)> = demo_chain(&alice, &bob, &carol, &genesis);
    let mut entries: Vec<BoardEntry> = chain.iter().map(|(_, tx)| encrypt_tx(tx)).collect();

    // ---- --execute: mock prover (no ZK proofs, just logic verification) -----
    if args.execute {
        let client = MockProver::new();
        let spend_pk = client
            .setup(CLOAKKCHAIN_SPEND_ELF)
            .expect("setup spend elf");
        let coinproof_pk = client
            .setup(CLOAKKCHAIN_COINPROOF_ELF)
            .expect("setup coinproof elf");
        let spend_vkey = spend_pk.verifying_key().hash_u32();
        let coinproof_vkey = coinproof_pk.verifying_key().hash_u32();
        println!("spend vkey:     {}", spend_pk.verifying_key().bytes32());
        println!("coinproof vkey: {}", coinproof_pk.verifying_key().bytes32());

        let mut stats: Vec<ExecStats> = Vec::new();

        // --- Slot 0: genesis mint ---
        let cn_genesis = chain[0].1.input_coin.commitment();
        let stdin = build_spend_stdin(
            &spend_vkey,
            &coinproof_vkey,
            &genesis,
            cn_genesis,
            &entries[..0],
            &chain[0].1,
            true,
            None,
        );
        let t = Instant::now();
        let (output, report) = client.execute(CLOAKKCHAIN_SPEND_ELF, stdin).run().unwrap();
        let exec_ms = t.elapsed().as_millis();
        let pv: ValidPublicValues = bincode::deserialize(output.as_slice()).expect("decode");
        assert_eq!(pv.board_root, merkle_root_of(&entries[..0]));
        chain[0].1.spend_proof = output.to_vec();
        entries[0] = encrypt_tx(&chain[0].1);
        stats.push(ExecStats {
            name: "Slot 0: genesis mint (spend)".into(),
            board_size: 1,
            exec_ms,
            cycles: report.total_instruction_count(),
        });

        // Wallets scan slot 0 (base case only — no recursive proofs in execute mode).
        // Each party scans for their own coin: Alice for cn_alice, others for theirs.
        let ap0 = append_proof_for(&entries[..1]);
        let cn_alice = chain[0].1.output_coin.commitment();
        for (owner_pk, cn, label) in [
            (&alice.pk, cn_alice, "Alice"),
            (&bob.pk, cn_alice, "Bob  "), // bob hasn't received yet — received_at=None
            (&carol.pk, cn_alice, "Carol"), // same
        ] {
            let stdin = build_coinproof_stdin(
                &coinproof_vkey,
                *owner_pk,
                cn,
                &entries[0],
                0,
                &ap0,
                &registry,
                None,
            );
            let t = Instant::now();
            let (output, report) = client
                .execute(CLOAKKCHAIN_COINPROOF_ELF, stdin)
                .run()
                .unwrap();
            let exec_ms = t.elapsed().as_millis();
            let cp: CoinProofPublicValues =
                bincode::deserialize(output.as_slice()).expect("decode");
            stats.push(ExecStats {
                name: format!("{label} coin-proof slot 0"),
                board_size: 1,
                exec_ms,
                cycles: report.total_instruction_count(),
            });
            println!(
                "  [{label} slot 0] received_at={:?} spent={}",
                cp.received_at, cp.spent
            );
        }

        print_exec_table(&stats);
        println!("\nRun --prove for the full recursive chain with real ZK proofs.");
        return;
    }

    // ---- --prove: wallet-based incremental IVC + real compressed proofs -----
    let client = ProverClient::from_env();
    let spend_pk = client
        .setup(CLOAKKCHAIN_SPEND_ELF)
        .expect("setup spend elf");
    let coinproof_pk = client
        .setup(CLOAKKCHAIN_COINPROOF_ELF)
        .expect("setup coinproof elf");
    let spend_vkey = spend_pk.verifying_key().hash_u32();
    let coinproof_vkey = coinproof_pk.verifying_key().hash_u32();
    println!("spend vkey:     {}", spend_pk.verifying_key().bytes32());
    println!("coinproof vkey: {}", coinproof_pk.verifying_key().bytes32());

    let mut alice_wallet = Wallet::new(&alice);
    let mut bob_wallet = Wallet::new(&bob);
    let mut carol_wallet = Wallet::new(&carol);
    let mut stats: Vec<ProveStats> = Vec::new();

    // =========================================================================
    // Slot 0: genesis mints 100 units to Alice
    // =========================================================================
    let cn_genesis = chain[0].1.input_coin.commitment();
    let cn_alice = chain[0].1.output_coin.commitment();

    println!("\n--- Slot 0: genesis mint ---");
    let stdin = build_spend_stdin(
        &spend_vkey,
        &coinproof_vkey,
        &genesis,
        cn_genesis,
        &entries[..0],
        &chain[0].1,
        true,
        None,
    );
    let t = Instant::now();
    let proof = client
        .prove(&spend_pk, stdin)
        .compressed()
        .run()
        .expect("genesis mint prove");
    let prove_secs = t.elapsed().as_secs_f64();
    let t = Instant::now();
    client
        .verify(&proof, spend_pk.verifying_key(), None)
        .expect("genesis mint verify");
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let pv: ValidPublicValues =
        bincode::deserialize(proof.public_values.as_slice()).expect("decode");
    assert_eq!(pv.board_root, merkle_root_of(&entries[..0]));
    chain[0].1.spend_proof = proof.public_values.to_vec();
    entries[0] = encrypt_tx(&chain[0].1);
    let entry0_bytes = entries[0].ciphertext.len();
    stats.push(ProveStats {
        name: "Slot 0: genesis mint (spend)".into(),
        board_size: 1,
        prove_secs,
        verify_ms,
        entry_bytes: Some(entry0_bytes),
    });
    println!("  Proved & verified ({prove_secs:.1} s) — entry now {entry0_bytes} B");

    // All wallets scan slot 0
    println!("--- Wallets scanning slot 0 ---");
    alice_wallet.process_slot(
        0,
        &entries[..1],
        &registry,
        &coinproof_pk,
        &coinproof_vkey,
        &client,
        &mut stats,
    );
    bob_wallet.process_slot(
        0,
        &entries[..1],
        &registry,
        &coinproof_pk,
        &coinproof_vkey,
        &client,
        &mut stats,
    );
    carol_wallet.process_slot(
        0,
        &entries[..1],
        &registry,
        &coinproof_pk,
        &coinproof_vkey,
        &client,
        &mut stats,
    );

    // =========================================================================
    // Slot 1: Alice spends cn_alice, sends 40 to Bob, keeps 60 change
    // =========================================================================
    println!("\n--- Slot 1: Alice spends to Bob ---");
    let alice_record = alice_wallet
        .get(&cn_alice)
        .expect("Alice must have coin-proof for cn_alice");
    let mut stdin = build_spend_stdin(
        &spend_vkey,
        &coinproof_vkey,
        &alice,
        cn_alice,
        &entries[..1],
        &chain[1].1,
        false,
        Some(&alice_record.pv),
    );
    {
        let SP1Proof::Compressed(inner) = alice_record.proof.proof.clone() else {
            panic!("compressed required")
        };
        stdin.write_proof(*inner, coinproof_pk.verifying_key().vk.clone());
    }
    let t = Instant::now();
    let proof = client
        .prove(&spend_pk, stdin)
        .compressed()
        .run()
        .expect("alice spend prove");
    let prove_secs = t.elapsed().as_secs_f64();
    let t = Instant::now();
    client
        .verify(&proof, spend_pk.verifying_key(), None)
        .expect("alice spend verify");
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let pv: ValidPublicValues =
        bincode::deserialize(proof.public_values.as_slice()).expect("decode");
    assert_eq!(pv.board_root, merkle_root_of(&entries[..1]));
    chain[1].1.spend_proof = proof.public_values.to_vec();
    entries[1] = encrypt_tx(&chain[1].1);
    let entry1_bytes = entries[1].ciphertext.len();
    stats.push(ProveStats {
        name: "Slot 1: Alice's spend (recursive)".into(),
        board_size: 2,
        prove_secs,
        verify_ms,
        entry_bytes: Some(entry1_bytes),
    });
    println!("  Proved & verified ({prove_secs:.1} s) — entry now {entry1_bytes} B");

    // All wallets scan slot 1
    println!("--- Wallets scanning slot 1 ---");
    alice_wallet.process_slot(
        1,
        &entries[..2],
        &registry,
        &coinproof_pk,
        &coinproof_vkey,
        &client,
        &mut stats,
    );
    bob_wallet.process_slot(
        1,
        &entries[..2],
        &registry,
        &coinproof_pk,
        &coinproof_vkey,
        &client,
        &mut stats,
    );
    carol_wallet.process_slot(
        1,
        &entries[..2],
        &registry,
        &coinproof_pk,
        &coinproof_vkey,
        &client,
        &mut stats,
    );

    // =========================================================================
    // Slot 2: Bob spends cn_bob, sends all 40 to Carol (no change)
    // =========================================================================
    let cn_bob = chain[1].1.output_coin.commitment();
    println!("\n--- Slot 2: Bob spends to Carol ---");
    let bob_record = bob_wallet
        .get(&cn_bob)
        .expect("Bob must have coin-proof for cn_bob");
    let mut stdin = build_spend_stdin(
        &spend_vkey,
        &coinproof_vkey,
        &bob,
        cn_bob,
        &entries[..2],
        &chain[2].1,
        false,
        Some(&bob_record.pv),
    );
    {
        let SP1Proof::Compressed(inner) = bob_record.proof.proof.clone() else {
            panic!("compressed required")
        };
        stdin.write_proof(*inner, coinproof_pk.verifying_key().vk.clone());
    }
    let t = Instant::now();
    let proof = client
        .prove(&spend_pk, stdin)
        .compressed()
        .run()
        .expect("bob spend prove");
    let prove_secs = t.elapsed().as_secs_f64();
    let t = Instant::now();
    client
        .verify(&proof, spend_pk.verifying_key(), None)
        .expect("bob spend verify");
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let pv: ValidPublicValues =
        bincode::deserialize(proof.public_values.as_slice()).expect("decode");
    assert_eq!(pv.board_root, merkle_root_of(&entries[..2]));
    chain[2].1.spend_proof = proof.public_values.to_vec();
    entries[2] = encrypt_tx(&chain[2].1);
    let entry2_bytes = entries[2].ciphertext.len();
    stats.push(ProveStats {
        name: "Slot 2: Bob's spend (recursive)".into(),
        board_size: 3,
        prove_secs,
        verify_ms,
        entry_bytes: Some(entry2_bytes),
    });
    println!("  Proved & verified ({prove_secs:.1} s) — entry now {entry2_bytes} B");

    // All wallets scan slot 2
    println!("--- Wallets scanning slot 2 ---");
    alice_wallet.process_slot(
        2,
        &entries[..3],
        &registry,
        &coinproof_pk,
        &coinproof_vkey,
        &client,
        &mut stats,
    );
    bob_wallet.process_slot(
        2,
        &entries[..3],
        &registry,
        &coinproof_pk,
        &coinproof_vkey,
        &client,
        &mut stats,
    );
    carol_wallet.process_slot(
        2,
        &entries[..3],
        &registry,
        &coinproof_pk,
        &coinproof_vkey,
        &client,
        &mut stats,
    );

    // =========================================================================
    // Summary
    // =========================================================================
    println!("\n=== Wallet States ===");
    alice_wallet.print_state();
    bob_wallet.print_state();
    carol_wallet.print_state();

    print_prove_table(&stats);
}
