//! Host driver for the `cloakkchain` IVC `CoinProof` + `Valid` (spend) relations.
//!
//! Builds a small encrypted bulletin board — genesis mints a coin to Alice,
//! Alice sends it to Bob, Bob sends it to Carol — and runs:
//!
//!   - `cloakkchain-program-coinproof`: one recursive step per board slot, per
//!     unspent coin, tracking whether (and where) its owner received the coin
//!     and whether they've already spent it.
//!   - `cloakkchain-program-spend`: the actual transfer, which (for non-genesis
//!     spends) recursively verifies the spender's latest coin-proof.
//!
//! ## Encrypted board
//!
//! Every board entry is `encrypt_tx(tx)` — opaque to everyone except the
//! sender/recipient pair. Both relations decrypt in-circuit via
//! `extract_msg`/`scan_entry`. After proving, the spend proof is embedded
//! back into the transaction and the entry is re-encrypted so the proof
//! travels inside the ciphertext on the board.
//!
//! ```shell
//! RUST_LOG=info cargo run --release -- --execute   # mock execution, no ZK proofs
//! RUST_LOG=info cargo run --release -- --prove     # full recursive chain (expensive)
//! ```

use std::time::Instant;

use clap::Parser;
use cloakkchain_lib::{
    append_proof_for, derive_pk, encrypt_tx, genesis_pk, merkle_root_of, BoardEntry, Coin,
    CoinProofPublicValues, Transaction, ValidPublicValues, GENESIS_SK,
};
use sp1_sdk::{
    blocking::{MockProver, ProveRequest, Prover, ProverClient},
    include_elf, Elf, HashableKey, ProvingKey, SP1Proof, SP1Stdin,
};

const CLOAKKCHAIN_SPEND_ELF: Elf = include_elf!("cloakkchain-program-spend");
const CLOAKKCHAIN_COINPROOF_ELF: Elf = include_elf!("cloakkchain-program-coinproof");

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(long)]
    execute: bool,
    #[arg(long)]
    prove: bool,
}

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

// ---- Statistics helpers -----------------------------------------------------

struct ExecStats {
    name: &'static str,
    board_size: usize,
    exec_ms: u128,
    cycles: u64,
}

struct ProveStats {
    name: &'static str,
    board_size: usize,
    prove_secs: f64,
    verify_ms: f64,
    entry_bytes: Option<usize>, // ciphertext size after proof embedding (spend steps only)
}

fn print_exec_table(stats: &[ExecStats]) {
    println!("\n{}", "=".repeat(70));
    println!("  Execution Statistics  (mock prover — no ZK proofs generated)");
    println!("{}", "=".repeat(70));
    println!("{:<40} {:>5}  {:>12}  {:>10}", "Step", "Board", "Cycles", "Time");
    println!("{}", "-".repeat(70));
    for s in stats {
        println!(
            "{:<40} {:>5}  {:>12}  {:>8} ms",
            s.name,
            s.board_size,
            format_cycles(s.cycles),
            s.exec_ms,
        );
    }
    println!("{}", "=".repeat(70));
}

fn print_prove_table(stats: &[ProveStats]) {
    println!("\n{}", "=".repeat(80));
    println!("  Proof Statistics  (compressed recursive SP1 STARKs)");
    println!("{}", "=".repeat(80));
    println!(
        "{:<42} {:>5}  {:>9}  {:>10}  {:>12}",
        "Step", "Board", "Prove", "Verify", "Entry size"
    );
    println!("{}", "-".repeat(80));

    let mut total_prove = 0f64;
    let mut total_verify = 0f64;

    for s in stats {
        let entry_col = match s.entry_bytes {
            Some(b) => format!("{:>8} B", b),
            None => "        —".into(),
        };
        println!(
            "{:<42} {:>5}  {:>7.1} s  {:>8.1} ms  {}",
            s.name,
            s.board_size,
            s.prove_secs,
            s.verify_ms,
            entry_col,
        );
        total_prove += s.prove_secs;
        total_verify += s.verify_ms;
    }

    println!("{}", "-".repeat(80));
    println!(
        "{:<42} {:>5}  {:>7.1} s  {:>8.1} ms",
        "TOTAL", "", total_prove, total_verify
    );
    println!("{}", "=".repeat(80));
    println!("  Board = number of entries scanned/committed at that step.");
    println!("  Entry size = ciphertext length after the spend proof is embedded");
    println!("  (base ciphertext with empty proof = 400 B; grows by proof.len()).");
    println!("{}", "=".repeat(80));
}

fn format_cycles(c: u64) -> String {
    // Insert thousands separators.
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
    let mut tag = [0u8; 32];
    tag[0] = seed;
    let mut rand = [0u8; 32];
    rand[1] = seed;
    Coin { tag, value, rand, owner_pk }
}

/// The 3-tx demo chain: genesis mints a 100-unit coin to Alice. Alice sends 40
/// units to Bob (keeping 60 as change). Bob sends his 40 units to Carol (keeping
/// no change). Each entry is `(sender, transaction)`.
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

/// Build the SP1Stdin for one step of the coin-proof relation at `slot`.
/// Only `entry_k` (the new entry) and its `append_path` are passed — no full
/// history. `inner` is the previous step's public values, or `None` for the
/// base case (`slot == 0`).
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

/// Build the SP1Stdin for the spend relation. `prior_entries` is the board
/// before tx* (used for the anchor); `tx_star` is the spending transaction
/// passed as plaintext — no encrypt/decrypt round-trip inside the zkVM.
/// For non-genesis spends, `coin_proof` must cover `prior_entries`.
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
    let genesis = Party { name: "Genesis", sk: GENESIS_SK, pk: genesis_pk() };

    let registry = vec![genesis.pk, alice.pk, bob.pk, carol.pk];

    let mut chain = demo_chain(&alice, &bob, &carol, &genesis);
    let mut entries: Vec<BoardEntry> = chain.iter().map(|(_, tx)| encrypt_tx(tx)).collect();
    let cn_genesis = chain[0].1.input_coin.commitment();
    let cn_alice = chain[0].1.output_coin.commitment();
    let cn_bob = chain[1].1.output_coin.commitment();

    // ---- --execute: mock prover, measures cycles only ----------------------
    if args.execute {
        let client = MockProver::new();
        let spend_pk = client.setup(CLOAKKCHAIN_SPEND_ELF).expect("failed to setup spend elf");
        let coinproof_pk =
            client.setup(CLOAKKCHAIN_COINPROOF_ELF).expect("failed to setup coinproof elf");
        let spend_vkey = spend_pk.verifying_key().hash_u32();
        let coinproof_vkey = coinproof_pk.verifying_key().hash_u32();
        println!("spend vkey:     {}", spend_pk.verifying_key().bytes32());
        println!("coinproof vkey: {}", coinproof_pk.verifying_key().bytes32());

        let mut exec_stats: Vec<ExecStats> = Vec::new();

        // Genesis mints a 100-unit coin to Alice (slot 0). Prior board is empty.
        let stdin = build_spend_stdin(&spend_vkey, &coinproof_vkey, &genesis, cn_genesis, &entries[..0], &chain[0].1, true, None);
        let t = Instant::now();
        let (output, report) = client.execute(CLOAKKCHAIN_SPEND_ELF, stdin).run().unwrap();
        let exec_ms = t.elapsed().as_millis();
        let pv: ValidPublicValues = bincode::deserialize(output.as_slice()).expect("decode");
        assert_eq!(pv.board_root, merkle_root_of(&entries[..0]), "genesis: anchor mismatch");
        assert_eq!(pv.pk_p, genesis.pk);
        assert_eq!(pv.board_size, 1);
        chain[0].1.spend_proof = output.to_vec();
        entries[0] = encrypt_tx(&chain[0].1);
        exec_stats.push(ExecStats { name: "Genesis mint (spend)", board_size: 1, exec_ms, cycles: report.total_instruction_count() });

        // Alice's coin-proof step 0: she received her 100-unit coin at slot 0.
        let ap0 = append_proof_for(&entries[..1]);
        let stdin = build_coinproof_stdin(&coinproof_vkey, alice.pk, cn_alice, &entries[0], 0, &ap0, &registry, None);
        let t = Instant::now();
        let (output, report) = client.execute(CLOAKKCHAIN_COINPROOF_ELF, stdin).run().unwrap();
        let exec_ms = t.elapsed().as_millis();
        let alice_cp0: CoinProofPublicValues = bincode::deserialize(output.as_slice()).expect("decode");
        assert_eq!(alice_cp0.board_root, merkle_root_of(&entries[..1]));
        assert_eq!(alice_cp0.received_at, Some(0));
        assert_eq!(alice_cp0.spent, false);
        exec_stats.push(ExecStats { name: "Alice coin-proof step 0", board_size: 1, exec_ms, cycles: report.total_instruction_count() });

        // Bob's coin-proof step 0: slot 0 isn't his.
        let stdin = build_coinproof_stdin(&coinproof_vkey, bob.pk, cn_bob, &entries[0], 0, &ap0, &registry, None);
        let t = Instant::now();
        let (output, report) = client.execute(CLOAKKCHAIN_COINPROOF_ELF, stdin).run().unwrap();
        let exec_ms = t.elapsed().as_millis();
        let bob_cp0: CoinProofPublicValues = bincode::deserialize(output.as_slice()).expect("decode");
        assert_eq!(bob_cp0.board_root, merkle_root_of(&entries[..1]));
        assert_eq!(bob_cp0.received_at, None);
        assert_eq!(bob_cp0.spent, false);
        exec_stats.push(ExecStats { name: "Bob coin-proof step 0", board_size: 1, exec_ms, cycles: report.total_instruction_count() });

        print_exec_table(&exec_stats);
        println!("\nRun --prove for the full recursive chain with real ZK proofs.");
        return;
    }

    // ---- --prove: full recursive chain with real compressed proofs ---------
    let client = ProverClient::from_env();
    let spend_pk = client.setup(CLOAKKCHAIN_SPEND_ELF).expect("failed to setup spend elf");
    let coinproof_pk =
        client.setup(CLOAKKCHAIN_COINPROOF_ELF).expect("failed to setup coinproof elf");
    let spend_vkey = spend_pk.verifying_key().hash_u32();
    let coinproof_vkey = coinproof_pk.verifying_key().hash_u32();
    println!("spend vkey:     {}", spend_pk.verifying_key().bytes32());
    println!("coinproof vkey: {}", coinproof_pk.verifying_key().bytes32());

    let mut prove_stats: Vec<ProveStats> = Vec::new();

    // -- Genesis mint (slot 0, anchor = empty) --------------------------------
    println!("\nProving genesis mint...");
    let stdin = build_spend_stdin(&spend_vkey, &coinproof_vkey, &genesis, cn_genesis, &entries[..0], &chain[0].1, true, None);
    let t = Instant::now();
    let genesis_proof = client.prove(&spend_pk, stdin).compressed().run().expect("failed to prove genesis mint");
    let prove_secs = t.elapsed().as_secs_f64();
    let t = Instant::now();
    client.verify(&genesis_proof, spend_pk.verifying_key(), None).expect("failed to verify genesis mint");
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let genesis_pv: ValidPublicValues = bincode::deserialize(genesis_proof.public_values.as_slice()).expect("decode");
    assert_eq!(genesis_pv.board_root, merkle_root_of(&entries[..0]));
    chain[0].1.spend_proof = genesis_proof.public_values.to_vec();
    entries[0] = encrypt_tx(&chain[0].1);
    let entry0_bytes = entries[0].ciphertext.len();
    prove_stats.push(ProveStats { name: "Genesis mint (spend)", board_size: 1, prove_secs, verify_ms, entry_bytes: Some(entry0_bytes) });
    println!("  -> Genesis mint proved & verified ({prove_secs:.1} s)");

    // -- Alice coin-proof step 0 (base case) ----------------------------------
    println!("Proving Alice's coin-proof step 0...");
    let ap0 = append_proof_for(&entries[..1]);
    let stdin = build_coinproof_stdin(&coinproof_vkey, alice.pk, cn_alice, &entries[0], 0, &ap0, &registry, None);
    let t = Instant::now();
    let alice_cp0_proof = client.prove(&coinproof_pk, stdin).compressed().run().expect("failed to prove alice cp0");
    let prove_secs = t.elapsed().as_secs_f64();
    let t = Instant::now();
    client.verify(&alice_cp0_proof, coinproof_pk.verifying_key(), None).expect("failed to verify alice cp0");
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let alice_cp0: CoinProofPublicValues = bincode::deserialize(alice_cp0_proof.public_values.as_slice()).expect("decode");
    assert_eq!(alice_cp0.received_at, Some(0));
    assert_eq!(alice_cp0.spent, false);
    prove_stats.push(ProveStats { name: "Alice coin-proof step 0", board_size: 1, prove_secs, verify_ms, entry_bytes: None });
    println!("  -> Alice coin-proof step 0 proved & verified ({prove_secs:.1} s, received_at={:?})", alice_cp0.received_at);

    // -- Alice's spend (slot 1, recursive, anchor = entries[..1]) -------------
    println!("Proving Alice's spend...");
    let mut stdin = build_spend_stdin(&spend_vkey, &coinproof_vkey, &alice, cn_alice, &entries[..1], &chain[1].1, false, Some(&alice_cp0));
    {
        let SP1Proof::Compressed(inner) = alice_cp0_proof.proof.clone() else { panic!("compressed mode required") };
        stdin.write_proof(*inner, coinproof_pk.verifying_key().vk.clone());
    }
    let t = Instant::now();
    let alice_spend_proof = client.prove(&spend_pk, stdin).compressed().run().expect("failed to prove alice's spend");
    let prove_secs = t.elapsed().as_secs_f64();
    let t = Instant::now();
    client.verify(&alice_spend_proof, spend_pk.verifying_key(), None).expect("failed to verify alice's spend");
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let alice_spend_pv: ValidPublicValues = bincode::deserialize(alice_spend_proof.public_values.as_slice()).expect("decode");
    assert_eq!(alice_spend_pv.board_root, merkle_root_of(&entries[..1]));
    chain[1].1.spend_proof = alice_spend_proof.public_values.to_vec();
    entries[1] = encrypt_tx(&chain[1].1);
    let entry1_bytes = entries[1].ciphertext.len();
    prove_stats.push(ProveStats { name: "Alice's spend (recursive)", board_size: 2, prove_secs, verify_ms, entry_bytes: Some(entry1_bytes) });
    println!("  -> Alice's spend proved & verified ({prove_secs:.1} s)");

    // -- Bob coin-proof step 0 (base case, slot 0 is not his) -----------------
    println!("Proving Bob's coin-proof step 0...");
    let stdin = build_coinproof_stdin(&coinproof_vkey, bob.pk, cn_bob, &entries[0], 0, &ap0, &registry, None);
    let t = Instant::now();
    let bob_cp0_proof = client.prove(&coinproof_pk, stdin).compressed().run().expect("failed to prove bob cp0");
    let prove_secs = t.elapsed().as_secs_f64();
    let t = Instant::now();
    client.verify(&bob_cp0_proof, coinproof_pk.verifying_key(), None).expect("failed to verify bob cp0");
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let bob_cp0: CoinProofPublicValues = bincode::deserialize(bob_cp0_proof.public_values.as_slice()).expect("decode");
    assert_eq!(bob_cp0.received_at, None);
    prove_stats.push(ProveStats { name: "Bob coin-proof step 0", board_size: 1, prove_secs, verify_ms, entry_bytes: None });
    println!("  -> Bob coin-proof step 0 proved & verified ({prove_secs:.1} s)");

    // -- Bob coin-proof step 1 (recursive, he received his coin here) ---------
    println!("Proving Bob's coin-proof step 1...");
    let ap1 = append_proof_for(&entries[..2]);
    let mut stdin = build_coinproof_stdin(&coinproof_vkey, bob.pk, cn_bob, &entries[1], 1, &ap1, &registry, Some(&bob_cp0));
    {
        let SP1Proof::Compressed(inner) = bob_cp0_proof.proof.clone() else { panic!("compressed mode required") };
        stdin.write_proof(*inner, coinproof_pk.verifying_key().vk.clone());
    }
    let t = Instant::now();
    let bob_cp1_proof = client.prove(&coinproof_pk, stdin).compressed().run().expect("failed to prove bob cp1");
    let prove_secs = t.elapsed().as_secs_f64();
    let t = Instant::now();
    client.verify(&bob_cp1_proof, coinproof_pk.verifying_key(), None).expect("failed to verify bob cp1");
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let bob_cp1: CoinProofPublicValues = bincode::deserialize(bob_cp1_proof.public_values.as_slice()).expect("decode");
    assert_eq!(bob_cp1.received_at, Some(1));
    assert_eq!(bob_cp1.spent, false);
    prove_stats.push(ProveStats { name: "Bob coin-proof step 1 (recursive)", board_size: 2, prove_secs, verify_ms, entry_bytes: None });
    println!("  -> Bob coin-proof step 1 proved & verified ({prove_secs:.1} s, received_at={:?})", bob_cp1.received_at);

    // -- Bob's spend (slot 2, recursive, anchor = entries[..2]) ---------------
    println!("Proving Bob's spend...");
    let mut stdin = build_spend_stdin(&spend_vkey, &coinproof_vkey, &bob, cn_bob, &entries[..2], &chain[2].1, false, Some(&bob_cp1));
    {
        let SP1Proof::Compressed(inner) = bob_cp1_proof.proof.clone() else { panic!("compressed mode required") };
        stdin.write_proof(*inner, coinproof_pk.verifying_key().vk.clone());
    }
    let t = Instant::now();
    let bob_spend_proof = client.prove(&spend_pk, stdin).compressed().run().expect("failed to prove bob's spend");
    let prove_secs = t.elapsed().as_secs_f64();
    let t = Instant::now();
    client.verify(&bob_spend_proof, spend_pk.verifying_key(), None).expect("failed to verify bob's spend");
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let bob_spend_pv: ValidPublicValues = bincode::deserialize(bob_spend_proof.public_values.as_slice()).expect("decode");
    assert_eq!(bob_spend_pv.board_root, merkle_root_of(&entries[..2]));
    chain[2].1.spend_proof = bob_spend_proof.public_values.to_vec();
    entries[2] = encrypt_tx(&chain[2].1);
    let entry2_bytes = entries[2].ciphertext.len();
    prove_stats.push(ProveStats { name: "Bob's spend (recursive)", board_size: 3, prove_secs, verify_ms, entry_bytes: Some(entry2_bytes) });
    println!("  -> Bob's spend proved & verified ({prove_secs:.1} s)");

    println!("\nFull chain of {} transfers proved valid end-to-end.", chain.len());
    print_prove_table(&prove_stats);
}
