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
//! sender/recipient pair, who share a hard-coded pairwise key (see
//! `cloakkchain_lib::pair_key`). Both relations decrypt in-circuit via
//! `extract_msg`/`scan_entry`.
//!
//! ```shell
//! RUST_LOG=info cargo run --release -- --execute   # non-recursive steps only
//! RUST_LOG=info cargo run --release -- --prove     # full recursive chain (expensive)
//! ```

use clap::Parser;
use cloakkchain_lib::{
    derive_pk, encrypt_tx, genesis_pk, merkle_proof_for, merkle_root_of, BoardEntry, Coin,
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

fn coin(seed: u8) -> Coin {
    let mut tag = [0u8; 32];
    tag[0] = seed;
    let mut rand = [0u8; 32];
    rand[1] = seed;
    Coin { tag, rand }
}

/// The 3-tx demo chain: genesis mints `coin_a` to Alice, Alice sends it to Bob,
/// Bob sends it to Carol. Each entry is `(sender, transaction)`.
fn demo_chain<'a>(
    alice: &'a Party,
    bob: &'a Party,
    carol: &'a Party,
    genesis: &'a Party,
) -> Vec<(&'a Party, Transaction)> {
    let coin_a = coin(0xA1);
    vec![
        (genesis, Transaction { id: 0, sender_pk: genesis.pk, recipient_pk: alice.pk, coin: coin_a.clone() }),
        (alice, Transaction { id: 1, sender_pk: alice.pk, recipient_pk: bob.pk, coin: coin_a.clone() }),
        (bob, Transaction { id: 2, sender_pk: bob.pk, recipient_pk: carol.pk, coin: coin_a.clone() }),
    ]
}

/// Build the SP1Stdin for one step of the coin-proof relation, covering
/// `entries` (= `entries[0..=k]`). `inner` is the previous step's public
/// values, or `None` for the base case (`k == 0`).
fn build_coinproof_stdin(
    coinproof_vkey: &[u32; 8],
    owner_pk: [u8; 32],
    coin_commitment: [u8; 32],
    entries: &[BoardEntry],
    registry: &[[u8; 32]],
    inner: Option<&CoinProofPublicValues>,
) -> SP1Stdin {
    let mut stdin = SP1Stdin::new();
    stdin.write(coinproof_vkey);
    stdin.write(&owner_pk);
    stdin.write(&coin_commitment);
    stdin.write(&entries.to_vec());
    stdin.write(&registry.to_vec());
    stdin.write(&inner.is_some());
    if let Some(pv) = inner {
        stdin.write(pv);
    }
    stdin
}

/// Build the SP1Stdin for the spend relation, spending the coin at
/// `entries.last()` (= `tx*`). For non-genesis spends, `coin_proof` must be
/// the latest coin-proof covering `entries[..last]`.
fn build_spend_stdin(
    spend_vkey: &[u32; 8],
    coinproof_vkey: &[u32; 8],
    sender: &Party,
    coin_commitment: [u8; 32],
    entries: &[BoardEntry],
    recipient_pk: [u8; 32],
    is_genesis: bool,
    coin_proof: Option<&CoinProofPublicValues>,
) -> SP1Stdin {
    let last = entries.len() - 1;
    let board_root = merkle_root_of(entries);
    let merkle_proof = merkle_proof_for(entries, last);

    let mut stdin = SP1Stdin::new();
    stdin.write(spend_vkey);
    stdin.write(coinproof_vkey);
    stdin.write(&sender.sk);
    stdin.write(&sender.pk);
    stdin.write(&coin_commitment);
    stdin.write(&board_root);
    stdin.write(&entries.to_vec());
    stdin.write(&merkle_proof);
    stdin.write(&recipient_pk);
    stdin.write(&is_genesis);
    if let Some(cp) = coin_proof {
        stdin.write(cp);
    }
    stdin
}

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

    let chain = demo_chain(&alice, &bob, &carol, &genesis);
    let entries: Vec<BoardEntry> = chain.iter().map(|(_, tx)| encrypt_tx(tx)).collect();
    let cn = chain[0].1.coin.commitment();

    if args.execute {
        let client = MockProver::new();
        let spend_pk = client.setup(CLOAKKCHAIN_SPEND_ELF).expect("failed to setup spend elf");
        let coinproof_pk =
            client.setup(CLOAKKCHAIN_COINPROOF_ELF).expect("failed to setup coinproof elf");
        let spend_vkey = spend_pk.verifying_key().hash_u32();
        let coinproof_vkey = coinproof_pk.verifying_key().hash_u32();
        println!("spend vkey:     {}", spend_pk.verifying_key().bytes32());
        println!("coinproof vkey: {}", coinproof_pk.verifying_key().bytes32());

        // Genesis mints coin_a to Alice (slot 0) — no coin-proof needed.
        let stdin = build_spend_stdin(&spend_vkey, &coinproof_vkey, &genesis, cn, &entries[..1], alice.pk, true, None);
        let (output, report) = client.execute(CLOAKKCHAIN_SPEND_ELF, stdin).run().unwrap();
        let pv: ValidPublicValues = bincode::deserialize(output.as_slice()).expect("decode");
        assert_eq!(pv.board_root, merkle_root_of(&entries[..1]), "genesis: board root mismatch");
        assert_eq!(pv.pk_p, genesis.pk);
        assert_eq!(pv.board_size, 1);
        println!(
            "Genesis mint OK: board_size={}, cycles={}",
            pv.board_size,
            report.total_instruction_count()
        );

        // Alice's coin-proof step 0 (base case, k == 0): she received coin_a here.
        let stdin = build_coinproof_stdin(&coinproof_vkey, alice.pk, cn, &entries[..1], &registry, None);
        let (output, report) = client.execute(CLOAKKCHAIN_COINPROOF_ELF, stdin).run().unwrap();
        let alice_cp0: CoinProofPublicValues = bincode::deserialize(output.as_slice()).expect("decode");
        assert_eq!(alice_cp0.board_root, merkle_root_of(&entries[..1]), "alice cp0: board root mismatch");
        assert_eq!(alice_cp0.received_at, Some(0));
        assert_eq!(alice_cp0.spent, false);
        println!(
            "Alice coin-proof step 0 OK: received_at={:?}, spent={}, cycles={}",
            alice_cp0.received_at,
            alice_cp0.spent,
            report.total_instruction_count()
        );

        // Bob's coin-proof step 0 (base case, k == 0): slot 0 isn't his.
        let stdin = build_coinproof_stdin(&coinproof_vkey, bob.pk, cn, &entries[..1], &registry, None);
        let (output, report) = client.execute(CLOAKKCHAIN_COINPROOF_ELF, stdin).run().unwrap();
        let bob_cp0: CoinProofPublicValues = bincode::deserialize(output.as_slice()).expect("decode");
        assert_eq!(bob_cp0.board_root, merkle_root_of(&entries[..1]), "bob cp0: board root mismatch");
        assert_eq!(bob_cp0.received_at, None);
        assert_eq!(bob_cp0.spent, false);
        println!(
            "Bob coin-proof step 0 OK: received_at={:?}, spent={}, cycles={}",
            bob_cp0.received_at,
            bob_cp0.spent,
            report.total_instruction_count()
        );

        println!("\n--execute ran the non-recursive steps only (genesis mint + base-case coin-proofs).");
        println!("Run --prove for the full recursive chain (Alice's spend, Bob's coin-proof step 1, Bob's spend).");
        return;
    }

    // --prove: full recursive chain.
    let client = ProverClient::from_env();
    let spend_pk = client.setup(CLOAKKCHAIN_SPEND_ELF).expect("failed to setup spend elf");
    let coinproof_pk =
        client.setup(CLOAKKCHAIN_COINPROOF_ELF).expect("failed to setup coinproof elf");
    let spend_vkey = spend_pk.verifying_key().hash_u32();
    let coinproof_vkey = coinproof_pk.verifying_key().hash_u32();
    println!("spend vkey:     {}", spend_pk.verifying_key().bytes32());
    println!("coinproof vkey: {}", coinproof_pk.verifying_key().bytes32());

    // Genesis mints coin_a to Alice (slot 0).
    let stdin = build_spend_stdin(&spend_vkey, &coinproof_vkey, &genesis, cn, &entries[..1], alice.pk, true, None);
    println!("Proving genesis mint...");
    let genesis_proof = client.prove(&spend_pk, stdin).compressed().run().expect("failed to prove genesis mint");
    client.verify(&genesis_proof, spend_pk.verifying_key(), None).expect("failed to verify genesis mint");
    let genesis_pv: ValidPublicValues =
        bincode::deserialize(genesis_proof.public_values.as_slice()).expect("decode");
    assert_eq!(genesis_pv.board_root, merkle_root_of(&entries[..1]));
    println!("  -> {} mint proved & verified", genesis.name);

    // Alice's coin-proof step 0 (base case).
    let stdin = build_coinproof_stdin(&coinproof_vkey, alice.pk, cn, &entries[..1], &registry, None);
    println!("Proving Alice's coin-proof step 0...");
    let alice_cp0_proof = client.prove(&coinproof_pk, stdin).compressed().run().expect("failed to prove alice cp0");
    client.verify(&alice_cp0_proof, coinproof_pk.verifying_key(), None).expect("failed to verify alice cp0");
    let alice_cp0: CoinProofPublicValues =
        bincode::deserialize(alice_cp0_proof.public_values.as_slice()).expect("decode");
    assert_eq!(alice_cp0.received_at, Some(0));
    assert_eq!(alice_cp0.spent, false);
    println!("  -> Alice's coin-proof step 0 proved & verified (received_at={:?})", alice_cp0.received_at);

    // Alice spends coin_a to Bob (slot 1), recursively verifying her coin-proof.
    let mut stdin = build_spend_stdin(&spend_vkey, &coinproof_vkey, &alice, cn, &entries[..2], bob.pk, false, Some(&alice_cp0));
    {
        let SP1Proof::Compressed(inner) = alice_cp0_proof.proof.clone() else {
            panic!("recursive proofs must be in compressed mode");
        };
        stdin.write_proof(*inner, coinproof_pk.verifying_key().vk.clone());
    }
    println!("Proving Alice's spend...");
    let alice_spend_proof = client.prove(&spend_pk, stdin).compressed().run().expect("failed to prove alice's spend");
    client.verify(&alice_spend_proof, spend_pk.verifying_key(), None).expect("failed to verify alice's spend");
    let alice_spend_pv: ValidPublicValues =
        bincode::deserialize(alice_spend_proof.public_values.as_slice()).expect("decode");
    assert_eq!(alice_spend_pv.board_root, merkle_root_of(&entries[..2]));
    println!("  -> Alice's spend proved & verified");

    // Bob's coin-proof step 0 (base case): slot 0 isn't his.
    let stdin = build_coinproof_stdin(&coinproof_vkey, bob.pk, cn, &entries[..1], &registry, None);
    println!("Proving Bob's coin-proof step 0...");
    let bob_cp0_proof = client.prove(&coinproof_pk, stdin).compressed().run().expect("failed to prove bob cp0");
    client.verify(&bob_cp0_proof, coinproof_pk.verifying_key(), None).expect("failed to verify bob cp0");
    let bob_cp0: CoinProofPublicValues =
        bincode::deserialize(bob_cp0_proof.public_values.as_slice()).expect("decode");
    assert_eq!(bob_cp0.received_at, None);
    println!("  -> Bob's coin-proof step 0 proved & verified");

    // Bob's coin-proof step 1, recursively verifying step 0: he received coin_a here.
    let mut stdin = build_coinproof_stdin(&coinproof_vkey, bob.pk, cn, &entries[..2], &registry, Some(&bob_cp0));
    {
        let SP1Proof::Compressed(inner) = bob_cp0_proof.proof.clone() else {
            panic!("recursive proofs must be in compressed mode");
        };
        stdin.write_proof(*inner, coinproof_pk.verifying_key().vk.clone());
    }
    println!("Proving Bob's coin-proof step 1...");
    let bob_cp1_proof = client.prove(&coinproof_pk, stdin).compressed().run().expect("failed to prove bob cp1");
    client.verify(&bob_cp1_proof, coinproof_pk.verifying_key(), None).expect("failed to verify bob cp1");
    let bob_cp1: CoinProofPublicValues =
        bincode::deserialize(bob_cp1_proof.public_values.as_slice()).expect("decode");
    assert_eq!(bob_cp1.received_at, Some(1));
    assert_eq!(bob_cp1.spent, false);
    println!("  -> Bob's coin-proof step 1 proved & verified (received_at={:?})", bob_cp1.received_at);

    // Bob spends coin_a to Carol (slot 2), recursively verifying his coin-proof.
    let mut stdin = build_spend_stdin(&spend_vkey, &coinproof_vkey, &bob, cn, &entries[..3], carol.pk, false, Some(&bob_cp1));
    {
        let SP1Proof::Compressed(inner) = bob_cp1_proof.proof.clone() else {
            panic!("recursive proofs must be in compressed mode");
        };
        stdin.write_proof(*inner, coinproof_pk.verifying_key().vk.clone());
    }
    println!("Proving Bob's spend...");
    let bob_spend_proof = client.prove(&spend_pk, stdin).compressed().run().expect("failed to prove bob's spend");
    client.verify(&bob_spend_proof, spend_pk.verifying_key(), None).expect("failed to verify bob's spend");
    let bob_spend_pv: ValidPublicValues =
        bincode::deserialize(bob_spend_proof.public_values.as_slice()).expect("decode");
    assert_eq!(bob_spend_pv.board_root, merkle_root_of(&entries[..3]));
    println!("  -> Bob's spend proved & verified");

    println!("\nFull chain of {} transfers proved valid end-to-end.", chain.len());
}
