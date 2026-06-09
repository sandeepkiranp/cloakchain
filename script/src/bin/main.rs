//! Host driver for the `cloakkchain` recursive `Valid` relation (paper §3, page 6).
//!
//! Builds a small bulletin-board history — genesis mints a coin to Alice, Alice sends it
//! to Bob, Bob sends it to Carol — and runs the `Valid` relation over each transfer.
//!
//! ## Merkle completeness fix
//!
//! The prover computes the Merkle root of the full board and commits it as a public
//! output.  Carol (or any verifier) independently recomputes the root from the real
//! board and checks it matches.  Each transaction in the proof is also accompanied by
//! its Merkle inclusion proof (verified in-circuit inside the zkVM), so the prover
//! cannot omit a slot without the roots diverging and cannot substitute a fake
//! transaction without the inclusion proof failing.
//!
//! ```shell
//! RUST_LOG=info cargo run --release -- --execute   # genesis step only, no proof
//! RUST_LOG=info cargo run --release -- --prove     # full recursive chain (expensive)
//! ```

use clap::Parser;
use cloakkchain_lib::{
    derive_pk, genesis_pk, merkle_proof_for, merkle_root_of, Coin, Transaction,
    ValidPublicValues, GENESIS_SK,
};
use sha2::{Digest, Sha256};
use sp1_sdk::{
    blocking::{MockProver, ProveRequest, Prover, ProverClient},
    include_elf, Elf, HashableKey, ProvingKey, SP1Proof, SP1ProofWithPublicValues, SP1Stdin,
};

const CLOAKKCHAIN_ELF: Elf = include_elf!("cloakkchain-program");

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

struct Step<'a> {
    sender: &'a Party,
    tx: Transaction,
    received_via: Option<usize>,
}

/// Build the SP1Stdin for `step`.
///
/// Computes the Merkle root of `history` and generates an inclusion proof for
/// every slot.  The root is passed as a public input; the inclusion proofs are
/// private witnesses verified in-circuit.
fn build_stdin(vkey: &[u32; 8], step: &Step, history: &[Transaction]) -> SP1Stdin {
    let board_root = merkle_root_of(history);
    let merkle_proofs: Vec<Vec<[u8; 32]>> =
        (0..history.len()).map(|i| merkle_proof_for(history, i)).collect();

    let mut stdin = SP1Stdin::new();
    stdin.write(vkey);
    stdin.write(&step.sender.sk);
    stdin.write(&step.sender.pk);
    stdin.write(&board_root);
    stdin.write(&history.to_vec());
    stdin.write(&merkle_proofs);
    stdin.write(&step.received_via.is_none());
    if let Some(t) = step.received_via {
        stdin.write(&(t as u32));
    }
    stdin
}

fn demo_chain<'a>(
    alice: &'a Party,
    bob: &'a Party,
    carol: &'a Party,
    genesis: &'a Party,
) -> Vec<Step<'a>> {
    let coin_a = coin(0xA1);
    vec![
        Step {
            sender: genesis,
            tx: Transaction {
                id: 0,
                sender_pk: genesis.pk,
                recipient_pk: alice.pk,
                coin: coin_a.clone(),
            },
            received_via: None,
        },
        Step {
            sender: alice,
            tx: Transaction {
                id: 1,
                sender_pk: alice.pk,
                recipient_pk: bob.pk,
                coin: coin_a.clone(),
            },
            received_via: Some(0),
        },
        Step {
            sender: bob,
            tx: Transaction {
                id: 2,
                sender_pk: bob.pk,
                recipient_pk: carol.pk,
                coin: coin_a.clone(),
            },
            received_via: Some(1),
        },
    ]
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

    if args.execute {
        let client = MockProver::new();
        let pk = client.setup(CLOAKKCHAIN_ELF).expect("failed to setup elf");
        let vkey = pk.verifying_key().hash_u32();
        println!("cloakkchain vkey: {}", pk.verifying_key().bytes32());

        let steps = demo_chain(&alice, &bob, &carol, &genesis);
        let genesis_step = &steps[0];
        let history = vec![genesis_step.tx.clone()];
        let stdin = build_stdin(&vkey, genesis_step, &history);

        println!(
            "Executing the genesis step: minting coin {:02x?} to {} ...",
            &genesis_step.tx.coin.tag[..1],
            genesis_step.sender.name
        );

        let (output, report) = client.execute(CLOAKKCHAIN_ELF, stdin).run().unwrap();
        println!("Program executed successfully.");

        let public_values: ValidPublicValues =
            bincode::deserialize(output.as_slice()).expect("failed to decode public values");

        // External Merkle check: Carol independently computes the board root
        // and verifies it matches what the proof committed to.
        let carol_root = merkle_root_of(&history);
        assert_eq!(
            public_values.board_root, carol_root,
            "committed board root does not match the real board"
        );
        assert_eq!(public_values.pk_p, genesis_pk());
        assert_eq!(public_values.board_size, history.len());

        println!("pk_P:        0x{}", hex::encode(public_values.pk_p));
        println!(
            "board_root:  0x{}",
            hex::encode(public_values.board_root)
        );
        println!("board_size:  {}", public_values.board_size);
        println!("External Merkle root check passed.");
        println!("Number of cycles: {}", report.total_instruction_count());
        return;
    }

    // --prove: full recursive chain.
    let client = ProverClient::from_env();
    let pk = client.setup(CLOAKKCHAIN_ELF).expect("failed to setup elf");
    let vkey = pk.verifying_key().hash_u32();
    println!("cloakkchain vkey: {}", pk.verifying_key().bytes32());

    let steps = demo_chain(&alice, &bob, &carol, &genesis);
    let mut history: Vec<Transaction> = Vec::new();
    let mut proofs: Vec<SP1ProofWithPublicValues> = Vec::new();

    for (i, step) in steps.iter().enumerate() {
        history.push(step.tx.clone());

        let mut stdin = build_stdin(&vkey, step, &history);
        if let Some(t) = step.received_via {
            let inner_proof = &proofs[t];
            let SP1Proof::Compressed(inner) = inner_proof.proof.clone() else {
                panic!("recursive proofs must be in compressed mode");
            };
            stdin.write_proof(*inner, pk.verifying_key().vk.clone());
        }

        println!(
            "Proving step {i}: {} sends tx#{} to 0x{}...",
            step.sender.name,
            step.tx.id,
            hex::encode(&step.tx.recipient_pk[..4]),
        );

        let proof =
            client.prove(&pk, stdin).compressed().run().expect("failed to generate proof");
        client.verify(&proof, pk.verifying_key(), None).expect("failed to verify proof");

        let public_values: ValidPublicValues =
            bincode::deserialize(proof.public_values.as_slice())
                .expect("failed to decode public values");

        // External Merkle check per step.
        let carol_root = merkle_root_of(&history);
        assert_eq!(
            public_values.board_root, carol_root,
            "step {i}: committed board root does not match the real board"
        );
        assert_eq!(public_values.pk_p, step.sender.pk);
        assert_eq!(public_values.board_size, history.len());
        assert_eq!(
            Sha256::digest(public_values.encode()).as_slice(),
            Sha256::digest(proof.public_values.as_slice()).as_slice()
        );

        println!(
            "  -> proved & verified: {} validly sent the coin (board_size {})",
            step.sender.name,
            public_values.board_size,
        );

        proofs.push(proof);
    }

    // Final check: vkey self-consistency + Merkle root matches the complete real board.
    let final_proof = proofs.last().unwrap();
    let final_pv: ValidPublicValues =
        bincode::deserialize(final_proof.public_values.as_slice()).unwrap();
    assert_eq!(final_pv.vkey, vkey, "chain was not built with the genuine relation");
    assert_eq!(
        final_pv.board_root,
        merkle_root_of(&history),
        "final committed board root does not match the real board"
    );

    println!(
        "\nChain of {} transfers proved valid end-to-end under vkey {}.",
        proofs.len(),
        pk.verifying_key().bytes32()
    );
}
