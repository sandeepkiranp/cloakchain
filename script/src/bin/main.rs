//! Host driver for the MNT-native cloakkchain relations (Phase 4 of the
//! MNT-native port).
//!
//! Demo chain: genesis mints to Alice, Alice's receipt is built
//! (recursively verifying the *wrapped* genesis proof), then Alice spends to
//! Bob (recursively verifying the *wrapped* receipt). This is the full
//! extent of what the current circuits support end to end:
//! `ReceiptStepCircuit` and the non-genesis `SpendStepCircuit` are each
//! fixed to recursively verify one specific wrapped VK (see
//! circuit-coinproof's and circuit-spend's module doc comments) rather than
//! accepting either spend variant, so a further Bob -> Carol hop — which
//! would need Bob's receipt to verify Alice's *spend* proof, not genesis's —
//! needs that generalization first. Also `MAX_INPUTS = MAX_OUTPUTS = 1`
//! throughout, so there is no "change" output: each transfer moves the full
//! coin value.
//!
//! ```shell
//! RUST_LOG=info cargo run --release -- --execute   # genesis circuit's constraint check only, no proving
//! RUST_LOG=info cargo run --release -- --prove     # full chain, five real Groth16 proofs
//! ```

use std::time::Instant;

use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
use ark_std::rand::{rngs::StdRng, SeedableRng};
use clap::Parser;
use cloakkchain_circuit_coinproof::ReceiptStepCircuit;
use cloakkchain_circuit_spend::{GenesisSpendCircuit, SpendStepCircuit};
use cloakkchain_circuit_wrap::WrapCircuit;
use cloakkchain_lib::{
    append_path_for_next, compute_root_from_path, derive_enc_pk, derive_owner_pk,
    entry_ciphertext_commitment, fold_owner_scalar, genesis_pk, genesis_sk, merkle_leaf,
    owner_pk_to_field_pair, poseidon_hash, scan_entry, BoardEntry, Coin, Fr, NullifierTree,
    OwnerPk, OwnerScalar, Transaction, EK_SALT,
};

const GENESIS_PUBLIC_INPUTS: usize = 6;
const RECEIPT_PUBLIC_INPUTS: usize = 5;

// ---- CLI args ---------------------------------------------------------------

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(long)]
    execute: bool,
    #[arg(long)]
    prove: bool,
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

// ---- Statistics --------------------------------------------------------------

struct ProveStats {
    name: String,
    prove_secs: f64,
    verify_ms: f64,
    proof_bytes: usize,
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

fn print_prove_table(stats: &[ProveStats]) {
    let w = 80;
    println!("\n{}", "=".repeat(w));
    println!("  Proof Statistics");
    println!("{}", "=".repeat(w));
    println!("{:<32} {:>10}  {:>10}  {:>11}", "Step", "Prove", "Verify", "Proof");
    println!("{}", "-".repeat(w));
    let (mut tp, mut tv) = (0f64, 0f64);
    for s in stats {
        println!(
            "{:<32} {:>7.1} s  {:>8.1} ms  {:>11}",
            s.name,
            s.prove_secs,
            s.verify_ms,
            fmt_bytes(s.proof_bytes)
        );
        tp += s.prove_secs;
        tv += s.verify_ms;
    }
    println!("{}", "-".repeat(w));
    println!("{:<32} {:>7.1} s  {:>8.1} ms", "TOTAL", tp, tv);
    println!("{}", "=".repeat(w));
}

// ---- main ---------------------------------------------------------------

fn main() {
    let args = Args::parse();
    let mode_count = [args.execute, args.prove].iter().filter(|&&b| b).count();
    if mode_count != 1 {
        eprintln!("Error: specify exactly one of --execute, --prove");
        std::process::exit(1);
    }

    let genesis = Party::genesis();
    let alice = Party::new("Alice", 1);
    let bob = Party::new("Bob", 2);

    let genesis_coin = coin(0xA1, 100, genesis.pk_p);
    let alice_coin = coin(0xA2, 100, alice.pk_p);

    if args.execute {
        run_execute(&genesis, &genesis_coin, &alice_coin);
        return;
    }

    run_prove(&genesis, &alice, &bob, genesis_coin, alice_coin);
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

    let coin_commitment = genesis_coin.commitment();
    let output_commitment = alice_coin.commitment();
    let append_path = append_path_for_next(&[]);
    let board_root = compute_root_from_path(Fr::from(0u64), 0, &append_path);
    let own_nullifier = poseidon_hash(&[coin_commitment, fold_owner_scalar(&genesis.sk_p)]);
    let tree = NullifierTree::new();

    let circuit = GenesisSpendCircuit {
        pk_p: Some(genesis.pk_p),
        coin_commitment: Some(coin_commitment),
        board_root: Some(board_root),
        output_commitment: Some(output_commitment),
        current_nullifier_root: Some(tree.root()),
        sk_p: Some(genesis.sk_p),
        input_coin: Some(genesis_coin.clone()),
        output_coin: Some(alice_coin.clone()),
        entry_position: Some(0),
        append_path: Some(append_path),
        own_nullifier_nonmembership: Some(tree.prove_non_membership(own_nullifier)),
    };

    let cs = ConstraintSystem::<Fr>::new_ref();
    circuit.generate_constraints(cs.clone()).expect("synthesize constraints");
    let satisfied = cs.is_satisfied().expect("check satisfiability");
    println!("  constraints: {}", cs.num_constraints());
    println!("  satisfied:   {satisfied}");
    assert!(satisfied);
    println!("\nRun --prove for the full chain (five real Groth16 proofs).");
}

fn run_prove(genesis: &Party, alice: &Party, bob: &Party, genesis_coin: Coin, alice_coin: Coin) {
    let mut rng = StdRng::seed_from_u64(0x636c6f616b); // "cloak" — deterministic demo, not a security-relevant seed
    let mut stats: Vec<ProveStats> = Vec::new();
    let mut entries: Vec<BoardEntry> = vec![];
    let mut nullifier_tree = NullifierTree::new();

    println!("--- Setting up Groth16 keys for all five circuit shapes ---");
    let t = Instant::now();
    let (genesis_pk_data, genesis_vk) = cloakkchain_circuit_spend::setup(&mut rng).unwrap();
    let (wrap_genesis_pk, wrap_genesis_vk) =
        cloakkchain_circuit_wrap::setup::<GENESIS_PUBLIC_INPUTS, _>(genesis_vk.clone(), &mut rng).unwrap();
    let (receipt_pk_data, receipt_vk) = cloakkchain_circuit_coinproof::setup(wrap_genesis_vk.clone(), &mut rng).unwrap();
    let (wrap_receipt_pk, wrap_receipt_vk) =
        cloakkchain_circuit_wrap::setup::<RECEIPT_PUBLIC_INPUTS, _>(receipt_vk.clone(), &mut rng).unwrap();
    let (spend_pk_data, spend_vk) =
        cloakkchain_circuit_spend::setup_non_genesis(wrap_receipt_vk.clone(), &mut rng).unwrap();
    println!("  done in {:.1}s (dev-mode/toy setup — see the MNT-native port memory)", t.elapsed().as_secs_f64());

    // =========================================================================
    // Slot 0: genesis mints 100 units to Alice
    // =========================================================================
    println!("\n--- Slot 0: genesis mint ---");
    let genesis_coin_commitment = genesis_coin.commitment();
    let alice_coin_commitment = alice_coin.commitment();
    let genesis_append_path = append_path_for_next(&entries);
    let genesis_board_root = compute_root_from_path(Fr::from(0u64), entries.len(), &genesis_append_path);
    let genesis_own_nullifier = poseidon_hash(&[genesis_coin_commitment, fold_owner_scalar(&genesis.sk_p)]);
    let genesis_nonmembership = nullifier_tree.prove_non_membership(genesis_own_nullifier);
    let genesis_nullifier_root = nullifier_tree.root();

    let genesis_circuit = GenesisSpendCircuit {
        pk_p: Some(genesis.pk_p),
        coin_commitment: Some(genesis_coin_commitment),
        board_root: Some(genesis_board_root),
        output_commitment: Some(alice_coin_commitment),
        current_nullifier_root: Some(genesis_nullifier_root),
        sk_p: Some(genesis.sk_p),
        input_coin: Some(genesis_coin.clone()),
        output_coin: Some(alice_coin.clone()),
        entry_position: Some(entries.len() as u64),
        append_path: Some(genesis_append_path.clone()),
        own_nullifier_nonmembership: Some(genesis_nonmembership),
    };
    let genesis_public_inputs: [Fr; GENESIS_PUBLIC_INPUTS] = GenesisSpendCircuit::public_inputs(
        genesis.pk_p,
        genesis_coin_commitment,
        genesis_board_root,
        alice_coin_commitment,
        genesis_nullifier_root,
    )
    .try_into()
    .unwrap();

    let t = Instant::now();
    let genesis_proof = cloakkchain_circuit_spend::prove(&genesis_pk_data, genesis_circuit, &mut rng).unwrap();
    let prove_secs = t.elapsed().as_secs_f64();
    let t = Instant::now();
    assert!(cloakkchain_circuit_spend::verify(&genesis_vk, &genesis_public_inputs, &genesis_proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let proof_bytes = ark_serialize_len(&genesis_proof);
    println!("  proved & verified ({prove_secs:.1}s) — proof {}", fmt_bytes(proof_bytes));
    stats.push(ProveStats { name: "Genesis mint".into(), prove_secs, verify_ms, proof_bytes });

    // Post the board entry. tx0.spend_proof carries the serialized proof so
    // a real chain could pass it along; the recursion here works entirely
    // off proof values already in hand, so this is informational.
    let (mut tx0, s0, r0) =
        make_tx(0, genesis.enc_sk, &genesis.sk_p, &[genesis_coin.clone()], &[(alice_coin.clone(), alice.enc_pk)]);
    tx0.spend_proof = ark_serialize_bytes(&genesis_proof);
    let genesis_entry = cloakkchain_lib::encrypt_tx(&tx0, &r0, s0);
    entries.push(genesis_entry.clone());
    nullifier_tree.insert(genesis_own_nullifier);

    // --- wrap the genesis proof so Alice's receipt circuit can verify it ---
    let t = Instant::now();
    let wrap1_proof = cloakkchain_circuit_wrap::prove::<GENESIS_PUBLIC_INPUTS, _>(
        &wrap_genesis_pk,
        WrapCircuit::<GENESIS_PUBLIC_INPUTS> {
            inner_vk: genesis_vk,
            inner_proof: Some(genesis_proof),
            inner_public_inputs: Some(genesis_public_inputs),
        },
        &mut rng,
    )
    .unwrap();
    let prove_secs = t.elapsed().as_secs_f64();
    let wrap1_public_inputs = cloakkchain_circuit_wrap::public_input_chunks(&genesis_public_inputs);
    let t = Instant::now();
    assert!(cloakkchain_circuit_wrap::verify(&wrap_genesis_vk, &wrap1_public_inputs, &wrap1_proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let proof_bytes = ark_serialize_len(&wrap1_proof);
    println!("  wrapped genesis proof ({prove_secs:.1}s) — proof {}", fmt_bytes(proof_bytes));
    stats.push(ProveStats { name: "Wrap genesis proof".into(), prove_secs, verify_ms, proof_bytes });

    // =========================================================================
    // Alice discovers her coin and builds her receipt
    // =========================================================================
    println!("\n--- Alice scans slot 0, builds her receipt ---");
    let alice_tx = scan_entry(&alice.enc_sk, &genesis_entry).expect("Alice must be able to decrypt slot 0");
    assert!(alice_tx.receives_coin(&alice_coin_commitment), "Alice's tx must transfer her coin");
    println!("  [{}] discovered coin (value={}) at slot 0", alice.name, alice_coin.value);

    let receipt_append_path = genesis_append_path.clone();
    let receipt_board_root =
        compute_root_from_path(merkle_leaf(0, &genesis_entry), 0, &receipt_append_path);
    let (apx, apy) = owner_pk_to_field_pair(&alice.pk_p);

    let receipt_circuit = ReceiptStepCircuit {
        owner_pk_x: Some(apx),
        owner_pk_y: Some(apy),
        coin_commitment: Some(alice_coin_commitment),
        board_root: Some(receipt_board_root),
        received_at: Some(0),
        wrap_vk: wrap_genesis_vk,
        wrap_proof: Some(wrap1_proof),
        wrap_public_inputs: Some(genesis_public_inputs),
        entry_nullifier: Some(genesis_entry.nullifier),
        entry_output_commitment: Some(alice_coin_commitment),
        entry_ciphertext_commitment: Some(entry_ciphertext_commitment(&genesis_entry)),
        received_slot: Some(0),
        append_path: Some(receipt_append_path),
        parent_nonmembership: Some(NullifierTree::new().prove_non_membership(genesis_entry.nullifier)),
        nullifier_root_at_parent_slot: Some(NullifierTree::new().root()),
    };
    let receipt_public_inputs: [Fr; RECEIPT_PUBLIC_INPUTS] =
        ReceiptStepCircuit::public_inputs(apx, apy, alice_coin_commitment, receipt_board_root, 0)
            .try_into()
            .unwrap();

    let t = Instant::now();
    let receipt_proof = cloakkchain_circuit_coinproof::prove(&receipt_pk_data, receipt_circuit, &mut rng).unwrap();
    let prove_secs = t.elapsed().as_secs_f64();
    let t = Instant::now();
    assert!(cloakkchain_circuit_coinproof::verify(&receipt_vk, &receipt_public_inputs, &receipt_proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let proof_bytes = ark_serialize_len(&receipt_proof);
    println!("  proved & verified Alice's receipt ({prove_secs:.1}s) — proof {}", fmt_bytes(proof_bytes));
    stats.push(ProveStats { name: "Alice's receipt".into(), prove_secs, verify_ms, proof_bytes });

    // --- wrap Alice's receipt so her spend circuit can verify it ---
    let t = Instant::now();
    let wrap2_proof = cloakkchain_circuit_wrap::prove::<RECEIPT_PUBLIC_INPUTS, _>(
        &wrap_receipt_pk,
        WrapCircuit::<RECEIPT_PUBLIC_INPUTS> {
            inner_vk: receipt_vk,
            inner_proof: Some(receipt_proof),
            inner_public_inputs: Some(receipt_public_inputs),
        },
        &mut rng,
    )
    .unwrap();
    let prove_secs = t.elapsed().as_secs_f64();
    let wrap2_public_inputs = cloakkchain_circuit_wrap::public_input_chunks(&receipt_public_inputs);
    let t = Instant::now();
    assert!(cloakkchain_circuit_wrap::verify(&wrap_receipt_vk, &wrap2_public_inputs, &wrap2_proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let proof_bytes = ark_serialize_len(&wrap2_proof);
    println!("  wrapped Alice's receipt ({prove_secs:.1}s) — proof {}", fmt_bytes(proof_bytes));
    stats.push(ProveStats { name: "Wrap Alice's receipt".into(), prove_secs, verify_ms, proof_bytes });

    // =========================================================================
    // Slot 1: Alice spends her full 100 units to Bob
    // =========================================================================
    println!("\n--- Slot 1: Alice spends to Bob ---");
    let bob_coin = coin(0xB1, 100, bob.pk_p);
    let bob_coin_commitment = bob_coin.commitment();

    let spend_append_path = append_path_for_next(&entries);
    let spend_board_root = compute_root_from_path(Fr::from(0u64), entries.len(), &spend_append_path);
    let alice_own_nullifier = poseidon_hash(&[alice_coin_commitment, fold_owner_scalar(&alice.sk_p)]);

    let spend_circuit = SpendStepCircuit {
        pk_p: Some(alice.pk_p),
        coin_commitment: Some(alice_coin_commitment),
        board_root: Some(spend_board_root),
        output_commitment: Some(bob_coin_commitment),
        current_nullifier_root: Some(nullifier_tree.root()),
        sk_p: Some(alice.sk_p),
        input_coin: Some(alice_coin.clone()),
        output_coin: Some(bob_coin.clone()),
        entry_position: Some(entries.len() as u64),
        append_path: Some(spend_append_path),
        own_nullifier_nonmembership: Some(nullifier_tree.prove_non_membership(alice_own_nullifier)),
        wrap_vk: wrap_receipt_vk,
        wrap_proof: Some(wrap2_proof),
        wrap_public_inputs: Some(receipt_public_inputs),
    };
    let spend_public_inputs = SpendStepCircuit::public_inputs(
        alice.pk_p,
        alice_coin_commitment,
        spend_board_root,
        bob_coin_commitment,
        nullifier_tree.root(),
    );

    let t = Instant::now();
    let spend_proof = cloakkchain_circuit_spend::prove_non_genesis(&spend_pk_data, spend_circuit, &mut rng).unwrap();
    let prove_secs = t.elapsed().as_secs_f64();
    let t = Instant::now();
    assert!(cloakkchain_circuit_spend::verify_non_genesis(&spend_vk, &spend_public_inputs, &spend_proof).unwrap());
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let proof_bytes = ark_serialize_len(&spend_proof);
    println!("  proved & verified Alice -> Bob spend ({prove_secs:.1}s) — proof {}", fmt_bytes(proof_bytes));
    stats.push(ProveStats { name: "Alice -> Bob spend".into(), prove_secs, verify_ms, proof_bytes });

    let (mut tx1, s1, r1) =
        make_tx(1, alice.enc_sk, &alice.sk_p, &[alice_coin.clone()], &[(bob_coin.clone(), bob.enc_pk)]);
    tx1.spend_proof = ark_serialize_bytes(&spend_proof);
    let alice_entry = cloakkchain_lib::encrypt_tx(&tx1, &r1, s1);
    entries.push(alice_entry.clone());
    nullifier_tree.insert(alice_own_nullifier);

    // Bob can discover his coin (off-circuit wallet scanning — no proof
    // needed for this); building *his* receipt would need to recursively
    // verify Alice's spend proof, which isn't supported yet (see the module
    // doc comment).
    println!("\n--- Bob scans slot 1 ---");
    let bob_tx = scan_entry(&bob.enc_sk, &alice_entry).expect("Bob must be able to decrypt slot 1");
    assert!(bob_tx.receives_coin(&bob_coin_commitment));
    println!("  [{}] discovered coin (value={}) at slot 1 — no receipt built (see module doc comment)", bob.name, bob_coin.value);

    print_prove_table(&stats);
}

fn ark_serialize_bytes<T: ark_serialize::CanonicalSerialize>(v: &T) -> Vec<u8> {
    let mut out = Vec::new();
    v.serialize_compressed(&mut out).expect("serialize proof");
    out
}

fn ark_serialize_len<T: ark_serialize::CanonicalSerialize>(v: &T) -> usize {
    v.compressed_size()
}
