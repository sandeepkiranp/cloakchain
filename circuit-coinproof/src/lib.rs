//! MNT-native coin-receipt circuit. `ReceiptStepCircuit` is the receipt-side
//! business logic (see `cloakkchain_lib::check_coin_receipt`) — Fr4-native,
//! the same field as `circuit-spend`'s circuits. Per the MNT-native port
//! plan's "wrap layer" architecture note: business logic (Merkle /
//! nullifier-tree work) stays entirely native here; curve-cycle recursion
//! happens via `circuit-wrap`'s `WrapCircuit`, never by putting hashing on
//! the "wrong" field.
//!
//! Currently fixed to recursively verify a *wrapped* `GenesisSpendCircuit`
//! proof specifically (its 6-public-input layout, in
//! `circuit_spend::GenesisSpendCircuit::public_inputs`'s order) — i.e. this
//! is the receipt circuit for a coin received directly from a genesis mint.
//! Accepting a wrapped non-genesis spend proof too (a different VK) needs
//! the "VK selection" gadget the port plan flagged as a later
//! generalization, once multi-hop chains with non-genesis parents are
//! needed.

use ark_crypto_primitives::snark::{constraints::SNARKGadget, BooleanInputVar};
use ark_crypto_primitives::sponge::{constraints::CryptographicSpongeVar, poseidon::constraints::PoseidonSpongeVar};
use ark_ff::{BigInteger, PrimeField};
use ark_groth16::{
    constraints::{Groth16VerifierGadget, ProofVar, VerifyingKeyVar},
    Groth16, Proof, ProvingKey, VerifyingKey,
};
use ark_mnt4_753::MNT4_753;
use ark_mnt6_753::MNT6_753;
use ark_r1cs_std::{cmp::CmpGadget, fields::fp::FpVar, prelude::*};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_snark::SNARK;
use ark_std::rand::{CryptoRng, RngCore};
use cloakkchain_circuit_wrap::{chunks_per_value, combine_chunks_var, public_input_chunks, Fr6};
use cloakkchain_lib::{Fr, NonMembershipWitness, TREE_DEPTH};

type Fp = FpVar<Fr>;
type MNT6PairingVar = ark_mnt6_753::constraints::PairingVar;

/// `GenesisSpendCircuit`'s public-input count/order (mirrors
/// `circuit_spend::GenesisSpendCircuit::public_inputs`, duplicated as a
/// plain constant rather than a crate dependency, to avoid a
/// circuit-coinproof <-> circuit-spend cycle — both sides must keep this in
/// sync by construction, not by the type system).
const SPEND_PUBLIC_INPUT_COUNT: usize = 6;
const SPEND_OUTPUT_COMMITMENT: usize = 4;

// Gadget helpers duplicated from circuit-spend (small, self-contained;
// keeping each circuit crate independently buildable rather than factoring
// ~20-line functions into a third shared crate).
fn poseidon_hash_var(cs: ConstraintSystemRef<Fr>, inputs: &[Fp]) -> Result<Fp, SynthesisError> {
    let mut sponge = PoseidonSpongeVar::new(cs, &cloakkchain_lib::poseidon_params::mnt4_753_fr_poseidon_config());
    sponge.absorb(&inputs.to_vec())?;
    Ok(sponge.squeeze_field_elements(1)?.remove(0))
}

fn merkle_combine_var(cs: ConstraintSystemRef<Fr>, l: &Fp, r: &Fp) -> Result<Fp, SynthesisError> {
    poseidon_hash_var(cs, &[l.clone(), r.clone()])
}

fn compute_root_from_path_var(
    cs: ConstraintSystemRef<Fr>,
    leaf: &Fp,
    slot_bits_le: &[Boolean<Fr>],
    path: &[Fp],
) -> Result<Fp, SynthesisError> {
    let mut current = leaf.clone();
    for (bit, sibling) in slot_bits_le.iter().zip(path.iter()) {
        let left = Fp::conditionally_select(bit, sibling, &current)?;
        let right = Fp::conditionally_select(bit, &current, sibling)?;
        current = merkle_combine_var(cs.clone(), &left, &right)?;
    }
    Ok(current)
}

fn fp_is_lt(a: &Fp, b: &Fp) -> Result<Boolean<Fr>, SynthesisError> {
    let mut a_bits = a.to_bits_le()?;
    let mut b_bits = b.to_bits_le()?;
    a_bits.reverse();
    b_bits.reverse();
    a_bits.as_slice().is_lt(b_bits.as_slice())
}

struct IndexedLeafVar {
    value: Fp,
    next_value: Fp,
    next_index: Fp,
}

impl IndexedLeafVar {
    fn hash(&self, cs: ConstraintSystemRef<Fr>) -> Result<Fp, SynthesisError> {
        poseidon_hash_var(cs, &[self.value.clone(), self.next_value.clone(), self.next_index.clone()])
    }
}

#[allow(clippy::too_many_arguments)]
fn verify_nonmembership_var(
    cs: ConstraintSystemRef<Fr>,
    root: &Fp,
    target: &Fp,
    low_leaf: &IndexedLeafVar,
    low_leaf_index_bits: &[Boolean<Fr>],
    sibling_path: &[Fp],
) -> Result<Boolean<Fr>, SynthesisError> {
    let lower_ok = fp_is_lt(&low_leaf.value, target)?;
    let upper_ok = fp_is_lt(target, &low_leaf.next_value)?;
    let ordering_ok = &lower_ok & &upper_ok;
    let leaf_hash = low_leaf.hash(cs.clone())?;
    let computed_root = compute_root_from_path_var(cs, &leaf_hash, low_leaf_index_bits, sibling_path)?;
    let root_ok = computed_root.is_eq(root)?;
    Ok(&ordering_ok & &root_ok)
}

fn opt<T: Clone>(o: &Option<T>) -> Result<T, SynthesisError> {
    o.clone().ok_or(SynthesisError::AssignmentMissing)
}

fn alloc_fp_vec(cs: ConstraintSystemRef<Fr>, values: &Option<Vec<Fr>>, len: usize) -> Result<Vec<Fp>, SynthesisError> {
    (0..len).map(|i| Fp::new_witness(cs.clone(), || opt(&values.as_ref().map(|v| v[i])))).collect()
}

/// Public values, in this order: `owner_pk.x, owner_pk.y, coin_commitment,
/// board_root, received_at`.
#[derive(Clone)]
pub struct ReceiptStepCircuit {
    // Public values.
    pub owner_pk_x: Option<Fr>,
    pub owner_pk_y: Option<Fr>,
    pub coin_commitment: Option<Fr>,
    pub board_root: Option<Fr>,
    pub received_at: Option<u64>,

    // Private witnesses: the wrapped parent-spend proof (a Wrap<6> proof
    // over `GenesisSpendCircuit`'s public inputs).
    /// Fixed per deployment — not `Option`, a verifying key isn't secret.
    pub wrap_vk: VerifyingKey<MNT6_753>,
    pub wrap_proof: Option<Proof<MNT6_753>>,
    /// `GenesisSpendCircuit`'s original 6 `Fr4` public values (pre-chunking
    /// — `public_input_chunks` derives what `wrap_proof` actually commits to).
    pub wrap_public_inputs: Option<[Fr; SPEND_PUBLIC_INPUT_COUNT]>,

    // Private witnesses: board inclusion of entry_k (MAX_OUTPUTS = 1, see
    // circuit-spend's `GenesisSpendCircuit` doc comment for why).
    pub entry_nullifier: Option<Fr>,
    pub entry_output_commitment: Option<Fr>,
    pub entry_ciphertext_commitment: Option<Fr>,
    pub received_slot: Option<u64>,
    /// Length `TREE_DEPTH`.
    pub append_path: Option<Vec<Fr>>,

    // Private witnesses: parent-nullifier non-membership.
    pub parent_nonmembership: Option<NonMembershipWitness>,
    pub nullifier_root_at_parent_slot: Option<Fr>,
}

impl ConstraintSynthesizer<Fr> for ReceiptStepCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        // --- public inputs ---
        // Allocated as public inputs (part of the circuit's public
        // statement) but never referenced in a constraint — `owner_pk` is a
        // free claim the receipt's builder asserts, not checked against
        // anything here; see the note further down where the spend proof's
        // output_commitment is recovered.
        let _owner_pk_x = Fp::new_input(cs.clone(), || opt(&self.owner_pk_x))?;
        let _owner_pk_y = Fp::new_input(cs.clone(), || opt(&self.owner_pk_y))?;
        let coin_commitment = Fp::new_input(cs.clone(), || opt(&self.coin_commitment))?;
        let board_root = Fp::new_input(cs.clone(), || opt(&self.board_root))?;
        let received_at = Fp::new_input(cs.clone(), || opt(&self.received_at.map(Fr::from)))?;

        // --- recursively verify the wrapped parent spend proof ---
        let wrap_public_len = SPEND_PUBLIC_INPUT_COUNT * chunks_per_value();
        let bit_len = Fr6::MODULUS_BIT_SIZE as usize;
        let wrap_native_chunks: Option<Vec<Fr6>> =
            self.wrap_public_inputs.as_ref().map(|v| public_input_chunks(v));
        let mut per_chunk_bits: Vec<Vec<Boolean<Fr>>> = Vec::with_capacity(wrap_public_len);
        for i in 0..wrap_public_len {
            let value_bits: Option<Vec<bool>> =
                wrap_native_chunks.as_ref().map(|v| v[i].into_bigint().to_bits_le());
            let bits: Vec<Boolean<Fr>> = (0..bit_len)
                .map(|j| Boolean::new_witness(cs.clone(), || opt(&value_bits.as_ref().map(|b| b[j]))))
                .collect::<Result<_, _>>()?;
            per_chunk_bits.push(bits);
        }
        let input_var = BooleanInputVar::<Fr6, Fr>::new(per_chunk_bits.clone());

        let wrap_vk_var = VerifyingKeyVar::<MNT6_753, MNT6PairingVar>::new_constant(cs.clone(), &self.wrap_vk)?;
        let wrap_proof_var =
            ProofVar::<MNT6_753, MNT6PairingVar>::new_witness(cs.clone(), || opt(&self.wrap_proof))?;
        let pvk = wrap_vk_var.prepare()?;
        let ok = Groth16VerifierGadget::<MNT6_753, MNT6PairingVar>::verify_with_processed_vk(
            &pvk,
            &input_var,
            &wrap_proof_var,
        )?;
        ok.enforce_equal(&Boolean::TRUE)?;

        // --- recover the spend proof's output_commitment from its chunk group ---
        //
        // Only `output_commitment` is needed: `check_coin_receipt` only ever
        // checks `spend_pv.output_commitments.contains(coin_commitment)`,
        // never the spend's own (input-side) `coin_commitment` — that's a
        // different coin (the one that funded the spend, not the one it
        // created). And the wrapped proof's `pk_p` is the *spender*, not
        // this receipt's `owner_pk` (the *recipient* — the wallet building
        // this receipt just asserts it, the same way `check_coin_receipt`
        // takes `owner_pk` as a free parameter, never checked against the
        // spend proof). Real ownership is enforced later, when the coin is
        // actually spent: `check_spend` derives `input_coin.owner_pk` from
        // the coin's full opening (tag/value/rand/owner_pk) and requires it
        // to equal the spender's own `pk_p` — that's the load-bearing
        // check, not this receipt's `owner_pk`.
        let cpv = chunks_per_value();
        let group = |idx: usize| -> &[Vec<Boolean<Fr>>] { &per_chunk_bits[idx * cpv..(idx + 1) * cpv] };
        let spend_output_commitment = combine_chunks_var(group(SPEND_OUTPUT_COMMITMENT))?;

        // Provenance: the spend proof must actually have created this coin
        // (mirrors `check_coin_receipt`'s `spend_pv.output_commitments.contains(...)`).
        spend_output_commitment.enforce_equal(&coin_commitment)?;

        // --- board inclusion of entry_k ---
        let entry_nullifier = Fp::new_witness(cs.clone(), || opt(&self.entry_nullifier))?;
        let entry_output_commitment = Fp::new_witness(cs.clone(), || opt(&self.entry_output_commitment))?;
        let entry_ciphertext_commitment = Fp::new_witness(cs.clone(), || opt(&self.entry_ciphertext_commitment))?;
        let received_slot_fp = Fp::new_witness(cs.clone(), || opt(&self.received_slot.map(Fr::from)))?;
        let received_slot_bits = received_slot_fp.to_bits_le()?;
        let append_path = alloc_fp_vec(cs.clone(), &self.append_path, TREE_DEPTH)?;

        let output_commitments_hash = poseidon_hash_var(cs.clone(), &[entry_output_commitment.clone()])?;
        let entry_leaf = poseidon_hash_var(
            cs.clone(),
            &[received_slot_fp.clone(), entry_ciphertext_commitment, entry_nullifier.clone(), output_commitments_hash],
        )?;
        let board_root_computed =
            compute_root_from_path_var(cs.clone(), &entry_leaf, &received_slot_bits[..TREE_DEPTH], &append_path)?;
        board_root_computed.enforce_equal(&board_root)?;
        received_slot_fp.enforce_equal(&received_at)?;

        // --- coin_commitment must be among entry_k.output_commitments
        // (MAX_OUTPUTS = 1, so this is a direct equality) ---
        entry_output_commitment.enforce_equal(&coin_commitment)?;

        // --- parent-nullifier non-membership ---
        let w = &self.parent_nonmembership;
        let low_leaf = IndexedLeafVar {
            value: Fp::new_witness(cs.clone(), || opt(&w.as_ref().map(|w| w.low_leaf.value)))?,
            next_value: Fp::new_witness(cs.clone(), || opt(&w.as_ref().map(|w| w.low_leaf.next_value)))?,
            next_index: Fp::new_witness(cs.clone(), || opt(&w.as_ref().map(|w| Fr::from(w.low_leaf.next_index))))?,
        };
        let low_leaf_index_fp =
            Fp::new_witness(cs.clone(), || opt(&w.as_ref().map(|w| Fr::from(w.low_leaf_index))))?;
        let low_leaf_index_bits = low_leaf_index_fp.to_bits_le()?;
        let sibling_path = alloc_fp_vec(cs.clone(), &w.as_ref().map(|w| w.sibling_path.clone()), TREE_DEPTH)?;
        let nullifier_root_at_parent_slot =
            Fp::new_witness(cs.clone(), || opt(&self.nullifier_root_at_parent_slot))?;

        let nonmembership_ok = verify_nonmembership_var(
            cs.clone(),
            &nullifier_root_at_parent_slot,
            &entry_nullifier,
            &low_leaf,
            &low_leaf_index_bits[..TREE_DEPTH],
            &sibling_path,
        )?;
        nonmembership_ok.enforce_equal(&Boolean::TRUE)?;

        Ok(())
    }
}

impl ReceiptStepCircuit {
    pub fn public_inputs(
        owner_pk_x: Fr,
        owner_pk_y: Fr,
        coin_commitment: Fr,
        board_root: Fr,
        received_at: u64,
    ) -> Vec<Fr> {
        vec![owner_pk_x, owner_pk_y, coin_commitment, board_root, Fr::from(received_at)]
    }
}

pub fn setup<R: RngCore + CryptoRng>(
    wrap_vk: VerifyingKey<MNT6_753>,
    rng: &mut R,
) -> Result<(ProvingKey<MNT4_753>, VerifyingKey<MNT4_753>), SynthesisError> {
    // See circuit-wrap's `setup` for why `wrap_proof` needs a structurally
    // valid dummy rather than `None` — `ProofVar`'s `AllocVar` impl calls
    // its value closure unconditionally, even in setup mode.
    let dummy_proof = Proof::<MNT6_753> {
        a: ark_mnt6_753::G1Affine::identity(),
        b: ark_mnt6_753::G2Affine::identity(),
        c: ark_mnt6_753::G1Affine::identity(),
    };
    let circuit = ReceiptStepCircuit {
        owner_pk_x: None,
        owner_pk_y: None,
        coin_commitment: None,
        board_root: None,
        received_at: None,
        wrap_vk,
        wrap_proof: Some(dummy_proof),
        wrap_public_inputs: None,
        entry_nullifier: None,
        entry_output_commitment: None,
        entry_ciphertext_commitment: None,
        received_slot: None,
        append_path: None,
        parent_nonmembership: None,
        nullifier_root_at_parent_slot: None,
    };
    Groth16::<MNT4_753>::circuit_specific_setup(circuit, rng)
}

pub fn prove<R: RngCore + CryptoRng>(
    pk: &ProvingKey<MNT4_753>,
    circuit: ReceiptStepCircuit,
    rng: &mut R,
) -> Result<Proof<MNT4_753>, SynthesisError> {
    Groth16::<MNT4_753>::prove(pk, circuit, rng)
}

pub fn verify(
    vk: &VerifyingKey<MNT4_753>,
    public_inputs: &[Fr],
    proof: &Proof<MNT4_753>,
) -> Result<bool, SynthesisError> {
    Groth16::<MNT4_753>::verify(vk, public_inputs, proof)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_std::rand::{rngs::StdRng, SeedableRng};
    use cloakkchain_circuit_spend::GenesisSpendCircuit;
    use cloakkchain_lib::{
        append_path_for_next, compute_root_from_path, derive_owner_pk, fold_owner_scalar, genesis_sk, poseidon_hash,
        Coin, NullifierTree, OwnerScalar,
    };

    /// End-to-end: a genesis mint (circuit-spend), wrapped for the curve
    /// cycle (circuit-wrap), then a coin-receipt built on top of it
    /// (this crate) — the "Genesis -> Wrap -> Receipt" leg of the port
    /// plan's 2-hop chain exit criterion.
    #[test]
    fn genesis_wrap_receipt_chain_end_to_end() {
        let mut rng = StdRng::seed_from_u64(99);

        // --- 1. genesis mint (mirrors circuit-spend's own valid_circuit()) ---
        let sk_p = genesis_sk();
        let pk_p = derive_owner_pk(&sk_p);
        let input_coin = Coin { tag: Fr::from(1u64), value: 100, rand: Fr::from(2u64), owner_pk: pk_p };
        let recipient_sk = OwnerScalar::from(42u64);
        let recipient_pk = derive_owner_pk(&recipient_sk);
        let output_coin = Coin { tag: Fr::from(3u64), value: 100, rand: Fr::from(4u64), owner_pk: recipient_pk };

        let coin_commitment = input_coin.commitment();
        let output_commitment = output_coin.commitment();
        let entry_position = 0u64;
        let append_path = append_path_for_next(&[]); // empty board — first-ever entry

        let genesis_own_nullifier = poseidon_hash(&[coin_commitment, fold_owner_scalar(&sk_p)]);
        let genesis_tree = NullifierTree::new(); // empty — genesis has no predecessor
        let current_nullifier_root = genesis_tree.root();
        let own_nullifier_nonmembership = genesis_tree.prove_non_membership(genesis_own_nullifier);

        let board_root = compute_root_from_path(Fr::from(0u64), entry_position as usize, &append_path);

        let genesis_circuit = GenesisSpendCircuit {
            pk_p: Some(pk_p),
            coin_commitment: Some(coin_commitment),
            board_root: Some(board_root),
            output_commitment: Some(output_commitment),
            current_nullifier_root: Some(current_nullifier_root),
            sk_p: Some(sk_p),
            input_coin: Some(input_coin),
            output_coin: Some(output_coin),
            entry_position: Some(entry_position),
            append_path: Some(append_path.clone()),
            own_nullifier_nonmembership: Some(own_nullifier_nonmembership),
        };
        let (genesis_pk_data, genesis_vk) = cloakkchain_circuit_spend::setup(&mut rng).unwrap();
        let genesis_public_inputs: [Fr; 6] =
            GenesisSpendCircuit::public_inputs(pk_p, coin_commitment, board_root, output_commitment, current_nullifier_root)
                .try_into()
                .unwrap();
        let genesis_proof = cloakkchain_circuit_spend::prove(&genesis_pk_data, genesis_circuit, &mut rng).unwrap();
        assert!(cloakkchain_circuit_spend::verify(&genesis_vk, &genesis_public_inputs, &genesis_proof).unwrap());

        // --- 2. wrap the genesis proof for the curve cycle ---
        let (wrap_pk, wrap_vk) = cloakkchain_circuit_wrap::setup::<6, _>(genesis_vk.clone(), &mut rng).unwrap();
        let wrap_circuit = cloakkchain_circuit_wrap::WrapCircuit::<6> {
            inner_vk: genesis_vk,
            inner_proof: Some(genesis_proof),
            inner_public_inputs: Some(genesis_public_inputs),
        };
        let wrap_proof = cloakkchain_circuit_wrap::prove::<6, _>(&wrap_pk, wrap_circuit, &mut rng).unwrap();
        let wrap_public_inputs = public_input_chunks(&genesis_public_inputs);
        assert!(cloakkchain_circuit_wrap::verify(&wrap_vk, &wrap_public_inputs, &wrap_proof).unwrap());

        // --- 3. the coin receipt: entry_k *is* the genesis transaction's
        // own board entry, at the same slot/append_path as its spend proof
        // checked against (this is the one and only entry on the board so far) ---
        let entry_ciphertext_commitment = Fr::from(999u64); // opaque placeholder — see the field's doc comment
        let receipt_board_root =
            compute_root_from_path(cloakkchain_lib::merkle_leaf_from_commitment(entry_position as usize, genesis_own_nullifier, &[output_commitment], entry_ciphertext_commitment), entry_position as usize, &append_path);

        let receipt_circuit = ReceiptStepCircuit {
            owner_pk_x: Some(cloakkchain_lib::owner_pk_to_field_pair(&recipient_pk).0),
            owner_pk_y: Some(cloakkchain_lib::owner_pk_to_field_pair(&recipient_pk).1),
            coin_commitment: Some(output_commitment),
            board_root: Some(receipt_board_root),
            received_at: Some(entry_position),
            wrap_vk: wrap_vk.clone(),
            wrap_proof: Some(wrap_proof),
            wrap_public_inputs: Some(genesis_public_inputs),
            entry_nullifier: Some(genesis_own_nullifier),
            entry_output_commitment: Some(output_commitment),
            entry_ciphertext_commitment: Some(entry_ciphertext_commitment),
            received_slot: Some(entry_position),
            append_path: Some(append_path),
            parent_nonmembership: Some(genesis_tree.prove_non_membership(genesis_own_nullifier)),
            nullifier_root_at_parent_slot: Some(genesis_tree.root()),
        };

        let (receipt_pk, receipt_vk) = setup(wrap_vk, &mut rng).unwrap();
        let (rpx, rpy) = cloakkchain_lib::owner_pk_to_field_pair(&recipient_pk);
        let receipt_public_inputs = ReceiptStepCircuit::public_inputs(rpx, rpy, output_commitment, receipt_board_root, entry_position);
        let receipt_proof = prove(&receipt_pk, receipt_circuit, &mut rng).unwrap();
        assert!(verify(&receipt_vk, &receipt_public_inputs, &receipt_proof).unwrap(), "a genuinely valid receipt proof must verify");

        let mut tampered = receipt_public_inputs.clone();
        tampered[2] += Fr::from(1u64);
        assert!(!verify(&receipt_vk, &tampered, &receipt_proof).unwrap(), "must not verify against the wrong public inputs");
    }

    /// The full port plan's 2-hop chain exit criterion: genesis mints a
    /// coin to Alice (circuit-spend), Alice's receipt is built on top of it
    /// (this crate, wrapped for the curve cycle both times), then Alice
    /// spends that coin to Bob (circuit-spend's non-genesis
    /// `SpendStepCircuit`, recursively verifying the wrapped receipt).
    /// Five real Groth16 proofs end to end: Genesis -> Wrap -> Receipt ->
    /// Wrap -> Spend.
    #[test]
    fn full_two_hop_chain_genesis_to_bob() {
        use cloakkchain_circuit_spend::SpendStepCircuit;
        use cloakkchain_lib::{entry_ciphertext_commitment, BoardEntry};

        let mut rng = StdRng::seed_from_u64(2026);

        // --- genesis mints to Alice ---
        let sk_genesis = genesis_sk();
        let pk_genesis = derive_owner_pk(&sk_genesis);
        let genesis_input_coin = Coin { tag: Fr::from(1u64), value: 100, rand: Fr::from(2u64), owner_pk: pk_genesis };
        let alice_sk = OwnerScalar::from(42u64);
        let alice_pk = derive_owner_pk(&alice_sk);
        let alice_coin = Coin { tag: Fr::from(3u64), value: 100, rand: Fr::from(4u64), owner_pk: alice_pk };

        let genesis_coin_commitment = genesis_input_coin.commitment();
        let alice_coin_commitment = alice_coin.commitment();
        let genesis_entry_position = 0u64;
        let genesis_append_path = append_path_for_next(&[]);

        let genesis_own_nullifier = poseidon_hash(&[genesis_coin_commitment, fold_owner_scalar(&sk_genesis)]);
        let empty_tree = NullifierTree::new();
        let genesis_board_root =
            compute_root_from_path(Fr::from(0u64), genesis_entry_position as usize, &genesis_append_path);

        let genesis_circuit = GenesisSpendCircuit {
            pk_p: Some(pk_genesis),
            coin_commitment: Some(genesis_coin_commitment),
            board_root: Some(genesis_board_root),
            output_commitment: Some(alice_coin_commitment),
            current_nullifier_root: Some(empty_tree.root()),
            sk_p: Some(sk_genesis),
            input_coin: Some(genesis_input_coin),
            output_coin: Some(alice_coin.clone()),
            entry_position: Some(genesis_entry_position),
            append_path: Some(genesis_append_path.clone()),
            own_nullifier_nonmembership: Some(empty_tree.prove_non_membership(genesis_own_nullifier)),
        };
        let (genesis_pk_data, genesis_vk) = cloakkchain_circuit_spend::setup(&mut rng).unwrap();
        let genesis_public_inputs: [Fr; 6] = GenesisSpendCircuit::public_inputs(
            pk_genesis,
            genesis_coin_commitment,
            genesis_board_root,
            alice_coin_commitment,
            empty_tree.root(),
        )
        .try_into()
        .unwrap();
        let genesis_proof = cloakkchain_circuit_spend::prove(&genesis_pk_data, genesis_circuit, &mut rng).unwrap();

        // --- wrap #1: the genesis proof ---
        let (wrap1_pk, wrap1_vk) = cloakkchain_circuit_wrap::setup::<6, _>(genesis_vk.clone(), &mut rng).unwrap();
        let wrap1_proof = cloakkchain_circuit_wrap::prove::<6, _>(
            &wrap1_pk,
            cloakkchain_circuit_wrap::WrapCircuit::<6> {
                inner_vk: genesis_vk,
                inner_proof: Some(genesis_proof),
                inner_public_inputs: Some(genesis_public_inputs),
            },
            &mut rng,
        )
        .unwrap();

        // --- Alice's receipt: entry_k is genesis's own (real) board entry ---
        let genesis_entry = BoardEntry {
            ciphertext: vec![],
            ek_pk: [0u8; 32],
            key_encs: vec![],
            nullifier: genesis_own_nullifier,
            output_commitments: vec![alice_coin_commitment],
        };
        let genesis_entry_ciphertext_commitment = entry_ciphertext_commitment(&genesis_entry);
        let receipt_board_root = compute_root_from_path(
            cloakkchain_lib::merkle_leaf(genesis_entry_position as usize, &genesis_entry),
            genesis_entry_position as usize,
            &genesis_append_path,
        );

        let receipt_circuit = ReceiptStepCircuit {
            owner_pk_x: Some(cloakkchain_lib::owner_pk_to_field_pair(&alice_pk).0),
            owner_pk_y: Some(cloakkchain_lib::owner_pk_to_field_pair(&alice_pk).1),
            coin_commitment: Some(alice_coin_commitment),
            board_root: Some(receipt_board_root),
            received_at: Some(genesis_entry_position),
            wrap_vk: wrap1_vk.clone(),
            wrap_proof: Some(wrap1_proof),
            wrap_public_inputs: Some(genesis_public_inputs),
            entry_nullifier: Some(genesis_own_nullifier),
            entry_output_commitment: Some(alice_coin_commitment),
            entry_ciphertext_commitment: Some(genesis_entry_ciphertext_commitment),
            received_slot: Some(genesis_entry_position),
            append_path: Some(genesis_append_path.clone()),
            parent_nonmembership: Some(empty_tree.prove_non_membership(genesis_own_nullifier)),
            nullifier_root_at_parent_slot: Some(empty_tree.root()),
        };
        let (receipt_pk_data, receipt_vk) = setup(wrap1_vk, &mut rng).unwrap();
        let (apx, apy) = cloakkchain_lib::owner_pk_to_field_pair(&alice_pk);
        let receipt_public_inputs: [Fr; 5] =
            ReceiptStepCircuit::public_inputs(apx, apy, alice_coin_commitment, receipt_board_root, genesis_entry_position)
                .try_into()
                .unwrap();
        let receipt_proof = prove(&receipt_pk_data, receipt_circuit, &mut rng).unwrap();

        // --- wrap #2: Alice's receipt proof ---
        let (wrap2_pk, wrap2_vk) = cloakkchain_circuit_wrap::setup::<5, _>(receipt_vk.clone(), &mut rng).unwrap();
        let wrap2_proof = cloakkchain_circuit_wrap::prove::<5, _>(
            &wrap2_pk,
            cloakkchain_circuit_wrap::WrapCircuit::<5> {
                inner_vk: receipt_vk,
                inner_proof: Some(receipt_proof),
                inner_public_inputs: Some(receipt_public_inputs),
            },
            &mut rng,
        )
        .unwrap();

        // --- Alice spends her coin to Bob ---
        let bob_sk = OwnerScalar::from(7u64);
        let bob_pk = derive_owner_pk(&bob_sk);
        let bob_coin = Coin { tag: Fr::from(5u64), value: 100, rand: Fr::from(6u64), owner_pk: bob_pk };
        let bob_coin_commitment = bob_coin.commitment();

        let spend_entry_position = 1u64; // the board now has one entry (genesis's)
        let spend_append_path = append_path_for_next(std::slice::from_ref(&genesis_entry));
        let spend_board_root =
            compute_root_from_path(Fr::from(0u64), spend_entry_position as usize, &spend_append_path);

        let alice_own_nullifier = poseidon_hash(&[alice_coin_commitment, fold_owner_scalar(&alice_sk)]);
        // Alice's coin has never been spent — the accumulator only contains
        // genesis's own nullifier so far (inserted after genesis's slot).
        let mut tree_after_genesis = NullifierTree::new();
        tree_after_genesis.insert(genesis_own_nullifier);

        let spend_circuit = SpendStepCircuit {
            pk_p: Some(alice_pk),
            coin_commitment: Some(alice_coin_commitment),
            board_root: Some(spend_board_root),
            output_commitment: Some(bob_coin_commitment),
            current_nullifier_root: Some(tree_after_genesis.root()),
            sk_p: Some(alice_sk),
            input_coin: Some(alice_coin),
            output_coin: Some(bob_coin),
            entry_position: Some(spend_entry_position),
            append_path: Some(spend_append_path),
            own_nullifier_nonmembership: Some(tree_after_genesis.prove_non_membership(alice_own_nullifier)),
            wrap_vk: wrap2_vk.clone(),
            wrap_proof: Some(wrap2_proof),
            wrap_public_inputs: Some(receipt_public_inputs),
        };
        let (spend_pk_data, spend_vk) = cloakkchain_circuit_spend::setup_non_genesis(wrap2_vk, &mut rng).unwrap();
        let spend_public_inputs = SpendStepCircuit::public_inputs(
            alice_pk,
            alice_coin_commitment,
            spend_board_root,
            bob_coin_commitment,
            tree_after_genesis.root(),
        );
        let spend_proof = cloakkchain_circuit_spend::prove_non_genesis(&spend_pk_data, spend_circuit, &mut rng).unwrap();

        assert!(
            cloakkchain_circuit_spend::verify_non_genesis(&spend_vk, &spend_public_inputs, &spend_proof).unwrap(),
            "a genuinely valid Alice-to-Bob spend, backed by a real verified receipt, must verify"
        );

        let mut tampered = spend_public_inputs.clone();
        tampered[3] += Fr::from(1u64); // perturb output_commitment
        assert!(
            !cloakkchain_circuit_spend::verify_non_genesis(&spend_vk, &tampered, &spend_proof).unwrap(),
            "must not verify against the wrong public inputs"
        );
    }
}
