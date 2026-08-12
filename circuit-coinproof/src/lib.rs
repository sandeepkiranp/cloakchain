//! MNT-native coin-receipt circuit. `ReceiptStepCircuit` is the receipt-side
//! business logic (see `cloakkchain_lib::check_coin_receipt`) — Fr4-native,
//! the same field as `circuit-spend`'s circuits. Per the MNT-native port
//! plan's "wrap layer" architecture note: business logic (Merkle /
//! nullifier-tree work) stays entirely native here; curve-cycle recursion
//! happens via `circuit-wrap`'s `WrapCircuit`, never by putting hashing on
//! the "wrong" field.
//!
//! Currently fixed to recursively verify a *wrapped* `GenesisSpendCircuit`-
//! or-`SpendStepCircuit`-shaped proof specifically (both share the same
//! public-input layout, `circuit_spend::SPEND_PUBLIC_INPUT_COUNT` /
//! `GenesisSpendCircuit::public_inputs`'s order) from one specific
//! deployment (`wrap_vk` is fixed at setup time, not chosen between several
//! candidates) — see `circuit_spend`'s module doc comment for why a single
//! circuit can't yet accept either of several *different* VKs without
//! solving the recursive-SNARK VK-bootstrapping problem.

use ark_crypto_primitives::snark::{constraints::SNARKGadget, BooleanInputVar};
use ark_crypto_primitives::sponge::{constraints::CryptographicSpongeVar, poseidon::constraints::PoseidonSpongeVar};
use ark_ec::PrimeGroup;
use ark_ff::{BigInteger, PrimeField};
use ark_groth16::{
    constraints::{Groth16VerifierGadget, ProofVar, VerifyingKeyVar},
    Groth16, Proof, ProvingKey, VerifyingKey,
};
use ark_mnt4_753::MNT4_753;
use ark_mnt6_753::MNT6_753;
use ark_r1cs_std::{cmp::CmpGadget, fields::fp::FpVar, prelude::*};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_snark::SNARK;
use ark_std::rand::{CryptoRng, RngCore};
use cloakkchain_circuit_wrap::{chunks_per_value, combine_chunks_var, public_input_chunks, Fr6};
use cloakkchain_lib::{Fr, NonMembershipWitness, OwnerScalar, TREE_DEPTH};

type Fp = FpVar<Fr>;
type MNT6PairingVar = ark_mnt6_753::constraints::PairingVar;
type G1Var = ark_mnt6_753::constraints::G1Var;

/// `MAX_OUTPUTS` output coins per board entry / spend, matching
/// `circuit_spend::MAX_OUTPUTS` (duplicated as a plain constant rather than
/// a crate dependency, to avoid a circuit-coinproof <-> circuit-spend
/// cycle — both sides must keep this in sync by construction, not by the
/// type system).
pub const MAX_OUTPUTS: usize = 2;

/// The wrapped spend circuit's public-input count/order (mirrors
/// `circuit_spend::SPEND_PUBLIC_INPUT_COUNT`
/// /`GenesisSpendCircuit::public_inputs`): `pk.x, pk.y,
/// output_commitments[0..MAX_OUTPUTS], board_root, nullifier_root`.
const SPEND_PUBLIC_INPUT_COUNT: usize = 2 + MAX_OUTPUTS + 2;
const SPEND_OUTPUT_COMMITMENTS_START: usize = 2;

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

/// `target` is a member of `list` — an OR of per-slot equality checks. Used
/// for both `coin_commitment ∈ entry_k.output_commitments` and
/// `coin_commitment ∈ spend_pv.output_commitments`, since both are now
/// fixed-size `MAX_OUTPUTS` lists rather than a single value.
fn is_member(target: &Fp, list: &[Fp]) -> Result<Boolean<Fr>, SynthesisError> {
    let mut any = Boolean::FALSE;
    for item in list {
        any = &any | &target.is_eq(item)?;
    }
    Ok(any)
}

/// Public values, in this order: `owner_pk.x, owner_pk.y, coin_commitment,
/// board_root, received_at`.
///
/// `owner_pk` is not a free claim: the circuit derives it in-circuit from a
/// witnessed `sk_p` and requires the witnessed coin opening (`coin_tag`/
/// `coin_value`/`coin_rand` plus that same `owner_pk`) to actually hash to
/// the public `coin_commitment`. So building a valid receipt requires
/// genuinely knowing how to open the coin, not just naming a commitment
/// that happens to be on the board.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct ReceiptStepCircuit {
    // Public values.
    pub owner_pk_x: Option<Fr>,
    pub owner_pk_y: Option<Fr>,
    pub coin_commitment: Option<Fr>,
    pub board_root: Option<Fr>,
    pub received_at: Option<u64>,

    // Private witnesses: the wrapped parent-spend proof (a
    // Wrap<SPEND_PUBLIC_INPUT_COUNT> proof).
    /// Fixed per deployment — not `Option`, a verifying key isn't secret.
    pub wrap_vk: VerifyingKey<MNT6_753>,
    pub wrap_proof: Option<Proof<MNT6_753>>,
    /// The wrapped spend circuit's original `Fr4` public values
    /// (pre-chunking — `public_input_chunks` derives what `wrap_proof`
    /// actually commits to).
    pub wrap_public_inputs: Option<[Fr; SPEND_PUBLIC_INPUT_COUNT]>,

    // Private witnesses: board inclusion of entry_k.
    pub entry_nullifier: Option<Fr>,
    pub entry_output_commitments: Option<[Fr; MAX_OUTPUTS]>,
    pub entry_ciphertext_commitment: Option<Fr>,
    pub received_slot: Option<u64>,
    /// Length `TREE_DEPTH`.
    pub append_path: Option<Vec<Fr>>,

    // Private witnesses: parent-nullifier non-membership.
    pub parent_nonmembership: Option<NonMembershipWitness>,
    pub nullifier_root_at_parent_slot: Option<Fr>,

    // Private witnesses: proof that the receipt-builder actually owns and
    // can open `coin_commitment` — `owner_pk` derived in-circuit from
    // `sk_p` (not a free claim, see the constraint below), and the coin's
    // full opening checked to actually hash to the public `coin_commitment`.
    pub sk_p: Option<OwnerScalar>,
    pub coin_tag: Option<Fr>,
    pub coin_value: Option<u64>,
    pub coin_rand: Option<Fr>,
}

impl ConstraintSynthesizer<Fr> for ReceiptStepCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        // --- public inputs ---
        let owner_pk_x = Fp::new_input(cs.clone(), || opt(&self.owner_pk_x))?;
        let owner_pk_y = Fp::new_input(cs.clone(), || opt(&self.owner_pk_y))?;
        let coin_commitment = Fp::new_input(cs.clone(), || opt(&self.coin_commitment))?;
        let board_root = Fp::new_input(cs.clone(), || opt(&self.board_root))?;
        let received_at = Fp::new_input(cs.clone(), || opt(&self.received_at.map(Fr::from)))?;

        // --- ownership + opening: owner_pk must genuinely be derived from
        // sk_p, and (owner_pk, tag, value, rand) must genuinely hash to the
        // public coin_commitment — the receipt-builder must actually be able
        // to open the coin they're claiming, not just assert a commitment
        // value that happens to be on the board. Mirrors the same
        // scalar-mult + canonicity pattern `GenesisSpendCircuit`/
        // `SpendStepCircuit` use for their own `pk_p`.
        let sk_bit_values: Option<Vec<bool>> = self.sk_p.map(|sk| sk.into_bigint().to_bits_le());
        let sk_bit_len = OwnerScalar::MODULUS_BIT_SIZE as usize;
        let sk_bits: Vec<Boolean<Fr>> = (0..sk_bit_len)
            .map(|i| Boolean::new_witness(cs.clone(), || opt(&sk_bit_values.as_ref().map(|b| b[i]))))
            .collect::<Result<_, _>>()?;
        let mut modulus_minus_one = OwnerScalar::MODULUS.0.to_vec();
        modulus_minus_one[0] -= 1; // odd prime modulus, so this can't borrow
        Boolean::enforce_smaller_or_equal_than_le(&sk_bits, modulus_minus_one)?;

        let generator = G1Var::new_constant(cs.clone(), ark_mnt6_753::G1Projective::generator())?;
        let pk_p_computed = generator.scalar_mul_le(sk_bits.iter())?.to_affine()?;
        pk_p_computed.x.enforce_equal(&owner_pk_x)?;
        pk_p_computed.y.enforce_equal(&owner_pk_y)?;

        let coin_tag = Fp::new_witness(cs.clone(), || opt(&self.coin_tag))?;
        let coin_value = UInt64::new_witness(cs.clone(), || opt(&self.coin_value))?;
        let coin_rand = Fp::new_witness(cs.clone(), || opt(&self.coin_rand))?;
        let coin_commitment_computed = poseidon_hash_var(
            cs.clone(),
            &[coin_tag, coin_value.to_fp()?, coin_rand, owner_pk_x, owner_pk_y],
        )?;
        coin_commitment_computed.enforce_equal(&coin_commitment)?;

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

        // --- recover the spend proof's output_commitments from their chunk groups ---
        //
        // Only `output_commitments` is needed: `check_coin_receipt` only
        // ever checks `spend_pv.output_commitments.contains(coin_commitment)`,
        // never the spend's own input side (a different coin — the one that
        // funded the spend, not the one it created). The wrapped proof's
        // `pk_p` is the *spender* who created this coin, deliberately never
        // compared against this receipt's `owner_pk` (the *recipient*,
        // verified above to genuinely open `coin_commitment`) — those are
        // two unrelated identities. Whether *this same* receipt-holder is
        // the one later spending the coin is a separate fact, checked when
        // it's actually spent: `SpendStepCircuit`'s `binding_ok` requires
        // the spender's own freshly-derived `pk_p` to match this receipt's
        // (verified) `owner_pk` public output.
        let cpv = chunks_per_value();
        let group = |idx: usize| -> &[Vec<Boolean<Fr>>] { &per_chunk_bits[idx * cpv..(idx + 1) * cpv] };
        let spend_output_commitments: Vec<Fp> = (0..MAX_OUTPUTS)
            .map(|i| combine_chunks_var(group(SPEND_OUTPUT_COMMITMENTS_START + i)))
            .collect::<Result<_, _>>()?;

        // Provenance: the spend proof must actually have created this coin
        // (mirrors `check_coin_receipt`'s `spend_pv.output_commitments.contains(...)`).
        is_member(&coin_commitment, &spend_output_commitments)?.enforce_equal(&Boolean::TRUE)?;

        // --- board inclusion of entry_k ---
        let entry_nullifier = Fp::new_witness(cs.clone(), || opt(&self.entry_nullifier))?;
        let entry_output_commitments: Vec<Fp> = (0..MAX_OUTPUTS)
            .map(|i| Fp::new_witness(cs.clone(), || opt(&self.entry_output_commitments.map(|a| a[i]))))
            .collect::<Result<_, _>>()?;
        let entry_ciphertext_commitment = Fp::new_witness(cs.clone(), || opt(&self.entry_ciphertext_commitment))?;
        let received_slot_fp = Fp::new_witness(cs.clone(), || opt(&self.received_slot.map(Fr::from)))?;
        let received_slot_bits = received_slot_fp.to_bits_le()?;
        let append_path = alloc_fp_vec(cs.clone(), &self.append_path, TREE_DEPTH)?;

        let output_commitments_hash = poseidon_hash_var(cs.clone(), &entry_output_commitments)?;
        let entry_leaf = poseidon_hash_var(
            cs.clone(),
            &[received_slot_fp.clone(), entry_ciphertext_commitment, entry_nullifier.clone(), output_commitments_hash],
        )?;
        let board_root_computed =
            compute_root_from_path_var(cs.clone(), &entry_leaf, &received_slot_bits[..TREE_DEPTH], &append_path)?;
        board_root_computed.enforce_equal(&board_root)?;
        received_slot_fp.enforce_equal(&received_at)?;

        // --- coin_commitment must be among entry_k.output_commitments ---
        is_member(&coin_commitment, &entry_output_commitments)?.enforce_equal(&Boolean::TRUE)?;

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
        entry_output_commitments: None,
        entry_ciphertext_commitment: None,
        received_slot: None,
        append_path: None,
        parent_nonmembership: None,
        nullifier_root_at_parent_slot: None,
        sk_p: None,
        coin_tag: None,
        coin_value: None,
        coin_rand: None,
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
    use cloakkchain_circuit_spend::{GenesisSpendCircuit, SpendStepCircuit};
    use cloakkchain_lib::{
        append_path_for_next, compute_root_from_path, derive_owner_pk, entry_ciphertext_commitment,
        fold_owner_scalar, genesis_sk, merkle_leaf, poseidon_hash, BoardEntry, Coin, NullifierTree, OwnerScalar,
    };

    /// Pads a variable-length list of real output commitments out to
    /// `MAX_OUTPUTS` with a zero sentinel — both `GenesisSpendCircuit`'s/
    /// `SpendStepCircuit`'s fixed-size public output and any `BoardEntry`
    /// built from the same transaction must agree on this padding, or the
    /// entry's leaf hash won't match what the circuit computed.
    fn pad_outputs(real: &[Fr]) -> [Fr; MAX_OUTPUTS] {
        let mut out = [Fr::from(0u64); MAX_OUTPUTS];
        out[..real.len()].copy_from_slice(real);
        out
    }

    /// A receipt-builder who doesn't actually own/can't open the coin they're
    /// claiming must fail — the ownership + opening check added to
    /// `ReceiptStepCircuit` (see its doc comment) is the thing under test
    /// here, not the recursive-verification/board-inclusion machinery, so
    /// this only pays for one genuine genesis+wrap proof (needed as a real
    /// witness either way) and then checks raw constraint satisfiability
    /// directly — no Groth16 setup/prove needed for the receipt itself.
    #[test]
    fn wrong_owner_key_fails_receipt() {
        use ark_relations::r1cs::ConstraintSystem;

        let mut rng = StdRng::seed_from_u64(20260811);

        let sk_genesis = genesis_sk();
        let pk_genesis = derive_owner_pk(&sk_genesis);
        let genesis_input = Coin { tag: Fr::from(1u64), value: 100, rand: Fr::from(2u64), owner_pk: pk_genesis };
        let alice_sk = OwnerScalar::from(42u64);
        let alice_pk = derive_owner_pk(&alice_sk);
        let alice_coin = Coin { tag: Fr::from(3u64), value: 100, rand: Fr::from(4u64), owner_pk: alice_pk };

        let genesis_input_commitment = genesis_input.commitment();
        let alice_commitment = alice_coin.commitment();
        let genesis_slot = 0u64;
        let genesis_append_path = append_path_for_next(&[]);
        let genesis_board_root = compute_root_from_path(Fr::from(0u64), genesis_slot as usize, &genesis_append_path);
        let genesis_own_nullifier = poseidon_hash(&[genesis_input_commitment, fold_owner_scalar(&sk_genesis)]);
        let empty_tree = NullifierTree::new();

        let genesis_outputs = pad_outputs(&[alice_commitment]);
        let genesis_circuit = GenesisSpendCircuit {
            pk_p: Some(pk_genesis),
            output_commitments: Some(genesis_outputs),
            board_root: Some(genesis_board_root),
            current_nullifier_root: Some(empty_tree.root()),
            sk_p: Some(sk_genesis),
            input_coins: [Some(genesis_input)],
            output_coins: [Some(alice_coin.clone()), None],
            entry_position: Some(genesis_slot),
            append_path: Some(genesis_append_path.clone()),
            own_nullifier_nonmembership: [Some(empty_tree.prove_non_membership(genesis_own_nullifier))],
        };
        let (genesis_pk_data, genesis_vk) = cloakkchain_circuit_spend::setup(&mut rng).unwrap();
        let genesis_public_inputs: [Fr; 6] =
            GenesisSpendCircuit::public_inputs(pk_genesis, genesis_outputs, genesis_board_root, empty_tree.root())
                .try_into()
                .unwrap();
        let genesis_proof = cloakkchain_circuit_spend::prove(&genesis_pk_data, genesis_circuit, &mut rng).unwrap();

        let (wrap_genesis_pk, wrap_genesis_vk) =
            cloakkchain_circuit_wrap::setup::<6, _>(genesis_vk, &mut rng).unwrap();
        let wrap_genesis_proof = cloakkchain_circuit_wrap::prove::<6, _>(
            &wrap_genesis_pk,
            cloakkchain_circuit_wrap::WrapCircuit::<6> {
                inner_vk: genesis_pk_data.vk.clone(),
                inner_proof: Some(genesis_proof),
                inner_public_inputs: Some(genesis_public_inputs),
            },
            &mut rng,
        )
        .unwrap();

        let genesis_entry = BoardEntry {
            ciphertext: vec![],
            ek_pk: [0u8; 32],
            key_encs: vec![],
            nullifier: genesis_own_nullifier,
            output_commitments: genesis_outputs.to_vec(),
        };
        let genesis_entry_ciphertext_commitment = entry_ciphertext_commitment(&genesis_entry);
        let alice_receipt_board_root = compute_root_from_path(
            merkle_leaf(genesis_slot as usize, &genesis_entry),
            genesis_slot as usize,
            &genesis_append_path,
        );
        let (apx, apy) = cloakkchain_lib::owner_pk_to_field_pair(&alice_pk);

        let base_circuit = ReceiptStepCircuit {
            owner_pk_x: Some(apx),
            owner_pk_y: Some(apy),
            coin_commitment: Some(alice_commitment),
            board_root: Some(alice_receipt_board_root),
            received_at: Some(genesis_slot),
            wrap_vk: wrap_genesis_vk,
            wrap_proof: Some(wrap_genesis_proof),
            wrap_public_inputs: Some(genesis_public_inputs),
            entry_nullifier: Some(genesis_own_nullifier),
            entry_output_commitments: Some(genesis_outputs),
            entry_ciphertext_commitment: Some(genesis_entry_ciphertext_commitment),
            received_slot: Some(genesis_slot),
            append_path: Some(genesis_append_path),
            parent_nonmembership: Some(empty_tree.prove_non_membership(genesis_own_nullifier)),
            nullifier_root_at_parent_slot: Some(empty_tree.root()),
            sk_p: Some(alice_sk),
            coin_tag: Some(alice_coin.tag),
            coin_value: Some(alice_coin.value),
            coin_rand: Some(alice_coin.rand),
        };

        let cs = ConstraintSystem::<Fr>::new_ref();
        base_circuit.clone().generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap(), "the genuine owner's receipt should satisfy every constraint");

        let mut wrong_key_circuit = base_circuit.clone();
        wrong_key_circuit.sk_p = Some(OwnerScalar::from(999u64)); // not alice_sk
        let cs2 = ConstraintSystem::<Fr>::new_ref();
        wrong_key_circuit.generate_constraints(cs2.clone()).unwrap();
        assert!(!cs2.is_satisfied().unwrap(), "a receipt built with the wrong sk_p must not satisfy the circuit");

        let mut wrong_coin_circuit = base_circuit;
        wrong_coin_circuit.coin_value = Some(999); // doesn't match the coin's real opening
        let cs3 = ConstraintSystem::<Fr>::new_ref();
        wrong_coin_circuit.generate_constraints(cs3.clone()).unwrap();
        assert!(!cs3.is_satisfied().unwrap(), "a receipt claiming the wrong coin opening must not satisfy the circuit");
    }

    /// Full chain exercising both new generalizations at once: genesis
    /// mints to Alice, Alice splits her spend 1-in/2-out (Bob + change —
    /// real multi-output), then Bob receives via a receipt that verifies a
    /// *wrapped spend* proof (not genesis) — the "second generation" that
    /// completes the Bob -> Carol hop — and spends on to Carol.
    /// Nine real Groth16 proofs end to end.
    #[test]
    fn genesis_alice_change_then_bob_to_carol() {
        let mut rng = StdRng::seed_from_u64(20260810);

        // --- Genesis mints 100 to Alice (1-in-1-out) ---
        let sk_genesis = genesis_sk();
        let pk_genesis = derive_owner_pk(&sk_genesis);
        let genesis_input = Coin { tag: Fr::from(1u64), value: 100, rand: Fr::from(2u64), owner_pk: pk_genesis };
        let alice_sk = OwnerScalar::from(42u64);
        let alice_pk = derive_owner_pk(&alice_sk);
        let alice_coin = Coin { tag: Fr::from(3u64), value: 100, rand: Fr::from(4u64), owner_pk: alice_pk };

        let genesis_input_commitment = genesis_input.commitment();
        let alice_commitment = alice_coin.commitment();
        let genesis_slot = 0u64;
        let genesis_append_path = append_path_for_next(&[]);
        let genesis_board_root = compute_root_from_path(Fr::from(0u64), genesis_slot as usize, &genesis_append_path);
        let genesis_own_nullifier = poseidon_hash(&[genesis_input_commitment, fold_owner_scalar(&sk_genesis)]);
        let empty_tree = NullifierTree::new();

        let genesis_outputs = pad_outputs(&[alice_commitment]);
        let genesis_circuit = GenesisSpendCircuit {
            pk_p: Some(pk_genesis),
            output_commitments: Some(genesis_outputs),
            board_root: Some(genesis_board_root),
            current_nullifier_root: Some(empty_tree.root()),
            sk_p: Some(sk_genesis),
            input_coins: [Some(genesis_input)],
            output_coins: [Some(alice_coin.clone()), None],
            entry_position: Some(genesis_slot),
            append_path: Some(genesis_append_path.clone()),
            own_nullifier_nonmembership: [Some(empty_tree.prove_non_membership(genesis_own_nullifier))],
        };
        let (genesis_pk_data, genesis_vk) = cloakkchain_circuit_spend::setup(&mut rng).unwrap();
        let genesis_public_inputs: [Fr; 6] =
            GenesisSpendCircuit::public_inputs(pk_genesis, genesis_outputs, genesis_board_root, empty_tree.root())
                .try_into()
                .unwrap();
        let genesis_proof = cloakkchain_circuit_spend::prove(&genesis_pk_data, genesis_circuit, &mut rng).unwrap();
        assert!(cloakkchain_circuit_spend::verify(&genesis_vk, &genesis_public_inputs, &genesis_proof).unwrap());

        let (wrap_genesis_pk, wrap_genesis_vk) =
            cloakkchain_circuit_wrap::setup::<6, _>(genesis_vk, &mut rng).unwrap();
        let wrap_genesis_proof = cloakkchain_circuit_wrap::prove::<6, _>(
            &wrap_genesis_pk,
            cloakkchain_circuit_wrap::WrapCircuit::<6> {
                inner_vk: genesis_pk_data.vk.clone(),
                inner_proof: Some(genesis_proof),
                inner_public_inputs: Some(genesis_public_inputs),
            },
            &mut rng,
        )
        .unwrap();

        // --- Alice's receipt (genesis-generation) ---
        let genesis_entry = BoardEntry {
            ciphertext: vec![],
            ek_pk: [0u8; 32],
            key_encs: vec![],
            nullifier: genesis_own_nullifier,
            output_commitments: genesis_outputs.to_vec(),
        };
        let genesis_entry_ciphertext_commitment = entry_ciphertext_commitment(&genesis_entry);
        let alice_receipt_board_root = compute_root_from_path(
            merkle_leaf(genesis_slot as usize, &genesis_entry),
            genesis_slot as usize,
            &genesis_append_path,
        );
        let (apx, apy) = cloakkchain_lib::owner_pk_to_field_pair(&alice_pk);
        let alice_receipt_circuit = ReceiptStepCircuit {
            owner_pk_x: Some(apx),
            owner_pk_y: Some(apy),
            coin_commitment: Some(alice_commitment),
            board_root: Some(alice_receipt_board_root),
            received_at: Some(genesis_slot),
            wrap_vk: wrap_genesis_vk.clone(),
            wrap_proof: Some(wrap_genesis_proof),
            wrap_public_inputs: Some(genesis_public_inputs),
            entry_nullifier: Some(genesis_own_nullifier),
            entry_output_commitments: Some(genesis_outputs),
            entry_ciphertext_commitment: Some(genesis_entry_ciphertext_commitment),
            received_slot: Some(genesis_slot),
            append_path: Some(genesis_append_path.clone()),
            parent_nonmembership: Some(empty_tree.prove_non_membership(genesis_own_nullifier)),
            nullifier_root_at_parent_slot: Some(empty_tree.root()),
            sk_p: Some(alice_sk),
            coin_tag: Some(alice_coin.tag),
            coin_value: Some(alice_coin.value),
            coin_rand: Some(alice_coin.rand),
        };
        let (alice_receipt_pk, alice_receipt_vk) = setup(wrap_genesis_vk, &mut rng).unwrap();
        let alice_receipt_public_inputs: [Fr; 5] =
            ReceiptStepCircuit::public_inputs(apx, apy, alice_commitment, alice_receipt_board_root, genesis_slot)
                .try_into()
                .unwrap();
        let alice_receipt_proof = prove(&alice_receipt_pk, alice_receipt_circuit, &mut rng).unwrap();
        assert!(verify(&alice_receipt_vk, &alice_receipt_public_inputs, &alice_receipt_proof).unwrap());

        let (wrap_alice_receipt_pk, wrap_alice_receipt_vk) =
            cloakkchain_circuit_wrap::setup::<5, _>(alice_receipt_vk, &mut rng).unwrap();
        let wrap_alice_receipt_proof = cloakkchain_circuit_wrap::prove::<5, _>(
            &wrap_alice_receipt_pk,
            cloakkchain_circuit_wrap::WrapCircuit::<5> {
                inner_vk: alice_receipt_pk.vk.clone(),
                inner_proof: Some(alice_receipt_proof),
                inner_public_inputs: Some(alice_receipt_public_inputs),
            },
            &mut rng,
        )
        .unwrap();

        // --- Alice spends 1-in-2-out: 40 to Bob, 60 change to herself ---
        let bob_sk = OwnerScalar::from(7u64);
        let bob_pk = derive_owner_pk(&bob_sk);
        let bob_coin = Coin { tag: Fr::from(5u64), value: 40, rand: Fr::from(6u64), owner_pk: bob_pk };
        let change_coin = Coin { tag: Fr::from(7u64), value: 60, rand: Fr::from(8u64), owner_pk: alice_pk };
        let bob_commitment = bob_coin.commitment();
        let change_commitment = change_coin.commitment();

        let alice_spend_slot = 1u64;
        let alice_spend_append_path = append_path_for_next(std::slice::from_ref(&genesis_entry));
        let alice_spend_board_root =
            compute_root_from_path(Fr::from(0u64), alice_spend_slot as usize, &alice_spend_append_path);
        let alice_own_nullifier = poseidon_hash(&[alice_commitment, fold_owner_scalar(&alice_sk)]);
        let mut tree_after_genesis = NullifierTree::new();
        tree_after_genesis.insert(genesis_own_nullifier);

        let alice_spend_outputs = pad_outputs(&[bob_commitment, change_commitment]);
        let alice_spend_circuit = SpendStepCircuit {
            pk_p: Some(alice_pk),
            output_commitments: Some(alice_spend_outputs),
            board_root: Some(alice_spend_board_root),
            current_nullifier_root: Some(tree_after_genesis.root()),
            sk_p: Some(alice_sk),
            input_coins: [Some(alice_coin)],
            output_coins: [Some(bob_coin.clone()), Some(change_coin.clone())],
            entry_position: Some(alice_spend_slot),
            append_path: Some(alice_spend_append_path.clone()),
            own_nullifier_nonmembership: [Some(tree_after_genesis.prove_non_membership(alice_own_nullifier))],
            wrap_vk: wrap_alice_receipt_vk.clone(),
            input_receipt_proofs: [Some(wrap_alice_receipt_proof)],
            input_receipt_public_inputs: [Some(alice_receipt_public_inputs)],
        };
        let (alice_spend_pk, alice_spend_vk) =
            cloakkchain_circuit_spend::setup_non_genesis(wrap_alice_receipt_vk, &mut rng).unwrap();
        let alice_spend_public_inputs =
            SpendStepCircuit::public_inputs(alice_pk, alice_spend_outputs, alice_spend_board_root, tree_after_genesis.root());
        let alice_spend_proof =
            cloakkchain_circuit_spend::prove_non_genesis(&alice_spend_pk, alice_spend_circuit, &mut rng).unwrap();
        assert!(cloakkchain_circuit_spend::verify_non_genesis(
            &alice_spend_vk,
            &alice_spend_public_inputs,
            &alice_spend_proof
        )
        .unwrap());

        let (wrap_alice_spend_pk, wrap_alice_spend_vk) =
            cloakkchain_circuit_wrap::setup::<6, _>(alice_spend_vk, &mut rng).unwrap();
        let alice_spend_public_inputs_arr: [Fr; 6] = alice_spend_public_inputs.clone().try_into().unwrap();
        let wrap_alice_spend_proof = cloakkchain_circuit_wrap::prove::<6, _>(
            &wrap_alice_spend_pk,
            cloakkchain_circuit_wrap::WrapCircuit::<6> {
                inner_vk: alice_spend_pk.vk.clone(),
                inner_proof: Some(alice_spend_proof),
                inner_public_inputs: Some(alice_spend_public_inputs_arr),
            },
            &mut rng,
        )
        .unwrap();

        // --- Bob's receipt: "second generation" — verifies a wrapped
        // *spend* proof (Alice's), not a wrapped genesis proof. Same
        // ReceiptStepCircuit Rust type, just a fresh setup() call keyed to
        // a different wrap_vk — see the module doc comment. ---
        let alice_spend_entry = BoardEntry {
            ciphertext: vec![],
            ek_pk: [0u8; 32],
            key_encs: vec![],
            nullifier: alice_own_nullifier,
            output_commitments: alice_spend_outputs.to_vec(),
        };
        let alice_spend_entry_ciphertext_commitment = entry_ciphertext_commitment(&alice_spend_entry);
        let bob_receipt_board_root = compute_root_from_path(
            merkle_leaf(alice_spend_slot as usize, &alice_spend_entry),
            alice_spend_slot as usize,
            &alice_spend_append_path,
        );
        let (bpx, bpy) = cloakkchain_lib::owner_pk_to_field_pair(&bob_pk);
        let bob_receipt_circuit = ReceiptStepCircuit {
            owner_pk_x: Some(bpx),
            owner_pk_y: Some(bpy),
            coin_commitment: Some(bob_commitment),
            board_root: Some(bob_receipt_board_root),
            received_at: Some(alice_spend_slot),
            wrap_vk: wrap_alice_spend_vk.clone(),
            wrap_proof: Some(wrap_alice_spend_proof),
            wrap_public_inputs: Some(alice_spend_public_inputs_arr),
            entry_nullifier: Some(alice_own_nullifier),
            entry_output_commitments: Some(alice_spend_outputs),
            entry_ciphertext_commitment: Some(alice_spend_entry_ciphertext_commitment),
            received_slot: Some(alice_spend_slot),
            append_path: Some(alice_spend_append_path),
            parent_nonmembership: Some(tree_after_genesis.prove_non_membership(alice_own_nullifier)),
            nullifier_root_at_parent_slot: Some(tree_after_genesis.root()),
            sk_p: Some(bob_sk),
            coin_tag: Some(bob_coin.tag),
            coin_value: Some(bob_coin.value),
            coin_rand: Some(bob_coin.rand),
        };
        let (bob_receipt_pk, bob_receipt_vk) = setup(wrap_alice_spend_vk, &mut rng).unwrap();
        let bob_receipt_public_inputs: [Fr; 5] =
            ReceiptStepCircuit::public_inputs(bpx, bpy, bob_commitment, bob_receipt_board_root, alice_spend_slot)
                .try_into()
                .unwrap();
        let bob_receipt_proof = prove(&bob_receipt_pk, bob_receipt_circuit, &mut rng).unwrap();
        assert!(verify(&bob_receipt_vk, &bob_receipt_public_inputs, &bob_receipt_proof).unwrap());

        let (wrap_bob_receipt_pk, wrap_bob_receipt_vk) =
            cloakkchain_circuit_wrap::setup::<5, _>(bob_receipt_vk, &mut rng).unwrap();
        let wrap_bob_receipt_proof = cloakkchain_circuit_wrap::prove::<5, _>(
            &wrap_bob_receipt_pk,
            cloakkchain_circuit_wrap::WrapCircuit::<5> {
                inner_vk: bob_receipt_pk.vk.clone(),
                inner_proof: Some(bob_receipt_proof),
                inner_public_inputs: Some(bob_receipt_public_inputs),
            },
            &mut rng,
        )
        .unwrap();

        // --- Bob spends his 40 units to Carol (1-in-1-out, "second generation" spend) ---
        let carol_sk = OwnerScalar::from(13u64);
        let carol_pk = derive_owner_pk(&carol_sk);
        let carol_coin = Coin { tag: Fr::from(9u64), value: 40, rand: Fr::from(10u64), owner_pk: carol_pk };
        let carol_commitment = carol_coin.commitment();

        let bob_spend_slot = 2u64;
        let bob_spend_append_path =
            append_path_for_next(&[genesis_entry.clone(), alice_spend_entry.clone()]);
        let bob_spend_board_root =
            compute_root_from_path(Fr::from(0u64), bob_spend_slot as usize, &bob_spend_append_path);
        let bob_own_nullifier = poseidon_hash(&[bob_commitment, fold_owner_scalar(&bob_sk)]);
        let mut tree_after_alice_spend = tree_after_genesis.clone();
        tree_after_alice_spend.insert(alice_own_nullifier);

        let bob_spend_outputs = pad_outputs(&[carol_commitment]);
        let bob_spend_circuit = SpendStepCircuit {
            pk_p: Some(bob_pk),
            output_commitments: Some(bob_spend_outputs),
            board_root: Some(bob_spend_board_root),
            current_nullifier_root: Some(tree_after_alice_spend.root()),
            sk_p: Some(bob_sk),
            input_coins: [Some(bob_coin)],
            output_coins: [Some(carol_coin), None],
            entry_position: Some(bob_spend_slot),
            append_path: Some(bob_spend_append_path),
            own_nullifier_nonmembership: [Some(tree_after_alice_spend.prove_non_membership(bob_own_nullifier))],
            wrap_vk: wrap_bob_receipt_vk.clone(),
            input_receipt_proofs: [Some(wrap_bob_receipt_proof)],
            input_receipt_public_inputs: [Some(bob_receipt_public_inputs)],
        };
        let (bob_spend_pk, bob_spend_vk) =
            cloakkchain_circuit_spend::setup_non_genesis(wrap_bob_receipt_vk, &mut rng).unwrap();
        let bob_spend_public_inputs =
            SpendStepCircuit::public_inputs(bob_pk, bob_spend_outputs, bob_spend_board_root, tree_after_alice_spend.root());
        let bob_spend_proof =
            cloakkchain_circuit_spend::prove_non_genesis(&bob_spend_pk, bob_spend_circuit, &mut rng).unwrap();

        assert!(
            cloakkchain_circuit_spend::verify_non_genesis(&bob_spend_vk, &bob_spend_public_inputs, &bob_spend_proof)
                .unwrap(),
            "the full genesis->Alice(+change)->Bob->Carol chain must verify end to end"
        );

        let mut tampered = bob_spend_public_inputs.clone();
        tampered[2] += Fr::from(1u64);
        assert!(!cloakkchain_circuit_spend::verify_non_genesis(&bob_spend_vk, &tampered, &bob_spend_proof).unwrap());
    }
}
