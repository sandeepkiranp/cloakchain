//! MNT-native spend circuit. `GenesisSpendCircuit` is the genesis-mint
//! variant of `check_spend` (see `cloakkchain_lib::check_spend`) — no
//! recursive coin-proof verification, since genesis mints never have a
//! parent receipt. The non-genesis variant (which does recursively verify a
//! `CoinReceiptCircuit` proof via `Groth16VerifierGadget`) is Phase 3.
//!
//! Fixed to exactly one input coin and one output coin for now (matches the
//! real genesis mint in the demo chain) — variable-length input/output lists
//! are a mechanical extension (padding + a count witness) once this core
//! shape is validated, not a new mechanism.

use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar, poseidon::constraints::PoseidonSpongeVar,
};
use ark_ec::PrimeGroup;
use ark_ff::{BigInteger, PrimeField};
use ark_groth16::{Groth16, Proof, ProvingKey, VerifyingKey};
use ark_mnt4_753::MNT4_753;
use ark_r1cs_std::{cmp::CmpGadget, fields::fp::FpVar, prelude::*};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_snark::SNARK;
use ark_std::rand::{CryptoRng, RngCore};
use cloakkchain_lib::{
    genesis_pk, owner_pk_to_field_pair, poseidon_params, Coin, Fr, NonMembershipWitness, OwnerPk,
    OwnerScalar, TREE_DEPTH,
};

type Fp = FpVar<Fr>;
type G1Var = ark_mnt6_753::constraints::G1Var;

// ---- gadget helpers (mirror cloakkchain_lib's native functions exactly) --

fn poseidon_hash_var(cs: ConstraintSystemRef<Fr>, inputs: &[Fp]) -> Result<Fp, SynthesisError> {
    let mut sponge = PoseidonSpongeVar::new(cs, &poseidon_params::mnt4_753_fr_poseidon_config());
    sponge.absorb(&inputs.to_vec())?;
    Ok(sponge.squeeze_field_elements(1)?.remove(0))
}

/// Mirrors `cloakkchain_lib::fold_bits_le` — chunk a little-endian bit vector
/// into 248-bit pieces and Poseidon-hash the resulting field elements.
fn fold_bits_le_var(cs: ConstraintSystemRef<Fr>, bits: &[Boolean<Fr>]) -> Result<Fp, SynthesisError> {
    let chunks: Vec<Fp> = bits
        .chunks(248)
        .map(Boolean::le_bits_to_fp)
        .collect::<Result<_, _>>()?;
    poseidon_hash_var(cs, &chunks)
}

fn merkle_combine_var(cs: ConstraintSystemRef<Fr>, l: &Fp, r: &Fp) -> Result<Fp, SynthesisError> {
    poseidon_hash_var(cs, &[l.clone(), r.clone()])
}

/// Mirrors `cloakkchain_lib::compute_root_from_path`, except the slot index
/// is a *witnessed* bit vector (not a compile-time constant) — the circuit
/// shape is fixed, so left/right selection at each level must be a
/// conditional-select gadget on the position's bits, not a Rust `if`.
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

/// `a < b` over `Fr`'s canonical integer representative. `ark-r1cs-std`
/// doesn't implement `CmpGadget` for `FpVar` directly (only for `UInt*` and
/// `Boolean`/slices-of-`CmpGadget`) — reuse its slice-lexicographic
/// comparator on the canonical (unique) big-endian bit decomposition, which
/// is exactly numeric comparison once the bits are MSB-first.
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

/// Mirrors `cloakkchain_lib::verify_nonmembership`.
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

/// A coin as circuit variables — `owner_pk` kept as a plain coordinate pair
/// (not a `G1Var`) since this circuit never does group arithmetic on a
/// coin's owner key, only equality-compares and hashes it; a bare `FpVar`
/// pair avoids needing on-curve verification that isn't otherwise required
/// (see the module's design notes in the MNT-native port plan).
struct CoinVar {
    tag: Fp,
    value: UInt64<Fr>,
    rand: Fp,
    owner_pk_x: Fp,
    owner_pk_y: Fp,
}

impl CoinVar {
    fn new_witness(cs: ConstraintSystemRef<Fr>, coin: &Option<Coin>) -> Result<Self, SynthesisError> {
        let owner_xy = coin.as_ref().map(|c| owner_pk_to_field_pair(&c.owner_pk));
        Ok(Self {
            tag: Fp::new_witness(cs.clone(), || opt(&coin.as_ref().map(|c| c.tag)))?,
            value: UInt64::new_witness(cs.clone(), || opt(&coin.as_ref().map(|c| c.value)))?,
            rand: Fp::new_witness(cs.clone(), || opt(&coin.as_ref().map(|c| c.rand)))?,
            owner_pk_x: Fp::new_witness(cs.clone(), || opt(&owner_xy.map(|(x, _)| x)))?,
            owner_pk_y: Fp::new_witness(cs.clone(), || opt(&owner_xy.map(|(_, y)| y)))?,
        })
    }

    fn commitment(&self, cs: ConstraintSystemRef<Fr>) -> Result<Fp, SynthesisError> {
        let value_fp = self.value.to_fp()?;
        poseidon_hash_var(
            cs,
            &[self.tag.clone(), value_fp, self.rand.clone(), self.owner_pk_x.clone(), self.owner_pk_y.clone()],
        )
    }
}

fn alloc_fp_vec(cs: ConstraintSystemRef<Fr>, values: &Option<Vec<Fr>>, len: usize) -> Result<Vec<Fp>, SynthesisError> {
    (0..len)
        .map(|i| Fp::new_witness(cs.clone(), || opt(&values.as_ref().map(|v| v[i]))))
        .collect()
}

/// The genesis-mint variant of the spend relation (`check_spend` with
/// `is_genesis = true`, no coin-proof recursion). Public values (allocated
/// first, in this exact order — matches [`public_inputs`]): `pk_p.x,
/// pk_p.y, coin_commitment, board_root, output_commitment,
/// current_nullifier_root`.
#[derive(Clone, Default)]
pub struct GenesisSpendCircuit {
    // Public values.
    pub pk_p: Option<OwnerPk>,
    pub coin_commitment: Option<Fr>,
    pub board_root: Option<Fr>,
    pub output_commitment: Option<Fr>,
    pub current_nullifier_root: Option<Fr>,

    // Private witnesses.
    pub sk_p: Option<OwnerScalar>,
    pub input_coin: Option<Coin>,
    pub output_coin: Option<Coin>,
    pub entry_position: Option<u64>,
    /// Length `TREE_DEPTH`.
    pub append_path: Option<Vec<Fr>>,
    pub own_nullifier_nonmembership: Option<NonMembershipWitness>,
}

impl ConstraintSynthesizer<Fr> for GenesisSpendCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        // --- public inputs, in the fixed order `public_inputs` matches ---
        let (pk_x_native, pk_y_native) = match &self.pk_p {
            Some(pk) => {
                let (x, y) = owner_pk_to_field_pair(pk);
                (Some(x), Some(y))
            }
            None => (None, None),
        };
        let pk_p_x = Fp::new_input(cs.clone(), || opt(&pk_x_native))?;
        let pk_p_y = Fp::new_input(cs.clone(), || opt(&pk_y_native))?;
        let coin_commitment = Fp::new_input(cs.clone(), || opt(&self.coin_commitment))?;
        let board_root = Fp::new_input(cs.clone(), || opt(&self.board_root))?;
        let output_commitment = Fp::new_input(cs.clone(), || opt(&self.output_commitment))?;
        let current_nullifier_root = Fp::new_input(cs.clone(), || opt(&self.current_nullifier_root))?;

        // --- private witnesses ---
        let sk_bit_values: Option<Vec<bool>> = self.sk_p.map(|sk| sk.into_bigint().to_bits_le());
        let sk_bit_len = OwnerScalar::MODULUS_BIT_SIZE as usize;
        let sk_bits: Vec<Boolean<Fr>> = (0..sk_bit_len)
            .map(|i| Boolean::new_witness(cs.clone(), || opt(&sk_bit_values.as_ref().map(|b| b[i]))))
            .collect::<Result<_, _>>()?;
        // Canonicity: sk_bits, as an integer, must be < OwnerScalar's modulus
        // — otherwise two different bit patterns could represent the same
        // group element (same pk_p) but fold to two different nullifiers,
        // letting the same coin be spent twice under different nullifiers.
        let mut modulus_minus_one = OwnerScalar::MODULUS.0.to_vec();
        modulus_minus_one[0] -= 1; // odd prime modulus, so this can't borrow
        Boolean::enforce_smaller_or_equal_than_le(&sk_bits, modulus_minus_one)?;

        let input_coin = CoinVar::new_witness(cs.clone(), &self.input_coin)?;
        let output_coin = CoinVar::new_witness(cs.clone(), &self.output_coin)?;

        let entry_position_fp = Fp::new_witness(cs.clone(), || {
            opt(&self.entry_position.map(Fr::from))
        })?;
        let entry_position_bits = entry_position_fp.to_bits_le()?;
        let append_path = alloc_fp_vec(cs.clone(), &self.append_path, TREE_DEPTH)?;

        let w = &self.own_nullifier_nonmembership;
        let low_leaf = IndexedLeafVar {
            value: Fp::new_witness(cs.clone(), || opt(&w.as_ref().map(|w| w.low_leaf.value)))?,
            next_value: Fp::new_witness(cs.clone(), || opt(&w.as_ref().map(|w| w.low_leaf.next_value)))?,
            next_index: Fp::new_witness(cs.clone(), || opt(&w.as_ref().map(|w| Fr::from(w.low_leaf.next_index))))?,
        };
        let low_leaf_index_fp = Fp::new_witness(cs.clone(), || opt(&w.as_ref().map(|w| Fr::from(w.low_leaf_index))))?;
        let low_leaf_index_bits = low_leaf_index_fp.to_bits_le()?;
        let sibling_path = alloc_fp_vec(cs.clone(), &w.as_ref().map(|w| w.sibling_path.clone()), TREE_DEPTH)?;

        // --- pk_p = sk_p * G (native scalar mult on MNT6-753's G1 — see the
        // `OwnerPk`/`OwnerScalar` doc comments in cloakkchain_lib) ---
        let generator = G1Var::new_constant(cs.clone(), ark_mnt6_753::G1Projective::generator())?;
        let pk_p_computed = generator.scalar_mul_le(sk_bits.iter())?.to_affine()?;
        pk_p_computed.x.enforce_equal(&pk_p_x)?;
        pk_p_computed.y.enforce_equal(&pk_p_y)?;

        // --- genesis: pk_p must be the fixed, well-known genesis key ---
        let (genesis_x, genesis_y) = owner_pk_to_field_pair(&genesis_pk());
        pk_p_x.enforce_equal(&Fp::constant(genesis_x))?;
        pk_p_y.enforce_equal(&Fp::constant(genesis_y))?;

        // --- board_root = compute_root_from_path(0, entry_position, append_path) ---
        let board_root_computed =
            compute_root_from_path_var(cs.clone(), &Fp::zero(), &entry_position_bits[..TREE_DEPTH], &append_path)?;
        board_root_computed.enforce_equal(&board_root)?;

        // --- own_nullifier = Poseidon(coin_commitment, fold(sk_p bits)) ---
        let sk_folded = fold_bits_le_var(cs.clone(), &sk_bits)?;
        let own_nullifier = poseidon_hash_var(cs.clone(), &[coin_commitment.clone(), sk_folded])?;

        // --- double-spend guard: own_nullifier absent from the accumulator ---
        let nonmembership_ok = verify_nonmembership_var(
            cs.clone(),
            &current_nullifier_root,
            &own_nullifier,
            &low_leaf,
            &low_leaf_index_bits[..TREE_DEPTH],
            &sibling_path,
        )?;
        nonmembership_ok.enforce_equal(&Boolean::TRUE)?;

        // --- input coin: commitment matches, owner is the spender ---
        input_coin.commitment(cs.clone())?.enforce_equal(&coin_commitment)?;
        input_coin.owner_pk_x.enforce_equal(&pk_p_x)?;
        input_coin.owner_pk_y.enforce_equal(&pk_p_y)?;

        // --- output coin: commitment matches the public output_commitment ---
        output_coin.commitment(cs.clone())?.enforce_equal(&output_commitment)?;

        // --- value conservation: single input, single output, so this is
        // a direct equality (a real sum only matters once MAX_INPUTS/
        // MAX_OUTPUTS > 1 — see the module doc comment) ---
        input_coin.value.enforce_equal(&output_coin.value)?;

        Ok(())
    }
}

impl GenesisSpendCircuit {
    /// Build the Groth16 public-input vector for this circuit's public
    /// values, in the exact order `generate_constraints` allocates them.
    pub fn public_inputs(
        pk_p: OwnerPk,
        coin_commitment: Fr,
        board_root: Fr,
        output_commitment: Fr,
        current_nullifier_root: Fr,
    ) -> Vec<Fr> {
        let (x, y) = owner_pk_to_field_pair(&pk_p);
        vec![x, y, coin_commitment, board_root, output_commitment, current_nullifier_root]
    }
}

pub fn setup<R: RngCore + CryptoRng>(
    rng: &mut R,
) -> Result<(ProvingKey<MNT4_753>, VerifyingKey<MNT4_753>), SynthesisError> {
    Groth16::<MNT4_753>::circuit_specific_setup(GenesisSpendCircuit::default(), rng)
}

pub fn prove<R: RngCore + CryptoRng>(
    pk: &ProvingKey<MNT4_753>,
    circuit: GenesisSpendCircuit,
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
    use ark_relations::r1cs::ConstraintSystem;
    use cloakkchain_lib::{append_path_for_next, derive_owner_pk, fold_owner_scalar, genesis_sk, poseidon_hash, NullifierTree};

    /// Build a valid genesis-mint witness the same way the native
    /// `check_spend`/test helpers in `cloakkchain_lib` would: real board
    /// state (empty, first-ever entry), real nullifier-tree state (empty),
    /// real Poseidon commitments — the circuit's constraints are checked
    /// against exactly the values the native functions produce.
    fn valid_circuit() -> GenesisSpendCircuit {
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

        let own_nullifier = poseidon_hash(&[coin_commitment, fold_owner_scalar(&sk_p)]);
        let tree = NullifierTree::new(); // empty accumulator — first-ever spend
        let current_nullifier_root = tree.root();
        let own_nullifier_nonmembership = tree.prove_non_membership(own_nullifier);

        let board_root = cloakkchain_lib::compute_root_from_path(Fr::from(0u64), entry_position as usize, &append_path);

        GenesisSpendCircuit {
            pk_p: Some(pk_p),
            coin_commitment: Some(coin_commitment),
            board_root: Some(board_root),
            output_commitment: Some(output_commitment),
            current_nullifier_root: Some(current_nullifier_root),
            sk_p: Some(sk_p),
            input_coin: Some(input_coin),
            output_coin: Some(output_coin),
            entry_position: Some(entry_position),
            append_path: Some(append_path),
            own_nullifier_nonmembership: Some(own_nullifier_nonmembership),
        }
    }

    #[test]
    fn valid_genesis_witness_satisfies_constraints() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        valid_circuit().generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap(), "valid genesis witness should satisfy every constraint");
        println!("constraint count: {}", cs.num_constraints());
    }

    #[test]
    fn wrong_output_value_violates_conservation() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut c = valid_circuit();
        let mut output_coin = c.output_coin.unwrap();
        output_coin.value = 99; // was 100 — breaks conservation
        c.output_commitment = Some(output_coin.commitment());
        c.output_coin = Some(output_coin);
        c.generate_constraints(cs.clone()).unwrap();
        assert!(!cs.is_satisfied().unwrap(), "mismatched input/output value must not satisfy the circuit");
    }

    #[test]
    fn wrong_secret_key_fails() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut c = valid_circuit();
        c.sk_p = Some(OwnerScalar::from(2u64)); // not genesis_sk()
        c.generate_constraints(cs.clone()).unwrap();
        assert!(!cs.is_satisfied().unwrap(), "wrong sk_p must not satisfy the circuit");
    }

    #[test]
    fn full_groth16_round_trip() {
        // `ark_std::test_rng()` is deterministic but deliberately doesn't
        // implement `CryptoRng` (it's not a CSPRNG) — `Groth16::setup`/
        // `prove` require `CryptoRng`, so use a seeded `StdRng` instead.
        use ark_std::rand::{rngs::StdRng, SeedableRng};
        let mut rng = StdRng::seed_from_u64(42);
        let (pk, vk) = setup(&mut rng).unwrap();

        let c = valid_circuit();
        let public_inputs = GenesisSpendCircuit::public_inputs(
            c.pk_p.unwrap(),
            c.coin_commitment.unwrap(),
            c.board_root.unwrap(),
            c.output_commitment.unwrap(),
            c.current_nullifier_root.unwrap(),
        );

        let proof = prove(&pk, c, &mut rng).unwrap();
        assert!(verify(&vk, &public_inputs, &proof).unwrap(), "a genuinely valid genesis-mint proof must verify");

        let mut tampered = public_inputs.clone();
        tampered[2] += Fr::from(1u64); // perturb coin_commitment
        assert!(!verify(&vk, &tampered, &proof).unwrap(), "a proof must not verify against the wrong public inputs");
    }

    #[test]
    fn already_spent_nullifier_fails() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut c = valid_circuit();
        // Insert this exact coin's nullifier into the accumulator first —
        // simulating "already spent" — then reuse the (now-stale) witness
        // against the new root: the non-membership check must fail.
        let sk_p = genesis_sk();
        let own_nullifier = poseidon_hash(&[c.coin_commitment.unwrap(), fold_owner_scalar(&sk_p)]);
        let mut tree = NullifierTree::new();
        tree.insert(own_nullifier);
        c.current_nullifier_root = Some(tree.root());
        c.own_nullifier_nonmembership = Some(tree.prove_non_membership(own_nullifier));
        c.generate_constraints(cs.clone()).unwrap();
        assert!(!cs.is_satisfied().unwrap(), "a nullifier already in the accumulator must fail non-membership");
    }
}
