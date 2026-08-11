//! MNT-native spend circuit. `GenesisSpendCircuit` is the genesis-mint
//! variant of `check_spend` (see `cloakkchain_lib::check_spend`) — no
//! recursive coin-proof verification, since genesis mints never have a
//! parent receipt. `SpendStepCircuit` is the non-genesis variant, which does
//! recursively verify one wrapped `ReceiptStepCircuit` proof *per active
//! input slot* via `Groth16VerifierGadget`.
//!
//! Both support up to [`MAX_INPUTS`] input coins and [`MAX_OUTPUTS`] output
//! coins (slot 0 of each is mandatory; the rest are optional, gated by an
//! explicit `is_active` witness per slot — see the module's padding notes
//! below). This is a genuine generalization beyond `cloakkchain_lib::check_spend`,
//! which only ever tracks *one* input's provenance (`coin_commitment`/
//! `coin_proof`) even though `input_coins: Vec<Coin>` already allowed
//! multiple — a latent gap in the native reference function that would let
//! a spender supply unproven "phantom" extra inputs if naively extended.
//! Every active input slot here gets its own coin-receipt verification, closing
//! that gap rather than reproducing it.
//!
//! **Padding safety**: an inactive slot's `is_active` bit gates its
//! nullifier-non-membership and receipt-verification checks (`check |
//! !is_active`, so a fabricated dummy witness can't fail them) — but *not*
//! its value's contribution to the conservation sum, which is separately
//! zeroed via `is_active.select(value, 0)` regardless of what value the
//! prover actually supplies. Only gating the checks (and not also the
//! value) would let a dishonest prover mark a real-valued slot "inactive"
//! and mint that value into the sum with no nullifier or receipt backing it.

use ark_crypto_primitives::snark::{constraints::SNARKGadget, BooleanInputVar};
use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar, poseidon::constraints::PoseidonSpongeVar,
};
use ark_ec::{CurveGroup, PrimeGroup};
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
use cloakkchain_lib::{
    genesis_pk, owner_pk_to_field_pair, poseidon_params, Coin, Fr, NonMembershipWitness, OwnerPk,
    OwnerScalar, TREE_DEPTH,
};

type Fp = FpVar<Fr>;
type G1Var = ark_mnt6_753::constraints::G1Var;
type MNT6PairingVar = ark_mnt6_753::constraints::PairingVar;

/// Up to this many real input coins per spend (slot 0 mandatory, the rest
/// optional — see the module doc comment for the padding scheme).
pub const MAX_INPUTS: usize = 2;
/// Up to this many real output coins per spend.
pub const MAX_OUTPUTS: usize = 2;

/// `ReceiptStepCircuit`'s public-input count/order (mirrors
/// `circuit_coinproof::ReceiptStepCircuit::public_inputs`, duplicated as a
/// plain constant rather than a crate dependency, to avoid a
/// circuit-spend <-> circuit-coinproof cycle — both sides must keep this in
/// sync by construction, not by the type system).
const RECEIPT_PUBLIC_INPUT_COUNT: usize = 5;
const RECEIPT_OWNER_PK_X: usize = 0;
const RECEIPT_OWNER_PK_Y: usize = 1;
const RECEIPT_COIN_COMMITMENT: usize = 2;

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

    /// `w` is `None` for an unused (padding) input slot — allocates a dummy
    /// (all-zero) leaf in that case, safe because padding slots' checks are
    /// gated by `is_active` (see the module doc comment).
    fn new_witness(cs: ConstraintSystemRef<Fr>, w: &Option<NonMembershipWitness>) -> Result<Self, SynthesisError> {
        Ok(Self {
            value: Fp::new_witness(cs.clone(), || Ok(w.as_ref().map(|w| w.low_leaf.value).unwrap_or(Fr::from(0u64))))?,
            next_value: Fp::new_witness(cs.clone(), || {
                Ok(w.as_ref().map(|w| w.low_leaf.next_value).unwrap_or(Fr::from(0u64)))
            })?,
            next_index: Fp::new_witness(cs.clone(), || {
                Ok(w.as_ref().map(|w| Fr::from(w.low_leaf.next_index)).unwrap_or(Fr::from(0u64)))
            })?,
        })
    }
}

/// `w` is `None` for an unused (padding) input slot — see
/// `IndexedLeafVar::new_witness`'s doc comment.
fn alloc_low_leaf_index_bits(cs: ConstraintSystemRef<Fr>, w: &Option<NonMembershipWitness>) -> Result<Vec<Boolean<Fr>>, SynthesisError> {
    let low_leaf_index_fp =
        Fp::new_witness(cs.clone(), || Ok(w.as_ref().map(|w| Fr::from(w.low_leaf_index)).unwrap_or(Fr::from(0u64))))?;
    low_leaf_index_fp.to_bits_le()
}

/// `w` is `None` for an unused (padding) input slot — see
/// `IndexedLeafVar::new_witness`'s doc comment.
fn alloc_sibling_path(cs: ConstraintSystemRef<Fr>, w: &Option<NonMembershipWitness>, len: usize) -> Result<Vec<Fp>, SynthesisError> {
    (0..len)
        .map(|i| {
            Fp::new_witness(cs.clone(), || {
                Ok(w.as_ref().map(|w| w.sibling_path[i]).unwrap_or(Fr::from(0u64)))
            })
        })
        .collect()
}

/// Mirrors `cloakkchain_lib::verify_nonmembership`, returning the boolean
/// result rather than enforcing it — callers combine it with an `is_active`
/// gate (see the module doc comment) before enforcing.
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
    /// `coin` is `None` for an unused (padding) slot — allocates a
    /// self-consistent dummy (`value = 0`, everything else `0`) in that
    /// case. Safe regardless of what checks end up gated on `is_active`,
    /// since the value-conservation sum separately zeroes a padding slot's
    /// contribution via `is_active.select` (see [`CoinVar::value_or_zero`]),
    /// not by trusting this dummy's `value` field.
    fn new_witness(cs: ConstraintSystemRef<Fr>, coin: &Option<Coin>) -> Result<Self, SynthesisError> {
        let owner_xy = coin.as_ref().map(|c| owner_pk_to_field_pair(&c.owner_pk));
        Ok(Self {
            tag: Fp::new_witness(cs.clone(), || Ok(coin.as_ref().map(|c| c.tag).unwrap_or(Fr::from(0u64))))?,
            value: UInt64::new_witness(cs.clone(), || Ok(coin.as_ref().map(|c| c.value).unwrap_or(0)))?,
            rand: Fp::new_witness(cs.clone(), || Ok(coin.as_ref().map(|c| c.rand).unwrap_or(Fr::from(0u64))))?,
            owner_pk_x: Fp::new_witness(cs.clone(), || Ok(owner_xy.map(|(x, _)| x).unwrap_or(Fr::from(0u64))))?,
            owner_pk_y: Fp::new_witness(cs.clone(), || Ok(owner_xy.map(|(_, y)| y).unwrap_or(Fr::from(0u64))))?,
        })
    }

    fn commitment(&self, cs: ConstraintSystemRef<Fr>) -> Result<Fp, SynthesisError> {
        let value_fp = self.value.to_fp()?;
        poseidon_hash_var(
            cs,
            &[self.tag.clone(), value_fp, self.rand.clone(), self.owner_pk_x.clone(), self.owner_pk_y.clone()],
        )
    }

    /// This slot's value if `is_active`, else `0` — used for the
    /// conservation sum. Deliberately does *not* trust the witnessed
    /// `value` field alone for inactive slots (see the module doc comment).
    fn value_or_zero(&self, is_active: &Boolean<Fr>) -> Result<Fp, SynthesisError> {
        Fp::conditionally_select(is_active, &self.value.to_fp()?, &Fp::zero())
    }
}

fn alloc_fp_vec(cs: ConstraintSystemRef<Fr>, values: &Option<Vec<Fr>>, len: usize) -> Result<Vec<Fp>, SynthesisError> {
    (0..len)
        .map(|i| Fp::new_witness(cs.clone(), || opt(&values.as_ref().map(|v| v[i]))))
        .collect()
}

/// `active[0]` is always `Boolean::TRUE` (every spend has at least one input
/// and one output) — only slots `1..N` need a witnessed flag.
fn alloc_active_flags<const N: usize>(
    cs: ConstraintSystemRef<Fr>,
    present: &[bool; N],
) -> Result<[Boolean<Fr>; N], SynthesisError> {
    let mut out: [Boolean<Fr>; N] = std::array::from_fn(|_| Boolean::TRUE);
    for i in 1..N {
        out[i] = Boolean::new_witness(cs.clone(), || Ok(present[i]))?;
    }
    Ok(out)
}

/// `check | !is_active` — an inactive slot's check is vacuously satisfied
/// regardless of witness content (see the module doc comment).
fn gate(check: Boolean<Fr>, is_active: &Boolean<Fr>) -> Boolean<Fr> {
    &check | &!is_active.clone()
}

/// The genesis-mint variant of the spend relation (`check_spend` with
/// `is_genesis = true`, no coin-proof recursion — genesis's own inputs are
/// always trusted by construction, never receipt-checked). Public values
/// (allocated first, in this exact order — matches [`public_inputs`]):
/// `pk_p.x, pk_p.y, output_commitments[0..MAX_OUTPUTS], board_root,
/// current_nullifier_root`.
#[derive(Clone, Default, CanonicalSerialize, CanonicalDeserialize)]
pub struct GenesisSpendCircuit {
    // Public values.
    pub pk_p: Option<OwnerPk>,
    pub output_commitments: Option<[Fr; MAX_OUTPUTS]>,
    pub board_root: Option<Fr>,
    pub current_nullifier_root: Option<Fr>,

    // Private witnesses.
    pub sk_p: Option<OwnerScalar>,
    /// Slot 0 must be `Some`; slots `1..MAX_INPUTS` are optional (padding).
    pub input_coins: [Option<Coin>; MAX_INPUTS],
    /// Slot 0 must be `Some`; slots `1..MAX_OUTPUTS` are optional (padding).
    pub output_coins: [Option<Coin>; MAX_OUTPUTS],
    pub entry_position: Option<u64>,
    /// Length `TREE_DEPTH`.
    pub append_path: Option<Vec<Fr>>,
    /// One non-membership witness per input slot (padding slots still need
    /// *some* witness — see the module doc comment for why it's safe to be
    /// unconstrained there).
    pub own_nullifier_nonmembership: [Option<NonMembershipWitness>; MAX_INPUTS],
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
        let output_commitments: Vec<Fp> = (0..MAX_OUTPUTS)
            .map(|i| Fp::new_input(cs.clone(), || opt(&self.output_commitments.map(|a| a[i]))))
            .collect::<Result<_, _>>()?;
        let board_root = Fp::new_input(cs.clone(), || opt(&self.board_root))?;
        let current_nullifier_root = Fp::new_input(cs.clone(), || opt(&self.current_nullifier_root))?;

        // --- sk_p / pk_p ---
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

        let generator = G1Var::new_constant(cs.clone(), ark_mnt6_753::G1Projective::generator())?;
        let pk_p_computed = generator.scalar_mul_le(sk_bits.iter())?.to_affine()?;
        pk_p_computed.x.enforce_equal(&pk_p_x)?;
        pk_p_computed.y.enforce_equal(&pk_p_y)?;

        // --- genesis: pk_p must be the fixed, well-known genesis key ---
        let (genesis_x, genesis_y) = owner_pk_to_field_pair(&genesis_pk());
        pk_p_x.enforce_equal(&Fp::constant(genesis_x))?;
        pk_p_y.enforce_equal(&Fp::constant(genesis_y))?;

        let sk_folded = fold_bits_le_var(cs.clone(), &sk_bits)?;

        // --- board_root = compute_root_from_path(0, entry_position, append_path) ---
        let entry_position_fp = Fp::new_witness(cs.clone(), || opt(&self.entry_position.map(Fr::from)))?;
        let entry_position_bits = entry_position_fp.to_bits_le()?;
        let append_path = alloc_fp_vec(cs.clone(), &self.append_path, TREE_DEPTH)?;
        let board_root_computed =
            compute_root_from_path_var(cs.clone(), &Fp::zero(), &entry_position_bits[..TREE_DEPTH], &append_path)?;
        board_root_computed.enforce_equal(&board_root)?;

        // --- input slots: owner is the spender, nullifier absent (genesis:
        // no receipt needed — all inputs are trusted by construction) ---
        let input_present: [bool; MAX_INPUTS] = std::array::from_fn(|i| self.input_coins[i].is_some());
        let input_active = alloc_active_flags(cs.clone(), &input_present)?;
        let mut total_in = Fp::zero();
        for i in 0..MAX_INPUTS {
            let coin = CoinVar::new_witness(cs.clone(), &self.input_coins[i])?;
            let owner_ok = &coin.owner_pk_x.is_eq(&pk_p_x)? & &coin.owner_pk_y.is_eq(&pk_p_y)?;
            gate(owner_ok, &input_active[i]).enforce_equal(&Boolean::TRUE)?;

            let commitment = coin.commitment(cs.clone())?;
            let own_nullifier = poseidon_hash_var(cs.clone(), &[commitment, sk_folded.clone()])?;
            let low_leaf = IndexedLeafVar::new_witness(cs.clone(), &self.own_nullifier_nonmembership[i])?;
            let w = &self.own_nullifier_nonmembership[i];
            let low_leaf_index_bits = alloc_low_leaf_index_bits(cs.clone(), w)?;
            let sibling_path = alloc_sibling_path(cs.clone(), w, TREE_DEPTH)?;
            let nonmembership_ok = verify_nonmembership_var(
                cs.clone(),
                &current_nullifier_root,
                &own_nullifier,
                &low_leaf,
                &low_leaf_index_bits[..TREE_DEPTH],
                &sibling_path,
            )?;
            gate(nonmembership_ok, &input_active[i]).enforce_equal(&Boolean::TRUE)?;

            total_in += coin.value_or_zero(&input_active[i])?;
        }

        // --- output slots: commitment matches the public list ---
        let output_present: [bool; MAX_OUTPUTS] = std::array::from_fn(|i| self.output_coins[i].is_some());
        let output_active = alloc_active_flags(cs.clone(), &output_present)?;
        let mut total_out = Fp::zero();
        for j in 0..MAX_OUTPUTS {
            let coin = CoinVar::new_witness(cs.clone(), &self.output_coins[j])?;
            let commitment_ok = coin.commitment(cs.clone())?.is_eq(&output_commitments[j])?;
            gate(commitment_ok, &output_active[j]).enforce_equal(&Boolean::TRUE)?;
            total_out += coin.value_or_zero(&output_active[j])?;
        }

        // --- value conservation: Σ active inputs == Σ active outputs ---
        total_in.enforce_equal(&total_out)?;

        Ok(())
    }
}

impl GenesisSpendCircuit {
    /// Build the Groth16 public-input vector for this circuit's public
    /// values, in the exact order `generate_constraints` allocates them.
    pub fn public_inputs(
        pk_p: OwnerPk,
        output_commitments: [Fr; MAX_OUTPUTS],
        board_root: Fr,
        current_nullifier_root: Fr,
    ) -> Vec<Fr> {
        let (x, y) = owner_pk_to_field_pair(&pk_p);
        let mut out = vec![x, y];
        out.extend_from_slice(&output_commitments);
        out.push(board_root);
        out.push(current_nullifier_root);
        out
    }
}

/// Total public-input count for [`GenesisSpendCircuit`]/[`SpendStepCircuit`]
/// (both share the same layout) — `2 (pk) + MAX_OUTPUTS + 2 (board_root,
/// nullifier_root)`.
pub const SPEND_PUBLIC_INPUT_COUNT: usize = 2 + MAX_OUTPUTS + 2;

/// The non-genesis variant of the spend relation (`check_spend` with
/// `is_genesis = false`): everything `GenesisSpendCircuit` checks, minus the
/// fixed-genesis-key constraint, plus a recursive verification of one
/// wrapped parent coin-receipt proof (`circuit_coinproof::ReceiptStepCircuit`,
/// wrapped via `circuit-wrap`) *per active input slot* — mirrors (and
/// generalizes, see the module doc comment) `check_spend`'s
/// `coin_proof.owner_pk == pk_p` / `coin_proof.coin_commitment ==
/// coin_commitment` checks, except the receipt's claims are now backed by
/// an actual verified proof rather than a plain witness.
///
/// Currently fixed to recursively verify wrapped `ReceiptStepCircuit`
/// proofs from one specific deployment (all active input slots share the
/// same `wrap_vk` — mixing receipt "generations" within one spend isn't
/// supported) — see `circuit_coinproof`'s module doc comment for why.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SpendStepCircuit {
    // Public values (same layout as `GenesisSpendCircuit`).
    pub pk_p: Option<OwnerPk>,
    pub output_commitments: Option<[Fr; MAX_OUTPUTS]>,
    pub board_root: Option<Fr>,
    pub current_nullifier_root: Option<Fr>,

    // Private witnesses (same shape as `GenesisSpendCircuit`).
    pub sk_p: Option<OwnerScalar>,
    pub input_coins: [Option<Coin>; MAX_INPUTS],
    pub output_coins: [Option<Coin>; MAX_OUTPUTS],
    pub entry_position: Option<u64>,
    /// Length `TREE_DEPTH`.
    pub append_path: Option<Vec<Fr>>,
    pub own_nullifier_nonmembership: [Option<NonMembershipWitness>; MAX_INPUTS],

    // Private witnesses: one wrapped parent coin-receipt proof per active
    // input slot (a Wrap<5> proof over `ReceiptStepCircuit`'s public inputs).
    /// Fixed per deployment — not `Option`, a verifying key isn't secret.
    pub wrap_vk: VerifyingKey<MNT6_753>,
    /// `None` for a padding slot (still needs *a* structurally-valid dummy
    /// proof — see `circuit-wrap::setup`'s doc comment for why — supplied
    /// automatically by [`SpendStepCircuit::pad_input`]).
    pub input_receipt_proofs: [Option<Proof<MNT6_753>>; MAX_INPUTS],
    pub input_receipt_public_inputs: [Option<[Fr; RECEIPT_PUBLIC_INPUT_COUNT]>; MAX_INPUTS],
}

impl SpendStepCircuit {
    /// A structurally-valid (not necessarily verifying) filler for an
    /// unused input slot's receipt proof — never checked when `is_active`
    /// is false (see the module doc comment).
    /// Deliberately *not* the point at infinity: unlike `circuit-wrap`'s and
    /// `circuit-coinproof`'s own `setup()` dummy proofs (which only ever run
    /// in Groth16 setup mode, where witness values are never numerically
    /// checked), this one is also used as the real witness for an *inactive*
    /// input slot during actual proving — the pairing gadget's internal
    /// (Miller-loop) arithmetic isn't guaranteed well-defined at infinity
    /// even though the gated `recursive_ok` is allowed to end up `false`,
    /// so use the group generator instead: non-degenerate, and still
    /// obviously not a valid proof for anything.
    fn dummy_wrap_proof() -> Proof<MNT6_753> {
        Proof {
            a: ark_mnt6_753::G1Projective::generator().into_affine(),
            b: ark_mnt6_753::G2Projective::generator().into_affine(),
            c: ark_mnt6_753::G1Projective::generator().into_affine(),
        }
    }
}

impl ConstraintSynthesizer<Fr> for SpendStepCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        // --- public inputs ---
        let (pk_x_native, pk_y_native) = match &self.pk_p {
            Some(pk) => {
                let (x, y) = owner_pk_to_field_pair(pk);
                (Some(x), Some(y))
            }
            None => (None, None),
        };
        let pk_p_x = Fp::new_input(cs.clone(), || opt(&pk_x_native))?;
        let pk_p_y = Fp::new_input(cs.clone(), || opt(&pk_y_native))?;
        let output_commitments: Vec<Fp> = (0..MAX_OUTPUTS)
            .map(|i| Fp::new_input(cs.clone(), || opt(&self.output_commitments.map(|a| a[i]))))
            .collect::<Result<_, _>>()?;
        let board_root = Fp::new_input(cs.clone(), || opt(&self.board_root))?;
        let current_nullifier_root = Fp::new_input(cs.clone(), || opt(&self.current_nullifier_root))?;

        // --- sk_p / pk_p ---
        let sk_bit_values: Option<Vec<bool>> = self.sk_p.map(|sk| sk.into_bigint().to_bits_le());
        let sk_bit_len = OwnerScalar::MODULUS_BIT_SIZE as usize;
        let sk_bits: Vec<Boolean<Fr>> = (0..sk_bit_len)
            .map(|i| Boolean::new_witness(cs.clone(), || opt(&sk_bit_values.as_ref().map(|b| b[i]))))
            .collect::<Result<_, _>>()?;
        let mut modulus_minus_one = OwnerScalar::MODULUS.0.to_vec();
        modulus_minus_one[0] -= 1;
        Boolean::enforce_smaller_or_equal_than_le(&sk_bits, modulus_minus_one)?;

        let generator = G1Var::new_constant(cs.clone(), ark_mnt6_753::G1Projective::generator())?;
        let pk_p_computed = generator.scalar_mul_le(sk_bits.iter())?.to_affine()?;
        pk_p_computed.x.enforce_equal(&pk_p_x)?;
        pk_p_computed.y.enforce_equal(&pk_p_y)?;

        let sk_folded = fold_bits_le_var(cs.clone(), &sk_bits)?;

        // --- board_root = compute_root_from_path(0, entry_position, append_path) ---
        let entry_position_fp = Fp::new_witness(cs.clone(), || opt(&self.entry_position.map(Fr::from)))?;
        let entry_position_bits = entry_position_fp.to_bits_le()?;
        let append_path = alloc_fp_vec(cs.clone(), &self.append_path, TREE_DEPTH)?;
        let board_root_computed =
            compute_root_from_path_var(cs.clone(), &Fp::zero(), &entry_position_bits[..TREE_DEPTH], &append_path)?;
        board_root_computed.enforce_equal(&board_root)?;

        // --- wrap VK (shared by every active input slot's receipt) ---
        let wrap_vk_var = VerifyingKeyVar::<MNT6_753, MNT6PairingVar>::new_constant(cs.clone(), &self.wrap_vk)?;
        let pvk = wrap_vk_var.prepare()?;
        let wrap_bit_len = Fr6::MODULUS_BIT_SIZE as usize;
        let wrap_public_len = RECEIPT_PUBLIC_INPUT_COUNT * chunks_per_value();
        let cpv = chunks_per_value();

        // --- input slots ---
        let input_present: [bool; MAX_INPUTS] = std::array::from_fn(|i| self.input_coins[i].is_some());
        let input_active = alloc_active_flags(cs.clone(), &input_present)?;
        let mut total_in = Fp::zero();
        for i in 0..MAX_INPUTS {
            let coin = CoinVar::new_witness(cs.clone(), &self.input_coins[i])?;
            let owner_ok = &coin.owner_pk_x.is_eq(&pk_p_x)? & &coin.owner_pk_y.is_eq(&pk_p_y)?;
            gate(owner_ok, &input_active[i]).enforce_equal(&Boolean::TRUE)?;

            let commitment = coin.commitment(cs.clone())?;
            let own_nullifier = poseidon_hash_var(cs.clone(), &[commitment.clone(), sk_folded.clone()])?;
            let low_leaf = IndexedLeafVar::new_witness(cs.clone(), &self.own_nullifier_nonmembership[i])?;
            let w = &self.own_nullifier_nonmembership[i];
            let low_leaf_index_bits = alloc_low_leaf_index_bits(cs.clone(), w)?;
            let sibling_path = alloc_sibling_path(cs.clone(), w, TREE_DEPTH)?;
            let nonmembership_ok = verify_nonmembership_var(
                cs.clone(),
                &current_nullifier_root,
                &own_nullifier,
                &low_leaf,
                &low_leaf_index_bits[..TREE_DEPTH],
                &sibling_path,
            )?;
            gate(nonmembership_ok, &input_active[i]).enforce_equal(&Boolean::TRUE)?;

            // --- this slot's coin-receipt: recursively verify the wrapped
            // receipt proof, then bind its claims to this input ---
            // A padding slot has no real receipt — fall back to all-zero
            // chunks (never checked, since `recursive_ok` below is gated by
            // `is_active`; see the module doc comment).
            let receipt_native = &self.input_receipt_public_inputs[i];
            let wrap_native_chunks: Vec<Fr6> = receipt_native
                .as_ref()
                .map(|v| public_input_chunks(v))
                .unwrap_or_else(|| vec![Fr6::from(0u64); wrap_public_len]);
            let mut per_chunk_bits: Vec<Vec<Boolean<Fr>>> = Vec::with_capacity(wrap_public_len);
            for k in 0..wrap_public_len {
                let value_bits: Vec<bool> = wrap_native_chunks[k].into_bigint().to_bits_le();
                let bits: Vec<Boolean<Fr>> = (0..wrap_bit_len)
                    .map(|j| Boolean::new_witness(cs.clone(), || Ok(value_bits[j])))
                    .collect::<Result<_, _>>()?;
                per_chunk_bits.push(bits);
            }
            let input_var = BooleanInputVar::<Fr6, Fr>::new(per_chunk_bits.clone());
            let proof_native = self.input_receipt_proofs[i].clone().unwrap_or_else(Self::dummy_wrap_proof);
            let proof_var = ProofVar::<MNT6_753, MNT6PairingVar>::new_witness(cs.clone(), || Ok(proof_native))?;
            let recursive_ok = Groth16VerifierGadget::<MNT6_753, MNT6PairingVar>::verify_with_processed_vk(
                &pvk,
                &input_var,
                &proof_var,
            )?;
            gate(recursive_ok, &input_active[i]).enforce_equal(&Boolean::TRUE)?;

            let group = |idx: usize| -> &[Vec<Boolean<Fr>>] { &per_chunk_bits[idx * cpv..(idx + 1) * cpv] };
            let receipt_owner_pk_x = combine_chunks_var(group(RECEIPT_OWNER_PK_X))?;
            let receipt_owner_pk_y = combine_chunks_var(group(RECEIPT_OWNER_PK_Y))?;
            let receipt_coin_commitment = combine_chunks_var(group(RECEIPT_COIN_COMMITMENT))?;
            let binding_ok = &(&receipt_owner_pk_x.is_eq(&pk_p_x)? & &receipt_owner_pk_y.is_eq(&pk_p_y)?)
                & &receipt_coin_commitment.is_eq(&commitment)?;
            gate(binding_ok, &input_active[i]).enforce_equal(&Boolean::TRUE)?;

            total_in += coin.value_or_zero(&input_active[i])?;
        }

        // --- output slots ---
        let output_present: [bool; MAX_OUTPUTS] = std::array::from_fn(|i| self.output_coins[i].is_some());
        let output_active = alloc_active_flags(cs.clone(), &output_present)?;
        let mut total_out = Fp::zero();
        for j in 0..MAX_OUTPUTS {
            let coin = CoinVar::new_witness(cs.clone(), &self.output_coins[j])?;
            let commitment_ok = coin.commitment(cs.clone())?.is_eq(&output_commitments[j])?;
            gate(commitment_ok, &output_active[j]).enforce_equal(&Boolean::TRUE)?;
            total_out += coin.value_or_zero(&output_active[j])?;
        }

        // --- value conservation ---
        total_in.enforce_equal(&total_out)?;

        Ok(())
    }
}

impl SpendStepCircuit {
    /// Build the Groth16 public-input vector for this circuit's public
    /// values — same layout as `GenesisSpendCircuit::public_inputs`.
    pub fn public_inputs(
        pk_p: OwnerPk,
        output_commitments: [Fr; MAX_OUTPUTS],
        board_root: Fr,
        current_nullifier_root: Fr,
    ) -> Vec<Fr> {
        GenesisSpendCircuit::public_inputs(pk_p, output_commitments, board_root, current_nullifier_root)
    }
}

pub fn setup_non_genesis<R: RngCore + CryptoRng>(
    wrap_vk: VerifyingKey<MNT6_753>,
    rng: &mut R,
) -> Result<(ProvingKey<MNT4_753>, VerifyingKey<MNT4_753>), SynthesisError> {
    let circuit = SpendStepCircuit {
        pk_p: None,
        output_commitments: None,
        board_root: None,
        current_nullifier_root: None,
        sk_p: None,
        input_coins: std::array::from_fn(|_| None),
        output_coins: std::array::from_fn(|_| None),
        entry_position: None,
        append_path: None,
        own_nullifier_nonmembership: std::array::from_fn(|_| None),
        wrap_vk,
        // See circuit-wrap's `setup` for why every slot needs *some*
        // structurally-valid dummy proof rather than `None` — `ProofVar`'s
        // `AllocVar` impl calls its value closure unconditionally.
        input_receipt_proofs: std::array::from_fn(|_| Some(SpendStepCircuit::dummy_wrap_proof())),
        input_receipt_public_inputs: std::array::from_fn(|_| None),
    };
    Groth16::<MNT4_753>::circuit_specific_setup(circuit, rng)
}

pub fn prove_non_genesis<R: RngCore + CryptoRng>(
    pk: &ProvingKey<MNT4_753>,
    circuit: SpendStepCircuit,
    rng: &mut R,
) -> Result<Proof<MNT4_753>, SynthesisError> {
    Groth16::<MNT4_753>::prove(pk, circuit, rng)
}

pub fn verify_non_genesis(
    vk: &VerifyingKey<MNT4_753>,
    public_inputs: &[Fr],
    proof: &Proof<MNT4_753>,
) -> Result<bool, SynthesisError> {
    Groth16::<MNT4_753>::verify(vk, public_inputs, proof)
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

    /// Build a valid genesis-mint witness (1 real input, 1 real output,
    /// padding slots empty) the same way the native `check_spend`/test
    /// helpers in `cloakkchain_lib` would: real board state (empty,
    /// first-ever entry), real nullifier-tree state (empty), real Poseidon
    /// commitments.
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
            output_commitments: Some([output_commitment, Fr::from(0u64)]),
            board_root: Some(board_root),
            current_nullifier_root: Some(current_nullifier_root),
            sk_p: Some(sk_p),
            input_coins: [Some(input_coin), None],
            output_coins: [Some(output_coin), None],
            entry_position: Some(entry_position),
            append_path: Some(append_path),
            own_nullifier_nonmembership: [Some(own_nullifier_nonmembership), None],
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
    fn two_real_outputs_with_conservation_satisfies_constraints() {
        let sk_p = genesis_sk();
        let pk_p = derive_owner_pk(&sk_p);
        let input_coin = Coin { tag: Fr::from(1u64), value: 100, rand: Fr::from(2u64), owner_pk: pk_p };
        let bob_pk = derive_owner_pk(&OwnerScalar::from(7u64));
        let bob_coin = Coin { tag: Fr::from(3u64), value: 40, rand: Fr::from(4u64), owner_pk: bob_pk };
        let change_pk = pk_p;
        let change_coin = Coin { tag: Fr::from(5u64), value: 60, rand: Fr::from(6u64), owner_pk: change_pk };

        let coin_commitment = input_coin.commitment();
        let entry_position = 0u64;
        let append_path = append_path_for_next(&[]);
        let own_nullifier = poseidon_hash(&[coin_commitment, fold_owner_scalar(&sk_p)]);
        let tree = NullifierTree::new();
        let board_root = cloakkchain_lib::compute_root_from_path(Fr::from(0u64), entry_position as usize, &append_path);

        let c = GenesisSpendCircuit {
            pk_p: Some(pk_p),
            output_commitments: Some([bob_coin.commitment(), change_coin.commitment()]),
            board_root: Some(board_root),
            current_nullifier_root: Some(tree.root()),
            sk_p: Some(sk_p),
            input_coins: [Some(input_coin), None],
            output_coins: [Some(bob_coin), Some(change_coin)],
            entry_position: Some(entry_position),
            append_path: Some(append_path),
            own_nullifier_nonmembership: [Some(tree.prove_non_membership(own_nullifier)), None],
        };
        let cs = ConstraintSystem::<Fr>::new_ref();
        c.generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap(), "1-in-2-out with correct conservation should satisfy every constraint");
    }

    #[test]
    fn marking_a_real_valued_slot_inactive_cannot_mint_value() {
        // A dishonest prover sets is_active=false for a slot that still
        // carries a nonzero value, hoping the value silently counts toward
        // the sum without any nullifier/receipt backing it. This must fail
        // — `value_or_zero` zeroes an inactive slot's contribution
        // regardless of the witnessed `value` field.
        let sk_p = genesis_sk();
        let pk_p = derive_owner_pk(&sk_p);
        let input_coin = Coin { tag: Fr::from(1u64), value: 100, rand: Fr::from(2u64), owner_pk: pk_p };
        let output_coin = Coin { tag: Fr::from(3u64), value: 100, rand: Fr::from(4u64), owner_pk: pk_p };
        // A "free" phantom second output worth 50, but left officially
        // inactive (output_present[1] derived from output_coins[1].is_some()
        // — so mark it None while still trying to have it contribute value
        // is impossible via the public struct; the attack this test checks
        // is the *value_or_zero* mechanism itself, exercised directly).
        let phantom = CoinVar {
            tag: Fp::constant(Fr::from(9u64)),
            value: UInt64::constant(50),
            rand: Fp::constant(Fr::from(9u64)),
            owner_pk_x: Fp::constant(Fr::from(0u64)),
            owner_pk_y: Fp::constant(Fr::from(0u64)),
        };
        let cs = ConstraintSystem::<Fr>::new_ref();
        let contribution = phantom.value_or_zero(&Boolean::constant(false)).unwrap();
        contribution.enforce_equal(&Fp::constant(Fr::from(0u64))).unwrap();
        assert!(cs.is_satisfied().unwrap(), "inactive slot's value must be forced to zero");
        let _ = (input_coin, output_coin);
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
            c.output_commitments.unwrap(),
            c.board_root.unwrap(),
            c.current_nullifier_root.unwrap(),
        );

        let proof = prove(&pk, c, &mut rng).unwrap();
        assert!(verify(&vk, &public_inputs, &proof).unwrap(), "a genuinely valid genesis-mint proof must verify");

        let mut tampered = public_inputs.clone();
        tampered[2] += Fr::from(1u64); // perturb output_commitments[0]
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
        let input_commitment = c.input_coins[0].as_ref().unwrap().commitment();
        let own_nullifier = poseidon_hash(&[input_commitment, fold_owner_scalar(&sk_p)]);
        let mut tree = NullifierTree::new();
        tree.insert(own_nullifier);
        c.current_nullifier_root = Some(tree.root());
        c.own_nullifier_nonmembership = [Some(tree.prove_non_membership(own_nullifier)), None];
        c.generate_constraints(cs.clone()).unwrap();
        assert!(!cs.is_satisfied().unwrap(), "a nullifier already in the accumulator must fail non-membership");
    }
}
