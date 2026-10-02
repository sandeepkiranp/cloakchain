//! MNT-native spend circuit. `GenesisSpendCircuit` is the genesis-mint
//! variant of `check_spend` (see `cloakkchain_lib::check_spend`) — no
//! recursive parent verification, since genesis mints never have a parent
//! spend. `SpendStepCircuit` is the non-genesis variant, which does
//! recursively verify one wrapped parent `GenesisSpendCircuit`/
//! `SpendStepCircuit` proof *per active input slot* via `GM17VerifierGadget`,
//! directly — no separate receipt-proof layer.
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
use ark_gm17::{
    constraints::{GM17VerifierGadget, ProofVar, VerifyingKeyVar},
    GM17, Proof, ProvingKey, VerifyingKey,
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
///
/// Temporarily reduced to 1 (from 2) to measure/reduce spend-step proving
/// cost — each input slot needs its own full recursive `GM17VerifierGadget`
/// verification (~250-300K constraints), by far the dominant cost driver.
/// Revisit raising this back to 2+ if/when multi-input spends are needed;
/// nothing else about the padding/`is_active` design changes with `N`.
pub const MAX_INPUTS: usize = 1;
/// Up to this many real output coins per spend.
pub const MAX_OUTPUTS: usize = 2;

/// Index, within a recursively-verified parent spend proof's public-input
/// chunk groups, of each value — mirrors `GenesisSpendCircuit::public_inputs`'/
/// `SpendStepCircuit::public_inputs`'s own fixed order:
/// `output_commitments[0..MAX_OUTPUTS], board_root, current_nullifier_root`.
const PARENT_OUTPUT_COMMITMENTS_START: usize = 0;
const PARENT_BOARD_ROOT: usize = MAX_OUTPUTS;
const PARENT_NULLIFIER_ROOT: usize = MAX_OUTPUTS + 1;

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
            value: UInt64::new_witness(cs.clone(), || Ok(coin.as_ref().map(|c| c.value).unwrap_or(0)))?,
            rand: Fp::new_witness(cs.clone(), || Ok(coin.as_ref().map(|c| c.rand).unwrap_or(Fr::from(0u64))))?,
            owner_pk_x: Fp::new_witness(cs.clone(), || Ok(owner_xy.map(|(x, _)| x).unwrap_or(Fr::from(0u64))))?,
            owner_pk_y: Fp::new_witness(cs.clone(), || Ok(owner_xy.map(|(_, y)| y).unwrap_or(Fr::from(0u64))))?,
        })
    }

    fn commitment(&self, cs: ConstraintSystemRef<Fr>) -> Result<Fp, SynthesisError> {
        let value_fp = self.value.to_fp()?;
        poseidon_hash_var(cs, &[value_fp, self.rand.clone(), self.owner_pk_x.clone(), self.owner_pk_y.clone()])
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

/// `target` is a member of `list` — an OR of per-slot equality checks. Used
/// to identify which of an origin entry's (up to `MAX_OUTPUTS`) output
/// commitments is this input coin's own commitment.
fn is_member(target: &Fp, list: &[Fp]) -> Result<Boolean<Fr>, SynthesisError> {
    let mut any = Boolean::FALSE;
    for item in list {
        any = &any | &target.is_eq(item)?;
    }
    Ok(any)
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
        // --- pk_p is a private witness, not a public input: nothing
        // downstream ever needs to read it back out of a genesis/spend
        // proof (the receipt circuit's provenance check only pulls
        // `output_commitments`), and its own uses here — the ownership
        // check against the input coin, and (for genesis specifically) the
        // fixed-authority check — work identically whether it's public or
        // private, since both are equality checks against values already
        // available inside this circuit. Keeping it private is a pure
        // privacy win (an outside observer of a standalone proof can no
        // longer see who minted/spent) with no loss of soundness anywhere.
        let (pk_x_native, pk_y_native) = match &self.pk_p {
            Some(pk) => {
                let (x, y) = owner_pk_to_field_pair(pk);
                (Some(x), Some(y))
            }
            None => (None, None),
        };
        let pk_p_x = Fp::new_witness(cs.clone(), || opt(&pk_x_native))?;
        let pk_p_y = Fp::new_witness(cs.clone(), || opt(&pk_y_native))?;

        // --- public inputs, in the fixed order `public_inputs` matches ---
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
    /// Build the GM17 public-input vector for this circuit's public
    /// values, in the exact order `generate_constraints` allocates them.
    pub fn public_inputs(
        output_commitments: [Fr; MAX_OUTPUTS],
        board_root: Fr,
        current_nullifier_root: Fr,
    ) -> Vec<Fr> {
        let mut out = output_commitments.to_vec();
        out.push(board_root);
        out.push(current_nullifier_root);
        out
    }
}

/// Total public-input count for [`GenesisSpendCircuit`]/[`SpendStepCircuit`]
/// (both share the same layout) — `MAX_OUTPUTS + 2 (board_root,
/// nullifier_root)`. `pk_p` is a private witness, not part of this vector —
/// see the `pk_p` allocation in each circuit's `generate_constraints` for why.
pub const SPEND_PUBLIC_INPUT_COUNT: usize = MAX_OUTPUTS + 2;

/// The non-genesis variant of the spend relation (`check_spend` with
/// `is_genesis = false`): everything `GenesisSpendCircuit` checks, plus, per
/// active input slot:
///
/// - a Merkle inclusion proof that the board entry which created this input
///   coin (the "origin entry") is genuinely included in the tree at THIS
///   spend's own, real, public `board_root` — not a self-chosen root (see
///   the module doc comment's board_root/nullifier_root discussion);
/// - a recursive verification of the parent spend proof that created this
///   input coin, directly (`GenesisSpendCircuit`/`SpendStepCircuit`, wrapped
///   via `circuit-wrap` — no separate receipt-proof layer);
/// - a binding check bridging the two: the roots embedded in the origin
///   entry's leaf (as they stood immediately before it was posted), and its
///   output commitments, must equal the parent proof's own recursively
///   verified public `board_root`/`current_nullifier_root`/
///   `output_commitments`. Since the inclusion check ties the origin leaf to
///   the real, checkable `board_root`, and the binding check reuses that
///   same leaf data against the parent's own public claims, a fabricated
///   origin can't be laundered one hop and then dropped — it forces the next
///   hop's own public `board_root` to be fake too, visible to whoever
///   receives it.
///
/// Currently fixed to recursively verify wrapped parent-spend proofs from
/// one specific deployment (all active input slots share the same
/// `wrap_vk` — mixing parents of different "generations"/shapes within one
/// spend isn't supported; this is the same deferred arbitrary-depth
/// VK-selection limitation as before, just relocated here).
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

    // Private witnesses: one wrapped parent spend proof per active input
    // slot — the proof that created this input coin (a
    // Wrap<SPEND_PUBLIC_INPUT_COUNT> proof over `GenesisSpendCircuit`'s/
    // `SpendStepCircuit`'s own public layout).
    /// Fixed per deployment — not `Option`, a verifying key isn't secret.
    pub wrap_vk: VerifyingKey<MNT6_753>,
    /// `None` for a padding slot (still needs *a* structurally-valid dummy
    /// proof — see `circuit-wrap::setup`'s doc comment for why).
    pub input_parent_proofs: [Option<Proof<MNT6_753>>; MAX_INPUTS],
    pub input_parent_public_inputs: [Option<[Fr; SPEND_PUBLIC_INPUT_COUNT]>; MAX_INPUTS],

    // Private witnesses: the origin entry (the board entry that created this
    // input coin) and the roots that stood immediately before it — see the
    // struct doc comment. `origin_append_path[i]` has length `TREE_DEPTH`.
    pub origin_received_slot: [Option<u64>; MAX_INPUTS],
    pub origin_entry_nullifier: [Option<Fr>; MAX_INPUTS],
    pub origin_entry_output_commitments: [Option<[Fr; MAX_OUTPUTS]>; MAX_INPUTS],
    pub origin_entry_ciphertext_commitment: [Option<Fr>; MAX_INPUTS],
    pub origin_append_path: [Option<Vec<Fr>>; MAX_INPUTS],
    pub origin_prev_board_root: [Option<Fr>; MAX_INPUTS],
    pub origin_prev_nullifier_root: [Option<Fr>; MAX_INPUTS],
}

impl SpendStepCircuit {
    /// A structurally-valid (not necessarily verifying) filler for an
    /// unused input slot's receipt proof — never checked when `is_active`
    /// is false (see the module doc comment).
    /// Deliberately *not* the point at infinity: unlike `circuit-wrap`'s and
    /// `circuit-coinproof`'s own `setup()` dummy proofs (which only ever run
    /// in GM17 setup mode, where witness values are never numerically
    /// checked), this one is also used as the real witness for an *inactive*
    /// input slot during actual proving — the pairing gadget's internal
    /// (Miller-loop) arithmetic isn't guaranteed well-defined at infinity
    /// even though the gated `recursive_ok` is allowed to end up `false`,
    /// so use the group generator instead: non-degenerate, and still
    /// obviously not a valid proof for anything.
    pub fn dummy_wrap_proof() -> Proof<MNT6_753> {
        Proof {
            a: ark_mnt6_753::G1Projective::generator().into_affine(),
            b: ark_mnt6_753::G2Projective::generator().into_affine(),
            c: ark_mnt6_753::G1Projective::generator().into_affine(),
        }
    }
}

impl ConstraintSynthesizer<Fr> for SpendStepCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        // --- pk_p is a private witness — see GenesisSpendCircuit's matching
        // comment for why nothing is lost by not publishing it.
        let (pk_x_native, pk_y_native) = match &self.pk_p {
            Some(pk) => {
                let (x, y) = owner_pk_to_field_pair(pk);
                (Some(x), Some(y))
            }
            None => (None, None),
        };
        let pk_p_x = Fp::new_witness(cs.clone(), || opt(&pk_x_native))?;
        let pk_p_y = Fp::new_witness(cs.clone(), || opt(&pk_y_native))?;

        // --- public inputs ---
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

        // --- wrap VK (shared by every active input slot's parent proof) ---
        let wrap_vk_var = VerifyingKeyVar::<MNT6_753, MNT6PairingVar>::new_constant(cs.clone(), &self.wrap_vk)?;
        let pvk = wrap_vk_var.prepare()?;
        let wrap_bit_len = Fr6::MODULUS_BIT_SIZE as usize;
        let parent_public_len = SPEND_PUBLIC_INPUT_COUNT * chunks_per_value();
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

            // --- origin entry: the board entry that created this input
            // coin, proven included against THIS spend's own, real,
            // currently-public `board_root` ("root A") — not a self-chosen
            // one. See the struct doc comment.
            let origin_nullifier = Fp::new_witness(cs.clone(), || opt(&self.origin_entry_nullifier[i]))?;
            let origin_output_commitments: Vec<Fp> = (0..MAX_OUTPUTS)
                .map(|j| {
                    Fp::new_witness(cs.clone(), || {
                        opt(&self.origin_entry_output_commitments[i].map(|a| a[j]))
                    })
                })
                .collect::<Result<_, _>>()?;
            let origin_ciphertext_commitment =
                Fp::new_witness(cs.clone(), || opt(&self.origin_entry_ciphertext_commitment[i]))?;
            let origin_slot_fp =
                Fp::new_witness(cs.clone(), || opt(&self.origin_received_slot[i].map(Fr::from)))?;
            let origin_slot_bits = origin_slot_fp.to_bits_le()?;
            let origin_append_path = alloc_fp_vec(cs.clone(), &self.origin_append_path[i], TREE_DEPTH)?;
            let origin_prev_board_root = Fp::new_witness(cs.clone(), || opt(&self.origin_prev_board_root[i]))?;
            let origin_prev_nullifier_root =
                Fp::new_witness(cs.clone(), || opt(&self.origin_prev_nullifier_root[i]))?;

            let origin_output_commitments_hash = poseidon_hash_var(cs.clone(), &origin_output_commitments)?;
            let origin_leaf = poseidon_hash_var(
                cs.clone(),
                &[
                    origin_slot_fp,
                    origin_ciphertext_commitment,
                    origin_nullifier,
                    origin_output_commitments_hash,
                    origin_prev_board_root.clone(),
                    origin_prev_nullifier_root.clone(),
                ],
            )?;
            let origin_root_computed = compute_root_from_path_var(
                cs.clone(),
                &origin_leaf,
                &origin_slot_bits[..TREE_DEPTH],
                &origin_append_path,
            )?;
            gate(origin_root_computed.is_eq(&board_root)?, &input_active[i]).enforce_equal(&Boolean::TRUE)?;

            // coin_commitment must be among the origin entry's own output
            // commitments — identifies which of (up to MAX_OUTPUTS) outputs
            // is this input coin.
            gate(is_member(&commitment, &origin_output_commitments)?, &input_active[i])
                .enforce_equal(&Boolean::TRUE)?;

            // --- recursively verify the parent spend proof that created
            // this input coin, directly (no separate receipt-proof layer).
            // A padding slot has no real parent — fall back to all-zero
            // chunks (never checked, since every check below is gated by
            // `is_active`; see the module doc comment).
            let parent_native = &self.input_parent_public_inputs[i];
            let parent_chunks: Vec<Fr6> = parent_native
                .as_ref()
                .map(|v| public_input_chunks(v))
                .unwrap_or_else(|| vec![Fr6::from(0u64); parent_public_len]);
            let mut parent_per_chunk_bits: Vec<Vec<Boolean<Fr>>> = Vec::with_capacity(parent_public_len);
            for k in 0..parent_public_len {
                let value_bits: Vec<bool> = parent_chunks[k].into_bigint().to_bits_le();
                let bits: Vec<Boolean<Fr>> = (0..wrap_bit_len)
                    .map(|j| Boolean::new_witness(cs.clone(), || Ok(value_bits[j])))
                    .collect::<Result<_, _>>()?;
                parent_per_chunk_bits.push(bits);
            }
            let parent_input_var = BooleanInputVar::<Fr6, Fr>::new(parent_per_chunk_bits.clone());
            let parent_proof_native = self.input_parent_proofs[i].clone().unwrap_or_else(Self::dummy_wrap_proof);
            let parent_proof_var =
                ProofVar::<MNT6_753, MNT6PairingVar>::new_witness(cs.clone(), || Ok(parent_proof_native))?;
            let parent_recursive_ok = GM17VerifierGadget::<MNT6_753, MNT6PairingVar>::verify_with_processed_vk(
                &pvk,
                &parent_input_var,
                &parent_proof_var,
            )?;
            gate(parent_recursive_ok, &input_active[i]).enforce_equal(&Boolean::TRUE)?;

            // --- binding: the core fix. The roots (and output commitments)
            // embedded in the origin leaf must equal the parent proof's own,
            // recursively verified, public claims — not a separately
            // witnessed, self-chosen copy. See the struct doc comment for
            // why this is what stops a fabricated origin from being
            // laundered past this hop.
            let pgroup = |idx: usize| -> &[Vec<Boolean<Fr>>] { &parent_per_chunk_bits[idx * cpv..(idx + 1) * cpv] };
            let parent_output_commitments: Vec<Fp> = (0..MAX_OUTPUTS)
                .map(|j| combine_chunks_var(pgroup(PARENT_OUTPUT_COMMITMENTS_START + j)))
                .collect::<Result<_, _>>()?;
            let parent_board_root = combine_chunks_var(pgroup(PARENT_BOARD_ROOT))?;
            let parent_nullifier_root = combine_chunks_var(pgroup(PARENT_NULLIFIER_ROOT))?;

            for j in 0..MAX_OUTPUTS {
                gate(origin_output_commitments[j].is_eq(&parent_output_commitments[j])?, &input_active[i])
                    .enforce_equal(&Boolean::TRUE)?;
            }
            gate(origin_prev_board_root.is_eq(&parent_board_root)?, &input_active[i])
                .enforce_equal(&Boolean::TRUE)?;
            gate(origin_prev_nullifier_root.is_eq(&parent_nullifier_root)?, &input_active[i])
                .enforce_equal(&Boolean::TRUE)?;

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
    /// Build the GM17 public-input vector for this circuit's public
    /// values — same layout as `GenesisSpendCircuit::public_inputs`.
    pub fn public_inputs(
        output_commitments: [Fr; MAX_OUTPUTS],
        board_root: Fr,
        current_nullifier_root: Fr,
    ) -> Vec<Fr> {
        GenesisSpendCircuit::public_inputs(output_commitments, board_root, current_nullifier_root)
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
        input_parent_proofs: std::array::from_fn(|_| Some(SpendStepCircuit::dummy_wrap_proof())),
        input_parent_public_inputs: std::array::from_fn(|_| None),
        origin_received_slot: std::array::from_fn(|_| None),
        origin_entry_nullifier: std::array::from_fn(|_| None),
        origin_entry_output_commitments: std::array::from_fn(|_| None),
        origin_entry_ciphertext_commitment: std::array::from_fn(|_| None),
        origin_append_path: std::array::from_fn(|_| None),
        origin_prev_board_root: std::array::from_fn(|_| None),
        origin_prev_nullifier_root: std::array::from_fn(|_| None),
    };
    GM17::<MNT4_753>::circuit_specific_setup(circuit, rng)
}

pub fn prove_non_genesis<R: RngCore + CryptoRng>(
    pk: &ProvingKey<MNT4_753>,
    circuit: SpendStepCircuit,
    rng: &mut R,
) -> Result<Proof<MNT4_753>, SynthesisError> {
    GM17::<MNT4_753>::prove(pk, circuit, rng)
}

pub fn verify_non_genesis(
    vk: &VerifyingKey<MNT4_753>,
    public_inputs: &[Fr],
    proof: &Proof<MNT4_753>,
) -> Result<bool, SynthesisError> {
    GM17::<MNT4_753>::verify(vk, public_inputs, proof)
}

pub fn setup<R: RngCore + CryptoRng>(
    rng: &mut R,
) -> Result<(ProvingKey<MNT4_753>, VerifyingKey<MNT4_753>), SynthesisError> {
    GM17::<MNT4_753>::circuit_specific_setup(GenesisSpendCircuit::default(), rng)
}

pub fn prove<R: RngCore + CryptoRng>(
    pk: &ProvingKey<MNT4_753>,
    circuit: GenesisSpendCircuit,
    rng: &mut R,
) -> Result<Proof<MNT4_753>, SynthesisError> {
    GM17::<MNT4_753>::prove(pk, circuit, rng)
}

pub fn verify(
    vk: &VerifyingKey<MNT4_753>,
    public_inputs: &[Fr],
    proof: &Proof<MNT4_753>,
) -> Result<bool, SynthesisError> {
    GM17::<MNT4_753>::verify(vk, public_inputs, proof)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_relations::r1cs::ConstraintSystem;
    use cloakkchain_lib::{
        append_path_for_next, compute_root_from_path, derive_owner_pk, empty_root, entry_ciphertext_commitment,
        fold_owner_scalar, genesis_sk, poseidon_hash, BoardEntry, NullifierTree,
    };

    /// Build a valid genesis-mint witness (1 real input, 1 real output,
    /// padding slots empty) the same way the native `check_spend`/test
    /// helpers in `cloakkchain_lib` would: real board state (empty,
    /// first-ever entry), real nullifier-tree state (empty), real Poseidon
    /// commitments.
    fn valid_circuit() -> GenesisSpendCircuit {
        let sk_p = genesis_sk();
        let pk_p = derive_owner_pk(&sk_p);

        let input_coin = Coin { value: 100, rand: Fr::from(2u64), owner_pk: pk_p };
        let recipient_sk = OwnerScalar::from(42u64);
        let recipient_pk = derive_owner_pk(&recipient_sk);
        let output_coin = Coin { value: 100, rand: Fr::from(4u64), owner_pk: recipient_pk };

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
            input_coins: [Some(input_coin)],
            output_coins: [Some(output_coin), None],
            entry_position: Some(entry_position),
            append_path: Some(append_path),
            own_nullifier_nonmembership: [Some(own_nullifier_nonmembership)],
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
        let input_coin = Coin { value: 100, rand: Fr::from(2u64), owner_pk: pk_p };
        let bob_pk = derive_owner_pk(&OwnerScalar::from(7u64));
        let bob_coin = Coin { value: 40, rand: Fr::from(4u64), owner_pk: bob_pk };
        let change_pk = pk_p;
        let change_coin = Coin { value: 60, rand: Fr::from(6u64), owner_pk: change_pk };

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
            input_coins: [Some(input_coin)],
            output_coins: [Some(bob_coin), Some(change_coin)],
            entry_position: Some(entry_position),
            append_path: Some(append_path),
            own_nullifier_nonmembership: [Some(tree.prove_non_membership(own_nullifier))],
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
        let input_coin = Coin { value: 100, rand: Fr::from(2u64), owner_pk: pk_p };
        let output_coin = Coin { value: 100, rand: Fr::from(4u64), owner_pk: pk_p };
        // A "free" phantom second output worth 50, but left officially
        // inactive (output_present[1] derived from output_coins[1].is_some()
        // — so mark it None while still trying to have it contribute value
        // is impossible via the public struct; the attack this test checks
        // is the *value_or_zero* mechanism itself, exercised directly).
        let phantom = CoinVar {
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
    fn full_gm17_round_trip() {
        // `ark_std::test_rng()` is deterministic but deliberately doesn't
        // implement `CryptoRng` (it's not a CSPRNG) — `GM17::setup`/
        // `prove` require `CryptoRng`, so use a seeded `StdRng` instead.
        use ark_std::rand::{rngs::StdRng, SeedableRng};
        let mut rng = StdRng::seed_from_u64(42);
        let (pk, vk) = setup(&mut rng).unwrap();

        let c = valid_circuit();
        let public_inputs = GenesisSpendCircuit::public_inputs(
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
        c.own_nullifier_nonmembership = [Some(tree.prove_non_membership(own_nullifier))];
        c.generate_constraints(cs.clone()).unwrap();
        assert!(!cs.is_satisfied().unwrap(), "a nullifier already in the accumulator must fail non-membership");
    }

    /// Pads a variable-length list of real output commitments out to
    /// `MAX_OUTPUTS` with a zero sentinel — both a spend's own fixed-size
    /// public output and any `BoardEntry` built from the same transaction
    /// must agree on this padding, or the entry's leaf hash won't match what
    /// the circuit computes.
    fn pad_outputs(real: &[Fr]) -> [Fr; MAX_OUTPUTS] {
        let mut out = [Fr::from(0u64); MAX_OUTPUTS];
        out[..real.len()].copy_from_slice(real);
        out
    }

    /// A real genesis mint (100 to Alice) plus its wrapped proof — shared
    /// setup for the tests below. Returns everything a child `SpendStepCircuit`
    /// needs to reference genesis as its origin.
    #[allow(clippy::type_complexity)]
    fn genesis_mint_to_alice<R: ark_std::rand::RngCore + ark_std::rand::CryptoRng>(
        rng: &mut R,
    ) -> (
        BoardEntry,                        // genesis_entry
        VerifyingKey<MNT6_753>,             // wrap_genesis_vk
        Proof<MNT6_753>,                    // wrap_genesis_proof
        [Fr; SPEND_PUBLIC_INPUT_COUNT],     // genesis_public_inputs
        Coin,                               // alice_coin
        OwnerScalar,                        // alice_sk
        OwnerPk,                            // alice_pk
    ) {
        let sk_genesis = genesis_sk();
        let pk_genesis = derive_owner_pk(&sk_genesis);
        let genesis_input = Coin { value: 100, rand: Fr::from(2u64), owner_pk: pk_genesis };
        let alice_sk = OwnerScalar::from(42u64);
        let alice_pk = derive_owner_pk(&alice_sk);
        let alice_coin = Coin { value: 100, rand: Fr::from(4u64), owner_pk: alice_pk };

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
        let (genesis_pk_data, genesis_vk) = setup(rng).unwrap();
        let genesis_public_inputs: [Fr; SPEND_PUBLIC_INPUT_COUNT] =
            GenesisSpendCircuit::public_inputs(genesis_outputs, genesis_board_root, empty_tree.root())
                .try_into()
                .unwrap();
        let genesis_proof = prove(&genesis_pk_data, genesis_circuit, rng).unwrap();

        let (wrap_genesis_pk, wrap_genesis_vk) =
            cloakkchain_circuit_wrap::setup::<SPEND_PUBLIC_INPUT_COUNT, _>(genesis_vk, rng).unwrap();
        let wrap_genesis_proof = cloakkchain_circuit_wrap::prove::<SPEND_PUBLIC_INPUT_COUNT, _>(
            &wrap_genesis_pk,
            cloakkchain_circuit_wrap::WrapCircuit::<SPEND_PUBLIC_INPUT_COUNT> {
                inner_vk: genesis_pk_data.vk.clone(),
                inner_proof: Some(genesis_proof),
                inner_public_inputs: Some(genesis_public_inputs),
            },
            rng,
        )
        .unwrap();

        let genesis_entry = BoardEntry {
            ciphertext: vec![],
            ek_pk: [0u8; 32],
            key_encs: vec![],
            nullifier: genesis_own_nullifier,
            output_commitments: genesis_outputs.to_vec(),
            // Nothing precedes genesis — both roots are the empty ones,
            // which also happen to be exactly `genesis_board_root`/
            // `empty_tree.root()` themselves (first-ever entry).
            prev_board_root: empty_root(),
            prev_nullifier_root: empty_tree.root(),
        };

        (genesis_entry, wrap_genesis_vk, wrap_genesis_proof, genesis_public_inputs, alice_coin, alice_sk, alice_pk)
    }

    /// Build Alice's (non-genesis) `SpendStepCircuit` witness spending the
    /// coin genesis just minted her, to Bob — exercising the new
    /// origin-inclusion + binding checks against a real wrapped parent proof.
    #[allow(clippy::too_many_arguments)]
    fn alice_spend_circuit(
        genesis_entry: &BoardEntry,
        wrap_genesis_vk: VerifyingKey<MNT6_753>,
        wrap_genesis_proof: Proof<MNT6_753>,
        genesis_public_inputs: [Fr; SPEND_PUBLIC_INPUT_COUNT],
        alice_coin: Coin,
        alice_sk: OwnerScalar,
        alice_pk: OwnerPk,
    ) -> (SpendStepCircuit, [Fr; SPEND_PUBLIC_INPUT_COUNT], OwnerScalar) {
        let bob_sk = OwnerScalar::from(7u64);
        let bob_pk = derive_owner_pk(&bob_sk);
        let bob_coin = Coin { value: 100, rand: Fr::from(6u64), owner_pk: bob_pk };
        let bob_commitment = bob_coin.commitment();

        let alice_spend_slot = 1u64;
        let alice_spend_append_path = append_path_for_next(std::slice::from_ref(genesis_entry));
        let alice_spend_board_root =
            compute_root_from_path(Fr::from(0u64), alice_spend_slot as usize, &alice_spend_append_path);
        let alice_own_nullifier = poseidon_hash(&[alice_coin.commitment(), fold_owner_scalar(&alice_sk)]);
        let mut tree_after_genesis = NullifierTree::new();
        tree_after_genesis.insert(genesis_entry.nullifier);

        let alice_spend_outputs = pad_outputs(&[bob_commitment]);
        let circuit = SpendStepCircuit {
            pk_p: Some(alice_pk),
            output_commitments: Some(alice_spend_outputs),
            board_root: Some(alice_spend_board_root),
            current_nullifier_root: Some(tree_after_genesis.root()),
            sk_p: Some(alice_sk),
            input_coins: [Some(alice_coin)],
            output_coins: [Some(bob_coin), None],
            entry_position: Some(alice_spend_slot),
            append_path: Some(alice_spend_append_path),
            own_nullifier_nonmembership: [Some(tree_after_genesis.prove_non_membership(alice_own_nullifier))],
            wrap_vk: wrap_genesis_vk,
            input_parent_proofs: [Some(wrap_genesis_proof)],
            input_parent_public_inputs: [Some(genesis_public_inputs)],
            origin_received_slot: [Some(0)],
            origin_entry_nullifier: [Some(genesis_entry.nullifier)],
            origin_entry_output_commitments: [Some(genesis_entry.output_commitments.clone().try_into().unwrap())],
            origin_entry_ciphertext_commitment: [Some(entry_ciphertext_commitment(genesis_entry))],
            origin_append_path: [Some(append_path_for_next(&[]))],
            origin_prev_board_root: [Some(genesis_entry.prev_board_root)],
            origin_prev_nullifier_root: [Some(genesis_entry.prev_nullifier_root)],
        };
        let public_inputs: [Fr; SPEND_PUBLIC_INPUT_COUNT] =
            SpendStepCircuit::public_inputs(alice_spend_outputs, alice_spend_board_root, tree_after_genesis.root())
                .try_into()
                .unwrap();
        (circuit, public_inputs, bob_sk)
    }

    /// The binding fix, exercised directly: a genuine origin (genesis's real
    /// entry, with its real preceding roots) satisfies every constraint; a
    /// tampered `origin_prev_board_root` or `origin_entry_output_commitments`
    /// — the two values the binding check ties to the recursively verified
    /// parent proof's own public claims — does not. Mirrors
    /// `wrong_secret_key_fails`'s approach of checking raw constraint
    /// satisfiability directly, paying for the one real genesis+wrap proof
    /// needed as a genuine witness either way.
    #[test]
    fn tampered_origin_binding_fails() {
        use ark_std::rand::{rngs::StdRng, SeedableRng};
        let mut rng = StdRng::seed_from_u64(20260918);

        let (genesis_entry, wrap_genesis_vk, wrap_genesis_proof, genesis_public_inputs, alice_coin, alice_sk, alice_pk) =
            genesis_mint_to_alice(&mut rng);
        let (base_circuit, _, _) = alice_spend_circuit(
            &genesis_entry,
            wrap_genesis_vk,
            wrap_genesis_proof,
            genesis_public_inputs,
            alice_coin,
            alice_sk,
            alice_pk,
        );

        let cs = ConstraintSystem::<Fr>::new_ref();
        base_circuit.clone().generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap(), "a genuine origin (real genesis entry) should satisfy every constraint");

        let mut wrong_prev_root = base_circuit.clone();
        wrong_prev_root.origin_prev_board_root = [Some(Fr::from(999u64))]; // not the real prev root
        let cs2 = ConstraintSystem::<Fr>::new_ref();
        wrong_prev_root.generate_constraints(cs2.clone()).unwrap();
        assert!(
            !cs2.is_satisfied().unwrap(),
            "a fabricated origin_prev_board_root must not satisfy the circuit"
        );

        let mut wrong_outputs = base_circuit;
        wrong_outputs.origin_entry_output_commitments = [Some([Fr::from(999u64), Fr::from(0u64)])]; // not genesis's real outputs
        let cs3 = ConstraintSystem::<Fr>::new_ref();
        wrong_outputs.generate_constraints(cs3.clone()).unwrap();
        assert!(
            !cs3.is_satisfied().unwrap(),
            "origin_entry_output_commitments inconsistent with the parent's own proof must not satisfy the circuit"
        );
    }

    /// Full chain, real GM17 proofs end to end, without any receipt-proof
    /// layer: genesis mints to Alice, Alice spends to Bob (directly
    /// recursively verifying genesis's own wrapped proof), Bob spends to
    /// Carol (directly recursively verifying Alice's own wrapped proof).
    #[test]
    fn genesis_alice_bob_carol_chain_without_receipts() {
        use ark_std::rand::{rngs::StdRng, SeedableRng};
        let mut rng = StdRng::seed_from_u64(20260919);

        let (genesis_entry, wrap_genesis_vk, wrap_genesis_proof, genesis_public_inputs, alice_coin, alice_sk, alice_pk) =
            genesis_mint_to_alice(&mut rng);
        let (alice_circuit, alice_public_inputs, bob_sk) = alice_spend_circuit(
            &genesis_entry,
            wrap_genesis_vk.clone(),
            wrap_genesis_proof,
            genesis_public_inputs,
            alice_coin,
            alice_sk,
            alice_pk,
        );
        let bob_pk = alice_circuit.output_coins[0].as_ref().unwrap().owner_pk;

        let (alice_spend_pk, alice_spend_vk) = setup_non_genesis(wrap_genesis_vk, &mut rng).unwrap();
        let alice_spend_proof = prove_non_genesis(&alice_spend_pk, alice_circuit, &mut rng).unwrap();
        assert!(
            verify_non_genesis(&alice_spend_vk, &alice_public_inputs, &alice_spend_proof).unwrap(),
            "Alice's spend (directly wrapping genesis's proof, no receipt layer) must verify"
        );

        let (wrap_alice_pk, wrap_alice_vk) =
            cloakkchain_circuit_wrap::setup::<SPEND_PUBLIC_INPUT_COUNT, _>(alice_spend_vk, &mut rng).unwrap();
        let wrap_alice_proof = cloakkchain_circuit_wrap::prove::<SPEND_PUBLIC_INPUT_COUNT, _>(
            &wrap_alice_pk,
            cloakkchain_circuit_wrap::WrapCircuit::<SPEND_PUBLIC_INPUT_COUNT> {
                inner_vk: alice_spend_pk.vk.clone(),
                inner_proof: Some(alice_spend_proof),
                inner_public_inputs: Some(alice_public_inputs),
            },
            &mut rng,
        )
        .unwrap();

        let bob_coin = Coin { value: 100, rand: Fr::from(6u64), owner_pk: bob_pk };
        let alice_spend_outputs = pad_outputs(&[bob_coin.commitment()]);
        let alice_spend_entry = BoardEntry {
            ciphertext: vec![],
            ek_pk: [0u8; 32],
            key_encs: vec![],
            nullifier: poseidon_hash(&[alice_coin_commitment(&genesis_entry), fold_owner_scalar(&alice_sk)]),
            output_commitments: alice_spend_outputs.to_vec(),
            prev_board_root: alice_public_inputs[MAX_OUTPUTS],
            prev_nullifier_root: alice_public_inputs[MAX_OUTPUTS + 1],
        };

        let carol_sk = OwnerScalar::from(13u64);
        let carol_pk = derive_owner_pk(&carol_sk);
        let carol_coin = Coin { value: 100, rand: Fr::from(10u64), owner_pk: carol_pk };
        let carol_commitment = carol_coin.commitment();

        let bob_spend_slot = 2u64;
        let bob_spend_append_path = append_path_for_next(&[genesis_entry.clone(), alice_spend_entry.clone()]);
        let bob_spend_board_root =
            compute_root_from_path(Fr::from(0u64), bob_spend_slot as usize, &bob_spend_append_path);
        let bob_own_nullifier = poseidon_hash(&[bob_coin.commitment(), fold_owner_scalar(&bob_sk)]);
        let mut tree_after_alice = NullifierTree::new();
        tree_after_alice.insert(genesis_entry.nullifier);
        tree_after_alice.insert(alice_spend_entry.nullifier);

        let bob_spend_outputs = pad_outputs(&[carol_commitment]);
        let bob_spend_circuit = SpendStepCircuit {
            pk_p: Some(bob_pk),
            output_commitments: Some(bob_spend_outputs),
            board_root: Some(bob_spend_board_root),
            current_nullifier_root: Some(tree_after_alice.root()),
            sk_p: Some(bob_sk),
            input_coins: [Some(bob_coin)],
            output_coins: [Some(carol_coin), None],
            entry_position: Some(bob_spend_slot),
            append_path: Some(bob_spend_append_path),
            own_nullifier_nonmembership: [Some(tree_after_alice.prove_non_membership(bob_own_nullifier))],
            wrap_vk: wrap_alice_vk.clone(),
            input_parent_proofs: [Some(wrap_alice_proof)],
            input_parent_public_inputs: [Some(alice_public_inputs)],
            origin_received_slot: [Some(1)],
            origin_entry_nullifier: [Some(alice_spend_entry.nullifier)],
            origin_entry_output_commitments: [Some(alice_spend_outputs)],
            origin_entry_ciphertext_commitment: [Some(entry_ciphertext_commitment(&alice_spend_entry))],
            origin_append_path: [Some(append_path_for_next(std::slice::from_ref(&genesis_entry)))],
            origin_prev_board_root: [Some(alice_spend_entry.prev_board_root)],
            origin_prev_nullifier_root: [Some(alice_spend_entry.prev_nullifier_root)],
        };
        let (bob_spend_pk, bob_spend_vk) = setup_non_genesis(wrap_alice_vk, &mut rng).unwrap();
        let bob_spend_public_inputs =
            SpendStepCircuit::public_inputs(bob_spend_outputs, bob_spend_board_root, tree_after_alice.root());
        let bob_spend_proof = prove_non_genesis(&bob_spend_pk, bob_spend_circuit, &mut rng).unwrap();

        assert!(
            verify_non_genesis(&bob_spend_vk, &bob_spend_public_inputs, &bob_spend_proof).unwrap(),
            "the full genesis->Alice->Bob->Carol chain must verify end to end, with no receipt-proof layer"
        );

        let mut tampered = bob_spend_public_inputs.clone();
        tampered[0] += Fr::from(1u64);
        assert!(!verify_non_genesis(&bob_spend_vk, &tampered, &bob_spend_proof).unwrap());
    }

    fn alice_coin_commitment(genesis_entry: &BoardEntry) -> Fr {
        genesis_entry.output_commitments[0]
    }
}
