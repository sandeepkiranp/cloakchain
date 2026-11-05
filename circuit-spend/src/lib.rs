//! MNT-native spend circuit: the constraint-system form of
//! `cloakkchain_lib::check_spend`, which is its correctness oracle.
//! `GenesisSpendCircuit` is the genesis-mint variant — no recursive parent
//! verification, since genesis mints never have a parent spend.
//! `SpendStepCircuit` is the non-genesis variant, which does recursively verify
//! one wrapped parent `GenesisSpendCircuit`/`SpendStepCircuit` proof *per active
//! input slot* via `GM17VerifierGadget`, directly — no separate receipt-proof
//! layer. Both share [`SpendCoreWitness`] and one public-input layout.
//!
//! **What a proof is checked against.** A spend commits to an *anchor*, a state
//! from before it was posted, and never to the slot it lands at, so another
//! entry landing first doesn't invalidate it. Serial numbers are public and
//! copyable, so an occurrence of one doesn't prove anything by itself: the
//! spender shows each occurrence in its parent's window is either the same spend
//! or carries an invalid signature. See [`parent_checks`].
//!
//! **Folding, with no cap on copies.** `SpendStepCircuit` has a private mode
//! bit. In *spend* mode it is the spend relation. In *fold* mode it verifies a
//! proof `R` (a spend proof `P`, or an earlier fold over `P`), copies `R`'s
//! statement as its own, and checks one more occurrence of `P`'s serial number is
//! harmless ([`fold_step`]). Every proof publishes a `window_head`: `0` for a
//! spend, the occurrence chain's head for a fold. A spend takes whatever proof it
//! verifies as its parent's statement plus a certified window, and only has to
//! show that head is exactly what `P`'s serial number has in the accumulator just
//! before `P`'s slot. So `k` copies cost `P`'s next spender `k` fold steps, an
//! honest spend with an empty window pays for none, and nothing can make a coin
//! unspendable. Both modes are one circuit, so one VK, which is what lets folds
//! verify each other.
//!
//! **Totality.** Window occurrences can be arbitrary junk posted by anyone. So
//! checking one must *evaluate to false*, never make the circuit unsatisfiable:
//! otherwise a single junk copy could stop a coin from ever being spent. That's
//! why signatures use challenge form (no attacker-supplied curve point to
//! parse), and it relies on scalar multiplication (`scalar_mul_le`, and
//! `scalar_mul_le_compact` for witness bases, the same algorithm) being complete
//! for scalars of up to 753 bits. Its incomplete additions only cover the low 751 bits, where the
//! accumulator stays odd and below `2^i`, so it can never equal `±2^i` mod the
//! group order; everything else goes through complete formulas.
//!
//! **One verifying key for every generation.** `SpendStepCircuit` embeds the
//! wrap circuit's VK as a constant, and that circuit takes the VK it verifies as
//! a witness, pinned by the inner proof's last public input, `vk_hash` (see
//! `circuit-wrap`). So the two keys don't depend on each other circularly, and a
//! single setup of each serves chains of any depth. A spend checks that its
//! parent's `vk_hash` is the genesis circuit's (a constant: genesis depends on
//! nothing) or its own; whoever verifies the final proof checks its own
//! `vk_hash` against the deployment's, which pins every step by induction.
//!
//! Both support up to [`MAX_INPUTS`] input coins and [`MAX_OUTPUTS`] output
//! coins (slot 0 of each is mandatory; the rest are optional, gated by an
//! explicit `is_active` witness per slot — see the module's padding notes
//! below). Every active input slot gets its own parent verification, so a
//! spender can't supply unproven "phantom" extra inputs.
//!
//! **Padding safety**: an inactive slot's `is_active` bit gates its checks
//! (`check | !is_active`, so a fabricated dummy witness can't fail them) — but
//! *not* its value's contribution to the conservation sum, which is separately
//! zeroed via `is_active.select(value, 0)` regardless of what value the prover
//! actually supplies. Only gating the checks (and not also the value) would let
//! a dishonest prover mark a real-valued slot "inactive" and mint that value
//! into the sum with no nullifier or parent backing it. Likewise an inactive
//! output's public commitment is forced to zero: it isn't counted towards
//! conservation, so anything else would be a spendable coin from nothing.

use ark_crypto_primitives::snark::{constraints::SNARKGadget, BooleanInputVar};
use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar, poseidon::constraints::PoseidonSpongeVar,
};
use ark_ec::{AffineRepr, CurveGroup, PrimeGroup};
use ark_ff::{BigInteger, PrimeField};
use ark_gm17::{
    constraints::{GM17VerifierGadget, ProofVar, VerifyingKeyVar},
    GM17, Proof, ProvingKey, VerifyingKey,
};
use ark_mnt4_753::MNT4_753;
use ark_mnt6_753::MNT6_753;
use ark_r1cs_std::{fields::fp::FpVar, prelude::*};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_snark::SNARK;
use ark_std::rand::{CryptoRng, RngCore};
use cloakkchain_circuit_wrap::{
    chunks_per_value, combine_chunks_var, public_input_chunks, scalar_mul_le_compact, Fr6, CHUNK_BITS,
};
use cloakkchain_lib::{
    derive_coin_vpk, derive_nullifier, genesis_pk, hash_vpk, owner_pk_to_field_pair, poseidon_params, Anchor,
    Coin, CoinSignature, Fr, IndexedLeaf, LeafOpening, NonMembershipWitness, Occurrence, OwnerPk, OwnerScalar,
    ParentWitness, SpendPublicValues, WindowWitness, SIG_CHALLENGE_DOMAIN, SIG_KEY_DOMAIN, SIG_S_LO_BITS,
    TREE_DEPTH,
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

// More inputs need one serial number and signature per input on `BoardEntry`,
// which holds one of each today: the leaf a parent check opens would only bind
// the first input, and the rest could be double-spent unnoticed.
const _: () = assert!(MAX_INPUTS == 1, "multi-input spends need BoardEntry to carry one SN and σ per input");

/// Total public-input count for [`GenesisSpendCircuit`]/[`SpendStepCircuit`]
/// (both share the same layout):
/// `output_commitments[0..MAX_OUTPUTS], anchor.size, anchor.board_root,
/// anchor.nullifier_root, nullifiers[0..MAX_INPUTS], vpk_hashes[0..MAX_INPUTS],
/// window_head, vk_hash`. `vk_hash` must be last: that's where the wrap circuit
/// looks for it. `pk_p` and `vpk` are private witnesses, not part of this
/// vector.
pub const SPEND_PUBLIC_INPUT_COUNT: usize = MAX_OUTPUTS + 5 + 2 * MAX_INPUTS;

/// Index, within a recursively-verified parent spend proof's public-input
/// chunk groups, of each value — mirrors [`spend_public_inputs`]'s order.
const PARENT_OUTPUT_COMMITMENTS_START: usize = 0;
const PARENT_ANCHOR_SIZE: usize = MAX_OUTPUTS;
const PARENT_ANCHOR_BOARD_ROOT: usize = MAX_OUTPUTS + 1;
const PARENT_ANCHOR_NULLIFIER_ROOT: usize = MAX_OUTPUTS + 2;
const PARENT_NULLIFIER: usize = MAX_OUTPUTS + 3;
const PARENT_VPK_HASH: usize = MAX_OUTPUTS + 3 + MAX_INPUTS;
const PARENT_WINDOW_HEAD: usize = SPEND_PUBLIC_INPUT_COUNT - 2;
const PARENT_VK_HASH: usize = SPEND_PUBLIC_INPUT_COUNT - 1;

/// Pads a variable-length list of real output commitments out to `MAX_OUTPUTS`
/// with zeros, for the proof's fixed-size public inputs. A `BoardEntry` posts
/// only the real ones, since a zero on the wire would mark it as a carrier. The
/// two still hash alike: trailing zeros leave a Poseidon sponge's state as it
/// was, and `H(O)` is what binds them (see
/// `posted_outputs_need_no_padding`).
pub fn pad_outputs(real: &[Fr]) -> [Fr; MAX_OUTPUTS] {
    let mut out = [Fr::from(0u64); MAX_OUTPUTS];
    out[..real.len()].copy_from_slice(real);
    out
}

/// What a proof of either circuit claims: a spend's public values, the window
/// head it certifies (`0` for a spend proof, see the module doc comment), and
/// `circuit_wrap::inner_vk_hash` of the key it's for.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct StepStatement {
    pub public_values: SpendPublicValues,
    pub window_head: Fr,
    pub vk_hash: Fr,
}

impl StepStatement {
    pub fn public_inputs(&self) -> [Fr; SPEND_PUBLIC_INPUT_COUNT] {
        spend_public_inputs(&self.public_values, self.window_head, self.vk_hash)
    }
}

/// What one fold step adds: an occurrence of the statement's serial number, and
/// the per-coin key its harmlessness is judged under.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct FoldWitness {
    pub vpk: OwnerPk,
    pub occurrence: Occurrence,
}

/// The GM17 public-input vector for a spend's public values, in the exact order
/// [`synthesize_core`] allocates them. Single-input, per the `MAX_INPUTS`
/// assertion above.
pub fn spend_public_inputs(pv: &SpendPublicValues, window_head: Fr, vk_hash: Fr) -> [Fr; SPEND_PUBLIC_INPUT_COUNT] {
    let mut out = pad_outputs(&pv.output_commitments).to_vec();
    out.push(Fr::from(pv.anchor.size));
    out.push(pv.anchor.board_root);
    out.push(pv.anchor.nullifier_root);
    out.extend([pv.nullifier; MAX_INPUTS]);
    out.extend([pv.vpk_hash; MAX_INPUTS]);
    out.push(window_head);
    out.push(vk_hash);
    out.try_into().expect("the layout above has SPEND_PUBLIC_INPUT_COUNT values")
}

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

/// `a < b` for equal-length, most-significant-bit-first bit vectors.
///
/// Deliberately not `ark-r1cs-std`'s `CmpGadget` for slices, which isn't
/// lexicographic (as of 0.5.0): past the first differing bit its `is_ge` still
/// demands `a[i] > b[i]` at every later position, so `[1,0] >= [0,1]` is false,
/// and its `is_lt` comes out true for nearly any `a != b`. Built on that, the
/// accumulator's bracketing check accepts a member through any unrelated leaf.
fn bits_msb_is_lt(a: &[Boolean<Fr>], b: &[Boolean<Fr>]) -> Result<Boolean<Fr>, SynthesisError> {
    assert_eq!(a.len(), b.len());
    let mut lt = Boolean::FALSE;
    let mut equal_so_far = Boolean::TRUE;
    for (x, y) in a.iter().zip(b) {
        lt = &lt | &(&equal_so_far & &(&!x.clone() & y));
        equal_so_far = &equal_so_far & &x.is_eq(y)?;
    }
    Ok(lt)
}

/// `a < b` over `Fr`'s canonical integer representative, via the canonical
/// (unique) bit decomposition.
fn fp_is_lt(a: &Fp, b: &Fp) -> Result<Boolean<Fr>, SynthesisError> {
    let mut a_bits = a.to_bits_le()?;
    let mut b_bits = b.to_bits_le()?;
    a_bits.reverse();
    b_bits.reverse();
    bits_msb_is_lt(&a_bits, &b_bits)
}

/// Every witness below defaults to zero when there's no value, i.e. in setup
/// mode and for an unused (padding) slot. Safe, since a padding slot's checks
/// are gated by `is_active` (see the module doc comment).
fn alloc_fp(cs: ConstraintSystemRef<Fr>, value: Option<Fr>) -> Result<Fp, SynthesisError> {
    Fp::new_witness(cs, || Ok(value.unwrap_or(Fr::from(0u64))))
}

fn alloc_path(cs: ConstraintSystemRef<Fr>, path: Option<&Vec<Fr>>) -> Result<Vec<Fp>, SynthesisError> {
    (0..TREE_DEPTH).map(|i| alloc_fp(cs.clone(), path.map(|p| p[i]))).collect()
}

/// `TREE_DEPTH` little-endian bits of a tree position. Allocated bit by bit, so
/// that the position is range-checked at no extra cost: the numeric comparison
/// of two slots in [`parent_checks`] depends on it.
fn alloc_position_bits(cs: ConstraintSystemRef<Fr>, position: Option<u64>) -> Result<Vec<Boolean<Fr>>, SynthesisError> {
    let position = position.unwrap_or(0);
    (0..TREE_DEPTH).map(|i| Boolean::new_witness(cs.clone(), || Ok((position >> i) & 1 == 1))).collect()
}

struct IndexedLeafVar {
    value: Fp,
    next_value: Fp,
    next_index: Fp,
    occ: Fp,
}

impl IndexedLeafVar {
    fn hash(&self, cs: ConstraintSystemRef<Fr>) -> Result<Fp, SynthesisError> {
        poseidon_hash_var(cs, &[self.value.clone(), self.next_value.clone(), self.next_index.clone(), self.occ.clone()])
    }

    fn new_witness(cs: ConstraintSystemRef<Fr>, leaf: Option<&IndexedLeaf>) -> Result<Self, SynthesisError> {
        Ok(Self {
            value: alloc_fp(cs.clone(), leaf.map(|l| l.value))?,
            next_value: alloc_fp(cs.clone(), leaf.map(|l| l.next_value))?,
            next_index: alloc_fp(cs.clone(), leaf.map(|l| Fr::from(l.next_index)))?,
            occ: alloc_fp(cs, leaf.map(|l| l.occ))?,
        })
    }

    /// `value < target < next_value`, which no member could satisfy.
    fn brackets(&self, target: &Fp) -> Result<Boolean<Fr>, SynthesisError> {
        Ok(&fp_is_lt(&self.value, target)? & &fp_is_lt(target, &self.next_value)?)
    }
}

/// Mirrors `cloakkchain_lib::verify_nonmembership`, returning the boolean
/// result rather than enforcing it — callers combine it with an `is_active`
/// gate (see the module doc comment) before enforcing.
fn verify_nonmembership_var(
    cs: ConstraintSystemRef<Fr>,
    root: &Fp,
    target: &Fp,
    witness: Option<&NonMembershipWitness>,
) -> Result<Boolean<Fr>, SynthesisError> {
    let low_leaf = IndexedLeafVar::new_witness(cs.clone(), witness.map(|w| &w.low_leaf))?;
    let index_bits = alloc_position_bits(cs.clone(), witness.map(|w| w.low_leaf_index))?;
    let path = alloc_path(cs.clone(), witness.map(|w| &w.sibling_path))?;
    let leaf_hash = low_leaf.hash(cs.clone())?;
    let computed_root = compute_root_from_path_var(cs, &leaf_hash, &index_bits, &path)?;
    Ok(&low_leaf.brackets(target)? & &computed_root.is_eq(root)?)
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
            rand: alloc_fp(cs.clone(), coin.as_ref().map(|c| c.rand))?,
            owner_pk_x: alloc_fp(cs.clone(), owner_xy.map(|(x, _)| x))?,
            owner_pk_y: alloc_fp(cs, owner_xy.map(|(_, y)| y))?,
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

/// `target` is a member of `list` — an OR of per-slot equality checks. Used
/// to identify which of a parent's (up to `MAX_OUTPUTS`) output commitments is
/// this input coin's own commitment.
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

fn generator_var(cs: ConstraintSystemRef<Fr>) -> Result<G1Var, SynthesisError> {
    G1Var::new_constant(cs, ark_mnt6_753::G1Projective::generator())
}

// ---- signatures --------------------------------------------------------------

/// A per-coin key as circuit variables: a real curve point, since it gets
/// multiplied, with its coordinates alongside for hashing.
struct CoinKeyVar {
    point: G1Var,
    x: Fp,
    y: Fp,
}

impl CoinKeyVar {
    fn from_point(point: G1Var) -> Result<Self, SynthesisError> {
        let affine = point.to_affine()?;
        Ok(Self { point, x: affine.x, y: affine.y })
    }

    /// Defaults to the generator when there's no value: unlike a zero field
    /// element it's a real point, so the group arithmetic stays well defined.
    fn new_witness(cs: ConstraintSystemRef<Fr>, vpk: Option<&OwnerPk>) -> Result<Self, SynthesisError> {
        let native = vpk.copied().unwrap_or(ark_mnt6_753::G1Affine::generator());
        Self::from_point(G1Var::new_witness(cs, || Ok(native.into_group()))?)
    }

    /// Mirrors `cloakkchain_lib::hash_vpk`.
    fn hash(&self, cs: ConstraintSystemRef<Fr>) -> Result<Fp, SynthesisError> {
        poseidon_hash_var(cs, &[self.x.clone(), self.y.clone()])
    }
}

/// `σ` as it enters hashes: `c` plus `s`'s two limbs. `native_s` is only for
/// witnessing `s`'s bits when a signature is actually verified, which plenty of
/// leaves never are.
struct CoinSignatureVar {
    c: Fp,
    s_lo: Fp,
    s_hi: Fp,
    native_s: Option<OwnerScalar>,
}

impl CoinSignatureVar {
    fn new_witness(cs: ConstraintSystemRef<Fr>, sig: Option<&CoinSignature>) -> Result<Self, SynthesisError> {
        let limbs = sig.map(CoinSignature::s_limbs);
        Ok(Self {
            c: alloc_fp(cs.clone(), sig.map(|s| s.c))?,
            s_lo: alloc_fp(cs.clone(), limbs.map(|(lo, _)| lo))?,
            s_hi: alloc_fp(cs, limbs.map(|(_, hi)| hi))?,
            native_s: sig.map(|s| s.s),
        })
    }

    /// Mirrors `cloakkchain_lib::verify_coin_signature`: `c == H(s·G − c·vpk,
    /// vpk, msg)`. Evaluates to `false` on junk rather than becoming
    /// unsatisfiable — see the module doc comment.
    ///
    /// The bits-to-limbs equalities are enforced, not returned, and that's
    /// still total: `s` is a canonical scalar on every entry that parses, so
    /// its limbs always decompose. The limbs are bound by the enclosing hash,
    /// so the bits are unique too.
    fn verify(&self, cs: ConstraintSystemRef<Fr>, vpk: &CoinKeyVar, msg: &Fp) -> Result<Boolean<Fr>, SynthesisError> {
        let s_bit_values: Vec<bool> = self.native_s.unwrap_or(OwnerScalar::from(0u64)).into_bigint().to_bits_le();
        let s_bits: Vec<Boolean<Fr>> = (0..OwnerScalar::MODULUS_BIT_SIZE as usize)
            .map(|i| Boolean::new_witness(cs.clone(), || Ok(s_bit_values[i])))
            .collect::<Result<_, _>>()?;
        Boolean::le_bits_to_fp(&s_bits[..SIG_S_LO_BITS])?.enforce_equal(&self.s_lo)?;
        Boolean::le_bits_to_fp(&s_bits[SIG_S_LO_BITS..])?.enforce_equal(&self.s_hi)?;

        // Canonical, and accepts any field value: junk `c` can't fail here.
        let c_bits = self.c.to_bits_le()?;

        let s_g = generator_var(cs.clone())?.scalar_mul_le(s_bits.iter())?;
        // `vpk` is a witness, so the library's scalar-mult would make these
        // rows very dense; see `scalar_mul_le_compact`.
        let c_vpk = scalar_mul_le_compact(&vpk.point, &c_bits)?;
        let r = (s_g - c_vpk).to_affine()?;
        let challenge = poseidon_hash_var(
            cs,
            &[Fp::constant(Fr::from(SIG_CHALLENGE_DOMAIN)), r.x, r.y, vpk.x.clone(), vpk.y.clone(), msg.clone()],
        )?;
        challenge.is_eq(&self.c)
    }
}

/// Mirrors `cloakkchain_lib::signature_message`.
fn signature_message_var(
    cs: ConstraintSystemRef<Fr>,
    nullifier: &Fp,
    outputs_hash: &Fp,
    ciphertext_commitment: &Fp,
) -> Result<Fp, SynthesisError> {
    poseidon_hash_var(cs, &[nullifier.clone(), outputs_hash.clone(), ciphertext_commitment.clone()])
}

// ---- history leaves ------------------------------------------------------------

/// Mirrors `cloakkchain_lib::LeafOpening`.
struct LeafOpeningVar {
    slot: Fp,
    slot_bits: Vec<Boolean<Fr>>,
    ciphertext_commitment: Fp,
    nullifier: Fp,
    outputs_hash: Fp,
    signature: CoinSignatureVar,
    prev_board_root: Fp,
    prev_nullifier_root: Fp,
}

impl LeafOpeningVar {
    fn new_witness(cs: ConstraintSystemRef<Fr>, leaf: Option<&LeafOpening>) -> Result<Self, SynthesisError> {
        let slot_bits = alloc_position_bits(cs.clone(), leaf.map(|l| l.slot))?;
        Ok(Self {
            slot: Boolean::le_bits_to_fp(&slot_bits)?,
            slot_bits,
            ciphertext_commitment: alloc_fp(cs.clone(), leaf.map(|l| l.ciphertext_commitment))?,
            nullifier: alloc_fp(cs.clone(), leaf.map(|l| l.nullifier))?,
            outputs_hash: alloc_fp(cs.clone(), leaf.map(|l| l.outputs_hash))?,
            signature: CoinSignatureVar::new_witness(cs.clone(), leaf.map(|l| &l.signature))?,
            prev_board_root: alloc_fp(cs.clone(), leaf.map(|l| l.prev_board_root))?,
            prev_nullifier_root: alloc_fp(cs, leaf.map(|l| l.prev_nullifier_root))?,
        })
    }

    fn hash(&self, cs: ConstraintSystemRef<Fr>) -> Result<Fp, SynthesisError> {
        poseidon_hash_var(
            cs,
            &[
                self.slot.clone(),
                self.ciphertext_commitment.clone(),
                self.nullifier.clone(),
                self.outputs_hash.clone(),
                self.signature.c.clone(),
                self.signature.s_lo.clone(),
                self.signature.s_hi.clone(),
                self.prev_board_root.clone(),
                self.prev_nullifier_root.clone(),
            ],
        )
    }

    /// Does this leaf open to `root` along `path`?
    fn opens_to(
        &self,
        cs: ConstraintSystemRef<Fr>,
        path: Option<&Vec<Fr>>,
        root: &Fp,
    ) -> Result<Boolean<Fr>, SynthesisError> {
        let path = alloc_path(cs.clone(), path)?;
        let leaf = self.hash(cs.clone())?;
        compute_root_from_path_var(cs, &leaf, &self.slot_bits, &path)?.is_eq(root)
    }
}

// ---- the window ------------------------------------------------------------------

/// Mirrors `Occurrence::link`.
fn occurrence_link_var(
    cs: ConstraintSystemRef<Fr>,
    previous: &Fp,
    outputs_hash: &Fp,
    ciphertext_commitment: &Fp,
    signature: &CoinSignatureVar,
) -> Result<Fp, SynthesisError> {
    poseidon_hash_var(
        cs,
        &[
            previous.clone(),
            outputs_hash.clone(),
            ciphertext_commitment.clone(),
            signature.c.clone(),
            signature.s_lo.clone(),
            signature.s_hi.clone(),
        ],
    )
}

/// The window, given a head that folds have certified: under `root`, the
/// nullifier is absent if `head` is zero (a spend proof certifies no window),
/// and otherwise its leaf holds exactly `head`. Exactly, so no occurrence can
/// have been left out of the folds.
fn window_opens(
    cs: ConstraintSystemRef<Fr>,
    root: &Fp,
    nullifier: &Fp,
    head: &Fp,
    witness: Option<&WindowWitness>,
) -> Result<Boolean<Fr>, SynthesisError> {
    let leaf = IndexedLeafVar::new_witness(cs.clone(), witness.map(|w| &w.leaf))?;
    let index_bits = alloc_position_bits(cs.clone(), witness.map(|w| w.leaf_index))?;
    let path = alloc_path(cs.clone(), witness.map(|w| &w.sibling_path))?;
    let leaf_hash = leaf.hash(cs.clone())?;
    let root_ok = compute_root_from_path_var(cs, &leaf_hash, &index_bits, &path)?.is_eq(root)?;

    // A prover can't claim the wrong case: a member can't be bracketed, and a
    // non-member has no leaf to open.
    let absent = leaf.brackets(nullifier)?;
    let member = &leaf.value.is_eq(nullifier)? & &leaf.occ.is_eq(head)?;
    let case_ok = Boolean::conditionally_select(&head.is_zero()?, &absent, &member)?;
    Ok(&root_ok & &case_ok)
}

/// One fold step: mirrors `Occurrence::is_harmless` for one occurrence of the
/// statement's serial number, under the key the statement names, and returns
/// the next window head alongside the result.
///
/// Total, like everything that reads occurrences: junk evaluates to a valid
/// fold, and a double-spend evaluates to `false`, never an unsatisfiable
/// circuit.
fn fold_step(
    cs: ConstraintSystemRef<Fr>,
    witness: Option<&FoldWitness>,
    pv: &ParentPublicVars,
) -> Result<(Boolean<Fr>, Fp), SynthesisError> {
    let occurrence = witness.map(|w| &w.occurrence);
    let vpk = CoinKeyVar::new_witness(cs.clone(), witness.map(|w| &w.vpk))?;
    let key_ok = vpk.hash(cs.clone())?.is_eq(&pv.vpk_hash)?;

    let occ_outputs_hash = alloc_fp(cs.clone(), occurrence.map(|o| o.outputs_hash))?;
    let occ_ciphertext = alloc_fp(cs.clone(), occurrence.map(|o| o.ciphertext_commitment))?;
    let occ_signature = CoinSignatureVar::new_witness(cs.clone(), occurrence.map(|o| &o.signature))?;

    let outputs_hash = poseidon_hash_var(cs.clone(), &pv.output_commitments)?;
    let msg = signature_message_var(cs.clone(), &pv.nullifier, &occ_outputs_hash, &occ_ciphertext)?;
    let valid = occ_signature.verify(cs.clone(), &vpk, &msg)?;
    let harmless = &occ_outputs_hash.is_eq(&outputs_hash)? | &!valid;

    let next_head = occurrence_link_var(cs, &pv.window_head, &occ_outputs_hash, &occ_ciphertext, &occ_signature)?;
    Ok((&key_ok & &harmless, next_head))
}

// ---- parent checks -------------------------------------------------------------

/// A parent spend proof's public values as circuit variables. In
/// [`SpendStepCircuit`] these come out of the recursive verification.
struct ParentPublicVars {
    output_commitments: Vec<Fp>,
    anchor_size: Fp,
    anchor_board_root: Fp,
    anchor_nullifier_root: Fp,
    nullifier: Fp,
    vpk_hash: Fp,
    window_head: Fp,
    vk_hash: Fp,
}

impl ParentPublicVars {
    /// The spend statement, in the order [`SpendCoreVars::statement`] has it.
    fn statement(&self) -> Vec<Fp> {
        let mut out = self.output_commitments.clone();
        out.extend([
            self.anchor_size.clone(),
            self.anchor_board_root.clone(),
            self.anchor_nullifier_root.clone(),
            self.nullifier.clone(),
            self.vpk_hash.clone(),
        ]);
        out
    }
}

/// Mirrors `cloakkchain_lib::check_parent`: everything about the entry that
/// created an input coin, except for the recursive verification itself and the
/// occurrences in its window, which folds have already checked: `pv.window_head`
/// certifies them. All of it is opened against this spend's own anchor, so
/// nothing depends on where this spend lands. Returns the result rather than
/// enforcing it so that it can be gated — and kept separate from recursion so
/// tests can reach it without a real proof.
fn parent_checks(
    cs: ConstraintSystemRef<Fr>,
    witness: Option<&ParentWitness>,
    pv: &ParentPublicVars,
    commitment: &Fp,
    anchor_board_root: &Fp,
) -> Result<Boolean<Fr>, SynthesisError> {
    let leaf = LeafOpeningVar::new_witness(cs.clone(), witness.map(|w| &w.leaf))?;
    let leaf_in_anchor = leaf.opens_to(cs.clone(), witness.map(|w| &w.leaf_path), anchor_board_root)?;

    let outputs_hash = poseidon_hash_var(cs.clone(), &pv.output_commitments)?;
    let proof_matches_entry = &pv.nullifier.is_eq(&leaf.nullifier)? & &outputs_hash.is_eq(&leaf.outputs_hash)?;
    let creates_coin = is_member(commitment, &pv.output_commitments)?;

    // The parent's anchor is real: the leaf right after that state, under this
    // spend's anchor, embeds exactly the roots the parent's proof was checked
    // against. The history itself vouches for them, and the anchor can't have
    // come after the parent.
    let anchor_leaf = LeafOpeningVar::new_witness(cs.clone(), witness.map(|w| &w.anchor_leaf))?;
    let anchor_leaf_in_anchor =
        anchor_leaf.opens_to(cs.clone(), witness.map(|w| &w.anchor_leaf_path), anchor_board_root)?;
    let msb_first = |bits: &[Boolean<Fr>]| bits.iter().rev().cloned().collect::<Vec<_>>();
    let anchor_precedes_parent = !bits_msb_is_lt(&msb_first(&leaf.slot_bits), &msb_first(&anchor_leaf.slot_bits))?;
    let anchor_real = Boolean::kary_and(&[
        anchor_leaf.slot.is_eq(&pv.anchor_size)?,
        anchor_leaf.prev_board_root.is_eq(&pv.anchor_board_root)?,
        anchor_leaf.prev_nullifier_root.is_eq(&pv.anchor_nullifier_root)?,
        anchor_precedes_parent,
    ])?;

    // Without this binding a dishonest parent could post a broken signature so
    // that its spend looks like junk, then double-spend the coin.
    let vpk = CoinKeyVar::new_witness(cs.clone(), witness.map(|w| &w.vpk))?;
    let vpk_matches = vpk.hash(cs.clone())?.is_eq(&pv.vpk_hash)?;
    let msg = signature_message_var(cs.clone(), &leaf.nullifier, &leaf.outputs_hash, &leaf.ciphertext_commitment)?;
    let signature_ok = leaf.signature.verify(cs.clone(), &vpk, &msg)?;

    let window_ok =
        window_opens(cs, &leaf.prev_nullifier_root, &leaf.nullifier, &pv.window_head, witness.map(|w| &w.window))?;

    Boolean::kary_and(&[
        leaf_in_anchor,
        proof_matches_entry,
        creates_coin,
        anchor_leaf_in_anchor,
        anchor_real,
        vpk_matches,
        signature_ok,
        window_ok,
    ])
}

// ---- the shared relation -------------------------------------------------------

/// Everything both spend circuits share: the public values, and the private
/// witnesses for `check_spend`'s conditions other than the parent's.
#[derive(Clone, Default, CanonicalSerialize, CanonicalDeserialize)]
pub struct SpendCoreWitness {
    // Public values.
    pub output_commitments: Option<[Fr; MAX_OUTPUTS]>,
    pub anchor: Option<Anchor>,
    pub nullifiers: Option<[Fr; MAX_INPUTS]>,
    pub vpk_hashes: Option<[Fr; MAX_INPUTS]>,
    /// `0` for a spend; a fold's is the occurrence chain head it certifies.
    pub window_head: Option<Fr>,
    /// The hash of the VK this proof is for. Not constrained by the circuit
    /// itself — see the module doc comment for who checks it.
    pub vk_hash: Option<Fr>,

    // Private witnesses.
    pub pk_p: Option<OwnerPk>,
    pub sk_p: Option<OwnerScalar>,
    /// Slot 0 must be `Some`; slots `1..MAX_INPUTS` are optional (padding).
    pub input_coins: [Option<Coin>; MAX_INPUTS],
    /// Slot 0 must be `Some`; slots `1..MAX_OUTPUTS` are optional (padding).
    pub output_coins: [Option<Coin>; MAX_OUTPUTS],
    /// Against `anchor.nullifier_root`. One per input slot (padding slots still
    /// need *some* witness — see the module doc comment for why it's safe to
    /// be unconstrained there).
    pub own_nullifier_nonmembership: [Option<NonMembershipWitness>; MAX_INPUTS],
}

impl SpendCoreWitness {
    /// A spend of `input_coin` by `sk`, deriving every public value from it,
    /// for the circuit whose VK hashes to `vk_hash`.
    pub fn new(
        sk: OwnerScalar,
        input_coin: Coin,
        output_coins: &[Coin],
        anchor: Anchor,
        nonmembership: NonMembershipWitness,
        vk_hash: Fr,
    ) -> Self {
        let commitment = input_coin.commitment();
        let real_outputs: Vec<Fr> = output_coins.iter().map(Coin::commitment).collect();
        Self {
            output_commitments: Some(pad_outputs(&real_outputs)),
            anchor: Some(anchor),
            nullifiers: Some([derive_nullifier(commitment, &sk); MAX_INPUTS]),
            vpk_hashes: Some([hash_vpk(&derive_coin_vpk(&sk, commitment)); MAX_INPUTS]),
            window_head: Some(Fr::from(0u64)),
            vk_hash: Some(vk_hash),
            pk_p: Some(input_coin.owner_pk),
            sk_p: Some(sk),
            input_coins: std::array::from_fn(|i| (i == 0).then(|| input_coin.clone())),
            output_coins: std::array::from_fn(|i| output_coins.get(i).cloned()),
            own_nullifier_nonmembership: std::array::from_fn(|i| (i == 0).then(|| nonmembership.clone())),
        }
    }

    /// A fold's public values: `previous`'s spend statement, with the window head
    /// it leads to. Everything private stays empty, since fold mode doesn't
    /// use it.
    pub fn for_fold(previous: &StepStatement, window_head: Fr, vk_hash: Fr) -> Self {
        let pv = &previous.public_values;
        Self {
            output_commitments: Some(pad_outputs(&pv.output_commitments)),
            anchor: Some(pv.anchor.clone()),
            nullifiers: Some([pv.nullifier; MAX_INPUTS]),
            vpk_hashes: Some([pv.vpk_hash; MAX_INPUTS]),
            window_head: Some(window_head),
            vk_hash: Some(vk_hash),
            ..Self::default()
        }
    }

    /// The statement this witness proves, for embedding next to the proof.
    pub fn public_values(&self) -> Option<SpendPublicValues> {
        Some(SpendPublicValues {
            output_commitments: self.output_commitments?.to_vec(),
            anchor: self.anchor.clone()?,
            nullifier: self.nullifiers?[0],
            vpk_hash: self.vpk_hashes?[0],
        })
    }
}

/// What [`SpendStepCircuit`] needs back from [`synthesize_core`], and
/// [`GenesisSpendCircuit`] for its fixed-key check.
struct SpendCoreVars {
    /// The public spend statement, in [`spend_public_inputs`]' order up to
    /// `window_head`. In fold mode these must equal the folded statement's.
    statement: Vec<Fp>,
    window_head: Fp,
    vk_hash: Fp,
    pk_p_x: Fp,
    pk_p_y: Fp,
    anchor_board_root: Fp,
    input_commitments: Vec<Fp>,
    input_active: [Boolean<Fr>; MAX_INPUTS],
}

/// Everything in `check_spend` but the parent: allocates the public inputs in
/// their fixed order, then ownership, freshness at the anchor, the derivation of
/// `SN` and `vpk`, and value conservation. All of it applies only when
/// `spend_mode` holds: in fold mode the public values are another proof's
/// statement, and the private witnesses are empty.
fn synthesize_core(
    cs: ConstraintSystemRef<Fr>,
    w: &SpendCoreWitness,
    spend_mode: &Boolean<Fr>,
) -> Result<SpendCoreVars, SynthesisError> {
    // --- public inputs, in the fixed order `spend_public_inputs` matches ---
    let output_commitments: Vec<Fp> = (0..MAX_OUTPUTS)
        .map(|i| Fp::new_input(cs.clone(), || opt(&w.output_commitments.map(|a| a[i]))))
        .collect::<Result<_, _>>()?;
    let anchor = w.anchor.as_ref();
    let anchor_size = Fp::new_input(cs.clone(), || opt(&anchor.map(|a| Fr::from(a.size))))?;
    let anchor_board_root = Fp::new_input(cs.clone(), || opt(&anchor.map(|a| a.board_root)))?;
    let anchor_nullifier_root = Fp::new_input(cs.clone(), || opt(&anchor.map(|a| a.nullifier_root)))?;
    let nullifiers: Vec<Fp> = (0..MAX_INPUTS)
        .map(|i| Fp::new_input(cs.clone(), || opt(&w.nullifiers.map(|a| a[i]))))
        .collect::<Result<_, _>>()?;
    let vpk_hashes: Vec<Fp> = (0..MAX_INPUTS)
        .map(|i| Fp::new_input(cs.clone(), || opt(&w.vpk_hashes.map(|a| a[i]))))
        .collect::<Result<_, _>>()?;
    let window_head = Fp::new_input(cs.clone(), || opt(&w.window_head))?;
    let vk_hash = Fp::new_input(cs.clone(), || opt(&w.vk_hash))?;

    // A spend certifies no window; only folds do.
    gate(window_head.is_zero()?, spend_mode).enforce_equal(&Boolean::TRUE)?;

    let mut statement = output_commitments.clone();
    statement.extend([anchor_size, anchor_board_root.clone(), anchor_nullifier_root.clone()]);
    statement.extend(nullifiers.iter().cloned());
    statement.extend(vpk_hashes.iter().cloned());

    // --- pk_p is a private witness, not a public input: nothing downstream
    // ever needs to read it back out of a spend proof, and its own uses here
    // work identically whether it's public or private, since they're all
    // equality checks against values already available inside this circuit.
    let pk_xy = w.pk_p.as_ref().map(owner_pk_to_field_pair);
    let pk_p_x = alloc_fp(cs.clone(), pk_xy.map(|(x, _)| x))?;
    let pk_p_y = alloc_fp(cs.clone(), pk_xy.map(|(_, y)| y))?;

    // --- sk_p / pk_p (zero in fold mode, where `pk_p` is zero too, as
    // `0·G` is the point at infinity) ---
    let sk_bit_values: Vec<bool> = w.sk_p.unwrap_or(OwnerScalar::from(0u64)).into_bigint().to_bits_le();
    let sk_bit_len = OwnerScalar::MODULUS_BIT_SIZE as usize;
    let sk_bits: Vec<Boolean<Fr>> = (0..sk_bit_len)
        .map(|i| Boolean::new_witness(cs.clone(), || Ok(sk_bit_values[i])))
        .collect::<Result<_, _>>()?;
    // Canonicity: sk_bits, as an integer, must be < OwnerScalar's modulus
    // — otherwise two different bit patterns could represent the same
    // group element (same pk_p) but fold to two different nullifiers,
    // letting the same coin be spent twice under different nullifiers.
    let mut modulus_minus_one = OwnerScalar::MODULUS.0.to_vec();
    modulus_minus_one[0] -= 1; // odd prime modulus, so this can't borrow
    Boolean::enforce_smaller_or_equal_than_le(&sk_bits, modulus_minus_one)?;

    let pk_p_computed = generator_var(cs.clone())?.scalar_mul_le(sk_bits.iter())?.to_affine()?;
    pk_p_computed.x.enforce_equal(&pk_p_x)?;
    pk_p_computed.y.enforce_equal(&pk_p_y)?;

    let sk_folded = fold_bits_le_var(cs.clone(), &sk_bits)?;

    // --- input slots ---
    let input_present: [bool; MAX_INPUTS] = std::array::from_fn(|i| w.input_coins[i].is_some());
    let mut input_active = alloc_active_flags(cs.clone(), &input_present)?;
    for active in input_active.iter_mut() {
        *active = &*active & spend_mode;
    }
    let mut input_commitments = Vec::with_capacity(MAX_INPUTS);
    let mut total_in = Fp::zero();
    for i in 0..MAX_INPUTS {
        let coin = CoinVar::new_witness(cs.clone(), &w.input_coins[i])?;
        let owner_ok = &coin.owner_pk_x.is_eq(&pk_p_x)? & &coin.owner_pk_y.is_eq(&pk_p_y)?;
        gate(owner_ok, &input_active[i]).enforce_equal(&Boolean::TRUE)?;

        let commitment = coin.commitment(cs.clone())?;

        // `SN` and `vpk` are correctly derived. This binding is essential:
        // without it a spender could hand a recipient a fake `vpk`, under which
        // their double-spend would look like junk.
        let own_nullifier = poseidon_hash_var(cs.clone(), &[commitment.clone(), sk_folded.clone()])?;
        gate(own_nullifier.is_eq(&nullifiers[i])?, &input_active[i]).enforce_equal(&Boolean::TRUE)?;

        let vsk = poseidon_hash_var(
            cs.clone(),
            &[Fp::constant(Fr::from(SIG_KEY_DOMAIN)), commitment.clone(), sk_folded.clone()],
        )?;
        let vsk_bits = vsk.to_bits_le()?;
        let vpk = CoinKeyVar::from_point(generator_var(cs.clone())?.scalar_mul_le(vsk_bits.iter())?)?;
        gate(vpk.hash(cs.clone())?.is_eq(&vpk_hashes[i])?, &input_active[i]).enforce_equal(&Boolean::TRUE)?;

        // `SN ∉ A_a`, which is what binds a spend to an anchor from before its
        // nullifier's first broadcast.
        let nonmembership_ok = verify_nonmembership_var(
            cs.clone(),
            &anchor_nullifier_root,
            &own_nullifier,
            w.own_nullifier_nonmembership[i].as_ref(),
        )?;
        gate(nonmembership_ok, &input_active[i]).enforce_equal(&Boolean::TRUE)?;

        total_in += coin.value_or_zero(&input_active[i])?;
        input_commitments.push(commitment);
    }

    // --- output slots: commitment matches the public list, and an inactive
    // slot's public commitment is forced to zero (see the module doc comment) ---
    let output_present: [bool; MAX_OUTPUTS] = std::array::from_fn(|i| w.output_coins[i].is_some());
    let output_active = alloc_active_flags(cs.clone(), &output_present)?;
    let mut total_out = Fp::zero();
    for j in 0..MAX_OUTPUTS {
        let coin = CoinVar::new_witness(cs.clone(), &w.output_coins[j])?;
        let expected = Fp::conditionally_select(&output_active[j], &coin.commitment(cs.clone())?, &Fp::zero())?;
        gate(expected.is_eq(&output_commitments[j])?, spend_mode).enforce_equal(&Boolean::TRUE)?;
        total_out += coin.value_or_zero(&output_active[j])?;
    }

    // --- value conservation: Σ active inputs == Σ active outputs ---
    total_in.enforce_equal(&total_out)?;

    Ok(SpendCoreVars { statement, window_head, vk_hash, pk_p_x, pk_p_y, anchor_board_root, input_commitments, input_active })
}

// ---- the circuits --------------------------------------------------------------

/// The genesis-mint variant of the spend relation (`check_spend` with no
/// parent — genesis's own inputs are always trusted by construction). Same
/// public layout as [`SpendStepCircuit`], since a spend of a minted coin
/// verifies this proof the same way as any other parent's.
#[derive(Clone, Default, CanonicalSerialize, CanonicalDeserialize)]
pub struct GenesisSpendCircuit {
    pub core: SpendCoreWitness,
}

impl ConstraintSynthesizer<Fr> for GenesisSpendCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let core = synthesize_core(cs, &self.core, &Boolean::TRUE)?;

        // --- genesis: pk_p must be the fixed, well-known genesis key ---
        let (genesis_x, genesis_y) = owner_pk_to_field_pair(&genesis_pk());
        core.pk_p_x.enforce_equal(&Fp::constant(genesis_x))?;
        core.pk_p_y.enforce_equal(&Fp::constant(genesis_y))?;
        Ok(())
    }
}

/// The non-genesis variant of the spend relation, and the fold step (see the
/// module doc comment), selected by `fold`.
///
/// Spend mode: everything [`GenesisSpendCircuit`] checks, plus, per active input
/// slot, a recursive verification of the proof describing the entry that
/// created the input coin — its spend proof, or a fold over it — wrapped via
/// `circuit-wrap`, plus [`parent_checks`] against that proof's statement.
///
/// Fold mode: verifies one such proof, publishes its statement unchanged, and
/// advances its window head by one harmless occurrence ([`fold_step`]).
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SpendStepCircuit {
    /// The spend in spend mode; [`SpendCoreWitness::for_fold`] in fold mode.
    pub core: SpendCoreWitness,
    /// `Some` selects fold mode.
    pub fold: Option<FoldWitness>,

    /// Fixed per deployment — not `Option`, a verifying key isn't secret.
    pub wrap_vk: VerifyingKey<MNT6_753>,
    /// `circuit_wrap::inner_vk_hash` of `GenesisSpendCircuit`'s VK, fixed per
    /// deployment like `wrap_vk`.
    pub genesis_vk_hash: Fr,
    /// One wrapped parent spend proof per active input slot (a
    /// `Wrap<SPEND_PUBLIC_INPUT_COUNT>` proof). `None` for a padding slot (still
    /// needs *a* structurally-valid dummy proof — see `circuit-wrap::setup`'s
    /// doc comment for why).
    pub input_parent_proofs: [Option<Proof<MNT6_753>>; MAX_INPUTS],
    /// What each of those proofs claims. Its `vk_hash` must be
    /// `genesis_vk_hash` or this proof's own.
    pub input_parent_statements: [Option<StepStatement>; MAX_INPUTS],
    /// Spend mode only: the parent's entry, and the openings against this
    /// spend's anchor.
    pub input_parents: [Option<ParentWitness>; MAX_INPUTS],
}

impl SpendStepCircuit {
    /// A structurally-valid (not necessarily verifying) filler for an
    /// unused input slot's parent proof — never checked when `is_active`
    /// is false (see the module doc comment).
    /// Deliberately *not* the point at infinity: unlike `circuit-wrap`'s
    /// own `setup()` dummy proof (which only ever runs in GM17 setup mode,
    /// where witness values are never numerically checked), this one is also
    /// used as the real witness for an *inactive* input slot during actual
    /// proving — the pairing gadget's internal (Miller-loop) arithmetic isn't
    /// guaranteed well-defined at infinity even though the gated `recursive_ok`
    /// is allowed to end up `false`, so use the group generator instead:
    /// non-degenerate, and still obviously not a valid proof for anything.
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
        let is_fold = Boolean::new_witness(cs.clone(), || Ok(self.fold.is_some()))?;
        let spend_mode = !is_fold.clone();
        let core = synthesize_core(cs.clone(), &self.core, &spend_mode)?;

        // --- wrap VK (shared by every active input slot's parent proof) ---
        let wrap_vk_var = VerifyingKeyVar::<MNT6_753, MNT6PairingVar>::new_constant(cs.clone(), &self.wrap_vk)?;
        let pvk = wrap_vk_var.prepare()?;
        let parent_public_len = SPEND_PUBLIC_INPUT_COUNT * chunks_per_value();
        let cpv = chunks_per_value();

        for i in 0..MAX_INPUTS {
            let is_active = &core.input_active[i];
            // A fold verifies slot 0's proof too, so that one is always checked.
            let recursion_active = if i == 0 { Boolean::TRUE } else { is_active.clone() };

            // --- recursively verify the proof describing the entry that
            // created this input coin, directly (no separate receipt-proof
            // layer). A padding slot has no real parent — fall back to all-zero
            // chunks (never checked, since every check below is gated; see the
            // module doc comment).
            //
            // Each chunk goes in as only the `CHUNK_BITS` the wrap circuit
            // already bounds it to. Wider would cost more and allow an alias:
            // the verifier reads the bits mod the wrap field's modulus `r`, so
            // `x + r` would pass for chunk `x`, while `combine_chunks_var`
            // would read its low bits as something else.
            let parent_chunks: Vec<Fr6> = self.input_parent_statements[i]
                .as_ref()
                .map(|statement| public_input_chunks(&statement.public_inputs()))
                .unwrap_or_else(|| vec![Fr6::from(0u64); parent_public_len]);
            let mut parent_per_chunk_bits: Vec<Vec<Boolean<Fr>>> = Vec::with_capacity(parent_public_len);
            for k in 0..parent_public_len {
                let value_bits: Vec<bool> = parent_chunks[k].into_bigint().to_bits_le();
                let bits: Vec<Boolean<Fr>> = (0..CHUNK_BITS)
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
            gate(parent_recursive_ok, &recursion_active).enforce_equal(&Boolean::TRUE)?;

            // --- what that proof claims, as just recursively verified ---
            let pgroup = |idx: usize| combine_chunks_var(&parent_per_chunk_bits[idx * cpv..(idx + 1) * cpv]);
            let pv = ParentPublicVars {
                output_commitments: (0..MAX_OUTPUTS)
                    .map(|j| pgroup(PARENT_OUTPUT_COMMITMENTS_START + j))
                    .collect::<Result<_, _>>()?,
                anchor_size: pgroup(PARENT_ANCHOR_SIZE)?,
                anchor_board_root: pgroup(PARENT_ANCHOR_BOARD_ROOT)?,
                anchor_nullifier_root: pgroup(PARENT_ANCHOR_NULLIFIER_ROOT)?,
                nullifier: pgroup(PARENT_NULLIFIER)?,
                vpk_hash: pgroup(PARENT_VPK_HASH)?,
                window_head: pgroup(PARENT_WINDOW_HEAD)?,
                vk_hash: pgroup(PARENT_VK_HASH)?,
            };

            // The wrap circuit guarantees that proof verifies under the VK its
            // `vk_hash` names; this pins which VKs those may be.
            let parent_vk_ok = &pv.vk_hash.is_eq(&Fp::constant(self.genesis_vk_hash))? | &pv.vk_hash.is_eq(&core.vk_hash)?;
            gate(parent_vk_ok, &recursion_active).enforce_equal(&Boolean::TRUE)?;

            // --- spend mode ---
            let parent_ok =
                parent_checks(cs.clone(), self.input_parents[i].as_ref(), &pv, &core.input_commitments[i], &core.anchor_board_root)?;
            gate(parent_ok, is_active).enforce_equal(&Boolean::TRUE)?;

            // --- fold mode: same statement, one more harmless occurrence ---
            if i == 0 {
                let (harmless, next_head) = fold_step(cs.clone(), self.fold.as_ref(), &pv)?;
                let mut fold_ok = vec![harmless, core.window_head.is_eq(&next_head)?];
                for (mine, theirs) in core.statement.iter().zip(pv.statement()) {
                    fold_ok.push(mine.is_eq(&theirs)?);
                }
                gate(Boolean::kary_and(&fold_ok)?, &is_fold).enforce_equal(&Boolean::TRUE)?;
            }
        }

        Ok(())
    }
}

/// One setup serves every generation — see the module doc comment.
pub fn setup_non_genesis<R: RngCore + CryptoRng>(
    wrap_vk: VerifyingKey<MNT6_753>,
    genesis_vk_hash: Fr,
    rng: &mut R,
) -> Result<(ProvingKey<MNT4_753>, VerifyingKey<MNT4_753>), SynthesisError> {
    let circuit = SpendStepCircuit {
        core: SpendCoreWitness::default(),
        fold: None,
        wrap_vk,
        genesis_vk_hash,
        // See circuit-wrap's `setup` for why every slot needs *some*
        // structurally-valid dummy proof rather than `None` — `ProofVar`'s
        // `AllocVar` impl calls its value closure unconditionally.
        input_parent_proofs: std::array::from_fn(|_| Some(SpendStepCircuit::dummy_wrap_proof())),
        input_parent_statements: std::array::from_fn(|_| None),
        input_parents: std::array::from_fn(|_| None),
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

/// Tests named `proving_*` run real GM17 setup and proving. They need far more
/// memory than a laptop has, so run them on a big machine (`cargo test --release
/// proving_`); everything else is constraint-level (`-- --skip proving_`).
#[cfg(test)]
mod tests {
    use super::*;
    use ark_relations::r1cs::{ConstraintSystem, SynthesisMode};
    use cloakkchain_lib::{
        check_spend, derive_coin_signing_key, encrypt_tx, genesis_sk, sign_coin_message, verify_coin_signature,
        BoardEntry, History, Transaction,
    };

    fn owner(seed: u64) -> (OwnerScalar, OwnerPk) {
        let sk = OwnerScalar::from(seed + 100);
        (sk, cloakkchain_lib::derive_owner_pk(&sk))
    }

    fn coin(seed: u64, value: u64, owner_pk: OwnerPk) -> Coin {
        Coin { value, rand: Fr::from(seed + 1000), owner_pk }
    }

    /// A spend as far as the native oracle goes: no real proof attached.
    #[derive(Clone)]
    struct Posted {
        entry: BoardEntry,
        pv: SpendPublicValues,
        vpk: OwnerPk,
        core: SpendCoreWitness,
    }

    fn post(
        history: &History,
        sk: OwnerScalar,
        input: &Coin,
        outputs: &[Coin],
        anchor_size: usize,
        parent: Option<&ParentWitness>,
        id: u8,
    ) -> Posted {
        let anchor = history.anchor_at(anchor_size).unwrap();
        let cm = input.commitment();
        let nonmembership = history.nullifier_tree_at(anchor_size).prove_non_membership(derive_nullifier(cm, &sk));
        let real: Vec<Fr> = outputs.iter().map(Coin::commitment).collect();
        let padded = pad_outputs(&real);
        let pv = check_spend(&sk, input, outputs, &padded, &anchor, &nonmembership, parent).unwrap();
        let vpk = derive_coin_vpk(&sk, cm);
        let tx = Transaction {
            id: id as u64,
            output_commitments: padded.to_vec(),
            note_encs: vec![],
            vpk,
            anchor: anchor.clone(),
            spend_proof: vec![],
        };
        let entry = encrypt_tx(&tx, cm, &sk, &[[9u8; 32]], [id; 32]);
        let core = SpendCoreWitness::new(sk, input.clone(), outputs, anchor, nonmembership, Fr::from(0u64));
        assert_eq!(core.public_values().as_ref(), Some(&pv), "circuit and oracle must agree on the statement");
        Posted { entry, pv, vpk, core }
    }

    fn junk_copy(nullifier: Fr, seed: u64) -> BoardEntry {
        BoardEntry {
            ciphertext: vec![seed as u8; 40],
            ek_pk: [seed as u8; 32],
            key_encs: vec![[seed as u8; 32]],
            nullifier,
            output_commitments: vec![Fr::from(seed)],
            signature: CoinSignature { c: Fr::from(seed), s: OwnerScalar::from(seed) },
        }
    }

    struct World {
        history: History,
        genesis: Posted,
        alice_coin: Coin,
        alice_sk: OwnerScalar,
        bob_coin: Coin,
        bob_sk: OwnerScalar,
    }

    /// Genesis (slot 0) mints 100 to Alice.
    fn world() -> World {
        let (alice_sk, alice_pk) = owner(1);
        let (bob_sk, bob_pk) = owner(2);
        let alice_coin = coin(2, 100, alice_pk);
        let mut history = History::new();
        let genesis = post(&history, genesis_sk(), &coin(1, 100, genesis_pk()), &[alice_coin.clone()], 0, None, 0);
        history.append(&genesis.entry);
        World { history, genesis, alice_coin, alice_sk, bob_coin: coin(3, 100, bob_pk), bob_sk }
    }

    impl World {
        fn alice_spends(&self, output: &Coin, id: u8) -> Posted {
            let parent = self.history.parent_witness(0, &self.genesis.pv, &self.genesis.vpk, 1);
            post(&self.history, self.alice_sk, &self.alice_coin, std::slice::from_ref(output), 1, Some(&parent), id)
        }

        fn alice_nullifier(&self) -> Fr {
            derive_nullifier(self.alice_coin.commitment(), &self.alice_sk)
        }

        /// What Bob shows about the carrier at `slot`, at the current state.
        fn witness_for(&self, slot: usize, carrier: &Posted) -> (ParentWitness, Fr) {
            let size = self.history.len();
            let witness = self.history.parent_witness(slot, &carrier.pv, &carrier.vpk, size);
            (witness, self.history.anchor_at(size).unwrap().board_root)
        }
    }

    /// The window head honest folds over this window would certify: zero if
    /// it's empty, else the chain head in the parent's leaf.
    fn certified_head(witness: &ParentWitness) -> Fr {
        if witness.window.occurrences.is_empty() { Fr::from(0u64) } else { witness.window.leaf.occ }
    }

    fn parent_public_vars(cs: ConstraintSystemRef<Fr>, statement: &StepStatement) -> ParentPublicVars {
        let vars: Vec<Fp> =
            statement.public_inputs().iter().map(|v| Fp::new_witness(cs.clone(), || Ok(*v)).unwrap()).collect();
        ParentPublicVars {
            output_commitments: vars[PARENT_OUTPUT_COMMITMENTS_START..MAX_OUTPUTS].to_vec(),
            anchor_size: vars[PARENT_ANCHOR_SIZE].clone(),
            anchor_board_root: vars[PARENT_ANCHOR_BOARD_ROOT].clone(),
            anchor_nullifier_root: vars[PARENT_ANCHOR_NULLIFIER_ROOT].clone(),
            nullifier: vars[PARENT_NULLIFIER].clone(),
            vpk_hash: vars[PARENT_VPK_HASH].clone(),
            window_head: vars[PARENT_WINDOW_HEAD].clone(),
            vk_hash: vars[PARENT_VK_HASH].clone(),
        }
    }

    /// Evaluate `parent_checks` on a witness, with the window head honest folds
    /// would certify. Checks totality on the way: the circuit must stay
    /// satisfiable whatever the answer is.
    fn parent_checks_result(witness: &ParentWitness, commitment: Fr, anchor_board_root: Fr) -> bool {
        parent_checks_with_head(witness, certified_head(witness), commitment, anchor_board_root)
    }

    fn parent_checks_with_head(witness: &ParentWitness, head: Fr, commitment: Fr, anchor_board_root: Fr) -> bool {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let statement = StepStatement { public_values: witness.public_values.clone(), window_head: head, vk_hash: Fr::from(0u64) };
        let pv = parent_public_vars(cs.clone(), &statement);
        let commitment = Fp::new_witness(cs.clone(), || Ok(commitment)).unwrap();
        let root = Fp::new_witness(cs.clone(), || Ok(anchor_board_root)).unwrap();
        let ok = parent_checks(cs.clone(), Some(witness), &pv, &commitment, &root).unwrap();
        assert!(cs.is_satisfied().unwrap(), "must evaluate to false, never become unsatisfiable");
        ok.value().unwrap()
    }

    /// Evaluate one fold step over `statement`. Returns whether it holds, and
    /// the head it leads to; checks totality like `parent_checks_with_head`.
    fn fold_result(statement: &StepStatement, fold: &FoldWitness) -> (bool, Fr) {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let pv = parent_public_vars(cs.clone(), statement);
        let (ok, head) = fold_step(cs.clone(), Some(fold), &pv).unwrap();
        assert!(cs.is_satisfied().unwrap(), "must evaluate to false, never become unsatisfiable");
        (ok.value().unwrap(), head.value().unwrap())
    }

    /// Fold every occurrence in `witness`'s window, as the next spender would.
    /// Returns whether every step held, and the final head.
    fn fold_window(witness: &ParentWitness) -> (bool, Fr) {
        let mut statement =
            StepStatement { public_values: witness.public_values.clone(), window_head: Fr::from(0u64), vk_hash: Fr::from(0u64) };
        let mut all_ok = true;
        for occurrence in &witness.window.occurrences {
            let (ok, head) = fold_result(&statement, &FoldWitness { vpk: witness.vpk, occurrence: occurrence.clone() });
            assert_eq!(head, occurrence.link(statement.window_head), "gadget and native links must agree");
            all_ok &= ok;
            statement.window_head = head;
        }
        (all_ok, statement.window_head)
    }

    // ---- ordering ----------------------------------------------------------

    /// `ark-r1cs-std`'s slice comparison isn't lexicographic (see
    /// [`bits_msb_is_lt`]), and this is the exact case it gets wrong.
    #[test]
    fn fp_is_lt_is_numeric() {
        let values = [
            Fr::from(0u64),
            Fr::from(1u64),
            Fr::from(2u64),
            Fr::from(3u64),
            Fr::from(u64::MAX),
            -Fr::from(2u64),
            -Fr::from(1u64),
            cloakkchain_lib::poseidon_hash(&[Fr::from(1u64)]),
            cloakkchain_lib::poseidon_hash(&[Fr::from(2u64)]),
        ];
        let cs = ConstraintSystem::<Fr>::new_ref();
        for a in values {
            for b in values {
                let a_var = Fp::new_witness(cs.clone(), || Ok(a)).unwrap();
                let b_var = Fp::new_witness(cs.clone(), || Ok(b)).unwrap();
                assert_eq!(fp_is_lt(&a_var, &b_var).unwrap().value().unwrap(), a < b, "{a} < {b}");
            }
        }
        assert!(cs.is_satisfied().unwrap());
    }

    /// The double-spend attack an unsound ordering check allows: a spender whose
    /// serial number IS in the accumulator picks a leaf that doesn't bracket it.
    /// Every leaf in the tree must be refused, not only the natural low leaf.
    #[test]
    fn nonmembership_rejects_a_member_through_any_leaf() {
        let member = cloakkchain_lib::poseidon_hash(&[Fr::from(1u64)]);
        let mut history = History::new();
        history.append(&junk_copy(member, 1));
        for seed in 2..6u64 {
            history.append(&junk_copy(cloakkchain_lib::poseidon_hash(&[Fr::from(seed)]), seed));
        }
        let tree = history.nullifier_tree_at(history.len());
        let root = tree.root();

        // One witness per leaf, each opening genuinely to the root.
        let others: Vec<Fr> = (2..6u64).map(|seed| cloakkchain_lib::poseidon_hash(&[Fr::from(seed)])).collect();
        let mut leaves = vec![tree.prove_non_membership(member)];
        leaves.extend(others.iter().map(|o| tree.prove_non_membership(*o)));
        leaves.push(tree.prove_non_membership(-Fr::from(2u64)));
        for w in &leaves {
            let cs = ConstraintSystem::<Fr>::new_ref();
            let root_var = Fp::new_witness(cs.clone(), || Ok(root)).unwrap();
            let target = Fp::new_witness(cs.clone(), || Ok(member)).unwrap();
            let ok = verify_nonmembership_var(cs.clone(), &root_var, &target, Some(w)).unwrap();
            assert!(cs.is_satisfied().unwrap());
            assert!(!ok.value().unwrap(), "a member must not pass via leaf {}", w.low_leaf.value);
        }

        // Whereas a genuine non-member still passes.
        let absent = Fr::from(12345u64);
        let cs = ConstraintSystem::<Fr>::new_ref();
        let root_var = Fp::new_witness(cs.clone(), || Ok(root)).unwrap();
        let target = Fp::new_witness(cs.clone(), || Ok(absent)).unwrap();
        let w = tree.prove_non_membership(absent);
        assert!(verify_nonmembership_var(cs, &root_var, &target, Some(&w)).unwrap().value().unwrap());
    }

    /// The wire format posts real outputs only, while the proof pads them. That
    /// holds up only if a carrier with fewer outputs than `MAX_OUTPUTS` still
    /// passes every check that hashes them.
    #[test]
    fn posted_outputs_need_no_padding() {
        let a = Fr::from(7u64);
        assert_eq!(cloakkchain_lib::poseidon_hash(&[a]), cloakkchain_lib::poseidon_hash(&pad_outputs(&[a])));

        let mut w = world();
        let mut alice = w.alice_spends(&w.bob_coin, 1);
        let tx = Transaction {
            id: 1,
            output_commitments: vec![w.bob_coin.commitment()],
            note_encs: vec![],
            vpk: alice.vpk,
            anchor: alice.pv.anchor.clone(),
            spend_proof: vec![],
        };
        alice.entry = encrypt_tx(&tx, w.alice_coin.commitment(), &w.alice_sk, &[[9u8; 32]], [1u8; 32]);
        assert_eq!(alice.entry.output_commitments.len(), 1);
        let slot = w.history.append(&alice.entry);
        let (witness, root) = w.witness_for(slot, &alice);
        assert!(parent_checks_result(&witness, w.bob_coin.commitment(), root));
    }

    // ---- signatures ---------------------------------------------------------

    fn signature_result(vpk: &OwnerPk, msg: Fr, sig: &CoinSignature) -> bool {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let key = CoinKeyVar::new_witness(cs.clone(), Some(vpk)).unwrap();
        let msg_var = Fp::new_witness(cs.clone(), || Ok(msg)).unwrap();
        let sig_var = CoinSignatureVar::new_witness(cs.clone(), Some(sig)).unwrap();
        let ok = sig_var.verify(cs.clone(), &key, &msg_var).unwrap();
        assert!(cs.is_satisfied().unwrap(), "must evaluate to false, never become unsatisfiable");
        ok.value().unwrap()
    }

    #[test]
    fn signature_gadget_matches_native_verification() {
        let (sk, pk) = owner(1);
        let cm = coin(1, 5, pk).commitment();
        let vsk = derive_coin_signing_key(&sk, cm);
        let vpk = derive_coin_vpk(&sk, cm);
        let msg = Fr::from(77u64);
        let good = sign_coin_message(&vsk, msg);

        assert!(signature_result(&vpk, msg, &good));
        assert!(!signature_result(&vpk, msg + Fr::from(1u64), &good));
        assert!(!signature_result(&derive_coin_vpk(&sk, cm + Fr::from(1u64)), msg, &good));
    }

    /// The trap: junk signatures, including the scalars at the edge of
    /// `scalar_mul_le`'s incomplete additions, must all evaluate to false.
    #[test]
    fn signature_gadget_is_total_on_junk() {
        let (sk, pk) = owner(1);
        let cm = coin(1, 5, pk).commitment();
        let vpk = derive_coin_vpk(&sk, cm);
        let msg = Fr::from(77u64);
        let x = OwnerScalar::from_le_bytes_mod_order(&derive_coin_signing_key(&sk, cm).into_bigint().to_bytes_le());
        let c = Fr::from(5u64);
        let cases = [
            (Fr::from(0u64), OwnerScalar::from(0u64)), // every point at infinity
            (Fr::from(1u64), OwnerScalar::from(0u64)),
            (Fr::from(0u64), OwnerScalar::from(1u64)),
            (Fr::from(2u64), OwnerScalar::from(2u64)),
            (-Fr::from(1u64), -OwnerScalar::from(1u64)), // the largest scalars
            (-Fr::from(2u64), -OwnerScalar::from(2u64)),
            (c, OwnerScalar::from(5u64) * x),            // R is exactly infinity, so the result is (0, 0)
        ];
        for (c, s) in cases {
            let sig = CoinSignature { c, s };
            assert!(!verify_coin_signature(&vpk, msg, &sig));
            assert!(!signature_result(&vpk, msg, &sig), "c={c}, s={s}");
        }
    }

    #[test]
    fn hash_gadgets_match_native() {
        let w = world();
        let opening = w.history.opening(0).unwrap();
        let cs = ConstraintSystem::<Fr>::new_ref();
        let var = LeafOpeningVar::new_witness(cs.clone(), Some(opening)).unwrap();
        assert_eq!(var.hash(cs.clone()).unwrap().value().unwrap(), opening.hash());

        let vpk = owner(5).1;
        let key = CoinKeyVar::new_witness(cs.clone(), Some(&vpk)).unwrap();
        assert_eq!(key.hash(cs).unwrap().value().unwrap(), hash_vpk(&vpk));
    }

    // ---- parent checks and folds, against the native oracle's scenarios ------

    #[test]
    fn clean_parent_passes_with_an_empty_window() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1);
        let slot = w.history.append(&alice.entry);
        let (witness, root) = w.witness_for(slot, &alice);
        assert!(witness.window.occurrences.is_empty());
        assert!(parent_checks_result(&witness, w.bob_coin.commitment(), root));
    }

    /// The reviewers' attack, in-circuit, past the old bound of 2: copies cost
    /// one fold each and never stop Bob spending.
    #[test]
    fn any_number_of_junk_copies_folds_and_passes() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1);
        for seed in 0..5 {
            w.history.append(&junk_copy(w.alice_nullifier(), seed + 1));
        }
        let slot = w.history.append(&alice.entry);
        let (witness, root) = w.witness_for(slot, &alice);
        assert_eq!(witness.window.occurrences.len(), 5);
        let (folds_ok, head) = fold_window(&witness);
        assert!(folds_ok);
        assert_eq!(head, witness.window.leaf.occ);
        assert!(parent_checks_result(&witness, w.bob_coin.commitment(), root));
    }

    #[test]
    fn honest_re_prove_in_the_window_folds() {
        let mut w = world();
        let first = w.alice_spends(&w.bob_coin, 1);
        let second = w.alice_spends(&w.bob_coin, 2);
        w.history.append(&first.entry);
        let slot = w.history.append(&second.entry);
        let (witness, root) = w.witness_for(slot, &second);
        assert!(fold_window(&witness).0);
        assert!(parent_checks_result(&witness, w.bob_coin.commitment(), root));
    }

    /// The first validly signed spend wins: its window is empty, and the second
    /// one's can't be folded.
    #[test]
    fn validly_signed_spend_in_the_window_cannot_be_folded() {
        let mut w = world();
        let (_, carol_pk) = owner(3);
        let carol_coin = coin(4, 100, carol_pk);
        let to_bob = w.alice_spends(&w.bob_coin, 1);
        let to_carol = w.alice_spends(&carol_coin, 2);
        let bob_slot = w.history.append(&to_bob.entry);
        let carol_slot = w.history.append(&to_carol.entry);

        let (witness, root) = w.witness_for(bob_slot, &to_bob);
        assert!(parent_checks_result(&witness, w.bob_coin.commitment(), root), "the first spend stands");
        let (witness, _) = w.witness_for(carol_slot, &to_carol);
        assert!(!fold_window(&witness).0, "the second's window holds a double-spend");
    }

    #[test]
    fn fold_needs_the_parents_own_key() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1);
        w.history.append(&junk_copy(w.alice_nullifier(), 1));
        let slot = w.history.append(&alice.entry);
        let (witness, _) = w.witness_for(slot, &alice);
        let statement =
            StepStatement { public_values: witness.public_values.clone(), window_head: Fr::from(0u64), vk_hash: Fr::from(0u64) };
        let occurrence = witness.window.occurrences[0].clone();
        assert!(fold_result(&statement, &FoldWitness { vpk: witness.vpk, occurrence: occurrence.clone() }).0);
        // Under some other key every signature is "invalid", so a double-spend
        // would look like junk. The statement's `vpk_hash` rules that out.
        assert!(!fold_result(&statement, &FoldWitness { vpk: owner(7).1, occurrence }).0);
    }

    /// Junk signatures at the scalar edges, inside a fold: the step evaluates,
    /// it never becomes unsatisfiable.
    #[test]
    fn fold_is_total_on_junk() {
        let w = world();
        let alice = w.alice_spends(&w.bob_coin, 1);
        let statement = StepStatement { public_values: alice.pv.clone(), window_head: Fr::from(0u64), vk_hash: Fr::from(0u64) };
        for (c, s) in [
            (Fr::from(0u64), OwnerScalar::from(0u64)),
            (-Fr::from(1u64), -OwnerScalar::from(1u64)),
            (Fr::from(1u64), OwnerScalar::from(1u64)),
        ] {
            let occurrence = LeafOpening::new(
                0,
                &BoardEntry { signature: CoinSignature { c, s }, ..junk_copy(w.alice_nullifier(), 1) },
                Fr::from(0u64),
                Fr::from(0u64),
            )
            .occurrence();
            assert!(fold_result(&statement, &FoldWitness { vpk: alice.vpk, occurrence }).0);
        }
    }

    #[test]
    fn window_head_must_cover_every_occurrence() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1);
        w.history.append(&junk_copy(w.alice_nullifier(), 1));
        w.history.append(&junk_copy(w.alice_nullifier(), 2));
        let slot = w.history.append(&alice.entry);
        let (witness, root) = w.witness_for(slot, &alice);
        let commitment = w.bob_coin.commitment();
        assert!(parent_checks_result(&witness, commitment, root));

        // Claiming no window at all, using the tree from before the copies.
        let mut hiding = witness.clone();
        hiding.window = w.history.nullifier_tree_at(1).prove_window(w.alice_nullifier());
        assert!(!parent_checks_with_head(&hiding, Fr::from(0u64), commitment, root));
        // Claiming no window against the real leaf.
        assert!(!parent_checks_with_head(&witness, Fr::from(0u64), commitment, root));
        // Folding only the first copy.
        let partial = witness.window.occurrences[0].link(Fr::from(0u64));
        assert!(!parent_checks_with_head(&witness, partial, commitment, root));
    }

    #[test]
    fn invalid_parent_signature_fails() {
        let mut w = world();
        let mut alice = w.alice_spends(&w.bob_coin, 1);
        alice.entry.signature = CoinSignature { c: Fr::from(1u64), s: OwnerScalar::from(1u64) };
        let slot = w.history.append(&alice.entry);
        let (witness, root) = w.witness_for(slot, &alice);
        assert!(!parent_checks_result(&witness, w.bob_coin.commitment(), root));
    }

    #[test]
    fn fake_parent_vpk_fails() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1);
        let slot = w.history.append(&alice.entry);
        let (mut witness, root) = w.witness_for(slot, &alice);
        witness.vpk = owner(7).1;
        assert!(!parent_checks_result(&witness, w.bob_coin.commitment(), root));
    }

    #[test]
    fn parent_anchor_must_be_real_and_precede_the_parent() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1);
        let slot = w.history.append(&alice.entry);
        w.history.append(&junk_copy(Fr::from(5u64), 1));
        let (parent, root) = w.witness_for(slot, &alice);
        let commitment = w.bob_coin.commitment();
        assert!(parent_checks_result(&parent, commitment, root));

        // A root that never existed.
        let mut fake_root = parent.clone();
        fake_root.public_values.anchor.nullifier_root += Fr::from(1u64);
        assert!(!parent_checks_result(&fake_root, commitment, root));

        // A real leaf, but not the one embedding the claimed anchor.
        let mut wrong_leaf = parent.clone();
        wrong_leaf.anchor_leaf = w.history.opening(0).unwrap().clone();
        wrong_leaf.anchor_leaf_path = w.history.board_path(0, w.history.len());
        assert!(!parent_checks_result(&wrong_leaf, commitment, root));

        // A real state, from after the parent's own slot.
        let mut later = parent;
        later.public_values.anchor = w.history.anchor_at(2).unwrap();
        later.anchor_leaf = w.history.opening(2).unwrap().clone();
        later.anchor_leaf_path = w.history.board_path(2, w.history.len());
        assert!(!parent_checks_result(&later, commitment, root));
    }

    #[test]
    fn parent_must_be_under_the_anchor_and_create_the_coin() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1);
        let slot = w.history.append(&alice.entry);
        let (witness, root) = w.witness_for(slot, &alice);
        let commitment = w.bob_coin.commitment();

        let earlier_root = w.history.anchor_at(1).unwrap().board_root;
        assert!(!parent_checks_result(&witness, commitment, earlier_root));
        assert!(!parent_checks_result(&witness, commitment + Fr::from(1u64), root));
        // A proof made for a different serial number than the entry's.
        let mut lying = witness;
        lying.public_values.nullifier += Fr::from(1u64);
        assert!(!parent_checks_result(&lying, commitment, root));
    }

    // ---- the shared relation ---------------------------------------------------

    fn genesis_circuit() -> GenesisSpendCircuit {
        let (_, alice_pk) = owner(1);
        let history = History::new();
        let posted = post(&history, genesis_sk(), &coin(1, 100, genesis_pk()), &[coin(2, 100, alice_pk)], 0, None, 0);
        GenesisSpendCircuit { core: posted.core }
    }

    fn satisfied(circuit: GenesisSpendCircuit) -> bool {
        let cs = ConstraintSystem::<Fr>::new_ref();
        circuit.generate_constraints(cs.clone()).unwrap();
        cs.is_satisfied().unwrap()
    }

    #[test]
    fn valid_genesis_witness_satisfies_constraints() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        genesis_circuit().generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap(), "valid genesis witness should satisfy every constraint");
        println!("genesis constraint count: {}", cs.num_constraints());
    }

    #[test]
    fn two_real_outputs_with_conservation_satisfies_constraints() {
        let (_, bob_pk) = owner(2);
        let outputs = [coin(4, 40, bob_pk), coin(6, 60, genesis_pk())];
        let posted = post(&History::new(), genesis_sk(), &coin(1, 100, genesis_pk()), &outputs, 0, None, 0);
        assert!(satisfied(GenesisSpendCircuit { core: posted.core }));
    }

    #[test]
    fn wrong_secret_key_fails() {
        let mut c = genesis_circuit();
        c.core.sk_p = Some(OwnerScalar::from(2u64)); // not genesis_sk()
        assert!(!satisfied(c));
    }

    #[test]
    fn non_genesis_key_cannot_mint() {
        let (alice_sk, alice_pk) = owner(1);
        let input = coin(1, 100, alice_pk);
        let output = coin(2, 100, alice_pk);
        let history = History::new();
        let anchor = history.anchor_at(0).unwrap();
        let nonmembership = history
            .nullifier_tree_at(0)
            .prove_non_membership(derive_nullifier(input.commitment(), &alice_sk));
        let core = SpendCoreWitness::new(alice_sk, input, &[output], anchor, nonmembership, Fr::from(0u64));
        assert!(!satisfied(GenesisSpendCircuit { core }));
    }

    #[test]
    fn serial_number_and_vpk_must_be_correctly_derived() {
        let mut wrong_sn = genesis_circuit();
        wrong_sn.core.nullifiers = Some([Fr::from(1u64)]);
        assert!(!satisfied(wrong_sn));

        // The binding that stops a spender from handing over a fake `vpk`.
        let mut wrong_vpk = genesis_circuit();
        wrong_vpk.core.vpk_hashes = Some([hash_vpk(&owner(7).1)]);
        assert!(!satisfied(wrong_vpk));
    }

    #[test]
    fn nullifier_already_at_the_anchor_fails() {
        // Simulates a copy landing before the anchor: non-membership can't hold,
        // which is exactly why a wallet can't re-anchor after one.
        let mut c = genesis_circuit();
        let sn = c.core.nullifiers.unwrap()[0];
        let mut history = History::new();
        history.append(&junk_copy(sn, 1));
        c.core.anchor = history.anchor_at(1);
        c.core.own_nullifier_nonmembership = [Some(history.nullifier_tree_at(1).prove_non_membership(sn))];
        assert!(!satisfied(c));
    }

    #[test]
    fn value_must_be_conserved() {
        let mut c = genesis_circuit();
        let mut bigger = c.core.output_coins[0].clone().unwrap();
        bigger.value += 1;
        c.core.output_commitments = Some(pad_outputs(&[bigger.commitment()]));
        c.core.output_coins[0] = Some(bigger);
        assert!(!satisfied(c));
    }

    /// The inflation bug this guards against: an inactive output slot's public
    /// commitment used to be unconstrained, so a spender could publish any coin
    /// there without its value ever counting towards conservation.
    #[test]
    fn phantom_commitment_in_an_inactive_output_slot_fails() {
        let mut c = genesis_circuit();
        assert!(c.core.output_coins[1].is_none());
        let real = c.core.output_commitments.unwrap()[0];
        let phantom = coin(9, 1000, owner(9).1).commitment();
        c.core.output_commitments = Some([real, phantom]);
        assert!(!satisfied(c));
    }

    #[test]
    fn marking_a_real_valued_slot_inactive_cannot_mint_value() {
        // A dishonest prover sets is_active=false for a slot that still
        // carries a nonzero value, hoping the value silently counts toward
        // the sum without any nullifier/parent backing it. `value_or_zero`
        // zeroes an inactive slot's contribution regardless of the witnessed
        // `value` field.
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
    }

    // ---- circuit shape ---------------------------------------------------------

    /// GM17 keys are generated from setup mode, so the constraint system must
    /// have the same shape whatever the witness says: spend mode or fold mode,
    /// an empty window or a full one, and no witness at all.
    #[test]
    fn constraint_shape_does_not_depend_on_the_witness() {
        let count = |circuit: SpendStepCircuit, setup: bool| {
            let cs = if setup { setup_mode_cs() } else { ConstraintSystem::<Fr>::new_ref() };
            circuit.generate_constraints(cs.clone()).unwrap();
            cs.num_constraints()
        };
        let expected = count(step_circuit_for_counting(), true);

        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1);
        for seed in 0..2 {
            w.history.append(&junk_copy(w.alice_nullifier(), seed + 1));
        }
        let slot = w.history.append(&alice.entry);
        let (witness, _) = w.witness_for(slot, &alice);
        let previous = StepStatement { public_values: alice.pv.clone(), window_head: Fr::from(0u64), vk_hash: Fr::from(0u64) };
        let occurrence = witness.window.occurrences[0].clone();

        // Dummy proofs: unsatisfied, but the shape is what's being compared.
        let spend = SpendStepCircuit {
            core: alice.core.clone(),
            input_parent_statements: [Some(previous.clone())],
            input_parents: [Some(witness.clone())],
            ..step_circuit_for_counting()
        };
        let fold = SpendStepCircuit {
            core: SpendCoreWitness::for_fold(&previous, occurrence.link(Fr::from(0u64)), Fr::from(0u64)),
            fold: Some(FoldWitness { vpk: alice.vpk, occurrence }),
            input_parent_statements: [Some(previous)],
            ..step_circuit_for_counting()
        };
        assert_eq!(count(spend, false), expected, "spend mode");
        assert_eq!(count(fold, false), expected, "fold mode");

        let genesis = |circuit: GenesisSpendCircuit, cs: ConstraintSystemRef<Fr>| {
            circuit.generate_constraints(cs.clone()).unwrap();
            cs.num_constraints()
        };
        assert_eq!(
            genesis(genesis_circuit(), ConstraintSystem::<Fr>::new_ref()),
            genesis(GenesisSpendCircuit::default(), setup_mode_cs()),
        );
    }

    /// Fold mode switches every spend check off, so its public values can be
    /// someone else's statement: here the core alone, as fold mode runs it, is
    /// satisfied with nothing but that statement.
    #[test]
    fn core_is_satisfiable_in_fold_mode() {
        let w = world();
        let alice = w.alice_spends(&w.bob_coin, 1);
        let previous = StepStatement { public_values: alice.pv.clone(), window_head: Fr::from(0u64), vk_hash: Fr::from(0u64) };
        let core = SpendCoreWitness::for_fold(&previous, Fr::from(5u64), Fr::from(0u64));
        let cs = ConstraintSystem::<Fr>::new_ref();
        synthesize_core(cs.clone(), &core, &Boolean::FALSE).unwrap();
        assert!(cs.is_satisfied().unwrap());

        // Whereas spend mode refuses a non-zero window head.
        let mut spend = alice.core.clone();
        spend.window_head = Some(Fr::from(5u64));
        let cs = ConstraintSystem::<Fr>::new_ref();
        synthesize_core(cs.clone(), &spend, &Boolean::TRUE).unwrap();
        assert!(!cs.is_satisfied().unwrap());
    }

    // ---- costs -----------------------------------------------------------------

    /// A verifying key of the right shape. Synthesis only needs that, so the
    /// constraint count doesn't require any setup or proving.
    fn shaped_wrap_vk() -> VerifyingKey<MNT6_753> {
        let g1 = ark_mnt6_753::G1Projective::generator().into_affine();
        let g2 = ark_mnt6_753::G2Projective::generator().into_affine();
        VerifyingKey {
            h_g2: g2,
            g_alpha_g1: g1,
            h_beta_g2: g2,
            g_gamma_g1: g1,
            h_gamma_g2: g2,
            query: vec![g1; SPEND_PUBLIC_INPUT_COUNT * chunks_per_value() + 1],
        }
    }

    fn step_circuit_for_counting() -> SpendStepCircuit {
        SpendStepCircuit {
            core: SpendCoreWitness::default(),
            fold: None,
            wrap_vk: shaped_wrap_vk(),
            genesis_vk_hash: Fr::from(0u64),
            input_parent_proofs: std::array::from_fn(|_| Some(SpendStepCircuit::dummy_wrap_proof())),
            input_parent_statements: std::array::from_fn(|_| None),
            input_parents: std::array::from_fn(|_| None),
        }
    }

    fn setup_mode_cs() -> ConstraintSystemRef<Fr> {
        let cs = ConstraintSystem::<Fr>::new_ref();
        cs.set_mode(SynthesisMode::Setup);
        cs
    }

    /// Prints what the fix costs, per spend: `cargo test --release
    /// report_constraint_costs -- --nocapture`. Setup-mode synthesis only.
    #[test]
    fn report_constraint_costs() {
        let cs = setup_mode_cs();
        let vpk = CoinKeyVar::new_witness(cs.clone(), None).unwrap();
        let msg = Fp::new_witness(cs.clone(), || Ok(Fr::from(0u64))).unwrap();
        let before = cs.num_constraints();
        let _ = CoinSignatureVar::new_witness(cs.clone(), None).unwrap().verify(cs.clone(), &vpk, &msg).unwrap();
        let signature = cs.num_constraints() - before;

        let zero_pv = |cs: &ConstraintSystemRef<Fr>| {
            let zero = || Fp::new_witness(cs.clone(), || Ok(Fr::from(0u64))).unwrap();
            ParentPublicVars {
                output_commitments: (0..MAX_OUTPUTS).map(|_| zero()).collect(),
                anchor_size: zero(),
                anchor_board_root: zero(),
                anchor_nullifier_root: zero(),
                nullifier: zero(),
                vpk_hash: zero(),
                window_head: zero(),
                vk_hash: zero(),
            }
        };
        let fold_pv = zero_pv(&cs);
        let before = cs.num_constraints();
        let _ = fold_step(cs.clone(), None, &fold_pv).unwrap();
        let fold = cs.num_constraints() - before;
        let before = cs.num_constraints();
        let _ = window_opens(cs.clone(), &msg, &msg, &msg, None).unwrap();
        let window = cs.num_constraints() - before;

        let parent_cs = setup_mode_cs();
        let pv = zero_pv(&parent_cs);
        let zero = || Fp::new_witness(parent_cs.clone(), || Ok(Fr::from(0u64))).unwrap();
        let root = zero();
        let before = parent_cs.num_constraints();
        let _ = parent_checks(parent_cs.clone(), None, &pv, &root, &root).unwrap();
        let parent = parent_cs.num_constraints() - before;

        let genesis_cs = setup_mode_cs();
        GenesisSpendCircuit::default().generate_constraints(genesis_cs.clone()).unwrap();

        let step_cs = setup_mode_cs();
        step_circuit_for_counting().generate_constraints(step_cs.clone()).unwrap();

        println!("one signature check:    {signature}");
        println!("one fold step:          {fold}");
        println!("window opening:         {window}");
        println!("parent checks in total: {parent}");
        println!("GenesisSpendCircuit:    {}", genesis_cs.num_constraints());
        println!("SpendStepCircuit:       {}", step_cs.num_constraints());
        println!("public inputs:          {SPEND_PUBLIC_INPUT_COUNT}");
    }

    /// Where the spend circuit's matrix nonzeros come from.
    #[test]
    fn report_spend_density() {
        fn report(name: &str, build: impl FnOnce(ConstraintSystemRef<Fr>)) {
            let cs = setup_mode_cs();
            build(cs.clone());
            cs.finalize();
            let m = cs.to_matrices().unwrap();
            println!(
                "{name:<28} constraints {:>7}  nonzeros A {:>9} B {:>9} C {:>8}",
                cs.num_constraints(),
                m.a_num_non_zero,
                m.b_num_non_zero,
                m.c_num_non_zero
            );
        }
        report("poseidon, 2 elements", |cs| {
            let xs: Vec<Fp> = (0..2).map(|_| Fp::new_witness(cs.clone(), || Ok(Fr::from(1u64))).unwrap()).collect();
            let _ = poseidon_hash_var(cs, &xs).unwrap();
        });
        report("GenesisSpendCircuit", |cs| GenesisSpendCircuit::default().generate_constraints(cs).unwrap());
        report("SpendStepCircuit", |cs| step_circuit_for_counting().generate_constraints(cs).unwrap());
    }

    /// Measurement only, for choosing a batch size: a fold circuit with `b`
    /// occurrence slots, built from the same pieces as `SpendStepCircuit`'s
    /// fold mode (recursive verification, statement copy) but with the key,
    /// the outputs hash and the statement shared across slots. Not used to
    /// prove anything.
    fn batched_fold_skeleton(cs: ConstraintSystemRef<Fr>, b: usize) {
        let inputs: Vec<Fp> =
            (0..SPEND_PUBLIC_INPUT_COUNT).map(|_| Fp::new_input(cs.clone(), || Ok(Fr::from(0u64))).unwrap()).collect();

        let pvk = VerifyingKeyVar::<MNT6_753, MNT6PairingVar>::new_constant(cs.clone(), shaped_wrap_vk())
            .unwrap()
            .prepare()
            .unwrap();
        let cpv = chunks_per_value();
        let bits: Vec<Vec<Boolean<Fr>>> = (0..SPEND_PUBLIC_INPUT_COUNT * cpv)
            .map(|_| (0..CHUNK_BITS).map(|_| Boolean::new_witness(cs.clone(), || Ok(false)).unwrap()).collect())
            .collect();
        let proof = ProofVar::<MNT6_753, MNT6PairingVar>::new_witness(cs.clone(), || {
            Ok(SpendStepCircuit::dummy_wrap_proof())
        })
        .unwrap();
        let ok = GM17VerifierGadget::<MNT6_753, MNT6PairingVar>::verify_with_processed_vk(
            &pvk,
            &BooleanInputVar::<Fr6, Fr>::new(bits.clone()),
            &proof,
        )
        .unwrap();
        ok.enforce_equal(&Boolean::TRUE).unwrap();
        let group = |idx: usize| combine_chunks_var(&bits[idx * cpv..(idx + 1) * cpv]).unwrap();
        let pv = ParentPublicVars {
            output_commitments: (0..MAX_OUTPUTS).map(|j| group(PARENT_OUTPUT_COMMITMENTS_START + j)).collect(),
            anchor_size: group(PARENT_ANCHOR_SIZE),
            anchor_board_root: group(PARENT_ANCHOR_BOARD_ROOT),
            anchor_nullifier_root: group(PARENT_ANCHOR_NULLIFIER_ROOT),
            nullifier: group(PARENT_NULLIFIER),
            vpk_hash: group(PARENT_VPK_HASH),
            window_head: group(PARENT_WINDOW_HEAD),
            vk_hash: group(PARENT_VK_HASH),
        };
        for (mine, theirs) in inputs.iter().zip(pv.statement()) {
            mine.enforce_equal(&theirs).unwrap();
        }

        // Shared across slots.
        let vpk = CoinKeyVar::new_witness(cs.clone(), None).unwrap();
        vpk.hash(cs.clone()).unwrap().enforce_equal(&pv.vpk_hash).unwrap();
        let outputs_hash = poseidon_hash_var(cs.clone(), &pv.output_commitments).unwrap();

        // Per slot: a prefix of active slots, each linked and checked.
        let mut head = pv.window_head.clone();
        let mut previous_active = Boolean::TRUE;
        for _ in 0..b {
            let active = Boolean::new_witness(cs.clone(), || Ok(true)).unwrap();
            (&!active.clone() | &previous_active).enforce_equal(&Boolean::TRUE).unwrap();
            previous_active = active.clone();
            let occ_outputs_hash = alloc_fp(cs.clone(), None).unwrap();
            let occ_ciphertext = alloc_fp(cs.clone(), None).unwrap();
            let occ_signature = CoinSignatureVar::new_witness(cs.clone(), None).unwrap();
            let msg = signature_message_var(cs.clone(), &pv.nullifier, &occ_outputs_hash, &occ_ciphertext).unwrap();
            let valid = occ_signature.verify(cs.clone(), &vpk, &msg).unwrap();
            let harmless = &occ_outputs_hash.is_eq(&outputs_hash).unwrap() | &!valid;
            gate(harmless, &active).enforce_equal(&Boolean::TRUE).unwrap();
            let linked =
                occurrence_link_var(cs.clone(), &head, &occ_outputs_hash, &occ_ciphertext, &occ_signature).unwrap();
            head = Fp::conditionally_select(&active, &linked, &head).unwrap();
        }
        head.enforce_equal(&inputs[PARENT_WINDOW_HEAD]).unwrap();
    }

    /// `cargo test --release report_batched_fold_costs -- --nocapture`.
    #[test]
    fn report_batched_fold_costs() {
        for b in [1usize, 2, 4, 8, 16, 32] {
            let cs = setup_mode_cs();
            batched_fold_skeleton(cs.clone(), b);
            cs.finalize();
            let m = cs.to_matrices().unwrap();
            println!(
                "B={b:<3} constraints {:>8}  nonzeros A {:>9} B {:>9} C {:>8}  total {:>9}",
                cs.num_constraints(),
                m.a_num_non_zero,
                m.b_num_non_zero,
                m.c_num_non_zero,
                m.a_num_non_zero + m.b_num_non_zero + m.c_num_non_zero,
            );
        }
        for (name, build) in [
            ("GenesisSpendCircuit", Box::new(|cs: ConstraintSystemRef<Fr>| GenesisSpendCircuit::default().generate_constraints(cs).unwrap()) as Box<dyn Fn(ConstraintSystemRef<Fr>)>),
            ("SpendStepCircuit", Box::new(|cs: ConstraintSystemRef<Fr>| step_circuit_for_counting().generate_constraints(cs).unwrap())),
        ] {
            let cs = setup_mode_cs();
            build(cs.clone());
            cs.finalize();
            let m = cs.to_matrices().unwrap();
            println!(
                "{name:<20} constraints {:>8}  nonzeros total {:>9}",
                cs.num_constraints(),
                m.a_num_non_zero + m.b_num_non_zero + m.c_num_non_zero,
            );
        }
    }

    /// Phase 4 spike: what the recursive verifier costs with the wrap VK as a
    /// witness (needed for a universal VK) instead of a constant, and with each
    /// public-input chunk fed in as its full width or only the 200 bits the wrap
    /// circuit already guarantees. `cargo test --release report_verifier_costs
    /// -- --nocapture`. Setup-mode synthesis only.
    #[test]
    fn report_verifier_costs() {
        use ark_crypto_primitives::snark::SNARKGadget;
        use ark_r1cs_std::alloc::AllocationMode;
        let chunks = SPEND_PUBLIC_INPUT_COUNT * chunks_per_value();
        for witness_vk in [false, true] {
            for bits_per_chunk in [Fr6::MODULUS_BIT_SIZE as usize, cloakkchain_circuit_wrap::CHUNK_BITS] {
                let cs = setup_mode_cs();
                let vk = if witness_vk {
                    GM17VerifierGadget::<MNT6_753, MNT6PairingVar>::new_verification_key_unchecked(
                        cs.clone(),
                        || Ok(shaped_wrap_vk()),
                        AllocationMode::Witness,
                    )
                    .unwrap()
                } else {
                    VerifyingKeyVar::<MNT6_753, MNT6PairingVar>::new_constant(cs.clone(), shaped_wrap_vk()).unwrap()
                };
                let after_vk = cs.num_constraints();
                let pvk = vk.prepare().unwrap();
                let after_prepare = cs.num_constraints();
                let bits: Vec<Vec<Boolean<Fr>>> = (0..chunks)
                    .map(|_| (0..bits_per_chunk).map(|_| Boolean::new_witness(cs.clone(), || Ok(false)).unwrap()).collect())
                    .collect();
                let input = BooleanInputVar::<Fr6, Fr>::new(bits);
                let proof = ProofVar::<MNT6_753, MNT6PairingVar>::new_witness(cs.clone(), || {
                    Ok(SpendStepCircuit::dummy_wrap_proof())
                })
                .unwrap();
                let before_verify = cs.num_constraints();
                let _ = GM17VerifierGadget::<MNT6_753, MNT6PairingVar>::verify_with_processed_vk(&pvk, &input, &proof)
                    .unwrap();
                println!(
                    "vk {:<8} {:>3}-bit chunks: alloc {:>7}  prepare {:>7}  verify {:>8}  total {:>8}",
                    if witness_vk { "witness" } else { "constant" },
                    bits_per_chunk,
                    after_vk,
                    after_prepare - after_vk,
                    cs.num_constraints() - before_verify,
                    cs.num_constraints(),
                );
            }
        }
    }

    // ---- real proving (see the module comment) --------------------------------

    struct Wrapped {
        proof: Proof<MNT6_753>,
    }

    fn wrap<R: RngCore + CryptoRng>(
        wrap_pk: &ProvingKey<MNT6_753>,
        inner_vk: VerifyingKey<MNT4_753>,
        inner_proof: Proof<MNT4_753>,
        public_inputs: [Fr; SPEND_PUBLIC_INPUT_COUNT],
        rng: &mut R,
    ) -> Wrapped {
        let proof = cloakkchain_circuit_wrap::prove::<SPEND_PUBLIC_INPUT_COUNT, _>(
            wrap_pk,
            cloakkchain_circuit_wrap::WrapCircuit::<SPEND_PUBLIC_INPUT_COUNT> {
                inner_vk,
                inner_proof: Some(inner_proof),
                inner_public_inputs: Some(public_inputs),
            },
            rng,
        )
        .unwrap();
        Wrapped { proof }
    }

    #[test]
    fn proving_genesis_round_trip() {
        // `ark_std::test_rng()` is deterministic but deliberately doesn't
        // implement `CryptoRng` (it's not a CSPRNG) — `GM17::setup`/
        // `prove` require `CryptoRng`, so use a seeded `StdRng` instead.
        use ark_std::rand::{rngs::StdRng, SeedableRng};
        let mut rng = StdRng::seed_from_u64(42);
        let (pk, vk) = setup(&mut rng).unwrap();

        let c = genesis_circuit();
        let public_inputs = spend_public_inputs(&c.core.public_values().unwrap(), Fr::from(0u64), Fr::from(0u64));
        let proof = prove(&pk, c, &mut rng).unwrap();
        assert!(verify(&vk, &public_inputs, &proof).unwrap(), "a genuinely valid genesis-mint proof must verify");

        let mut tampered = public_inputs;
        tampered[0] += Fr::from(1u64); // perturb output_commitments[0]
        assert!(!verify(&vk, &tampered, &proof).unwrap(), "a proof must not verify against the wrong public inputs");
    }

    /// Full chain, real GM17 proofs end to end, under the reviewers' attack
    /// past the old bound: three copies of Alice's serial number land before
    /// her carrier, and Bob folds each of them before spending onward to Carol.
    ///
    /// One setup of each circuit for the whole chain: spends and folds share a
    /// proving key, and each verifies proofs made under that same key.
    #[test]
    fn proving_chain_survives_copied_serial_numbers() {
        use ark_std::rand::{rngs::StdRng, SeedableRng};
        use cloakkchain_circuit_wrap::inner_vk_hash;
        const COPIES: u64 = 3;
        let mut rng = StdRng::seed_from_u64(20260919);

        let (genesis_pk_data, genesis_vk) = setup(&mut rng).unwrap();
        let (wrap_pk, wrap_vk) = cloakkchain_circuit_wrap::setup::<SPEND_PUBLIC_INPUT_COUNT, _>(&mut rng).unwrap();
        let genesis_vk_hash = inner_vk_hash(&genesis_vk);
        let (step_pk, step_vk) = setup_non_genesis(wrap_vk.clone(), genesis_vk_hash, &mut rng).unwrap();
        let step_vk_hash = inner_vk_hash(&step_vk);

        let satisfied = |circuit: &SpendStepCircuit| {
            let cs = ConstraintSystem::<Fr>::new_ref();
            circuit.clone().generate_constraints(cs.clone()).unwrap();
            cs.is_satisfied().unwrap()
        };
        // Prove a step-circuit witness, check it, and wrap it for the next step.
        let prove_step = |circuit: SpendStepCircuit, statement: &StepStatement, rng: &mut StdRng| {
            assert!(satisfied(&circuit), "witness must satisfy every constraint");
            let proof = prove_non_genesis(&step_pk, circuit, rng).unwrap();
            assert!(verify_non_genesis(&step_vk, &statement.public_inputs(), &proof).unwrap());
            wrap(&wrap_pk, step_vk.clone(), proof, statement.public_inputs(), rng)
        };

        let mut w = world();
        let mut genesis_core = w.genesis.core.clone();
        genesis_core.vk_hash = Some(genesis_vk_hash);
        let genesis_statement =
            StepStatement { public_values: w.genesis.pv.clone(), window_head: Fr::from(0u64), vk_hash: genesis_vk_hash };
        let genesis_proof = prove(&genesis_pk_data, GenesisSpendCircuit { core: genesis_core }, &mut rng).unwrap();
        assert!(verify(&genesis_vk, &genesis_statement.public_inputs(), &genesis_proof).unwrap());
        let wrap_genesis = wrap(&wrap_pk, genesis_vk, genesis_proof, genesis_statement.public_inputs(), &mut rng);
        assert!(cloakkchain_circuit_wrap::verify(
            &wrap_vk,
            &public_input_chunks(&genesis_statement.public_inputs()),
            &wrap_genesis.proof
        )
        .unwrap());

        // Alice proves at anchor 1, then copies of her SN get ordered first.
        let alice = w.alice_spends(&w.bob_coin, 1);
        let mut alice_core = alice.core.clone();
        alice_core.vk_hash = Some(step_vk_hash);
        let alice_statement =
            StepStatement { public_values: alice.pv.clone(), window_head: Fr::from(0u64), vk_hash: step_vk_hash };
        let alice_circuit = SpendStepCircuit {
            core: alice_core,
            fold: None,
            wrap_vk: wrap_vk.clone(),
            genesis_vk_hash,
            input_parent_proofs: [Some(wrap_genesis.proof.clone())],
            input_parent_statements: [Some(genesis_statement)],
            input_parents: [Some(w.history.parent_witness(0, &w.genesis.pv, &w.genesis.vpk, 1))],
        };

        // A spend can't treat a parent's VK as acceptable unless it's genesis's
        // or its own.
        let mut wrong_genesis = alice_circuit.clone();
        wrong_genesis.genesis_vk_hash += Fr::from(1u64);
        assert!(!satisfied(&wrong_genesis), "a parent under an unexpected VK must fail");

        let mut latest = prove_step(alice_circuit, &alice_statement, &mut rng);
        let mut latest_statement = alice_statement;

        for seed in 0..COPIES {
            w.history.append(&junk_copy(w.alice_nullifier(), seed + 1));
        }
        let slot = w.history.append(&alice.entry);
        let size = w.history.len();
        let parent = w.history.parent_witness(slot, &alice.pv, &alice.vpk, size);
        assert_eq!(parent.window.occurrences.len() as u64, COPIES);

        // Bob folds each copy into Alice's statement, one proof per copy.
        for occurrence in &parent.window.occurrences {
            let next = StepStatement {
                window_head: occurrence.link(latest_statement.window_head),
                ..latest_statement.clone()
            };
            let fold = SpendStepCircuit {
                core: SpendCoreWitness::for_fold(&latest_statement, next.window_head, step_vk_hash),
                fold: Some(FoldWitness { vpk: alice.vpk, occurrence: occurrence.clone() }),
                wrap_vk: wrap_vk.clone(),
                genesis_vk_hash,
                input_parent_proofs: [Some(latest.proof.clone())],
                input_parent_statements: [Some(latest_statement.clone())],
                input_parents: [None],
            };
            latest = prove_step(fold, &next, &mut rng);
            latest_statement = next;
        }
        assert_eq!(latest_statement.window_head, parent.window.leaf.occ);

        // Bob spends onward to Carol, verifying the last fold.
        let (_, carol_pk) = owner(3);
        let bob = post(&w.history, w.bob_sk, &w.bob_coin, &[coin(4, 100, carol_pk)], size, Some(&parent), 2);
        let mut bob_core = bob.core.clone();
        bob_core.vk_hash = Some(step_vk_hash);
        let bob_statement = StepStatement { public_values: bob.pv.clone(), window_head: Fr::from(0u64), vk_hash: step_vk_hash };
        let bob_circuit = SpendStepCircuit {
            core: bob_core,
            fold: None,
            wrap_vk,
            genesis_vk_hash,
            input_parent_proofs: [Some(latest.proof.clone())],
            input_parent_statements: [Some(latest_statement.clone())],
            input_parents: [Some(parent.clone())],
        };

        // Skipping the last fold doesn't work: the head must cover every copy.
        let mut unfolded = bob_circuit.clone();
        unfolded.input_parent_statements[0].as_mut().unwrap().window_head = Fr::from(0u64);
        assert!(!satisfied(&unfolded), "a window head that misses copies must fail");

        assert!(satisfied(&bob_circuit), "Bob's witness should satisfy every constraint");
        let bob_proof = prove_non_genesis(&step_pk, bob_circuit, &mut rng).unwrap();
        assert!(verify_non_genesis(&step_vk, &bob_statement.public_inputs(), &bob_proof).unwrap());
        let mut tampered = bob_statement.public_inputs();
        tampered[0] += Fr::from(1u64);
        assert!(!verify_non_genesis(&step_vk, &tampered, &bob_proof).unwrap());
    }
}
