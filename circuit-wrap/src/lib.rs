//! Generic "wrap" circuit: recursively verifies an MNT4-753 (`Fr4`-native)
//! GM17 proof against a fixed, compile-time-known verifying key, and
//! re-exposes each of its `N` public inputs as its own public output —
//! losslessly, via a fixed per-value chunking scheme, rather than relying on
//! `BooleanInputVar`'s own capacity-based repacking (which concatenates all
//! `N` values into one bit stream before rechunking, interleaving value
//! boundaries in a way that's expensive to invert on the far side of the
//! next recursion hop).
//!
//! This is the curve-cycle "translation layer" the MNT-native port plan
//! settled on after discovering that putting real business logic (Merkle /
//! nullifier-tree work) on the "wrap" side makes every hash foreign-field —
//! the same cost class the `mnt_native_experiment` measured as catastrophic
//! for SHA256-in-R1CS. Business logic instead stays entirely native (see
//! `circuit-spend`); this circuit does no hashing of
//! application data at all, only pairing-based proof verification plus
//! bit-repacking — mirroring the "inner does the real work, outer is a thin
//! composition layer" pattern the experiment's own inner/outer measurements
//! validated as cheap and roughly fixed-cost regardless of inner complexity.
//!
//! **One verifying key for every generation.** The inner VK is a *witness*, not
//! a constant, so this circuit doesn't depend on the circuit it wraps. That is
//! what breaks the cycle in recursion: a spend circuit can embed this circuit's
//! VK as a constant, while this one verifies that spend circuit's proofs without
//! embedding its VK in turn. The price is that the VK must be pinned another
//! way: by convention the inner proof's *last* public input is the hash of the
//! VK it claims to verify under ([`inner_vk_hash`]), and this circuit enforces
//! that. The spend circuit then checks the hash it reads back is an expected one.

use ark_crypto_primitives::snark::SNARKGadget;
use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar, poseidon::constraints::PoseidonSpongeVar, poseidon::PoseidonSponge,
    CryptographicSponge, FieldBasedCryptographicSponge,
};
use ark_ff::{BigInteger, Field, PrimeField};
pub mod snark;

use snark::{PreparedVerifyingKeyVar, Proof, ProofVar, ProvingKey, Snark, VerifierGadget, VerifyingKey};
use ark_mnt4_753::MNT4_753;
use ark_mnt6_753::MNT6_753;
use ark_ec::short_weierstrass::SWCurveConfig;
use ark_r1cs_std::{
    alloc::AllocationMode,
    fields::fp::FpVar,
    groups::curves::short_weierstrass::{non_zero_affine::NonZeroAffineVar, ProjectiveVar},
    pairing::PairingVar,
    prelude::*,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_snark::SNARK;
use ark_std::rand::{CryptoRng, RngCore};
use cloakkchain_lib::{poseidon_params, Fr as Fr4};

pub type Fr6 = ark_mnt6_753::Fr;
type Fp6 = FpVar<Fr6>;
type MNT4PairingVar = ark_mnt4_753::constraints::PairingVar;

/// Bits per chunk when splitting an `Fr4` value for lossless pass-through —
/// small enough to be an unambiguous non-negative integer in either `Fr4` or
/// `Fr6` (both ~753-bit fields), so a chunk value round-trips exactly
/// regardless of which field currently holds it.
pub const CHUNK_BITS: usize = 200;

/// How many `CHUNK_BITS`-sized chunks one `Fr4` value splits into — derived
/// from `Fr4::MODULUS_BIT_SIZE` rather than hardcoded, so it can't silently
/// drift out of sync with the field.
pub fn chunks_per_value() -> usize {
    (Fr4::MODULUS_BIT_SIZE as usize).div_ceil(CHUNK_BITS)
}

fn opt<T: Clone>(o: &Option<T>) -> Result<T, SynthesisError> {
    o.clone().ok_or(SynthesisError::AssignmentMissing)
}

/// `bits · base` for a base that is a witness, as `ark-r1cs-std`'s
/// `scalar_mul_le` computes it, but with matrices orders of magnitude sparser.
///
/// The library's version leaves each doubling's coordinates as linear
/// combinations of the previous ones (`x' = λ² − 2x`, `y' = λ(x − x') − y`), so
/// after hundreds of doublings a single row can hold hundreds of terms. For a
/// constant base that costs nothing, since doubling a constant is a constant.
/// For a witness base it made the wrap circuit's matrices 25 times denser than
/// its constraint count suggests, and prover time and memory follow nonzeros.
/// Here each doubled point is re-allocated, at one constraint per coordinate.
///
/// Otherwise it's the library algorithm step for step, so its completeness
/// argument carries over: incomplete affine additions on the low
/// `MODULUS_BIT_SIZE − 2` bits, where the accumulator `k·a` has `2 ≤ k < p − 1`
/// and so never equals `±` the point being added; complete projective additions
/// after that; and the base at infinity handled by substituting the generator
/// and selecting zero at the end. Takes at most `MODULUS_BIT_SIZE` bits.
pub fn scalar_mul_le_compact<P: SWCurveConfig>(
    base: &ProjectiveVar<P, FpVar<P::BaseField>>,
    bits: &[Boolean<P::BaseField>],
) -> Result<ProjectiveVar<P, FpVar<P::BaseField>>, SynthesisError>
where
    P::BaseField: PrimeField,
{
    type Point<P> = ProjectiveVar<P, FpVar<<P as ark_ec::CurveConfig>::BaseField>>;
    let scalar_bits = <P::ScalarField as PrimeField>::MODULUS_BIT_SIZE as usize;
    assert!(bits.len() <= scalar_bits, "one chunk of scalar bits at most");
    if bits.is_empty() {
        return Ok(Point::<P>::zero());
    }

    let cs = base.cs();
    let compact = |p: NonZeroAffineVar<P, FpVar<P::BaseField>>| -> Result<_, SynthesisError> {
        if p.x.is_constant() && p.y.is_constant() {
            return Ok(p);
        }
        let x = FpVar::new_witness(cs.clone(), || p.x.value())?;
        let y = FpVar::new_witness(cs.clone(), || p.y.value())?;
        x.enforce_equal(&p.x)?;
        y.enforce_equal(&p.y)?;
        Ok(NonZeroAffineVar::new(x, y))
    };

    let affine = base.to_affine()?;
    let infinity = affine.infinity;
    let x = infinity.select(&FpVar::constant(P::GENERATOR.x), &affine.x)?;
    let y = infinity.select(&FpVar::constant(P::GENERATOR.y), &affine.y)?;
    let mut power = NonZeroAffineVar::new(x, y);

    // Start the accumulator at `base`, as if the low bit were set, and correct
    // for it after the incomplete part.
    let mut accumulator = power.clone();
    let initial = accumulator.into_projective();
    power = compact(power.double()?)?;

    let split = (scalar_bits - 2).min(bits.len());
    for bit in &bits[1..split] {
        let sum = accumulator.add_unchecked(&power)?;
        accumulator = bit.select(&sum, &accumulator)?;
        power = compact(power.double()?)?;
    }
    let mut result = accumulator.into_projective() - bits[0].select(&Point::<P>::zero(), &initial)?;

    for bit in &bits[split..] {
        let sum = &result + &power.into_projective();
        result = bit.select(&sum, &result)?;
        power = compact(power.double()?)?;
    }
    infinity.select(&Point::<P>::zero(), &result)
}

/// Verification of an MNT4-753 proof, as the proof system's own gadget does it,
/// except that the public-input sum uses [`scalar_mul_le_compact`]: with a
/// witness VK, the input bases are witnesses, and the gadget's own sum was by
/// far the densest part of this circuit. One version per proof system, since
/// each follows its own verification equation.
#[cfg(not(feature = "groth16"))]
fn verify_mnt4(
    pvk: &PreparedVerifyingKeyVar<MNT4_753, MNT4PairingVar>,
    inputs: &[Vec<Boolean<Fr6>>],
    proof: &ProofVar<MNT4_753, MNT4PairingVar>,
) -> Result<Boolean<Fr6>, SynthesisError> {
    assert_eq!(inputs.len() + 1, pvk.query.len());
    let mut g_psi = pvk.query[0].clone();
    for (bits, base) in inputs.iter().zip(&pvk.query[1..]) {
        g_psi += scalar_mul_le_compact(base, bits)?;
    }

    let test1_a_g_alpha = (proof.a.clone() + &pvk.g_alpha).negate()?;
    let test1_b_h_beta = proof.b.clone() + &pvk.h_beta;
    let test1 = MNT4PairingVar::final_exponentiation(&MNT4PairingVar::miller_loop(
        &[
            MNT4PairingVar::prepare_g1(&test1_a_g_alpha)?,
            MNT4PairingVar::prepare_g1(&g_psi)?,
            MNT4PairingVar::prepare_g1(&proof.c)?,
            pvk.g_alpha_pc.clone(),
        ],
        &[
            MNT4PairingVar::prepare_g2(&test1_b_h_beta)?,
            pvk.h_gamma_pc.clone(),
            pvk.h_pc.clone(),
            pvk.h_beta_pc.clone(),
        ],
    )?)?;
    let test2 = MNT4PairingVar::final_exponentiation(&MNT4PairingVar::miller_loop(
        &[MNT4PairingVar::prepare_g1(&proof.a)?, pvk.g_gamma_pc.clone()],
        &[pvk.h_gamma_pc.clone(), MNT4PairingVar::prepare_g2(&proof.b.negate()?)?],
    )?)?;
    let one = <MNT4PairingVar as PairingVar<MNT4_753>>::GTVar::one();
    Ok(&test1.is_eq(&one)? & &test2.is_eq(&one)?)
}

/// See the GM17 version above. Groth16's single check:
/// `e(A, B) · e(Σ xᵢ·γᵢ, −γ) · e(C, −δ) == e(α, β)`.
#[cfg(feature = "groth16")]
fn verify_mnt4(
    pvk: &PreparedVerifyingKeyVar<MNT4_753, MNT4PairingVar>,
    inputs: &[Vec<Boolean<Fr6>>],
    proof: &ProofVar<MNT4_753, MNT4PairingVar>,
) -> Result<Boolean<Fr6>, SynthesisError> {
    assert_eq!(inputs.len() + 1, pvk.gamma_abc_g1.len());
    let mut g_ic = pvk.gamma_abc_g1[0].clone();
    for (bits, base) in inputs.iter().zip(&pvk.gamma_abc_g1[1..]) {
        g_ic += scalar_mul_le_compact(base, bits)?;
    }
    let test = MNT4PairingVar::final_exponentiation(&MNT4PairingVar::miller_loop(
        &[
            MNT4PairingVar::prepare_g1(&proof.a)?,
            MNT4PairingVar::prepare_g1(&g_ic)?,
            MNT4PairingVar::prepare_g1(&proof.c)?,
        ],
        &[MNT4PairingVar::prepare_g2(&proof.b)?, pvk.gamma_g2_neg_pc.clone(), pvk.delta_g2_neg_pc.clone()],
    )?)?;
    test.is_eq(&pvk.alpha_g1_beta_g2)
}

/// Bits of the Poseidon digest kept as a VK's hash: few enough that the value
/// fits below `Fr4`'s modulus, so it can be the inner proof's public input, and
/// still 300-bit collision resistance.
pub const VK_HASH_BITS: usize = 600;

/// A VK's points as `Fr6` elements — MNT4-753's base field is MNT6-753's
/// scalar field, so its point coordinates are native here. `G1` points give
/// `x, y`; `G2` points, over a quadratic extension, give `x.c0, x.c1, y.c0,
/// y.c1`. The order is part of the hash's definition.
fn vk_coordinates(vk: &VerifyingKey<MNT4_753>) -> Vec<Fr6> {
    let (g1s, g2s) = snark::vk_points(vk);
    let mut out = Vec::new();
    for g in g1s {
        out.extend([g.x, g.y]);
    }
    for g in g2s {
        out.extend([g.x.c0, g.x.c1, g.y.c0, g.y.c1]);
    }
    out
}

/// The hash an inner proof must carry as its last public input to be wrapped:
/// the low [`VK_HASH_BITS`] of a Poseidon digest of the VK's coordinates.
pub fn inner_vk_hash(vk: &VerifyingKey<MNT4_753>) -> Fr4 {
    let mut sponge = PoseidonSponge::new(&poseidon_params::mnt6_753_fr_poseidon_config());
    sponge.absorb(&vk_coordinates(vk));
    let digest: Fr6 = sponge.squeeze_native_field_elements(1)[0];
    let bits = &digest.into_bigint().to_bits_le()[..VK_HASH_BITS];
    Fr4::from_bigint(<Fr4 as PrimeField>::BigInt::from_bits_le(bits)).expect("600 bits are below the modulus")
}

/// Mirrors [`inner_vk_hash`], returning the digest's low [`VK_HASH_BITS`] bits.
fn inner_vk_hash_bits_var(
    cs: ConstraintSystemRef<Fr6>,
    vk: &snark::VerifyingKeyVar<MNT4_753, MNT4PairingVar>,
) -> Result<Vec<Boolean<Fr6>>, SynthesisError> {
    let (g1s, g2s) = snark::vk_var_points(vk);
    let mut coordinates = Vec::new();
    for g in g1s {
        let affine = g.to_affine()?;
        coordinates.extend([affine.x, affine.y]);
    }
    for g in g2s {
        let affine = g.to_affine()?;
        coordinates.extend([affine.x.c0, affine.x.c1, affine.y.c0, affine.y.c1]);
    }
    let mut sponge = PoseidonSpongeVar::new(cs, &poseidon_params::mnt6_753_fr_poseidon_config());
    sponge.absorb(&coordinates)?;
    let digest = sponge.squeeze_field_elements(1)?.remove(0);
    let mut bits = digest.to_bits_le()?;
    bits.truncate(VK_HASH_BITS);
    Ok(bits)
}

/// Recursively verifies an `N`-public-input MNT4-753 GM17 proof under any
/// verifying key, provided its last public input is that key's
/// [`inner_vk_hash`], re-exposing each public input as `chunks_per_value()`
/// small `Fr6` public inputs (`N * chunks_per_value()` total, in input
/// order, each value's chunks contiguous and low-chunk-first).
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct WrapCircuit<const N: usize> {
    /// A witness — see the module doc comment. Not `Option`: a verifying key
    /// isn't secret, and setup only needs one of the right shape.
    pub inner_vk: VerifyingKey<MNT4_753>,
    pub inner_proof: Option<Proof<MNT4_753>>,
    pub inner_public_inputs: Option<[Fr4; N]>,
}

impl<const N: usize> ConstraintSynthesizer<Fr6> for WrapCircuit<N> {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr6>) -> Result<(), SynthesisError> {
        // Witness each inner public value's full canonical bit decomposition
        // directly (bypassing `BooleanInputVar`'s own `AllocVar` impl, which
        // concatenates all N values into one stream before repacking) so we
        // keep full control over per-value boundaries.
        let bit_len = Fr4::MODULUS_BIT_SIZE as usize;
        let mut per_value_bits: Vec<Vec<Boolean<Fr6>>> = Vec::with_capacity(N);
        for i in 0..N {
            let value_bits: Option<Vec<bool>> =
                self.inner_public_inputs.as_ref().map(|v| v[i].into_bigint().to_bits_le());
            let bits: Vec<Boolean<Fr6>> = (0..bit_len)
                .map(|j| Boolean::new_witness(cs.clone(), || opt(&value_bits.as_ref().map(|b| b[j]))))
                .collect::<Result<_, _>>()?;
            per_value_bits.push(bits);
        }

        // Recursive GM17 verification of the inner (Fr4/MNT4-753) proof,
        // under a VK pinned by the inner proof's own last public input. That
        // input's bits must be exactly the hash's, high bits zero: so it's also
        // canonical, with no alias `v + p` to pass for it.
        let vk_var = VerifierGadget::<MNT4_753, MNT4PairingVar>::new_verification_key_unchecked(
            cs.clone(),
            || Ok(self.inner_vk.clone()),
            AllocationMode::Witness,
        )?;
        let hash_bits = inner_vk_hash_bits_var(cs.clone(), &vk_var)?;
        let claimed_bits = &per_value_bits[N - 1];
        for (claimed, actual) in claimed_bits.iter().zip(&hash_bits) {
            claimed.enforce_equal(actual)?;
        }
        for claimed in &claimed_bits[VK_HASH_BITS..] {
            claimed.enforce_equal(&Boolean::FALSE)?;
        }
        let proof_var = ProofVar::<MNT4_753, MNT4PairingVar>::new_witness(cs.clone(), || opt(&self.inner_proof))?;
        let pvk = vk_var.prepare()?;
        verify_mnt4(&pvk, &per_value_bits, &proof_var)?.enforce_equal(&Boolean::TRUE)?;

        // Re-expose each value losslessly as small public Fr6 inputs — see
        // the module doc comment for why not `BooleanInputVar`'s own
        // repacking.
        for bits in &per_value_bits {
            for chunk in bits.chunks(CHUNK_BITS) {
                let chunk_fp = Boolean::le_bits_to_fp(chunk)?;
                let public_chunk = Fp6::new_input(cs.clone(), || chunk_fp.value())?;
                chunk_fp.enforce_equal(&public_chunk)?;
            }
        }

        Ok(())
    }
}

/// Reassemble `chunks_per_value()` small `Fr4`-native bit-vectors (each
/// recovered, on the far side of the next recursion hop, from one of
/// `WrapCircuit`'s `Fr6` public-input chunks via a recursive verification of
/// *its* proof) back into the original `Fr4` value. Trusts that each chunk
/// is `< 2^CHUNK_BITS`, which `WrapCircuit`'s own proof already enforces —
/// soundness composes transitively, so no need to re-check bounds here.
pub fn combine_chunks_var(chunk_bits: &[Vec<Boolean<Fr4>>]) -> Result<FpVar<Fr4>, SynthesisError> {
    let base = Fr4::from(2u64).pow([CHUNK_BITS as u64]);
    let mut acc = FpVar::<Fr4>::zero();
    let mut place = FpVar::<Fr4>::one();
    for bits in chunk_bits {
        let low_bits = &bits[..CHUNK_BITS.min(bits.len())];
        let value = Boolean::le_bits_to_fp(low_bits)?;
        acc += &value * &place;
        place *= FpVar::<Fr4>::constant(base);
    }
    Ok(acc)
}

/// Host-side mirror of what `WrapCircuit<N>`'s constraints compute for the
/// public-input pass-through — used to build the `Vec<Fr6>` public-input
/// vector for `GM17::<MNT6_753>::verify`.
pub fn public_input_chunks(values: &[Fr4]) -> Vec<Fr6> {
    let bit_len = Fr4::MODULUS_BIT_SIZE as usize;
    let mut out = Vec::new();
    for v in values {
        let mut bits = v.into_bigint().to_bits_le();
        bits.truncate(bit_len);
        for chunk in bits.chunks(CHUNK_BITS) {
            let mut acc = Fr6::from(0u64);
            let mut place = Fr6::from(1u64);
            for &b in chunk {
                if b {
                    acc += place;
                }
                place *= Fr6::from(2u64);
            }
            out.push(acc);
        }
    }
    out
}

/// A verifying key of the shape an `N`-public-input inner circuit has. Setup
/// only needs the shape, since the inner VK is a witness.
pub fn shaped_inner_vk(n: usize) -> VerifyingKey<MNT4_753> {
    snark::shaped_vk::<MNT4_753>(n)
}

/// One setup serves every inner circuit with `N` public inputs, of every
/// generation — see the module doc comment.
pub fn setup<const N: usize, R: RngCore + CryptoRng>(
    rng: &mut R,
) -> Result<(ProvingKey<MNT6_753>, VerifyingKey<MNT6_753>), SynthesisError> {
    // Unlike a plain `FpVar`/`Boolean` witness, `ProofVar`'s `AllocVar` impl
    // calls its value closure *unconditionally* (it needs the concrete
    // `Proof { a, b, c }` to decompose into G1/G2 sub-allocations) — so
    // setup mode can't just skip it via `None`. Any structurally-valid
    // dummy proof works; setup mode never checks constraint satisfaction.
    let dummy_proof = Proof::<MNT4_753> {
        a: ark_mnt4_753::G1Affine::identity(),
        b: ark_mnt4_753::G2Affine::identity(),
        c: ark_mnt4_753::G1Affine::identity(),
    };
    let circuit = WrapCircuit::<N> { inner_vk: shaped_inner_vk(N), inner_proof: Some(dummy_proof), inner_public_inputs: None };
    Snark::<MNT6_753>::circuit_specific_setup(circuit, rng)
}

pub fn prove<const N: usize, R: RngCore + CryptoRng>(
    pk: &ProvingKey<MNT6_753>,
    circuit: WrapCircuit<N>,
    rng: &mut R,
) -> Result<Proof<MNT6_753>, SynthesisError> {
    Snark::<MNT6_753>::prove(pk, circuit, rng)
}

pub fn verify(
    vk: &VerifyingKey<MNT6_753>,
    public_inputs: &[Fr6],
    proof: &Proof<MNT6_753>,
) -> Result<bool, SynthesisError> {
    Snark::<MNT6_753>::verify(vk, public_inputs, proof)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(not(feature = "groth16"))]
    use ark_crypto_primitives::snark::BooleanInputVar;
    use ark_std::rand::{rngs::StdRng, SeedableRng};

    /// Same results as the library's `scalar_mul_le`, on the scalars at the
    /// edges of its incomplete additions and on a base at infinity, and stays
    /// satisfiable throughout.
    #[test]
    fn compact_scalar_mul_matches_the_library() {
        use ark_ec::{CurveGroup, PrimeGroup};
        use ark_relations::r1cs::ConstraintSystem;
        type G1Var = ark_mnt4_753::constraints::G1Var;
        let n = <ark_mnt4_753::Fr as PrimeField>::MODULUS_BIT_SIZE as usize;
        let scalar_bits = |x: ark_mnt4_753::Fr| x.into_bigint().to_bits_le()[..n].to_vec();
        let mut cases: Vec<Vec<bool>> = vec![
            vec![false; n],
            vec![true; n],
            scalar_bits(-ark_mnt4_753::Fr::from(1u64)),
            scalar_bits(-ark_mnt4_753::Fr::from(2u64)),
            scalar_bits(ark_mnt4_753::Fr::from(1u64)),
            scalar_bits(ark_mnt4_753::Fr::from(2u64)),
            scalar_bits(ark_mnt4_753::Fr::from(u64::MAX)),
            vec![true],
            vec![false, true],
        ];
        let mut top = vec![false; n];
        top[n - 1] = true;
        cases.push(top);

        let bases = [
            ark_mnt4_753::G1Projective::generator() * ark_mnt4_753::Fr::from(7u64),
            ark_mnt4_753::G1Projective::default(), // infinity
        ];
        for base in bases {
            for bits in &cases {
                let cs = ConstraintSystem::<Fr6>::new_ref();
                let base_var = G1Var::new_witness(cs.clone(), || Ok(base)).unwrap();
                let bit_vars: Vec<Boolean<Fr6>> =
                    bits.iter().map(|b| Boolean::new_witness(cs.clone(), || Ok(*b)).unwrap()).collect();
                let ours = scalar_mul_le_compact(&base_var, &bit_vars).unwrap().value().unwrap();
                let theirs = base_var.scalar_mul_le(bit_vars.iter()).unwrap().value().unwrap();
                assert_eq!(ours.into_affine(), theirs.into_affine(), "{} bits", bits.len());
                assert!(cs.is_satisfied().unwrap());
            }
        }
    }

    /// Phase 4 spike, the other side of the cycle: what this circuit's MNT4
    /// verifier costs with the inner VK as a witness instead of a constant, for
    /// `N` inner public inputs. `cargo test --release report_inner_verifier_costs
    /// -- --nocapture`. Setup-mode synthesis only.
    #[cfg(not(feature = "groth16"))]
    #[test]
    fn report_inner_verifier_costs() {
        use ark_crypto_primitives::snark::SNARKGadget;
        use ark_ec::{CurveGroup, PrimeGroup};
        use ark_r1cs_std::alloc::AllocationMode;
        use ark_relations::r1cs::{ConstraintSystem, SynthesisMode};
        let g1 = ark_mnt4_753::G1Projective::generator().into_affine();
        let g2 = ark_mnt4_753::G2Projective::generator().into_affine();
        for n in [7usize, 8] {
            let vk = VerifyingKey::<MNT4_753> {
                h_g2: g2,
                g_alpha_g1: g1,
                h_beta_g2: g2,
                g_gamma_g1: g1,
                h_gamma_g2: g2,
                query: vec![g1; n + 1],
            };
            for witness_vk in [false, true] {
                let cs = ConstraintSystem::<Fr6>::new_ref();
                cs.set_mode(SynthesisMode::Setup);
                let vk_var = if witness_vk {
                    VerifierGadget::<MNT4_753, MNT4PairingVar>::new_verification_key_unchecked(
                        cs.clone(),
                        || Ok(vk.clone()),
                        AllocationMode::Witness,
                    )
                    .unwrap()
                } else {
                    ark_gm17::constraints::VerifyingKeyVar::<MNT4_753, MNT4PairingVar>::new_constant(cs.clone(), &vk)
                        .unwrap()
                };
                let start = cs.num_constraints();
                let pvk = vk_var.prepare().unwrap();
                let after_prepare = cs.num_constraints();
                let bits: Vec<Vec<Boolean<Fr6>>> = (0..n)
                    .map(|_| {
                        (0..Fr4::MODULUS_BIT_SIZE as usize)
                            .map(|_| Boolean::new_witness(cs.clone(), || Ok(false)).unwrap())
                            .collect()
                    })
                    .collect();
                let input = BooleanInputVar::<Fr4, Fr6>::new(bits);
                let dummy = Proof::<MNT4_753> { a: g1, b: g2, c: g1 };
                let proof = ProofVar::<MNT4_753, MNT4PairingVar>::new_witness(cs.clone(), || Ok(dummy)).unwrap();
                let before_verify = cs.num_constraints();
                let _ = VerifierGadget::<MNT4_753, MNT4PairingVar>::verify_with_processed_vk(&pvk, &input, &proof)
                    .unwrap();
                println!(
                    "N={n} vk {:<8}: prepare {:>7}  verify {:>8}  verifier total {:>8}",
                    if witness_vk { "witness" } else { "constant" },
                    after_prepare - start,
                    cs.num_constraints() - before_verify,
                    cs.num_constraints() - before_verify + after_prepare - start,
                );
            }
        }
    }

    /// A trivial 2-public-input MNT4-753 circuit: `a * b == c` for private `b, c`,
    /// publics `[a, vk_hash]` — the last one is the wrap convention, and the
    /// toy itself doesn't constrain it.
    #[derive(Clone, Default)]
    struct Toy {
        a: Option<Fr4>,
        b: Option<Fr4>,
        c: Option<Fr4>,
        vk_hash: Option<Fr4>,
    }
    impl ConstraintSynthesizer<Fr4> for Toy {
        fn generate_constraints(self, cs: ConstraintSystemRef<Fr4>) -> Result<(), SynthesisError> {
            let a = FpVar::new_input(cs.clone(), || opt(&self.a))?;
            let _vk_hash = FpVar::new_input(cs.clone(), || opt(&self.vk_hash))?;
            let b = FpVar::new_witness(cs.clone(), || opt(&self.b))?;
            let c = FpVar::new_witness(cs.clone(), || opt(&self.c))?;
            (&a * &b).enforce_equal(&c)
        }
    }

    /// A real toy proof carrying `claimed_hash`, and the VK it verifies under.
    fn toy_proof(claimed_hash: Option<Fr4>) -> (VerifyingKey<MNT4_753>, Proof<MNT4_753>, [Fr4; 2]) {
        let mut rng = StdRng::seed_from_u64(7);
        let (pk, vk) = Snark::<MNT4_753>::circuit_specific_setup(Toy::default(), &mut rng).unwrap();
        let a = Fr4::from(6u64);
        let vk_hash = claimed_hash.unwrap_or_else(|| inner_vk_hash(&vk));
        let circuit = Toy { a: Some(a), b: Some(Fr4::from(7u64)), c: Some(Fr4::from(42u64)), vk_hash: Some(vk_hash) };
        let proof = Snark::<MNT4_753>::prove(&pk, circuit, &mut rng).unwrap();
        assert!(Snark::<MNT4_753>::verify(&vk, &[a, vk_hash], &proof).unwrap());
        (vk, proof, [a, vk_hash])
    }

    fn wrap_satisfied(vk: VerifyingKey<MNT4_753>, proof: Proof<MNT4_753>, inputs: [Fr4; 2]) -> bool {
        let cs = ark_relations::r1cs::ConstraintSystem::<Fr6>::new_ref();
        WrapCircuit::<2> { inner_vk: vk, inner_proof: Some(proof), inner_public_inputs: Some(inputs) }
            .generate_constraints(cs.clone())
            .unwrap();
        cs.is_satisfied().unwrap()
    }

    /// `cargo test --release report_wrap_constraints -- --nocapture`.
    #[test]
    fn report_wrap_constraints() {
        use ark_relations::r1cs::{ConstraintSystem, SynthesisMode};
        let dummy = Proof::<MNT4_753> {
            a: ark_mnt4_753::G1Affine::identity(),
            b: ark_mnt4_753::G2Affine::identity(),
            c: ark_mnt4_753::G1Affine::identity(),
        };
        let cs = ConstraintSystem::<Fr6>::new_ref();
        cs.set_mode(SynthesisMode::Setup);
        WrapCircuit::<8> { inner_vk: shaped_inner_vk(8), inner_proof: Some(dummy), inner_public_inputs: None }
            .generate_constraints(cs.clone())
            .unwrap();
        cs.finalize();
        let m = cs.to_matrices().unwrap();
        println!(
            "WrapCircuit<8>: {} constraints, {} witness variables, nonzeros A {} B {} C {}",
            cs.num_constraints(),
            cs.num_witness_variables(),
            m.a_num_non_zero,
            m.b_num_non_zero,
            m.c_num_non_zero,
        );
    }

    /// Which part of the wrap circuit makes its matrices dense.
    #[cfg(not(feature = "groth16"))]
    #[test]
    fn report_wrap_density() {
        use ark_ec::PrimeGroup;
        use ark_relations::r1cs::{ConstraintSystem, SynthesisMode};
        fn report(name: &str, build: impl FnOnce(ConstraintSystemRef<Fr6>)) {
            let cs = ConstraintSystem::<Fr6>::new_ref();
            cs.set_mode(SynthesisMode::Setup);
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
        let witness_vk = |cs: ConstraintSystemRef<Fr6>| {
            VerifierGadget::<MNT4_753, MNT4PairingVar>::new_verification_key_unchecked(
                cs,
                || Ok(shaped_inner_vk(8)),
                AllocationMode::Witness,
            )
            .unwrap()
        };
        report("poseidon, 60 elements", |cs| {
            let xs: Vec<Fp6> = (0..60).map(|_| Fp6::new_witness(cs.clone(), || Ok(Fr6::from(1u64))).unwrap()).collect();
            let mut sponge = PoseidonSpongeVar::new(cs, &poseidon_params::mnt6_753_fr_poseidon_config());
            sponge.absorb(&xs).unwrap();
            sponge.squeeze_field_elements(1).unwrap();
        });
        report("vk hash (to_affine + poseidon)", |cs| {
            let vk = witness_vk(cs.clone());
            inner_vk_hash_bits_var(cs, &vk).unwrap();
        });
        report("prepare witness vk", |cs| {
            witness_vk(cs).prepare().unwrap();
        });
        report("input sum, witness query", |cs| {
            let vk = witness_vk(cs.clone());
            let mut g_psi = vk.query[0].clone();
            for b in vk.query.iter().skip(1) {
                let bits: Vec<Boolean<Fr6>> =
                    (0..753).map(|_| Boolean::new_witness(cs.clone(), || Ok(false)).unwrap()).collect();
                g_psi += b.scalar_mul_le(bits.iter()).unwrap();
            }
        });
        report("input sum, constant query", |cs| {
            let vk = ark_gm17::constraints::VerifyingKeyVar::<MNT4_753, MNT4PairingVar>::new_constant(
                cs.clone(),
                shaped_inner_vk(8),
            )
            .unwrap();
            let mut g_psi = vk.query[0].clone();
            for b in vk.query.iter().skip(1) {
                let bits: Vec<Boolean<Fr6>> =
                    (0..753).map(|_| Boolean::new_witness(cs.clone(), || Ok(false)).unwrap()).collect();
                g_psi += b.scalar_mul_le(bits.iter()).unwrap();
            }
        });
        report("miller+final exp, witness", |cs| {
            use ark_r1cs_std::pairing::PairingVar;
            let pvk = witness_vk(cs.clone()).prepare().unwrap();
            let g1 = MNT4PairingVar::prepare_g1(&pvk.query[0]).unwrap();
            let ml = MNT4PairingVar::miller_loop(&[g1], &[pvk.h_gamma_pc.clone()]).unwrap();
            let _ = MNT4PairingVar::final_exponentiation(&ml).unwrap();
        });
        report("miller+final exp, constant", |cs| {
            use ark_r1cs_std::pairing::PairingVar;
            let vk = ark_gm17::constraints::VerifyingKeyVar::<MNT4_753, MNT4PairingVar>::new_constant(
                cs.clone(),
                shaped_inner_vk(8),
            )
            .unwrap();
            let pvk = vk.prepare().unwrap();
            let p = <MNT4PairingVar as PairingVar<MNT4_753>>::G1Var::new_witness(cs.clone(), || {
                Ok(ark_mnt4_753::G1Projective::generator())
            })
            .unwrap();
            let g1 = MNT4PairingVar::prepare_g1(&p).unwrap();
            let ml = MNT4PairingVar::miller_loop(&[g1], &[pvk.h_gamma_pc.clone()]).unwrap();
            let _ = MNT4PairingVar::final_exponentiation(&ml).unwrap();
        });
        report("verify, witness vk, ours", |cs| {
            let pvk = witness_vk(cs.clone()).prepare().unwrap();
            let bits: Vec<Vec<Boolean<Fr6>>> = (0..8)
                .map(|_| (0..753).map(|_| Boolean::new_witness(cs.clone(), || Ok(false)).unwrap()).collect())
                .collect();
            let g1 = ark_mnt4_753::G1Affine::identity();
            let dummy = Proof::<MNT4_753> { a: g1, b: ark_mnt4_753::G2Affine::identity(), c: g1 };
            let proof = ProofVar::<MNT4_753, MNT4PairingVar>::new_witness(cs, || Ok(dummy)).unwrap();
            let _ = verify_mnt4(&pvk, &bits, &proof).unwrap();
        });
        report("verify, witness vk, gadget", |cs| {
            let pvk = witness_vk(cs.clone()).prepare().unwrap();
            let bits: Vec<Vec<Boolean<Fr6>>> = (0..8)
                .map(|_| (0..753).map(|_| Boolean::new_witness(cs.clone(), || Ok(false)).unwrap()).collect())
                .collect();
            let g1 = ark_mnt4_753::G1Affine::identity();
            let dummy = Proof::<MNT4_753> { a: g1, b: ark_mnt4_753::G2Affine::identity(), c: g1 };
            let proof = ProofVar::<MNT4_753, MNT4PairingVar>::new_witness(cs, || Ok(dummy)).unwrap();
            let _ = VerifierGadget::<MNT4_753, MNT4PairingVar>::verify_with_processed_vk(
                &pvk,
                &BooleanInputVar::<Fr4, Fr6>::new(bits),
                &proof,
            )
            .unwrap();
        });
    }

    #[test]
    fn vk_hash_gadget_matches_native() {
        let vk = toy_proof(None).0;
        let cs = ark_relations::r1cs::ConstraintSystem::<Fr6>::new_ref();
        let vk_var = VerifierGadget::<MNT4_753, MNT4PairingVar>::new_verification_key_unchecked(
            cs.clone(),
            || Ok(vk.clone()),
            AllocationMode::Witness,
        )
        .unwrap();
        let bits: Vec<bool> = inner_vk_hash_bits_var(cs, &vk_var).unwrap().iter().map(|b| b.value().unwrap()).collect();
        let expected = inner_vk_hash(&vk).into_bigint().to_bits_le();
        assert_eq!(bits, expected[..VK_HASH_BITS]);
        assert!(expected[VK_HASH_BITS..].iter().all(|b| !b));
    }

    #[test]
    fn wrap_accepts_a_proof_carrying_its_own_vk_hash() {
        let (vk, proof, inputs) = toy_proof(None);
        assert!(wrap_satisfied(vk, proof, inputs));
    }

    /// The point of the hash: a proof under some other VK can't pass for one
    /// under the VK it names.
    #[test]
    fn wrap_rejects_a_proof_naming_another_vk() {
        let other = inner_vk_hash(&shaped_inner_vk(1));
        let (vk, proof, inputs) = toy_proof(Some(other));
        assert!(!wrap_satisfied(vk, proof, inputs));
    }

    #[test]
    fn proving_wraps_a_proof_end_to_end() {
        let mut rng = StdRng::seed_from_u64(8);
        let (vk, proof, inputs) = toy_proof(None);

        let (wrap_pk, wrap_vk) = setup::<2, _>(&mut rng).unwrap();
        let wrap_circuit = WrapCircuit::<2> { inner_vk: vk, inner_proof: Some(proof), inner_public_inputs: Some(inputs) };
        let wrap_proof = prove::<2, _>(&wrap_pk, wrap_circuit, &mut rng).unwrap();

        let expected_public_inputs = public_input_chunks(&inputs);
        assert_eq!(expected_public_inputs.len(), 2 * chunks_per_value());
        assert!(verify(&wrap_vk, &expected_public_inputs, &wrap_proof).unwrap());

        let mut tampered = expected_public_inputs.clone();
        tampered[0] += Fr6::from(1u64);
        assert!(!verify(&wrap_vk, &tampered, &wrap_proof).unwrap());
    }
}
