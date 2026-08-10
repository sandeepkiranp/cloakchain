//! Generic "wrap" circuit: recursively verifies an MNT4-753 (`Fr4`-native)
//! Groth16 proof against a fixed, compile-time-known verifying key, and
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
//! `circuit-spend`, `circuit-coinproof`); this circuit does no hashing of
//! application data at all, only pairing-based proof verification plus
//! bit-repacking — mirroring the "inner does the real work, outer is a thin
//! composition layer" pattern the experiment's own inner/outer measurements
//! validated as cheap and roughly fixed-cost regardless of inner complexity.

use ark_crypto_primitives::snark::{BooleanInputVar, SNARKGadget};
use ark_ff::{BigInteger, Field, PrimeField};
use ark_groth16::{
    constraints::{Groth16VerifierGadget, ProofVar, VerifyingKeyVar},
    Groth16, Proof, ProvingKey, VerifyingKey,
};
use ark_mnt4_753::MNT4_753;
use ark_mnt6_753::MNT6_753;
use ark_r1cs_std::{fields::fp::FpVar, prelude::*};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_snark::SNARK;
use ark_std::rand::{CryptoRng, RngCore};
use cloakkchain_lib::Fr as Fr4;

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

/// Recursively verifies an `N`-public-input MNT4-753 Groth16 proof from a
/// fixed verifying key, re-exposing each public input as `chunks_per_value()`
/// small `Fr6` public inputs (`N * chunks_per_value()` total, in input
/// order, each value's chunks contiguous and low-chunk-first).
#[derive(Clone)]
pub struct WrapCircuit<const N: usize> {
    /// Fixed per `WrapCircuit<N>` use (e.g. "wraps GenesisSpendCircuit
    /// proofs") — not `Option`, since a verifying key isn't secret and
    /// doesn't need setup-mode placeholder handling.
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
        let input_var = BooleanInputVar::<Fr4, Fr6>::new(per_value_bits.clone());

        // Recursive Groth16 verification of the inner (Fr4/MNT4-753) proof.
        let vk_var = VerifyingKeyVar::<MNT4_753, MNT4PairingVar>::new_constant(cs.clone(), &self.inner_vk)?;
        let proof_var = ProofVar::<MNT4_753, MNT4PairingVar>::new_witness(cs.clone(), || opt(&self.inner_proof))?;
        let pvk = vk_var.prepare()?;
        let ok = Groth16VerifierGadget::<MNT4_753, MNT4PairingVar>::verify_with_processed_vk(
            &pvk,
            &input_var,
            &proof_var,
        )?;
        ok.enforce_equal(&Boolean::TRUE)?;

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
/// vector for `Groth16::<MNT6_753>::verify`.
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

pub fn setup<const N: usize, R: RngCore + CryptoRng>(
    inner_vk: VerifyingKey<MNT4_753>,
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
    let circuit = WrapCircuit::<N> { inner_vk, inner_proof: Some(dummy_proof), inner_public_inputs: None };
    Groth16::<MNT6_753>::circuit_specific_setup(circuit, rng)
}

pub fn prove<const N: usize, R: RngCore + CryptoRng>(
    pk: &ProvingKey<MNT6_753>,
    circuit: WrapCircuit<N>,
    rng: &mut R,
) -> Result<Proof<MNT6_753>, SynthesisError> {
    Groth16::<MNT6_753>::prove(pk, circuit, rng)
}

pub fn verify(
    vk: &VerifyingKey<MNT6_753>,
    public_inputs: &[Fr6],
    proof: &Proof<MNT6_753>,
) -> Result<bool, SynthesisError> {
    Groth16::<MNT6_753>::verify(vk, public_inputs, proof)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_std::rand::{rngs::StdRng, SeedableRng};

    #[test]
    fn wraps_a_genesis_spend_proof_end_to_end() {
        let mut rng = StdRng::seed_from_u64(7);

        // A real GenesisSpendCircuit proof (Phase 2), reproduced minimally
        // here to avoid a circular dev-dependency on circuit-spend: any
        // valid MNT4-753 Groth16 proof exercises WrapCircuit identically,
        // since Wrap never inspects the inner circuit's shape beyond its VK
        // and public-input count.
        use ark_relations::r1cs::ConstraintSystemRef;
        use cloakkchain_lib::Fr;

        /// A trivial 2-public-input MNT4-753 circuit: `a * b == c`, publics `[a, c]`.
        #[derive(Clone, Default)]
        struct Toy {
            a: Option<Fr>,
            b: Option<Fr>,
            c: Option<Fr>,
        }
        impl ConstraintSynthesizer<Fr> for Toy {
            fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
                let a = FpVar::new_input(cs.clone(), || opt(&self.a))?;
                let b = FpVar::new_witness(cs.clone(), || opt(&self.b))?;
                let c = FpVar::new_input(cs.clone(), || opt(&self.c))?;
                (&a * &b).enforce_equal(&c)
            }
        }

        let (toy_pk, toy_vk) = Groth16::<MNT4_753>::circuit_specific_setup(Toy::default(), &mut rng).unwrap();
        let a = Fr::from(6u64);
        let b = Fr::from(7u64);
        let c = Fr::from(42u64);
        let toy_proof =
            Groth16::<MNT4_753>::prove(&toy_pk, Toy { a: Some(a), b: Some(b), c: Some(c) }, &mut rng).unwrap();
        assert!(Groth16::<MNT4_753>::verify(&toy_vk, &[a, c], &toy_proof).unwrap());

        // Now wrap it.
        let (wrap_pk, wrap_vk) = setup::<2, _>(toy_vk, &mut rng).unwrap();
        let wrap_circuit =
            WrapCircuit::<2> { inner_vk: toy_pk.vk.clone(), inner_proof: Some(toy_proof), inner_public_inputs: Some([a, c]) };
        let wrap_proof = prove::<2, _>(&wrap_pk, wrap_circuit, &mut rng).unwrap();

        let expected_public_inputs = public_input_chunks(&[a, c]);
        assert_eq!(expected_public_inputs.len(), 2 * chunks_per_value());
        assert!(verify(&wrap_vk, &expected_public_inputs, &wrap_proof).unwrap());

        let mut tampered = expected_public_inputs.clone();
        tampered[0] += Fr6::from(1u64);
        assert!(!verify(&wrap_vk, &tampered, &wrap_proof).unwrap());
    }
}
