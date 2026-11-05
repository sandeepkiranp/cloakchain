//! The proof system every circuit in the chain is proved with, chosen at build
//! time: GM17 by default, or Groth16 with the `groth16` feature.
//!
//! GM17 is the main instantiation: it is non-malleable, which the construction
//! relies on. Groth16 has minor known malleability, and is here so the
//! self-recursive Groth16 instantiation can be benchmarked alongside it.
//!
//! Everything else refers to these names rather than to either crate, so the
//! only code that knows which proof system is in use is in this module, plus
//! the hand-written verifier in the crate root (`verify_mnt4`), which follows
//! each system's own verification equation.

use ark_ec::{pairing::Pairing, CurveGroup, PrimeGroup};
use ark_r1cs_std::pairing::PairingVar;

#[cfg(not(feature = "groth16"))]
pub use ark_gm17::{
    constraints::{PreparedVerifyingKeyVar, ProofVar, VerifyingKeyVar},
    Proof, ProvingKey, VerifyingKey, GM17 as Snark,
};
#[cfg(not(feature = "groth16"))]
pub type VerifierGadget<E, P> = ark_gm17::constraints::GM17VerifierGadget<E, P>;

#[cfg(feature = "groth16")]
pub use ark_groth16::{
    constraints::{PreparedVerifyingKeyVar, ProofVar, VerifyingKeyVar},
    Groth16 as Snark, Proof, ProvingKey, VerifyingKey,
};
#[cfg(feature = "groth16")]
pub type VerifierGadget<E, P> = ark_groth16::constraints::Groth16VerifierGadget<E, P>;

/// For reports and logs.
pub const NAME: &str = if cfg!(feature = "groth16") { "Groth16" } else { "GM17" };

/// A VK's G1 and G2 points, in a fixed order that is part of the definition of
/// `inner_vk_hash`. The input bases come last among the G1 points.
pub fn vk_points<E: Pairing>(vk: &VerifyingKey<E>) -> (Vec<E::G1Affine>, Vec<E::G2Affine>) {
    #[cfg(not(feature = "groth16"))]
    let points = (
        [vk.g_alpha_g1, vk.g_gamma_g1].into_iter().chain(vk.query.iter().copied()).collect(),
        vec![vk.h_g2, vk.h_beta_g2, vk.h_gamma_g2],
    );
    #[cfg(feature = "groth16")]
    let points = (
        [vk.alpha_g1].into_iter().chain(vk.gamma_abc_g1.iter().copied()).collect(),
        vec![vk.beta_g2, vk.gamma_g2, vk.delta_g2],
    );
    points
}

/// [`vk_points`] for a VK allocated in-circuit, in the same order.
pub fn vk_var_points<E: Pairing, P: PairingVar<E>>(vk: &VerifyingKeyVar<E, P>) -> (Vec<&P::G1Var>, Vec<&P::G2Var>) {
    #[cfg(not(feature = "groth16"))]
    let points = (
        [&vk.g_alpha_g1, &vk.g_gamma_g1].into_iter().chain(vk.query.iter()).collect(),
        vec![&vk.h_g2, &vk.h_beta_g2, &vk.h_gamma_g2],
    );
    #[cfg(feature = "groth16")]
    let points = (
        [&vk.alpha_g1].into_iter().chain(vk.gamma_abc_g1.iter()).collect(),
        vec![&vk.beta_g2, &vk.gamma_g2, &vk.delta_g2],
    );
    points
}

/// A verifying key of the shape a circuit with `inputs` public inputs has, made
/// of generators. Setup and constraint counting only need the shape.
pub fn shaped_vk<E: Pairing>(inputs: usize) -> VerifyingKey<E> {
    let g1 = E::G1::generator().into_affine();
    let g2 = E::G2::generator().into_affine();
    #[cfg(not(feature = "groth16"))]
    let vk = VerifyingKey { h_g2: g2, g_alpha_g1: g1, h_beta_g2: g2, g_gamma_g1: g1, h_gamma_g2: g2, query: vec![g1; inputs + 1] };
    #[cfg(feature = "groth16")]
    let vk = VerifyingKey { alpha_g1: g1, beta_g2: g2, gamma_g2: g2, delta_g2: g2, gamma_abc_g1: vec![g1; inputs + 1] };
    vk
}
