// Test program: SP1 guest that verifies an MNT4-753 Groth16 proof, mirroring
// program-vfy-g16/src/main.rs's structure exactly, so cycle-count and
// peak-memory numbers are directly comparable to the real VFY-G16 (BN254).
//
// Purpose: settle empirically whether verifying a Groth16 proof over MNT
// curves inside SP1 is cheaper or (as predicted, since SP1 has no MNT
// precompile - only bn254/bls12-381 - and MNT curves need larger 753-bit
// fields than BN254's 254-bit) more expensive than today's VFY-G16.
#![no_main]
sp1_zkvm::entrypoint!(main);

use ark_groth16::{Groth16, Proof, VerifyingKey};
use ark_mnt4_753::{Fr, MNT4_753};
use ark_serialize::CanonicalDeserialize;
use ark_snark::SNARK;

pub fn main() {
    let proof_bytes: Vec<u8> = sp1_zkvm::io::read_vec();
    let vk_bytes: Vec<u8> = sp1_zkvm::io::read_vec();
    let public_input_bytes: Vec<u8> = sp1_zkvm::io::read_vec();

    let proof = Proof::<MNT4_753>::deserialize_compressed(&proof_bytes[..])
        .expect("proof deserialize");
    let vk = VerifyingKey::<MNT4_753>::deserialize_compressed(&vk_bytes[..])
        .expect("vk deserialize");
    let public_input = Fr::deserialize_compressed(&public_input_bytes[..])
        .expect("public input deserialize");

    let pvk = Groth16::<MNT4_753>::process_vk(&vk).expect("process_vk");
    let valid = Groth16::<MNT4_753>::verify_with_processed_vk(&pvk, &[public_input], &proof)
        .expect("verify failed to run");

    assert!(valid, "MNT4-753 Groth16 proof verification failed inside SP1");

    sp1_zkvm::io::commit(&valid);
}
