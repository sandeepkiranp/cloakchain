#![no_main]
sp1_zkvm::entrypoint!(main);

pub fn main() {
    let spend_proof_bytes: Vec<u8> = sp1_zkvm::io::read_vec();
    let pv_encode: Vec<u8>         = sp1_zkvm::io::read_vec();
    let spend_vkey_hash: String    = sp1_zkvm::io::read();

    // Empty bytes in execute/mock mode → skip (verify_sp1_proof is a no-op there anyway).
    if !spend_proof_bytes.is_empty() {
        sp1_verifier::Groth16Verifier::verify(
            &spend_proof_bytes,
            &pv_encode,
            &spend_vkey_hash,
            *sp1_verifier::GROTH16_VK_BYTES,
        ).expect("Groth16 spend proof verification failed");
    }

    // Commit the verified spend proof's public values so the coin-proof can bind
    // this validation proof to a specific spend via SHA256(pv_encode).
    sp1_zkvm::io::commit_slice(&pv_encode);
}
