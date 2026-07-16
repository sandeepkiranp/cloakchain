#![no_main]
sp1_zkvm::entrypoint!(main);

use cloakkchain_groth16_verifier::verify_sp1_spend_proof;

pub fn main() {
    let spend_proof_bytes: Vec<u8> = sp1_zkvm::io::read_vec();
    let pv_encode: Vec<u8>         = sp1_zkvm::io::read_vec();
    let spend_vkey_hash: String    = sp1_zkvm::io::read();

    if !spend_proof_bytes.is_empty() {
        verify_sp1_spend_proof(&spend_proof_bytes, &pv_encode, &spend_vkey_hash)
            .expect("Groth16 spend proof verification failed");
    }

    sp1_zkvm::io::commit_slice(&pv_encode);
}
