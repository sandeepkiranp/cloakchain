#![no_main]
sp1_zkvm::entrypoint!(main);

use cloakkchain_groth16_verifier::verify_sp1_spend_proof;

pub fn main() {
    let spend_proof_bytes: Vec<u8> = sp1_zkvm::io::read_vec();
    let pv_encode: Vec<u8>         = sp1_zkvm::io::read_vec();
    let spend_vkey_hash: String    = sp1_zkvm::io::read();

    if !spend_proof_bytes.is_empty() {
        if let Err(reason) = verify_sp1_spend_proof(&spend_proof_bytes, &pv_encode, &spend_vkey_hash) {
            println!(
                "[VFY-G16-GUEST] verify_sp1_spend_proof FAILED: {reason}  \
                 proof_bytes.len()={}  pv_encode.len()={}  spend_vkey_hash={spend_vkey_hash}",
                spend_proof_bytes.len(),
                pv_encode.len()
            );
            panic!("Groth16 spend proof verification failed: {reason}");
        }
    }

    sp1_zkvm::io::commit_slice(&pv_encode);
}
