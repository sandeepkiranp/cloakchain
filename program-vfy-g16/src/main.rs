#![no_main]
sp1_zkvm::entrypoint!(main);

use cloakkchain_groth16_verifier::verify_sp1_spend_proof;

pub fn main() {
    let spend_proof_bytes: Vec<u8> = sp1_zkvm::io::read_vec();
    let pv_encode: Vec<u8>         = sp1_zkvm::io::read_vec();
    let spend_vkey_hash: String    = sp1_zkvm::io::read();

    if !spend_proof_bytes.is_empty() {
        if let Err(reason) = verify_sp1_spend_proof(&spend_proof_bytes, &pv_encode, &spend_vkey_hash) {
            // Guest println!/stdout isn't reliably visible through client.execute() in this
            // build (confirmed empirically - zero "stdout:" lines appear anywhere in the host
            // log even though sp1-core-executor's write syscall handler should eprintln! them).
            // commit_slice writes directly to the public-values stream via a syscall, which
            // already takes effect before the panic below halts execution - so this is visible
            // in `output.as_slice()` on the host side even though the guest never returns.
            let debug_msg = format!(
                "[VFY-G16-GUEST] verify_sp1_spend_proof FAILED: {reason}  \
                 proof_bytes.len()={}  pv_encode.len()={}  spend_vkey_hash={spend_vkey_hash}",
                spend_proof_bytes.len(),
                pv_encode.len()
            );
            sp1_zkvm::io::commit_slice(debug_msg.as_bytes());
            panic!("Groth16 spend proof verification failed: {reason}");
        }
    }

    sp1_zkvm::io::commit_slice(&pv_encode);
}
