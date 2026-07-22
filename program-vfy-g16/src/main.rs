#![no_main]
sp1_zkvm::entrypoint!(main);

use cloakkchain_groth16_verifier::verify_sp1_spend_proof;

pub fn main() {
    // The public_value_stream came back completely empty (`[]`) on the last run despite
    // exit_code=1, meaning the explicit `if let Err(reason) = ...` branch below never ran -
    // verify_sp1_spend_proof (or something it calls, e.g. in the vendored
    // snark-bn254-verifier/bn crates) is panicking internally (slice bounds, unwrap, etc.)
    // rather than returning a clean Err. sp1-zkvm routes every panic straight to
    // syscall_halt(1) with no message surfaced, so install a panic hook that commits the
    // real panic message/location first - this runs regardless of where the panic
    // originates, unlike the Result-based handling below.
    std::panic::set_hook(Box::new(|info| {
        let payload = if let Some(s) = info.payload().downcast_ref::<&str>() {
            (*s).to_string()
        } else if let Some(s) = info.payload().downcast_ref::<String>() {
            s.clone()
        } else {
            "<non-string panic payload>".to_string()
        };
        let location = info
            .location()
            .map(|l| format!("{}:{}", l.file(), l.line()))
            .unwrap_or_else(|| "<unknown location>".to_string());
        let debug_msg = format!("[VFY-G16-PANIC] {payload} at {location}");
        sp1_zkvm::io::commit_slice(debug_msg.as_bytes());
    }));

    let spend_proof_bytes: Vec<u8> = sp1_zkvm::io::read_vec();
    let pv_encode: Vec<u8>         = sp1_zkvm::io::read_vec();
    let spend_vkey_hash: String    = sp1_zkvm::io::read();

    if !spend_proof_bytes.is_empty() {
        if let Err(reason) = verify_sp1_spend_proof(&spend_proof_bytes, &pv_encode, &spend_vkey_hash) {
            // Dump the exact inputs that failed so they can be pulled off-machine and
            // replayed against both the official sp1-verifier and this custom verifier
            // locally - "verification returned false" (as opposed to a panic) means the
            // crypto math ran to completion but didn't match, which needs real test
            // vectors to debug further, not more panic-location diagnostics.
            let mut dump = Vec::new();
            for field in [spend_proof_bytes.as_slice(), pv_encode.as_slice(), spend_vkey_hash.as_bytes()] {
                dump.extend_from_slice(&(field.len() as u32).to_le_bytes());
                dump.extend_from_slice(field);
            }
            sp1_zkvm::io::commit_slice(&dump);
            panic!(
                "Groth16 spend proof verification failed: {reason}  \
                 proof_bytes.len()={}  pv_encode.len()={}  spend_vkey_hash={spend_vkey_hash}",
                spend_proof_bytes.len(),
                pv_encode.len()
            );
        }
    }

    sp1_zkvm::io::commit_slice(&pv_encode);
}
