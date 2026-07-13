#![no_main]
sp1_zkvm::entrypoint!(main);

use cloakkchain_lib::{
    check_coin_proof_step, BoardEntry, CoinProofJustification, CoinProofPublicValues,
};

pub fn main() {
    let vkey: [u32; 8]             = sp1_zkvm::io::read();
    let vkey_hash: String          = sp1_zkvm::io::read();
    let owner_sk: [u8; 32]         = sp1_zkvm::io::read();
    let coin_commitment: [u8; 32]  = sp1_zkvm::io::read();
    let entry_k: BoardEntry        = sp1_zkvm::io::read();
    let slot: usize                = sp1_zkvm::io::read();
    let append_path: Vec<[u8; 32]> = sp1_zkvm::io::read();
    let has_inner: bool            = sp1_zkvm::io::read();
    // Inner Groth16 proof bytes come before the decoded public values.
    let inner_proof_bytes: Vec<u8> = if has_inner { sp1_zkvm::io::read_vec() } else { vec![] };
    let inner: Option<CoinProofPublicValues> =
        if has_inner { Some(sp1_zkvm::io::read()) } else { None };
    let parent_nullifier: [u8; 32] = sp1_zkvm::io::read();
    let own_nullifier: [u8; 32]    = sp1_zkvm::io::read();
    // Groth16 spend-proof hint — only present at the receipt slot.
    let has_spend_proof: bool      = sp1_zkvm::io::read();
    let spend_proof_bytes: Vec<u8> = if has_spend_proof { sp1_zkvm::io::read_vec() } else { vec![] };
    let spend_vkey_hash: String    = if has_spend_proof { sp1_zkvm::io::read() } else { String::new() };

    let (public_values, justification) =
        check_coin_proof_step(vkey, owner_sk, coin_commitment, entry_k, slot, append_path,
            inner, parent_nullifier, own_nullifier)
            .expect("the CoinProof relation does not hold for this step");

    // Inner coin-proof: verify via Groth16. Empty bytes in execute/mock mode → skipped.
    if let CoinProofJustification::Step { inner_public_values, .. } = &justification {
        if !inner_proof_bytes.is_empty() {
            sp1_verifier::Groth16Verifier::verify(
                &inner_proof_bytes,
                &inner_public_values.encode(),
                &vkey_hash,
                *sp1_verifier::GROTH16_VK_BYTES,
            ).expect("inner coin-proof Groth16 verification failed");
        }
    }

    // Spend-proof at the receipt slot: verified as Groth16.
    let receipt = match &justification {
        CoinProofJustification::Base { receipt: Some(r) } => Some(r),
        CoinProofJustification::Step { receipt: Some(r), .. } => Some(r),
        _ => None,
    };
    if let Some(r) = receipt {
        if has_spend_proof {
            sp1_verifier::Groth16Verifier::verify(
                &spend_proof_bytes,
                &r.pv_encode,
                &spend_vkey_hash,
                *sp1_verifier::GROTH16_VK_BYTES,
            ).expect("spend Groth16 proof verification failed");
        }
    }

    sp1_zkvm::io::commit_slice(&public_values.encode());
}
