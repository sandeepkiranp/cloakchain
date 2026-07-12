#![no_main]
sp1_zkvm::entrypoint!(main);

use sha2::{Digest, Sha256};
use cloakkchain_lib::{
    check_coin_proof_step, BoardEntry, CoinProofJustification, CoinProofPublicValues,
};

pub fn main() {
    let vkey: [u32; 8]             = sp1_zkvm::io::read();
    let owner_sk: [u8; 32]         = sp1_zkvm::io::read();
    let coin_commitment: [u8; 32]  = sp1_zkvm::io::read();
    let entry_k: BoardEntry        = sp1_zkvm::io::read();
    let slot: usize                = sp1_zkvm::io::read();
    let append_path: Vec<[u8; 32]> = sp1_zkvm::io::read();
    let has_inner: bool            = sp1_zkvm::io::read();
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

    // Inner coin-proof (compressed STARK): verify via deferred syscall.
    // The proof was passed by the host via stdin.write_proof; pv_digest is
    // SHA-256 of the committed public values bytes.
    if let CoinProofJustification::Step { inner_public_values, .. } = &justification {
        let pv_digest: [u8; 32] = Sha256::digest(&inner_public_values.encode()).into();
        sp1_zkvm::lib::verify::verify_sp1_proof(&vkey, &pv_digest);
    }

    // Spend-proof hint at the receipt slot: verified as Groth16 since spend
    // proofs are always proved with Groth16 (for the small board entry size).
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
            )
            .expect("spend Groth16 proof verification failed");
        }
    }

    sp1_zkvm::io::commit_slice(&public_values.encode());
}
