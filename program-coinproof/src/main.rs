//! One step of the IVC `CoinProof` relation.
//!
//! Uses `owner_sk` (private key) for X25519 ECDH decryption in `scan_entry`.
//!
//! Inner coin-proof (slot k-1) and spend proof (at receipt slot) are both
//! verified via `Groth16Verifier::verify`. The HOST passes both as raw bytes
//! via `stdin.write_vec` — no `write_proof` / `verify_sp1_proof` used.
//!
//! Public values for verification come from `check_coin_proof_step` return
//! values (board-derived, trusted) — not from separate stdin writes.

#![no_main]
sp1_zkvm::entrypoint!(main);

use cloakkchain_lib::{
    check_coin_proof_step, BoardEntry, CoinProofJustification, CoinProofPublicValues,
};

pub fn main() {
    let vkey: [u32; 8]            = sp1_zkvm::io::read();
    let owner_sk: [u8; 32]        = sp1_zkvm::io::read();
    let coin_commitment: [u8; 32] = sp1_zkvm::io::read();
    let entry_k: BoardEntry       = sp1_zkvm::io::read();
    let slot: usize               = sp1_zkvm::io::read();
    let append_path: Vec<[u8; 32]> = sp1_zkvm::io::read();
    let has_inner: bool           = sp1_zkvm::io::read();
    let inner: Option<CoinProofPublicValues> =
        if has_inner { Some(sp1_zkvm::io::read()) } else { None };
    // Groth16 inner coin-proof bytes — only present when has_inner.
    let inner_proof_bytes: Vec<u8>  = if has_inner { sp1_zkvm::io::read_vec() } else { vec![] };
    let inner_vkey_hash: String     = if has_inner { sp1_zkvm::io::read() } else { String::new() };
    let parent_nullifier: [u8; 32]  = sp1_zkvm::io::read();
    let own_nullifier: [u8; 32]     = sp1_zkvm::io::read();
    // Groth16 spend proof hint — only present at the receipt slot in prove mode.
    let has_spend_proof: bool       = sp1_zkvm::io::read();
    let spend_proof_bytes: Vec<u8>  = if has_spend_proof { sp1_zkvm::io::read_vec() } else { vec![] };
    let spend_vkey_hash: String     = if has_spend_proof { sp1_zkvm::io::read() } else { String::new() };

    let (public_values, justification) =
        check_coin_proof_step(vkey, owner_sk, coin_commitment, entry_k, slot, append_path,
            inner, parent_nullifier, own_nullifier)
            .expect("the CoinProof relation does not hold for this step");

    // Verify the inner coin-proof as Groth16 (all steps except base case).
    // pv comes from check_coin_proof_step (board-derived, trusted) — not from stdin.
    if let CoinProofJustification::Step { inner_public_values, .. } = &justification {
        sp1_verifier::Groth16Verifier::verify(
            &inner_proof_bytes,
            &inner_public_values.encode(),
            &inner_vkey_hash,
            *sp1_verifier::GROTH16_VK_BYTES,
        )
        .expect("inner coin-proof Groth16 verification failed");
    }

    // At the receipt slot: verify the parent's Groth16 spend proof.
    // pv_encode comes from ReceiptInfo (board-derived, trusted) — not from stdin.
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
