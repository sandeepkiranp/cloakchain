//! One step of the IVC `CoinProof` relation.
//!
//! Uses `owner_sk` (private key) for X25519 ECDH decryption in `scan_entry`.
//!
//! At the receipt slot the justification carries `ReceiptInfo` (spend vkey +
//! public values).  We call `verify_sp1_proof` on it — the same mechanism used
//! for recursive inner-proof verification — establishing a cryptographic chain
//! of custody without any extra proof format conversions.
//!
//! The HOST passes the compressed spend proof as a `write_proof` hint alongside
//! the inner coin-proof hint.

#![no_main]
sp1_zkvm::entrypoint!(main);

use cloakkchain_lib::{
    check_coin_proof_step, BoardEntry, CoinProofJustification, CoinProofPublicValues,
};
use sha2::{Digest, Sha256};

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
    let parent_nullifier: [u8; 32] = sp1_zkvm::io::read();
    let own_nullifier: [u8; 32]    = sp1_zkvm::io::read();

    let (public_values, justification) =
        check_coin_proof_step(vkey, owner_sk, coin_commitment, entry_k, slot, append_path,
            inner, parent_nullifier, own_nullifier)
            .expect("the CoinProof relation does not hold for this step");

    // Verify the recursive inner coin-proof (all steps except base case).
    // The HOST passes the compressed inner proof as write_proof hint #1.
    if let CoinProofJustification::Step { inner_public_values, .. } = &justification {
        let digest: [u8; 32] = Sha256::digest(inner_public_values.encode()).into();
        sp1_zkvm::lib::verify::verify_sp1_proof(&vkey, &digest);
    }

    // At the receipt slot: verify the parent's compressed spend proof.
    // The HOST passes it as write_proof hint #2 (or #1 for base-case receipts).
    // This establishes a cryptographic chain of custody from spend → coin-proof.
    let receipt = match &justification {
        CoinProofJustification::Base { receipt: Some(r) } => Some(r),
        CoinProofJustification::Step { receipt: Some(r), .. } => Some(r),
        _ => None,
    };
    if let Some(r) = receipt {
        let digest: [u8; 32] = Sha256::digest(&r.pv_encode).into();
        sp1_zkvm::lib::verify::verify_sp1_proof(&r.spend_vkey, &digest);
    }

    sp1_zkvm::io::commit_slice(&public_values.encode());
}
