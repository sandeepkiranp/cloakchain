//! One step of the IVC `CoinProof` relation.
//!
//! Uses `owner_sk` (private key) for X25519 ECDH decryption in `scan_entry` —
//! no registry needed.
//!
//! At the receipt slot `receipt_spend_pv` is `Some`; the program verifies the
//! parent's spend proof here so that every coin tracked by this IVC has a
//! cryptographic chain of custody back to a valid spend.

#![no_main]
sp1_zkvm::entrypoint!(main);

use cloakkchain_lib::{
    check_coin_proof_step, BoardEntry, CoinProofJustification,
    CoinProofPublicValues, ValidPublicValues,
};
use sha2::{Digest, Sha256};

pub fn main() {
    let vkey: [u32; 8]         = sp1_zkvm::io::read();
    let spend_vkey: [u32; 8]   = sp1_zkvm::io::read();
    let owner_sk: [u8; 32]     = sp1_zkvm::io::read();
    let coin_commitment: [u8; 32] = sp1_zkvm::io::read();
    let entry_k: BoardEntry    = sp1_zkvm::io::read();
    let slot: usize            = sp1_zkvm::io::read();
    let append_path: Vec<[u8; 32]> = sp1_zkvm::io::read();
    let has_inner: bool        = sp1_zkvm::io::read();
    let inner: Option<CoinProofPublicValues> =
        if has_inner { Some(sp1_zkvm::io::read()) } else { None };
    let parent_nullifier: [u8; 32] = sp1_zkvm::io::read();
    let own_nullifier: [u8; 32]    = sp1_zkvm::io::read();
    let has_receipt_spend_pv: bool = sp1_zkvm::io::read();
    let receipt_spend_pv: Option<ValidPublicValues> =
        if has_receipt_spend_pv { Some(sp1_zkvm::io::read()) } else { None };

    let (public_values, justification) =
        check_coin_proof_step(
            vkey, owner_sk, coin_commitment, entry_k, slot, append_path,
            inner, parent_nullifier, own_nullifier, receipt_spend_pv,
        )
        .expect("the CoinProof relation does not hold for this step");

    // Verify the recursive inner coin-proof (all steps except the base case).
    if let CoinProofJustification::Step { inner_public_values, .. } = &justification {
        let digest: [u8; 32] = Sha256::digest(inner_public_values.encode()).into();
        sp1_zkvm::lib::verify::verify_sp1_proof(&vkey, &digest);
    }

    // At the receipt slot verify the parent's spend proof, establishing a
    // cryptographic chain of custody from coin creation to this coin-proof.
    let receipt_pv = match &justification {
        CoinProofJustification::Base { receipt_spend_pv: Some(pv) } => Some(pv),
        CoinProofJustification::Step { receipt_spend_pv: Some(pv), .. } => Some(pv),
        _ => None,
    };
    if let Some(pv) = receipt_pv {
        let digest: [u8; 32] = Sha256::digest(pv.encode()).into();
        sp1_zkvm::lib::verify::verify_sp1_proof(&spend_vkey, &digest);
    }

    sp1_zkvm::io::commit_slice(&public_values.encode());
}
