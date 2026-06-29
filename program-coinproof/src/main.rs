//! One step of the IVC `CoinProof` relation.
//!
//! Uses `owner_sk` (private key) for X25519 ECDH decryption in `scan_entry`.
//!
//! At the receipt slot the justification carries a `SpendProofPackage`.  We
//! verify it here with our self-contained Groth16 verifier (BN254 algebraic
//! check via `substrate-bn-succinct-rs`), establishing a cryptographic chain
//! of custody from the creating spend proof all the way to this coin-proof.
//!
//! Board entries stay ~1 KB because spend proofs are Groth16 (~356 bytes
//! inside the package) rather than compressed STARKs (~1.21 MB).

#![no_main]
extern crate alloc;
sp1_zkvm::entrypoint!(main);

mod groth16;

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
    if let CoinProofJustification::Step { inner_public_values, .. } = &justification {
        let digest: [u8; 32] = Sha256::digest(inner_public_values.encode()).into();
        sp1_zkvm::lib::verify::verify_sp1_proof(&vkey, &digest);
    }

    // At the receipt slot: verify the parent's Groth16 spend proof in-circuit.
    // This establishes that the coin was created by a valid spend — full chain
    // of custody without any large proof hints or OOM risk.
    let receipt_pkg = match &justification {
        CoinProofJustification::Base { receipt_spend_pkg: Some(p) } => Some(p),
        CoinProofJustification::Step { receipt_spend_pkg: Some(p), .. } => Some(p),
        _ => None,
    };
    if let Some(pkg) = receipt_pkg {
        groth16::verify_sp1_groth16(
            &pkg.proof_bytes,
            &pkg.public_values,
            &pkg.spend_vkey_hash,
        ).expect("parent spend proof failed Groth16 verification");
    }

    sp1_zkvm::io::commit_slice(&public_values.encode());
}
