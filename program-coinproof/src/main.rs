//! One step of the IVC `CoinProof` relation.
//!
//! All relation logic lives in [`cloakkchain_lib::check_coin_proof_step`]. This
//! program reads the witnesses for one board slot, calls that function, and (for
//! every step after the first) verifies the previous step's proof of itself
//! before committing the new public values.
//!
//! The spend proof embedded in the transaction is a Groth16 proof — verified
//! externally by the recipient, not inside the zkVM.

#![no_main]
sp1_zkvm::entrypoint!(main);

use cloakkchain_lib::{check_coin_proof_step, BoardEntry, CoinProofJustification, CoinProofPublicValues};
use sha2::{Digest, Sha256};

pub fn main() {
    let vkey: [u32; 8] = sp1_zkvm::io::read();
    let owner_pk: [u8; 32] = sp1_zkvm::io::read();
    let coin_commitment: [u8; 32] = sp1_zkvm::io::read();
    let entry_k: BoardEntry = sp1_zkvm::io::read();
    let slot: usize = sp1_zkvm::io::read();
    let append_path: Vec<[u8; 32]> = sp1_zkvm::io::read();
    let registry: Vec<[u8; 32]> = sp1_zkvm::io::read();
    let has_inner: bool = sp1_zkvm::io::read();
    let inner: Option<CoinProofPublicValues> =
        if has_inner { Some(sp1_zkvm::io::read()) } else { None };
    let parent_nullifier: [u8; 32] = sp1_zkvm::io::read();
    let own_nullifier: [u8; 32] = sp1_zkvm::io::read();

    let (public_values, justification) =
        check_coin_proof_step(vkey, owner_pk, coin_commitment, entry_k, slot, append_path,
            registry, inner, parent_nullifier, own_nullifier)
            .expect("the CoinProof relation does not hold for this step");

    // Verify the previous IVC step's coin-proof recursively.
    if let CoinProofJustification::Step { inner_public_values } = &justification {
        let digest: [u8; 32] = Sha256::digest(inner_public_values.encode()).into();
        sp1_zkvm::lib::verify::verify_sp1_proof(&vkey, &digest);
    }

    // The spend proof that created the tracked coin is a Groth16 proof embedded
    // in the transaction. Recipients verify it directly (externally) — no
    // in-circuit verification needed here.

    sp1_zkvm::io::commit_slice(&public_values.encode());
}
