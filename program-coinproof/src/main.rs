//! One step of the IVC `CoinProof` relation.
//!
//! All relation logic lives in [`cloakkchain_lib::check_coin_proof_step`]. This
//! program reads the witnesses for one board slot, calls that function, and (for
//! every step after the first) verifies the previous step's proof of itself
//! before committing the new public values.

#![no_main]
sp1_zkvm::entrypoint!(main);

use cloakkchain_lib::{
    check_coin_proof_step, BoardEntry, CoinProofJustification, CoinProofPublicValues,
    ValidPublicValues,
};
use sha2::{Digest, Sha256};

pub fn main() {
    let vkey: [u32; 8] = sp1_zkvm::io::read();
    // spend_vkey is the verifying key for `program-spend`. Used to verify the
    // spend proof embedded in the transaction that first delivered a coin to
    // this owner — proving the transaction was genuinely authorised.
    let spend_vkey: [u32; 8] = sp1_zkvm::io::read();
    let owner_pk: [u8; 32] = sp1_zkvm::io::read();
    let coin_commitment: [u8; 32] = sp1_zkvm::io::read();
    let entry_k: BoardEntry = sp1_zkvm::io::read();
    let slot: usize = sp1_zkvm::io::read();
    let append_path: Vec<[u8; 32]> = sp1_zkvm::io::read();
    let registry: Vec<[u8; 32]> = sp1_zkvm::io::read();
    let has_inner: bool = sp1_zkvm::io::read();
    let inner: Option<CoinProofPublicValues> =
        if has_inner { Some(sp1_zkvm::io::read()) } else { None };

    let (public_values, justification, receipt_spend_pv) =
        check_coin_proof_step(vkey, owner_pk, coin_commitment, entry_k, slot, append_path, registry, inner)
            .expect("the CoinProof relation does not hold for this step");

    // Verify the previous IVC step's coin-proof (existing recursive check).
    if let CoinProofJustification::Step { inner_public_values } = &justification {
        let digest: [u8; 32] = Sha256::digest(inner_public_values.encode()).into();
        sp1_zkvm::lib::verify::verify_sp1_proof(&vkey, &digest);
    }

    // Verify the spend proof that CREATED the coin we just received.
    // This ensures no fake coin was accepted — the transaction that outputted
    // this coin must have been backed by a genuine, valid spend proof.
    // The compressed proof bytes are passed via stdin.write_proof by the host;
    // here we provide the digest so verify_sp1_proof knows which proof to check.
    if let Some(spend_pv_bytes) = receipt_spend_pv {
        let spend_pv: ValidPublicValues = bincode::deserialize(&spend_pv_bytes)
            .expect("failed to decode spend proof public values");
        let digest: [u8; 32] = Sha256::digest(spend_pv.encode()).into();
        sp1_zkvm::lib::verify::verify_sp1_proof(&spend_vkey, &digest);
    }

    sp1_zkvm::io::commit_slice(&public_values.encode());
}
