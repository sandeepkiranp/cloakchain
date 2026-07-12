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

    let (public_values, justification) =
        check_coin_proof_step(vkey, owner_sk, coin_commitment, entry_k, slot, append_path,
            inner, parent_nullifier, own_nullifier)
            .expect("the CoinProof relation does not hold for this step");

    // Inner coin-proof (compressed STARK): verify via deferred syscall.
    if let CoinProofJustification::Step { inner_public_values, .. } = &justification {
        let pv_digest: [u8; 32] = Sha256::digest(&inner_public_values.encode()).into();
        sp1_zkvm::lib::verify::verify_sp1_proof(&vkey, &pv_digest);
    }

    sp1_zkvm::io::commit_slice(&public_values.encode());
}
