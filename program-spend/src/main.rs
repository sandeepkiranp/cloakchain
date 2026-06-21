//! The `Valid` (spend) relation from §3 of "Embedding Data Into Transactions".
//!
//! All relation logic lives in [`cloakkchain_lib::check_spend`]. This program
//! reads the witnesses from stdin, calls that function, and — for non-genesis
//! spends — verifies the spender's latest `CoinProof` (proved by the
//! `cloakkchain-program-coinproof` program, hence the separate `coin_proof_vkey`)
//! before committing the public values.
//!
//! The Merkle root of the complete (encrypted) bulletin board is a PUBLIC
//! output. Carol independently computes her own root from the real board and
//! checks it matches — this is the external half of the completeness fix. The
//! in-circuit half (decrypting and verifying the inclusion proof of `tx*`, and
//! checking the spender's coin-proof) happens inside `check_spend`.

#![no_main]
sp1_zkvm::entrypoint!(main);

use cloakkchain_lib::{check_spend, BoardEntry, CoinProofPublicValues};
use sha2::{Digest, Sha256};

pub fn main() {
    let vkey: [u32; 8] = sp1_zkvm::io::read();
    let coin_proof_vkey: [u32; 8] = sp1_zkvm::io::read();
    let sk_p: [u8; 32] = sp1_zkvm::io::read();
    let pk_p: [u8; 32] = sp1_zkvm::io::read();
    let coin_commitment: [u8; 32] = sp1_zkvm::io::read();
    let entries: Vec<BoardEntry> = sp1_zkvm::io::read();
    let recipient_pk: [u8; 32] = sp1_zkvm::io::read();
    let is_genesis: bool = sp1_zkvm::io::read();
    let coin_proof: Option<CoinProofPublicValues> =
        if is_genesis { None } else { Some(sp1_zkvm::io::read()) };

    let public_values = check_spend(
        vkey,
        coin_proof_vkey,
        sk_p,
        pk_p,
        coin_commitment,
        entries,
        recipient_pk,
        is_genesis,
        coin_proof.clone(),
    )
    .expect("the Valid relation does not hold for this transaction");

    if let Some(cp) = &coin_proof {
        let digest: [u8; 32] = Sha256::digest(cp.encode()).into();
        sp1_zkvm::lib::verify::verify_sp1_proof(&coin_proof_vkey, &digest);
    }

    sp1_zkvm::io::commit_slice(&public_values.encode());
}
