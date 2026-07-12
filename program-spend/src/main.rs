//! The `Valid` (spend) relation from §3 of "Embedding Data Into Transactions".
//!
//! All relation logic lives in [`cloakkchain_lib::check_spend`]. This program
//! reads the witnesses from stdin, calls that function, and — for non-genesis
//! spends — verifies the spender's latest `CoinProof` (proved by the
//! `cloakkchain-program-coinproof` program) via `Groth16Verifier::verify`
//! before committing the public values.
//!
//! The Merkle root of the complete (encrypted) bulletin board is a PUBLIC
//! output. Carol independently computes her own root from the real board and
//! checks it matches — this is the external half of the completeness fix. The
//! in-circuit half (decrypting and verifying the inclusion proof of `tx*`, and
//! checking the spender's coin-proof) happens inside `check_spend`.

#![no_main]
sp1_zkvm::entrypoint!(main);

use cloakkchain_lib::{check_spend, BoardEntry, Coin, CoinProofPublicValues, Transaction};

pub fn main() {
    let vkey: [u32; 8] = sp1_zkvm::io::read();
    let coin_proof_vkey: [u32; 8] = sp1_zkvm::io::read();
    let sk_p: [u8; 32] = sp1_zkvm::io::read();
    let pk_p: [u8; 32] = sp1_zkvm::io::read();
    let coin_commitment: [u8; 32] = sp1_zkvm::io::read();
    let prior_entries: Vec<BoardEntry> = sp1_zkvm::io::read();
    let tx_star: Transaction = sp1_zkvm::io::read();
    let input_coins: Vec<Coin> = sp1_zkvm::io::read();
    let output_coins: Vec<Coin> = sp1_zkvm::io::read();
    let is_genesis: bool = sp1_zkvm::io::read();
    let coin_proof: Option<CoinProofPublicValues> =
        if is_genesis { None } else { Some(sp1_zkvm::io::read()) };
    // Groth16 coin-proof hint — only present for non-genesis spends.
    let coin_proof_bytes: Vec<u8>    = if is_genesis { vec![] } else { sp1_zkvm::io::read_vec() };
    let coin_proof_vkey_hash: String = if is_genesis { String::new() } else { sp1_zkvm::io::read() };

    let public_values = check_spend(
        vkey,
        coin_proof_vkey,
        sk_p,
        pk_p,
        coin_commitment,
        prior_entries,
        tx_star,
        input_coins,
        output_coins,
        is_genesis,
        coin_proof.clone(),
    )
    .expect("the Valid relation does not hold for this transaction");

    if let Some(cp) = &coin_proof {
        sp1_verifier::Groth16Verifier::verify(
            &coin_proof_bytes,
            &cp.encode(),
            &coin_proof_vkey_hash,
            *sp1_verifier::GROTH16_VK_BYTES,
        )
        .expect("coin-proof Groth16 verification failed");
    }

    sp1_zkvm::io::commit_slice(&public_values.encode());
}
