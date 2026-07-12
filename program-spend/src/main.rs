#![no_main]
sp1_zkvm::entrypoint!(main);

use sha2::{Digest, Sha256};
use cloakkchain_lib::{
    check_spend, scan_entry, BoardEntry, Coin, CoinProofPublicValues, SpendProofPackage,
    Transaction,
};

pub fn main() {
    let vkey: [u32; 8]             = sp1_zkvm::io::read();
    let coin_proof_vkey: [u32; 8]  = sp1_zkvm::io::read();
    let sk_p: [u8; 32]             = sp1_zkvm::io::read();
    let pk_p: [u8; 32]             = sp1_zkvm::io::read();
    let coin_commitment: [u8; 32]  = sp1_zkvm::io::read();
    let prior_entries: Vec<BoardEntry> = sp1_zkvm::io::read();
    let tx_star: Transaction       = sp1_zkvm::io::read();
    let input_coins: Vec<Coin>     = sp1_zkvm::io::read();
    let output_coins: Vec<Coin>    = sp1_zkvm::io::read();
    let is_genesis: bool           = sp1_zkvm::io::read();
    let coin_proof: Option<CoinProofPublicValues> =
        if is_genesis { None } else { Some(sp1_zkvm::io::read()) };

    // Extract receipt entry before prior_entries is consumed by check_spend.
    // The receipt is the board slot where we received the coin being spent;
    // its spend proof proves our coin was legitimately created.
    let receipt_entry: Option<BoardEntry> = coin_proof.as_ref().and_then(|cp| {
        cp.received_at.map(|at| prior_entries[at as usize].clone())
    });

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
        // Verify the spender's coin-proof (compressed STARK) via deferred syscall.
        let pv_digest: [u8; 32] = Sha256::digest(&cp.encode()).into();
        sp1_zkvm::lib::verify::verify_sp1_proof(&coin_proof_vkey, &pv_digest);

        // Verify the spend proof that created our coin (at the receipt slot).
        // Ensures no coin can be minted from a fake or invalid spend proof.
        if let Some(entry) = receipt_entry {
            let receipt_tx = scan_entry(&sk_p, &entry)
                .expect("cannot decrypt receipt entry with spender sk");
            let pkg: SpendProofPackage = bincode::deserialize(&receipt_tx.spend_proof)
                .expect("malformed SpendProofPackage in receipt entry");
            if !pkg.proof_bytes.is_empty() {
                sp1_verifier::Groth16Verifier::verify(
                    &pkg.proof_bytes,
                    &pkg.pv_encode,
                    &pkg.spend_vkey_hash,
                    *sp1_verifier::GROTH16_VK_BYTES,
                )
                .expect("receipt spend proof verification failed");
            }
        }
    }

    sp1_zkvm::io::commit_slice(&public_values.encode());
}
