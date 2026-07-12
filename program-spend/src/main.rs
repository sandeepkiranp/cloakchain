#![no_main]
sp1_zkvm::entrypoint!(main);

use sha2::{Digest, Sha256};
use cloakkchain_lib::{check_spend, BoardEntry, Coin, CoinProofPublicValues, Transaction};

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

    // Non-genesis: verify the spender's coin-proof (compressed STARK) via
    // the deferred verify syscall. The proof was passed by the host via
    // stdin.write_proof; pv_digest is SHA-256 of the committed public values.
    if let Some(cp) = &coin_proof {
        let pv_digest: [u8; 32] = Sha256::digest(&cp.encode()).into();
        sp1_zkvm::lib::verify::verify_sp1_proof(&coin_proof_vkey, &pv_digest);
    }

    sp1_zkvm::io::commit_slice(&public_values.encode());
}
