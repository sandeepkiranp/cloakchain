//! The recursive `Valid` relation from §3 of "Embedding Data Into Transactions".
//!
//! All relation logic lives in [`cloakkchain_lib::check_valid`].  This program
//! is a thin wrapper that reads witnesses from stdin, calls that function, performs
//! the one step that requires real zkVM machinery (verifying the recursive proof),
//! and commits the public values.
//!
//! The Merkle root of the complete bulletin board is a PUBLIC output.  Carol
//! independently computes her own root from the real board and checks it matches —
//! this is the external half of the completeness fix.  The in-circuit half
//! (verifying each transaction's inclusion proof against that root) happens inside
//! `check_valid`.

#![no_main]
sp1_zkvm::entrypoint!(main);

use cloakkchain_lib::{check_valid, Justification, Transaction};
use sha2::{Digest, Sha256};

pub fn main() {
    let vkey: [u32; 8] = sp1_zkvm::io::read();
    let sk_p: [u8; 32] = sp1_zkvm::io::read();
    let pk_p: [u8; 32] = sp1_zkvm::io::read();
    let board_root: [u8; 32] = sp1_zkvm::io::read();
    let transactions: Vec<Transaction> = sp1_zkvm::io::read();
    let merkle_proofs: Vec<Vec<[u8; 32]>> = sp1_zkvm::io::read();
    let is_genesis: bool = sp1_zkvm::io::read();
    let t: Option<u32> = if is_genesis { None } else { Some(sp1_zkvm::io::read()) };

    let (public_values, justification) =
        check_valid(vkey, sk_p, pk_p, board_root, transactions, merkle_proofs, is_genesis, t)
            .expect("the Valid relation does not hold for this transaction");

    if let Justification::Recursive { inner_public_values, .. } = &justification {
        let digest: [u8; 32] = Sha256::digest(inner_public_values.encode()).into();
        sp1_zkvm::lib::verify::verify_sp1_proof(&vkey, &digest);
    }

    sp1_zkvm::io::commit_slice(&public_values.encode());
}
