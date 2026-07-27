#![no_main]
sp1_zkvm::entrypoint!(main);

use sha2::{Digest, Sha256};
use cloakkchain_lib::{check_coin_receipt, BoardEntry, NonMembershipWitness};

pub fn main() {
    let vkey: [u32; 8]             = sp1_zkvm::io::read();
    let vfy_g16_vkey: [u32; 8]     = sp1_zkvm::io::read();
    let owner_sk: [u8; 32]         = sp1_zkvm::io::read();
    let coin_commitment: [u8; 32]  = sp1_zkvm::io::read();
    let entry_k: BoardEntry        = sp1_zkvm::io::read();
    let received_slot: usize       = sp1_zkvm::io::read();
    let append_path: Vec<[u8; 32]> = sp1_zkvm::io::read();
    let parent_nonmembership: NonMembershipWitness = sp1_zkvm::io::read();
    let nullifier_root_at_parent_slot: [u8; 32] = sp1_zkvm::io::read();

    let (public_values, justification) = check_coin_receipt(
        vkey, owner_sk, coin_commitment, entry_k, received_slot, append_path,
        parent_nonmembership, nullifier_root_at_parent_slot,
    )
    .expect("the CoinReceipt relation does not hold");

    // Verify the VFY_G16_ELF validation proof (~100 cycles) via deferred
    // compressed-STARK check. Consumes the proof written via stdin.write_proof.
    if let Some(r) = &justification.receipt {
        let pv_digest: [u8; 32] = Sha256::digest(&r.pv_encode).into();
        sp1_zkvm::lib::verify::verify_sp1_proof(&vfy_g16_vkey, &pv_digest);
    }

    sp1_zkvm::io::commit_slice(&public_values.encode());
}
