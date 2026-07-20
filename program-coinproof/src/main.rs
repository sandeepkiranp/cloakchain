#![no_main]
sp1_zkvm::entrypoint!(main);

use sha2::{Digest, Sha256};
use cloakkchain_lib::{
    check_coin_proof_step, BoardEntry, CoinProofJustification, CoinProofPublicValues,
};

pub fn main() {
    // SP1 6.2.3 single-shard DivF workaround: the recursion circuit emits an
    // unsatisfiable DivF(in2=0, in1≠0) for single-shard programs; multi-shard
    // programs use a different recursion path that avoids the bug.
    //
    // Pure RISC-V arithmetic loop: ~6 instructions/iter (mul + add + black_box
    // sw/lw + counter + branch).  100K iters ≈ 600K cycles → 3 shards at
    // SHARD_SIZE=262144, guaranteed without relying on precompile call costs.
    {
        let mut acc = 0u32;
        for i in 0u32..100_000 {
            acc = core::hint::black_box(acc).wrapping_mul(1_664_525).wrapping_add(i);
        }
        let _ = core::hint::black_box(acc);
    }

    let vkey: [u32; 8]             = sp1_zkvm::io::read();
    let vfy_g16_vkey: [u32; 8]     = sp1_zkvm::io::read();
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

    // Inner coin-proof: verify via deferred compressed-STARK check (~100 cycles).
    // Consumes the first proof written via stdin.write_proof.
    if let CoinProofJustification::Step { inner_public_values, .. } = &justification {
        let pv_digest: [u8; 32] = Sha256::digest(&inner_public_values.encode()).into();
        sp1_zkvm::lib::verify::verify_sp1_proof(&vkey, &pv_digest);
    }

    // Receipt slot: verify the VFY_G16_ELF validation proof (~100 cycles).
    // Consumes the next proof written via stdin.write_proof.
    let receipt = match &justification {
        CoinProofJustification::Base { receipt: Some(r) } => Some(r),
        CoinProofJustification::Step { receipt: Some(r), .. } => Some(r),
        _ => None,
    };
    if let Some(r) = receipt {
        let pv_digest: [u8; 32] = Sha256::digest(&r.pv_encode).into();
        sp1_zkvm::lib::verify::verify_sp1_proof(&vfy_g16_vkey, &pv_digest);
    }

    sp1_zkvm::io::commit_slice(&public_values.encode());
}
