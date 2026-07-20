#![no_main]
sp1_zkvm::entrypoint!(main);

use sha2::{Digest, Sha256};
use cloakkchain_lib::{
    check_coin_proof_step, BoardEntry, CoinProofJustification, CoinProofPublicValues,
};

pub fn main() {
    // SP1 6.2.3 recursion workaround: the compress circuit evaluates every chip's
    // log-up polynomial at a random challenge point.  For a chip with zero events
    // the polynomial is identically 0, so that evaluation = 0.  For one specific
    // chip (Uint256MulModUser, activated by the UINT256_MUL / sys_bigint ecall)
    // the circuit computes SubF(1, eval) / eval; when eval = 0 this gives DivF(1, 0)
    // → panic at step ~174554.
    //
    // VFY-G16 avoids the crash because substrate-bn calls sys_bigint hundreds of
    // times during Groth16 verification (U256 modular multiply in arith.rs:333),
    // making the Uint256MulModUser evaluation non-zero.
    //
    // Fix: one dummy sys_bigint call gives coinproof ≥1 UINT256_MUL event so the
    // chip evaluation polynomial is non-zero → DivF succeeds.
    unsafe {
        // 2 × 3 mod 7 = 6  — any valid modular multiplication activates the chip.
        let x          = core::hint::black_box([2u64, 0, 0, 0]);
        let y          = core::hint::black_box([3u64, 0, 0, 0]);
        let modulus    = core::hint::black_box([7u64, 0, 0, 0]);
        let mut result = core::mem::MaybeUninit::<[u64; 4]>::uninit();
        sp1_zkvm::syscalls::sys_bigint(
            result.as_mut_ptr() as *mut [u64; 4],
            0,
            &x       as *const [u64; 4],
            &y       as *const [u64; 4],
            &modulus as *const [u64; 4],
        );
        let _ = core::hint::black_box(result.assume_init());
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
