#![no_main]
sp1_zkvm::entrypoint!(main);

use sha2::{Digest, Sha256};
use cloakkchain_lib::{
    check_coin_proof_step, BoardEntry, CoinProofJustification, CoinProofPublicValues,
};

pub fn main() {
    // SP1 6.2.3 recursion workaround: the compress circuit reads a combined BN254
    // chip evaluation from the proof at initialisation; when coinproof makes zero
    // BN254 precompile calls that evaluation is 0, and the circuit later computes
    // DivF(1, 0) → panic.  VFY-G16 uses BN254 arithmetic (via substrate-bn) so
    // its evaluation is always non-zero.  One dummy call per BN254 chip type
    // ensures every chip has ≥1 event → evaluation ≠ 0 → DivF succeeds.
    //
    // Chips activated: BN254_FP_{ADD,SUB,MUL}, BN254_FP2_{ADD,SUB,MUL},
    //                  BN254_{ADD,DOUBLE}  (8 ecalls total, ~negligible cycles).
    unsafe {
        // --- BN254 Fp field arithmetic (256-bit limbs, 4 × u64 LE) ---
        let mut fp_a = core::hint::black_box([1u64, 0, 0, 0]); // Fp element 1
        let fp_b     = core::hint::black_box([2u64, 0, 0, 0]); // Fp element 2
        sp1_zkvm::syscalls::syscall_bn254_fp_addmod(fp_a.as_mut_ptr(), fp_b.as_ptr()); // 1+2=3
        sp1_zkvm::syscalls::syscall_bn254_fp_submod(fp_a.as_mut_ptr(), fp_b.as_ptr()); // 3-2=1
        sp1_zkvm::syscalls::syscall_bn254_fp_mulmod(fp_a.as_mut_ptr(), fp_b.as_ptr()); // 1*2=2
        let _ = core::hint::black_box(fp_a);

        // --- BN254 Fp2 field arithmetic (512-bit limbs, 8 × u64 LE) ---
        let mut fp2_a = core::hint::black_box([1u64, 0, 0, 0, 0, 0, 0, 0]); // (1, 0)
        let fp2_b     = core::hint::black_box([2u64, 0, 0, 0, 0, 0, 0, 0]); // (2, 0)
        sp1_zkvm::syscalls::syscall_bn254_fp2_addmod(fp2_a.as_mut_ptr(), fp2_b.as_ptr()); // (3,0)
        sp1_zkvm::syscalls::syscall_bn254_fp2_submod(fp2_a.as_mut_ptr(), fp2_b.as_ptr()); // (1,0)
        sp1_zkvm::syscalls::syscall_bn254_fp2_mulmod(fp2_a.as_mut_ptr(), fp2_b.as_ptr()); // (2,0)
        let _ = core::hint::black_box(fp2_a);

        // --- BN254 group operations (affine point = Gx ++ Gy, 8 × u64 LE) ---
        // BN254 generator G satisfies y² = x³ + 3: (1)³ + 3 = 4 = (2)². ✓
        let mut g  = core::hint::black_box([1u64, 0, 0, 0, 2, 0, 0, 0]); // G
        let orig_g = core::hint::black_box([1u64, 0, 0, 0, 2, 0, 0, 0]); // G (copy for add)
        sp1_zkvm::syscalls::syscall_bn254_double(
            core::hint::black_box(&mut g) as *mut [u64; 8]                // g = 2G
        );
        sp1_zkvm::syscalls::syscall_bn254_add(
            core::hint::black_box(&mut g) as *mut [u64; 8],               // g = 3G
            &orig_g as *const [u64; 8],
        );
        let _ = core::hint::black_box(g);
    }
    println!("[COINPROOF-DIAG] BN254 chip activation OK");

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
