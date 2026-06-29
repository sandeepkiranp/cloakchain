//! Self-contained Groth16 verifier for SP1 spend proofs.
//!
//! Extracted from sp1-verifier (v6.2.3) to run inside the zkVM without its
//! heavy recursion dependencies. Uses `substrate-bn-succinct-rs` for BN254
//! arithmetic, which is patched by Succinct to use SP1's BN254 precompiles.
//!
//! The Groth16 VK is embedded as a 492-byte constant for SP1 v6.2.3.

use alloc::vec::Vec;
use bn::{pairing_batch, AffineG1, AffineG2, Fq, Fq2, Fr, Gt, G1, G2};
use sha2::{Digest, Sha256};

// ── Constants ─────────────────────────────────────────────────────────────────

const GROTH16_VK_BYTES: &[u8] = include_bytes!("groth16_vk.bin");

const VK_HASH_PREFIX_LEN: usize = 4;
/// Layout of proof.bytes(): [4 vk_hash | 32 exit_code | 32 vk_root | 32 nonce | 256 gnark]
const HEADER_LEN: usize = VK_HASH_PREFIX_LEN + 32 + 32 + 32;
const GROTH16_GNARK_LEN: usize = 256; // 2 uncompressed G1 + 1 uncompressed G2

const MASK: u8 = 0b11 << 6;
const COMPRESSED_POSITIVE: u8 = 0b10 << 6;
const COMPRESSED_NEGATIVE: u8 = 0b11 << 6;
const COMPRESSED_INFINITY: u8 = 0b01 << 6;

// ── Error ─────────────────────────────────────────────────────────────────────

#[derive(Debug)]
pub enum Groth16Error {
    InvalidProofBytes,
    InvalidVkBytes,
    VkHashMismatch,
    VkeyHashMismatch,
    PrepareInputsFailed,
    ProofVerificationFailed,
    FieldError,
    GroupError,
}

impl core::fmt::Display for Groth16Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}", self)
    }
}

// ── Internal types ────────────────────────────────────────────────────────────

struct Groth16VerifyingKey {
    alpha: AffineG1,
    k: Vec<AffineG1>,
    beta: AffineG2,
    delta: AffineG2,
    gamma: AffineG2,
}

struct Groth16Proof {
    ar: AffineG1,
    bs: AffineG2,
    krs: AffineG1,
}

// ── Compressed-point flag ─────────────────────────────────────────────────────

#[derive(PartialEq, Eq)]
enum Flag { Positive, Negative, Infinity }

impl Flag {
    fn from_byte(b: u8) -> Option<Self> {
        match b & MASK {
            COMPRESSED_POSITIVE => Some(Flag::Positive),
            COMPRESSED_NEGATIVE => Some(Flag::Negative),
            COMPRESSED_INFINITY => Some(Flag::Infinity),
            _ => None,
        }
    }
}

// ── Point parsing ─────────────────────────────────────────────────────────────

fn uncompressed_g1(buf: &[u8]) -> Result<AffineG1, Groth16Error> {
    if buf.len() != 64 { return Err(Groth16Error::InvalidProofBytes); }
    let x = Fq::from_slice(&buf[..32]).map_err(|_| Groth16Error::FieldError)?;
    let y = Fq::from_slice(&buf[32..]).map_err(|_| Groth16Error::FieldError)?;
    AffineG1::new(x, y).map_err(|_| Groth16Error::GroupError)
}

fn uncompressed_g2(buf: &[u8]) -> Result<AffineG2, Groth16Error> {
    if buf.len() != 128 { return Err(Groth16Error::InvalidProofBytes); }
    let x1 = Fq::from_slice(&buf[..32]).map_err(|_| Groth16Error::FieldError)?;
    let x0 = Fq::from_slice(&buf[32..64]).map_err(|_| Groth16Error::FieldError)?;
    let y1 = Fq::from_slice(&buf[64..96]).map_err(|_| Groth16Error::FieldError)?;
    let y0 = Fq::from_slice(&buf[96..]).map_err(|_| Groth16Error::FieldError)?;
    AffineG2::new(Fq2::new(x0, x1), Fq2::new(y0, y1)).map_err(|_| Groth16Error::GroupError)
}

fn compressed_g1(buf: &[u8]) -> Result<AffineG1, Groth16Error> {
    if buf.len() != 32 { return Err(Groth16Error::InvalidVkBytes); }
    let flag = Flag::from_byte(buf[0]).ok_or(Groth16Error::InvalidVkBytes)?;
    if flag == Flag::Infinity {
        return Err(Groth16Error::InvalidVkBytes);
    }
    let mut xb = [0u8; 32];
    xb.copy_from_slice(buf);
    xb[0] &= !MASK;
    let x = Fq::from_be_bytes_mod_order(&xb).map_err(|_| Groth16Error::FieldError)?;
    let (y, neg_y) = AffineG1::get_ys_from_x_unchecked(x).ok_or(Groth16Error::InvalidVkBytes)?;
    let final_y = if y > neg_y {
        if flag == Flag::Positive { -y } else { y }
    } else {
        if flag == Flag::Negative { -y } else { y }
    };
    Ok(AffineG1::new_unchecked(x, final_y))
}

fn compressed_g2(buf: &[u8]) -> Result<AffineG2, Groth16Error> {
    if buf.len() != 64 { return Err(Groth16Error::InvalidVkBytes); }
    let flag = Flag::from_byte(buf[0]).ok_or(Groth16Error::InvalidVkBytes)?;
    if flag == Flag::Infinity { return Ok(AffineG2::zero()); }
    let x1 = {
        let mut xb = [0u8; 32];
        xb.copy_from_slice(&buf[..32]);
        xb[0] &= !MASK;
        Fq::from_be_bytes_mod_order(&xb).map_err(|_| Groth16Error::FieldError)?
    };
    let x0 = Fq::from_be_bytes_mod_order(&buf[32..64]).map_err(|_| Groth16Error::FieldError)?;
    let x = Fq2::new(x0, x1);
    let (y, neg_y) = AffineG2::get_ys_from_x_unchecked(x).ok_or(Groth16Error::InvalidVkBytes)?;
    match flag {
        Flag::Positive => Ok(AffineG2::new_unchecked(x, y)),
        Flag::Negative => Ok(AffineG2::new_unchecked(x, neg_y)),
        _ => Err(Groth16Error::InvalidVkBytes),
    }
}

// ── VK + proof loading ────────────────────────────────────────────────────────

fn load_vk(buf: &[u8]) -> Result<Groth16VerifyingKey, Groth16Error> {
    if buf.len() < 292 { return Err(Groth16Error::InvalidVkBytes); }
    let alpha    = compressed_g1(&buf[..32])?;
    let beta     = -compressed_g2(&buf[64..128])?;   // negated as per sp1-verifier
    let gamma    = compressed_g2(&buf[128..192])?;
    let delta    = compressed_g2(&buf[224..288])?;
    let num_k = u32::from_be_bytes([buf[288], buf[289], buf[290], buf[291]]) as usize;
    if buf.len() < 292 + num_k * 32 { return Err(Groth16Error::InvalidVkBytes); }
    let mut k = Vec::with_capacity(num_k);
    for i in 0..num_k {
        k.push(compressed_g1(&buf[292 + i * 32..292 + (i + 1) * 32])?);
    }
    Ok(Groth16VerifyingKey { alpha, beta, delta, gamma, k })
}

fn load_proof(buf: &[u8]) -> Result<Groth16Proof, Groth16Error> {
    if buf.len() != GROTH16_GNARK_LEN { return Err(Groth16Error::InvalidProofBytes); }
    Ok(Groth16Proof {
        ar:  uncompressed_g1(&buf[..64])?,
        bs:  uncompressed_g2(&buf[64..192])?,
        krs: uncompressed_g1(&buf[192..256])?,
    })
}

// ── Core algebraic verification ───────────────────────────────────────────────

fn verify_algebraic(
    vk: &Groth16VerifyingKey,
    proof: &Groth16Proof,
    public_inputs: &[Fr],
) -> Result<(), Groth16Error> {
    if (public_inputs.len() + 1) != vk.k.len() {
        return Err(Groth16Error::PrepareInputsFailed);
    }
    let prepared: G1 = public_inputs
        .iter()
        .zip(vk.k.iter().skip(1))
        .fold(vk.k[0], |acc, (i, b)| {
            if *i != Fr::zero() { acc + (*b * *i) } else { acc }
        })
        .into();

    if pairing_batch(&[
        (-Into::<G1>::into(proof.ar), proof.bs.into()),
        (prepared, vk.gamma.into()),
        (proof.krs.into(), vk.delta.into()),
        (vk.alpha.into(), -Into::<G2>::into(vk.beta)),
    ]) == Gt::one()
    {
        Ok(())
    } else {
        Err(Groth16Error::ProofVerificationFailed)
    }
}

// ── Public-input hashing (matches SP1 verifier contract) ─────────────────────

fn hash_public_inputs(pv: &[u8]) -> [u8; 32] {
    let mut h: [u8; 32] = Sha256::digest(pv).into();
    h[0] &= 0x1F; // zero the 3 most-significant bits (field is 254-bit)
    h
}

fn to_fr(bytes: &[u8; 32]) -> Result<Fr, Groth16Error> {
    Fr::from_slice(bytes).map_err(|_| Groth16Error::FieldError)
}

// ── Main entry point ──────────────────────────────────────────────────────────

/// Verify that `proof_bytes` (= `proof.bytes()` from the SP1 SDK) is a valid
/// SP1 Groth16 spend proof for `spend_vkey_hash` with `public_values`.
///
/// This runs the full algebraic Groth16 check inside the zkVM using BN254
/// arithmetic from `substrate-bn-succinct-rs`.
pub fn verify_sp1_groth16(
    proof_bytes: &[u8],
    public_values: &[u8],
    spend_vkey_hash: &[u8; 32],
) -> Result<(), Groth16Error> {
    if proof_bytes.len() < HEADER_LEN + GROTH16_GNARK_LEN {
        return Err(Groth16Error::InvalidProofBytes);
    }

    // Check the first 4 bytes are the correct Groth16 VK hash.
    let vk_hash: [u8; 4] = Sha256::digest(GROTH16_VK_BYTES)[..4].try_into().unwrap();
    if vk_hash != proof_bytes[..VK_HASH_PREFIX_LEN] {
        return Err(Groth16Error::VkHashMismatch);
    }

    let exit_code: &[u8; 32] = proof_bytes[4..36].try_into().unwrap();
    let vk_root:   &[u8; 32] = proof_bytes[36..68].try_into().unwrap();
    let proof_nonce: &[u8; 32] = proof_bytes[68..100].try_into().unwrap();
    let gnark_bytes = &proof_bytes[HEADER_LEN..HEADER_LEN + GROTH16_GNARK_LEN];

    let vk    = load_vk(GROTH16_VK_BYTES)?;
    let proof = load_proof(gnark_bytes)?;

    // Public inputs to the Groth16 circuit (5 × 32-byte field elements):
    //   [sp1_vkey_hash, hash(public_values), exit_code, vk_root, proof_nonce]
    let pv_hash = hash_public_inputs(public_values);
    let inputs_sha256 = [
        to_fr(spend_vkey_hash)?,
        to_fr(&pv_hash)?,
        to_fr(exit_code)?,
        to_fr(vk_root)?,
        to_fr(proof_nonce)?,
    ];
    if verify_algebraic(&vk, &proof, &inputs_sha256).is_ok() {
        return Ok(());
    }

    // Fallback: SP1 v6.x proofs may use blake3 for the public-values hash.
    #[cfg(feature = "blake3")]
    {
        let pv_hash_b3 = {
            let raw = blake3::hash(public_values);
            let mut h = *raw.as_bytes();
            h[0] &= 0x1F;
            h
        };
        let inputs_b3 = [
            to_fr(spend_vkey_hash)?,
            to_fr(&pv_hash_b3)?,
            to_fr(exit_code)?,
            to_fr(vk_root)?,
            to_fr(proof_nonce)?,
        ];
        return verify_algebraic(&vk, &proof, &inputs_b3);
    }

    #[cfg(not(feature = "blake3"))]
    Err(Groth16Error::ProofVerificationFailed)
}
