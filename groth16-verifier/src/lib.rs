use ark_bn254::{Bn254, Fq12, Fr, G1Affine, G1Projective, G2Affine};
use ark_ec::pairing::Pairing;
use ark_ff::{Field, PrimeField};
use ark_serialize::{CanonicalDeserialize, Compress, Validate};
use sha2::{Digest, Sha256};

static GROTH16_VK_BYTES: &[u8] = include_bytes!("../vk-artifacts/groth16_vk.bin");

// SP1 proof byte layout (total 356 bytes from proof.bytes()):
//   [0..4]    = SHA256(groth16_vk)[0..4]  — vk hash prefix
//   [4..36]   = exit_code
//   [36..68]  = vk_root
//   [68..100] = proof_nonce
//   [100..356] = gnark Groth16 proof (256 bytes, uncompressed G1+G2+G1)
const GNARK_PROOF_OFFSET: usize = 100;
const GNARK_PROOF_LEN: usize = 256;

// Gnark compressed-point flag encoding (in MSB)
const GNARK_MASK: u8 = 0b11 << 6;
const GNARK_COMPRESSED_POSITIVE: u8 = 0b10 << 6;
const GNARK_COMPRESSED_NEGATIVE: u8 = 0b11 << 6;
const GNARK_COMPRESSED_INFINITY: u8 = 0b01 << 6;
// Ark compressed-point flag encoding
const ARK_MASK: u8 = 0b11 << 6;
const ARK_COMPRESSED_POSITIVE: u8 = 0b00 << 6;
const ARK_COMPRESSED_NEGATIVE: u8 = 0b10 << 6;
const ARK_COMPRESSED_INFINITY: u8 = 0b01 << 6;

/// Verify an SP1 Groth16 spend proof using ark-bn254 (hardware-multiply path).
///
/// - `proof_bytes`: raw bytes from `proof.bytes()` (356 bytes)
/// - `pv_encode`  : from `proof.public_values.as_slice()`
/// - `vkey_hash`  : hex string from `vk.bytes32()`, e.g. `"0xabcd1234..."`
pub fn verify_sp1_spend_proof(
    proof_bytes: &[u8],
    pv_encode: &[u8],
    vkey_hash: &str,
) -> Result<(), &'static str> {
    if proof_bytes.len() < GNARK_PROOF_OFFSET + GNARK_PROOF_LEN {
        return Err("proof bytes too short");
    }

    // Extract SP1 metadata embedded in the proof prefix.
    let exit_code:   [u8; 32] = proof_bytes[4..36].try_into().unwrap();
    let vk_root:     [u8; 32] = proof_bytes[36..68].try_into().unwrap();
    let proof_nonce: [u8; 32] = proof_bytes[68..100].try_into().unwrap();
    let gnark_bytes            = &proof_bytes[GNARK_PROOF_OFFSET..GNARK_PROOF_OFFSET + GNARK_PROOF_LEN];

    // Decode vkey hash hex string → 32 bytes.
    let vkey_bytes: [u8; 32] = decode_hex32(vkey_hash)?;

    // committed_values_digest = SHA256(pv_encode) with top 3 bits zeroed (fits BN254 scalar field).
    let pv_hash: [u8; 32] = {
        let mut h: [u8; 32] = Sha256::digest(pv_encode).into();
        h[0] &= 0x1f;
        h
    };

    // Build 5 public inputs as Fr elements (big-endian bytes).
    let inputs: Vec<Fr> = [vkey_bytes, pv_hash, exit_code, vk_root, proof_nonce]
        .iter()
        .map(|b| Fr::from_be_bytes_mod_order(b))
        .collect();

    // Parse gnark uncompressed proof → ark affine types.
    let proof_a = parse_gnark_g1(gnark_bytes[0..64].try_into().unwrap())?;
    let proof_b = parse_gnark_g2(gnark_bytes[64..192].try_into().unwrap())?;
    let proof_c = parse_gnark_g1(gnark_bytes[192..256].try_into().unwrap())?;

    // Parse embedded VK (gnark compressed format → ark affine types).
    let (alpha, beta, gamma, delta, s) = parse_gnark_vk(GROTH16_VK_BYTES)?;

    // p = s[0] + Σ inputs[i] * s[i+1]
    let mut p: G1Projective = s[0].into();
    for (i, input) in inputs.iter().enumerate() {
        let term: G1Projective = s[i + 1].into();
        p += term * input;
    }

    // Groth16 check: e(-a, b) · e(alpha, beta) · e(p, gamma) · e(c, delta) == Gt(1)
    let miller_out = Bn254::multi_miller_loop(
        [-proof_a, alpha, p.into(), proof_c],
        [proof_b,  beta,  gamma,    delta],
    );
    match Bn254::final_exponentiation(miller_out) {
        Some(r) if r.0 == Fq12::ONE => Ok(()),
        _ => Err("Groth16 pairing check failed"),
    }
}

// --- hex decoding -----------------------------------------------------------

fn decode_hex32(s: &str) -> Result<[u8; 32], &'static str> {
    let hex = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")).unwrap_or(s);
    if hex.len() != 64 {
        return Err("vkey hash must be exactly 64 hex chars");
    }
    let mut out = [0u8; 32];
    for (i, chunk) in hex.as_bytes().chunks(2).enumerate() {
        out[i] = (nibble(chunk[0])? << 4) | nibble(chunk[1])?;
    }
    Ok(out)
}

fn nibble(b: u8) -> Result<u8, &'static str> {
    Ok(match b {
        b'0'..=b'9' => b - b'0',
        b'a'..=b'f' => b - b'a' + 10,
        b'A'..=b'F' => b - b'A' + 10,
        _ => return Err("invalid hex char in vkey hash"),
    })
}

// --- gnark proof format → ark types ----------------------------------------
// Gnark uses big-endian field elements; ark uses little-endian.
// For G2 Fp2 elements gnark stores (c1, c0) but ark expects (c0, c1).
// Reversing each CHUNK-sized sub-block handles both endianness and component order.

fn convert_endianness<const CHUNK: usize, const N: usize>(bytes: &[u8; N]) -> [u8; N] {
    let mut out = [0u8; N];
    for (i, chunk) in bytes.chunks_exact(CHUNK).enumerate() {
        for (j, &b) in chunk.iter().rev().enumerate() {
            out[i * CHUNK + j] = b;
        }
    }
    out
}

fn parse_gnark_g1(buf: &[u8; 64]) -> Result<G1Affine, &'static str> {
    // Convert each 32-byte field element from big-endian to little-endian.
    let le = convert_endianness::<32, 64>(buf);
    // Ark's uncompressed format appends a 1-byte infinity flag (0 = not infinity).
    let mut with_flag = [0u8; 65];
    with_flag[..64].copy_from_slice(&le);
    G1Affine::deserialize_with_mode(with_flag.as_slice(), Compress::No, Validate::Yes)
        .map_err(|_| "G1 point deserialization failed")
}

fn parse_gnark_g2(buf: &[u8; 128]) -> Result<G2Affine, &'static str> {
    // Reversing each 64-byte block converts (c1.BE, c0.BE) → (c0.LE, c1.LE).
    let le = convert_endianness::<64, 128>(buf);
    let mut with_flag = [0u8; 129];
    with_flag[..128].copy_from_slice(&le);
    G2Affine::deserialize_with_mode(with_flag.as_slice(), Compress::No, Validate::Yes)
        .map_err(|_| "G2 point deserialization failed")
}

fn gnark_flag_to_ark(msb: u8) -> Result<u8, &'static str> {
    let ark = match msb & GNARK_MASK {
        GNARK_COMPRESSED_POSITIVE => ARK_COMPRESSED_POSITIVE,
        GNARK_COMPRESSED_NEGATIVE => ARK_COMPRESSED_NEGATIVE,
        GNARK_COMPRESSED_INFINITY => ARK_COMPRESSED_INFINITY,
        _ => return Err("invalid gnark compression flag"),
    };
    Ok((msb & !ARK_MASK) | ark)
}

fn decompress_g1(bytes: &[u8; 32]) -> Result<G1Affine, &'static str> {
    let mut b = *bytes;
    b[0] = gnark_flag_to_ark(b[0])?;
    b.reverse(); // big-endian → little-endian
    G1Affine::deserialize_with_mode(b.as_slice(), Compress::Yes, Validate::No)
        .map_err(|_| "compressed G1 deserialization failed")
}

fn decompress_g2(bytes: &[u8; 64]) -> Result<G2Affine, &'static str> {
    let mut b = *bytes;
    b[0] = gnark_flag_to_ark(b[0])?;
    b.reverse(); // big-endian (c1, c0) → little-endian (c0, c1)
    G2Affine::deserialize_with_mode(b.as_slice(), Compress::Yes, Validate::No)
        .map_err(|_| "compressed G2 deserialization failed")
}

// SP1 gnark VK layout (492 bytes):
//   [0..32]    alpha_g1        (compressed G1)
//   [32..64]   g1_beta         (not used in verification)
//   [64..128]  beta_g2         (compressed G2)
//   [128..192] gamma_g2        (compressed G2)
//   [192..224] g1_gamma        (not used)
//   [224..288] delta_g2        (compressed G2)
//   [288..292] num_k           (u32 big-endian)
//   [292..]    k[0..num_k]     (compressed G1, 32 bytes each)
fn parse_gnark_vk(
    vk: &[u8],
) -> Result<(G1Affine, G2Affine, G2Affine, G2Affine, Vec<G1Affine>), &'static str> {
    if vk.len() < 292 {
        return Err("vk too short");
    }
    let alpha = decompress_g1(vk[0..32].try_into().unwrap())?;
    let beta   = decompress_g2(vk[64..128].try_into().unwrap())?;
    let gamma  = decompress_g2(vk[128..192].try_into().unwrap())?;
    let delta  = decompress_g2(vk[224..288].try_into().unwrap())?;

    let num_k = u32::from_be_bytes(vk[288..292].try_into().unwrap()) as usize;
    if vk.len() < 292 + num_k * 32 {
        return Err("vk k-points truncated");
    }
    let mut s = Vec::with_capacity(num_k);
    for i in 0..num_k {
        let off = 292 + i * 32;
        s.push(decompress_g1(vk[off..off + 32].try_into().unwrap())?);
    }

    Ok((alpha, beta, gamma, delta, s))
}
