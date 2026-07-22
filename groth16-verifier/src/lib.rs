use bn::Fr;
use sha2::{Digest, Sha256};
use snark_bn254_verifier::Groth16Verifier;

static GROTH16_VK_BYTES: &[u8] = include_bytes!("../vk-artifacts/groth16_vk.bin");

// SP1 proof byte layout (total 356 bytes from proof.bytes()):
//   [0..4]    = SHA256(groth16_vk)[0..4]  — vk hash prefix
//   [4..36]   = exit_code
//   [36..68]  = vk_root
//   [68..100] = proof_nonce
//   [100..356] = gnark Groth16 proof (256 bytes, uncompressed G1+G2+G1)
const GNARK_PROOF_OFFSET: usize = 100;
const GNARK_PROOF_LEN: usize = 256;

// snark-bn254-verifier's VK parser reads a 128-byte Pedersen commitment key at
// the end of the VK, but SP1 v6's VK is only 492 bytes (no commitment key).
// Append gamma_g2 (bytes [128..192]) twice as dummy bytes — verify_groth16
// never uses the commitment key when num_of_array_of_public_and_commitment_committed=0.
const VK_LEN: usize = 492;
const VK_PADDED_LEN: usize = VK_LEN + 128;

// `load_groth16_verifying_key_from_bytes` (vendor/snark-bn254-verifier) reads, in order:
// g1_alpha(32) + g1_beta(32) + g2_beta(64) + g2_gamma(64) + g1_delta(32) + g2_delta(64) = 288,
// then num_k(4) + k[0..num_k](32 each), then num_of_array_of_public_and_commitment_committed(4).
// For this VK (5 public inputs -> num_k=6) that's 288 + 4 + 32*6 + 4 = 488 bytes of real
// content — 4 bytes short of VK_LEN (492). The file's own trailing 4 bytes (492-VK_LEN..492,
// all zero) aren't part of that read sequence at all.
//
// Appending the dummy commitment-key padding starting at VK_LEN (492) instead of this real
// 488-byte boundary shifts everything the parser reads for `commitment_key_g`/
// `commitment_key_g_root_sigma_neg` by 4 bytes: it ends up reading those 4 trailing zero
// bytes as the start of `commitment_key_g`, whose top 2 bits (0x00) don't match any
// `CompressedPointFlag`, so `unchecked_compressed_x_to_g2_point` panics ("Invalid compressed
// point flag") — even though `verify_groth16` never actually reads the parsed commitment key.
fn real_vk_content_len() -> usize {
    let num_k = u32::from_be_bytes(GROTH16_VK_BYTES[288..292].try_into().unwrap()) as usize;
    288 + 4 + 32 * num_k + 4
}

fn build_padded_vk() -> [u8; VK_PADDED_LEN] {
    let real_len = real_vk_content_len();
    let mut out = [0u8; VK_PADDED_LEN];
    out[..real_len].copy_from_slice(&GROTH16_VK_BYTES[..real_len]);
    out[real_len..real_len + 64].copy_from_slice(&GROTH16_VK_BYTES[128..192]);
    out[real_len + 64..real_len + 128].copy_from_slice(&GROTH16_VK_BYTES[128..192]);
    out
}

/// Verify an SP1 Groth16 spend proof using snark-bn254-verifier (SP1 precompile path).
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

    let exit_code:   [u8; 32] = proof_bytes[4..36].try_into().unwrap();
    let vk_root:     [u8; 32] = proof_bytes[36..68].try_into().unwrap();
    let proof_nonce: [u8; 32] = proof_bytes[68..100].try_into().unwrap();
    let gnark_bytes            = &proof_bytes[GNARK_PROOF_OFFSET..GNARK_PROOF_OFFSET + GNARK_PROOF_LEN];

    let vkey_bytes: [u8; 32] = decode_hex32(vkey_hash)?;

    // committed_values_digest = SHA256(pv_encode) with top 3 bits zeroed.
    let pv_hash: [u8; 32] = {
        let mut h: [u8; 32] = Sha256::digest(pv_encode).into();
        h[0] &= 0x1f;
        h
    };

    // 5 public inputs as bn::Fr (big-endian bytes → field element).
    let inputs: Vec<Fr> = [vkey_bytes, pv_hash, exit_code, vk_root, proof_nonce]
        .iter()
        .map(|b| Fr::from_slice(b).map_err(|_| "Fr conversion failed"))
        .collect::<Result<Vec<_>, _>>()?;

    let padded_vk = build_padded_vk();

    match Groth16Verifier::verify(gnark_bytes, &padded_vk, &inputs) {
        Ok(true)  => Ok(()),
        Ok(false) => Err("Groth16 verification returned false"),
        Err(_)    => Err("Groth16 pairing check failed"),
    }
}

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
