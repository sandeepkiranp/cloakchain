// CloakChain spend (Valid) circuit.
//
// Proves that party P may spend coin_commitment:
//   1. input_nullifier == Blake2s(coin_commitment || sk_p)
//   2. Input coin preimages match tx*.input_commitments
//   3. Output coin preimages match tx*.output_commitments
//   4. Sum(input values) == Sum(output values) -- conservation
//   5. For non-genesis: coin-proof shows received_at_valid && !spent
//
// All hashes use Blake2s-256 (matches Rust blake2 crate).
//
// Public output: Blake2s(board_root(32) || num_outputs_le8(8) || cn_0..cn_7(256))

use bb_proof_verification::{UltraHonkProof, UltraHonkVerificationKey, verify_honk_proof_non_zk};

// ---- integer helpers -------------------------------------------------------

fn u64_to_le_bytes(x: u64) -> [u8; 8] {
    [
        (x & 0xff) as u8,
        ((x >> 8) & 0xff) as u8,
        ((x >> 16) & 0xff) as u8,
        ((x >> 24) & 0xff) as u8,
        ((x >> 32) & 0xff) as u8,
        ((x >> 40) & 0xff) as u8,
        ((x >> 48) & 0xff) as u8,
        ((x >> 56) & 0xff) as u8,
    ]
}

// ---- Blake2s helpers -------------------------------------------------------

fn blake2s_64(a: [u8; 32], b: [u8; 32]) -> [u8; 32] {
    let mut buf = [0 as u8; 64];
    for i in 0..32 { buf[i] = a[i]; }
    for i in 0..32 { buf[32 + i] = b[i]; }
    std::hash::blake2s(buf)
}

fn bytes32_to_fields(b: [u8; 32]) -> [Field; 32] {
    let mut out = [0 as Field; 32];
    for i in 0..32 { out[i] = b[i] as Field; }
    out
}

// ---- Constants -------------------------------------------------------------

global MAX_INPUTS: u32 = 8;
global MAX_OUTPUTS: u32 = 8;

// Coin commitment preimage: tag(32) || value_le8(8) || rand(32) || owner_pk(32) = 104 bytes
global COIN_PREIMAGE_LEN: u32 = 104;

// ---- Coin commitment -------------------------------------------------------

// Matches Coin::commitment() in lib/src/lib.rs.
fn compute_coin_commitment(
    tag: [u8; 32],
    value: u64,
    rand: [u8; 32],
    owner_pk: [u8; 32],
) -> [u8; 32] {
    let mut pre = [0 as u8; COIN_PREIMAGE_LEN];
    for i in 0..32 { pre[i] = tag[i]; }
    let vb = u64_to_le_bytes(value);
    for i in 0..8 { pre[32 + i] = vb[i]; }
    for i in 0..32 { pre[40 + i] = rand[i]; }
    for i in 0..32 { pre[72 + i] = owner_pk[i]; }
    std::hash::blake2s(pre)
}

// ---- Spend state hash ------------------------------------------------------
//
// Layout: board_root(32) || num_outputs_le8(8) || cn_0..cn_7(256) = 296 bytes.
// Unused commitment slots are zero-padded (matches Rust host encoding).
global SPEND_STATE_BUF_LEN: u32 = 296;

fn spend_state_hash(
    board_root: [u8; 32],
    output_commitments: [[u8; 32]; MAX_OUTPUTS],
    num_outputs: u64,
) -> [u8; 32] {
    let mut buf = [0 as u8; SPEND_STATE_BUF_LEN];
    for i in 0..32 { buf[i] = board_root[i]; }
    let nb = u64_to_le_bytes(num_outputs);
    for i in 0..8 { buf[32 + i] = nb[i]; }
    for i in 0..MAX_OUTPUTS {
        let off = 40 + i * 32;
        for j in 0..32 { buf[off + j] = output_commitments[i][j]; }
    }
    std::hash::blake2s(buf)
}

// ---- Coinproof state hash --------------------------------------------------
//
// Must match state_hash() in circuits/coinproof/src/main.nr exactly.
// Layout (147 bytes):
//   owner_pk(32) | coin_commitment(32) | board_root(32) |
//   board_size_le8(8) | received_at_valid(1) | received_at_le8(8) |
//   spent(1) | parent_nullifier(32) | parent_nullifier_seen(1)
global CP_STATE_BUF_LEN: u32 = 147;

fn coinproof_state_hash(
    owner_pk: [u8; 32],
    coin_commitment: [u8; 32],
    board_root: [u8; 32],
    board_size: u64,
    received_at_valid: bool,
    received_at: u64,
    spent: bool,
    parent_nullifier: [u8; 32],
    parent_nullifier_seen: bool,
) -> [u8; 32] {
    let mut buf = [0 as u8; CP_STATE_BUF_LEN];
    for i in 0..32 { buf[i]      = owner_pk[i]; }
    for i in 0..32 { buf[32 + i] = coin_commitment[i]; }
    for i in 0..32 { buf[64 + i] = board_root[i]; }
    let bsb = u64_to_le_bytes(board_size);
    for i in 0..8 { buf[96 + i] = bsb[i]; }
    buf[104] = if received_at_valid { 1 } else { 0 };
    let rab = u64_to_le_bytes(received_at);
    for i in 0..8 { buf[105 + i] = rab[i]; }
    buf[113] = if spent { 1 } else { 0 };
    for i in 0..32 { buf[114 + i] = parent_nullifier[i]; }
    buf[146] = if parent_nullifier_seen { 1 } else { 0 };
    std::hash::blake2s(buf)
}

// ---- Main ------------------------------------------------------------------

fn main(
    // --- spender identity ---
    sk_p: [u8; 32],
    pk_p: pub [u8; 32],

    // --- coin being spent ---
    coin_commitment_in: pub [u8; 32],

    // --- board anchor ---
    board_root: pub [u8; 32],

    // --- spend nullifier (public so validators can bind it to BoardEntry.nullifier) ---
    input_nullifier: pub [u8; 32],
    input_tags:       [[u8; 32]; MAX_INPUTS],
    input_values:     [u64;       MAX_INPUTS],
    input_rands:      [[u8; 32]; MAX_INPUTS],
    input_owner_pks:  [[u8; 32]; MAX_INPUTS],
    num_inputs: u64,
    output_tags:      [[u8; 32]; MAX_OUTPUTS],
    output_values:    [u64;       MAX_OUTPUTS],
    output_rands:     [[u8; 32]; MAX_OUTPUTS],
    output_owner_pks: [[u8; 32]; MAX_OUTPUTS],
    num_outputs: u64,
    tx_input_commitments:  [[u8; 32]; MAX_INPUTS],
    tx_output_commitments: [[u8; 32]; MAX_OUTPUTS],

    // --- genesis flag ---
    is_genesis: bool,

    // --- recursive coin-proof (final step, non-genesis only) ---
    has_coin_proof: bool,
    coinproof_vk: UltraHonkVerificationKey,
    coinproof_proof: UltraHonkProof,
    coinproof_vk_hash: Field,
    cp_slot: u64,
    cp_state_hash: [u8; 32],
    cp_owner_pk: [u8; 32],
    cp_coin_commitment: [u8; 32],
    cp_board_root: [u8; 32],
    cp_board_size: u64,
    cp_received_at_valid: bool,
    cp_received_at: u64,
    cp_spent: bool,
    cp_parent_nullifier: [u8; 32],
    cp_parent_nullifier_seen: bool,
) -> pub [u8; 32] {

    // ---- 1. Nullifier: Blake2s(coin_commitment_in || sk_p) ----------------
    let expected_nullifier = blake2s_64(coin_commitment_in, sk_p);
    assert(input_nullifier == expected_nullifier,
        "input_nullifier does not match Blake2s(coin_commitment || sk_p)");

    // ---- 2. coin_commitment_in must appear in tx*.input_commitments -------
    let mut found_coin = false;
    for i in 0..MAX_INPUTS {
        if (i as u64) < num_inputs {
            if tx_input_commitments[i] == coin_commitment_in {
                found_coin = true;
            }
        }
    }
    assert(found_coin, "tx does not spend the claimed coin");

    // ---- 3. Input coin preimage checks ------------------------------------
    let mut total_in: u64 = 0;
    for i in 0..MAX_INPUTS {
        if (i as u64) < num_inputs {
            let cn = compute_coin_commitment(
                input_tags[i], input_values[i], input_rands[i], input_owner_pks[i],
            );
            assert(cn == tx_input_commitments[i], "input coin commitment mismatch");
            assert(input_owner_pks[i] == pk_p,    "input coin is not owned by pk_p");
            total_in += input_values[i];
        }
    }

    // ---- 4. Output coin preimage checks -----------------------------------
    let mut total_out: u64 = 0;
    for i in 0..MAX_OUTPUTS {
        if (i as u64) < num_outputs {
            let cn = compute_coin_commitment(
                output_tags[i], output_values[i], output_rands[i], output_owner_pks[i],
            );
            assert(cn == tx_output_commitments[i], "output coin commitment mismatch");
            total_out += output_values[i];
        }
    }

    // ---- 5. Value conservation --------------------------------------------
    assert(total_in == total_out, "transaction violates value conservation");

    // ---- 6. Coin-proof or genesis check -----------------------------------
    if is_genesis {
        let genesis_sk = [0 as u8; 32];
        assert(sk_p == genesis_sk, "only the genesis key may mint without provenance");
    } else {
        assert(has_coin_proof, "non-genesis spends require a coin-proof");

        let recomputed = coinproof_state_hash(
            cp_owner_pk, cp_coin_commitment, cp_board_root,
            cp_board_size, cp_received_at_valid, cp_received_at,
            cp_spent, cp_parent_nullifier, cp_parent_nullifier_seen,
        );
        assert(recomputed == cp_state_hash, "coin-proof state witnesses mismatch");

        // Build 129-field coinproof public inputs (same layout as coinproof_base + coinproof_step):
        //   [0..32] owner_pk | [32..64] coin_commitment | [64] slot |
        //   [65..97] parent_nullifier | [97..129] state_hash
        let mut cp_pub_fields: [Field; 129] = [0; 129];
        for i in 0..32 { cp_pub_fields[i]      = cp_owner_pk[i] as Field; }
        for i in 0..32 { cp_pub_fields[32 + i] = cp_coin_commitment[i] as Field; }
        cp_pub_fields[64] = cp_slot as Field;
        for i in 0..32 { cp_pub_fields[65 + i] = cp_parent_nullifier[i] as Field; }
        let cp_state_fields = bytes32_to_fields(cp_state_hash);
        for i in 0..32 { cp_pub_fields[97 + i] = cp_state_fields[i]; }
        verify_honk_proof_non_zk(coinproof_vk, coinproof_proof, cp_pub_fields, coinproof_vk_hash);

        assert(cp_owner_pk == pk_p,              "coin-proof owner must be pk_p");
        assert(cp_coin_commitment == coin_commitment_in, "coin-proof tracks wrong coin");
        assert(cp_board_root == board_root,      "coin-proof board root mismatch");
        assert(cp_received_at_valid,             "coin was not received at any prior slot");
        assert(!cp_spent,                        "coin was already spent (double spend)");
    }

    // ---- 7. Public output -------------------------------------------------
    spend_state_hash(board_root, tx_output_commitments, num_outputs)
}
