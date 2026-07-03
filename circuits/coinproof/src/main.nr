// CloakChain coinproof STEP circuit -- slot k > 0, always recursive.
//
// Extends the IVC chain from the previous step (whose proof is always present).
// The inner proof may come from coinproof_base (slot 0) or coinproof_step (slot k-1).
// Both produce the same state_hash encoding so no special casing is needed.
//
// All hashes use Blake2s-256 (matches Rust blake2 crate).
// Public output: Blake2s(state_bytes) as [u8; 32].

use bb_proof_verification::{UltraHonkProof, UltraHonkVerificationKey, verify_honk_proof_non_zk};

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

fn blake2s_pair(a: [u8; 32], b: [u8; 32]) -> [u8; 32] {
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

global TREE_DEPTH: u32 = 32;
global MAX_OUTPUT_COMMITMENTS: u32 = 8;
global LEAF_BUF_LEN: u32 = 296;
global STATE_BUF_LEN: u32 = 147;

fn compute_root(leaf: [u8; 32], slot: u64, path: [[u8; 32]; 32]) -> [u8; 32] {
    let mut current = leaf;
    let mut idx = slot;
    for i in 0..TREE_DEPTH {
        let sibling = path[i];
        if idx % 2 == 0 {
            current = blake2s_pair(current, sibling);
        } else {
            current = blake2s_pair(sibling, current);
        }
        idx = idx / 2;
    }
    current
}

fn compute_leaf(
    slot: u64,
    output_commitments: [[u8; 32]; MAX_OUTPUT_COMMITMENTS],
    ciphertext_hash: [u8; 32],
) -> [u8; 32] {
    let mut buf = [0 as u8; LEAF_BUF_LEN];
    let sb = u64_to_le_bytes(slot);
    for i in 0..8 { buf[i] = sb[i]; }
    for i in 0..MAX_OUTPUT_COMMITMENTS {
        let off = 8 + i * 32;
        for j in 0..32 { buf[off + j] = output_commitments[i][j]; }
    }
    for j in 0..32 { buf[264 + j] = ciphertext_hash[j]; }
    std::hash::blake2s(buf)
}

fn state_hash(
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
    let mut buf = [0 as u8; STATE_BUF_LEN];
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

fn main(
    // --- coin being tracked ---
    owner_pk: pub [u8; 32],
    coin_commitment: pub [u8; 32],

    // --- current board slot (k >= 1) ---
    slot: pub u64,

    // --- board entry at slot k ---
    entry_output_commitments: [[u8; 32]; MAX_OUTPUT_COMMITMENTS],
    entry_num_outputs: u64,
    entry_nullifier: [u8; 32],
    entry_ciphertext_hash: [u8; 32],

    // --- Merkle append path ---
    append_path: [[u8; 32]; 32],

    // --- nullifiers ---
    parent_nullifier: pub [u8; 32],
    own_nullifier: [u8; 32],

    // --- inner proof (always present; from coinproof_base or coinproof_step) ---
    inner_vk: UltraHonkVerificationKey,
    inner_proof: UltraHonkProof,
    inner_vk_hash: Field,
    // Decoded state from the inner proof (private witnesses; hash verified below).
    inner_state_hash: [u8; 32],
    inner_owner_pk: [u8; 32],
    inner_coin_commitment: [u8; 32],
    inner_board_root: [u8; 32],
    inner_board_size: u64,
    inner_received_at_valid: bool,
    inner_received_at: u64,
    inner_spent: bool,
    inner_parent_nullifier: [u8; 32],
    inner_parent_nullifier_seen: bool,

    // --- receipt hint ---
    is_receipt_hint: bool,
) -> pub [u8; 32] {

    // ---- 1. Merkle roots --------------------------------------------------

    let zero_leaf = [0 as u8; 32];
    let old_root = compute_root(zero_leaf, slot, append_path);
    let leaf_k = compute_leaf(slot, entry_output_commitments, entry_ciphertext_hash);
    let new_root = compute_root(leaf_k, slot, append_path);

    // ---- 2. Inner proof verification (always) -----------------------------

    // Both coinproof_base and coinproof_step share the same 129-field public input layout:
    //   [0..32]  owner_pk   (one Field per byte)
    //   [32..64] coin_commitment
    //   [64]     slot       (inner slot = current slot - 1)
    //   [65..97] parent_nullifier
    //   [97..129] state_hash
    // coinproof_base has slot=0 (enforced by its circuit). coinproof_step has slot=k-1.
    // We know inner.owner_pk == owner_pk, inner.coin_commitment == coin_commitment,
    // inner.parent_nullifier == parent_nullifier (asserted below), so we build from them.
    let inner_slot: u64 = slot - 1;
    let mut inner_pub_fields: [Field; 129] = [0; 129];
    for i in 0..32 { inner_pub_fields[i]      = owner_pk[i] as Field; }
    for i in 0..32 { inner_pub_fields[32 + i] = coin_commitment[i] as Field; }
    inner_pub_fields[64] = inner_slot as Field;
    for i in 0..32 { inner_pub_fields[65 + i] = parent_nullifier[i] as Field; }
    let state_fields = bytes32_to_fields(inner_state_hash);
    for i in 0..32 { inner_pub_fields[97 + i] = state_fields[i]; }
    verify_honk_proof_non_zk(inner_vk, inner_proof, inner_pub_fields, inner_vk_hash);

    let recomputed = state_hash(
        inner_owner_pk, inner_coin_commitment, inner_board_root,
        inner_board_size, inner_received_at_valid, inner_received_at,
        inner_spent, inner_parent_nullifier, inner_parent_nullifier_seen,
    );
    assert(recomputed == inner_state_hash, "inner state witnesses mismatch");

    assert(inner_owner_pk == owner_pk,                "inner proof: wrong owner");
    assert(inner_coin_commitment == coin_commitment,   "inner proof: wrong coin");
    assert(inner_parent_nullifier == parent_nullifier, "inner proof: wrong parent nullifier");
    assert(inner_board_size == slot,                   "inner proof: wrong board size");
    assert(inner_board_root == old_root,               "inner proof: wrong board root");

    // ---- 3. Receipt detection ---------------------------------------------

    let mut coin_in_this_entry = false;
    for i in 0..MAX_OUTPUT_COMMITMENTS {
        if (i as u64) < entry_num_outputs {
            if entry_output_commitments[i] == coin_commitment {
                coin_in_this_entry = true;
            }
        }
    }

    let is_receipt = coin_in_this_entry
        & !inner_received_at_valid
        & !inner_parent_nullifier_seen;
    assert(is_receipt == is_receipt_hint, "receipt hint disagrees with in-circuit detection");

    // ---- 4. Nullifier tracking --------------------------------------------

    let parent_nullifier_seen = inner_parent_nullifier_seen
        | (!inner_received_at_valid & (entry_nullifier == parent_nullifier));

    let spent = inner_spent | (entry_nullifier == own_nullifier);

    // ---- 5. State update --------------------------------------------------

    let received_at_valid = inner_received_at_valid | is_receipt;
    let received_at = if is_receipt & !inner_received_at_valid { slot } else { inner_received_at };

    state_hash(
        owner_pk, coin_commitment, new_root,
        slot + 1, received_at_valid, received_at,
        spent, parent_nullifier, parent_nullifier_seen,
    )
}
