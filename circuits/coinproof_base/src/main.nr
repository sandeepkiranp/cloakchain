// CloakChain coinproof BASE CASE circuit -- slot 0, no recursion.
//
// Proves the initial step of the coin-proof IVC for slot k=0.
// No inner proof is required; slot must be 0.
// The output state_hash matches the encoding used by coinproof_step so
// the step circuit can treat a base proof as a valid "inner" proof.
//
// All hashes use Blake2s-256 (matches Rust blake2 crate).
// Public output: Blake2s(state_bytes) as [u8; 32].

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

global TREE_DEPTH: u32 = 32;
global MAX_OUTPUT_COMMITMENTS: u32 = 8;
global LEAF_BUF_LEN: u32 = 328; // slot(8) + output_commitments(256) + ciphertext_hash(32) + nullifier(32)
global LEAF_WINDOWS: u32 = 297;  // LEAF_BUF_LEN - 32 + 1
global STATE_BUF_LEN: u32 = 147;

fn compute_root(leaf: [u8; 32], path: [[u8; 32]; 32]) -> [u8; 32] {
    let mut current = leaf;
    let mut idx: u64 = 0; // slot 0
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

fn compute_leaf_buf(
    output_commitments: [[u8; 32]; MAX_OUTPUT_COMMITMENTS],
    ciphertext_hash: [u8; 32],
    nullifier: [u8; 32],
) -> [u8; LEAF_BUF_LEN] {
    let mut buf = [0 as u8; LEAF_BUF_LEN];
    // slot = 0, so slot_le8 = [0; 8], already zeroed in the buffer
    for i in 0..MAX_OUTPUT_COMMITMENTS {
        let off = 8 + i * 32;
        for j in 0..32 { buf[off + j] = output_commitments[i][j]; }
    }
    for j in 0..32 { buf[264 + j] = ciphertext_hash[j]; }
    for j in 0..32 { buf[296 + j] = nullifier[j]; }
    buf
}

fn compute_leaf(
    output_commitments: [[u8; 32]; MAX_OUTPUT_COMMITMENTS],
    ciphertext_hash: [u8; 32],
    nullifier: [u8; 32],
) -> [u8; 32] {
    std::hash::blake2s(compute_leaf_buf(output_commitments, ciphertext_hash, nullifier))
}

// Sliding-window search: does `needle` appear as any 32-byte substring of `buf`?
// Matches SP1's bincode::serialize(&entry).windows(32).any(|w| w == needle).
fn buf_contains(buf: [u8; LEAF_BUF_LEN], needle: [u8; 32]) -> bool {
    let mut found = false;
    for i in 0..LEAF_WINDOWS {
        let mut window = [0 as u8; 32];
        for j in 0..32 { window[j] = buf[i + j]; }
        if window == needle { found = true; }
    }
    found
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
    owner_pk: pub [u8; 32],
    coin_commitment: pub [u8; 32],
    slot: pub u64,         // must be 0 for the base case
    parent_nullifier: pub [u8; 32],

    entry_output_commitments: [[u8; 32]; MAX_OUTPUT_COMMITMENTS],
    entry_num_outputs: u64,
    entry_nullifier: [u8; 32],
    entry_ciphertext_hash: [u8; 32],
    own_nullifier: [u8; 32],
    append_path: [[u8; 32]; 32],
    is_receipt_hint: bool,
) -> pub [u8; 32] {
    assert(slot == 0, "slot must be 0 for the base case");

    let leaf_0 = compute_leaf(entry_output_commitments, entry_ciphertext_hash, entry_nullifier);
    let new_root = compute_root(leaf_0, append_path);

    // Receipt: coin appears in entry 0 (no parent_nullifier seen yet).
    let mut coin_in_entry = false;
    for i in 0..MAX_OUTPUT_COMMITMENTS {
        if (i as u64) < entry_num_outputs {
            if entry_output_commitments[i] == coin_commitment {
                coin_in_entry = true;
            }
        }
    }
    let is_receipt = coin_in_entry;
    assert(is_receipt == is_receipt_hint, "receipt hint disagrees with in-circuit detection");

    // Sliding-window search over the raw 328-byte leaf buffer.
    // Matches SP1's bincode::serialize(&entry).windows(32).any(|w| w == nullifier).
    let leaf_buf = compute_leaf_buf(entry_output_commitments, entry_ciphertext_hash, entry_nullifier);
    let parent_nullifier_seen = buf_contains(leaf_buf, parent_nullifier);
    let spent                 = buf_contains(leaf_buf, own_nullifier);

    let received_at_valid = is_receipt;
    let received_at: u64 = if is_receipt { 0 } else { 0 };

    // board_size after slot 0 = 1
    state_hash(
        owner_pk, coin_commitment, new_root,
        1, received_at_valid, received_at,
        spent, parent_nullifier, parent_nullifier_seen,
    )
}
