// CloakChain IVC coin-proof circuit -- one step of the coin-proof relation.
//
// Each step covers one board slot k and asserts:
//   - The Merkle root is updated correctly from slot k-1 to slot k.
//   - If coin_commitment appears in entry_k.output_commitments, this is the
//     receipt slot (received_at = k), provided parent_nullifier was not seen.
//   - If entry_k.nullifier == own_nullifier, the coin was already spent.
//   - If entry_k.nullifier == parent_nullifier (before receipt), the creating
//     transaction was double-spent.
//
// ONE recursive verifier: the previous step's coinproof.
// The creating spend proof is verified in the spend circuit (not here),
// keeping this circuit to a single recursive call so it remains provable.
//
// All hashes use Blake2s-256 (matches Rust blake2 crate).
// Public output: Blake2s(state_bytes) as [u8; 32].

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

// ---- Merkle helpers --------------------------------------------------------

global TREE_DEPTH: u32 = 32;

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

// ---- Leaf hash -------------------------------------------------------------

global MAX_OUTPUT_COMMITMENTS: u32 = 8;

// Buffer: slot_le8(8) + 8 commitment slots(256) + ciphertext_hash(32) = 296 bytes.
global LEAF_BUF_LEN: u32 = 296;

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

// ---- State hash ------------------------------------------------------------

// Layout (147 bytes):
//   owner_pk(32) | coin_commitment(32) | board_root(32) |
//   board_size_le8(8) | received_at_valid(1) | received_at_le8(8) |
//   spent(1) | parent_nullifier(32) | parent_nullifier_seen(1)
global STATE_BUF_LEN: u32 = 147;

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

// ---- Main ------------------------------------------------------------------

fn main(
    // --- coin being tracked ---
    owner_pk: pub [u8; 32],
    coin_commitment: pub [u8; 32],

    // --- current board slot ---
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

    // --- recursive inner coin-proof (previous step) ---
    has_inner: bool,
    inner_vk: UltraHonkVerificationKey,
    inner_proof: UltraHonkProof,
    inner_vk_hash: Field,
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

    // --- receipt flag (no spend proof in circuit; provenance checked in spend circuit) ---
    // The host asserts coin_commitment appears in entry_output_commitments at this slot
    // and the parent spend proof's output_commitments include coin_commitment.
    // This is enforced by the spend circuit when the coin holder eventually spends.
    is_receipt_hint: bool,
) -> pub [u8; 32] {

    // ---- 1. Merkle roots --------------------------------------------------

    let zero_leaf = [0 as u8; 32];
    let old_root = compute_root(zero_leaf, slot, append_path);
    let leaf_k = compute_leaf(slot, entry_output_commitments, entry_ciphertext_hash);
    let new_root = compute_root(leaf_k, slot, append_path);

    // ---- 2. Inner proof verification and state loading --------------------

    let (prev_received_at_valid, prev_received_at, prev_spent, prev_parent_nullifier_seen) =
        if has_inner {
            let inner_pub_fields = bytes32_to_fields(inner_state_hash);
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

            (inner_received_at_valid, inner_received_at, inner_spent, inner_parent_nullifier_seen)
        } else {
            assert(slot == 0, "base case must be slot 0");
            (false, 0, false, false)
        };

    // ---- 3. Receipt detection ---------------------------------------------

    let mut coin_in_this_entry = false;
    for i in 0..MAX_OUTPUT_COMMITMENTS {
        if (i as u64) < entry_num_outputs {
            if entry_output_commitments[i] == coin_commitment {
                coin_in_this_entry = true;
            }
        }
    }

    // Receipt: coin appears in this entry AND not already received AND
    // parent nullifier not seen (creating tx was not a double-spend).
    // The is_receipt_hint from the host must agree with the in-circuit detection.
    let is_receipt = coin_in_this_entry & !prev_received_at_valid & !prev_parent_nullifier_seen;
    assert(is_receipt == is_receipt_hint, "receipt hint disagrees with in-circuit detection");

    // ---- 4. Nullifier tracking --------------------------------------------

    let parent_nullifier_seen = prev_parent_nullifier_seen
        | (!prev_received_at_valid & (entry_nullifier == parent_nullifier));

    let spent = prev_spent | (entry_nullifier == own_nullifier);

    // ---- 5. State update --------------------------------------------------

    let received_at_valid = prev_received_at_valid | is_receipt;
    let received_at = if is_receipt & !prev_received_at_valid { slot } else { prev_received_at };

    state_hash(
        owner_pk, coin_commitment, new_root,
        slot + 1, received_at_valid, received_at,
        spent, parent_nullifier, parent_nullifier_seen,
    )
}
