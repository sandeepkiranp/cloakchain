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
// All hashes use Blake2s-256 (fixed-size arrays; matches Rust blake2 crate).
// The previous step is verified recursively via Noir UltraHonk.
// At the receipt slot the parent spend proof is also verified recursively.
//
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

// Blake2s of two concatenated 32-byte values.
// Matches blake2s_pair() in lib/src/lib.rs.
fn blake2s_pair(a: [u8; 32], b: [u8; 32]) -> [u8; 32] {
    let mut buf = [0 as u8; 64];
    for i in 0..32 { buf[i] = a[i]; }
    for i in 0..32 { buf[32 + i] = b[i]; }
    std::hash::blake2s(buf)
}

// Convert a [u8; 32] to [Field; 32] for passing as public_inputs.
fn bytes32_to_fields(b: [u8; 32]) -> [Field; 32] {
    let mut out = [0 as Field; 32];
    for i in 0..32 { out[i] = b[i] as Field; }
    out
}

// ---- Merkle helpers --------------------------------------------------------

global TREE_DEPTH: u32 = 32;

// Recompute the Merkle root from a leaf and its sibling path.
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
// Unused commitment slots are zero-padded.
// Matches merkle_leaf() in lib/src/lib.rs.
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

// ---- Spend state hash (mirrors circuits/spend/src/main.nr) -----------------

// Layout: board_root(32) + num_outputs_le8(8) + 8 commitment slots(256) = 296 bytes.
global SPEND_STATE_BUF_LEN: u32 = 296;

fn spend_state_hash(
    board_root: [u8; 32],
    output_commitments: [[u8; 32]; MAX_OUTPUT_COMMITMENTS],
    num_outputs: u64,
) -> [u8; 32] {
    let mut buf = [0 as u8; SPEND_STATE_BUF_LEN];
    for i in 0..32 { buf[i] = board_root[i]; }
    let nb = u64_to_le_bytes(num_outputs);
    for i in 0..8 { buf[32 + i] = nb[i]; }
    for i in 0..MAX_OUTPUT_COMMITMENTS {
        let off = 40 + i * 32;
        for j in 0..32 { buf[off + j] = output_commitments[i][j]; }
    }
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

    // --- recursive spend proof (at receipt slot only) ---
    has_spend_proof: bool,
    spend_vk: UltraHonkVerificationKey,
    spend_proof: UltraHonkProof,
    spend_vk_hash: Field,
    spend_proof_state_hash: [u8; 32],
    spend_board_root: [u8; 32],
    spend_output_commitments: [[u8; 32]; MAX_OUTPUT_COMMITMENTS],
    spend_num_outputs: u64,
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

            assert(inner_owner_pk == owner_pk,               "inner proof: wrong owner");
            assert(inner_coin_commitment == coin_commitment,  "inner proof: wrong coin");
            assert(inner_parent_nullifier == parent_nullifier,"inner proof: wrong parent nullifier");
            assert(inner_board_size == slot,                  "inner proof: wrong board size");
            assert(inner_board_root == old_root,              "inner proof: wrong board root");

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

    let is_receipt = coin_in_this_entry & !prev_received_at_valid & !prev_parent_nullifier_seen;

    // ---- 4. Spend proof at receipt slot ------------------------------------

    if is_receipt & has_spend_proof {
        let recomputed_spend = spend_state_hash(
            spend_board_root, spend_output_commitments, spend_num_outputs,
        );
        assert(recomputed_spend == spend_proof_state_hash, "spend proof witnesses mismatch");

        let spend_pub_fields = bytes32_to_fields(spend_proof_state_hash);
        verify_honk_proof_non_zk(spend_vk, spend_proof, spend_pub_fields, spend_vk_hash);

        let mut found = false;
        for i in 0..MAX_OUTPUT_COMMITMENTS {
            if (i as u64) < spend_num_outputs {
                if spend_output_commitments[i] == coin_commitment {
                    found = true;
                }
            }
        }
        assert(found, "spend proof does not commit to this coin commitment");
    }

    // ---- 5. Nullifier tracking --------------------------------------------

    let parent_nullifier_seen = prev_parent_nullifier_seen
        | (!prev_received_at_valid & (entry_nullifier == parent_nullifier));

    let spent = prev_spent | (entry_nullifier == own_nullifier);

    // ---- 6. State update --------------------------------------------------

    let received_at_valid = prev_received_at_valid | is_receipt;
    let received_at = if is_receipt & !prev_received_at_valid { slot } else { prev_received_at };

    state_hash(
        owner_pk, coin_commitment, new_root,
        slot + 1, received_at_valid, received_at,
        spent, parent_nullifier, parent_nullifier_seen,
    )
}
