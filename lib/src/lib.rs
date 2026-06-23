use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

pub const GENESIS_SK: [u8; 32] = [0u8; 32];

pub fn genesis_pk() -> [u8; 32] {
    derive_pk(&GENESIS_SK)
}

/// Toy key derivation: pk = H(sk).
pub fn derive_pk(sk: &[u8; 32]) -> [u8; 32] {
    let d = Sha256::digest(sk);
    let mut out = [0u8; 32];
    out.copy_from_slice(&d);
    out
}

/// A coin: tag `t`, value `v`, owner public key `pk`, plus masking randomness `r`.
/// Commitment cn = H(t || v || r || pk) — binds the coin to its intended owner,
/// so a coin created for Alice cannot be claimed by Bob even if he knows the
/// tag/value/rand (analogous to how Zcash embeds the recipient address in cm).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Coin {
    pub tag: [u8; 32],
    pub value: u64,
    pub rand: [u8; 32],
    pub owner_pk: [u8; 32],
}

impl Coin {
    pub fn commitment(&self) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(self.tag);
        h.update(self.value.to_le_bytes());
        h.update(self.rand);
        h.update(self.owner_pk);
        let mut out = [0u8; 32];
        out.copy_from_slice(&h.finalize());
        out
    }
}

/// A generalised transaction: `S` spends one or more input coins and creates
/// one or more output coins for (potentially different) recipients.
///
/// Only **commitments** appear in the transaction body — the actual coin data
/// (`tag`, `value`, `rand`) for each output is encrypted separately in
/// `note_encs[i]` using `pair_key(sender_pk, recipient_pks[i])`, so that each
/// recipient can only read their own coin's value and not the others'.
///
/// `spend_proof` is attached after proving and the whole struct re-encrypted.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Transaction {
    pub id: u64,
    pub sender_pk: [u8; 32],
    /// One entry per output coin; sender appears here for change outputs.
    pub recipient_pks: Vec<[u8; 32]>,
    /// Commitments to the coins being spent (`input_coins[i].commitment()`).
    pub input_commitments: Vec<[u8; 32]>,
    /// Commitments to the new coins (`output_coins[i].commitment()`),
    /// matching `recipient_pks` index-for-index.
    pub output_commitments: Vec<[u8; 32]>,
    /// `note_encs[i]` = `encrypt(output_coin_i, pair_key(sender, recipient_pks[i]))`.
    /// Only `recipient_pks[i]` (or the sender, who knows all keys) can decrypt.
    pub note_encs: Vec<Vec<u8>>,
    pub spend_proof: Vec<u8>,
}

impl Transaction {
    pub fn sent_by(&self, pk: &[u8; 32]) -> bool {
        &self.sender_pk == pk
    }
    pub fn received_by(&self, pk: &[u8; 32]) -> bool {
        self.recipient_pks.contains(pk)
    }

    /// `pk` receives the coin with commitment `cn` in this tx if any
    /// `(recipient_pks[i], output_commitments[i])` pair matches `(pk, cn)`.
    pub fn receives_coin(&self, pk: &[u8; 32], cn: &[u8; 32]) -> bool {
        self.recipient_pks.iter().zip(self.output_commitments.iter())
            .any(|(rpk, ocn)| rpk == pk && ocn == cn)
    }

    /// `pk` spends coin `cn` in this tx if `sender_pk == pk` and `cn` is
    /// one of the input commitments.
    pub fn spends_coin(&self, pk: &[u8; 32], cn: &[u8; 32]) -> bool {
        self.sender_pk == *pk && self.input_commitments.contains(cn)
    }
}

// ---- Session-key encryption with per-recipient note privacy ---------------
//
// A single `session_key` encrypts the full `Transaction` (which contains only
// commitments, not raw coin values). The session key is then wrapped once per
// authorised participant (sender + every recipient) using their pairwise key,
// producing a small `key_enc` per participant. Any authorised party can recover
// the session key from their own `key_enc` and decrypt the transaction.
//
// Each output coin's actual data (`tag`, `value`, `rand`) is encrypted
// separately as a "note" using `pair_key(sender, recipient_i)`. Only that
// specific recipient (or the sender, who knows all pair keys) can decrypt the
// note — other recipients cannot see each other's coin values.

/// Domain-separation salt for pairwise key derivation.
pub const PAIR_SALT: [u8; 32] = *b"CLOAKCHAIN-PAIRWISE-KEY-SALT!!!!";

/// Magic tag embedded in each `key_enc` so successful decryption is detectable.
const SESSION_MAGIC: [u8; 8] = *b"CLOAKKY1";

/// Magic tag embedded in the transaction ciphertext.
const MAGIC_TAG: [u8; 8] = *b"CLOAKTX1";

/// Magic tag embedded in each note encryption.
const NOTE_MAGIC: [u8; 8] = *b"CLOAKNT1";

/// The hard-coded long-term key shared by `pk_a` and `pk_b`. Symmetric in its
/// arguments: `pair_key(a, b) == pair_key(b, a)`.
pub fn pair_key(pk_a: &[u8; 32], pk_b: &[u8; 32]) -> [u8; 32] {
    let (lo, hi) = if pk_a <= pk_b { (pk_a, pk_b) } else { (pk_b, pk_a) };
    let mut h = Sha256::new();
    h.update(lo);
    h.update(hi);
    h.update(PAIR_SALT);
    let mut out = [0u8; 32];
    out.copy_from_slice(&h.finalize());
    out
}

/// XOR-with-hash-keystream. Encryption and decryption are the same operation.
fn xor_with_keystream(key: &[u8; 32], data: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(data.len());
    let mut counter: u64 = 0;
    while out.len() < data.len() {
        let mut h = Sha256::new();
        h.update(key);
        h.update(counter.to_le_bytes());
        out.extend_from_slice(&h.finalize());
        counter += 1;
    }
    out.truncate(data.len());
    for (o, d) in out.iter_mut().zip(data.iter()) {
        *o ^= d;
    }
    out
}

/// A board entry: the transaction encrypted with a session key (visible to all
/// authorised parties) plus one `key_enc` per participant for session-key recovery.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BoardEntry {
    /// `xor_with_keystream(session_key, MAGIC_TAG || bincode(tx))`.
    pub ciphertext: Vec<u8>,
    /// `key_encs[i] = xor_with_keystream(pair_key(sender, participant_i), SESSION_MAGIC || session_key)`.
    /// Participants = [sender, recipient_pks[0], recipient_pks[1], …].
    pub key_encs: Vec<Vec<u8>>,
}

/// Derive a deterministic session key from the transaction (reproducible across
/// re-encryptions of the same logical transaction).
fn session_key_for(tx: &Transaction) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(tx.sender_pk);
    h.update(tx.id.to_le_bytes());
    h.update(PAIR_SALT);
    let mut out = [0u8; 32];
    out.copy_from_slice(&h.finalize());
    out
}

/// Encrypt `tx` using a session key. All authorised parties (sender + all
/// recipients) receive a wrapped copy of the session key in `key_encs`.
/// Call again after updating `tx.spend_proof` to re-encrypt with the proof.
pub fn encrypt_tx(tx: &Transaction) -> BoardEntry {
    let session_key = session_key_for(tx);

    // Encrypt the transaction body.
    let tx_bytes = bincode::serialize(tx).expect("Transaction is always serializable");
    let mut plaintext = MAGIC_TAG.to_vec();
    plaintext.extend_from_slice(&tx_bytes);
    let ciphertext = xor_with_keystream(&session_key, &plaintext);

    // Wrap the session key for each participant: sender first, then recipients.
    let mut participants = vec![tx.sender_pk];
    participants.extend_from_slice(&tx.recipient_pks);
    let key_encs = participants.iter().map(|p| {
        let k = pair_key(&tx.sender_pk, p);
        let mut payload = SESSION_MAGIC.to_vec();
        payload.extend_from_slice(&session_key);
        xor_with_keystream(&k, &payload)
    }).collect();

    BoardEntry { ciphertext, key_encs }
}

/// Try every registry member as a potential sender/co-participant to recover
/// the session key, then decrypt the transaction. Returns `Some(tx)` only if
/// `owner_pk` is genuinely the sender or one of the recipients.
pub fn scan_entry(
    owner_pk: &[u8; 32],
    registry: &[[u8; 32]],
    entry: &BoardEntry,
) -> Option<Transaction> {
    const KEY_ENC_LEN: usize = 8 + 32; // SESSION_MAGIC + session_key
    for candidate in registry {
        let k = pair_key(owner_pk, candidate);
        for key_enc in &entry.key_encs {
            if key_enc.len() != KEY_ENC_LEN { continue; }
            let dec = xor_with_keystream(&k, key_enc);
            if dec[..8] != SESSION_MAGIC { continue; }
            let mut session_key = [0u8; 32];
            session_key.copy_from_slice(&dec[8..]);
            // Decrypt the transaction ciphertext.
            if entry.ciphertext.len() <= 8 { continue; }
            let tx_bytes = xor_with_keystream(&session_key, &entry.ciphertext);
            if tx_bytes[..8] != MAGIC_TAG { continue; }
            let tx: Transaction = bincode::deserialize(&tx_bytes[8..]).ok()?;
            if tx.sent_by(owner_pk) || tx.received_by(owner_pk) {
                return Some(tx);
            }
        }
    }
    None
}

/// Encrypt a coin as a note for a specific recipient.
/// `note_encs[i] = build_note_enc(sender_pk, recipient_pks[i], &output_coins[i])`.
pub fn build_note_enc(sender_pk: &[u8; 32], recipient_pk: &[u8; 32], coin: &Coin) -> Vec<u8> {
    let key = pair_key(sender_pk, recipient_pk);
    let coin_bytes = bincode::serialize(coin).expect("Coin is always serializable");
    let mut payload = NOTE_MAGIC.to_vec();
    payload.extend_from_slice(&coin_bytes);
    xor_with_keystream(&key, &payload)
}

/// Decrypt a note — returns the `Coin` if `pair_key(sender, recipient)` is correct.
pub fn decrypt_note(sender_pk: &[u8; 32], recipient_pk: &[u8; 32], note_enc: &[u8]) -> Option<Coin> {
    let key = pair_key(sender_pk, recipient_pk);
    let dec = xor_with_keystream(&key, note_enc);
    if dec.len() <= 8 || dec[..8] != NOTE_MAGIC { return None; }
    bincode::deserialize(&dec[8..]).ok()
}

// ---- Fixed-depth Merkle tree over board entries ------------------------
//
// The tree has a fixed depth of TREE_DEPTH (supporting up to 2^TREE_DEPTH
// entries). Unfilled leaf positions are treated as the zero byte array [0u8;32].
// This lets each IVC coin-proof step update the root in O(TREE_DEPTH) = O(1)
// time using a single Merkle inclusion (append) proof, rather than O(n) by
// recomputing the root from all prior entries.
//
// Key property: if `append_path` is the inclusion proof for slot k in the
// fixed-depth tree containing entries[0..=k], then:
//
//   compute_root_from_path([0u8;32], k, &append_path)  == root_{k-1}  (old root)
//   compute_root_from_path(merkle_leaf(k, e_k), k, &append_path) == root_k (new root)
//
// Only the leaf value changes between the two computations; the path is the
// same. This lets the IVC step verify consistency with the prior root AND
// compute the new root in a single O(TREE_DEPTH) pass.

/// Maximum tree depth. Supports up to 2^32 ≈ 4 billion board entries.
pub const TREE_DEPTH: usize = 32;

/// Leaf hash = SHA256(slot_as_u64_le || ciphertext). Including the slot index
/// prevents permuting entries while keeping a valid root.
pub fn merkle_leaf(slot: usize, entry: &BoardEntry) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update((slot as u64).to_le_bytes());
    h.update(&entry.ciphertext);
    let mut out = [0u8; 32];
    out.copy_from_slice(&h.finalize());
    out
}

fn merkle_combine(l: &[u8; 32], r: &[u8; 32]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(l);
    h.update(r);
    let mut out = [0u8; 32];
    out.copy_from_slice(&h.finalize());
    out
}

/// Precomputed hashes of empty subtrees at each depth.
/// `zero_hashes()[d]` = root of a complete subtree of depth `d` with all
/// leaves equal to [0u8;32].
fn zero_hashes() -> Vec<[u8; 32]> {
    let mut out = vec![[0u8; 32]]; // depth 0: the zero leaf itself
    for _ in 0..TREE_DEPTH {
        let prev = *out.last().unwrap();
        out.push(merkle_combine(&prev, &prev));
    }
    out
}

/// Root of the empty fixed-depth tree (all leaves = [0u8;32]).
pub fn empty_root() -> [u8; 32] {
    zero_hashes()[TREE_DEPTH]
}

/// Walk the path from `leaf` at `slot` to the root. Used by both
/// `merkle_root_of` and `check_coin_proof_step`.
pub fn compute_root_from_path(leaf: [u8; 32], slot: usize, path: &[[u8; 32]]) -> [u8; 32] {
    let mut current = leaf;
    let mut idx = slot;
    for sibling in path {
        current = if idx % 2 == 0 {
            merkle_combine(&current, sibling)
        } else {
            merkle_combine(sibling, &current)
        };
        idx >>= 1;
    }
    current
}

/// Compute the Merkle root of a fixed-depth tree containing `entries` at
/// slots 0..T and [0u8;32] at all other leaf positions.
pub fn merkle_root_of(entries: &[BoardEntry]) -> [u8; 32] {
    if entries.is_empty() {
        return empty_root();
    }
    let last = entries.len() - 1;
    let path = append_proof_for(entries);
    compute_root_from_path(merkle_leaf(last, &entries[last]), last, &path)
}

/// Inclusion proof for `slot` in the fixed-depth tree over `entries`.
/// At each level the sibling is either the real hash of the adjacent subtree
/// (if it was already filled by prior entries) or the zero-subtree hash.
pub fn append_proof_for(entries: &[BoardEntry]) -> Vec<[u8; 32]> {
    let slot = entries.len() - 1;
    let zeros = zero_hashes();
    let mut path = Vec::with_capacity(TREE_DEPTH);

    // Build the filled portion of the current level from real entries.
    let mut level: Vec<[u8; 32]> = entries.iter().enumerate()
        .map(|(i, e)| merkle_leaf(i, e))
        .collect();

    let mut idx = slot;
    for d in 0..TREE_DEPTH {
        let sibling_idx = idx ^ 1;
        let sibling = if sibling_idx < level.len() {
            level[sibling_idx]
        } else {
            zeros[d] // unfilled subtree — use the zero hash for this depth
        };
        path.push(sibling);

        // Collapse current level to the next level up.
        let mut next = Vec::with_capacity((level.len() + 1) / 2);
        let mut i = 0;
        while i < level.len() {
            let left = level[i];
            let right = if i + 1 < level.len() { level[i + 1] } else { zeros[d] };
            next.push(merkle_combine(&left, &right));
            i += 2;
        }
        level = next;
        idx >>= 1;
    }
    path
}

/// Verify that `entry` is the genuine content of `slot` in a fixed-depth tree
/// with the given `root`.
pub fn merkle_verify(root: [u8; 32], slot: usize, entry: &BoardEntry, proof: &[[u8; 32]]) -> bool {
    compute_root_from_path(merkle_leaf(slot, entry), slot, proof) == root
}

// ---- Public values -------------------------------------------------------

/// The public values committed by the spend (`Valid`) relation.
///
/// `board_root` is the Merkle root of `entries[0..last]` — the board state
/// *before* tx* was posted (the Zcash-style "anchor"). This breaks the
/// circular dependency: the proof commits to a root that does not include itself,
/// so the proof can be embedded inside tx* and re-encrypted without any
/// self-reference.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ValidPublicValues {
    pub vkey: [u32; 8],
    pub pk_p: [u8; 32],
    pub board_root: [u8; 32],
    pub board_size: usize,
}

impl ValidPublicValues {
    pub fn encode(&self) -> Vec<u8> {
        bincode::serialize(self).expect("ValidPublicValues is always serializable")
    }
}

// ---- IVC coin-proof -------------------------------------------------------
//
// Instead of a single batch proof at spend time that scans the whole board,
// every coin owner maintains a "coin-proof": a recursive proof updated by one
// step per new board slot. Each step asserts:
//
//   - `received_at`: the slot (if any) where the owner received this coin.
//   - `spent`: whether the owner has already sent this coin in any slot seen
//     so far.
//
// The final spend proof just checks the latest coin-proof's `received_at` is
// `Some` and `spent` is `false` — O(1) instead of an O(T) scan.

/// The public values committed by every step of the coin-proof relation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoinProofPublicValues {
    pub vkey: [u32; 8],
    pub owner_pk: [u8; 32],
    pub coin_commitment: [u8; 32],
    pub board_root: [u8; 32],
    pub board_size: usize,
    pub received_at: Option<u64>,
    pub spent: bool,
}

impl CoinProofPublicValues {
    pub fn encode(&self) -> Vec<u8> {
        bincode::serialize(self).expect("CoinProofPublicValues is always serializable")
    }
}

/// What justifies a coin-proof step.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoinProofJustification {
    /// `entries.len() == 1`: nothing to verify recursively yet.
    Base,
    /// `entries.len() > 1`: this step extends `inner_public_values`.
    Step { inner_public_values: CoinProofPublicValues },
}

/// One step of the coin-proof IVC, extended for slot `slot` (= k).
///
/// Instead of receiving all prior entries and recomputing the root in O(n),
/// this step receives only:
///   - `entry_k`: the single new board entry at position `slot`
///   - `append_path`: its Merkle inclusion proof in the fixed-depth tree
///     (TREE_DEPTH sibling hashes, leaf → root)
///
/// The root is updated in O(TREE_DEPTH) = O(1):
///   old root = compute_root_from_path([0u8;32],    slot, &append_path)
///   new root = compute_root_from_path(leaf_k,      slot, &append_path)
///
/// The inner proof's `board_root` is verified against the old root, binding
/// the chain to a genuine board history without passing all prior entries.
pub fn check_coin_proof_step(
    vkey: [u32; 8],
    owner_pk: [u8; 32],
    coin_commitment: [u8; 32],
    entry_k: BoardEntry,
    slot: usize,
    append_path: Vec<[u8; 32]>,
    registry: Vec<[u8; 32]>,
    inner: Option<CoinProofPublicValues>,
) -> Result<(CoinProofPublicValues, CoinProofJustification), &'static str> {
    let leaf_k = merkle_leaf(slot, &entry_k);
    let board_root = compute_root_from_path(leaf_k, slot, &append_path);

    let (prev_received_at, prev_spent, justification) = if slot == 0 {
        (None, false, CoinProofJustification::Base)
    } else {
        let inner = inner.ok_or("steps after the base case require an inner coin-proof")?;
        if inner.vkey != vkey {
            return Err("inner coin-proof was produced under a different vkey");
        }
        if inner.owner_pk != owner_pk {
            return Err("inner coin-proof has a different owner");
        }
        if inner.coin_commitment != coin_commitment {
            return Err("inner coin-proof tracks a different coin");
        }
        if inner.board_size != slot {
            return Err("inner coin-proof must cover exactly the prefix before this slot");
        }
        // Verify the append_path is consistent with the inner proof's root:
        // the old root is what you get from the same path with a zero leaf at slot.
        let old_root = compute_root_from_path([0u8; 32], slot, &append_path);
        if inner.board_root != old_root {
            return Err("inner coin-proof's board root does not match this prefix");
        }
        let prev_received_at = inner.received_at;
        let prev_spent = inner.spent;
        (prev_received_at, prev_spent, CoinProofJustification::Step { inner_public_values: inner })
    };

    let mut received_at = prev_received_at;
    let mut spent = prev_spent;
    if let Some(tx) = scan_entry(&owner_pk, &registry, &entry_k) {
        if tx.receives_coin(&owner_pk, &coin_commitment) && received_at.is_none() {
            received_at = Some(slot as u64);
        }
        if tx.spends_coin(&owner_pk, &coin_commitment) {
            spent = true;
        }
    }

    Ok((
        CoinProofPublicValues {
            vkey,
            owner_pk,
            coin_commitment,
            board_root,
            board_size: slot + 1,
            received_at,
            spent,
        },
        justification,
    ))
}

// ---- Spend relation --------------------------------------------------------

/// Checks every condition of the `Valid` (spend) relation except actually
/// verifying the recursive coin-proof's ZK proof.
///
/// `prior_entries` is the board history *before* tx* (`entries[0..last]`);
/// `tx_star` is the spending transaction (commitments only — no raw values).
/// `input_coins` and `output_coins` are the private witnesses: the actual coin
/// data whose commitments are asserted to match `tx_star`'s commitment lists.
/// This lets the circuit verify conservation (`Σ input values == Σ output values`)
/// without revealing any values to parties outside the zkVM.
pub fn check_spend(
    vkey: [u32; 8],
    coin_proof_vkey: [u32; 8],
    sk_p: [u8; 32],
    pk_p: [u8; 32],
    coin_commitment: [u8; 32],
    prior_entries: Vec<BoardEntry>,
    tx_star: Transaction,
    input_coins: Vec<Coin>,
    output_coins: Vec<Coin>,
    is_genesis: bool,
    coin_proof: Option<CoinProofPublicValues>,
) -> Result<ValidPublicValues, &'static str> {
    if derive_pk(&sk_p) != pk_p {
        return Err("pk_P must be the public key for sk_P");
    }

    let anchor = merkle_root_of(&prior_entries);

    if tx_star.sender_pk != pk_p {
        return Err("tx* must be sent by P");
    }

    // Verify input coin preimages match the transaction's committed commitments.
    if input_coins.len() != tx_star.input_commitments.len() {
        return Err("input_coins length does not match tx* input_commitments");
    }
    for (coin, cn) in input_coins.iter().zip(tx_star.input_commitments.iter()) {
        if &coin.commitment() != cn {
            return Err("input coin commitment does not match tx*");
        }
        if coin.owner_pk != pk_p {
            return Err("input coin's owner does not match the spender");
        }
    }

    // The specific coin being spent must be in the input list.
    if !tx_star.input_commitments.contains(&coin_commitment) {
        return Err("tx* does not spend the claimed coin");
    }

    // Verify output coin preimages match the transaction's committed commitments.
    if output_coins.len() != tx_star.output_commitments.len() {
        return Err("output_coins length does not match tx* output_commitments");
    }
    for (coin, cn) in output_coins.iter().zip(tx_star.output_commitments.iter()) {
        if &coin.commitment() != cn {
            return Err("output coin commitment does not match tx*");
        }
    }

    // Value conservation: Σ inputs == Σ outputs (no minting, no burning).
    let total_in: u64 = input_coins.iter().map(|c| c.value).sum();
    let total_out: u64 = output_coins.iter().map(|c| c.value).sum();
    if total_in != total_out {
        return Err("transaction violates value conservation: sum(inputs) must equal sum(outputs)");
    }

    if is_genesis {
        if pk_p != genesis_pk() {
            return Err("only the genesis key may mint without provenance");
        }
        if !prior_entries.is_empty() {
            return Err("a genesis mint has no prior history");
        }
    } else {
        let cp = coin_proof.ok_or("non-genesis spends require a coin-proof")?;
        if cp.vkey != coin_proof_vkey {
            return Err("coin-proof was produced under an unexpected vkey");
        }
        if cp.owner_pk != pk_p {
            return Err("coin-proof owner must be P");
        }
        if cp.coin_commitment != coin_commitment {
            return Err("coin-proof tracks a different coin");
        }
        if cp.board_size != prior_entries.len() {
            return Err("coin-proof must cover exactly the board prefix before tx*");
        }
        if cp.board_root != anchor {
            return Err("coin-proof's board root does not match the board prefix");
        }
        if cp.received_at.is_none() {
            return Err("P must have received this coin at some prior slot");
        }
        if cp.spent {
            return Err("P must not have spent this coin before (double spend)");
        }
    }

    Ok(ValidPublicValues { vkey, pk_p, board_root: anchor, board_size: prior_entries.len() + 1 })
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEST_VKEY: [u32; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    const TEST_COIN_PROOF_VKEY: [u32; 8] = [9, 9, 9, 9, 9, 9, 9, 9];

    fn party(seed: u8) -> ([u8; 32], [u8; 32]) {
        let mut sk = [0u8; 32];
        sk[0] = seed;
        (sk, derive_pk(&sk))
    }

    fn coin(seed: u8, value: u64, owner_pk: [u8; 32]) -> Coin {
        let mut tag = [0u8; 32];
        tag[0] = seed;
        let mut rand = [0u8; 32];
        rand[1] = seed;
        Coin { tag, value, rand, owner_pk }
    }

    /// Build a Transaction from explicit input coins and (coin, recipient_pk) output pairs.
    fn make_tx(
        id: u64,
        sender_pk: [u8; 32],
        input_coins: &[Coin],
        outputs: &[(Coin, [u8; 32])],
    ) -> Transaction {
        let input_commitments = input_coins.iter().map(|c| c.commitment()).collect();
        let recipient_pks: Vec<[u8; 32]> = outputs.iter().map(|(_, rpk)| *rpk).collect();
        let output_commitments: Vec<[u8; 32]> = outputs.iter().map(|(c, _)| c.commitment()).collect();
        let note_encs: Vec<Vec<u8>> = outputs.iter()
            .map(|(c, rpk)| build_note_enc(&sender_pk, rpk, c))
            .collect();
        Transaction { id, sender_pk, recipient_pks, input_commitments, output_commitments, note_encs, spend_proof: vec![] }
    }

    /// Run the coin-proof IVC chain for `owner_pk`/`coin_commitment` over `entries`.
    fn coin_proof_chain(
        owner_pk: [u8; 32],
        coin_commitment: [u8; 32],
        entries: &[BoardEntry],
        registry: &[[u8; 32]],
    ) -> Vec<CoinProofPublicValues> {
        let mut out = Vec::new();
        let mut inner = None;
        for k in 0..entries.len() {
            let ap = append_proof_for(&entries[..=k]);
            let (pv, _) = check_coin_proof_step(
                TEST_COIN_PROOF_VKEY, owner_pk, coin_commitment,
                entries[k].clone(), k, ap, registry.to_vec(), inner.clone(),
            ).unwrap();
            inner = Some(pv.clone());
            out.push(pv);
        }
        out
    }

    /// Convenience wrapper: call `check_spend` with explicit input/output coin witnesses.
    fn spend(
        sk: [u8; 32],
        pk: [u8; 32],
        coin_commitment: [u8; 32],
        prior_entries: &[BoardEntry],
        tx_star: &Transaction,
        input_coins: &[Coin],
        output_coins: &[Coin],
        is_genesis: bool,
        coin_proof: Option<CoinProofPublicValues>,
    ) -> Result<ValidPublicValues, &'static str> {
        check_spend(
            TEST_VKEY, TEST_COIN_PROOF_VKEY, sk, pk, coin_commitment,
            prior_entries.to_vec(), tx_star.clone(),
            input_coins.to_vec(), output_coins.to_vec(),
            is_genesis, coin_proof,
        )
    }

    #[test]
    fn encrypt_decrypt_round_trips_for_participants_and_rejects_outsiders() {
        let (_, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (_, alice_pk) = party(1);
        let (_, bob_pk) = party(2);
        let (_, carol_pk) = party(3);
        let registry = vec![genesis_pk, alice_pk, bob_pk, carol_pk];

        let alice_coin = coin(0xA2, 100, alice_pk);
        let tx0 = make_tx(0, genesis_pk,
            &[coin(0xA1, 100, genesis_pk)],
            &[(alice_coin.clone(), alice_pk)]);
        let entry = encrypt_tx(&tx0);

        // Both sender and recipient can decrypt.
        assert_eq!(scan_entry(&genesis_pk, &registry, &entry), Some(tx0.clone()));
        assert_eq!(scan_entry(&alice_pk, &registry, &entry), Some(tx0.clone()));

        // Outsiders cannot.
        assert_eq!(scan_entry(&bob_pk, &registry, &entry), None);
        assert_eq!(scan_entry(&carol_pk, &registry, &entry), None);

        // Recipient can decrypt their own note.
        assert_eq!(decrypt_note(&genesis_pk, &alice_pk, &tx0.note_encs[0]), Some(alice_coin));
        // Bob cannot decrypt Alice's note.
        assert_eq!(decrypt_note(&genesis_pk, &bob_pk, &tx0.note_encs[0]), None);
    }

    #[test]
    fn multi_output_tx_each_recipient_sees_only_own_note() {
        let (_, alice_pk) = party(1);
        let (_, bob_pk) = party(2);
        let (_, carol_pk) = party(3);

        let alice_coin = coin(0xA1, 100, alice_pk);
        let bob_coin = coin(0xB1, 40, bob_pk);
        let alice_change = coin(0xB2, 60, alice_pk);

        // Alice→Bob+change: two outputs.
        let tx1 = make_tx(1, alice_pk,
            &[alice_coin.clone()],
            &[(bob_coin.clone(), bob_pk), (alice_change.clone(), alice_pk)]);

        // Bob decrypts his note.
        assert_eq!(decrypt_note(&alice_pk, &bob_pk,   &tx1.note_encs[0]), Some(bob_coin));
        // Alice decrypts her change note.
        assert_eq!(decrypt_note(&alice_pk, &alice_pk, &tx1.note_encs[1]), Some(alice_change));
        // Carol cannot decrypt either note.
        assert_eq!(decrypt_note(&alice_pk, &carol_pk, &tx1.note_encs[0]), None);
        assert_eq!(decrypt_note(&alice_pk, &carol_pk, &tx1.note_encs[1]), None);
    }

    #[test]
    fn registry_scan_finds_the_right_counterparty() {
        let (_, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (_, alice_pk) = party(1);
        let (_, bob_pk) = party(2);
        let (_, carol_pk) = party(3);
        let registry = vec![genesis_pk, alice_pk, bob_pk, carol_pk];

        let tx0 = make_tx(0, genesis_pk,
            &[coin(0xA1, 100, genesis_pk)],
            &[(coin(0xA2, 100, alice_pk), alice_pk)]);
        let entry = encrypt_tx(&tx0);

        assert_eq!(scan_entry(&alice_pk,   &registry, &entry), Some(tx0.clone()));
        assert_eq!(scan_entry(&genesis_pk, &registry, &entry), Some(tx0));
        assert_eq!(scan_entry(&bob_pk,     &registry, &entry), None);
        assert_eq!(scan_entry(&carol_pk,   &registry, &entry), None);
    }

    #[test]
    fn coin_proof_tracks_receipt_and_spend_for_demo_chain() {
        let (genesis_sk, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (alice_sk, alice_pk) = party(1);
        let (bob_sk, bob_pk) = party(2);
        let (_carol_sk, carol_pk) = party(3);
        let registry = vec![genesis_pk, alice_pk, bob_pk, carol_pk];

        let alice_coin  = coin(0xA2, 100, alice_pk);
        let bob_coin    = coin(0xB1,  40, bob_pk);
        let alice_change = coin(0xB2, 60, alice_pk);
        let carol_coin  = coin(0xC1,  40, carol_pk);

        let tx0 = make_tx(0, genesis_pk, &[coin(0xA1, 100, genesis_pk)],
            &[(alice_coin.clone(), alice_pk)]);
        let tx1 = make_tx(1, alice_pk, &[alice_coin.clone()],
            &[(bob_coin.clone(), bob_pk), (alice_change, alice_pk)]);
        let tx2 = make_tx(2, bob_pk, &[bob_coin.clone()],
            &[(carol_coin, carol_pk)]);
        let entries = vec![encrypt_tx(&tx0), encrypt_tx(&tx1), encrypt_tx(&tx2)];

        let cn_alice = alice_coin.commitment();
        let cn_bob   = bob_coin.commitment();

        let alice_cp = coin_proof_chain(alice_pk, cn_alice, &entries[..1], &registry);
        assert_eq!(alice_cp[0].received_at, Some(0));
        assert_eq!(alice_cp[0].spent, false);

        let bob_cp = coin_proof_chain(bob_pk, cn_bob, &entries[..2], &registry);
        assert_eq!(bob_cp[0].received_at, None);
        assert_eq!(bob_cp[1].received_at, Some(1));
        assert_eq!(bob_cp[1].spent, false);

        let _ = (genesis_sk, alice_sk, bob_sk);
    }

    #[test]
    fn coin_proof_tracks_change_as_a_receipt() {
        let (genesis_sk, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (alice_sk, alice_pk) = party(1);
        let (bob_sk, bob_pk) = party(2);
        let (_, carol_pk) = party(3);
        let registry = vec![genesis_pk, alice_pk, bob_pk, carol_pk];

        let alice_coin   = coin(0xA2, 100, alice_pk);
        let bob_coin     = coin(0xB1,  40, bob_pk);
        let alice_change = coin(0xB2,  60, alice_pk);

        let tx0 = make_tx(0, genesis_pk, &[coin(0xA1, 100, genesis_pk)],
            &[(alice_coin.clone(), alice_pk)]);
        let tx1 = make_tx(1, alice_pk, &[alice_coin.clone()],
            &[(bob_coin, bob_pk), (alice_change.clone(), alice_pk)]);
        let entries = vec![encrypt_tx(&tx0), encrypt_tx(&tx1)];

        let cn_alice_change = alice_change.commitment();
        let cp = coin_proof_chain(alice_pk, cn_alice_change, &entries, &registry);
        assert_eq!(cp[0].received_at, None);
        assert_eq!(cp[1].received_at, Some(1));
        assert_eq!(cp[1].spent, false);

        let _ = (genesis_sk, bob_sk, carol_pk);
    }

    #[test]
    fn demo_chain_is_valid_end_to_end() {
        let (genesis_sk, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (alice_sk, alice_pk) = party(1);
        let (bob_sk, bob_pk) = party(2);
        let (_, carol_pk) = party(3);
        let registry = vec![genesis_pk, alice_pk, bob_pk, carol_pk];

        let genesis_coin  = coin(0xA1, 100, genesis_pk);
        let alice_coin    = coin(0xA2, 100, alice_pk);
        let bob_coin      = coin(0xB1,  40, bob_pk);
        let alice_change  = coin(0xB2,  60, alice_pk);
        let carol_coin    = coin(0xC1,  40, carol_pk);

        let tx0 = make_tx(0, genesis_pk, &[genesis_coin.clone()],
            &[(alice_coin.clone(), alice_pk)]);
        let tx1 = make_tx(1, alice_pk, &[alice_coin.clone()],
            &[(bob_coin.clone(), bob_pk), (alice_change.clone(), alice_pk)]);
        let tx2 = make_tx(2, bob_pk, &[bob_coin.clone()],
            &[(carol_coin, carol_pk)]);
        let entries = vec![encrypt_tx(&tx0), encrypt_tx(&tx1), encrypt_tx(&tx2)];

        let cn_genesis = genesis_coin.commitment();
        let cn_alice   = alice_coin.commitment();
        let cn_bob     = bob_coin.commitment();

        spend(genesis_sk, genesis_pk, cn_genesis, &[], &tx0,
            &[genesis_coin.clone()], &[alice_coin.clone()], true, None).unwrap();

        let alice_cp = coin_proof_chain(alice_pk, cn_alice, &entries[..1], &registry);
        spend(alice_sk, alice_pk, cn_alice, &entries[..1], &tx1,
            &[alice_coin.clone()], &[bob_coin.clone(), alice_change], false,
            Some(alice_cp[0].clone())).unwrap();

        let bob_cp = coin_proof_chain(bob_pk, cn_bob, &entries[..2], &registry);
        spend(bob_sk, bob_pk, cn_bob, &entries[..2], &tx2,
            &[bob_coin.clone()], &[coin(0xC1, 40, carol_pk)], false,
            Some(bob_cp[1].clone())).unwrap();
    }

    #[test]
    fn rejects_wrong_secret_key() {
        let (_, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (alice_sk, alice_pk) = party(1);
        let genesis_coin = coin(0xA1, 100, genesis_pk);
        let alice_coin = coin(0xA2, 100, alice_pk);
        let tx0 = make_tx(0, genesis_pk, &[genesis_coin.clone()], &[(alice_coin.clone(), alice_pk)]);

        let err = spend(alice_sk, genesis_pk, genesis_coin.commitment(), &[], &tx0,
            &[genesis_coin], &[alice_coin], true, None).unwrap_err();
        assert_eq!(err, "pk_P must be the public key for sk_P");
    }

    #[test]
    fn rejects_minting_without_the_genesis_key() {
        let (alice_sk, alice_pk) = party(1);
        let (_, bob_pk) = party(2);
        let alice_coin = coin(0xA1, 100, alice_pk);
        let bob_coin = coin(0xB1, 100, bob_pk);
        let tx0 = make_tx(0, alice_pk, &[alice_coin.clone()], &[(bob_coin.clone(), bob_pk)]);

        let err = spend(alice_sk, alice_pk, alice_coin.commitment(), &[], &tx0,
            &[alice_coin], &[bob_coin], true, None).unwrap_err();
        assert_eq!(err, "only the genesis key may mint without provenance");
    }

    #[test]
    fn rejects_spending_a_coin_one_never_received() {
        let (genesis_sk, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (alice_sk, alice_pk) = party(1);
        let (carol_sk, carol_pk) = party(3);
        let registry = vec![genesis_pk, alice_pk, carol_pk];

        let genesis_coin     = coin(0xA1, 100, genesis_pk);
        let alice_coin       = coin(0xA2, 100, alice_pk);
        let carol_fake_input = coin(0xC1, 100, carol_pk);
        let carol_fake_out   = coin(0xC2, 100, alice_pk);

        let tx0     = make_tx(0, genesis_pk, &[genesis_coin], &[(alice_coin, alice_pk)]);
        let tx_fake = make_tx(1, carol_pk,   &[carol_fake_input.clone()], &[(carol_fake_out.clone(), alice_pk)]);
        let entries = vec![encrypt_tx(&tx0)];
        let cn_carol = carol_fake_input.commitment();

        let carol_cp = coin_proof_chain(carol_pk, cn_carol, &entries, &registry);
        assert_eq!(carol_cp[0].received_at, None);

        let err = spend(carol_sk, carol_pk, cn_carol, &entries, &tx_fake,
            &[carol_fake_input], &[carol_fake_out], false,
            Some(carol_cp[0].clone())).unwrap_err();
        assert_eq!(err, "P must have received this coin at some prior slot");

        let _ = (genesis_sk, alice_sk);
    }

    #[test]
    fn rejects_double_spend() {
        let (genesis_sk, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (alice_sk, alice_pk) = party(1);
        let (_, bob_pk) = party(2);
        let (_, carol_pk) = party(3);
        let registry = vec![genesis_pk, alice_pk, bob_pk, carol_pk];

        let genesis_coin  = coin(0xA1, 100, genesis_pk);
        let alice_coin    = coin(0xA2, 100, alice_pk);
        let bob_coin      = coin(0xB1,  60, bob_pk);
        let alice_change  = coin(0xB2,  40, alice_pk);
        let carol_coin    = coin(0xC1, 100, carol_pk);

        let cn_genesis = genesis_coin.commitment();
        let cn_alice   = alice_coin.commitment();

        let tx0  = make_tx(0, genesis_pk, &[genesis_coin.clone()], &[(alice_coin.clone(), alice_pk)]);
        let tx1  = make_tx(1, alice_pk,   &[alice_coin.clone()],   &[(bob_coin.clone(), bob_pk), (alice_change.clone(), alice_pk)]);
        let tx1b = make_tx(2, alice_pk,   &[alice_coin.clone()],   &[(carol_coin.clone(), carol_pk)]);
        let entries = vec![encrypt_tx(&tx0), encrypt_tx(&tx1)];

        spend(genesis_sk, genesis_pk, cn_genesis, &[], &tx0,
            &[genesis_coin], &[alice_coin.clone()], true, None).unwrap();

        let alice_cp = coin_proof_chain(alice_pk, cn_alice, &entries, &registry);
        assert_eq!(alice_cp[0].received_at, Some(0));
        assert_eq!(alice_cp[1].spent, true);

        spend(alice_sk, alice_pk, cn_alice, &entries[..1], &tx1,
            &[alice_coin.clone()], &[bob_coin, alice_change], false,
            Some(alice_cp[0].clone())).unwrap();

        let err = spend(alice_sk, alice_pk, cn_alice, &entries, &tx1b,
            &[alice_coin], &[carol_coin], false,
            Some(alice_cp[1].clone())).unwrap_err();
        assert_eq!(err, "P must not have spent this coin before (double spend)");
    }

    #[test]
    fn rejects_tampered_board_entry() {
        let (genesis_sk, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (alice_sk, alice_pk) = party(1);
        let (_, bob_pk) = party(2);
        let registry = vec![genesis_pk, alice_pk, bob_pk];

        let genesis_coin = coin(0xA1, 100, genesis_pk);
        let alice_coin   = coin(0xA2, 100, alice_pk);
        let bob_coin     = coin(0xB1, 100, bob_pk);

        let tx0_real = make_tx(0, genesis_pk, &[genesis_coin.clone()], &[(alice_coin.clone(), alice_pk)]);
        let tx1      = make_tx(1, alice_pk,   &[alice_coin.clone()],   &[(bob_coin.clone(), bob_pk)]);
        let entries_real    = vec![encrypt_tx(&tx0_real)];
        let cn_alice = alice_coin.commitment();
        let alice_cp = coin_proof_chain(alice_pk, cn_alice, &entries_real, &registry);

        // Attacker posts a different genesis entry.
        let fake_coin    = coin(0xB3, 100, alice_pk);
        let tx0_fake     = make_tx(0, genesis_pk, &[genesis_coin.clone()], &[(fake_coin.clone(), alice_pk)]);
        let entries_tampered = vec![encrypt_tx(&tx0_fake)];

        let err = spend(alice_sk, alice_pk, cn_alice, &entries_tampered, &tx1,
            &[alice_coin], &[bob_coin], false,
            Some(alice_cp[0].clone())).unwrap_err();
        assert_eq!(err, "coin-proof's board root does not match the board prefix");

        let _ = genesis_sk;
    }

    #[test]
    fn rejects_value_conservation_violation() {
        let (genesis_sk, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (_, alice_pk) = party(1);
        let genesis_coin  = coin(0xA1, 100, genesis_pk);
        let alice_coin    = coin(0xA2, 100, alice_pk);
        let extra_coin    = coin(0xA3,   1, alice_pk);  // total out = 101 ≠ 100

        let tx0 = make_tx(0, genesis_pk, &[genesis_coin.clone()],
            &[(alice_coin.clone(), alice_pk), (extra_coin.clone(), alice_pk)]);

        let err = spend(genesis_sk, genesis_pk, genesis_coin.commitment(), &[], &tx0,
            &[genesis_coin], &[alice_coin, extra_coin], true, None).unwrap_err();
        assert_eq!(err, "transaction violates value conservation: sum(inputs) must equal sum(outputs)");
    }
}
