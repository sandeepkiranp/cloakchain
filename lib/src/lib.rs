use std::collections::{BTreeMap, HashMap};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use x25519_dalek::{PublicKey as X25519PublicKey, StaticSecret as X25519Secret};

pub const GENESIS_SK: [u8; 32] = [0u8; 32];

pub fn genesis_pk() -> [u8; 32] {
    derive_pk(&GENESIS_SK)
}

/// Key derivation: pk = X25519(sk, basepoint).
/// X25519 public keys are indistinguishable from random 32-byte strings —
/// every 32-byte value is a valid Curve25519 u-coordinate.
pub fn derive_pk(sk: &[u8; 32]) -> [u8; 32] {
    let secret = X25519Secret::from(*sk);
    *X25519PublicKey::from(&secret).as_bytes()
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
/// Only **commitments** appear in the transaction body. Sender and recipient
/// identities are NOT stored — the sender is proven via `input_nullifier` and
/// recipient ownership is encoded inside each coin commitment (`H(tag||v||r||pk)`).
/// Each output's coin data is encrypted in `note_encs[i]` per recipient.
///
/// `spend_proof` is attached after proving and the whole struct re-encrypted.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Transaction {
    pub id: u64,
    /// Commitments to the coins being spent.
    pub input_commitments: Vec<[u8; 32]>,
    /// Commitments to the new coins (same index as note_encs).
    pub output_commitments: Vec<[u8; 32]>,
    /// `note_encs[i]` = `encrypt(output_coin_i, pair_key(sender, recipient_i))`.
    pub note_encs: Vec<Vec<u8>>,
    /// `H(primary_input_commitment || sk_spender)` — proves sender identity
    /// without storing sender_pk; also serves as the double-spend nullifier.
    pub input_nullifier: [u8; 32],
    pub spend_proof: Vec<u8>,
}

impl Transaction {
    /// `cn` was received in this tx if it is among the output commitments.
    /// Recipient ownership is already encoded inside the commitment itself.
    pub fn receives_coin(&self, cn: &[u8; 32]) -> bool {
        self.output_commitments.contains(cn)
    }

    /// `cn` was spent as an input in this tx.
    pub fn spends_coin(&self, cn: &[u8; 32]) -> bool {
        self.input_commitments.contains(cn)
    }
}

// ---- X25519 sender-anonymous encryption ------------------------------------
//
// Each transaction is encrypted with a random session key. The session key is
// wrapped separately for each recipient using X25519 ECDH — only the holder of
// the recipient's private key can recover it. The sender is never identified:
// the recipient only uses their own sk and the ephemeral public key `ek_pk`.
//
// Note data (coin tag/value/rand) for output i is encrypted with a key derived
// from the session key: `note_key_i = H(session_key || i || NOTE_SALT)`. The
// recipient decrypts the transaction ciphertext first (giving session_key), then
// tries each index to find their coin.

/// Magic tag embedded in the transaction ciphertext.
const MAGIC_TAG: [u8; 8] = *b"CLOAKTX1";
/// Magic tag embedded in each note encryption.
const NOTE_MAGIC: [u8; 8] = *b"CLOAKNT1";
/// Salt for deriving the ephemeral key from the session key.
pub const EK_SALT: [u8; 8] = *b"CLOAKEK1";
/// Salt for the X25519 shared-secret → wrapping-key derivation.
const DH_SALT: [u8; 8] = *b"CLOAKDH1";
/// Salt for per-index note key derivation.
const NOTE_SALT: [u8; 8] = *b"CLOAKNT2";

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

/// Derive the ephemeral X25519 secret from the session key (deterministic so
/// re-encryption after attaching a spend proof produces the same `ek_pk`).
fn ek_secret(session_key: &[u8; 32]) -> X25519Secret {
    let mut h = Sha256::new();
    h.update(session_key);
    h.update(EK_SALT);
    let mut bytes = [0u8; 32];
    bytes.copy_from_slice(&h.finalize());
    X25519Secret::from(bytes)
}

/// Wrapping key: H(X25519 shared secret || DH_SALT).
fn wrapping_key(shared: &[u8; 32]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(shared);
    h.update(DH_SALT);
    let mut out = [0u8; 32];
    out.copy_from_slice(&h.finalize());
    out
}

/// A board entry: the transaction encrypted with a session key, plus one 32-byte
/// `key_enc` per recipient (indistinguishable from random), plus one ephemeral
/// X25519 public key `ek_pk` (also looks like 32 random bytes on Curve25519).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BoardEntry {
    /// `xor_with_keystream(session_key, MAGIC_TAG || bincode(tx))`.
    pub ciphertext: Vec<u8>,
    /// The ephemeral X25519 public key — 32 bytes, looks random.
    /// Recipients compute `X25519(recipient_sk, ek_pk)` to get the shared secret.
    pub ek_pk: [u8; 32],
    /// `key_encs[i] = XOR(H(X25519(ek_sk, recipient_pk_i) || DH_SALT), session_key)`.
    /// Each is exactly 32 bytes, looks random. One per recipient.
    pub key_encs: Vec<[u8; 32]>,
    /// `tx.input_nullifier` — looks random, used by IVC for double-spend detection.
    pub nullifier: [u8; 32],
}

/// Encrypt `tx` for the given `recipient_pks` and `session_key`.
/// Pass the same `session_key` when re-encrypting after attaching a spend proof —
/// the deterministic `ek_sk` ensures `ek_pk` and `key_encs` are unchanged.
pub fn encrypt_tx(
    tx: &Transaction,
    recipient_pks: &[[u8; 32]],
    session_key: [u8; 32],
) -> BoardEntry {
    // Derive the ephemeral key from the session key (deterministic).
    let ek_sk = ek_secret(&session_key);
    let ek_pk = *X25519PublicKey::from(&ek_sk).as_bytes();

    // Encrypt the transaction body.
    let tx_bytes = bincode::serialize(tx).expect("Transaction is always serializable");
    let mut plaintext = MAGIC_TAG.to_vec();
    plaintext.extend_from_slice(&tx_bytes);
    let ciphertext = xor_with_keystream(&session_key, &plaintext);

    // Wrap the session key for each recipient using X25519 ECDH.
    let key_encs = recipient_pks.iter().map(|rpk| {
        let recipient_pub = X25519PublicKey::from(*rpk);
        let shared = *ek_sk.diffie_hellman(&recipient_pub).as_bytes();
        let wk = wrapping_key(&shared);
        let mut enc = [0u8; 32];
        for (e, (w, s)) in enc.iter_mut().zip(wk.iter().zip(session_key.iter())) {
            *e = w ^ s;
        }
        enc
    }).collect();

    BoardEntry { ciphertext, ek_pk, key_encs, nullifier: tx.input_nullifier }
}

/// Decrypt a board entry using the recipient's private key.
/// Tries each `key_enc` — the one that yields a valid session key will decrypt
/// the ciphertext successfully. No sender identity is needed or revealed.
pub fn scan_entry(
    owner_sk: &[u8; 32],
    entry: &BoardEntry,
) -> Option<Transaction> {
    let owner_secret = X25519Secret::from(*owner_sk);
    let ek_pub = X25519PublicKey::from(entry.ek_pk);
    let shared = *owner_secret.diffie_hellman(&ek_pub).as_bytes();
    let wk = wrapping_key(&shared);

    for key_enc in &entry.key_encs {
        let mut session_key = [0u8; 32];
        for (s, (w, e)) in session_key.iter_mut().zip(wk.iter().zip(key_enc.iter())) {
            *s = w ^ e;
        }
        if entry.ciphertext.len() <= 8 { continue; }
        let tx_bytes = xor_with_keystream(&session_key, &entry.ciphertext);
        if tx_bytes[..8] != MAGIC_TAG { continue; }
        if let Ok(tx) = bincode::deserialize::<Transaction>(&tx_bytes[8..]) {
            return Some(tx);
        }
    }
    None
}

/// Recover the session key for a board entry. Used by the sender to re-encrypt
/// or by a recipient who needs to decrypt notes after already having the tx.
pub fn recover_session_key(owner_sk: &[u8; 32], entry: &BoardEntry) -> Option<[u8; 32]> {
    let owner_secret = X25519Secret::from(*owner_sk);
    let ek_pub = X25519PublicKey::from(entry.ek_pk);
    let shared = *owner_secret.diffie_hellman(&ek_pub).as_bytes();
    let wk = wrapping_key(&shared);
    for key_enc in &entry.key_encs {
        let mut session_key = [0u8; 32];
        for (s, (w, e)) in session_key.iter_mut().zip(wk.iter().zip(key_enc.iter())) {
            *s = w ^ e;
        }
        // Verify by attempting to decrypt the ciphertext.
        if entry.ciphertext.len() > 8 {
            let tx_bytes = xor_with_keystream(&session_key, &entry.ciphertext);
            if tx_bytes[..8] == MAGIC_TAG {
                return Some(session_key);
            }
        }
    }
    None
}

/// Encrypt a coin as output note `index` of a transaction.
/// `note_key = H(session_key || index || NOTE_SALT)` — derived from the session key.
pub fn build_note_enc(session_key: &[u8; 32], index: usize, coin: &Coin) -> Vec<u8> {
    let mut h = Sha256::new();
    h.update(session_key);
    h.update((index as u64).to_le_bytes());
    h.update(NOTE_SALT);
    let mut note_key = [0u8; 32];
    note_key.copy_from_slice(&h.finalize());
    let coin_bytes = bincode::serialize(coin).expect("Coin is always serializable");
    let mut payload = NOTE_MAGIC.to_vec();
    payload.extend_from_slice(&coin_bytes);
    xor_with_keystream(&note_key, &payload)
}

/// Decrypt note at `index` — returns the `Coin` if the session key is correct.
pub fn decrypt_note(session_key: &[u8; 32], index: usize, note_enc: &[u8]) -> Option<Coin> {
    let mut h = Sha256::new();
    h.update(session_key);
    h.update((index as u64).to_le_bytes());
    h.update(NOTE_SALT);
    let mut note_key = [0u8; 32];
    note_key.copy_from_slice(&h.finalize());
    let dec = xor_with_keystream(&note_key, note_enc);
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
/// leaves equal to [0u8;32]. Computed once and cached — `NullifierTree::insert`
/// calls this on every leaf update, and recomputing 32 hashes from scratch
/// each time (rather than once, ever) was the dominant cost at scale.
fn zero_hashes() -> &'static [[u8; 32]] {
    static ZERO_HASHES: std::sync::OnceLock<Vec<[u8; 32]>> = std::sync::OnceLock::new();
    ZERO_HASHES.get_or_init(|| {
        let mut out = vec![[0u8; 32]]; // depth 0: the zero leaf itself
        for _ in 0..TREE_DEPTH {
            let prev = *out.last().unwrap();
            out.push(merkle_combine(&prev, &prev));
        }
        out
    })
}

/// Root of the empty fixed-depth tree (all leaves = [0u8;32]).
pub fn empty_root() -> [u8; 32] {
    zero_hashes()[TREE_DEPTH]
}

/// Walk the path from `leaf` at `slot` to the root. Used by
/// `merkle_root_of`, `check_coin_receipt`, and `check_spend`.
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

/// Build the fixed-depth (`TREE_DEPTH`) Merkle path for position `target_idx`,
/// given the hashes of whatever leaves are currently filled. Any position at
/// or beyond `leaf_hashes.len()` (including `target_idx` itself) is treated
/// as unfilled and uses the zero-subtree hash — this works equally well for
/// proving an *existing* leaf or for proving the next, as-yet-empty slot.
fn merkle_path_for_index(leaf_hashes: &[[u8; 32]], target_idx: usize) -> Vec<[u8; 32]> {
    let zeros = zero_hashes();
    let mut path = Vec::with_capacity(TREE_DEPTH);
    let mut level: Vec<[u8; 32]> = leaf_hashes.to_vec();
    let mut idx = target_idx;
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

/// Inclusion proof for `slot` in the fixed-depth tree over `entries`.
/// At each level the sibling is either the real hash of the adjacent subtree
/// (if it was already filled by prior entries) or the zero-subtree hash.
pub fn append_proof_for(entries: &[BoardEntry]) -> Vec<[u8; 32]> {
    let slot = entries.len() - 1;
    let hashes: Vec<[u8; 32]> = entries.iter().enumerate().map(|(i, e)| merkle_leaf(i, e)).collect();
    merkle_path_for_index(&hashes, slot)
}

/// Append-path for the *next*, as-yet-unfilled slot after `entries` — used by
/// `check_spend` to prove the board state immediately before `tx_star` is
/// posted, without needing the entire prior board history as a witness (only
/// its leaf hashes, derived here from the entries the caller already has).
pub fn append_path_for_next(entries: &[BoardEntry]) -> Vec<[u8; 32]> {
    let hashes: Vec<[u8; 32]> = entries.iter().enumerate().map(|(i, e)| merkle_leaf(i, e)).collect();
    merkle_path_for_index(&hashes, entries.len())
}

/// Verify that `entry` is the genuine content of `slot` in a fixed-depth tree
/// with the given `root`.
pub fn merkle_verify(root: [u8; 32], slot: usize, entry: &BoardEntry, proof: &[[u8; 32]]) -> bool {
    compute_root_from_path(merkle_leaf(slot, entry), slot, proof) == root
}

// ---- Nullifier accumulator (indexed Merkle tree) --------------------------
//
// Double-spend detection no longer requires walking every board slot in an
// IVC chain. Every nullifier ever published (`BoardEntry.nullifier`, already
// public) is inserted into a single indexed Merkle tree — a sorted linked
// list of leaves, each storing `(value, next_value, next_index)`. A single
// Merkle path to a leaf whose `value < target < next_value` proves `target`
// is absent from the *entire* set the tree's root represents, in one
// O(TREE_DEPTH) proof instead of an O(slots) scan. Reuses the same SHA256
// combine/path primitives as the board tree above.

/// One leaf of the indexed nullifier tree.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IndexedLeaf {
    pub value: [u8; 32],
    pub next_value: [u8; 32],
    pub next_index: u64,
}

/// Sentinel "infinity" value: no real nullifier (a SHA256 output) will ever
/// equal this, so it safely upper-bounds every real value.
const MAX_NULLIFIER: [u8; 32] = [0xFF; 32];

impl IndexedLeaf {
    fn hash(&self) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(self.value);
        h.update(self.next_value);
        h.update(self.next_index.to_le_bytes());
        let mut out = [0u8; 32];
        out.copy_from_slice(&h.finalize());
        out
    }
}

/// A non-membership proof: the "low" leaf whose `value < target < next_value`
/// — impossible to construct unless `target` is genuinely absent — plus its
/// Merkle inclusion path. (If `target` happens to already be a member, the
/// natural low leaf instead has `next_value == target`, which fails the
/// strict `target < next_value` check in `verify_nonmembership` below.)
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NonMembershipWitness {
    pub low_leaf: IndexedLeaf,
    pub low_leaf_index: u64,
    pub sibling_path: Vec<[u8; 32]>,
}

/// Verify a non-membership witness against `root`: `target` cannot be a
/// member if some leaf's `value < target < next_value` genuinely Merkle-opens
/// to `root` — no member could exist strictly between two adjacent leaves.
pub fn verify_nonmembership(root: [u8; 32], target: [u8; 32], witness: &NonMembershipWitness) -> bool {
    if !(witness.low_leaf.value < target && target < witness.low_leaf.next_value) {
        return false;
    }
    let leaf_hash = witness.low_leaf.hash();
    compute_root_from_path(leaf_hash, witness.low_leaf_index as usize, &witness.sibling_path) == root
}

/// Host-side append-only indexed Merkle tree of nullifiers. Anyone can rebuild
/// this deterministically from the public `BoardEntry.nullifier` values, the
/// same way `merkle_root_of` lets anyone rebuild the board's root.
///
/// Maintained *incrementally*: `index_of` gives O(log n) low-leaf lookup
/// (instead of scanning every leaf), and `nodes` caches every level's node
/// hashes so inserting only recomputes the O(TREE_DEPTH) ancestors of the two
/// leaves that actually changed — not the whole tree from scratch. Both
/// matter once the board has hundreds of thousands of entries: without them,
/// `insert` is O(n) and `replay` (which calls `insert` in a loop) becomes
/// O(n²), the same class of problem sorted-leaf Merkle trees have, just
/// arrived at via a slow implementation rather than a sorted array.
#[derive(Clone, Debug)]
pub struct NullifierTree {
    leaves: Vec<IndexedLeaf>,
    /// value → leaf index, sorted — gives the low leaf for any target via one
    /// `range(..target).next_back()` lookup instead of a linear scan.
    index_of: BTreeMap<[u8; 32], usize>,
    /// `nodes[d]` holds the hash of every *filled* node at depth d (0 =
    /// leaves, `TREE_DEPTH` = root), keyed by its position at that depth.
    /// A missing entry means "unfilled" — use the precomputed zero-subtree
    /// hash for that depth instead (see `zero_hashes`).
    nodes: Vec<HashMap<usize, [u8; 32]>>,
}

impl NullifierTree {
    /// A fresh tree, seeded with the single "everything" sentinel leaf.
    pub fn new() -> Self {
        let sentinel = IndexedLeaf { value: [0u8; 32], next_value: MAX_NULLIFIER, next_index: 0 };
        let mut tree = Self {
            leaves: vec![sentinel.clone()],
            index_of: BTreeMap::new(),
            nodes: vec![HashMap::new(); TREE_DEPTH + 1],
        };
        tree.index_of.insert(sentinel.value, 0);
        tree.set_leaf(0, sentinel.hash());
        tree
    }

    /// Set leaf `idx`'s hash and propagate the change up to the root —
    /// O(TREE_DEPTH), independent of how many leaves currently exist.
    fn set_leaf(&mut self, idx: usize, hash: [u8; 32]) {
        let zeros = zero_hashes();
        let mut cur_idx = idx;
        let mut cur_hash = hash;
        for d in 0..TREE_DEPTH {
            self.nodes[d].insert(cur_idx, cur_hash);
            let sibling_idx = cur_idx ^ 1;
            let sibling = self.nodes[d].get(&sibling_idx).copied().unwrap_or(zeros[d]);
            cur_hash = if cur_idx % 2 == 0 { merkle_combine(&cur_hash, &sibling) } else { merkle_combine(&sibling, &cur_hash) };
            cur_idx >>= 1;
        }
        self.nodes[TREE_DEPTH].insert(cur_idx, cur_hash); // cur_idx == 0: the root
    }

    pub fn root(&self) -> [u8; 32] {
        self.nodes[TREE_DEPTH].get(&0).copied().unwrap_or_else(|| zero_hashes()[TREE_DEPTH])
    }

    pub fn contains(&self, value: [u8; 32]) -> bool {
        self.index_of.contains_key(&value)
    }

    /// The leaf whose `value < target <= next_value` — for a genuine
    /// non-member this is the unique insertion point (`target < next_value`
    /// strictly); for an existing member it's that value's predecessor
    /// (`next_value == target`), which correctly yields a witness that
    /// `verify_nonmembership` will reject rather than one that panics here.
    /// O(log n) via `index_of` instead of scanning every leaf.
    fn find_low_leaf_index(&self, target: [u8; 32]) -> usize {
        *self.index_of.range(..target).next_back().map(|(_, idx)| idx)
            .expect("no matching leaf — target is [0u8;32] or tree invariant violated")
    }

    /// Insert `value` (a no-op if already present) and return the new root.
    /// O(log n): one BTreeMap lookup plus two O(TREE_DEPTH) path updates.
    pub fn insert(&mut self, value: [u8; 32]) -> [u8; 32] {
        if self.contains(value) {
            return self.root();
        }
        let low_idx = self.find_low_leaf_index(value);
        let low = self.leaves[low_idx].clone();
        let new_index = self.leaves.len();
        let updated_low = IndexedLeaf { value: low.value, next_value: value, next_index: new_index as u64 };
        let new_leaf = IndexedLeaf { value, next_value: low.next_value, next_index: low.next_index };

        self.leaves[low_idx] = updated_low.clone();
        self.leaves.push(new_leaf.clone());
        self.index_of.insert(value, new_index);

        self.set_leaf(low_idx, updated_low.hash());
        self.set_leaf(new_index, new_leaf.hash());
        self.root()
    }

    /// Sibling path for leaf `idx`, read directly from the maintained
    /// per-level node hashes — O(TREE_DEPTH), not a from-scratch rebuild.
    fn path_for(&self, idx: usize) -> Vec<[u8; 32]> {
        let zeros = zero_hashes();
        let mut path = Vec::with_capacity(TREE_DEPTH);
        let mut cur_idx = idx;
        for d in 0..TREE_DEPTH {
            let sibling_idx = cur_idx ^ 1;
            path.push(self.nodes[d].get(&sibling_idx).copied().unwrap_or(zeros[d]));
            cur_idx >>= 1;
        }
        path
    }

    /// Build a non-membership witness for `target` against the tree's current
    /// state. Safe to call even if `target` is already a member — the
    /// resulting witness simply won't pass `verify_nonmembership`.
    pub fn prove_non_membership(&self, target: [u8; 32]) -> NonMembershipWitness {
        let low_idx = self.find_low_leaf_index(target);
        NonMembershipWitness {
            low_leaf: self.leaves[low_idx].clone(),
            low_leaf_index: low_idx as u64,
            sibling_path: self.path_for(low_idx),
        }
    }

    /// Rebuild the tree as it stood after exactly `count` of `inserted`'s
    /// values were inserted, by replaying from scratch. Used to answer "was X
    /// absent as of slot S" for the historical parent-nullifier check below.
    /// O(count log count) given the incremental `insert` above — cheap,
    /// no SNARK cost, run entirely host-side.
    pub fn replay(inserted: &[[u8; 32]], count: usize) -> Self {
        let mut tree = Self::new();
        for &n in &inserted[..count] {
            tree.insert(n);
        }
        tree
    }
}

impl Default for NullifierTree {
    fn default() -> Self {
        Self::new()
    }
}

// ---- Public values -------------------------------------------------------

/// The public values committed by the spend (`Valid`) relation.
///
/// `board_root` is the Merkle root of `entries[0..last]` — the board state
/// *before* tx* was posted (the Zcash-style "anchor"). This breaks the
/// circular dependency: the proof commits to a root that does not include itself,
/// so the proof can be embedded inside tx* and re-encrypted without any
/// self-reference.
///
/// `output_commitments` are the coin commitments created by this spend. The
/// recipient's IVC coin-proof verifies this proof at the receipt slot and checks
/// that their `coin_commitment` is listed here — establishing a cryptographic
/// chain of custody from the creating spend proof all the way to the final
/// spend proof.
///
/// The spender's public key is intentionally NOT included — the proof proves
/// "someone with the right key spent this coin" without revealing who.
/// Spender identity is encoded in `tx.input_nullifier` inside the encrypted
/// transaction, visible only to authorised parties.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ValidPublicValues {
    pub vkey: [u32; 8],
    pub board_root: [u8; 32],
    /// The output coin commitments created by this spend — used by recipients
    /// to chain-verify provenance in their receipt proof.
    pub output_commitments: Vec<[u8; 32]>,
    /// The nullifier-accumulator root as of just before this spend (i.e. not
    /// yet including this spend's own `input_nullifier`) — lets downstream
    /// verifiers independently confirm it against their own rebuilt tree, the
    /// same way `board_root` already lets them confirm board state.
    pub nullifier_root: [u8; 32],
}

impl ValidPublicValues {
    pub fn encode(&self) -> Vec<u8> {
        bincode::serialize(self).expect("ValidPublicValues is always serializable")
    }
}

// ---- Coin receipt ----------------------------------------------------------
//
// A coin's receipt is a single proof, built once when the coin is first
// discovered — not an IVC chain re-extended every board slot. It proves:
//
//   - `entry_k` (the transaction that created this coin) really is included
//     in the board at `received_at`, via one Merkle append-path.
//   - that creating transaction's own Groth16 receipt is valid (the VFY-G16
//     fold, unchanged from before).
//   - the creating transaction's own nullifier had not already been used
//     anywhere on the board as of its own slot — via one non-membership
//     proof against the nullifier accumulator (see above), replacing the old
//     per-slot byte-scan for "parent_nullifier_seen". This is enforced
//     directly: a receipt simply cannot be constructed over a double-spending
//     parent transaction (see `check_coin_receipt` below).
//
// Whether the coin has since been *spent* is no longer tracked here at all —
// that's answered fresh, at spend time, with a single non-membership check
// against the *current* nullifier root (see `check_spend`), not maintained
// incrementally while the coin just sits held.

/// The public values committed by a coin's receipt proof.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoinReceiptPublicValues {
    pub vkey: [u32; 8],
    pub owner_pk: [u8; 32],
    pub coin_commitment: [u8; 32],
    pub board_root: [u8; 32],
    pub received_at: u64,
}

impl CoinReceiptPublicValues {
    pub fn encode(&self) -> Vec<u8> {
        bincode::serialize(self).expect("CoinReceiptPublicValues is always serializable")
    }
}

/// The spend proof stored in `tx.spend_proof` for in-circuit chain verification.
///
/// Contains the Groth16 proof bytes from `proof.bytes()`, the spend proof public
/// values, and the spend vkey hash — everything the coin-proof IVC needs to call
/// `Groth16Verifier::verify` at the receipt slot.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SpendProofPackage {
    /// `SP1ProofWithPublicValues::bytes()` of the Groth16 spend proof.
    /// HOST passes this via `stdin.write_vec()`; program calls `Groth16Verifier::verify`.
    /// Empty in execute/mock mode — logical output_commitments check is sufficient then.
    pub proof_bytes: Vec<u8>,
    /// `ValidPublicValues::encode()` — the spend proof's committed public values.
    /// Checked in `check_coin_receipt` to verify the spend commits to this coin.
    pub pv_encode: Vec<u8>,
    /// Spend program vkey hash from `spend_pk.verifying_key().bytes32()`.
    pub spend_vkey_hash: String,
}

/// What the program must verify at the receipt slot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiptInfo {
    /// `ValidPublicValues::encode()` from the spend proof package — used by the
    /// program as `sp1_public_inputs` when calling `Groth16Verifier::verify`.
    pub pv_encode: Vec<u8>,
}

/// What the receipt proof needs the guest program to additionally verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoinReceiptJustification {
    /// Present iff the creating transaction has a Groth16 spend proof to fold
    /// (empty only in mock/execute mode — see `SpendProofPackage`).
    pub receipt: Option<ReceiptInfo>,
}

/// Build a coin's one-shot receipt proof.
///
/// `entry_k` is the single board entry that transfers `coin_commitment` to
/// `owner_sk`'s holder, at `received_slot`; `append_path` is its Merkle
/// inclusion proof (`TREE_DEPTH` sibling hashes, leaf → root) — the same
/// mechanism `merkle_root_of` uses, just proving one specific leaf instead of
/// recomputing the whole tree, and used exactly once instead of per-slot.
///
/// The creating transaction's own nullifier (= `entry_k.nullifier`, since
/// `BoardEntry.nullifier` is always set to `tx.input_nullifier`) must not
/// already have been used anywhere on the board as of that transaction's own
/// slot — `parent_nonmembership`/`nullifier_root_at_parent_slot` prove this.
/// If that check fails, the creating transaction was itself a double-spend,
/// and this function returns `Err` rather than a usable receipt (replacing
/// the old per-slot `parent_nullifier_seen` scan, which was computed but
/// never actually enforced).
pub fn check_coin_receipt(
    vkey: [u32; 8],
    owner_sk: [u8; 32],
    coin_commitment: [u8; 32],
    entry_k: BoardEntry,
    received_slot: usize,
    append_path: Vec<[u8; 32]>,
    parent_nonmembership: NonMembershipWitness,
    nullifier_root_at_parent_slot: [u8; 32],
) -> Result<(CoinReceiptPublicValues, CoinReceiptJustification), &'static str> {
    let owner_pk = derive_pk(&owner_sk);

    if !verify_nonmembership(nullifier_root_at_parent_slot, entry_k.nullifier, &parent_nonmembership) {
        return Err("parent transaction's nullifier was already present on the board — it was a double-spend");
    }

    let leaf_k = merkle_leaf(received_slot, &entry_k);
    let board_root = compute_root_from_path(leaf_k, received_slot, &append_path);

    let tx = scan_entry(&owner_sk, &entry_k).ok_or("entry_k does not decrypt for this owner")?;
    if !tx.receives_coin(&coin_commitment) {
        return Err("entry_k's transaction does not transfer coin_commitment to this owner");
    }

    // Extract the spend proof package from the creating transaction and verify
    // that it commits to this coin. The program will call verify_sp1_proof on
    // it; here we only do the logical provenance check.
    let mut receipt: Option<ReceiptInfo> = None;
    if !tx.spend_proof.is_empty() {
        let pkg = bincode::deserialize::<SpendProofPackage>(&tx.spend_proof)
            .map_err(|_| "receipt tx.spend_proof is not a valid SpendProofPackage")?;
        let pv = bincode::deserialize::<ValidPublicValues>(&pkg.pv_encode)
            .map_err(|_| "SpendProofPackage has invalid pv_encode")?;
        if !pv.output_commitments.contains(&coin_commitment) {
            return Err("parent spend proof does not commit to this coin commitment");
        }
        // Non-empty proof_bytes → real Groth16 proof; program verifies it.
        // Empty → mock/execute mode; output_commitments check is sufficient.
        if !pkg.proof_bytes.is_empty() {
            receipt = Some(ReceiptInfo { pv_encode: pkg.pv_encode });
        }
    }

    Ok((
        CoinReceiptPublicValues {
            vkey,
            owner_pk,
            coin_commitment,
            board_root,
            received_at: received_slot as u64,
        },
        CoinReceiptJustification { receipt },
    ))
}

// ---- Spend relation --------------------------------------------------------

/// Checks every condition of the `Valid` (spend) relation except actually
/// verifying the recursive receipt proof's ZK proof.
///
/// `entry_position` is the slot `tx_star` will land at (== current board
/// size); `append_path` is its Merkle append proof, verified against the
/// *old* root (`[0u8;32]` placeholder at that position) — the same technique
/// `check_coin_receipt` uses for a receiving entry, just for an unfilled
/// position. This replaces passing the entire prior board history and
/// recomputing its root from scratch on every spend.
///
/// `own_nullifier_nonmembership`/`current_nullifier_root` prove the coin has
/// not already been spent: a single non-membership check against the
/// nullifier accumulator's current state, replacing the old `cp.spent` field
/// that had to be kept fresh via a per-slot IVC. This check is uniform for
/// genesis and non-genesis spends — an empty/near-empty accumulator trivially
/// proves non-membership, so no special-casing is needed for an empty board.
///
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
    entry_position: usize,
    append_path: Vec<[u8; 32]>,
    tx_star: Transaction,
    input_coins: Vec<Coin>,
    output_coins: Vec<Coin>,
    is_genesis: bool,
    coin_proof: Option<CoinReceiptPublicValues>,
    own_nullifier_nonmembership: NonMembershipWitness,
    current_nullifier_root: [u8; 32],
) -> Result<ValidPublicValues, &'static str> {
    if derive_pk(&sk_p) != pk_p {
        return Err("pk_P must be the public key for sk_P");
    }

    let board_root = compute_root_from_path([0u8; 32], entry_position, &append_path);

    // Compute and verify the spender's own nullifier.
    // This replaces the old sender_pk check and also serves as the double-spend guard.
    let own_nullifier = {
        let mut h = Sha256::new();
        h.update(coin_commitment);
        h.update(sk_p);
        let mut out = [0u8; 32];
        out.copy_from_slice(&h.finalize());
        out
    };
    if tx_star.input_nullifier != own_nullifier {
        return Err("tx* input_nullifier does not match H(coin_commitment || sk_p)");
    }

    // Double-spend guard: own_nullifier must be absent from the nullifier
    // accumulator's current state. Uniform for genesis and non-genesis.
    if !verify_nonmembership(current_nullifier_root, own_nullifier, &own_nullifier_nonmembership) {
        return Err("P must not have spent this coin before (double spend)");
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
        // Genesis creates coins from authority (PoW) — no prior receipt required.
        if pk_p != genesis_pk() {
            return Err("only the genesis key may mint without provenance");
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
    }

    Ok(ValidPublicValues {
        vkey,
        board_root,
        output_commitments: tx_star.output_commitments.clone(),
        nullifier_root: current_nullifier_root,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEST_VKEY: [u32; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    const TEST_COIN_PROOF_VKEY: [u32; 8] = [9, 9, 9, 9, 9, 9, 9, 9];

    fn party(seed: u8) -> ([u8; 32], [u8; 32]) {
        let mut sk = [0u8; 32];
        sk[1] = seed; // byte 0 is clamped by X25519 (sk[0] &= 248), so seeds 1-7 would
                      // all collapse to the same scalar as genesis. Use byte 1 instead.
        (sk, derive_pk(&sk))
    }

    fn coin(seed: u8, value: u64, owner_pk: [u8; 32]) -> Coin {
        let mut tag = [0u8; 32];
        tag[0] = seed;
        let mut rand = [0u8; 32];
        rand[1] = seed;
        Coin { tag, value, rand, owner_pk }
    }

    /// Build a Transaction using X25519 note encryption derived from session_key.
    /// Returns (tx, session_key, recipient_pks) so callers can pass to `enc`.
    fn make_tx(
        id: u64,
        sender_sk: [u8; 32],
        input_coins: &[Coin],
        outputs: &[(Coin, [u8; 32])],
    ) -> (Transaction, [u8; 32], Vec<[u8; 32]>) {
        let input_commitments: Vec<[u8; 32]> = input_coins.iter().map(|c| c.commitment()).collect();
        let recipient_pks: Vec<[u8; 32]> = outputs.iter().map(|(_, rpk)| *rpk).collect();
        let output_commitments: Vec<[u8; 32]> = outputs.iter().map(|(c, _)| c.commitment()).collect();
        // Derive session key deterministically from sender_sk and id (test helper).
        let session_key = {
            let mut h = Sha256::new();
            h.update(sender_sk); h.update((id as u64).to_le_bytes()); h.update(EK_SALT);
            let mut out = [0u8; 32]; out.copy_from_slice(&h.finalize()); out
        };
        let note_encs: Vec<Vec<u8>> = outputs.iter().enumerate()
            .map(|(i, (c, _))| build_note_enc(&session_key, i, c))
            .collect();
        let input_nullifier = {
            let mut h = Sha256::new();
            h.update(input_commitments[0]); h.update(sender_sk);
            let mut out = [0u8; 32]; out.copy_from_slice(&h.finalize()); out
        };
        let tx = Transaction { id, input_commitments, output_commitments, note_encs, input_nullifier, spend_proof: vec![] };
        (tx, session_key, recipient_pks)
    }

    fn enc(tx: &Transaction, recipient_pks: &[[u8;32]], session_key: [u8;32]) -> BoardEntry {
        encrypt_tx(tx, recipient_pks, session_key)
    }

    /// Build a coin's one-shot receipt: `entries[received_slot]` must be the
    /// transaction that transfers `coin_commitment` to `owner_sk`'s holder.
    /// The parent-nullifier non-membership witness/root are derived by
    /// replaying all of `entries`' nullifiers up to (excluding)
    /// `received_slot` — the board state as it stood just before the
    /// creating transaction itself.
    fn make_receipt(
        owner_sk: [u8; 32],
        coin_commitment: [u8; 32],
        entries: &[BoardEntry],
        received_slot: usize,
    ) -> Result<(CoinReceiptPublicValues, CoinReceiptJustification), &'static str> {
        let ap = append_proof_for(&entries[..=received_slot]);
        let all_nullifiers: Vec<[u8; 32]> = entries.iter().map(|e| e.nullifier).collect();
        let tree = NullifierTree::replay(&all_nullifiers, received_slot);
        let parent_root = tree.root();
        let parent_witness = tree.prove_non_membership(entries[received_slot].nullifier);
        check_coin_receipt(
            TEST_COIN_PROOF_VKEY, owner_sk, coin_commitment,
            entries[received_slot].clone(), received_slot, ap,
            parent_witness, parent_root,
        )
    }

    /// Spend `coin_commitment` given the board state `prior_entries` (i.e.
    /// before `tx_star` is posted). The nullifier non-membership witness and
    /// current root are derived by replaying all of `prior_entries`' own
    /// nullifiers — the same accumulator state any external verifier could
    /// independently rebuild.
    fn spend(
        sk: [u8; 32],
        pk: [u8; 32],
        coin_commitment: [u8; 32],
        prior_entries: &[BoardEntry],
        tx_star: &Transaction,
        input_coins: &[Coin],
        output_coins: &[Coin],
        is_genesis: bool,
        coin_proof: Option<CoinReceiptPublicValues>,
    ) -> Result<ValidPublicValues, &'static str> {
        let ap = append_path_for_next(prior_entries);
        let all_nullifiers: Vec<[u8; 32]> = prior_entries.iter().map(|e| e.nullifier).collect();
        let tree = NullifierTree::replay(&all_nullifiers, prior_entries.len());
        let own_nullifier = {
            let mut h = Sha256::new();
            h.update(coin_commitment); h.update(sk);
            let mut out = [0u8; 32]; out.copy_from_slice(&h.finalize()); out
        };
        let witness = tree.prove_non_membership(own_nullifier);
        let root = tree.root();
        check_spend(
            TEST_VKEY, TEST_COIN_PROOF_VKEY, sk, pk, coin_commitment,
            prior_entries.len(), ap, tx_star.clone(),
            input_coins.to_vec(), output_coins.to_vec(),
            is_genesis, coin_proof, witness, root,
        )
    }

    #[test]
    fn encrypt_decrypt_round_trips_for_participants_and_rejects_outsiders() {
        let (alice_sk, alice_pk) = party(1);
        let (bob_sk, bob_pk) = party(2);
        let (carol_sk, carol_pk) = party(3);

        let alice_coin = coin(0xA2, 100, alice_pk);
        let (tx0, sk0, r0) = make_tx(0, GENESIS_SK,
            &[coin(0xA1, 100, genesis_pk())], &[(alice_coin.clone(), alice_pk)]);
        let entry = enc(&tx0, &r0, sk0);

        // Alice (recipient) can decrypt.
        assert_eq!(scan_entry(&alice_sk, &entry), Some(tx0.clone()));
        // Outsiders cannot.
        assert_eq!(scan_entry(&bob_sk,   &entry), None);
        assert_eq!(scan_entry(&carol_sk, &entry), None);

        // Alice decrypts her note via session_key + index.
        assert_eq!(decrypt_note(&sk0, 0, &tx0.note_encs[0]), Some(alice_coin));
        // Wrong index gives None.
        assert_eq!(decrypt_note(&sk0, 1, &tx0.note_encs[0]), None);
        let _ = (alice_pk, bob_pk, carol_pk);
    }

    #[test]
    fn multi_output_tx_each_recipient_sees_only_own_note() {
        let (alice_sk, alice_pk) = party(1);
        let (_, bob_pk) = party(2);
        let (_, carol_pk) = party(3);

        let alice_coin   = coin(0xA1, 100, alice_pk);
        let bob_coin     = coin(0xB1,  40, bob_pk);
        let alice_change = coin(0xB2,  60, alice_pk);

        let (tx1, sk1, _) = make_tx(1, alice_sk, &[alice_coin],
            &[(bob_coin.clone(), bob_pk), (alice_change.clone(), alice_pk)]);

        // Index 0 → bob_coin, index 1 → alice_change.
        assert_eq!(decrypt_note(&sk1, 0, &tx1.note_encs[0]), Some(bob_coin));
        assert_eq!(decrypt_note(&sk1, 1, &tx1.note_encs[1]), Some(alice_change));
        // Wrong index gives None.
        assert_eq!(decrypt_note(&sk1, 1, &tx1.note_encs[0]), None);
        assert_eq!(decrypt_note(&sk1, 0, &tx1.note_encs[1]), None);
        let _ = carol_pk;
    }

    #[test]
    fn scan_entry_finds_recipient_but_not_outsiders() {
        let (alice_sk, alice_pk) = party(1);
        let (bob_sk, _bob_pk) = party(2);
        let (carol_sk, _carol_pk) = party(3);

        let (tx0, sk0, r0) = make_tx(0, GENESIS_SK,
            &[coin(0xA1, 100, genesis_pk())],
            &[(coin(0xA2, 100, alice_pk), alice_pk)]);
        let entry = enc(&tx0, &r0, sk0);

        assert_eq!(scan_entry(&alice_sk, &entry), Some(tx0.clone()));
        assert_eq!(scan_entry(&bob_sk,   &entry), None);
        assert_eq!(scan_entry(&carol_sk, &entry), None);
    }

    #[test]
    fn receipt_tracks_correct_received_slot() {
        let (alice_sk, alice_pk) = party(1);
        let (bob_sk, bob_pk) = party(2);
        let (_, carol_pk) = party(3);

        let alice_coin   = coin(0xA2, 100, alice_pk);
        let bob_coin     = coin(0xB1,  40, bob_pk);
        let alice_change = coin(0xB2,  60, alice_pk);
        let carol_coin   = coin(0xC1,  40, carol_pk);

        let (tx0, sk0, r0) = make_tx(0, GENESIS_SK, &[coin(0xA1, 100, genesis_pk())], &[(alice_coin.clone(), alice_pk)]);
        let (tx1, sk1, r1) = make_tx(1, alice_sk, &[alice_coin.clone()], &[(bob_coin.clone(), bob_pk), (alice_change, alice_pk)]);
        let (tx2, sk2, r2) = make_tx(2, bob_sk, &[bob_coin.clone()], &[(carol_coin, carol_pk)]);
        let entries = vec![enc(&tx0,&r0,sk0), enc(&tx1,&r1,sk1), enc(&tx2,&r2,sk2)];

        let cn_alice = alice_coin.commitment();
        let cn_bob   = bob_coin.commitment();

        let (alice_receipt, _) = make_receipt(alice_sk, cn_alice, &entries, 0).unwrap();
        assert_eq!(alice_receipt.received_at, 0);

        let (bob_receipt, _) = make_receipt(bob_sk, cn_bob, &entries, 1).unwrap();
        assert_eq!(bob_receipt.received_at, 1);
    }

    #[test]
    fn coin_proof_tracks_change_as_a_receipt() {
        let (alice_sk, alice_pk) = party(1);
        let (bob_sk, bob_pk) = party(2);

        let alice_coin   = coin(0xA2, 100, alice_pk);
        let bob_coin     = coin(0xB1,  40, bob_pk);
        let alice_change = coin(0xB2,  60, alice_pk);

        let (tx0, sk0, r0) = make_tx(0, GENESIS_SK, &[coin(0xA1, 100, genesis_pk())], &[(alice_coin.clone(), alice_pk)]);
        let (tx1, sk1, r1) = make_tx(1, alice_sk, &[alice_coin], &[(bob_coin, bob_pk), (alice_change.clone(), alice_pk)]);
        let entries = vec![enc(&tx0,&r0,sk0), enc(&tx1,&r1,sk1)];

        let cn_change = alice_change.commitment();
        let (receipt, _) = make_receipt(alice_sk, cn_change, &entries, 1).unwrap();
        assert_eq!(receipt.received_at, 1);
        let _ = bob_sk;
    }

    #[test]
    fn demo_chain_is_valid_end_to_end() {
        let (alice_sk, alice_pk) = party(1);
        let (bob_sk, bob_pk) = party(2);
        let (_, carol_pk) = party(3);

        let genesis_coin = coin(0xA1, 100, genesis_pk());
        let alice_coin   = coin(0xA2, 100, alice_pk);
        let bob_coin     = coin(0xB1,  40, bob_pk);
        let alice_change = coin(0xB2,  60, alice_pk);
        let carol_coin   = coin(0xC1,  40, carol_pk);

        let (tx0, sk0, r0) = make_tx(0, GENESIS_SK, &[genesis_coin.clone()], &[(alice_coin.clone(), alice_pk)]);
        let (tx1, sk1, r1) = make_tx(1, alice_sk, &[alice_coin.clone()], &[(bob_coin.clone(), bob_pk), (alice_change.clone(), alice_pk)]);
        let (tx2, sk2, r2) = make_tx(2, bob_sk, &[bob_coin.clone()], &[(carol_coin.clone(), carol_pk)]);
        let entries = vec![enc(&tx0,&r0,sk0), enc(&tx1,&r1,sk1), enc(&tx2,&r2,sk2)];

        let cn_genesis = genesis_coin.commitment();
        let cn_alice   = alice_coin.commitment();
        let cn_bob     = bob_coin.commitment();

        spend(GENESIS_SK, genesis_pk(), cn_genesis, &[], &tx0,
            &[genesis_coin], &[alice_coin.clone()], true, None).unwrap();

        let (alice_receipt, _) = make_receipt(alice_sk, cn_alice, &entries, 0).unwrap();
        spend(alice_sk, alice_pk, cn_alice, &entries[..1], &tx1,
            &[alice_coin.clone()], &[bob_coin.clone(), alice_change], false,
            Some(alice_receipt)).unwrap();

        let (bob_receipt, _) = make_receipt(bob_sk, cn_bob, &entries, 1).unwrap();
        spend(bob_sk, bob_pk, cn_bob, &entries[..2], &tx2,
            &[bob_coin.clone()], &[carol_coin], false,
            Some(bob_receipt)).unwrap();
    }

    #[test]
    fn rejects_wrong_secret_key() {
        let (alice_sk, alice_pk) = party(1);
        let genesis_coin = coin(0xA1, 100, genesis_pk());
        let alice_coin   = coin(0xA2, 100, alice_pk);
        let (tx0, _, _) = make_tx(0, GENESIS_SK, &[genesis_coin.clone()], &[(alice_coin.clone(), alice_pk)]);

        let err = spend(alice_sk, genesis_pk(), genesis_coin.commitment(), &[], &tx0,
            &[genesis_coin], &[alice_coin], true, None).unwrap_err();
        assert_eq!(err, "pk_P must be the public key for sk_P");
    }

    #[test]
    fn rejects_minting_without_the_genesis_key() {
        let (alice_sk, alice_pk) = party(1);
        let (_, bob_pk) = party(2);
        let alice_coin = coin(0xA1, 100, alice_pk);
        let bob_coin   = coin(0xB1, 100, bob_pk);
        let (tx0, _, _) = make_tx(0, alice_sk, &[alice_coin.clone()], &[(bob_coin.clone(), bob_pk)]);

        let err = spend(alice_sk, alice_pk, alice_coin.commitment(), &[], &tx0,
            &[alice_coin], &[bob_coin], true, None).unwrap_err();
        assert_eq!(err, "only the genesis key may mint without provenance");
    }

    #[test]
    fn rejects_building_a_receipt_for_a_coin_never_received() {
        let (alice_sk, alice_pk) = party(1);
        let (carol_sk, carol_pk) = party(3);

        let genesis_coin     = coin(0xA1, 100, genesis_pk());
        let alice_coin       = coin(0xA2, 100, alice_pk);
        let carol_fake_input = coin(0xC1, 100, carol_pk);

        let (tx0, sk0, r0) = make_tx(0, GENESIS_SK, &[genesis_coin], &[(alice_coin, alice_pk)]);
        let entries = vec![enc(&tx0,&r0,sk0)];
        let cn_carol = carol_fake_input.commitment();

        // Carol never actually received this coin — tx0 doesn't even decrypt
        // for her — so a receipt for it simply cannot be built.
        let err = make_receipt(carol_sk, cn_carol, &entries, 0).unwrap_err();
        assert_eq!(err, "entry_k does not decrypt for this owner");
    }

    #[test]
    fn rejects_receipt_when_creating_transaction_was_itself_a_double_spend() {
        let (alice_sk, alice_pk) = party(1);
        let (bob_sk, bob_pk) = party(2);
        let (carol_sk, carol_pk) = party(3);

        let genesis_coin = coin(0xA1, 100, genesis_pk());
        let alice_coin   = coin(0xA2, 100, alice_pk);
        let bob_coin     = coin(0xB1, 100, bob_pk);
        let carol_coin   = coin(0xC1, 100, carol_pk);

        let (tx0, sk0, r0) = make_tx(0, GENESIS_SK, &[genesis_coin], &[(alice_coin.clone(), alice_pk)]);
        // Alice double-spends alice_coin: tx1 and tx2 both claim to spend it
        // (same coin, same key ⇒ identical input_nullifier for both).
        let (tx1, sk1, r1) = make_tx(1, alice_sk, &[alice_coin.clone()], &[(bob_coin, bob_pk)]);
        let (tx2, sk2, r2) = make_tx(2, alice_sk, &[alice_coin], &[(carol_coin.clone(), carol_pk)]);
        let entries = vec![enc(&tx0,&r0,sk0), enc(&tx1,&r1,sk1), enc(&tx2,&r2,sk2)];

        let cn_carol = carol_coin.commitment();
        let err = make_receipt(carol_sk, cn_carol, &entries, 2).unwrap_err();
        assert_eq!(err, "parent transaction's nullifier was already present on the board — it was a double-spend");
        let _ = bob_sk;
    }

    #[test]
    fn rejects_double_spend() {
        let (alice_sk, alice_pk) = party(1);
        let (bob_sk, bob_pk) = party(2);
        let (_, carol_pk) = party(3);

        let genesis_coin = coin(0xA1, 100, genesis_pk());
        let alice_coin   = coin(0xA2, 100, alice_pk);
        let bob_coin     = coin(0xB1,  60, bob_pk);
        let alice_change = coin(0xB2,  40, alice_pk);
        let carol_coin   = coin(0xC1, 100, carol_pk);

        let cn_genesis = genesis_coin.commitment();
        let cn_alice   = alice_coin.commitment();

        let (tx0,  sk0, r0) = make_tx(0, GENESIS_SK, &[genesis_coin.clone()], &[(alice_coin.clone(), alice_pk)]);
        let (tx1,  sk1, r1) = make_tx(1, alice_sk, &[alice_coin.clone()], &[(bob_coin.clone(), bob_pk), (alice_change.clone(), alice_pk)]);
        let (tx1b, _,   _ ) = make_tx(2, alice_sk, &[alice_coin.clone()], &[(carol_coin.clone(), carol_pk)]);
        let entries = vec![enc(&tx0,&r0,sk0), enc(&tx1,&r1,sk1)];

        spend(GENESIS_SK, genesis_pk(), cn_genesis, &[], &tx0,
            &[genesis_coin], &[alice_coin.clone()], true, None).unwrap();

        // The receipt is built once — no per-slot re-extension needed before
        // either spend attempt below; freshness comes from the live
        // nullifier-accumulator check inside `spend`/`check_spend` instead.
        let (alice_receipt, _) = make_receipt(alice_sk, cn_alice, &entries, 0).unwrap();
        assert_eq!(alice_receipt.received_at, 0);

        spend(alice_sk, alice_pk, cn_alice, &entries[..1], &tx1,
            &[alice_coin.clone()], &[bob_coin, alice_change], false,
            Some(alice_receipt.clone())).unwrap();

        let err = spend(alice_sk, alice_pk, cn_alice, &entries, &tx1b,
            &[alice_coin], &[carol_coin], false,
            Some(alice_receipt)).unwrap_err();
        assert_eq!(err, "P must not have spent this coin before (double spend)");
        let _ = bob_sk;
    }

    #[test]
    fn rejects_spend_using_a_receipt_for_a_different_coin() {
        let (alice_sk, alice_pk) = party(1);
        let (bob_sk, bob_pk) = party(2);

        let genesis_coin = coin(0xA1, 100, genesis_pk());
        let alice_coin   = coin(0xA2, 100, alice_pk);
        let bob_coin     = coin(0xB1,  40, bob_pk);
        let alice_change = coin(0xB2,  60, alice_pk);

        let (tx0, sk0, r0) = make_tx(0, GENESIS_SK, &[genesis_coin], &[(alice_coin.clone(), alice_pk)]);
        let (tx1, sk1, r1) = make_tx(1, alice_sk, &[alice_coin.clone()], &[(bob_coin.clone(), bob_pk), (alice_change.clone(), alice_pk)]);
        let entries = vec![enc(&tx0,&r0,sk0), enc(&tx1,&r1,sk1)];

        let cn_alice  = alice_coin.commitment();
        let cn_change = alice_change.commitment();

        let (alice_receipt, _) = make_receipt(alice_sk, cn_alice, &entries, 0).unwrap();

        // tx2 legitimately spends alice_change, but we supply the receipt for
        // alice_coin — a different (and already-spent) commitment — instead.
        let payout = coin(0xC1, 60, bob_pk);
        let (tx2, _, _) = make_tx(2, alice_sk, &[alice_change.clone()], &[(payout.clone(), bob_pk)]);
        let err = spend(alice_sk, alice_pk, cn_change, &entries, &tx2,
            &[alice_change], &[payout], false, Some(alice_receipt)).unwrap_err();
        assert_eq!(err, "coin-proof tracks a different coin");
        let _ = (bob_sk, sk1, r1);
    }

    #[test]
    fn rejects_value_conservation_violation() {
        let (_, alice_pk) = party(1);
        let genesis_coin = coin(0xA1, 100, genesis_pk());
        let alice_coin   = coin(0xA2, 100, alice_pk);
        let extra_coin   = coin(0xA3,   1, alice_pk);

        let (tx0, _, _) = make_tx(0, GENESIS_SK, &[genesis_coin.clone()],
            &[(alice_coin.clone(), alice_pk), (extra_coin.clone(), alice_pk)]);

        let err = spend(GENESIS_SK, genesis_pk(), genesis_coin.commitment(), &[], &tx0,
            &[genesis_coin], &[alice_coin, extra_coin], true, None).unwrap_err();
        assert_eq!(err, "transaction violates value conservation: sum(inputs) must equal sum(outputs)");
    }

    #[test]
    fn nullifier_tree_insert_cost_does_not_grow_with_tree_size() {
        // Regression test for an earlier version with an O(n) `find_low_leaf_index`
        // (linear scan) and a `root()` that rehashed the whole tree from scratch:
        // that made `insert` cost scale with current tree size, turning `replay`
        // (which calls `insert` in a loop) into O(k²) — catastrophic once the
        // board has hundreds of thousands of entries. The incremental version
        // (BTreeMap index + cached per-level node hashes) should insert in O(1)
        // amortized, regardless of how many leaves already exist.
        //
        // Compares per-insert cost at two tree sizes 8x apart rather than
        // asserting an absolute wall-clock budget, so it isn't flaky across
        // debug/release builds or slower CI hardware — only relative growth
        // matters here.
        fn value(i: u32) -> [u8; 32] {
            let mut v = [0u8; 32];
            v[..4].copy_from_slice(&i.to_be_bytes());
            v[31] = 1; // keep every value > [0u8;32], avoiding the sentinel edge case
            v
        }

        let mut tree = NullifierTree::new();
        let batch = 500u32;
        let t = std::time::Instant::now();
        for i in 0..batch {
            tree.insert(value(i));
        }
        let small_per_insert = t.elapsed() / batch;

        // Grow the tree 8x larger, then time an equal-sized batch again.
        for i in batch..(batch * 8) {
            tree.insert(value(i));
        }
        let t = std::time::Instant::now();
        for i in (batch * 8)..(batch * 9) {
            tree.insert(value(i));
        }
        let large_per_insert = t.elapsed() / batch;

        assert!(
            large_per_insert.as_secs_f64() < small_per_insert.as_secs_f64() * 4.0 + 0.001,
            "insert cost grew from {small_per_insert:?}/insert at a small tree size to \
             {large_per_insert:?}/insert at 8x the size — looks non-incremental"
        );

        // Correctness alongside the scale check: a never-inserted value still
        // verifies as absent, and an inserted one no longer does.
        let mut absent = [0xAAu8; 32];
        absent[0] = 0xFF;
        let witness = tree.prove_non_membership(absent);
        assert!(verify_nonmembership(tree.root(), absent, &witness));

        let member = value(batch * 8);
        let w = tree.prove_non_membership(member);
        assert!(!verify_nonmembership(tree.root(), member, &w));
    }
}
