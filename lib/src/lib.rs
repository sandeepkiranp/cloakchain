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
    /// to chain-verify provenance in their IVC coin-proof.
    pub output_commitments: Vec<[u8; 32]>,
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
    /// The nullifier to watch for across prior slots (= H(parent_input_commitment || sk_parent_spender)).
    /// Known upfront before bootstrap starts; carried through the IVC unchanged.
    pub parent_nullifier: [u8; 32],
    /// Set to true if `parent_nullifier` was found (as a substring) in any prior slot's entry bytes.
    /// If true at the receipt slot, the creating transaction was a double-spend → receipt invalid.
    pub parent_nullifier_seen: bool,
}

impl CoinProofPublicValues {
    pub fn encode(&self) -> Vec<u8> {
        bincode::serialize(self).expect("CoinProofPublicValues is always serializable")
    }
}

/// What justifies a coin-proof step.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoinProofJustification {
    /// `slot == 0`: no recursive inner proof to verify.
    Base,
    /// `slot > 0`: extends the chain from `inner_public_values`.
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
    owner_sk: [u8; 32],
    coin_commitment: [u8; 32],
    entry_k: BoardEntry,
    slot: usize,
    append_path: Vec<[u8; 32]>,
    inner: Option<CoinProofPublicValues>,
    // H(parent_input_commitment || sk_parent_spender) — the nullifier of the
    // transaction that CREATED the tracked coin. Known upfront; checked via
    // substring search in every prior slot's raw entry bytes.
    parent_nullifier: [u8; 32],
    // H(coin_commitment || sk_owner) — the owner's own spending nullifier.
    // If found in a prior slot, the coin was already spent (double-spend).
    own_nullifier: [u8; 32],
) -> Result<(CoinProofPublicValues, CoinProofJustification), &'static str> {
    let owner_pk = derive_pk(&owner_sk);
    let leaf_k = merkle_leaf(slot, &entry_k);
    let board_root = compute_root_from_path(leaf_k, slot, &append_path);

    let (prev_received_at, prev_spent, prev_parent_nullifier_seen, justification) = if slot == 0 {
        (None, false, false, CoinProofJustification::Base)
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
        if inner.parent_nullifier != parent_nullifier {
            return Err("inner coin-proof tracks a different parent nullifier");
        }
        if inner.board_size != slot {
            return Err("inner coin-proof must cover exactly the prefix before this slot");
        }
        let old_root = compute_root_from_path([0u8; 32], slot, &append_path);
        if inner.board_root != old_root {
            return Err("inner coin-proof's board root does not match this prefix");
        }
        let (pra, ps, pns) = (inner.received_at, inner.spent, inner.parent_nullifier_seen);
        (pra, ps, pns, CoinProofJustification::Step { inner_public_values: inner })
    };

    let raw = bincode::serialize(&entry_k).unwrap_or_default();

    let mut received_at = prev_received_at;

    if let Some(tx) = scan_entry(&owner_sk, &entry_k) {
        if tx.receives_coin(&coin_commitment) && received_at.is_none() {
            if !prev_parent_nullifier_seen {
                received_at = Some(slot as u64);
            }
        }
    }

    // Only scan for parent_nullifier while the coin has not yet been received.
    // Once received_at is set, further appearances of parent_nullifier on the
    // board are irrelevant and must not be able to retroactively invalidate it.
    let parent_nullifier_seen = prev_parent_nullifier_seen
        || (prev_received_at.is_none()
            && raw.windows(32).any(|w| w == parent_nullifier));
    let spent = prev_spent
        || raw.windows(32).any(|w| w == own_nullifier);

    Ok((
        CoinProofPublicValues {
            vkey,
            owner_pk,
            coin_commitment,
            board_root,
            board_size: slot + 1,
            received_at,
            spent,
            parent_nullifier,
            parent_nullifier_seen,
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
        if prior_entries.is_empty() {
            // Empty board → own_nullifier cannot exist anywhere → double-spend
            // is trivially impossible. No coin-proof needed.
        } else {
            // Prior entries exist → require a coin-proof so cp.spent (set by
            // the IVC's per-slot own-nullifier search) gives us O(1) double-spend
            // detection without scanning all entries again here.
            let cp = coin_proof.ok_or("genesis at a non-empty board requires a coin-proof")?;
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
            if cp.spent {
                return Err("P must not have spent this coin before (double spend)");
            }
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
        // Double-spend check: the IVC encoded cp.spent via per-slot own-nullifier
        // search → O(1) here, no redundant O(n) scan.
        if cp.spent {
            return Err("P must not have spent this coin before (double spend)");
        }
    }

    Ok(ValidPublicValues { vkey, board_root: anchor, output_commitments: tx_star.output_commitments.clone() })
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

    fn coin_proof_chain(
        owner_sk: [u8; 32],
        coin_commitment: [u8; 32],
        entries: &[BoardEntry],
        parent_nullifier: [u8; 32],
    ) -> Vec<CoinProofPublicValues> {
        let own_nullifier = {
            let mut h = Sha256::new();
            h.update(coin_commitment); h.update(owner_sk);
            let mut out = [0u8; 32]; out.copy_from_slice(&h.finalize()); out
        };
        let mut out = Vec::new();
        let mut inner: Option<CoinProofPublicValues> = None;
        for k in 0..entries.len() {
            let ap = append_proof_for(&entries[..=k]);
            let (pv, _) = check_coin_proof_step(
                TEST_COIN_PROOF_VKEY, owner_sk, coin_commitment,
                entries[k].clone(), k, ap, inner.clone(),
                parent_nullifier, own_nullifier,
            ).unwrap();
            inner = Some(pv.clone());
            out.push(pv);
        }
        out
    }

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
    fn coin_proof_tracks_receipt_and_spend_for_demo_chain() {
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

        let alice_cp = coin_proof_chain(alice_sk, cn_alice, &entries[..1], [0u8;32]);
        assert_eq!(alice_cp[0].received_at, Some(0));
        assert!(!alice_cp[0].spent);

        let bob_cp = coin_proof_chain(bob_sk, cn_bob, &entries[..2], [0u8;32]);
        assert_eq!(bob_cp[0].received_at, None);
        assert_eq!(bob_cp[1].received_at, Some(1));
        assert!(!bob_cp[1].spent);
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
        let cp = coin_proof_chain(alice_sk, cn_change, &entries, [0u8;32]);
        assert_eq!(cp[0].received_at, None);
        assert_eq!(cp[1].received_at, Some(1));
        assert!(!cp[1].spent);
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

        let alice_cp = coin_proof_chain(alice_sk, cn_alice, &entries[..1], [0u8;32]);
        spend(alice_sk, alice_pk, cn_alice, &entries[..1], &tx1,
            &[alice_coin.clone()], &[bob_coin.clone(), alice_change], false,
            Some(alice_cp[0].clone())).unwrap();

        let bob_cp = coin_proof_chain(bob_sk, cn_bob, &entries[..2], [0u8;32]);
        spend(bob_sk, bob_pk, cn_bob, &entries[..2], &tx2,
            &[bob_coin.clone()], &[carol_coin], false,
            Some(bob_cp[1].clone())).unwrap();
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
    fn rejects_spending_a_coin_one_never_received() {
        let (alice_sk, alice_pk) = party(1);
        let (carol_sk, carol_pk) = party(3);

        let genesis_coin     = coin(0xA1, 100, genesis_pk());
        let alice_coin       = coin(0xA2, 100, alice_pk);
        let carol_fake_input = coin(0xC1, 100, carol_pk);
        let carol_fake_out   = coin(0xC2, 100, alice_pk);

        let (tx0,     sk0, r0) = make_tx(0, GENESIS_SK, &[genesis_coin], &[(alice_coin, alice_pk)]);
        let (tx_fake, _,   _ ) = make_tx(1, carol_sk, &[carol_fake_input.clone()], &[(carol_fake_out.clone(), alice_pk)]);
        let entries = vec![enc(&tx0,&r0,sk0)];
        let cn_carol = carol_fake_input.commitment();

        let carol_cp = coin_proof_chain(carol_sk, cn_carol, &entries, [0u8;32]);
        assert_eq!(carol_cp[0].received_at, None);

        let err = spend(carol_sk, carol_pk, cn_carol, &entries, &tx_fake,
            &[carol_fake_input], &[carol_fake_out], false,
            Some(carol_cp[0].clone())).unwrap_err();
        assert_eq!(err, "P must have received this coin at some prior slot");
        let _ = alice_sk;
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

        let alice_cp = coin_proof_chain(alice_sk, cn_alice, &entries, [0u8;32]);
        assert_eq!(alice_cp[0].received_at, Some(0));
        assert!(alice_cp[1].spent);

        spend(alice_sk, alice_pk, cn_alice, &entries[..1], &tx1,
            &[alice_coin.clone()], &[bob_coin, alice_change], false,
            Some(alice_cp[0].clone())).unwrap();

        let err = spend(alice_sk, alice_pk, cn_alice, &entries, &tx1b,
            &[alice_coin], &[carol_coin], false,
            Some(alice_cp[1].clone())).unwrap_err();
        assert_eq!(err, "P must not have spent this coin before (double spend)");
        let _ = bob_sk;
    }

    #[test]
    fn rejects_tampered_board_entry() {
        let (alice_sk, alice_pk) = party(1);
        let (bob_sk, bob_pk) = party(2);

        let genesis_coin = coin(0xA1, 100, genesis_pk());
        let alice_coin   = coin(0xA2, 100, alice_pk);
        let bob_coin     = coin(0xB1, 100, bob_pk);

        let (tx0_real, sk0r, r0r) = make_tx(0, GENESIS_SK, &[genesis_coin.clone()], &[(alice_coin.clone(), alice_pk)]);
        let (tx1,      _,    r1 ) = make_tx(1, alice_sk, &[alice_coin.clone()], &[(bob_coin.clone(), bob_pk)]);
        let entries_real = vec![enc(&tx0_real,&r0r,sk0r)];
        let cn_alice = alice_coin.commitment();
        let alice_cp = coin_proof_chain(alice_sk, cn_alice, &entries_real, [0u8;32]);

        let fake_coin = coin(0xB3, 100, alice_pk);
        let (tx0_fake, skf, rf) = make_tx(0, GENESIS_SK, &[genesis_coin], &[(fake_coin, alice_pk)]);
        let entries_tampered = vec![enc(&tx0_fake,&rf,skf)];

        let err = spend(alice_sk, alice_pk, cn_alice, &entries_tampered, &tx1,
            &[alice_coin], &[bob_coin], false,
            Some(alice_cp[0].clone())).unwrap_err();
        assert_eq!(err, "coin-proof's board root does not match the board prefix");
        let _ = (bob_sk, r1);
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
}
