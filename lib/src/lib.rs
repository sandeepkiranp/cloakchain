use std::collections::{BTreeMap, HashMap};

use ark_crypto_primitives::sponge::{
    poseidon::PoseidonSponge, CryptographicSponge, FieldBasedCryptographicSponge,
};
use ark_ec::{AffineRepr, CurveGroup, PrimeGroup};
use ark_ff::{BigInteger, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use serde::{Deserialize, Serialize};

/// Bridges arkworks' `CanonicalSerialize`/`CanonicalDeserialize` (its own
/// SNARK-friendly encoding) to `serde`, via `#[serde(with = "field_serde")]`
/// on any field/point-typed struct field — arkworks types don't implement
/// `serde::Serialize` directly (no serde feature exists for these crates).
mod field_serde {
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S, T>(value: &T, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
        T: CanonicalSerialize,
    {
        let mut bytes = Vec::new();
        value
            .serialize_compressed(&mut bytes)
            .map_err(serde::ser::Error::custom)?;
        bytes.serialize(serializer)
    }

    pub fn deserialize<'de, D, T>(deserializer: D) -> Result<T, D::Error>
    where
        D: Deserializer<'de>,
        T: CanonicalDeserialize,
    {
        let bytes = Vec::<u8>::deserialize(deserializer)?;
        T::deserialize_compressed(&bytes[..]).map_err(serde::de::Error::custom)
    }
}
use sha2::{Digest, Sha256};
use x25519_dalek::{PublicKey as X25519PublicKey, StaticSecret as X25519Secret};

pub mod poseidon_params;

/// The canonical data-model field: MNT4-753's scalar field. Chosen to match
/// the `SpendCircuit`'s constraint field (Phase 2/3) — Groth16 R1CS
/// constraints for a circuit proved over curve E live over `E::ScalarField`.
pub type Fr = ark_mnt4_753::Fr;

/// The coin-ownership keypair lives on **MNT6-753's** G1 group, not
/// MNT4-753's own. This is deliberate, not arbitrary: MNT6-753's base field
/// equals MNT4-753's scalar field (`Fr`, above) — that's the defining
/// property of the MNT4/6-753 curve cycle. So `OwnerPk`'s point coordinates
/// are already native `Fr` elements, hashable into an `Fr`-Poseidon sponge
/// with no foreign-field wrapping. The scalar `OwnerScalar` is naturally an
/// element of MNT6-753's own scalar field (== MNT4-753's *base* field) —
/// genuinely a different field from `Fr`, so it's folded through
/// [`fold_owner_scalar`] (bit decomposition) wherever it needs to enter an
/// `Fr`-native hash, rather than absorbed as a native field element.
/// This is the same non-native-scalar/native-point-coordinate split that
/// `Groth16VerifierGadget`'s own recursive verification relies on for public
/// inputs crossing the cycle (see the MNT-native port plan).
pub type OwnerPk = ark_mnt6_753::G1Affine;
pub type OwnerScalar = ark_mnt6_753::Fr;

fn poseidon_sponge() -> PoseidonSponge<Fr> {
    PoseidonSponge::new(&poseidon_params::mnt4_753_fr_poseidon_config())
}

/// General-purpose Poseidon hash of any number of native `Fr` elements.
pub fn poseidon_hash(inputs: &[Fr]) -> Fr {
    let mut sponge = poseidon_sponge();
    sponge.absorb(&inputs.to_vec());
    sponge.squeeze_native_field_elements(1)[0]
}

/// Fold arbitrary bytes into `Fr` elements, 31 bytes at a time (safely under
/// any field modulus this codebase targets) via `from_le_bytes_mod_order`,
/// then Poseidon-hash the resulting vector. Used for data that is inherently
/// byte-oriented (ciphertexts, X25519 keys) or foreign-field (an
/// `OwnerScalar`, serialized canonically) rather than a native `Fr` value.
pub fn poseidon_hash_bytes(bytes: &[u8]) -> Fr {
    if bytes.is_empty() {
        return poseidon_hash(&[Fr::from(0u64)]);
    }
    let elems: Vec<Fr> = bytes
        .chunks(31)
        .map(Fr::from_le_bytes_mod_order)
        .collect();
    poseidon_hash(&elems)
}

/// Fold a foreign-field scalar (an `OwnerScalar`, genuinely a different
/// field from `Fr` — see the `OwnerScalar` doc comment) into a native `Fr`
/// value for Poseidon hashing: split the scalar's canonical little-endian
/// bit decomposition into 248-bit chunks (safely below `Fr`'s capacity),
/// interpret each chunk as a little-endian integer, then Poseidon-hash the
/// resulting `Fr` chunks.
///
/// Deliberately defined directly in terms of *bits*, not a byte-serialization
/// format (`ark_serialize`'s or otherwise) — the in-circuit gadget needs to
/// reproduce this exactly, and it already has to witness `sk_p` as bits for
/// the native scalar-mult gadget (`pk_p = sk_p · G`); reusing that same bit
/// vector for folding avoids depending on a serialization library's byte
/// layout matching a hand-written circuit gadget bit-for-bit.
pub fn fold_owner_scalar(sk: &OwnerScalar) -> Fr {
    fold_bits_le(&sk.into_bigint().to_bits_le())
}

fn fold_bits_le(bits: &[bool]) -> Fr {
    let chunks: Vec<Fr> = bits
        .chunks(248)
        .map(|chunk| {
            let mut acc = Fr::from(0u64);
            let mut place = Fr::from(1u64);
            for &b in chunk {
                if b {
                    acc += place;
                }
                place *= Fr::from(2u64);
            }
            acc
        })
        .collect();
    poseidon_hash(&chunks)
}

/// Extract `pk`'s two coordinates as `Fr` elements — exposed (not just used
/// internally by [`Coin::commitment`]) so circuit crates can build the exact
/// same public-input layout without duplicating this logic.
pub fn owner_pk_to_field_pair(pk: &OwnerPk) -> (Fr, Fr) {
    // `pk`'s coordinates live in MNT6-753's base field, i.e. MNT4-753's
    // scalar field `Fr` — see the `OwnerPk` doc comment above. Extract them
    // directly, no re-encoding needed. The point at infinity (only ever
    // relevant for a malformed/zero key) maps to (0, 0), which is never a
    // valid curve point's coordinates, so it can't collide with a real key.
    match pk.xy() {
        Some((x, y)) => (x, y),
        None => (Fr::from(0u64), Fr::from(0u64)),
    }
}

/// Genesis owner scalar. `0` would give the identity point (an invalid,
/// non-hashable public key), unlike X25519 where clamping avoided that
/// automatically — so genesis uses scalar `1` instead: `genesis_pk` is
/// simply the group generator, a fixed and well-known point.
pub fn genesis_sk() -> OwnerScalar {
    OwnerScalar::from(1u64)
}

pub fn genesis_pk() -> OwnerPk {
    derive_owner_pk(&genesis_sk())
}

/// Native coin-ownership key derivation: `pk = sk * G`, on MNT6-753's G1 —
/// see the `OwnerPk`/`OwnerScalar` doc comments for why this curve.
pub fn derive_owner_pk(sk: &OwnerScalar) -> OwnerPk {
    (ark_mnt6_753::G1Projective::generator() * sk).into_affine()
}

/// A coin: value `v`, owner public key `pk`, plus masking randomness `r`.
/// Commitment cn = Poseidon(v, r, pk.x, pk.y) — binds the coin to its
/// intended owner, so a coin created for Alice cannot be claimed by Bob even
/// if he knows the value/rand (analogous to how Zcash embeds the recipient
/// address in cm).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize)]
pub struct Coin {
    pub value: u64,
    #[serde(with = "field_serde")]
    pub rand: Fr,
    #[serde(with = "field_serde")]
    pub owner_pk: OwnerPk,
}

impl Coin {
    pub fn commitment(&self) -> Fr {
        let (px, py) = owner_pk_to_field_pair(&self.owner_pk);
        poseidon_hash(&[Fr::from(self.value), self.rand, px, py])
    }
}

/// A generalised transaction: `S` spends one or more input coins and creates
/// one or more output coins for (potentially different) recipients.
///
/// Only **commitments** appear in the transaction body. Sender and recipient
/// identities are NOT stored — the sender is proven via the nullifier
/// (published in the clear on `BoardEntry.nullifier`, not duplicated here —
/// no circuit or wallet workflow ever reads it back out of the decrypted
/// transaction, so there's nothing to gain by encrypting a second copy) and
/// recipient ownership is encoded inside each coin commitment
/// (`Poseidon(v, r, pk)`). Each output's coin data is encrypted in
/// `note_encs[i]` per recipient.
///
/// `spend_proof` is attached after proving and the whole struct re-encrypted.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Transaction {
    pub id: u64,
    /// Commitments to the coins being spent.
    #[serde(with = "field_serde")]
    pub input_commitments: Vec<Fr>,
    /// Commitments to the new coins (same index as note_encs).
    #[serde(with = "field_serde")]
    pub output_commitments: Vec<Fr>,
    /// `note_encs[i]` = `encrypt(output_coin_i, pair_key(sender, recipient_i))`.
    pub note_encs: Vec<Vec<u8>>,
    pub spend_proof: Vec<u8>,
}

impl Transaction {
    /// `cn` was received in this tx if it is among the output commitments.
    /// Recipient ownership is already encoded inside the commitment itself.
    pub fn receives_coin(&self, cn: &Fr) -> bool {
        self.output_commitments.contains(cn)
    }

    /// `cn` was spent as an input in this tx.
    pub fn spends_coin(&self, cn: &Fr) -> bool {
        self.input_commitments.contains(cn)
    }
}

// ---- X25519 sender-anonymous encryption ------------------------------------
//
// Unchanged from the SHA256/SP1 design and entirely off-circuit: this is
// *wallet-side* bookkeeping (delivering a coin's opening — value/rand — to
// its recipient), not something any circuit needs to prove anymore. The
// port's "move decryption off-circuit" decision made `BoardEntry`'s
// `output_commitments` public instead (see below), so `check_coin_receipt`
// no longer calls any of this. X25519 keys are now entirely separate from
// coin-ownership keys (`OwnerScalar`/`OwnerPk`) — each party holds both.
//
// Each transaction is encrypted with a random session key. The session key is
// wrapped separately for each recipient using X25519 ECDH — only the holder of
// the recipient's private key can recover it. The sender is never identified:
// the recipient only uses their own sk and the ephemeral public key `ek_pk`.
//
// Note data (coin value/rand) for output i is encrypted with a key derived
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

/// Derive a party's X25519 encryption public key from their encryption
/// secret key — a separate keyspace from coin ownership (`OwnerScalar`/
/// `OwnerPk`), see the `OwnerPk` doc comment above.
pub fn derive_enc_pk(enc_sk: &[u8; 32]) -> [u8; 32] {
    *X25519PublicKey::from(&X25519Secret::from(*enc_sk)).as_bytes()
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
/// X25519 public key `ek_pk` (also looks like 32 random bytes on Curve25519),
/// plus the **public** commitments this entry's transaction creates.
///
/// `output_commitments` is public (not only inside `ciphertext`) so that
/// `check_coin_receipt` can prove `coin_commitment ∈
/// entry.output_commitments` directly, without decrypting anything
/// in-circuit — see the MNT-native port plan's "move decryption off-circuit"
/// decision. This leaks nothing beyond what a hiding commitment already
/// leaks (nothing about value/rand/owner), the same trade-off Zcash's
/// public note-commitment tree makes.
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
    /// `tx.input_nullifier` — looks random, used by the nullifier accumulator.
    #[serde(with = "field_serde")]
    pub nullifier: Fr,
    /// `tx.output_commitments` — public, see the struct doc comment above.
    #[serde(with = "field_serde")]
    pub output_commitments: Vec<Fr>,
}

/// Encrypt `tx` for the given `recipient_pks` (X25519 encryption keys — a
/// separate keyspace from coin-ownership `OwnerPk`s) and `session_key`. Pass
/// the same `session_key` when re-encrypting after attaching a spend proof —
/// the deterministic `ek_sk` ensures `ek_pk` and `key_encs` are unchanged.
pub fn encrypt_tx(
    tx: &Transaction,
    sender_sk: &OwnerScalar,
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

    // The double-spend nullifier: Poseidon(primary_input_commitment,
    // sk_spender-folded) — published here in the clear (this is the only
    // place it's ever produced; `Transaction` itself no longer carries a
    // copy, see its doc comment).
    let nullifier = poseidon_hash(&[tx.input_commitments[0], fold_owner_scalar(sender_sk)]);

    BoardEntry {
        ciphertext,
        ek_pk,
        key_encs,
        nullifier,
        output_commitments: tx.output_commitments.clone(),
    }
}

/// Decrypt a board entry using the recipient's X25519 private key.
/// Tries each `key_enc` — the one that yields a valid session key will decrypt
/// the ciphertext successfully. No sender identity is needed or revealed.
/// Purely a wallet convenience now (see the module doc comment) — no circuit
/// depends on this succeeding.
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
// entries). Unfilled leaf positions are treated as the zero field element.
// This lets each spend/receipt proof update the root in O(TREE_DEPTH) = O(1)
// time using a single Merkle inclusion (append) proof, rather than O(n) by
// recomputing the root from all prior entries.
//
// Key property: if `append_path` is the inclusion proof for slot k in the
// fixed-depth tree containing entries[0..=k], then:
//
//   compute_root_from_path(Fr::from(0), k, &append_path)  == root_{k-1}  (old root)
//   compute_root_from_path(merkle_leaf(k, e_k), k, &append_path) == root_k (new root)
//
// Only the leaf value changes between the two computations; the path is the
// same. This lets a spend proof verify consistency with the prior root AND
// compute the new root in a single O(TREE_DEPTH) pass.

/// Maximum tree depth. Supports up to 2^32 ≈ 4 billion board entries.
pub const TREE_DEPTH: usize = 32;

/// Leaf hash = Poseidon(slot, fold(ciphertext), fold(ek_pk), fold(key_encs),
/// nullifier, Poseidon(output_commitments)). Including the slot index
/// prevents permuting entries while keeping a valid root.
pub fn merkle_leaf(slot: usize, entry: &BoardEntry) -> Fr {
    merkle_leaf_from_commitment(slot, entry.nullifier, &entry.output_commitments, entry_ciphertext_commitment(entry))
}

/// Fold a board entry's off-circuit-only fields (`ciphertext`, `ek_pk`,
/// `key_encs` — all variable-length, X25519/wallet-scanning data with no
/// cryptographic role in any circuit's checks, see the `BoardEntry` doc
/// comment) into a single opaque `Fr` value, host-side only. No circuit ever
/// re-derives this from the raw bytes — R1CS circuit shape is fixed, and
/// these fields are unbounded-length — it only needs to be *some* value
/// bound into the leaf hash for board integrity, auditable off-circuit by
/// anyone checking the raw posted bytes against a board root.
pub fn entry_ciphertext_commitment(entry: &BoardEntry) -> Fr {
    let key_encs_bytes: Vec<u8> = entry.key_encs.iter().flatten().copied().collect();
    poseidon_hash(&[
        poseidon_hash_bytes(&entry.ciphertext),
        poseidon_hash_bytes(&entry.ek_pk),
        poseidon_hash_bytes(&key_encs_bytes),
    ])
}

/// The fixed-size core of `merkle_leaf` — mirrorable in-circuit, since every
/// input is either a native `Fr` value or (for `ciphertext_commitment`) an
/// opaque witness the circuit never expands.
pub fn merkle_leaf_from_commitment(
    slot: usize,
    nullifier: Fr,
    output_commitments: &[Fr],
    ciphertext_commitment: Fr,
) -> Fr {
    poseidon_hash(&[
        Fr::from(slot as u64),
        ciphertext_commitment,
        nullifier,
        poseidon_hash(output_commitments),
    ])
}

fn merkle_combine(l: &Fr, r: &Fr) -> Fr {
    poseidon_hash(&[*l, *r])
}

/// Precomputed hashes of empty subtrees at each depth.
/// `zero_hashes()[d]` = root of a complete subtree of depth `d` with all
/// leaves equal to the zero field element. Computed once and cached —
/// `NullifierTree::insert` calls this on every leaf update, and recomputing
/// 32 hashes from scratch each time (rather than once, ever) was the
/// dominant cost at scale.
fn zero_hashes() -> &'static [Fr] {
    static ZERO_HASHES: std::sync::OnceLock<Vec<Fr>> = std::sync::OnceLock::new();
    ZERO_HASHES.get_or_init(|| {
        let mut out = vec![Fr::from(0u64)]; // depth 0: the zero leaf itself
        for _ in 0..TREE_DEPTH {
            let prev = *out.last().unwrap();
            out.push(merkle_combine(&prev, &prev));
        }
        out
    })
}

/// Root of the empty fixed-depth tree (all leaves = 0).
pub fn empty_root() -> Fr {
    zero_hashes()[TREE_DEPTH]
}

/// Walk the path from `leaf` at `slot` to the root. Used by
/// `merkle_root_of`, `check_coin_receipt`, and `check_spend`.
pub fn compute_root_from_path(leaf: Fr, slot: usize, path: &[Fr]) -> Fr {
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
/// slots 0..T and the zero element at all other leaf positions.
pub fn merkle_root_of(entries: &[BoardEntry]) -> Fr {
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
fn merkle_path_for_index(leaf_hashes: &[Fr], target_idx: usize) -> Vec<Fr> {
    let zeros = zero_hashes();
    let mut path = Vec::with_capacity(TREE_DEPTH);
    let mut level: Vec<Fr> = leaf_hashes.to_vec();
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
pub fn append_proof_for(entries: &[BoardEntry]) -> Vec<Fr> {
    let slot = entries.len() - 1;
    let hashes: Vec<Fr> = entries.iter().enumerate().map(|(i, e)| merkle_leaf(i, e)).collect();
    merkle_path_for_index(&hashes, slot)
}

/// Append-path for the *next*, as-yet-unfilled slot after `entries` — used by
/// `check_spend` to prove the board state immediately before `tx_star` is
/// posted, without needing the entire prior board history as a witness (only
/// its leaf hashes, derived here from the entries the caller already has).
pub fn append_path_for_next(entries: &[BoardEntry]) -> Vec<Fr> {
    let hashes: Vec<Fr> = entries.iter().enumerate().map(|(i, e)| merkle_leaf(i, e)).collect();
    merkle_path_for_index(&hashes, entries.len())
}

/// Verify that `entry` is the genuine content of `slot` in a fixed-depth tree
/// with the given `root`.
pub fn merkle_verify(root: Fr, slot: usize, entry: &BoardEntry, proof: &[Fr]) -> bool {
    compute_root_from_path(merkle_leaf(slot, entry), slot, proof) == root
}

// ---- Nullifier accumulator (indexed Merkle tree) --------------------------
//
// Double-spend detection does not require walking every board slot. Every
// nullifier ever published (`BoardEntry.nullifier`, already public) is
// inserted into a single indexed Merkle tree — a sorted linked list of
// leaves, each storing `(value, next_value, next_index)`. A single Merkle
// path to a leaf whose `value < target < next_value` proves `target` is
// absent from the *entire* set the tree's root represents, in one
// O(TREE_DEPTH) proof instead of an O(slots) scan. Reuses the same Poseidon
// combine/path primitives as the board tree above.
//
// Ordering is over `Fr`'s canonical integer representative (`Fr: Ord`,
// comparing values in `0..p`) rather than byte-lexicographic order — any
// consistent total order works for the accumulator's soundness, and
// comparisons on `Fr` are confirmed safe to do in-circuit on this stack
// (unlike gnark/Sunspot, which the `sunspot_groth16_experiment` finding
// showed breaks on Field ordering comparisons — arkworks does not share that
// bug).

/// One leaf of the indexed nullifier tree.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize)]
pub struct IndexedLeaf {
    #[serde(with = "field_serde")]
    pub value: Fr,
    #[serde(with = "field_serde")]
    pub next_value: Fr,
    pub next_index: u64,
}

/// Sentinel "infinity" value: the field's largest canonical representative
/// (`p - 1`). No real nullifier will ever equal this except by a
/// negligible-probability Poseidon collision, so it safely upper-bounds
/// every real value.
fn max_nullifier() -> Fr {
    -Fr::from(1u64)
}

impl IndexedLeaf {
    fn hash(&self) -> Fr {
        poseidon_hash(&[self.value, self.next_value, Fr::from(self.next_index)])
    }
}

/// A non-membership proof: the "low" leaf whose `value < target < next_value`
/// — impossible to construct unless `target` is genuinely absent — plus its
/// Merkle inclusion path. (If `target` happens to already be a member, the
/// natural low leaf instead has `next_value == target`, which fails the
/// strict `target < next_value` check in `verify_nonmembership` below.)
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize)]
pub struct NonMembershipWitness {
    pub low_leaf: IndexedLeaf,
    pub low_leaf_index: u64,
    #[serde(with = "field_serde")]
    pub sibling_path: Vec<Fr>,
}

/// Verify a non-membership witness against `root`: `target` cannot be a
/// member if some leaf's `value < target < next_value` genuinely Merkle-opens
/// to `root` — no member could exist strictly between two adjacent leaves.
pub fn verify_nonmembership(root: Fr, target: Fr, witness: &NonMembershipWitness) -> bool {
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
    index_of: BTreeMap<Fr, usize>,
    /// `nodes[d]` holds the hash of every *filled* node at depth d (0 =
    /// leaves, `TREE_DEPTH` = root), keyed by its position at that depth.
    /// A missing entry means "unfilled" — use the precomputed zero-subtree
    /// hash for that depth instead (see `zero_hashes`).
    nodes: Vec<HashMap<usize, Fr>>,
}

impl NullifierTree {
    /// A fresh tree, seeded with the single "everything" sentinel leaf.
    pub fn new() -> Self {
        let sentinel = IndexedLeaf { value: Fr::from(0u64), next_value: max_nullifier(), next_index: 0 };
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
    fn set_leaf(&mut self, idx: usize, hash: Fr) {
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

    pub fn root(&self) -> Fr {
        self.nodes[TREE_DEPTH].get(&0).copied().unwrap_or_else(|| zero_hashes()[TREE_DEPTH])
    }

    pub fn contains(&self, value: Fr) -> bool {
        self.index_of.contains_key(&value)
    }

    /// The leaf whose `value < target <= next_value` — for a genuine
    /// non-member this is the unique insertion point (`target < next_value`
    /// strictly); for an existing member it's that value's predecessor
    /// (`next_value == target`), which correctly yields a witness that
    /// `verify_nonmembership` will reject rather than one that panics here.
    /// O(log n) via `index_of` instead of scanning every leaf.
    fn find_low_leaf_index(&self, target: Fr) -> usize {
        *self.index_of.range(..target).next_back().map(|(_, idx)| idx)
            .expect("no matching leaf — target is 0 or tree invariant violated")
    }

    /// Insert `value` (a no-op if already present) and return the new root.
    /// O(log n): one BTreeMap lookup plus two O(TREE_DEPTH) path updates.
    pub fn insert(&mut self, value: Fr) -> Fr {
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
    fn path_for(&self, idx: usize) -> Vec<Fr> {
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
    pub fn prove_non_membership(&self, target: Fr) -> NonMembershipWitness {
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
    pub fn replay(inserted: &[Fr], count: usize) -> Self {
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
/// recipient's coin-receipt proof verifies this proof recursively (Phase 3)
/// and checks that their `coin_commitment` is listed here — establishing a
/// cryptographic chain of custody from the creating spend proof all the way
/// to the final spend proof.
///
/// The spender's public key is intentionally NOT included — the proof proves
/// "someone with the right key spent this coin" without revealing who. The
/// nullifier (`BoardEntry.nullifier`) is public, but reveals nothing about
/// spender identity: it's a one-way hash, useful only for equality-checking
/// against future spends, not for recovering who produced it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ValidPublicValues {
    pub vkey: [u32; 8],
    #[serde(with = "field_serde")]
    pub board_root: Fr,
    /// The output coin commitments created by this spend — used by recipients
    /// to chain-verify provenance in their receipt proof.
    #[serde(with = "field_serde")]
    pub output_commitments: Vec<Fr>,
    /// The nullifier-accumulator root as of just before this spend (i.e. not
    /// yet including this spend's own `input_nullifier`) — lets downstream
    /// verifiers independently confirm it against their own rebuilt tree, the
    /// same way `board_root` already lets them confirm board state.
    #[serde(with = "field_serde")]
    pub nullifier_root: Fr,
}

impl ValidPublicValues {
    pub fn encode(&self) -> Vec<u8> {
        bincode::serialize(self).expect("ValidPublicValues is always serializable")
    }
}

// ---- Coin receipt ----------------------------------------------------------
//
// A coin's receipt is a single proof, built once when the coin is first
// discovered. It proves:
//
//   - `entry_k` (the transaction that created this coin) really is included
//     in the board at `received_at`, via one Merkle append-path.
//   - `coin_commitment` is among `entry_k.output_commitments` — a direct,
//     public equality/membership check now that `BoardEntry` publishes its
//     output commitments (see the port's "move decryption off-circuit"
//     decision) — no in-circuit decryption needed at all.
//   - the creating transaction's spend proof really does commit to
//     `coin_commitment` (`spend_pv.output_commitments` — Phase 3 replaces
//     "take this as a witness" with "recursively verify the proof that
//     produced it", via `Groth16VerifierGadget`; the check itself is
//     unchanged).
//   - the creating transaction's own nullifier had not already been used
//     anywhere on the board as of its own slot — via one non-membership
//     proof against the nullifier accumulator (see above). This is enforced
//     directly: a receipt simply cannot be constructed over a
//     double-spending parent transaction.
//
// Whether the coin has since been *spent* is not tracked here at all —
// that's answered fresh, at spend time, with a single non-membership check
// against the *current* nullifier root (see `check_spend`).
pub fn check_coin_receipt(
    vkey: [u32; 8],
    owner_pk: OwnerPk,
    coin_commitment: Fr,
    entry_k: BoardEntry,
    received_slot: usize,
    append_path: Vec<Fr>,
    parent_nonmembership: NonMembershipWitness,
    nullifier_root_at_parent_slot: Fr,
    spend_pv: ValidPublicValues,
) -> Result<CoinReceiptPublicValues, &'static str> {
    if !verify_nonmembership(nullifier_root_at_parent_slot, entry_k.nullifier, &parent_nonmembership) {
        return Err("parent transaction's nullifier was already present on the board — it was a double-spend");
    }

    let leaf_k = merkle_leaf(received_slot, &entry_k);
    let board_root = compute_root_from_path(leaf_k, received_slot, &append_path);

    if !entry_k.output_commitments.contains(&coin_commitment) {
        return Err("entry_k does not create coin_commitment");
    }
    if !spend_pv.output_commitments.contains(&coin_commitment) {
        return Err("parent spend proof does not commit to this coin commitment");
    }

    Ok(CoinReceiptPublicValues {
        vkey,
        owner_pk,
        coin_commitment,
        board_root,
        received_at: received_slot as u64,
    })
}

/// The public values committed by a coin's receipt proof.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct CoinReceiptPublicValues {
    pub vkey: [u32; 8],
    #[serde(with = "field_serde")]
    pub owner_pk: OwnerPk,
    #[serde(with = "field_serde")]
    pub coin_commitment: Fr,
    #[serde(with = "field_serde")]
    pub board_root: Fr,
    pub received_at: u64,
}

impl CoinReceiptPublicValues {
    pub fn encode(&self) -> Vec<u8> {
        bincode::serialize(self).expect("CoinReceiptPublicValues is always serializable")
    }
}

// ---- Spend relation --------------------------------------------------------

/// Checks every condition of the `Valid` (spend) relation. In Phase 2/3 this
/// same logic becomes `SpendCircuit`'s `ConstraintSynthesizer` body; here
/// it's the plain-Rust reference implementation used both directly (tests
/// below) and as the correctness oracle circuit tests are checked against.
///
/// `entry_position` is the slot `tx_star` will land at (== current board
/// size); `append_path` is its Merkle append proof, verified against the
/// *old* root (the zero-element placeholder at that position) — the same
/// technique `check_coin_receipt` uses for a receiving entry, just for an
/// unfilled position.
///
/// `own_nullifier_nonmembership`/`current_nullifier_root` prove the coin has
/// not already been spent: a single non-membership check against the
/// nullifier accumulator's current state. This check is uniform for genesis
/// and non-genesis spends — an empty/near-empty accumulator trivially proves
/// non-membership, so no special-casing is needed for an empty board.
///
/// `input_coins` and `output_coins` are the private witnesses: the actual coin
/// data whose commitments are asserted to match `tx_star`'s commitment lists.
/// This lets the circuit verify conservation (`Σ input values == Σ output values`)
/// without revealing any values to parties outside the proof.
///
/// **Phase 2/3 note**: `Coin.value` needs an explicit range-check gadget once
/// this becomes a circuit (bounded to 64 bits) — `Fr` is a 753-bit field, so
/// an unconstrained field-element "value" could wrap around and defeat this
/// conservation check. Rust's own `u64` type makes that impossible here.
pub fn check_spend(
    vkey: [u32; 8],
    coin_proof_vkey: [u32; 8],
    sk_p: OwnerScalar,
    pk_p: OwnerPk,
    coin_commitment: Fr,
    entry_position: usize,
    append_path: Vec<Fr>,
    tx_star: Transaction,
    input_coins: Vec<Coin>,
    output_coins: Vec<Coin>,
    is_genesis: bool,
    coin_proof: Option<CoinReceiptPublicValues>,
    own_nullifier_nonmembership: NonMembershipWitness,
    current_nullifier_root: Fr,
) -> Result<ValidPublicValues, &'static str> {
    if derive_owner_pk(&sk_p) != pk_p {
        return Err("pk_P must be the public key for sk_P");
    }

    let board_root = compute_root_from_path(Fr::from(0u64), entry_position, &append_path);

    // Compute the spender's own nullifier. `sk_p` is a foreign field element
    // relative to `Fr` (see the `OwnerScalar` doc comment), so it's folded
    // through `fold_owner_scalar` rather than absorbed as a native `Fr`
    // value. Published in the clear on `BoardEntry.nullifier` by whoever
    // calls `encrypt_tx` — `Transaction` itself carries no nullifier field
    // to cross-check against (see its doc comment).
    let own_nullifier = poseidon_hash(&[coin_commitment, fold_owner_scalar(&sk_p)]);

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

    /// X25519 encryption keypair for party `seed` — used only for board-entry
    /// encryption, entirely separate from that party's coin-ownership keypair.
    fn enc_party(seed: u8) -> ([u8; 32], [u8; 32]) {
        let mut sk = [0u8; 32];
        sk[1] = seed; // byte 0 is clamped by X25519 (sk[0] &= 248), so seeds 1-7 would
                      // all collapse to the same scalar as genesis. Use byte 1 instead.
        let secret = X25519Secret::from(sk);
        let pk = *X25519PublicKey::from(&secret).as_bytes();
        (sk, pk)
    }

    /// Native coin-ownership keypair for party `seed`.
    fn owner_party(seed: u8) -> (OwnerScalar, OwnerPk) {
        let sk = OwnerScalar::from((seed as u64) + 100); // +100: keep well away from genesis_sk()==1
        (sk, derive_owner_pk(&sk))
    }

    fn coin(seed: u8, value: u64, owner_pk: OwnerPk) -> Coin {
        Coin { value, rand: Fr::from(seed as u64 + 1000), owner_pk }
    }

    /// Build a Transaction using X25519 note encryption derived from session_key.
    /// Returns (tx, session_key, recipient_enc_pks) so callers can pass to `enc`
    /// (along with the sender's native key, needed there to derive the
    /// nullifier — see `encrypt_tx`'s doc comment).
    fn make_tx(
        id: u64,
        // Unused now: nullifier derivation moved to `encrypt_tx` (see its doc
        // comment) — kept as a parameter so every call site's argument list
        // stays self-documenting ("whose transaction is this") without
        // needing to touch the ~20 call sites below.
        _sender_sk: OwnerScalar,
        sender_enc_sk: [u8; 32],
        input_coins: &[Coin],
        outputs: &[(Coin, OwnerPk, [u8; 32] /* recipient enc pk */)],
    ) -> (Transaction, [u8; 32], Vec<[u8; 32]>) {
        let input_commitments: Vec<Fr> = input_coins.iter().map(|c| c.commitment()).collect();
        let recipient_enc_pks: Vec<[u8; 32]> = outputs.iter().map(|(_, _, rpk)| *rpk).collect();
        let output_commitments: Vec<Fr> = outputs.iter().map(|(c, _, _)| c.commitment()).collect();
        // Derive session key deterministically from sender's encryption sk and id (test helper).
        let session_key = {
            let mut h = Sha256::new();
            h.update(sender_enc_sk); h.update(id.to_le_bytes()); h.update(EK_SALT);
            let mut out = [0u8; 32]; out.copy_from_slice(&h.finalize()); out
        };
        let note_encs: Vec<Vec<u8>> = outputs.iter().enumerate()
            .map(|(i, (c, _, _))| build_note_enc(&session_key, i, c))
            .collect();
        let tx = Transaction { id, input_commitments, output_commitments, note_encs, spend_proof: vec![] };
        (tx, session_key, recipient_enc_pks)
    }

    fn enc(tx: &Transaction, sender_sk: &OwnerScalar, recipient_enc_pks: &[[u8; 32]], session_key: [u8; 32]) -> BoardEntry {
        encrypt_tx(tx, sender_sk, recipient_enc_pks, session_key)
    }

    /// Build a coin's one-shot receipt: `entries[received_slot]` must be the
    /// transaction that transfers `coin_commitment` to `owner_pk`. The
    /// parent-nullifier non-membership witness/root are derived by replaying
    /// all of `entries`' nullifiers up to (excluding) `received_slot` — the
    /// board state as it stood just before the creating transaction itself.
    /// `spend_pv` is the creating transaction's own spend public values
    /// (stands in for Phase 3's recursively-verified parent proof).
    fn make_receipt(
        owner_pk: OwnerPk,
        coin_commitment: Fr,
        entries: &[BoardEntry],
        received_slot: usize,
        spend_pv: ValidPublicValues,
    ) -> Result<CoinReceiptPublicValues, &'static str> {
        let ap = append_proof_for(&entries[..=received_slot]);
        let all_nullifiers: Vec<Fr> = entries.iter().map(|e| e.nullifier).collect();
        let tree = NullifierTree::replay(&all_nullifiers, received_slot);
        let parent_root = tree.root();
        let parent_witness = tree.prove_non_membership(entries[received_slot].nullifier);
        check_coin_receipt(
            TEST_COIN_PROOF_VKEY, owner_pk, coin_commitment,
            entries[received_slot].clone(), received_slot, ap,
            parent_witness, parent_root, spend_pv,
        )
    }

    /// Spend `coin_commitment` given the board state `prior_entries` (i.e.
    /// before `tx_star` is posted). The nullifier non-membership witness and
    /// current root are derived by replaying all of `prior_entries`' own
    /// nullifiers — the same accumulator state any external verifier could
    /// independently rebuild.
    fn spend(
        sk: OwnerScalar,
        pk: OwnerPk,
        coin_commitment: Fr,
        prior_entries: &[BoardEntry],
        tx_star: &Transaction,
        input_coins: &[Coin],
        output_coins: &[Coin],
        is_genesis: bool,
        coin_proof: Option<CoinReceiptPublicValues>,
    ) -> Result<ValidPublicValues, &'static str> {
        let ap = append_path_for_next(prior_entries);
        let all_nullifiers: Vec<Fr> = prior_entries.iter().map(|e| e.nullifier).collect();
        let tree = NullifierTree::replay(&all_nullifiers, prior_entries.len());
        let own_nullifier = poseidon_hash(&[coin_commitment, fold_owner_scalar(&sk)]);
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
        let (alice_enc_sk, alice_enc_pk) = enc_party(1);
        let (bob_enc_sk, _) = enc_party(2);
        let (carol_enc_sk, _) = enc_party(3);
        let (_, alice_pk) = owner_party(1);

        let alice_coin = coin(0xA2, 100, alice_pk);
        let (tx0, sk0, r0) = make_tx(0, genesis_sk(), [0u8; 32],
            &[coin(0xA1, 100, genesis_pk())], &[(alice_coin.clone(), alice_pk, alice_enc_pk)]);
        let entry = enc(&tx0, &genesis_sk(), &r0, sk0);

        // Alice (recipient) can decrypt.
        assert_eq!(scan_entry(&alice_enc_sk, &entry), Some(tx0.clone()));
        // Outsiders cannot.
        assert_eq!(scan_entry(&bob_enc_sk,   &entry), None);
        assert_eq!(scan_entry(&carol_enc_sk, &entry), None);

        // Alice decrypts her note via session_key + index.
        assert_eq!(decrypt_note(&sk0, 0, &tx0.note_encs[0]), Some(alice_coin));
        // Wrong index gives None.
        assert_eq!(decrypt_note(&sk0, 1, &tx0.note_encs[0]), None);
    }

    #[test]
    fn multi_output_tx_each_recipient_sees_only_own_note() {
        let (alice_sk, alice_pk) = owner_party(1);
        let (_, bob_pk) = owner_party(2);
        let (_, bob_enc_pk) = enc_party(2);
        let (_, alice_enc_pk) = enc_party(1);

        let alice_coin   = coin(0xA1, 100, alice_pk);
        let bob_coin     = coin(0xB1,  40, bob_pk);
        let alice_change = coin(0xB2,  60, alice_pk);

        let (tx1, sk1, _) = make_tx(1, alice_sk, [0u8; 32], &[alice_coin],
            &[(bob_coin.clone(), bob_pk, bob_enc_pk), (alice_change.clone(), alice_pk, alice_enc_pk)]);

        // Index 0 → bob_coin, index 1 → alice_change.
        assert_eq!(decrypt_note(&sk1, 0, &tx1.note_encs[0]), Some(bob_coin));
        assert_eq!(decrypt_note(&sk1, 1, &tx1.note_encs[1]), Some(alice_change));
        // Wrong index gives None.
        assert_eq!(decrypt_note(&sk1, 1, &tx1.note_encs[0]), None);
        assert_eq!(decrypt_note(&sk1, 0, &tx1.note_encs[1]), None);
    }

    #[test]
    fn scan_entry_finds_recipient_but_not_outsiders() {
        let (alice_enc_sk, alice_enc_pk) = enc_party(1);
        let (bob_enc_sk, _) = enc_party(2);
        let (carol_enc_sk, _) = enc_party(3);
        let (_, alice_pk) = owner_party(1);

        let (tx0, sk0, r0) = make_tx(0, genesis_sk(), [0u8; 32],
            &[coin(0xA1, 100, genesis_pk())],
            &[(coin(0xA2, 100, alice_pk), alice_pk, alice_enc_pk)]);
        let entry = enc(&tx0, &genesis_sk(), &r0, sk0);

        assert_eq!(scan_entry(&alice_enc_sk, &entry), Some(tx0.clone()));
        assert_eq!(scan_entry(&bob_enc_sk,   &entry), None);
        assert_eq!(scan_entry(&carol_enc_sk, &entry), None);
    }

    struct Chain {
        entries: Vec<BoardEntry>,
        tx0: Transaction, tx1: Transaction, tx2: Transaction,
        alice_coin: Coin, bob_coin: Coin, alice_change: Coin, carol_coin: Coin, genesis_coin: Coin,
        alice_sk: OwnerScalar, alice_pk: OwnerPk,
        bob_sk: OwnerScalar, bob_pk: OwnerPk,
        carol_pk: OwnerPk,
        pv0: ValidPublicValues,
    }

    /// Build the standard alice→bob→carol demo chain's board entries and
    /// coins, and the genesis spend's public values (needed as `spend_pv`
    /// for building Alice's receipt).
    fn build_chain() -> Chain {
        let (alice_sk, alice_pk) = owner_party(1);
        let (bob_sk, bob_pk) = owner_party(2);
        let (_, carol_pk) = owner_party(3);
        let (_, alice_enc_pk) = enc_party(1);
        let (_, bob_enc_pk) = enc_party(2);
        let (_, carol_enc_pk) = enc_party(3);

        let genesis_coin = coin(0xA1, 100, genesis_pk());
        let alice_coin   = coin(0xA2, 100, alice_pk);
        let bob_coin     = coin(0xB1,  40, bob_pk);
        let alice_change = coin(0xB2,  60, alice_pk);
        let carol_coin   = coin(0xC1,  40, carol_pk);

        let (tx0, sk0, r0) = make_tx(0, genesis_sk(), [0u8; 32], &[genesis_coin.clone()], &[(alice_coin.clone(), alice_pk, alice_enc_pk)]);
        let (tx1, sk1, r1) = make_tx(1, alice_sk, [0u8; 32], &[alice_coin.clone()], &[(bob_coin.clone(), bob_pk, bob_enc_pk), (alice_change.clone(), alice_pk, alice_enc_pk)]);
        let (tx2, sk2, r2) = make_tx(2, bob_sk, [0u8; 32], &[bob_coin.clone()], &[(carol_coin.clone(), carol_pk, carol_enc_pk)]);
        let entries = vec![
            enc(&tx0, &genesis_sk(), &r0, sk0),
            enc(&tx1, &alice_sk, &r1, sk1),
            enc(&tx2, &bob_sk, &r2, sk2),
        ];

        let pv0 = spend(genesis_sk(), genesis_pk(), genesis_coin.commitment(), &[], &tx0,
            &[genesis_coin.clone()], &[alice_coin.clone()], true, None).unwrap();

        Chain { entries, tx0, tx1, tx2, alice_coin, bob_coin, alice_change, carol_coin, genesis_coin,
            alice_sk, alice_pk, bob_sk, bob_pk, carol_pk, pv0 }
    }

    #[test]
    fn receipt_tracks_correct_received_slot() {
        let c = build_chain();
        let cn_alice = c.alice_coin.commitment();
        let cn_bob = c.bob_coin.commitment();

        let alice_receipt = make_receipt(c.alice_pk, cn_alice, &c.entries, 0, c.pv0.clone()).unwrap();
        assert_eq!(alice_receipt.received_at, 0);

        let alice_spend_pv = spend(c.alice_sk, c.alice_pk, cn_alice, &c.entries[..1], &c.tx1,
            &[c.alice_coin.clone()], &[c.bob_coin.clone(), c.alice_change.clone()], false, Some(alice_receipt)).unwrap();

        let bob_receipt = make_receipt(c.bob_pk, cn_bob, &c.entries, 1, alice_spend_pv).unwrap();
        assert_eq!(bob_receipt.received_at, 1);
        let _ = c.tx2;
    }

    #[test]
    fn coin_proof_tracks_change_as_a_receipt() {
        let c = build_chain();
        let cn_change = c.alice_change.commitment();

        let alice_receipt = make_receipt(c.alice_pk, c.alice_coin.commitment(), &c.entries, 0, c.pv0.clone()).unwrap();
        let alice_spend_pv = spend(c.alice_sk, c.alice_pk, c.alice_coin.commitment(), &c.entries[..1], &c.tx1,
            &[c.alice_coin.clone()], &[c.bob_coin.clone(), c.alice_change.clone()], false, Some(alice_receipt)).unwrap();

        let receipt = make_receipt(c.alice_pk, cn_change, &c.entries, 1, alice_spend_pv).unwrap();
        assert_eq!(receipt.received_at, 1);
    }

    #[test]
    fn demo_chain_is_valid_end_to_end() {
        let c = build_chain();
        let cn_alice = c.alice_coin.commitment();
        let cn_bob = c.bob_coin.commitment();

        let alice_receipt = make_receipt(c.alice_pk, cn_alice, &c.entries, 0, c.pv0).unwrap();
        let pv1 = spend(c.alice_sk, c.alice_pk, cn_alice, &c.entries[..1], &c.tx1,
            &[c.alice_coin.clone()], &[c.bob_coin.clone(), c.alice_change.clone()], false,
            Some(alice_receipt)).unwrap();

        let bob_receipt = make_receipt(c.bob_pk, cn_bob, &c.entries, 1, pv1).unwrap();
        spend(c.bob_sk, c.bob_pk, cn_bob, &c.entries[..2], &c.tx2,
            &[c.bob_coin.clone()], &[c.carol_coin.clone()], false,
            Some(bob_receipt)).unwrap();
        let _ = (c.genesis_coin, c.tx0, c.carol_pk);
    }

    #[test]
    fn rejects_wrong_secret_key() {
        let (alice_sk, _) = owner_party(1);
        let genesis_coin = coin(0xA1, 100, genesis_pk());
        let alice_coin   = coin(0xA2, 100, derive_owner_pk(&alice_sk));
        let (tx0, _, _) = make_tx(0, genesis_sk(), [0u8; 32], &[genesis_coin.clone()], &[(alice_coin.clone(), derive_owner_pk(&alice_sk), [0u8; 32])]);

        let err = spend(alice_sk, genesis_pk(), genesis_coin.commitment(), &[], &tx0,
            &[genesis_coin], &[alice_coin], true, None).unwrap_err();
        assert_eq!(err, "pk_P must be the public key for sk_P");
    }

    #[test]
    fn rejects_minting_without_the_genesis_key() {
        let (alice_sk, alice_pk) = owner_party(1);
        let (_, bob_pk) = owner_party(2);
        let alice_coin = coin(0xA1, 100, alice_pk);
        let bob_coin   = coin(0xB1, 100, bob_pk);
        let (tx0, _, _) = make_tx(0, alice_sk, [0u8; 32], &[alice_coin.clone()], &[(bob_coin.clone(), bob_pk, [0u8; 32])]);

        let err = spend(alice_sk, alice_pk, alice_coin.commitment(), &[], &tx0,
            &[alice_coin], &[bob_coin], true, None).unwrap_err();
        assert_eq!(err, "only the genesis key may mint without provenance");
    }

    #[test]
    fn rejects_building_a_receipt_for_a_coin_never_created() {
        let (_, alice_pk) = owner_party(1);
        let (_, carol_pk) = owner_party(3);

        let genesis_coin     = coin(0xA1, 100, genesis_pk());
        let alice_coin       = coin(0xA2, 100, alice_pk);
        let carol_fake_input = coin(0xC1, 100, carol_pk);

        let (tx0, sk0, r0) = make_tx(0, genesis_sk(), [0u8; 32], &[genesis_coin.clone()], &[(alice_coin, alice_pk, [0u8; 32])]);
        let entries = vec![enc(&tx0, &genesis_sk(), &r0, sk0)];
        let cn_carol = carol_fake_input.commitment();

        let pv0 = spend(genesis_sk(), genesis_pk(), genesis_coin.commitment(), &[], &tx0,
            &[genesis_coin], &[coin(0xA2, 100, alice_pk)], true, None).unwrap();

        // Carol never actually received this coin — entries[0] doesn't create
        // it — so a receipt for it simply cannot be built.
        let err = make_receipt(carol_pk, cn_carol, &entries, 0, pv0).unwrap_err();
        assert_eq!(err, "entry_k does not create coin_commitment");
    }

    #[test]
    fn rejects_receipt_when_creating_transaction_was_itself_a_double_spend() {
        let (alice_sk, alice_pk) = owner_party(1);
        let (_, bob_pk) = owner_party(2);
        let (_, carol_pk) = owner_party(3);

        let genesis_coin = coin(0xA1, 100, genesis_pk());
        let alice_coin   = coin(0xA2, 100, alice_pk);
        let bob_coin     = coin(0xB1, 100, bob_pk);
        let carol_coin   = coin(0xC1, 100, carol_pk);

        let (tx0, sk0, r0) = make_tx(0, genesis_sk(), [0u8; 32], &[genesis_coin.clone()], &[(alice_coin.clone(), alice_pk, [0u8; 32])]);
        // Alice double-spends alice_coin: tx1 and tx2 both claim to spend it
        // (same coin, same key ⇒ identical nullifier for both).
        let (tx1, sk1, r1) = make_tx(1, alice_sk, [0u8; 32], &[alice_coin.clone()], &[(bob_coin, bob_pk, [0u8; 32])]);
        let (tx2, sk2, r2) = make_tx(2, alice_sk, [0u8; 32], &[alice_coin.clone()], &[(carol_coin.clone(), carol_pk, [0u8; 32])]);
        let entries = vec![
            enc(&tx0, &genesis_sk(), &r0, sk0),
            enc(&tx1, &alice_sk, &r1, sk1),
            enc(&tx2, &alice_sk, &r2, sk2),
        ];

        let pv0 = spend(genesis_sk(), genesis_pk(), genesis_coin.commitment(), &[], &tx0,
            &[genesis_coin], &[alice_coin], true, None).unwrap();

        let cn_carol = carol_coin.commitment();
        let err = make_receipt(carol_pk, cn_carol, &entries, 2, pv0).unwrap_err();
        assert_eq!(err, "parent transaction's nullifier was already present on the board — it was a double-spend");
    }

    #[test]
    fn rejects_double_spend() {
        let (alice_sk, alice_pk) = owner_party(1);
        let (bob_sk, bob_pk) = owner_party(2);
        let (_, carol_pk) = owner_party(3);

        let genesis_coin = coin(0xA1, 100, genesis_pk());
        let alice_coin   = coin(0xA2, 100, alice_pk);
        let bob_coin     = coin(0xB1,  60, bob_pk);
        let alice_change = coin(0xB2,  40, alice_pk);
        let carol_coin   = coin(0xC1, 100, carol_pk);

        let cn_alice = alice_coin.commitment();

        let (tx0,  sk0, r0) = make_tx(0, genesis_sk(), [0u8; 32], &[genesis_coin.clone()], &[(alice_coin.clone(), alice_pk, [0u8; 32])]);
        let (tx1,  sk1, r1) = make_tx(1, alice_sk, [0u8; 32], &[alice_coin.clone()], &[(bob_coin.clone(), bob_pk, [0u8; 32]), (alice_change.clone(), alice_pk, [0u8; 32])]);
        let (tx1b, _,   _ ) = make_tx(2, alice_sk, [0u8; 32], &[alice_coin.clone()], &[(carol_coin.clone(), carol_pk, [0u8; 32])]);
        let entries = vec![enc(&tx0, &genesis_sk(), &r0, sk0), enc(&tx1, &alice_sk, &r1, sk1)];

        let pv0 = spend(genesis_sk(), genesis_pk(), genesis_coin.commitment(), &[], &tx0,
            &[genesis_coin], &[alice_coin.clone()], true, None).unwrap();

        let alice_receipt = make_receipt(alice_pk, cn_alice, &entries, 0, pv0).unwrap();
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
        let (alice_sk, alice_pk) = owner_party(1);
        let (_, bob_pk) = owner_party(2);

        let genesis_coin = coin(0xA1, 100, genesis_pk());
        let alice_coin   = coin(0xA2, 100, alice_pk);
        let bob_coin     = coin(0xB1,  40, bob_pk);
        let alice_change = coin(0xB2,  60, alice_pk);

        let (tx0, sk0, r0) = make_tx(0, genesis_sk(), [0u8; 32], &[genesis_coin.clone()], &[(alice_coin.clone(), alice_pk, [0u8; 32])]);
        let (tx1, sk1, r1) = make_tx(1, alice_sk, [0u8; 32], &[alice_coin.clone()], &[(bob_coin.clone(), bob_pk, [0u8; 32]), (alice_change.clone(), alice_pk, [0u8; 32])]);
        let entries = vec![enc(&tx0, &genesis_sk(), &r0, sk0), enc(&tx1, &alice_sk, &r1, sk1)];

        let cn_alice  = alice_coin.commitment();
        let cn_change = alice_change.commitment();

        let pv0 = spend(genesis_sk(), genesis_pk(), genesis_coin.commitment(), &[], &tx0,
            &[genesis_coin], &[alice_coin.clone()], true, None).unwrap();
        let alice_receipt = make_receipt(alice_pk, cn_alice, &entries, 0, pv0).unwrap();

        // tx2 legitimately spends alice_change, but we supply the receipt for
        // alice_coin — a different (and already-spent) commitment — instead.
        let payout = coin(0xC1, 60, bob_pk);
        let (tx2, _, _) = make_tx(2, alice_sk, [0u8; 32], &[alice_change.clone()], &[(payout.clone(), bob_pk, [0u8; 32])]);
        let err = spend(alice_sk, alice_pk, cn_change, &entries, &tx2,
            &[alice_change], &[payout], false, Some(alice_receipt)).unwrap_err();
        assert_eq!(err, "coin-proof tracks a different coin");
        let _ = (sk1, r1);
    }

    #[test]
    fn rejects_value_conservation_violation() {
        let (_, alice_pk) = owner_party(1);
        let genesis_coin = coin(0xA1, 100, genesis_pk());
        let alice_coin   = coin(0xA2, 100, alice_pk);
        let extra_coin   = coin(0xA3,   1, alice_pk);

        let (tx0, _, _) = make_tx(0, genesis_sk(), [0u8; 32], &[genesis_coin.clone()],
            &[(alice_coin.clone(), alice_pk, [0u8; 32]), (extra_coin.clone(), alice_pk, [0u8; 32])]);

        let err = spend(genesis_sk(), genesis_pk(), genesis_coin.commitment(), &[], &tx0,
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
        fn value(i: u32) -> Fr {
            Fr::from(i as u64 + 1) // keep every value > 0, avoiding the sentinel edge case
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
        let absent = Fr::from(u64::MAX);
        let witness = tree.prove_non_membership(absent);
        assert!(verify_nonmembership(tree.root(), absent, &witness));

        let member = value(batch * 8);
        let w = tree.prove_non_membership(member);
        assert!(!verify_nonmembership(tree.root(), member, &w));
    }
}
