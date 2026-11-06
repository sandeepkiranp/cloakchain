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
use sha2::{Digest, Sha256, Sha512};
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
    let chunks: Vec<Fr> = bits.chunks(248).map(bits_le_to_fr).collect();
    poseidon_hash(&chunks)
}

/// Interpret little-endian bits as an integer. Callers must pass few enough
/// bits to stay under `Fr`'s modulus.
fn bits_le_to_fr(bits: &[bool]) -> Fr {
    let mut acc = Fr::from(0u64);
    let mut place = Fr::from(1u64);
    for &b in bits {
        if b {
            acc += place;
        }
        place *= Fr::from(2u64);
    }
    acc
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

/// The serial number ("nullifier") of a coin: `Poseidon(cm, fold(sk))`.
/// Deterministic per coin, posted in the clear on `BoardEntry.nullifier`.
pub fn derive_nullifier(coin_commitment: Fr, sk: &OwnerScalar) -> Fr {
    poseidon_hash(&[coin_commitment, fold_owner_scalar(sk)])
}

// ---- Per-coin signing keys -------------------------------------------------
//
// A serial number is public and deterministic, so anyone can copy it into
// their own transaction. Accumulator insertion can't be gated on validity
// without exposing which transactions are carriers (see `History`), so
// genuine occurrences are instead told apart from copies *after* the fact: a
// real spend carries a signature under a key only the coin's owner can derive.
//
// `vsk = PRF_sk(cm, "sig")`, `vpk = vsk·G` on the same curve as owner keys, so
// the circuit reuses its existing scalar-mult gadget. Every spend of one coin
// has the same `vpk`, which is what makes two validly-signed spends a provable
// double-spend. `vpk` never appears publicly: it travels only inside the
// ciphertext and, as a hash, in the spend proof's public inputs.

/// Domain separator for [`derive_coin_signing_key`]: keeps it unrelated to
/// [`derive_nullifier`], which hashes the same `(cm, fold(sk))` pair.
pub const SIG_KEY_DOMAIN: u64 = u64::from_be_bytes(*b"CLOAKVSK");
/// Domain separator for [`signature_challenge`].
pub const SIG_CHALLENGE_DOMAIN: u64 = u64::from_be_bytes(*b"CLOAKSIG");
/// Bits in `CoinSignature.s`'s low limb — see [`CoinSignature::s_limbs`].
pub const SIG_S_LO_BITS: usize = 376;

/// `vsk` as an `Fr` element, the Poseidon output's native form. The circuit
/// feeds its canonical bits directly to scalar-mult, which is why this isn't
/// reduced here: `G` has prime order `OwnerScalar::MODULUS`, so the integer
/// and its reduction ([`scalar_from_fr`]) give the same point.
pub fn derive_coin_signing_key(sk: &OwnerScalar, coin_commitment: Fr) -> Fr {
    poseidon_hash(&[Fr::from(SIG_KEY_DOMAIN), coin_commitment, fold_owner_scalar(sk)])
}

/// Reduce an `Fr` element's canonical integer into the scalar field — the
/// two are genuinely different fields, see the `OwnerScalar` doc comment.
fn scalar_from_fr(x: &Fr) -> OwnerScalar {
    OwnerScalar::from_le_bytes_mod_order(&x.into_bigint().to_bytes_le())
}

/// The per-coin verification key `vpk = vsk·G`.
pub fn derive_coin_vpk(sk: &OwnerScalar, coin_commitment: Fr) -> OwnerPk {
    derive_owner_pk(&scalar_from_fr(&derive_coin_signing_key(sk, coin_commitment)))
}

/// `H(vpk)` — the only form of `vpk` in a spend proof's public inputs.
pub fn hash_vpk(vpk: &OwnerPk) -> Fr {
    let (x, y) = owner_pk_to_field_pair(vpk);
    poseidon_hash(&[x, y])
}

/// The message a coin signature covers: `H(SN, H(O), ct_commitment)`.
/// Covering the ciphertext is what stops a copier reusing a real `σ` next to
/// their own payload.
pub fn signature_message(nullifier: Fr, outputs_hash: Fr, ciphertext_commitment: Fr) -> Fr {
    poseidon_hash(&[nullifier, outputs_hash, ciphertext_commitment])
}

/// The Schnorr challenge `H(R, vpk, msg)`.
pub fn signature_challenge(r: &OwnerPk, vpk: &OwnerPk, msg: Fr) -> Fr {
    let (rx, ry) = owner_pk_to_field_pair(r);
    let (vx, vy) = owner_pk_to_field_pair(vpk);
    poseidon_hash(&[Fr::from(SIG_CHALLENGE_DOMAIN), rx, ry, vx, vy, msg])
}

/// A Schnorr signature in challenge form, `σ = (c, s)`, verified as
/// `c == H(s·G − c·vpk, vpk, msg)`. Challenge form matters: `σ` holds no curve
/// point, so a junk occurrence's `σ` can't fail to parse and verification is a
/// total function — the window check in `circuit-spend` must evaluate to
/// `false` on junk, never become unsatisfiable.
///
/// `s` is posted as one scalar rather than as its two limbs: limbs are
/// half-empty field elements, which would make carriers recognizable on the
/// wire. Limbs exist only where `s` enters an `Fr`-native hash.
///
/// The all-zero default fills a history leaf's unused input slots.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize)]
pub struct CoinSignature {
    #[serde(with = "field_serde")]
    pub c: Fr,
    #[serde(with = "field_serde")]
    pub s: OwnerScalar,
}

impl CoinSignature {
    /// `s` split at [`SIG_S_LO_BITS`] into two native `Fr` limbs, each well
    /// under `Fr`'s capacity, so that `s` can be hashed without reducing it.
    pub fn s_limbs(&self) -> (Fr, Fr) {
        let bits = self.s.into_bigint().to_bits_le();
        (bits_le_to_fr(&bits[..SIG_S_LO_BITS]), bits_le_to_fr(&bits[SIG_S_LO_BITS..]))
    }
}

/// Derive the signing nonce from `(vsk, msg)`. Deterministic, so re-signing
/// can't reuse a nonce across messages, and drawn from 1024 bits before
/// reducing: a nonce merely biased mod a 753-bit order leaks `vsk` to lattice
/// attacks across signatures, so a single 256- or 512-bit digest isn't enough.
fn signature_nonce(vsk: &Fr, msg: Fr) -> OwnerScalar {
    let mut wide = Vec::with_capacity(128);
    for counter in 0u8..2 {
        let mut h = Sha512::new();
        h.update(b"CLOAKNCE");
        h.update([counter]);
        h.update(vsk.into_bigint().to_bytes_le());
        h.update(msg.into_bigint().to_bytes_le());
        wide.extend_from_slice(&h.finalize());
    }
    OwnerScalar::from_le_bytes_mod_order(&wide)
}

/// Sign `msg` under the per-coin key `vsk`. Must run last when building an
/// entry: the proof goes inside the ciphertext and the ciphertext is under the
/// signature, so the proof can't take `σ` as an input.
pub fn sign_coin_message(vsk: &Fr, msg: Fr) -> CoinSignature {
    let x = scalar_from_fr(vsk);
    let k = signature_nonce(vsk, msg);
    let c = signature_challenge(&derive_owner_pk(&k), &derive_owner_pk(&x), msg);
    CoinSignature { c, s: k + scalar_from_fr(&c) * x }
}

/// Total on every `σ`: junk simply returns `false`.
pub fn verify_coin_signature(vpk: &OwnerPk, msg: Fr, sig: &CoinSignature) -> bool {
    let r = ark_mnt6_753::G1Projective::generator() * sig.s - vpk.into_group() * scalar_from_fr(&sig.c);
    signature_challenge(&r.into_affine(), vpk, msg) == sig.c
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

/// Input coins a spend may consume. Fixed per deployment, since it sets the
/// shape of every history leaf (see [`LeafOpening`]); the `two-inputs` feature
/// raises it from 1 to 2. Every input needs its own serial number, signature
/// and window, so each one costs the next spender a full set of parent checks.
#[cfg(not(feature = "two-inputs"))]
pub const MAX_INPUTS: usize = 1;
#[cfg(feature = "two-inputs")]
pub const MAX_INPUTS: usize = 2;

/// A generalised transaction: `S` spends up to [`MAX_INPUTS`] input coins and
/// creates one or more output coins for (potentially different) recipients.
///
/// Only **commitments** appear in the transaction body. Sender and recipient
/// identities are NOT stored — the sender is proven via the nullifiers
/// (published in the clear on `BoardEntry.nullifiers`, not duplicated here)
/// and recipient ownership is encoded inside each coin commitment
/// (`Poseidon(v, r, pk)`). Each output's coin data is encrypted in
/// `note_encs[i]` per recipient.
///
/// The input coins' commitments aren't stored here either: whoever builds this
/// transaction already holds the real input `Coin`s, so `encrypt_tx` takes them
/// as a direct parameter instead of reading them back out of a stored field.
///
/// `vpks` and `anchor` stay inside the ciphertext so that nothing posted
/// can be matched against real roots or linked between spends — see
/// `BoardEntry`. A recipient checks both in [`check_receipt`].
///
/// `spend_proof` is attached after proving and the whole struct re-encrypted.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Transaction {
    pub id: u64,
    /// Commitments to the new coins (same index as note_encs).
    #[serde(with = "field_serde")]
    pub output_commitments: Vec<Fr>,
    /// `note_encs[i]` = `encrypt(output_coin_i, pair_key(sender, recipient_i))`.
    pub note_encs: Vec<Vec<u8>>,
    /// Each input coin's per-coin key, see [`derive_coin_vpk`], in input order.
    #[serde(with = "field_serde")]
    pub vpks: Vec<OwnerPk>,
    /// The history state this transaction's proof is checked against.
    pub anchor: Anchor,
    pub spend_proof: Vec<u8>,
}

impl Transaction {
    /// `cn` was received in this tx if it is among the output commitments.
    /// Recipient ownership is already encoded inside the commitment itself.
    pub fn receives_coin(&self, cn: &Fr) -> bool {
        self.output_commitments.contains(cn)
    }
}

// ---- X25519 sender-anonymous encryption ------------------------------------
//
// Unchanged from the SHA256/SP1 design and entirely off-circuit: this is
// *wallet-side* bookkeeping (delivering a coin's opening — value/rand — to
// its recipient), not something any circuit needs to prove anymore. The
// port's "move decryption off-circuit" decision made `BoardEntry`'s
// `output_commitments` public instead (see below), so no proof depends on
// any of this. X25519 keys are now entirely separate from
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
/// plus the **public** commitments this entry's transaction creates, plus the
/// signature that distinguishes a real spend from a copy of its nullifier.
///
/// `output_commitments` is public (not only inside `ciphertext`) so that a
/// spend can prove `coin_commitment ∈ entry.output_commitments` directly,
/// without decrypting anything in-circuit — see the MNT-native port plan's
/// "move decryption off-circuit" decision. This leaks nothing beyond what a
/// hiding commitment already leaks (nothing about value/rand/owner), the same
/// trade-off Zcash's public note-commitment tree makes.
///
/// The board and accumulator roots preceding an entry are deliberately **not**
/// posted: anyone could match them against the real roots and pick out
/// carriers. Each wallet computes them from its own replay, see [`History`].
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
    /// One serial number per input coin, see [`derive_nullifier`] — each looks
    /// random, and goes into the nullifier accumulator. Copyable by anyone, so
    /// one never proves a spend on its own.
    #[serde(with = "field_serde")]
    pub nullifiers: Vec<Fr>,
    /// `tx.output_commitments` — public, see the struct doc comment above.
    #[serde(with = "field_serde")]
    pub output_commitments: Vec<Fr>,
    /// `signatures[i]` is `σ` over `signature_message(nullifiers[i],
    /// H(output_commitments), entry_ciphertext_commitment(self))`, under input
    /// `i`'s `vpk`. Each input signs separately because each input's copies
    /// are judged under its own key.
    pub signatures: Vec<CoinSignature>,
}

impl BoardEntry {
    pub fn outputs_hash(&self) -> Fr {
        poseidon_hash(&self.output_commitments)
    }

    /// The message `signatures[i]` must verify over.
    pub fn signature_message(&self, i: usize) -> Fr {
        signature_message(self.nullifiers[i], self.outputs_hash(), entry_ciphertext_commitment(self))
    }

    /// The inputs a wallet replays from this entry, whatever was posted: at
    /// most [`MAX_INPUTS`], in order, and a missing signature reads as the
    /// all-zero junk one. Total, since every host transaction gets replayed and
    /// none may stall a wallet. Anything past `MAX_INPUTS` is simply not part
    /// of the board.
    pub fn posted_inputs(&self) -> Vec<PostedInput> {
        self.nullifiers
            .iter()
            .take(MAX_INPUTS)
            .enumerate()
            .map(|(i, sn)| PostedInput { nullifier: *sn, signature: self.signatures.get(i).cloned().unwrap_or_default() })
            .collect()
    }
}

/// One input as it appears on the board: a serial number and the signature
/// claiming it. Either can be anyone's junk.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize)]
pub struct PostedInput {
    #[serde(with = "field_serde")]
    pub nullifier: Fr,
    pub signature: CoinSignature,
}

/// Encrypt `tx` for the given `recipient_pks` (X25519 encryption keys — a
/// separate keyspace from coin-ownership `OwnerPk`s) and `session_key`, then
/// sign the result. Pass the same `session_key` when re-encrypting after
/// attaching a spend proof — the deterministic `ek_sk` ensures `ek_pk` and
/// `key_encs` are unchanged. The signatures do change, since they cover the
/// ciphertext; signing here, last, is what avoids any circularity with the
/// proof inside it. One signature per input coin, under that coin's key.
pub fn encrypt_tx(
    tx: &Transaction,
    input_commitments: &[Fr],
    sender_sk: &OwnerScalar,
    recipient_pks: &[[u8; 32]],
    session_key: [u8; 32],
) -> BoardEntry {
    debug_assert!(input_commitments.iter().map(|cm| derive_coin_vpk(sender_sk, *cm)).eq(tx.vpks.iter().copied()));

    // Derive the ephemeral key from the session key (deterministic).
    let ek_sk = ek_secret(&session_key);
    let ek_pk = *X25519PublicKey::from(&ek_sk).as_bytes();

    // Encrypt the transaction body.
    let tx_bytes = bincode::serialize(tx).expect("Transaction is always serializable");
    let mut plaintext = MAGIC_TAG.to_vec();
    plaintext.extend_from_slice(&tx_bytes);
    let ciphertext = xor_with_keystream(&session_key, &plaintext);

    // Wrap the session key for each recipient using X25519 ECDH.
    let key_encs: Vec<[u8; 32]> = recipient_pks.iter().map(|rpk| {
        let recipient_pub = X25519PublicKey::from(*rpk);
        let shared = *ek_sk.diffie_hellman(&recipient_pub).as_bytes();
        let wk = wrapping_key(&shared);
        let mut enc = [0u8; 32];
        for (e, (w, s)) in enc.iter_mut().zip(wk.iter().zip(session_key.iter())) {
            *e = w ^ s;
        }
        enc
    }).collect();

    let outputs_hash = poseidon_hash(&tx.output_commitments);
    let ct_commitment = ciphertext_commitment(&ciphertext, &ek_pk, &key_encs);
    let nullifiers: Vec<Fr> = input_commitments.iter().map(|cm| derive_nullifier(*cm, sender_sk)).collect();
    let signatures = input_commitments
        .iter()
        .zip(&nullifiers)
        .map(|(cm, sn)| {
            let msg = signature_message(*sn, outputs_hash, ct_commitment);
            sign_coin_message(&derive_coin_signing_key(sender_sk, *cm), msg)
        })
        .collect();

    BoardEntry {
        ciphertext,
        ek_pk,
        key_encs,
        nullifiers,
        output_commitments: tx.output_commitments.clone(),
        signatures,
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
// A leaf embeds the roots preceding it, computed from each wallet's own replay
// rather than read from the entry (see `History`). Because a spend's anchor
// predates its own slot, a proof never depends on where its entry lands.

/// Maximum tree depth. Supports up to 2^32 ≈ 4 billion board entries.
pub const TREE_DEPTH: usize = 32;

/// The preimage of a history leaf `t`: `H(slot, ct_commitment, H(O),
/// (SN_i, σ_i) for i < MAX_INPUTS, R_{t-1}, A_{t-1})`, with unused input slots
/// all zero. Including the slot index prevents permuting entries while keeping
/// a valid root. Including the preceding roots is what lets a later spend
/// prove, against its own anchor, that a parent's claimed anchor is real and
/// what the parent's windows looked like.
///
/// A zero-padded slot hashes like a posted input `(0, σ = 0)`, so two entries
/// can share a leaf. That's harmless: the leaf is still fixed by the board, and
/// a spend reads a zero serial number as "no input here" (see `check_parent`),
/// which no real coin can have.
///
/// Every field is a native `Fr` value (or, for `ciphertext_commitment`, an
/// opaque witness the circuit never expands), so `circuit-spend` mirrors
/// [`LeafOpening::hash`] directly.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize)]
pub struct LeafOpening {
    pub slot: u64,
    #[serde(with = "field_serde")]
    pub ciphertext_commitment: Fr,
    #[serde(with = "field_serde")]
    pub outputs_hash: Fr,
    /// [`BoardEntry::posted_inputs`]: at most `MAX_INPUTS`.
    pub inputs: Vec<PostedInput>,
    #[serde(with = "field_serde")]
    pub prev_board_root: Fr,
    #[serde(with = "field_serde")]
    pub prev_nullifier_root: Fr,
}

impl LeafOpening {
    pub fn new(slot: usize, entry: &BoardEntry, prev_board_root: Fr, prev_nullifier_root: Fr) -> Self {
        Self {
            slot: slot as u64,
            ciphertext_commitment: entry_ciphertext_commitment(entry),
            outputs_hash: entry.outputs_hash(),
            inputs: entry.posted_inputs(),
            prev_board_root,
            prev_nullifier_root,
        }
    }

    /// Input slot `i`'s serial number, zero if unused.
    pub fn nullifier(&self, i: usize) -> Fr {
        self.inputs.get(i).map_or(Fr::from(0u64), |input| input.nullifier)
    }

    /// The serial numbers of every input slot, zero-padded to `MAX_INPUTS`.
    pub fn nullifiers(&self) -> [Fr; MAX_INPUTS] {
        std::array::from_fn(|i| self.nullifier(i))
    }

    pub fn hash(&self) -> Fr {
        let mut preimage = vec![Fr::from(self.slot), self.ciphertext_commitment, self.outputs_hash];
        for i in 0..MAX_INPUTS {
            let signature = self.inputs.get(i).map(|input| input.signature.clone()).unwrap_or_default();
            let (s_lo, s_hi) = signature.s_limbs();
            preimage.extend([self.nullifier(i), signature.c, s_lo, s_hi]);
        }
        preimage.extend([self.prev_board_root, self.prev_nullifier_root]);
        poseidon_hash(&preimage)
    }

    /// Input `i`'s link in its serial number's occurrence chain.
    pub fn occurrence(&self, i: usize) -> Occurrence {
        Occurrence {
            outputs_hash: self.outputs_hash,
            ciphertext_commitment: self.ciphertext_commitment,
            signature: self.inputs[i].signature.clone(),
        }
    }

    /// The links this entry adds to `nullifier`'s chain, one per input posting
    /// it, in order.
    pub fn occurrences_of(&self, nullifier: Fr) -> impl Iterator<Item = Occurrence> + '_ {
        (0..self.inputs.len()).filter(move |&i| self.inputs[i].nullifier == nullifier).map(|i| self.occurrence(i))
    }

    /// Does input `i`'s `σ` verify as this entry's signature under `vpk`?
    pub fn signature_valid(&self, i: usize, vpk: &OwnerPk) -> bool {
        self.occurrence(i).signature_valid(self.inputs[i].nullifier, vpk)
    }
}

/// The history leaf for `entry` at `slot`, given the roots preceding it.
pub fn merkle_leaf(slot: usize, entry: &BoardEntry, prev_board_root: Fr, prev_nullifier_root: Fr) -> Fr {
    LeafOpening::new(slot, entry, prev_board_root, prev_nullifier_root).hash()
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
    ciphertext_commitment(&entry.ciphertext, &entry.ek_pk, &entry.key_encs)
}

fn ciphertext_commitment(ciphertext: &[u8], ek_pk: &[u8; 32], key_encs: &[[u8; 32]]) -> Fr {
    let key_encs_bytes: Vec<u8> = key_encs.iter().flatten().copied().collect();
    poseidon_hash(&[
        poseidon_hash_bytes(ciphertext),
        poseidon_hash_bytes(ek_pk),
        poseidon_hash_bytes(&key_encs_bytes),
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

/// Walk the path from `leaf` at `slot` to the root.
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

/// A fixed-depth Merkle tree maintained incrementally: `nodes` caches every
/// level's node hashes, so changing one leaf only recomputes its O(TREE_DEPTH)
/// ancestors instead of the whole tree. Shared by the board tree (see
/// [`History`]) and the nullifier accumulator (see [`NullifierTree`]).
#[derive(Clone, Debug)]
struct IncrementalTree {
    /// `nodes[d]` holds the hash of every *filled* node at depth d (0 =
    /// leaves, `TREE_DEPTH` = root), keyed by its position at that depth.
    /// A missing entry means "unfilled" — use the precomputed zero-subtree
    /// hash for that depth instead (see `zero_hashes`).
    nodes: Vec<HashMap<usize, Fr>>,
}

impl IncrementalTree {
    fn new() -> Self {
        Self { nodes: vec![HashMap::new(); TREE_DEPTH + 1] }
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

    fn root(&self) -> Fr {
        self.nodes[TREE_DEPTH].get(&0).copied().unwrap_or_else(empty_root)
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
}

// ---- Occurrence accumulator (indexed Merkle tree) ---------------------------
//
// Double-spend detection does not require walking every board slot. Every
// nullifier ever published (`BoardEntry.nullifier`, already public) is
// inserted into a single indexed Merkle tree — a sorted linked list of
// leaves, each storing `(value, next_value, next_index, occ)`. A single Merkle
// path to a leaf whose `value < target < next_value` proves `target` is
// absent from the *entire* set the tree's root represents, in one
// O(TREE_DEPTH) proof instead of an O(slots) scan. Reuses the same Poseidon
// combine/path primitives as the board tree above.
//
// A nullifier can occur more than once, because anyone can copy one, and
// wallets can't tell a copy from a spend while replaying. So instead of being
// a no-op, re-inserting extends a per-nullifier hash chain held in the leaf:
// `occ = H(occ_prev, H(O), ct_commitment, σ)`. The next spender opens that
// chain to prove every occurrence in its parent's window was harmless.
//
// Ordering is over `Fr`'s canonical integer representative (`Fr: Ord`,
// comparing values in `0..p`) rather than byte-lexicographic order — any
// consistent total order works for the accumulator's soundness. In-circuit,
// comparisons must use `circuit-spend`'s own comparator: `ark-r1cs-std` 0.5's
// slice comparison isn't numeric, see `bits_msb_is_lt`.

/// One leaf of the indexed nullifier tree.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize)]
pub struct IndexedLeaf {
    #[serde(with = "field_serde")]
    pub value: Fr,
    #[serde(with = "field_serde")]
    pub next_value: Fr,
    pub next_index: u64,
    /// Head of `value`'s occurrence chain, see [`Occurrence::link`]. Zero only
    /// on the sentinel leaf.
    #[serde(with = "field_serde")]
    pub occ: Fr,
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
        poseidon_hash(&[self.value, self.next_value, Fr::from(self.next_index), self.occ])
    }
}

/// One appearance of a nullifier on the board: the parts of an entry the
/// window check needs. May be a real spend or arbitrary junk.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize)]
pub struct Occurrence {
    #[serde(with = "field_serde")]
    pub outputs_hash: Fr,
    #[serde(with = "field_serde")]
    pub ciphertext_commitment: Fr,
    pub signature: CoinSignature,
}

impl Occurrence {
    /// The next chain head: `H(occ_prev, H(O), ct_commitment, σ)`.
    pub fn link(&self, occ_prev: Fr) -> Fr {
        let (s_lo, s_hi) = self.signature.s_limbs();
        poseidon_hash(&[occ_prev, self.outputs_hash, self.ciphertext_commitment, self.signature.c, s_lo, s_hi])
    }

    pub fn signature_valid(&self, nullifier: Fr, vpk: &OwnerPk) -> bool {
        let msg = signature_message(nullifier, self.outputs_hash, self.ciphertext_commitment);
        verify_coin_signature(vpk, msg, &self.signature)
    }

    /// Can this occurrence coexist with a spend of `outputs_hash` under `vpk`?
    /// Yes if it's the same spend (this includes an honest re-prove, whose
    /// ciphertext differs) or if it's junk. A valid signature over *different*
    /// outputs is a double-spend. The one rule behind both [`check_receipt`]
    /// and [`check_window`].
    pub fn is_harmless(&self, nullifier: Fr, vpk: &OwnerPk, outputs_hash: Fr) -> bool {
        self.outputs_hash == outputs_hash || !self.signature_valid(nullifier, vpk)
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

/// What a spender shows about a nullifier's occurrences under some root: one
/// opened leaf and its chain. A non-empty `occurrences` claims `leaf` is the
/// nullifier's own leaf; an empty one claims `leaf` is its low leaf, i.e. that
/// the nullifier is absent. One shape for both because the circuit is fixed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize)]
pub struct WindowWitness {
    pub leaf: IndexedLeaf,
    pub leaf_index: u64,
    #[serde(with = "field_serde")]
    pub sibling_path: Vec<Fr>,
    /// Oldest first.
    pub occurrences: Vec<Occurrence>,
}

/// Verify that `witness.occurrences` is `target`'s complete occurrence chain
/// under `root`. Complete because the chain must re-fold from zero to exactly
/// the head in the leaf, so nothing can be dropped from either end.
pub fn verify_occurrences(root: Fr, target: Fr, witness: &WindowWitness) -> bool {
    let occ = witness.occurrences.iter().fold(Fr::from(0u64), |prev, o| o.link(prev));
    !witness.occurrences.is_empty()
        && witness.leaf.value == target
        && witness.leaf.occ == occ
        && compute_root_from_path(witness.leaf.hash(), witness.leaf_index as usize, &witness.sibling_path) == root
}

/// The window check: against `root` (the accumulator just before a parent's
/// slot), every occurrence of the parent's nullifier is harmless to a spend of
/// `outputs_hash`, however many there are. Together with the parent's own proof
/// that the nullifier was absent at its anchor, this covers everything between
/// that anchor and the parent's slot. In-circuit, the occurrences are checked
/// one recursive "fold" step at a time (see `circuit-spend`), so copies cost
/// their victim proving time but can't make a coin unspendable.
pub fn check_window(root: Fr, nullifier: Fr, vpk: &OwnerPk, outputs_hash: Fr, witness: &WindowWitness) -> bool {
    if witness.occurrences.is_empty() {
        witness.leaf.value < nullifier
            && nullifier < witness.leaf.next_value
            && compute_root_from_path(witness.leaf.hash(), witness.leaf_index as usize, &witness.sibling_path) == root
    } else {
        verify_occurrences(root, nullifier, witness)
            && witness.occurrences.iter().all(|o| o.is_harmless(nullifier, vpk, outputs_hash))
    }
}

/// Host-side append-only indexed Merkle tree of nullifiers. Anyone can rebuild
/// this deterministically from the public board entries, see [`History`].
///
/// Maintained *incrementally*: `index_of` gives O(log n) low-leaf lookup
/// (instead of scanning every leaf), and `tree` only recomputes the
/// O(TREE_DEPTH) ancestors of the leaves that actually changed — not the whole
/// tree from scratch. Both matter once the board has hundreds of thousands of
/// entries: without them, `insert` is O(n) and a full replay (which calls
/// `insert` in a loop) becomes O(n²), the same class of problem sorted-leaf
/// Merkle trees have, just arrived at via a slow implementation rather than a
/// sorted array.
#[derive(Clone, Debug)]
pub struct NullifierTree {
    leaves: Vec<IndexedLeaf>,
    /// value → leaf index, sorted — gives the low leaf for any target via one
    /// `range(..target).next_back()` lookup instead of a linear scan.
    index_of: BTreeMap<Fr, usize>,
    tree: IncrementalTree,
    /// value → the preimages behind that leaf's `occ` head, oldest first.
    chains: BTreeMap<Fr, Vec<Occurrence>>,
}

impl NullifierTree {
    /// A fresh tree, seeded with the single "everything" sentinel leaf.
    pub fn new() -> Self {
        let sentinel = IndexedLeaf {
            value: Fr::from(0u64),
            next_value: max_nullifier(),
            next_index: 0,
            occ: Fr::from(0u64),
        };
        let mut tree = Self {
            leaves: vec![sentinel.clone()],
            index_of: BTreeMap::new(),
            tree: IncrementalTree::new(),
            chains: BTreeMap::new(),
        };
        tree.index_of.insert(sentinel.value, 0);
        tree.tree.set_leaf(0, sentinel.hash());
        tree
    }

    pub fn root(&self) -> Fr {
        self.tree.root()
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

    /// Record an occurrence of `value` and return the new root: a new leaf the
    /// first time, one more link in that leaf's chain every time after. Blind
    /// by design, since no wallet can check a carrier's validity while
    /// replaying. O(log n): one BTreeMap lookup plus at most two O(TREE_DEPTH)
    /// path updates.
    pub fn insert(&mut self, value: Fr, occurrence: &Occurrence) -> Fr {
        if let Some(&idx) = self.index_of.get(&value) {
            self.leaves[idx].occ = occurrence.link(self.leaves[idx].occ);
            self.tree.set_leaf(idx, self.leaves[idx].hash());
        } else {
            let low_idx = self.find_low_leaf_index(value);
            let low = self.leaves[low_idx].clone();
            let new_index = self.leaves.len();
            let updated_low = IndexedLeaf { next_value: value, next_index: new_index as u64, ..low.clone() };
            let new_leaf = IndexedLeaf {
                value,
                next_value: low.next_value,
                next_index: low.next_index,
                occ: occurrence.link(Fr::from(0u64)),
            };

            self.leaves[low_idx] = updated_low.clone();
            self.leaves.push(new_leaf.clone());
            self.index_of.insert(value, new_index);

            self.tree.set_leaf(low_idx, updated_low.hash());
            self.tree.set_leaf(new_index, new_leaf.hash());
        }
        self.chains.entry(value).or_default().push(occurrence.clone());
        self.root()
    }

    /// Build a non-membership witness for `target` against the tree's current
    /// state. Safe to call even if `target` is already a member — the
    /// resulting witness simply won't pass `verify_nonmembership`.
    pub fn prove_non_membership(&self, target: Fr) -> NonMembershipWitness {
        let low_idx = self.find_low_leaf_index(target);
        NonMembershipWitness {
            low_leaf: self.leaves[low_idx].clone(),
            low_leaf_index: low_idx as u64,
            sibling_path: self.tree.path_for(low_idx),
        }
    }

    /// Open `target`'s leaf and occurrence chain, if it's a member.
    pub fn prove_occurrences(&self, target: Fr) -> Option<WindowWitness> {
        let idx = *self.index_of.get(&target)?;
        Some(WindowWitness {
            leaf: self.leaves[idx].clone(),
            leaf_index: idx as u64,
            sibling_path: self.tree.path_for(idx),
            occurrences: self.chains.get(&target).cloned().unwrap_or_default(),
        })
    }

    /// The witness for [`check_window`]: the chain if `target` is a member,
    /// otherwise its low leaf with an empty chain.
    pub fn prove_window(&self, target: Fr) -> WindowWitness {
        self.prove_occurrences(target).unwrap_or_else(|| {
            let low_idx = self.find_low_leaf_index(target);
            WindowWitness {
                leaf: self.leaves[low_idx].clone(),
                leaf_index: low_idx as u64,
                sibling_path: self.tree.path_for(low_idx),
                occurrences: Vec::new(),
            }
        })
    }
}

impl Default for NullifierTree {
    fn default() -> Self {
        Self::new()
    }
}

/// Replay one leaf's inputs into the accumulator, in input order.
fn insert_inputs(tree: &mut NullifierTree, opening: &LeafOpening) {
    for i in 0..opening.inputs.len() {
        tree.insert(opening.inputs[i].nullifier, &opening.occurrence(i));
    }
}

// ---- History ------------------------------------------------------------------

/// A state of the history that a spend proof is checked against. `size` counts
/// the entries covered, i.e. this is the state after slot `size - 1` (the
/// paper's `a = size - 1`), which gives the empty board an anchor too: a
/// genesis mint at slot 0 anchors at `size == 0`.
///
/// The anchor must predate the nullifier's first broadcast, because once any
/// copy lands the nullifier is in the accumulator and non-membership at a later
/// anchor can't be proven. So a wallet must remember the anchor of a spend it
/// has broadcast, and rebroadcast rather than re-anchor.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize)]
pub struct Anchor {
    pub size: u64,
    #[serde(with = "field_serde")]
    pub board_root: Fr,
    #[serde(with = "field_serde")]
    pub nullifier_root: Fr,
}

/// A wallet's replay of the board: the history tree `R`, the occurrence tree
/// `A`, and both roots after every slot. Deterministic and blind — every host
/// transaction goes in with no checks and no decryption, since gating insertion
/// on validity would expose which transactions are carriers. The roots a leaf
/// embeds come from here, and are never posted.
#[derive(Clone, Debug)]
pub struct History {
    board: IncrementalTree,
    occurrences: NullifierTree,
    openings: Vec<LeafOpening>,
    leaves: Vec<Fr>,
    /// `board_roots[n]`/`nullifier_roots[n]` cover the first `n` entries.
    board_roots: Vec<Fr>,
    nullifier_roots: Vec<Fr>,
    slots_by_nullifier: BTreeMap<Fr, Vec<usize>>,
}

impl History {
    pub fn new() -> Self {
        let board = IncrementalTree::new();
        let occurrences = NullifierTree::new();
        let board_roots = vec![board.root()];
        let nullifier_roots = vec![occurrences.root()];
        Self {
            board,
            occurrences,
            openings: Vec::new(),
            leaves: Vec::new(),
            board_roots,
            nullifier_roots,
            slots_by_nullifier: BTreeMap::new(),
        }
    }

    /// Replay one more entry and return its slot.
    pub fn append(&mut self, entry: &BoardEntry) -> usize {
        let slot = self.openings.len();
        let opening = LeafOpening::new(slot, entry, self.board.root(), self.occurrences.root());
        let leaf = opening.hash();
        self.board.set_leaf(slot, leaf);
        insert_inputs(&mut self.occurrences, &opening);
        for input in &opening.inputs {
            let slots = self.slots_by_nullifier.entry(input.nullifier).or_default();
            if slots.last() != Some(&slot) {
                slots.push(slot);
            }
        }
        self.openings.push(opening);
        self.leaves.push(leaf);
        self.board_roots.push(self.board.root());
        self.nullifier_roots.push(self.occurrences.root());
        slot
    }

    pub fn from_entries(entries: &[BoardEntry]) -> Self {
        let mut history = Self::new();
        for entry in entries {
            history.append(entry);
        }
        history
    }

    pub fn len(&self) -> usize {
        self.openings.len()
    }

    pub fn is_empty(&self) -> bool {
        self.openings.is_empty()
    }

    /// The state covering the first `size` entries, if it has happened yet.
    pub fn anchor_at(&self, size: usize) -> Option<Anchor> {
        Some(Anchor {
            size: size as u64,
            board_root: *self.board_roots.get(size)?,
            nullifier_root: *self.nullifier_roots.get(size)?,
        })
    }

    pub fn opening(&self, slot: usize) -> Option<&LeafOpening> {
        self.openings.get(slot)
    }

    /// Merkle path from `slot`'s leaf to the board root at `size`. O(size):
    /// this is a historical root, so the live tree's cached nodes don't apply.
    pub fn board_path(&self, slot: usize, size: usize) -> Vec<Fr> {
        merkle_path_for_index(&self.leaves[..size], slot)
    }

    /// The accumulator as it stood covering the first `size` entries, rebuilt
    /// by replaying. O(size log size), and entirely host-side.
    pub fn nullifier_tree_at(&self, size: usize) -> NullifierTree {
        let mut tree = NullifierTree::new();
        for opening in &self.openings[..size] {
            insert_inputs(&mut tree, opening);
        }
        tree
    }

    /// Occurrences of `nullifier` at slots in `from_size..before_slot`, oldest
    /// first.
    pub fn occurrences_between(&self, nullifier: Fr, from_size: usize, before_slot: usize) -> Vec<Occurrence> {
        self.slots_by_nullifier
            .get(&nullifier)
            .into_iter()
            .flatten()
            .filter(|&&slot| from_size <= slot && slot < before_slot)
            .flat_map(|&slot| self.openings[slot].occurrences_of(nullifier))
            .collect()
    }

    /// Everything a spend anchored at `size` needs to show about the parent
    /// entry at `parent_slot`, whose inputs have keys `vpks` — see
    /// [`ParentWitness`].
    pub fn parent_witness(
        &self,
        parent_slot: usize,
        public_values: &SpendPublicValues,
        vpks: &[OwnerPk],
        size: usize,
    ) -> ParentWitness {
        let leaf = self.openings[parent_slot].clone();
        let anchor_slot = public_values.anchor.size as usize;
        let before = self.nullifier_tree_at(parent_slot);
        ParentWitness {
            public_values: public_values.clone(),
            vpks: vpks.to_vec(),
            windows: leaf.inputs.iter().map(|input| before.prove_window(input.nullifier)).collect(),
            leaf,
            leaf_path: self.board_path(parent_slot, size),
            anchor_leaf: self.openings[anchor_slot].clone(),
            anchor_leaf_path: self.board_path(anchor_slot, size),
        }
    }
}

impl Default for History {
    fn default() -> Self {
        Self::new()
    }
}

// ---- Public values -------------------------------------------------------

/// The public values committed by the spend relation. They say nothing about
/// the slot the entry lands at, which the spender can't know.
///
/// `anchor` is a state before this spend was posted (the Zcash-style "anchor"):
/// the proof commits to roots that don't include itself, so it can be embedded
/// inside the ciphertext without any self-reference, and other entries landing
/// first don't invalidate it.
///
/// `output_commitments` are the coin commitments created by this spend. The
/// next spender verifies this proof recursively and checks its input coin is
/// listed here — establishing a cryptographic chain of custody.
///
/// The spender's public key is intentionally NOT included. A nullifier
/// reveals nothing about spender identity: it's a one-way hash, useful only for
/// equality-checking. `vpk_hashes` are what tie each `vsk` to its coin, so a
/// spender can't hand a recipient a fake `vpk` under which their double-spend
/// would pass for junk.
///
/// `nullifiers` and `vpk_hashes` list the real inputs only, one each, in input
/// order; proofs pad them with zeros.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize)]
pub struct SpendPublicValues {
    #[serde(with = "field_serde")]
    pub output_commitments: Vec<Fr>,
    pub anchor: Anchor,
    #[serde(with = "field_serde")]
    pub nullifiers: Vec<Fr>,
    #[serde(with = "field_serde")]
    pub vpk_hashes: Vec<Fr>,
}

impl SpendPublicValues {
    pub fn encode(&self) -> Vec<u8> {
        bincode::serialize(self).expect("SpendPublicValues is always serializable")
    }
}

// ---- Receipt -----------------------------------------------------------------

/// The recipient's off-circuit acceptance check for the carrier at `slot`,
/// whose decrypted transaction is `tx`, against the recipient's own replay.
/// The proof is checked against the anchor state; freshness against the board
/// up to the carrier's inclusion. The first validly signed spend wins.
///
/// `verify_proof` stands in for verifying `tx.spend_proof`, whose verifying
/// keys live in the circuit crates that depend on this one.
pub fn check_receipt(
    history: &History,
    slot: usize,
    entry: &BoardEntry,
    tx: &Transaction,
    verify_proof: impl FnOnce(&SpendPublicValues, &[u8]) -> bool,
) -> Result<SpendPublicValues, &'static str> {
    let opening = history.opening(slot).ok_or("carrier's slot is not in this history")?;
    if *opening != LeafOpening::new(slot, entry, opening.prev_board_root, opening.prev_nullifier_root) {
        return Err("carrier does not match this history's entry at that slot");
    }
    if tx.output_commitments != entry.output_commitments {
        return Err("decrypted transaction disagrees with the posted output commitments");
    }

    let size = tx.anchor.size as usize;
    if size > slot || history.anchor_at(size).as_ref() != Some(&tx.anchor) {
        return Err("anchor is not a real state preceding the carrier");
    }

    if opening.inputs.is_empty() || tx.vpks.len() != opening.inputs.len() {
        return Err("carrier must have one key per posted input");
    }

    let public_values = SpendPublicValues {
        output_commitments: entry.output_commitments.clone(),
        anchor: tx.anchor.clone(),
        nullifiers: opening.inputs.iter().map(|input| input.nullifier).collect(),
        vpk_hashes: tx.vpks.iter().map(hash_vpk).collect(),
    };
    if !verify_proof(&public_values, &tx.spend_proof) {
        return Err("spend proof does not verify");
    }

    // Every input must stand: one input's double-spend spoils the whole
    // carrier, since its outputs count that input's value.
    for (i, (input, vpk)) in opening.inputs.iter().zip(&tx.vpks).enumerate() {
        if !opening.signature_valid(i, vpk) {
            return Err("carrier's signature does not verify under its vpk");
        }
        let window = history.occurrences_between(input.nullifier, size, slot);
        if window.iter().any(|o| !o.is_harmless(input.nullifier, vpk, opening.outputs_hash)) {
            return Err("double-spend: a validly signed spend of different outputs came first");
        }
    }

    Ok(public_values)
}

// ---- Spend relation --------------------------------------------------------

/// What a spend shows about the entry that created its input coin, its
/// "parent": all of it opened against the spend's own anchor.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, CanonicalSerialize, CanonicalDeserialize)]
pub struct ParentWitness {
    /// The parent proof's public values. Stands in for its recursive
    /// verification, which is `circuit-spend`'s job.
    pub public_values: SpendPublicValues,
    /// One per parent input, in input order.
    #[serde(with = "field_serde")]
    pub vpks: Vec<OwnerPk>,
    pub leaf: LeafOpening,
    #[serde(with = "field_serde")]
    pub leaf_path: Vec<Fr>,
    /// The leaf right after the parent's anchor state, which embeds that
    /// state's roots. Equal to `leaf` when nothing landed in between.
    pub anchor_leaf: LeafOpening,
    #[serde(with = "field_serde")]
    pub anchor_leaf_path: Vec<Fr>,
    /// One per parent input: that serial number's window.
    pub windows: Vec<WindowWitness>,
}

/// Checks every condition of the spend relation. `circuit-spend` is this same
/// logic as a `ConstraintSynthesizer`; here it's the plain-Rust reference
/// implementation used directly by tests and as the correctness oracle circuit
/// tests are checked against. `parents` is empty only for a genesis mint, and
/// otherwise has one entry per input coin.
///
/// `nonmemberships[i]` proves input `i`'s nullifier is absent at `anchor`.
/// `anchor` itself is checked by whoever verifies the result, since only they
/// can compare it against the history they replayed: the recipient in
/// [`check_receipt`], the next spender through [`ParentWitness::anchor_leaf`].
pub fn check_spend(
    sk: &OwnerScalar,
    input_coins: &[Coin],
    output_coins: &[Coin],
    output_commitments: &[Fr],
    anchor: &Anchor,
    nonmemberships: &[NonMembershipWitness],
    parents: &[ParentWitness],
) -> Result<SpendPublicValues, &'static str> {
    if input_coins.is_empty() || input_coins.len() > MAX_INPUTS || nonmemberships.len() != input_coins.len() {
        return Err("a spend has 1 to MAX_INPUTS inputs, each with a non-membership witness");
    }
    let pk = derive_owner_pk(sk);
    if input_coins.iter().any(|coin| coin.owner_pk != pk) {
        return Err("input coin's owner does not match the spender");
    }

    let commitments: Vec<Fr> = input_coins.iter().map(Coin::commitment).collect();
    let nullifiers: Vec<Fr> = commitments.iter().map(|cm| derive_nullifier(*cm, sk)).collect();
    // The same coin twice would count its value twice, and nothing else
    // catches it: both copies are absent at the anchor.
    if (1..nullifiers.len()).any(|k| nullifiers[..k].contains(&nullifiers[k])) {
        return Err("a spend cannot consume the same coin twice");
    }

    // Double-spend guard, uniform for genesis and non-genesis. This is also
    // what enforces the anchor rule: a later anchor can't pass once a copy of
    // this nullifier has landed.
    if nullifiers.iter().zip(nonmemberships).any(|(sn, w)| !verify_nonmembership(anchor.nullifier_root, *sn, w)) {
        return Err("nullifier is already present at this anchor");
    }

    if output_coins.len() > output_commitments.len() {
        return Err("more output_coins than output_commitments");
    }
    for (coin, cn) in output_coins.iter().zip(output_commitments.iter()) {
        if &coin.commitment() != cn {
            return Err("output coin does not match its commitment");
        }
    }
    // Commitments past the real coins are padding. They must be zero, because
    // their value isn't counted below: anything else would be a spendable coin
    // conjured from nothing.
    if output_commitments[output_coins.len()..].iter().any(|cn| *cn != Fr::from(0u64)) {
        return Err("unused output slots must hold a zero commitment");
    }

    // Value conservation: Σ inputs == Σ outputs (no minting, no burning).
    let total_in: u128 = input_coins.iter().map(|c| c.value as u128).sum();
    let total_out: u128 = output_coins.iter().map(|c| c.value as u128).sum();
    if total_in != total_out {
        return Err("transaction violates value conservation: sum(inputs) must equal sum(outputs)");
    }

    if parents.is_empty() {
        // Genesis creates coins from authority (PoW) — no parent required.
        if pk != genesis_pk() {
            return Err("only the genesis key may mint without provenance");
        }
    } else if parents.len() != input_coins.len() {
        return Err("every input needs its own parent");
    } else {
        for (parent, commitment) in parents.iter().zip(&commitments) {
            check_parent(parent, *commitment, anchor)?;
        }
    }

    Ok(SpendPublicValues {
        output_commitments: output_commitments.to_vec(),
        anchor: anchor.clone(),
        nullifiers,
        vpk_hashes: commitments.iter().map(|cm| hash_vpk(&derive_coin_vpk(sk, *cm))).collect(),
    })
}

fn check_parent(parent: &ParentWitness, commitment: Fr, anchor: &Anchor) -> Result<(), &'static str> {
    let pv = &parent.public_values;
    let leaf = &parent.leaf;

    if compute_root_from_path(leaf.hash(), leaf.slot as usize, &parent.leaf_path) != anchor.board_root {
        return Err("parent entry is not in this spend's anchor state");
    }
    // Every input slot, not only the first: otherwise the leaf would bind one
    // input and the others could be double-spent unnoticed. Compared padded,
    // as the circuit sees them.
    let padded = |real: &[Fr]| -> Option<[Fr; MAX_INPUTS]> {
        let mut out = [Fr::from(0u64); MAX_INPUTS];
        out.get_mut(..real.len())?.copy_from_slice(real);
        Some(out)
    };
    if padded(&pv.nullifiers) != Some(leaf.nullifiers()) || poseidon_hash(&pv.output_commitments) != leaf.outputs_hash
    {
        return Err("parent proof disagrees with the parent entry");
    }
    if !pv.output_commitments.contains(&commitment) {
        return Err("parent does not create the input coin");
    }

    // The parent's anchor is real: the leaf right after that state, under this
    // spend's anchor, embeds exactly the roots the parent's proof was checked
    // against. The history itself vouches for them, and the anchor can't have
    // come after the parent.
    let anchor_leaf = &parent.anchor_leaf;
    if compute_root_from_path(anchor_leaf.hash(), anchor_leaf.slot as usize, &parent.anchor_leaf_path)
        != anchor.board_root
    {
        return Err("parent's anchor leaf is not in this spend's anchor state");
    }
    if anchor_leaf.slot != pv.anchor.size
        || anchor_leaf.prev_board_root != pv.anchor.board_root
        || anchor_leaf.prev_nullifier_root != pv.anchor.nullifier_root
        || pv.anchor.size > leaf.slot
    {
        return Err("parent's anchor is not a real state preceding it");
    }

    // Each of the parent's inputs must stand, as in `check_receipt`. A zero
    // serial number marks an unused slot: no real coin has one.
    for i in (0..leaf.inputs.len()).filter(|&i| leaf.inputs[i].nullifier != Fr::from(0u64)) {
        let (Some(vpk), Some(window)) = (parent.vpks.get(i), parent.windows.get(i)) else {
            return Err("parent witness needs one key and one window per parent input");
        };
        // Without this binding a dishonest parent could post a broken signature
        // so that its spend looks like junk, then double-spend the coin.
        if pv.vpk_hashes.get(i) != Some(&hash_vpk(vpk)) {
            return Err("parent's vpk does not match its proof");
        }
        if !leaf.signature_valid(i, vpk) {
            return Err("parent's signature does not verify");
        }
        if !check_window(leaf.prev_nullifier_root, leaf.inputs[i].nullifier, vpk, leaf.outputs_hash, window) {
            return Err("parent's window is not clean");
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

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

    /// Everything a spend produces: what got posted, and what a recipient
    /// decrypts plus the proof's public values.
    struct Spend {
        entry: BoardEntry,
        tx: Transaction,
        pv: SpendPublicValues,
    }

    /// Stand-in proof: the encoded public values, so `proof_ok` accepts exactly
    /// the statement the native `check_spend` certified. Real proofs arrive in
    /// `circuit-spend`.
    fn proof_ok(pv: &SpendPublicValues, proof: &[u8]) -> bool {
        pv.encode() == proof
    }

    /// Run the spend relation at the anchor covering `anchor_size` entries and
    /// build the resulting entry. `id` varies the session key, hence the
    /// ciphertext, between otherwise identical spends.
    fn spend(
        history: &History,
        sk: OwnerScalar,
        input: &Coin,
        outputs: &[Coin],
        anchor_size: usize,
        parent: Option<&ParentWitness>,
        id: u64,
    ) -> Result<Spend, &'static str> {
        let parents: Vec<ParentWitness> = parent.into_iter().cloned().collect();
        spend_inputs(history, sk, std::slice::from_ref(input), outputs, anchor_size, &parents, id)
    }

    /// [`spend`] of several input coins, one parent each (none for genesis).
    fn spend_inputs(
        history: &History,
        sk: OwnerScalar,
        inputs: &[Coin],
        outputs: &[Coin],
        anchor_size: usize,
        parents: &[ParentWitness],
        id: u64,
    ) -> Result<Spend, &'static str> {
        let anchor = history.anchor_at(anchor_size).unwrap();
        let commitments: Vec<Fr> = inputs.iter().map(Coin::commitment).collect();
        let tree = history.nullifier_tree_at(anchor_size);
        let nonmemberships: Vec<NonMembershipWitness> =
            commitments.iter().map(|cm| tree.prove_non_membership(derive_nullifier(*cm, &sk))).collect();
        let output_commitments: Vec<Fr> = outputs.iter().map(Coin::commitment).collect();
        let pv = check_spend(&sk, inputs, outputs, &output_commitments, &anchor, &nonmemberships, parents)?;

        let session_key = {
            let mut h = Sha256::new();
            h.update(id.to_le_bytes());
            h.update(EK_SALT);
            let mut out = [0u8; 32];
            out.copy_from_slice(&h.finalize());
            out
        };
        let tx = Transaction {
            id,
            note_encs: outputs.iter().enumerate().map(|(i, c)| build_note_enc(&session_key, i, c)).collect(),
            output_commitments,
            vpks: commitments.iter().map(|cm| derive_coin_vpk(&sk, *cm)).collect(),
            anchor,
            spend_proof: pv.encode(),
        };
        let entry = encrypt_tx(&tx, &commitments, &sk, &[enc_party(9).1], session_key);
        Ok(Spend { entry, tx, pv })
    }

    /// A third party's copy of `nullifier`: arbitrary everything else, and a
    /// signature that's just junk. Needs no secrets at all.
    fn junk_copy(nullifier: Fr, seed: u8) -> BoardEntry {
        BoardEntry {
            ciphertext: vec![seed; 40],
            ek_pk: [seed; 32],
            key_encs: vec![[seed; 32]],
            nullifiers: vec![nullifier],
            output_commitments: vec![Fr::from(seed as u64)],
            signatures: vec![CoinSignature { c: Fr::from(seed as u64), s: OwnerScalar::from(seed as u64) }],
        }
    }

    /// The running example: genesis (slot 0) mints 100 to Alice.
    struct World {
        history: History,
        genesis: Spend,
        alice_coin: Coin,
        alice_sk: OwnerScalar,
        bob_coin: Coin,
        carol_coin: Coin,
    }

    fn world() -> World {
        let (alice_sk, alice_pk) = owner_party(1);
        let (_, bob_pk) = owner_party(2);
        let (_, carol_pk) = owner_party(3);
        let alice_coin = coin(0xA2, 100, alice_pk);
        let mut history = History::new();
        let genesis_input = coin(0xA1, 100, genesis_pk());
        let genesis =
            spend(&history, genesis_sk(), &genesis_input, &[alice_coin.clone()], 0, None, 0).unwrap();
        history.append(&genesis.entry);
        World {
            history,
            genesis,
            alice_coin,
            alice_sk,
            bob_coin: coin(0xB1, 100, bob_pk),
            carol_coin: coin(0xC1, 100, carol_pk),
        }
    }

    impl World {
        fn parent_is_genesis(&self, anchor_size: usize) -> ParentWitness {
            self.history.parent_witness(0, &self.genesis.pv, &self.genesis.tx.vpks, anchor_size)
        }

        /// Alice spends her coin to `output`, anchored at `anchor_size`.
        fn alice_spends(&self, output: &Coin, anchor_size: usize, id: u64) -> Result<Spend, &'static str> {
            let parent = self.parent_is_genesis(anchor_size);
            spend(&self.history, self.alice_sk, &self.alice_coin, std::slice::from_ref(output), anchor_size, Some(&parent), id)
        }

        fn alice_nullifier(&self) -> Fr {
            derive_nullifier(self.alice_coin.commitment(), &self.alice_sk)
        }

        fn receipt(&self, slot: usize, s: &Spend) -> Result<SpendPublicValues, &'static str> {
            check_receipt(&self.history, slot, &s.entry, &s.tx, proof_ok)
        }

        /// Bob spends onward from the carrier at `slot`, anchored at the
        /// current state, regardless of whether he should have accepted it.
        fn bob_spends_onward(&self, slot: usize, carrier: &Spend) -> Result<Spend, &'static str> {
            let (bob_sk, _) = owner_party(2);
            let size = self.history.len();
            let parent = self.history.parent_witness(slot, &carrier.pv, &carrier.tx.vpks, size);
            spend(&self.history, bob_sk, &self.bob_coin, std::slice::from_ref(&self.carol_coin), size, Some(&parent), 100)
        }
    }

    // ---- signatures ---------------------------------------------------------

    #[test]
    fn signature_verifies_only_for_its_key_and_message() {
        let (sk, pk) = owner_party(1);
        let cm = coin(1, 5, pk).commitment();
        let vsk = derive_coin_signing_key(&sk, cm);
        let vpk = derive_coin_vpk(&sk, cm);
        let msg = Fr::from(77u64);
        let sig = sign_coin_message(&vsk, msg);

        assert!(verify_coin_signature(&vpk, msg, &sig));
        assert!(!verify_coin_signature(&vpk, msg + Fr::from(1u64), &sig));
        assert!(!verify_coin_signature(&derive_coin_vpk(&sk, cm + Fr::from(1u64)), msg, &sig));
        assert_eq!(sig, sign_coin_message(&vsk, msg), "signing must be deterministic");
    }

    #[test]
    fn signature_verification_is_total_on_junk() {
        let (sk, pk) = owner_party(1);
        let vpk = derive_coin_vpk(&sk, coin(1, 5, pk).commitment());
        let msg = Fr::from(77u64);
        // Includes the edge cases where a scalar is 0 or -1, and where both
        // parts of `s·G − c·vpk` vanish: all just `false`, never a panic.
        for (c, s) in [
            (Fr::from(0u64), OwnerScalar::from(0u64)),
            (Fr::from(1u64), OwnerScalar::from(0u64)),
            (Fr::from(0u64), OwnerScalar::from(1u64)),
            (-Fr::from(1u64), -OwnerScalar::from(1u64)),
        ] {
            assert!(!verify_coin_signature(&vpk, msg, &CoinSignature { c, s }));
        }
    }

    #[test]
    fn s_limbs_recompose_to_s() {
        let (sk, pk) = owner_party(1);
        let vsk = derive_coin_signing_key(&sk, coin(1, 5, pk).commitment());
        let sig = sign_coin_message(&vsk, Fr::from(77u64));
        let (lo, hi) = sig.s_limbs();

        let bits = |x: Fr| x.into_bigint().to_bits_le();
        assert!(bits(lo)[SIG_S_LO_BITS..].iter().all(|b| !b));
        let mut recomposed = bits(lo)[..SIG_S_LO_BITS].to_vec();
        recomposed.extend_from_slice(&bits(hi)[..768 - SIG_S_LO_BITS]);
        assert_eq!(recomposed, sig.s.into_bigint().to_bits_le());
    }

    #[test]
    fn vpk_is_per_coin_and_unrelated_to_the_nullifier() {
        let (alice_sk, alice_pk) = owner_party(1);
        let (bob_sk, _) = owner_party(2);
        let cm = coin(1, 5, alice_pk).commitment();
        let other_cm = coin(2, 5, alice_pk).commitment();

        assert_eq!(derive_coin_vpk(&alice_sk, cm), derive_coin_vpk(&alice_sk, cm));
        assert_ne!(derive_coin_vpk(&alice_sk, cm), derive_coin_vpk(&alice_sk, other_cm));
        assert_ne!(derive_coin_vpk(&alice_sk, cm), derive_coin_vpk(&bob_sk, cm));
        assert_ne!(derive_coin_signing_key(&alice_sk, cm), derive_nullifier(cm, &alice_sk));
    }

    // ---- entries ------------------------------------------------------------

    #[test]
    fn signature_covers_nullifier_outputs_and_ciphertext() {
        let w = world();
        let s = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        assert!(verify_coin_signature(&s.tx.vpks[0], s.entry.signature_message(0), &s.entry.signatures[0]));

        let tampered = |edit: &dyn Fn(&mut BoardEntry)| {
            let mut e = s.entry.clone();
            edit(&mut e);
            verify_coin_signature(&s.tx.vpks[0], e.signature_message(0), &e.signatures[0])
        };
        assert!(!tampered(&|e| e.nullifiers[0] += Fr::from(1u64)));
        assert!(!tampered(&|e| e.output_commitments[0] += Fr::from(1u64)));
        assert!(!tampered(&|e| e.ciphertext[0] ^= 1));
        assert!(!tampered(&|e| e.ek_pk[0] ^= 1));
        assert!(!tampered(&|e| e.key_encs[0][0] ^= 1));
    }

    #[test]
    fn posted_bytes_contain_no_roots_or_vpk() {
        let mut w = world();
        let s = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        w.history.append(&s.entry);
        let opening = w.history.opening(1).unwrap();

        let posted = bincode::serialize(&s.entry).unwrap();
        let contains = |needle: Vec<u8>| posted.windows(needle.len()).any(|window| window == needle);
        let fr_bytes = |x: Fr| {
            let mut out = Vec::new();
            x.serialize_compressed(&mut out).unwrap();
            out
        };
        assert!(contains(fr_bytes(s.entry.nullifiers[0])), "sanity: the encoding under test is the right one");
        assert!(!contains(fr_bytes(opening.prev_board_root)));
        assert!(!contains(fr_bytes(opening.prev_nullifier_root)));
        assert!(!contains(fr_bytes(hash_vpk(&s.tx.vpks[0]))));
        let (vx, _) = owner_pk_to_field_pair(&s.tx.vpks[0]);
        assert!(!contains(fr_bytes(vx)));
    }

    #[test]
    fn encrypt_decrypt_round_trips_for_participants_and_rejects_outsiders() {
        let w = world();
        let s = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        // `spend` always encrypts to enc_party(9).
        assert_eq!(scan_entry(&enc_party(9).0, &s.entry), Some(s.tx.clone()));
        assert_eq!(scan_entry(&enc_party(2).0, &s.entry), None);
        assert_eq!(scan_entry(&enc_party(3).0, &s.entry), None);

        let session_key = recover_session_key(&enc_party(9).0, &s.entry).unwrap();
        assert_eq!(decrypt_note(&session_key, 0, &s.tx.note_encs[0]), Some(w.bob_coin.clone()));
        assert_eq!(decrypt_note(&session_key, 1, &s.tx.note_encs[0]), None);
    }

    #[test]
    fn multi_output_tx_each_recipient_sees_only_own_note() {
        let (_, alice_pk) = owner_party(1);
        let (_, bob_pk) = owner_party(2);
        let bob_coin = coin(0xB1, 40, bob_pk);
        let alice_change = coin(0xB2, 60, alice_pk);
        let session_key = [7u8; 32];

        let bob_note = build_note_enc(&session_key, 0, &bob_coin);
        let change_note = build_note_enc(&session_key, 1, &alice_change);

        assert_eq!(decrypt_note(&session_key, 0, &bob_note), Some(bob_coin));
        assert_eq!(decrypt_note(&session_key, 1, &change_note), Some(alice_change));
        assert_eq!(decrypt_note(&session_key, 1, &bob_note), None);
        assert_eq!(decrypt_note(&session_key, 0, &change_note), None);
    }

    // ---- history and the occurrence accumulator -----------------------------

    #[test]
    fn history_tracks_roots_per_slot_and_opens_against_old_anchors() {
        let mut w = world();
        let sn = w.alice_nullifier();
        w.history.append(&junk_copy(sn, 1));
        w.history.append(&junk_copy(Fr::from(5u64), 2));

        for slot in 0..3 {
            let opening = w.history.opening(slot).unwrap();
            let before = w.history.anchor_at(slot).unwrap();
            assert_eq!(opening.prev_board_root, before.board_root);
            assert_eq!(opening.prev_nullifier_root, before.nullifier_root);
            // Under every anchor that covers it, not only the latest.
            for size in (slot + 1)..=3 {
                let path = w.history.board_path(slot, size);
                assert_eq!(
                    compute_root_from_path(opening.hash(), slot, &path),
                    w.history.anchor_at(size).unwrap().board_root,
                );
            }
        }
        assert!(w.history.anchor_at(3).is_some());
        assert!(w.history.anchor_at(4).is_none());
        // A copy changes the accumulator root like anything else does.
        assert_ne!(w.history.anchor_at(1).unwrap().nullifier_root, w.history.anchor_at(2).unwrap().nullifier_root);
        for size in 0..=3 {
            assert_eq!(
                w.history.nullifier_tree_at(size).root(),
                w.history.anchor_at(size).unwrap().nullifier_root,
            );
        }
    }

    #[test]
    fn replay_is_order_sensitive_so_wallets_must_agree_on_order() {
        let a = junk_copy(Fr::from(5u64), 1);
        let b = junk_copy(Fr::from(5u64), 2);
        assert_eq!(
            History::from_entries(&[a.clone(), b.clone()]).anchor_at(2),
            History::from_entries(&[a.clone(), b.clone()]).anchor_at(2),
        );
        assert_ne!(
            History::from_entries(&[a.clone(), b.clone()]).anchor_at(2),
            History::from_entries(&[b, a]).anchor_at(2),
        );
    }

    /// Wallets replay every host transaction blindly, so no entry may be able
    /// to panic one or wedge the accumulator: not empty fields, and not serial
    /// numbers colliding with the tree's own sentinels.
    #[test]
    fn blind_replay_survives_adversarial_entries() {
        let empty = |nullifier| BoardEntry {
            ciphertext: vec![],
            ek_pk: [0; 32],
            key_encs: vec![],
            nullifiers: vec![nullifier],
            output_commitments: vec![],
            signatures: vec![CoinSignature { c: Fr::from(0u64), s: OwnerScalar::from(0u64) }],
        };
        let sentinel_low = Fr::from(0u64);
        let sentinel_high = max_nullifier();
        let mut history = History::new();
        for nullifier in [sentinel_low, sentinel_high, sentinel_low, sentinel_high, Fr::from(5u64)] {
            history.append(&empty(nullifier));
        }
        // Malformed shapes: no inputs, missing signatures, too many inputs.
        let mut odd = empty(Fr::from(7u64));
        odd.nullifiers = vec![];
        history.append(&odd);
        odd.nullifiers = vec![Fr::from(8u64); MAX_INPUTS + 2];
        odd.signatures = vec![];
        history.append(&odd);
        assert_eq!(history.opening(history.len() - 1).unwrap().inputs.len(), MAX_INPUTS);

        let tree = history.nullifier_tree_at(history.len());
        assert_eq!(tree.root(), history.anchor_at(history.len()).unwrap().nullifier_root);
        for member in [sentinel_low, sentinel_high, Fr::from(5u64)] {
            assert!(verify_occurrences(tree.root(), member, &tree.prove_occurrences(member).unwrap()));
        }
        let absent = Fr::from(6u64);
        assert!(verify_nonmembership(tree.root(), absent, &tree.prove_non_membership(absent)));
    }

    #[test]
    fn duplicate_insert_extends_the_chain_and_moves_the_root() {
        let sn = Fr::from(5u64);
        let first = LeafOpening::new(0, &junk_copy(sn, 1), Fr::from(0u64), Fr::from(0u64)).occurrence(0);
        let second = LeafOpening::new(0, &junk_copy(sn, 2), Fr::from(0u64), Fr::from(0u64)).occurrence(0);

        let mut tree = NullifierTree::new();
        let empty = tree.root();
        let w = tree.prove_non_membership(sn);
        assert!(verify_nonmembership(empty, sn, &w));
        assert!(tree.prove_occurrences(sn).is_none());

        let root1 = tree.insert(sn, &first);
        assert_ne!(root1, empty);
        let w1 = tree.prove_occurrences(sn).unwrap();
        assert_eq!(w1.occurrences, vec![first.clone()]);
        assert!(verify_occurrences(root1, sn, &w1));

        let root2 = tree.insert(sn, &second);
        assert_ne!(root2, root1, "a duplicate must not be a no-op any more");
        let w2 = tree.prove_occurrences(sn).unwrap();
        assert_eq!(w2.occurrences, vec![first.clone(), second.clone()]);
        assert!(verify_occurrences(root2, sn, &w2));

        // Membership still fails non-membership, duplicates or not.
        assert!(!verify_nonmembership(root2, sn, &tree.prove_non_membership(sn)));

        // Neither end of the chain can be dropped, or the order changed.
        for occurrences in [vec![second.clone()], vec![first.clone()], vec![second, first], vec![]] {
            let lying = WindowWitness { occurrences, ..w2.clone() };
            assert!(!verify_occurrences(root2, sn, &lying));
        }
        assert!(!verify_occurrences(root2, sn + Fr::from(1u64), &w2));
    }

    #[test]
    fn inserting_a_neighbour_keeps_a_chain_openable() {
        let sn = Fr::from(5u64);
        let occ = LeafOpening::new(0, &junk_copy(sn, 1), Fr::from(0u64), Fr::from(0u64)).occurrence(0);
        let mut tree = NullifierTree::new();
        tree.insert(sn, &occ);
        // Lands right after `sn`, making `sn`'s leaf the low leaf that gets
        // its `next_*` rewritten. Its chain has to survive that.
        let root = tree.insert(Fr::from(6u64), &occ);
        assert_eq!(tree.prove_occurrences(sn).unwrap().occurrences, vec![occ]);
        assert!(verify_occurrences(root, sn, &tree.prove_occurrences(sn).unwrap()));
        let gap = Fr::from(1000u64);
        assert!(verify_nonmembership(root, gap, &tree.prove_non_membership(gap)));
    }

    // ---- the honest path ----------------------------------------------------

    #[test]
    fn demo_chain_is_valid_end_to_end() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        let slot = w.history.append(&alice.entry);
        assert_eq!(w.receipt(slot, &alice).unwrap(), alice.pv);

        let bob = w.bob_spends_onward(slot, &alice).unwrap();
        let bob_slot = w.history.append(&bob.entry);
        assert_eq!(w.receipt(bob_slot, &bob).unwrap(), bob.pv);
    }

    /// The reviewer's question: history changes between proving and inclusion.
    #[test]
    fn unrelated_entries_landing_first_do_not_invalidate_a_proof() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        w.history.append(&junk_copy(Fr::from(5u64), 1));
        w.history.append(&junk_copy(Fr::from(6u64), 2));
        let slot = w.history.append(&alice.entry);
        w.receipt(slot, &alice).unwrap();
        w.bob_spends_onward(slot, &alice).unwrap();
    }

    // ---- the copy attack ----------------------------------------------------

    /// The reviewers' attack: a third party gets Alice's serial number ordered
    /// before her carrier. It must neither stop Bob accepting nor spending.
    #[test]
    fn copied_serial_number_is_ignored() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        w.history.append(&junk_copy(w.alice_nullifier(), 1));
        let slot = w.history.append(&alice.entry);

        w.receipt(slot, &alice).expect("Bob must accept despite the copy");
        let bob = w.bob_spends_onward(slot, &alice).expect("Bob must be able to spend despite the copy");
        let bob_slot = w.history.append(&bob.entry);
        w.receipt(bob_slot, &bob).unwrap();
    }

    #[test]
    fn copy_can_reuse_real_public_fields_and_still_is_just_junk() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        // Everything public from the real carrier, with its genuine signature,
        // but a payload of the attacker's own: the signature covers the
        // ciphertext, and different outputs would need a new signature.
        let mut copy = alice.entry.clone();
        copy.ciphertext = vec![1; 40];
        copy.output_commitments = vec![Fr::from(999u64)];
        w.history.append(&copy);
        let slot = w.history.append(&alice.entry);

        w.receipt(slot, &alice).unwrap();
        w.bob_spends_onward(slot, &alice).unwrap();
    }

    #[test]
    fn verbatim_replay_of_the_carrier_is_the_same_spend() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        let first = w.history.append(&alice.entry);
        let second = w.history.append(&alice.entry);
        w.receipt(first, &alice).unwrap();
        w.receipt(second, &alice).unwrap();
        w.bob_spends_onward(second, &alice).unwrap();
    }

    /// Anchor rule: once a copy lands, only the spend's original anchor can
    /// work. So wallets rebroadcast rather than re-anchor.
    #[test]
    fn anchor_after_a_copy_cannot_prove_freshness_but_the_original_can() {
        let mut w = world();
        w.history.append(&junk_copy(w.alice_nullifier(), 1));
        assert_eq!(
            w.alice_spends(&w.bob_coin, 2, 1).err(),
            Some("nullifier is already present at this anchor"),
        );
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        let slot = w.history.append(&alice.entry);
        w.receipt(slot, &alice).unwrap();
    }

    /// An honest re-prove and rebroadcast differs in ciphertext, not outputs.
    #[test]
    fn honest_re_prove_is_the_same_spend() {
        let mut w = world();
        let first = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        let second = w.alice_spends(&w.bob_coin, 1, 2).unwrap();
        assert_ne!(entry_ciphertext_commitment(&first.entry), entry_ciphertext_commitment(&second.entry));
        w.history.append(&first.entry);
        let slot = w.history.append(&second.entry);
        w.receipt(slot, &second).unwrap();
        w.bob_spends_onward(slot, &second).unwrap();
    }

    // ---- double-spends ------------------------------------------------------

    /// Two validly signed spends of one coin: first one wins, at both the
    /// recipient and the next spender, even though both share an anchor.
    #[test]
    fn first_validly_signed_spend_wins() {
        let mut w = world();
        let to_bob = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        let to_carol = w.alice_spends(&w.carol_coin, 1, 2).unwrap();
        let bob_slot = w.history.append(&to_bob.entry);
        let carol_slot = w.history.append(&to_carol.entry);

        w.receipt(bob_slot, &to_bob).expect("first spend stands");
        assert_eq!(
            w.receipt(carol_slot, &to_carol).err(),
            Some("double-spend: a validly signed spend of different outputs came first"),
        );

        w.bob_spends_onward(bob_slot, &to_bob).expect("first spend's coin stays spendable");

        // A recipient ignoring the rejection still can't spend onward.
        let (carol_sk, _) = owner_party(3);
        let size = w.history.len();
        let parent = w.history.parent_witness(carol_slot, &to_carol.pv, &to_carol.tx.vpks, size);
        let err = spend(&w.history, carol_sk, &w.carol_coin, &[coin(0xD1, 100, owner_party(4).1)], size, Some(&parent), 3);
        assert_eq!(err.err(), Some("parent's window is not clean"));
    }

    #[test]
    fn spending_again_after_inclusion_fails_at_a_fresh_anchor() {
        let mut w = world();
        let to_bob = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        w.history.append(&to_bob.entry);
        assert_eq!(
            w.alice_spends(&w.carol_coin, 2, 2).err(),
            Some("nullifier is already present at this anchor"),
        );
    }

    /// Hiding a double-spend behind a broken signature: the first spend posts a
    /// bad `σ` so it would count as junk later. So the broken one must itself
    /// be unusable, by the recipient and by anyone spending onward.
    #[test]
    fn invalid_parent_signature_is_rejected() {
        let mut w = world();
        let mut alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        alice.entry.signatures[0] = CoinSignature { c: Fr::from(1u64), s: OwnerScalar::from(1u64) };
        let slot = w.history.append(&alice.entry);

        assert_eq!(
            w.receipt(slot, &alice).err(),
            Some("carrier's signature does not verify under its vpk"),
        );
        assert_eq!(w.bob_spends_onward(slot, &alice).err(), Some("parent's signature does not verify"));
    }

    /// `vpk` comes from the sender, so it has to be pinned by the proof.
    #[test]
    fn fake_vpk_is_rejected() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        let slot = w.history.append(&alice.entry);
        let fake_vpk = owner_party(7).1;

        let mut lying_tx = alice.tx.clone();
        lying_tx.vpks = vec![fake_vpk];
        assert_eq!(
            check_receipt(&w.history, slot, &alice.entry, &lying_tx, proof_ok).err(),
            Some("spend proof does not verify"),
        );

        let (bob_sk, _) = owner_party(2);
        let size = w.history.len();
        let mut parent = w.history.parent_witness(slot, &alice.pv, &alice.tx.vpks, size);
        parent.vpks = vec![fake_vpk];
        let err = spend(&w.history, bob_sk, &w.bob_coin, &[w.carol_coin.clone()], size, Some(&parent), 3);
        assert_eq!(err.err(), Some("parent's vpk does not match its proof"));
    }

    // ---- no cap on copies ----------------------------------------------------

    /// No number of copies makes a coin unspendable; they only cost its next
    /// spender one fold step each.
    #[test]
    fn any_number_of_copies_is_tolerated() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        for i in 0..5 {
            w.history.append(&junk_copy(w.alice_nullifier(), i + 1));
        }
        let slot = w.history.append(&alice.entry);
        w.receipt(slot, &alice).unwrap();
        w.bob_spends_onward(slot, &alice).unwrap();
    }

    #[test]
    fn copies_after_the_carrier_do_not_count_against_it() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        let slot = w.history.append(&alice.entry);
        for i in 0..3 {
            w.history.append(&junk_copy(w.alice_nullifier(), i as u8 + 1));
        }
        w.receipt(slot, &alice).unwrap();
        w.bob_spends_onward(slot, &alice).unwrap();
    }

    // ---- check_spend's parent checks ----------------------------------------

    #[test]
    fn window_witness_must_match_the_state_before_the_parent() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        w.history.append(&junk_copy(w.alice_nullifier(), 1));
        let slot = w.history.append(&alice.entry);
        let size = w.history.len();
        let (bob_sk, _) = owner_party(2);
        let onward = |parent: &ParentWitness| {
            spend(&w.history, bob_sk, &w.bob_coin, &[w.carol_coin.clone()], size, Some(parent), 3).err()
        };
        let parent = w.history.parent_witness(slot, &alice.pv, &alice.tx.vpks, size);
        assert_eq!(onward(&parent), None);

        // Hiding the copy: claim an empty window using the pre-copy tree.
        let mut hiding = parent.clone();
        hiding.windows[0] = w.history.nullifier_tree_at(1).prove_window(w.alice_nullifier());
        assert_eq!(onward(&hiding), Some("parent's window is not clean"));

        // Dropping the copy from the opened chain.
        let mut dropping = parent;
        assert!(!dropping.windows[0].occurrences.is_empty());
        dropping.windows[0].occurrences.clear();
        assert_eq!(onward(&dropping), Some("parent's window is not clean"));
    }

    #[test]
    fn parent_anchor_must_be_real_and_precede_the_parent() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        let slot = w.history.append(&alice.entry);
        let size = w.history.len();
        let (bob_sk, _) = owner_party(2);
        let onward = |parent: &ParentWitness| {
            spend(&w.history, bob_sk, &w.bob_coin, &[w.carol_coin.clone()], size, Some(parent), 3).err()
        };

        // The parent's proof claims a nullifier root that never existed.
        let mut fake_root = w.history.parent_witness(slot, &alice.pv, &alice.tx.vpks, size);
        fake_root.public_values.anchor.nullifier_root += Fr::from(1u64);
        assert_eq!(onward(&fake_root), Some("parent's anchor is not a real state preceding it"));

        // A real leaf, but the wrong one for the claimed anchor.
        let mut wrong_leaf = w.history.parent_witness(slot, &alice.pv, &alice.tx.vpks, size);
        wrong_leaf.anchor_leaf = w.history.opening(0).unwrap().clone();
        wrong_leaf.anchor_leaf_path = w.history.board_path(0, size);
        assert_eq!(onward(&wrong_leaf), Some("parent's anchor is not a real state preceding it"));

        // An anchor from after the parent's own slot: the leaf embedding it
        // exists, but a proof anchored there says nothing about the window.
        let later = junk_copy(Fr::from(5u64), 1);
        w.history.append(&later);
        let size = w.history.len();
        let mut parent = w.history.parent_witness(slot, &alice.pv, &alice.tx.vpks, size);
        parent.public_values.anchor = w.history.anchor_at(2).unwrap();
        parent.anchor_leaf = w.history.opening(2).unwrap().clone();
        parent.anchor_leaf_path = w.history.board_path(2, size);
        let err = spend(&w.history, bob_sk, &w.bob_coin, &[w.carol_coin.clone()], size, Some(&parent), 3);
        assert_eq!(err.err(), Some("parent's anchor is not a real state preceding it"));
    }

    #[test]
    fn parent_must_be_under_the_spends_anchor_and_create_the_coin() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        let slot = w.history.append(&alice.entry);
        let size = w.history.len();
        let (bob_sk, _) = owner_party(2);

        // Anchored at a state from before the parent existed.
        let parent = w.history.parent_witness(slot, &alice.pv, &alice.tx.vpks, size);
        let err = spend(&w.history, bob_sk, &w.bob_coin, &[w.carol_coin.clone()], slot, Some(&parent), 3);
        assert_eq!(err.err(), Some("parent entry is not in this spend's anchor state"));

        // A coin the parent never created.
        let parent = w.history.parent_witness(slot, &alice.pv, &alice.tx.vpks, size);
        let phantom = coin(0xEE, 100, owner_party(2).1);
        let err = spend(&w.history, bob_sk, &phantom, &[w.carol_coin.clone()], size, Some(&parent), 3);
        assert_eq!(err.err(), Some("parent does not create the input coin"));
    }

    // ---- check_receipt's own checks ------------------------------------------

    #[test]
    fn receipt_rejects_bad_anchor_proof_or_mismatched_carrier() {
        let mut w = world();
        let alice = w.alice_spends(&w.bob_coin, 1, 1).unwrap();
        let slot = w.history.append(&alice.entry);
        const BAD_ANCHOR: &str = "anchor is not a real state preceding the carrier";

        let mut fake_root = alice.tx.clone();
        fake_root.anchor.board_root += Fr::from(1u64);
        assert_eq!(check_receipt(&w.history, slot, &alice.entry, &fake_root, proof_ok).err(), Some(BAD_ANCHOR));

        let mut after_carrier = alice.tx.clone();
        after_carrier.anchor = w.history.anchor_at(slot + 1).unwrap();
        assert_eq!(check_receipt(&w.history, slot, &alice.entry, &after_carrier, proof_ok).err(), Some(BAD_ANCHOR));

        assert_eq!(
            check_receipt(&w.history, slot, &alice.entry, &alice.tx, |_, _| false).err(),
            Some("spend proof does not verify"),
        );

        // Wrong slot, unknown slot, and a tampered carrier.
        assert_eq!(
            check_receipt(&w.history, 0, &alice.entry, &alice.tx, proof_ok).err(),
            Some("carrier does not match this history's entry at that slot"),
        );
        assert_eq!(
            check_receipt(&w.history, 9, &alice.entry, &alice.tx, proof_ok).err(),
            Some("carrier's slot is not in this history"),
        );
        let mut other_outputs = alice.tx.clone();
        other_outputs.output_commitments = vec![Fr::from(1u64)];
        assert_eq!(
            check_receipt(&w.history, slot, &alice.entry, &other_outputs, proof_ok).err(),
            Some("decrypted transaction disagrees with the posted output commitments"),
        );
    }

    // ---- the base relation ---------------------------------------------------

    #[test]
    fn rejects_wrong_secret_key() {
        let w = world();
        let (mallory_sk, _) = owner_party(5);
        let parent = w.parent_is_genesis(1);
        let err = spend(&w.history, mallory_sk, &w.alice_coin, &[w.bob_coin.clone()], 1, Some(&parent), 1);
        assert_eq!(err.err(), Some("input coin's owner does not match the spender"));
    }

    #[test]
    fn rejects_minting_without_the_genesis_key() {
        let w = world();
        let err = spend(&w.history, w.alice_sk, &w.alice_coin, &[w.bob_coin.clone()], 1, None, 1);
        assert_eq!(err.err(), Some("only the genesis key may mint without provenance"));
    }

    /// A commitment in a slot with no coin behind it would be spendable later
    /// without ever having counted towards conservation.
    #[test]
    fn rejects_a_phantom_commitment_in_an_unused_output_slot() {
        let w = world();
        let anchor = w.history.anchor_at(1).unwrap();
        let commitment = w.alice_coin.commitment();
        let nonmembership = w.history.nullifier_tree_at(1).prove_non_membership(w.alice_nullifier());
        let parent = w.parent_is_genesis(1);
        let check = |padding: Fr| {
            check_spend(
                &w.alice_sk,
                std::slice::from_ref(&w.alice_coin),
                std::slice::from_ref(&w.bob_coin),
                &[w.bob_coin.commitment(), padding],
                &anchor,
                std::slice::from_ref(&nonmembership),
                std::slice::from_ref(&parent),
            )
        };
        assert!(check(Fr::from(0u64)).is_ok());
        assert_eq!(check(commitment).err(), Some("unused output slots must hold a zero commitment"));
    }

    // ---- several inputs -------------------------------------------------------

    /// Genesis mints a second coin to Alice at slot 1, so she holds two coins
    /// from two different parents.
    #[cfg(feature = "two-inputs")]
    struct TwoCoins {
        w: World,
        second_mint: Spend,
        second_coin: Coin,
    }

    #[cfg(feature = "two-inputs")]
    impl TwoCoins {
        fn new() -> Self {
            let mut w = world();
            let second_coin = coin(0xA3, 50, owner_party(1).1);
            let second_mint =
                spend(&w.history, genesis_sk(), &coin(0xA4, 50, genesis_pk()), &[second_coin.clone()], 1, None, 50)
                    .unwrap();
            w.history.append(&second_mint.entry);
            Self { w, second_mint, second_coin }
        }

        fn second_nullifier(&self) -> Fr {
            derive_nullifier(self.second_coin.commitment(), &self.w.alice_sk)
        }

        /// Alice spends both coins (150) to `output`, anchored at `anchor_size`.
        fn alice_spends_both(&self, output: &Coin, anchor_size: usize, id: u64) -> Result<Spend, &'static str> {
            let h = &self.w.history;
            let parents = [
                h.parent_witness(0, &self.w.genesis.pv, &self.w.genesis.tx.vpks, anchor_size),
                h.parent_witness(1, &self.second_mint.pv, &self.second_mint.tx.vpks, anchor_size),
            ];
            let inputs = [self.w.alice_coin.clone(), self.second_coin.clone()];
            spend_inputs(h, self.w.alice_sk, &inputs, std::slice::from_ref(output), anchor_size, &parents, id)
        }

        fn bob_coin(&self) -> Coin {
            coin(0xB1, 150, owner_party(2).1)
        }

        /// Bob spends onward from the two-input carrier at `slot`.
        fn bob_spends_onward(&self, slot: usize, carrier: &Spend) -> Result<Spend, &'static str> {
            let size = self.w.history.len();
            let parent = self.w.history.parent_witness(slot, &carrier.pv, &carrier.tx.vpks, size);
            let to_carol = coin(0xC1, 150, owner_party(3).1);
            spend(&self.w.history, owner_party(2).0, &self.bob_coin(), &[to_carol], size, Some(&parent), 100)
        }
    }

    #[test]
    #[cfg(feature = "two-inputs")]
    fn two_input_spend_is_valid_end_to_end() {
        let mut t = TwoCoins::new();
        let alice = t.alice_spends_both(&t.bob_coin(), 2, 1).unwrap();
        assert_eq!(alice.entry.nullifiers.len(), 2);
        assert_eq!(alice.entry.signatures.len(), 2);
        let slot = t.w.history.append(&alice.entry);
        assert_eq!(check_receipt(&t.w.history, slot, &alice.entry, &alice.tx, proof_ok).unwrap(), alice.pv);
        let bob = t.bob_spends_onward(slot, &alice).unwrap();
        let bob_slot = t.w.history.append(&bob.entry);
        check_receipt(&t.w.history, bob_slot, &bob.entry, &bob.tx, proof_ok).unwrap();
    }

    #[test]
    #[cfg(feature = "two-inputs")]
    fn the_same_coin_twice_is_rejected() {
        let w = world();
        let parent = w.parent_is_genesis(1);
        let inputs = [w.alice_coin.clone(), w.alice_coin.clone()];
        let err = spend_inputs(&w.history, w.alice_sk, &inputs, &[coin(0xB1, 200, owner_party(2).1)], 1, &[parent.clone(), parent], 1);
        assert_eq!(err.err(), Some("a spend cannot consume the same coin twice"));
    }

    #[test]
    #[cfg(feature = "two-inputs")]
    fn every_input_needs_its_own_parent() {
        let t = TwoCoins::new();
        let h = &t.w.history;
        let only_one = [h.parent_witness(0, &t.w.genesis.pv, &t.w.genesis.tx.vpks, 2)];
        let inputs = [t.w.alice_coin.clone(), t.second_coin.clone()];
        let err = spend_inputs(h, t.w.alice_sk, &inputs, &[t.bob_coin()], 2, &only_one, 1);
        assert_eq!(err.err(), Some("every input needs its own parent"));
    }

    /// A double-spend of the *second* input must spoil the carrier as surely as
    /// one of the first: its outputs count both inputs' value.
    #[test]
    #[cfg(feature = "two-inputs")]
    fn double_spend_of_the_second_input_is_caught() {
        let mut t = TwoCoins::new();
        // Both proved at anchor 2, so both pass non-membership.
        let both = t.alice_spends_both(&t.bob_coin(), 2, 1).unwrap();
        let parent = t.w.history.parent_witness(1, &t.second_mint.pv, &t.second_mint.tx.vpks, 2);
        let second_alone =
            spend(&t.w.history, t.w.alice_sk, &t.second_coin, &[coin(0xC2, 50, owner_party(3).1)], 2, Some(&parent), 2)
                .unwrap();
        t.w.history.append(&second_alone.entry);
        let slot = t.w.history.append(&both.entry);

        assert_eq!(
            check_receipt(&t.w.history, slot, &both.entry, &both.tx, proof_ok).err(),
            Some("double-spend: a validly signed spend of different outputs came first"),
        );
        assert_eq!(t.bob_spends_onward(slot, &both).err(), Some("parent's window is not clean"));
    }

    #[test]
    #[cfg(feature = "two-inputs")]
    fn copies_of_the_second_inputs_serial_number_are_ignored() {
        let mut t = TwoCoins::new();
        let alice = t.alice_spends_both(&t.bob_coin(), 2, 1).unwrap();
        for seed in 0..3 {
            t.w.history.append(&junk_copy(t.second_nullifier(), seed + 1));
        }
        let slot = t.w.history.append(&alice.entry);
        check_receipt(&t.w.history, slot, &alice.entry, &alice.tx, proof_ok).unwrap();
        let bob = t.bob_spends_onward(slot, &alice).unwrap();
        let bob_slot = t.w.history.append(&bob.entry);
        check_receipt(&t.w.history, bob_slot, &bob.entry, &bob.tx, proof_ok).unwrap();
    }

    /// A copy that reposts only the first input, verbatim, with the real
    /// ciphertext and outputs: harmless as a copy, and useless as a parent,
    /// since the leaf no longer matches the proof's serial numbers.
    #[test]
    #[cfg(feature = "two-inputs")]
    fn a_carrier_with_an_input_dropped_is_no_parent() {
        let mut t = TwoCoins::new();
        let alice = t.alice_spends_both(&t.bob_coin(), 2, 1).unwrap();
        let mut truncated = alice.entry.clone();
        truncated.nullifiers.truncate(1);
        truncated.signatures.truncate(1);
        let copy_slot = t.w.history.append(&truncated);
        let slot = t.w.history.append(&alice.entry);

        assert_eq!(
            check_receipt(&t.w.history, copy_slot, &truncated, &alice.tx, proof_ok).err(),
            Some("carrier must have one key per posted input"),
        );
        assert_eq!(t.bob_spends_onward(copy_slot, &alice).err(), Some("parent proof disagrees with the parent entry"));
        check_receipt(&t.w.history, slot, &alice.entry, &alice.tx, proof_ok).unwrap();
        t.bob_spends_onward(slot, &alice).unwrap();
    }

    #[test]
    #[cfg(feature = "two-inputs")]
    fn parent_witness_must_cover_every_parent_input() {
        let mut t = TwoCoins::new();
        let alice = t.alice_spends_both(&t.bob_coin(), 2, 1).unwrap();
        let slot = t.w.history.append(&alice.entry);
        let size = t.w.history.len();
        let onward = |parent: &ParentWitness| {
            let to_carol = coin(0xC1, 150, owner_party(3).1);
            spend(&t.w.history, owner_party(2).0, &t.bob_coin(), &[to_carol], size, Some(parent), 3).err()
        };
        let parent = t.w.history.parent_witness(slot, &alice.pv, &alice.tx.vpks, size);

        let mut one_key = parent.clone();
        one_key.vpks.truncate(1);
        assert_eq!(onward(&one_key), Some("parent witness needs one key and one window per parent input"));

        let mut swapped = parent.clone();
        swapped.vpks.swap(0, 1);
        assert_eq!(onward(&swapped), Some("parent's vpk does not match its proof"));

        // A proof claiming only the first input can't stand for this entry.
        let mut one_input = parent;
        one_input.public_values.nullifiers.truncate(1);
        assert_eq!(onward(&one_input), Some("parent proof disagrees with the parent entry"));
    }

    #[test]
    fn rejects_value_conservation_violation() {
        let w = world();
        let too_much = coin(0xB1, 101, owner_party(2).1);
        assert_eq!(
            w.alice_spends(&too_much, 1, 1).err(),
            Some("transaction violates value conservation: sum(inputs) must equal sum(outputs)"),
        );
    }

    #[test]
    fn nullifier_tree_insert_cost_does_not_grow_with_tree_size() {
        // Regression test for an earlier version with an O(n) `find_low_leaf_index`
        // (linear scan) and a `root()` that rehashed the whole tree from scratch:
        // that made `insert` cost scale with current tree size, turning a full
        // replay (which calls `insert` in a loop) into O(k²) — catastrophic once
        // the board has hundreds of thousands of entries. The incremental version
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
        let occ = LeafOpening::new(0, &junk_copy(value(0), 1), Fr::from(0u64), Fr::from(0u64)).occurrence(0);

        let mut tree = NullifierTree::new();
        let batch = 500u32;
        let t = std::time::Instant::now();
        for i in 0..batch {
            tree.insert(value(i), &occ);
        }
        let small_per_insert = t.elapsed() / batch;

        // Grow the tree 8x larger, then time an equal-sized batch again.
        for i in batch..(batch * 8) {
            tree.insert(value(i), &occ);
        }
        let t = std::time::Instant::now();
        for i in (batch * 8)..(batch * 9) {
            tree.insert(value(i), &occ);
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
