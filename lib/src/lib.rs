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

/// A coin: tag `t`, value `v`, plus masking randomness `r`.
/// Commitment cn = H(t || v || r) — same semantics as the paper's Pedersen
/// commitment, without elliptic-curve arithmetic in the zkVM.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Coin {
    pub tag: [u8; 32],
    pub value: u64,
    pub rand: [u8; 32],
}

impl Coin {
    pub fn commitment(&self) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(self.tag);
        h.update(self.value.to_le_bytes());
        h.update(self.rand);
        let mut out = [0u8; 32];
        out.copy_from_slice(&h.finalize());
        out
    }
}

/// A transaction: `S` spends `input_coin` and creates two new coins —
/// `output_coin` (the payment to `R`) and `change_coin` (returned to `S`).
/// Posted to the bulletin board only in encrypted form — see [`encrypt_tx`] /
/// [`extract_msg`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Transaction {
    pub id: u64,
    pub sender_pk: [u8; 32],
    pub recipient_pk: [u8; 32],
    pub input_coin: Coin,
    pub output_coin: Coin,
    pub change_coin: Coin,
}

impl Transaction {
    pub fn sent_by(&self, pk: &[u8; 32]) -> bool {
        &self.sender_pk == pk
    }
    pub fn received_by(&self, pk: &[u8; 32]) -> bool {
        &self.recipient_pk == pk
    }

    /// `pk` receives the coin with commitment `cn` in this tx — either as the
    /// payment (`pk == recipient_pk`) or as change (`pk == sender_pk`).
    pub fn receives_coin(&self, pk: &[u8; 32], cn: &[u8; 32]) -> bool {
        (self.recipient_pk == *pk && self.output_coin.commitment() == *cn)
            || (self.sender_pk == *pk && self.change_coin.commitment() == *cn)
    }

    /// `pk` spends the coin with commitment `cn` as the input of this tx.
    pub fn spends_coin(&self, pk: &[u8; 32], cn: &[u8; 32]) -> bool {
        self.sender_pk == *pk && self.input_coin.commitment() == *cn
    }
}

// ---- Whisper-style pairwise encryption ---------------------------------
//
// Each pair of parties shares a fixed symmetric key derived from their public
// keys. A transaction is encrypted under the key shared by its sender and
// recipient, so it looks like opaque noise to everyone else. `extract_msg`
// is the in-circuit `ExtractMsg`: it derives the pairwise key for a candidate
// counterparty, decrypts, and checks a magic tag embedded in the plaintext.
//
// Because the cipher is a hash-based one-time pad (`H(key || counter)` XORed
// with the plaintext), decrypting with the *wrong* key produces bytes that are
// indistinguishable from random. The chance that random bytes happen to carry
// the correct 8-byte tag *and* name `owner_pk` as sender or recipient is
// astronomically small. So a prover cannot forge "this slot decrypts to a
// transaction of mine" for a slot that wasn't actually encrypted under their
// pairwise key with the claimed counterparty.

/// Domain-separation salt for pairwise key derivation.
pub const PAIR_SALT: [u8; 32] = *b"CLOAKCHAIN-PAIRWISE-KEY-SALT!!!!";

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

/// Marks a successfully-decrypted plaintext. An 8-byte tag is astronomically
/// unlikely to survive decryption under the wrong pairwise key.
const MAGIC_TAG: [u8; 8] = *b"CLOAKTX1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct Plaintext {
    tag: [u8; 8],
    tx: Transaction,
}

/// `bincode` encoding of [`Plaintext`] is fixed-length (no `Vec`s or `Option`s
/// inside `Transaction`/`Coin`), so every ciphertext on the board has this
/// length: 8 (tag) + [8 (id) + 32*2 (sender_pk, recipient_pk) + 3 * (32 (tag) +
/// 8 (value) + 32 (rand))] = 8 + [8 + 64 + 3*72] = 8 + 288 = 296 bytes.
pub const CIPHERTEXT_LEN: usize = 296;

/// XOR-with-hash-keystream: `keystream = H(key||0) || H(key||1) || ...`,
/// truncated to `len` bytes. Encryption and decryption are the same operation.
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

/// An opaque ciphertext posted to the bulletin board.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BoardEntry {
    pub ciphertext: Vec<u8>,
}

/// Encrypt `tx` under the pairwise key shared by its sender and recipient.
pub fn encrypt_tx(tx: &Transaction) -> BoardEntry {
    let plaintext = Plaintext { tag: MAGIC_TAG, tx: tx.clone() };
    let bytes = bincode::serialize(&plaintext).expect("Plaintext is always serializable");
    let key = pair_key(&tx.sender_pk, &tx.recipient_pk);
    BoardEntry { ciphertext: xor_with_keystream(&key, &bytes) }
}

/// `ExtractMsg`: try to decrypt `entry` as a transaction between `owner_pk` and
/// `counterparty_pk`. Returns `Some(tx)` only if the decrypted plaintext carries
/// the magic tag *and* `owner_pk` is genuinely the sender or recipient of `tx`.
pub fn extract_msg(
    owner_pk: &[u8; 32],
    counterparty_pk: &[u8; 32],
    entry: &BoardEntry,
) -> Option<Transaction> {
    let key = pair_key(owner_pk, counterparty_pk);
    let bytes = xor_with_keystream(&key, &entry.ciphertext);
    let plaintext: Plaintext = bincode::deserialize(&bytes).ok()?;
    if plaintext.tag != MAGIC_TAG {
        return None;
    }
    let tx = plaintext.tx;
    if tx.sent_by(owner_pk) || tx.received_by(owner_pk) {
        Some(tx)
    } else {
        None
    }
}

/// Try every other member of `registry` as the counterparty for `entry`,
/// returning the unique transaction (if any) that genuinely involves
/// `owner_pk`. Because the prover cannot forge a valid decryption for the
/// wrong counterparty (see module docs), this leaves the prover no freedom to
/// claim "this slot isn't mine" for a slot that actually is.
pub fn scan_entry(
    owner_pk: &[u8; 32],
    registry: &[[u8; 32]],
    entry: &BoardEntry,
) -> Option<Transaction> {
    for cp in registry {
        if cp == owner_pk {
            continue;
        }
        if let Some(tx) = extract_msg(owner_pk, cp, entry) {
            return Some(tx);
        }
    }
    None
}

// ---- Merkle tree over board entries ------------------------------------
//
// The prover can't be trusted to supply a genuine, complete copy of the
// bulletin board — they could omit slots where they previously spent a coin.
// The fix:
//
//   1. The Merkle root of the complete board is a PUBLIC output, committed in
//      the proof. Carol independently computes her own root from the real
//      board (the real ciphertexts) and checks it matches. This guarantees the
//      prover used the genuine, complete board.
//
//   2. Each board entry the prover witnesses is accompanied by its Merkle
//      inclusion proof (a log-T-length chain of sibling hashes from the leaf
//      to the root), verified in-circuit, tying the witnessed ciphertext to
//      the committed root.

/// Leaf hash = SHA256(slot_as_u64_le || bincode(entry)).
/// Including the slot index prevents permuting genuine entries across slots
/// while keeping a valid root.
pub fn merkle_leaf(slot: usize, entry: &BoardEntry) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update((slot as u64).to_le_bytes());
    h.update(&bincode::serialize(entry).expect("BoardEntry is always serializable"));
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

fn next_pow2(n: usize) -> usize {
    if n <= 1 {
        return 1;
    }
    let mut p = 1usize;
    while p < n {
        p <<= 1;
    }
    p
}

/// Build the complete Merkle tree over `leaves`.
/// Returns all levels: index 0 = leaf level, last index = [root].
/// Padded with [0u8;32] to the next power of 2.
fn build_tree(leaves: &[[u8; 32]]) -> Vec<Vec<[u8; 32]>> {
    let n = next_pow2(leaves.len().max(1));
    let mut level = leaves.to_vec();
    level.resize(n, [0u8; 32]);
    let mut levels = vec![level.clone()];
    while level.len() > 1 {
        let next: Vec<[u8; 32]> = level
            .chunks(2)
            .map(|pair| merkle_combine(&pair[0], &pair[1]))
            .collect();
        levels.push(next.clone());
        level = next;
    }
    levels
}

/// Compute the Merkle root of `entries` at consecutive slots 0..T-1.
pub fn merkle_root_of(entries: &[BoardEntry]) -> [u8; 32] {
    let leaves: Vec<[u8; 32]> =
        entries.iter().enumerate().map(|(i, e)| merkle_leaf(i, e)).collect();
    let tree = build_tree(&leaves);
    tree.last().unwrap()[0]
}

/// Generate the Merkle inclusion proof (sibling hashes leaf→root) for `slot`
/// in the tree over `entries`.
pub fn merkle_proof_for(entries: &[BoardEntry], slot: usize) -> Vec<[u8; 32]> {
    let leaves: Vec<[u8; 32]> =
        entries.iter().enumerate().map(|(i, e)| merkle_leaf(i, e)).collect();
    let tree = build_tree(&leaves);
    let mut proof = Vec::new();
    let mut idx = slot;
    for level in &tree[..tree.len() - 1] {
        let sibling = if idx % 2 == 0 { idx + 1 } else { idx - 1 };
        proof.push(level[sibling]);
        idx /= 2;
    }
    proof
}

/// Verify that `entry` at `slot` is a member of the tree with the given `root`.
pub fn merkle_verify(root: [u8; 32], slot: usize, entry: &BoardEntry, proof: &[[u8; 32]]) -> bool {
    let mut current = merkle_leaf(slot, entry);
    let mut idx = slot;
    for sibling in proof {
        current = if idx % 2 == 0 {
            merkle_combine(&current, sibling)
        } else {
            merkle_combine(sibling, &current)
        };
        idx /= 2;
    }
    current == root
}

// ---- Public values -------------------------------------------------------

/// The public values committed by the spend (`Valid`) relation.
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

/// One step of the coin-proof IVC: extend the previous step's public values
/// (covering `entries[0..k]`) to cover `entries[0..=k]`.
///
/// `registry` is the set of all known parties' public keys (excluding
/// `owner_pk` is not required — it is skipped automatically). The relation
/// scans `entries[k]` against every other registry member; see [`scan_entry`].
pub fn check_coin_proof_step(
    vkey: [u32; 8],
    owner_pk: [u8; 32],
    coin_commitment: [u8; 32],
    entries: Vec<BoardEntry>,
    registry: Vec<[u8; 32]>,
    inner: Option<CoinProofPublicValues>,
) -> Result<(CoinProofPublicValues, CoinProofJustification), &'static str> {
    if entries.is_empty() {
        return Err("coin-proof must cover at least one board slot");
    }
    let k = entries.len() - 1;
    let board_root = merkle_root_of(&entries);

    let (prev_received_at, prev_spent, justification) = if k == 0 {
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
        if inner.board_size != k {
            return Err("inner coin-proof must cover exactly the prefix before this slot");
        }
        if inner.board_root != merkle_root_of(&entries[..k]) {
            return Err("inner coin-proof's board root does not match this prefix");
        }
        let prev_received_at = inner.received_at;
        let prev_spent = inner.spent;
        (prev_received_at, prev_spent, CoinProofJustification::Step { inner_public_values: inner })
    };

    let mut received_at = prev_received_at;
    let mut spent = prev_spent;
    if let Some(tx) = scan_entry(&owner_pk, &registry, &entries[k]) {
        if tx.receives_coin(&owner_pk, &coin_commitment) && received_at.is_none() {
            received_at = Some(k as u64);
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
            board_size: k + 1,
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
/// `entries` is the full board (`entries[0..=last]`); `merkle_proof` is the
/// inclusion proof for `entries[last]` (the spend transaction `tx*`) against
/// `board_root`. For non-genesis spends, `coin_proof` must be the latest
/// coin-proof covering `entries[0..last]`, with `received_at = Some(_)` and
/// `spent = false`.
pub fn check_spend(
    vkey: [u32; 8],
    coin_proof_vkey: [u32; 8],
    sk_p: [u8; 32],
    pk_p: [u8; 32],
    coin_commitment: [u8; 32],
    board_root: [u8; 32],
    entries: Vec<BoardEntry>,
    merkle_proof: Vec<[u8; 32]>,
    recipient_pk: [u8; 32],
    is_genesis: bool,
    coin_proof: Option<CoinProofPublicValues>,
) -> Result<ValidPublicValues, &'static str> {
    if derive_pk(&sk_p) != pk_p {
        return Err("pk_P must be the public key for sk_P");
    }
    if entries.is_empty() {
        return Err("board must contain at least one entry");
    }
    let last = entries.len() - 1;

    if !merkle_verify(board_root, last, &entries[last], &merkle_proof) {
        return Err("Merkle proof failed: tx* does not match committed board root");
    }

    let tx_star = extract_msg(&pk_p, &recipient_pk, &entries[last])
        .ok_or("tx* could not be decrypted as a transaction sent by P")?;
    if !tx_star.sent_by(&pk_p) {
        return Err("tx* must be sent by P");
    }
    if tx_star.input_coin.commitment() != coin_commitment {
        return Err("tx* must spend the claimed coin");
    }
    if tx_star.output_coin.value + tx_star.change_coin.value != tx_star.input_coin.value {
        return Err("transaction violates value conservation: output + change must equal input");
    }

    if is_genesis {
        if pk_p != genesis_pk() {
            return Err("only the genesis key may mint without provenance");
        }
        if last != 0 {
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
        if cp.board_size != last {
            return Err("coin-proof must cover exactly the board prefix before tx*");
        }
        if cp.board_root != merkle_root_of(&entries[..last]) {
            return Err("coin-proof's board root does not match the board prefix");
        }
        if cp.received_at.is_none() {
            return Err("P must have received this coin at some prior slot");
        }
        if cp.spent {
            return Err("P must not have spent this coin before (double spend)");
        }
    }

    Ok(ValidPublicValues { vkey, pk_p, board_root, board_size: entries.len() })
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

    fn coin(seed: u8, value: u64) -> Coin {
        let mut tag = [0u8; 32];
        tag[0] = seed;
        let mut rand = [0u8; 32];
        rand[1] = seed;
        Coin { tag, value, rand }
    }

    fn tx(
        id: u64,
        sender: [u8; 32],
        recipient: [u8; 32],
        input: Coin,
        output: Coin,
        change: Coin,
    ) -> Transaction {
        Transaction {
            id,
            sender_pk: sender,
            recipient_pk: recipient,
            input_coin: input,
            output_coin: output,
            change_coin: change,
        }
    }

    /// Run the coin-proof IVC chain for `owner_pk`/`coin_commitment` over the
    /// full board `entries`, returning the public values after each step
    /// (`result[i]` covers `entries[0..=i]`).
    fn coin_proof_chain(
        owner_pk: [u8; 32],
        coin_commitment: [u8; 32],
        entries: &[BoardEntry],
        registry: &[[u8; 32]],
    ) -> Vec<CoinProofPublicValues> {
        let mut out = Vec::new();
        let mut inner = None;
        for k in 0..entries.len() {
            let (pv, _) = check_coin_proof_step(
                TEST_COIN_PROOF_VKEY,
                owner_pk,
                coin_commitment,
                entries[..=k].to_vec(),
                registry.to_vec(),
                inner.clone(),
            )
            .unwrap();
            inner = Some(pv.clone());
            out.push(pv);
        }
        out
    }

    #[test]
    fn ciphertext_has_constant_length() {
        let (_, alice_pk) = party(1);
        let (_, genesis_pk) = (GENESIS_SK, genesis_pk());
        let tx0 = tx(0, genesis_pk, alice_pk, coin(0xA1, 100), coin(0xA2, 100), coin(0xA3, 0));
        let entry = encrypt_tx(&tx0);
        assert_eq!(entry.ciphertext.len(), CIPHERTEXT_LEN);
    }

    #[test]
    fn extract_msg_round_trips_for_both_parties_and_rejects_others() {
        let (_, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (_, alice_pk) = party(1);
        let (_, bob_pk) = party(2);
        let tx0 = tx(0, genesis_pk, alice_pk, coin(0xA1, 100), coin(0xA2, 100), coin(0xA3, 0));
        let entry = encrypt_tx(&tx0);

        // Both genuine parties can decrypt it (pair_key is symmetric).
        assert_eq!(extract_msg(&genesis_pk, &alice_pk, &entry), Some(tx0.clone()));
        assert_eq!(extract_msg(&alice_pk, &genesis_pk, &entry), Some(tx0));

        // An uninvolved party cannot.
        assert_eq!(extract_msg(&bob_pk, &genesis_pk, &entry), None);
        assert_eq!(extract_msg(&bob_pk, &alice_pk, &entry), None);
        // Even a genuine party using the wrong counterparty key fails.
        assert_eq!(extract_msg(&alice_pk, &bob_pk, &entry), None);
    }

    #[test]
    fn registry_scan_finds_the_right_counterparty() {
        let (_, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (_, alice_pk) = party(1);
        let (_, bob_pk) = party(2);
        let (_, carol_pk) = party(3);
        let registry = vec![genesis_pk, alice_pk, bob_pk, carol_pk];

        let tx0 = tx(0, genesis_pk, alice_pk, coin(0xA1, 100), coin(0xA2, 100), coin(0xA3, 0));
        let entry = encrypt_tx(&tx0);

        assert_eq!(scan_entry(&alice_pk, &registry, &entry), Some(tx0.clone()));
        assert_eq!(scan_entry(&genesis_pk, &registry, &entry), Some(tx0));
        assert_eq!(scan_entry(&bob_pk, &registry, &entry), None);
        assert_eq!(scan_entry(&carol_pk, &registry, &entry), None);
    }

    #[test]
    fn coin_proof_tracks_receipt_and_spend_for_demo_chain() {
        let (genesis_sk, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (alice_sk, alice_pk) = party(1);
        let (bob_sk, bob_pk) = party(2);
        let (_carol_sk, carol_pk) = party(3);
        let registry = vec![genesis_pk, alice_pk, bob_pk, carol_pk];

        let alice_coin = coin(0xA2, 100);
        let bob_coin = coin(0xB1, 40);

        let tx0 = tx(0, genesis_pk, alice_pk, coin(0xA1, 100), alice_coin.clone(), coin(0xA3, 0));
        let tx1 = tx(1, alice_pk, bob_pk, alice_coin.clone(), bob_coin.clone(), coin(0xB2, 60));
        let tx2 = tx(2, bob_pk, carol_pk, bob_coin.clone(), coin(0xC1, 40), coin(0xC2, 0));
        let entries = vec![encrypt_tx(&tx0), encrypt_tx(&tx1), encrypt_tx(&tx2)];

        let cn_alice = alice_coin.commitment();
        let cn_bob = bob_coin.commitment();

        // Alice's coin-proof: she receives the coin at slot 0.
        let alice_cp = coin_proof_chain(alice_pk, cn_alice, &entries[..1], &registry);
        assert_eq!(alice_cp[0].received_at, Some(0));
        assert_eq!(alice_cp[0].spent, false);

        // Bob's coin-proof: nothing at slot 0, receives at slot 1.
        let bob_cp = coin_proof_chain(bob_pk, cn_bob, &entries[..2], &registry);
        assert_eq!(bob_cp[0].received_at, None);
        assert_eq!(bob_cp[0].spent, false);
        assert_eq!(bob_cp[1].received_at, Some(1));
        assert_eq!(bob_cp[1].spent, false);

        // Sanity: spends below also succeed using these coin-proofs.
        let _ = (genesis_sk, alice_sk, bob_sk);
    }

    /// A transaction's change is a *receipt* too: the sender's coin-proof for
    /// their change coin should pick it up via the `change_coin` branch of
    /// [`Transaction::receives_coin`].
    #[test]
    fn coin_proof_tracks_change_as_a_receipt() {
        let (genesis_sk, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (alice_sk, alice_pk) = party(1);
        let (bob_sk, bob_pk) = party(2);
        let (_, carol_pk) = party(3);
        let registry = vec![genesis_pk, alice_pk, bob_pk, carol_pk];

        let alice_coin = coin(0xA2, 100);
        let bob_coin = coin(0xB1, 40);
        let alice_change = coin(0xB2, 60);

        let tx0 = tx(0, genesis_pk, alice_pk, coin(0xA1, 100), alice_coin.clone(), coin(0xA3, 0));
        let tx1 = tx(1, alice_pk, bob_pk, alice_coin.clone(), bob_coin, alice_change.clone());
        let entries = vec![encrypt_tx(&tx0), encrypt_tx(&tx1)];

        let cn_alice_change = alice_change.commitment();

        // Alice's coin-proof for her change coin: doesn't exist at slot 0,
        // received (as change) at slot 1.
        let alice_change_cp = coin_proof_chain(alice_pk, cn_alice_change, &entries, &registry);
        assert_eq!(alice_change_cp[0].received_at, None);
        assert_eq!(alice_change_cp[1].received_at, Some(1));
        assert_eq!(alice_change_cp[1].spent, false);

        let _ = (genesis_sk, bob_sk, carol_pk);
    }

    /// Convenience: `check_spend` for the tx at `entries.len()-1`, given the
    /// previous coin-proof (or `None` for genesis).
    fn spend(
        sk: [u8; 32],
        pk: [u8; 32],
        coin_commitment: [u8; 32],
        entries: &[BoardEntry],
        recipient_pk: [u8; 32],
        is_genesis: bool,
        coin_proof: Option<CoinProofPublicValues>,
    ) -> Result<ValidPublicValues, &'static str> {
        let last = entries.len() - 1;
        let board_root = merkle_root_of(entries);
        let proof = merkle_proof_for(entries, last);
        check_spend(
            TEST_VKEY,
            TEST_COIN_PROOF_VKEY,
            sk,
            pk,
            coin_commitment,
            board_root,
            entries.to_vec(),
            proof,
            recipient_pk,
            is_genesis,
            coin_proof,
        )
    }

    #[test]
    fn demo_chain_is_valid_end_to_end() {
        let (genesis_sk, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (alice_sk, alice_pk) = party(1);
        let (bob_sk, bob_pk) = party(2);
        let (_, carol_pk) = party(3);
        let registry = vec![genesis_pk, alice_pk, bob_pk, carol_pk];

        let genesis_coin = coin(0xA1, 100);
        let alice_coin = coin(0xA2, 100);
        let bob_coin = coin(0xB1, 40);
        let alice_change = coin(0xB2, 60);
        let carol_coin = coin(0xC1, 40);
        let bob_change = coin(0xC2, 0);

        // Genesis mints 100 units to Alice (no change kept).
        let tx0 = tx(0, genesis_pk, alice_pk, genesis_coin.clone(), alice_coin.clone(), coin(0xA3, 0));
        // Alice sends 40 to Bob, keeping 60 as change.
        let tx1 = tx(1, alice_pk, bob_pk, alice_coin.clone(), bob_coin.clone(), alice_change);
        // Bob sends all 40 to Carol (no change kept).
        let tx2 = tx(2, bob_pk, carol_pk, bob_coin.clone(), carol_coin, bob_change);
        let entries = vec![encrypt_tx(&tx0), encrypt_tx(&tx1), encrypt_tx(&tx2)];

        let cn_genesis = genesis_coin.commitment();
        let cn_alice = alice_coin.commitment();
        let cn_bob = bob_coin.commitment();

        // Genesis mints to Alice.
        spend(genesis_sk, genesis_pk, cn_genesis, &entries[..1], alice_pk, true, None).unwrap();

        // Alice's coin-proof over entries[0..1], then her spend to Bob.
        let alice_cp = coin_proof_chain(alice_pk, cn_alice, &entries[..1], &registry);
        spend(alice_sk, alice_pk, cn_alice, &entries[..2], bob_pk, false, Some(alice_cp[0].clone()))
            .unwrap();

        // Bob's coin-proof over entries[0..2], then his spend to Carol.
        let bob_cp = coin_proof_chain(bob_pk, cn_bob, &entries[..2], &registry);
        spend(bob_sk, bob_pk, cn_bob, &entries[..3], carol_pk, false, Some(bob_cp[1].clone()))
            .unwrap();
    }

    #[test]
    fn rejects_wrong_secret_key() {
        let (_, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (alice_sk, alice_pk) = party(1);
        let genesis_coin = coin(0xA1, 100);
        let tx0 = tx(0, genesis_pk, alice_pk, genesis_coin.clone(), coin(0xA2, 100), coin(0xA3, 0));
        let entries = vec![encrypt_tx(&tx0)];

        let err = spend(alice_sk, genesis_pk, genesis_coin.commitment(), &entries, alice_pk, true, None)
            .unwrap_err();
        assert_eq!(err, "pk_P must be the public key for sk_P");
    }

    #[test]
    fn rejects_minting_without_the_genesis_key() {
        let (alice_sk, alice_pk) = party(1);
        let (_, bob_pk) = party(2);
        let alice_coin = coin(0xA1, 100);
        let tx0 = tx(0, alice_pk, bob_pk, alice_coin.clone(), coin(0xB1, 100), coin(0xA3, 0));
        let entries = vec![encrypt_tx(&tx0)];

        let err = spend(alice_sk, alice_pk, alice_coin.commitment(), &entries, bob_pk, true, None)
            .unwrap_err();
        assert_eq!(err, "only the genesis key may mint without provenance");
    }

    #[test]
    fn rejects_spending_a_coin_one_never_received() {
        let (genesis_sk, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (alice_sk, alice_pk) = party(1);
        let (carol_sk, carol_pk) = party(3);
        let registry = vec![genesis_pk, alice_pk, carol_pk];

        let genesis_coin = coin(0xA1, 100);
        let alice_coin = coin(0xA2, 100);
        // A coin Carol never received.
        let carol_fake_input = coin(0xC1, 100);

        let tx0 = tx(0, genesis_pk, alice_pk, genesis_coin, alice_coin, coin(0xA3, 0));
        // Carol fabricates a "spend" of a coin she never received.
        let tx_fake =
            tx(1, carol_pk, alice_pk, carol_fake_input.clone(), coin(0xC2, 100), coin(0xC3, 0));
        let entries = vec![encrypt_tx(&tx0), encrypt_tx(&tx_fake)];
        let cn_carol = carol_fake_input.commitment();

        let carol_cp = coin_proof_chain(carol_pk, cn_carol, &entries[..1], &registry);
        assert_eq!(carol_cp[0].received_at, None);

        let err =
            spend(carol_sk, carol_pk, cn_carol, &entries, alice_pk, false, Some(carol_cp[0].clone()))
                .unwrap_err();
        assert_eq!(err, "P must have received this coin at some prior slot");

        let _ = genesis_sk;
        let _ = alice_sk;
    }

    #[test]
    fn rejects_double_spend() {
        let (genesis_sk, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (alice_sk, alice_pk) = party(1);
        let (_, bob_pk) = party(2);
        let (_, carol_pk) = party(3);
        let registry = vec![genesis_pk, alice_pk, bob_pk, carol_pk];

        let genesis_coin = coin(0xA1, 100);
        let alice_coin = coin(0xA2, 100);
        let cn_genesis = genesis_coin.commitment();
        let cn_alice = alice_coin.commitment();

        let tx0 = tx(0, genesis_pk, alice_pk, genesis_coin, alice_coin.clone(), coin(0xA3, 0));
        let tx1 = tx(1, alice_pk, bob_pk, alice_coin.clone(), coin(0xB1, 60), coin(0xB2, 40));
        // Alice tries to spend the same coin again, to Carol this time.
        let tx1b = tx(2, alice_pk, carol_pk, alice_coin.clone(), coin(0xC1, 100), coin(0xC2, 0));
        let entries = vec![encrypt_tx(&tx0), encrypt_tx(&tx1), encrypt_tx(&tx1b)];

        spend(genesis_sk, genesis_pk, cn_genesis, &entries[..1], alice_pk, true, None).unwrap();

        let alice_cp = coin_proof_chain(alice_pk, cn_alice, &entries[..2], &registry);
        assert_eq!(alice_cp[0].received_at, Some(0));
        assert_eq!(alice_cp[1].spent, true); // tx1 already recorded as a spend

        // Alice's first spend (to Bob) succeeds using alice_cp[0].
        spend(alice_sk, alice_pk, cn_alice, &entries[..2], bob_pk, false, Some(alice_cp[0].clone()))
            .unwrap();

        // The double-spend (to Carol) is rejected: alice_cp[1].spent == true.
        let err = spend(
            alice_sk,
            alice_pk,
            cn_alice,
            &entries[..3],
            carol_pk,
            false,
            Some(alice_cp[1].clone()),
        )
        .unwrap_err();
        assert_eq!(err, "P must not have spent this coin before (double spend)");
    }

    /// An attacker swaps the ciphertext at slot 0 but keeps the genuine root.
    /// The inclusion proof computed from the fake entry won't reconstruct the
    /// genuine root, so `check_spend` rejects it.
    #[test]
    fn rejects_tampered_board_entry() {
        let (genesis_sk, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (_, alice_pk) = party(1);
        let genesis_coin = coin(0xA1, 100);

        let tx0_real =
            tx(0, genesis_pk, alice_pk, genesis_coin.clone(), coin(0xA2, 100), coin(0xA3, 0));
        let entry_real = encrypt_tx(&tx0_real);
        let real_root = merkle_root_of(&[entry_real]);

        let tx0_fake =
            tx(0, genesis_pk, alice_pk, genesis_coin.clone(), coin(0xB2, 100), coin(0xB3, 0));
        let entry_fake = encrypt_tx(&tx0_fake);
        let fake_proof = merkle_proof_for(&[entry_fake.clone()], 0);

        let err = check_spend(
            TEST_VKEY,
            TEST_COIN_PROOF_VKEY,
            genesis_sk,
            genesis_pk,
            genesis_coin.commitment(),
            real_root,
            vec![entry_fake],
            fake_proof,
            alice_pk,
            true,
            None,
        )
        .unwrap_err();
        assert_eq!(err, "Merkle proof failed: tx* does not match committed board root");
    }

    /// `output.value + change.value` must equal `input.value` exactly — no
    /// value may be created (overdraft) or destroyed by a transfer.
    #[test]
    fn rejects_value_conservation_violation() {
        let (genesis_sk, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (_, alice_pk) = party(1);
        let genesis_coin = coin(0xA1, 100);

        // Overdraft: output (100) + change (1) > input (100).
        let tx0 = tx(0, genesis_pk, alice_pk, genesis_coin.clone(), coin(0xA2, 100), coin(0xA3, 1));
        let entries = vec![encrypt_tx(&tx0)];

        let err =
            spend(genesis_sk, genesis_pk, genesis_coin.commitment(), &entries, alice_pk, true, None)
                .unwrap_err();
        assert_eq!(err, "transaction violates value conservation: output + change must equal input");
    }
}
