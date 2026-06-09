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

/// A coin: tag `t` plus masking randomness `r`.
/// Commitment cn = H(t || r) — same semantics as the paper's Pedersen commitment,
/// without elliptic-curve arithmetic in the zkVM.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Coin {
    pub tag: [u8; 32],
    pub rand: [u8; 32],
}

impl Coin {
    pub fn commitment(&self) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(self.tag);
        h.update(self.rand);
        let mut out = [0u8; 32];
        out.copy_from_slice(&h.finalize());
        out
    }
}

/// A transaction posted to the bulletin board: `S` transfers `coin` to `R`.
///
/// Whisper is out of scope, so transactions are posted in the clear.
/// `sent_by` and `received_by` are stand-ins for `HaveISent?`/`ExtractMsg_S` and
/// `ExtractMsg_R` from §1.2 of the paper.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Transaction {
    pub id: u64,
    pub sender_pk: [u8; 32],
    pub recipient_pk: [u8; 32],
    pub coin: Coin,
}

impl Transaction {
    pub fn sent_by(&self, pk: &[u8; 32]) -> bool {
        &self.sender_pk == pk
    }
    pub fn received_by(&self, pk: &[u8; 32]) -> bool {
        &self.recipient_pk == pk
    }
}

// ---- Merkle tree -------------------------------------------------------
//
// The prover can't be trusted to supply a genuine, complete copy of the bulletin
// board — they could omit slots where they previously spent a coin.  The fix:
//
//   1. The Merkle root of the complete board is a PUBLIC output, committed in
//      the proof.  Carol independently computes her own root from the real board
//      and checks it matches.  This guarantees the prover used the genuine,
//      complete board — they can't omit or alter any slot without the roots
//      diverging.
//
//   2. Each transaction the prover witnesses is accompanied by its Merkle
//      inclusion proof (a log-T-length chain of sibling hashes from the leaf to
//      the root).  The circuit verifies each inclusion proof in-circuit, tying
//      the specific transaction content to the committed root.  The prover
//      therefore cannot substitute a fake transaction at any slot — the
//      inclusion proof would fail to verify against the real root.
//
// Together these two checks close both the omission attack (skipping a slot)
// and the fabrication attack (swapping content at a slot you didn't omit).

/// Leaf hash = SHA256(slot_as_u64_le || bincode(tx)).
/// Including the slot index prevents permuting genuine transactions across slots
/// while keeping a valid root.
pub fn merkle_leaf(slot: usize, tx: &Transaction) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update((slot as u64).to_le_bytes());
    h.update(&bincode::serialize(tx).expect("Transaction is always serializable"));
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

/// Compute the Merkle root of `transactions` at consecutive slots 0..T-1.
pub fn merkle_root_of(transactions: &[Transaction]) -> [u8; 32] {
    let leaves: Vec<[u8; 32]> =
        transactions.iter().enumerate().map(|(i, tx)| merkle_leaf(i, tx)).collect();
    let tree = build_tree(&leaves);
    tree.last().unwrap()[0]
}

/// Generate the Merkle inclusion proof (sibling hashes leaf→root) for `slot`
/// in the tree over `transactions`.
pub fn merkle_proof_for(transactions: &[Transaction], slot: usize) -> Vec<[u8; 32]> {
    let leaves: Vec<[u8; 32]> =
        transactions.iter().enumerate().map(|(i, tx)| merkle_leaf(i, tx)).collect();
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

/// Verify that `tx` at `slot` is a member of the tree with the given `root`.
pub fn merkle_verify(
    root: [u8; 32],
    slot: usize,
    tx: &Transaction,
    proof: &[[u8; 32]],
) -> bool {
    let mut current = merkle_leaf(slot, tx);
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

// ---- Public values -----------------------------------------------------

/// The public values committed by every invocation of the `Valid` relation.
///
/// The full `history` vector is replaced by its Merkle root: a single 32-byte
/// fingerprint that commits to all T board slots in order.  Replacing the
/// full vector with the root keeps the committed output constant-size and
/// forces Carol to verify the root against the real board (one hash comparison)
/// rather than diffing an arbitrarily large vector.
///
/// `board_size` records how many slots this root covers so that, in the
/// recursive step, the outer proof can recompute the inner board's root from
/// the same witnessed transactions without re-reading them as additional inputs.
///
/// `vkey` is the verification key of this program — included for self-consistency
/// of the recursive chain (each step verifies its predecessor under the same key).
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

/// What justifies condition 1 of the `Valid` relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Justification {
    Genesis,
    Recursive { t: usize, inner_public_values: ValidPublicValues },
}

/// Checks every condition of the `Valid` relation except actually verifying
/// the recursive ZK proof.
///
/// Each transaction in `transactions` must be accompanied by its Merkle
/// inclusion proof against `board_root`.  The circuit verifies every
/// inclusion proof in-circuit, tying the witnessed board contents to the
/// committed root that Carol can independently check against the real board.
///
/// On success returns the public values this invocation commits to, together
/// with the [`Justification`] for condition 1.
pub fn check_valid(
    vkey: [u32; 8],
    sk_p: [u8; 32],
    pk_p: [u8; 32],
    board_root: [u8; 32],
    transactions: Vec<Transaction>,
    merkle_proofs: Vec<Vec<[u8; 32]>>,
    is_genesis: bool,
    t: Option<u32>,
) -> Result<(ValidPublicValues, Justification), &'static str> {
    if derive_pk(&sk_p) != pk_p {
        return Err("pk_P must be the public key for sk_P");
    }
    if transactions.is_empty() {
        return Err("board must contain at least one transaction");
    }
    if transactions.len() != merkle_proofs.len() {
        return Err("must supply one Merkle proof per transaction");
    }

    // Verify every witnessed transaction is genuinely part of the committed board.
    // This is the in-circuit half of the completeness fix: the prover cannot
    // substitute a different transaction at any slot because the inclusion proof
    // would fail to reconstruct the committed root.
    for (slot, (tx, proof)) in transactions.iter().zip(merkle_proofs.iter()).enumerate() {
        if !merkle_verify(board_root, slot, tx, proof) {
            return Err("Merkle proof failed: transaction does not match committed board root");
        }
    }

    let last = transactions.len() - 1;
    let tx_star = &transactions[last];
    if tx_star.sender_pk != pk_p {
        return Err("tx* must be sent by P");
    }

    // ---- Condition 1 ----
    let justification = if is_genesis {
        if pk_p != genesis_pk() {
            return Err("only the genesis key may mint without provenance");
        }
        if last != 0 {
            return Err("a genesis mint has no prior history");
        }
        Justification::Genesis
    } else {
        let t = t.ok_or("non-genesis transactions must name the receiving transaction")? as usize;
        if t >= last {
            return Err("tx_t must be strictly earlier than tx*");
        }
        let tx_t = &transactions[t];
        if !tx_t.received_by(&pk_p) {
            return Err("P must have received tx_t");
        }
        if tx_t.coin.commitment() != tx_star.coin.commitment() {
            return Err("cn(tx_t) must be the same coin as cn(tx*)");
        }

        // Reconstruct the inner board's Merkle root from the prefix transactions[0..=t].
        // These are already verified above against `board_root`, so their leaf hashes are
        // genuine; building a sub-tree from them gives the correct inner board root
        // without re-witnessing any data.
        let inner_root = merkle_root_of(&transactions[..=t]);
        Justification::Recursive {
            t,
            inner_public_values: ValidPublicValues {
                vkey,
                pk_p: tx_t.sender_pk,
                board_root: inner_root,
                board_size: t + 1,
            },
        }
    };

    // ---- Condition 2 ----
    // Full scan — no nullifier shortcut.
    for m in &transactions[..last] {
        if m.sent_by(&pk_p) && m.coin.commitment() == tx_star.coin.commitment() {
            return Err("P must not have sent this coin before (double spend)");
        }
    }

    Ok((
        ValidPublicValues { vkey, pk_p, board_root, board_size: transactions.len() },
        justification,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEST_VKEY: [u32; 8] = [1, 2, 3, 4, 5, 6, 7, 8];

    fn party(seed: u8) -> ([u8; 32], [u8; 32]) {
        let mut sk = [0u8; 32];
        sk[0] = seed;
        (sk, derive_pk(&sk))
    }

    fn coin(seed: u8) -> Coin {
        let mut tag = [0u8; 32];
        tag[0] = seed;
        let mut rand = [0u8; 32];
        rand[1] = seed;
        Coin { tag, rand }
    }

    fn tx(id: u64, sender: [u8; 32], recipient: [u8; 32], c: Coin) -> Transaction {
        Transaction { id, sender_pk: sender, recipient_pk: recipient, coin: c }
    }

    /// Build the root + all inclusion proofs for a board in one call.
    fn board_proofs(txs: &[Transaction]) -> ([u8; 32], Vec<Vec<[u8; 32]>>) {
        let root = merkle_root_of(txs);
        let proofs = (0..txs.len()).map(|i| merkle_proof_for(txs, i)).collect();
        (root, proofs)
    }

    /// Convenience wrapper: `check_valid` from genuine board contents.
    fn valid(
        sk: [u8; 32],
        pk: [u8; 32],
        txs: Vec<Transaction>,
        is_genesis: bool,
        t: Option<u32>,
    ) -> Result<(ValidPublicValues, Justification), &'static str> {
        let (root, proofs) = board_proofs(&txs);
        check_valid(TEST_VKEY, sk, pk, root, txs, proofs, is_genesis, t)
    }

    #[test]
    fn demo_chain_is_valid_end_to_end() {
        let (genesis_sk, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (alice_sk, alice_pk) = party(1);
        let (bob_sk, bob_pk) = party(2);
        let (_carol_sk, carol_pk) = party(3);
        let coin_a = coin(0xA1);

        let tx0 = tx(0, genesis_pk, alice_pk, coin_a.clone());
        let tx1 = tx(1, alice_pk, bob_pk, coin_a.clone());
        let tx2 = tx(2, bob_pk, carol_pk, coin_a.clone());

        let (pv0, j0) =
            valid(genesis_sk, genesis_pk, vec![tx0.clone()], true, None).unwrap();
        assert_eq!(j0, Justification::Genesis);

        let (pv1, j1) =
            valid(alice_sk, alice_pk, vec![tx0.clone(), tx1.clone()], false, Some(0)).unwrap();
        assert_eq!(
            j1,
            Justification::Recursive { t: 0, inner_public_values: pv0.clone() },
            "Alice's inner_public_values must exactly match genesis's committed values"
        );

        let (_pv2, j2) =
            valid(bob_sk, bob_pk, vec![tx0, tx1, tx2], false, Some(1)).unwrap();
        assert_eq!(
            j2,
            Justification::Recursive { t: 1, inner_public_values: pv1.clone() },
            "Bob's inner_public_values must exactly match Alice's committed values"
        );
    }

    #[test]
    fn rejects_wrong_secret_key() {
        let (_, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (alice_sk, alice_pk) = party(1);
        let tx0 = tx(0, genesis_pk, alice_pk, coin(0xA1));
        let err = valid(alice_sk, genesis_pk, vec![tx0], true, None).unwrap_err();
        assert_eq!(err, "pk_P must be the public key for sk_P");
    }

    #[test]
    fn rejects_minting_without_the_genesis_key() {
        let (alice_sk, alice_pk) = party(1);
        let (_, bob_pk) = party(2);
        let tx0 = tx(0, alice_pk, bob_pk, coin(0xA1));
        let err = valid(alice_sk, alice_pk, vec![tx0], true, None).unwrap_err();
        assert_eq!(err, "only the genesis key may mint without provenance");
    }

    #[test]
    fn rejects_spending_a_coin_one_never_received() {
        let (_, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (alice_sk, alice_pk) = party(1);
        let (_, bob_pk) = party(2);
        let tx0 = tx(0, genesis_pk, alice_pk, coin(0xA1));
        let tx1 = tx(1, alice_pk, bob_pk, coin(0xB2)); // different coin
        let err = valid(alice_sk, alice_pk, vec![tx0, tx1], false, Some(0)).unwrap_err();
        assert_eq!(err, "cn(tx_t) must be the same coin as cn(tx*)");
    }

    #[test]
    fn rejects_double_spend() {
        let (genesis_sk, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (alice_sk, alice_pk) = party(1);
        let (_, bob_pk) = party(2);
        let (_, carol_pk) = party(3);
        let coin_a = coin(0xA1);

        let tx0 = tx(0, genesis_pk, alice_pk, coin_a.clone());
        let tx1 = tx(1, alice_pk, bob_pk, coin_a.clone());
        let tx2 = tx(2, alice_pk, carol_pk, coin_a.clone()); // Alice double-spends

        valid(genesis_sk, genesis_pk, vec![tx0.clone()], true, None).unwrap();
        valid(alice_sk, alice_pk, vec![tx0.clone(), tx1.clone()], false, Some(0)).unwrap();

        let err =
            valid(alice_sk, alice_pk, vec![tx0, tx1, tx2], false, Some(0)).unwrap_err();
        assert_eq!(err, "P must not have sent this coin before (double spend)");
    }

    /// Bob tries to use the genuine board root but swap the content at one slot.
    /// The Merkle inclusion proofs computed from the fake board won't reconstruct
    /// the genuine root, so the check rejects the fabricated transaction.
    #[test]
    fn rejects_tampered_board_entry() {
        let (genesis_sk, genesis_pk) = (GENESIS_SK, genesis_pk());
        let (_, alice_pk) = party(1);
        let coin_a = coin(0xA1);

        let tx0_real = tx(0, genesis_pk, alice_pk, coin_a.clone());
        let real_root = merkle_root_of(&[tx0_real.clone()]);

        // Attacker substitutes different content but keeps the real root.
        // The inclusion proof computed from the fake transaction won't verify
        // against the real root.
        let tx0_fake = tx(0, genesis_pk, alice_pk, coin(0xB2));
        let fake_proofs = vec![merkle_proof_for(&[tx0_fake.clone()], 0)];

        let err = check_valid(
            TEST_VKEY,
            genesis_sk,
            genesis_pk,
            real_root,
            vec![tx0_fake],
            fake_proofs,
            true,
            None,
        )
        .unwrap_err();
        assert_eq!(err, "Merkle proof failed: transaction does not match committed board root");
    }
}
