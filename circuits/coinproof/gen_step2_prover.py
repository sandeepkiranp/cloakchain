#!/usr/bin/env python3
"""
Generate Prover.toml for coinproof_step at slot=2.
Run from circuits/coinproof/ after slot=1 has been proved (artifacts in target/).
The VK is the same coinproof_step VK — no need to rerun bb write_vk.
"""

import hashlib
import os
import struct

STEP_DIR = "."   # coinproof_step artifacts (slot=1 proof used as inner)

def blake2s(data: bytes) -> bytes:
    return hashlib.blake2s(data, digest_size=32).digest()

def u64_le(x: int) -> bytes:
    return struct.pack('<Q', x)

# Proper empty subtree hashes: Z[0] = [0;32], Z[h] = blake2s(Z[h-1] || Z[h-1])
Z = [bytes(32)]
for _ in range(32):
    Z.append(blake2s(Z[-1] + Z[-1]))

def compute_leaf(slot: int, out_cns: list, ct_hash: bytes) -> bytes:
    buf = bytearray(296)
    buf[0:8] = u64_le(slot)
    for i, cn in enumerate(out_cns):
        buf[8 + i*32 : 8 + i*32 + 32] = cn
    buf[264:296] = ct_hash
    return blake2s(bytes(buf))

def compute_root(leaf: bytes, slot: int, path: list) -> bytes:
    cur = leaf
    idx = slot
    for sib in path:
        cur = blake2s(sib + cur if idx % 2 else cur + sib)
        idx //= 2
    return cur

def state_hash_py(owner_pk, coin_cn, board_root, board_size,
                  rcv_valid, rcv_at, spent, par_null, par_null_seen) -> bytes:
    buf = bytearray(147)
    buf[0:32]   = owner_pk
    buf[32:64]  = coin_cn
    buf[64:96]  = board_root
    buf[96:104] = u64_le(board_size)
    buf[104]    = 1 if rcv_valid else 0
    buf[105:113]= u64_le(rcv_at)
    buf[113]    = 1 if spent else 0
    buf[114:146]= par_null
    buf[146]    = 1 if par_null_seen else 0
    return blake2s(bytes(buf))

def read_fields_be(path: str, n: int, offset: int = 0) -> list:
    with open(path, 'rb') as f:
        data = f.read()
    return [f'"0x{int.from_bytes(data[(offset+i)*32:(offset+i+1)*32], "big"):064x}"' for i in range(n)]

def read_vk_hash(path: str) -> str:
    with open(path, 'rb') as f:
        raw = f.read()
    if len(raw) == 32:
        return f'"0x{int.from_bytes(raw, "big"):064x}"'
    s = raw.decode().strip()
    return f'"{s}"' if s.startswith("0x") else f'"0x{s}"'

def arr32(b: bytes) -> str:
    return '[' + ', '.join(f'"0x{x:02x}"' for x in b) + ']'

def zeros32() -> str:
    return arr32(bytes(32))

def arr8x32z() -> str:
    return '[' + ', '.join([zeros32()] * 8) + ']'

Z32 = bytes(32)

# ── Reconstruct leaf_0 and leaf_1 ──────────────────────────────────────────
leaf_0 = compute_leaf(0, [Z32]*8, Z32)
leaf_1 = compute_leaf(1, [Z32]*8, Z32)
print(f"leaf_0 = {list(leaf_0)}")
print(f"leaf_1 = {list(leaf_1)}")

# ── Verify inner_board_root (new_root_1) from slot=1 public_inputs ──────────
pub_path = os.path.join(STEP_DIR, "target/proof/public_inputs")
with open(pub_path, 'rb') as f:
    pub_data = f.read()
total_fields = len(pub_data) // 32
print(f"coinproof_step (slot=1) public_inputs: {total_fields} fields")

# state_hash is at fields [97..129] in coinproof_step's public_inputs
inner_state_hash = bytes(
    int.from_bytes(pub_data[(97+i)*32:(97+i+1)*32], 'big') for i in range(32)
)
print(f"inner_state_hash (from slot=1 proof) = {list(inner_state_hash)}")

# ── Recompute inner state to extract inner_board_root ─────────────────────
# new_root_1: computed with proper Z paths for slot=1
new_root_1 = compute_root(leaf_1, 1, [leaf_0] + [Z[h] for h in range(1, 32)])
print(f"new_root_1 (inner_board_root) = {list(new_root_1)}")

# Recompute state_hash for slot=1 to cross-check
inner_board_root = new_root_1
inner_state_recomputed = state_hash_py(
    Z32, Z32, inner_board_root,
    2, False, 0, True, Z32, True,
)
if inner_state_recomputed != inner_state_hash:
    print(f"WARNING: recomputed state_hash != circuit output; using circuit output")
    print(f"  recomputed: {list(inner_state_recomputed)}")
    print(f"  circuit:    {list(inner_state_hash)}")
else:
    print("✓ inner_state_hash verified")

# ── Merkle path for slot=2 ───────────────────────────────────────────────────
# append_path for slot=2:
#   [0]: Z[0] = [0;32]   (sibling of slot 2 is slot 3 = empty leaf)
#   [1]: blake2s(leaf_0 || leaf_1)  (sibling of pair (2,3) is filled pair (0,1))
#   [h]: Z[h] for h >= 2  (proper empty subtree hash)
pair_01 = blake2s(leaf_0 + leaf_1)
step_path = [Z[0], pair_01] + [Z[h] for h in range(2, 32)]

old_root_2 = compute_root(Z32, 2, step_path)
assert old_root_2 == new_root_1, (
    f"Root mismatch!\n  old_root_2: {list(old_root_2)}\n  new_root_1: {list(new_root_1)}")
print("✓ Merkle root consistency verified (old_root_2 == new_root_1)")

# ── Read coinproof_step (slot=1) proof artifacts ────────────────────────────
vk_path    = os.path.join(STEP_DIR, "target/vk/vk")
proof_path = os.path.join(STEP_DIR, "target/proof/proof")
vkhash_path= os.path.join(STEP_DIR, "target/vk/vk_hash")

inner_vk_fields    = read_fields_be(vk_path, 115)
inner_proof_fields = read_fields_be(proof_path, 457)
inner_vk_hash      = read_vk_hash(vkhash_path)

print(f"VK fields: {len(inner_vk_fields)}, proof fields: {len(inner_proof_fields)}")
print(f"VK hash: {inner_vk_hash[:20]}...")

# ── Write Prover.toml ─────────────────────────────────────────────────────────
path_rows = ', '.join(arr32(p) for p in step_path)

lines = [
    # public inputs
    f"owner_pk = {zeros32()}",
    f"coin_commitment = {zeros32()}",
    f'slot = "0x0000000000000002"',
    # board entry at slot 2 (all zeros)
    f"entry_output_commitments = {arr8x32z()}",
    f'entry_num_outputs = "0x0000000000000000"',
    f"entry_nullifier = {zeros32()}",
    f"entry_ciphertext_hash = {zeros32()}",
    # merkle path
    f"append_path = [{path_rows}]",
    # nullifiers
    f"parent_nullifier = {zeros32()}",
    f"own_nullifier = {zeros32()}",
    # inner proof (coinproof_step slot=1)
    f"inner_vk = [{', '.join(inner_vk_fields)}]",
    f"inner_proof = [{', '.join(inner_proof_fields)}]",
    f"inner_vk_hash = {inner_vk_hash}",
    # inner state witnesses (from coinproof_step slot=1)
    f"inner_state_hash = {arr32(inner_state_hash)}",
    f"inner_owner_pk = {zeros32()}",
    f"inner_coin_commitment = {zeros32()}",
    f"inner_board_root = {arr32(inner_board_root)}",
    f'inner_board_size = "0x0000000000000002"',   # slot=1 produced board_size=2
    f"inner_received_at_valid = false",
    f'inner_received_at = "0x0000000000000000"',
    f"inner_spent = true",
    f"inner_parent_nullifier = {zeros32()}",
    f"inner_parent_nullifier_seen = true",
    f"is_receipt_hint = false",
]

with open("Prover.toml", "w") as f:
    f.write("\n".join(lines) + "\n")
print("Prover.toml written.")
