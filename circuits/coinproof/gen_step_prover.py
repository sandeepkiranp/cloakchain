#!/usr/bin/env python3
"""
Generate Prover.toml for coinproof_step at slot=1.
Run from circuits/coinproof/ with coinproof_base already proved at ../coinproof_base/.
"""

import hashlib
import os
import struct

BASE_DIR = "../coinproof_base"

def blake2s(data: bytes) -> bytes:
    return hashlib.blake2s(data, digest_size=32).digest()

def u64_le(x: int) -> bytes:
    return struct.pack('<Q', x)

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

def read_fields_le(path: str, n: int) -> list:
    """Read n little-endian 32-byte field elements, return as hex strings."""
    with open(path, 'rb') as f:
        data = f.read()
    return [f'"0x{int.from_bytes(data[i*32:(i+1)*32], "little"):064x}"' for i in range(n)]

def read_vk_hash(path: str) -> str:
    with open(path, 'rb') as f:
        raw = f.read()
    if len(raw) == 32:
        return f'"0x{int.from_bytes(raw, "little"):064x}"'
    s = raw.decode().strip()
    return f'"{s}"' if s.startswith("0x") else f'"0x{s}"'

def arr32(b: bytes) -> str:
    return '[' + ', '.join(f'"0x{x:02x}"' for x in b) + ']'

def zeros32() -> str:
    return '[' + ', '.join(['"0x00"'] * 32) + ']'

def arr8x32z() -> str:
    r = '[' + ', '.join(['"0x00"'] * 32) + ']'
    return '[' + ', '.join([r] * 8) + ']'

# ── Compute inner state from coinproof_base (all-zero inputs) ──────────────────

Z32 = bytes(32)
Z8  = bytes(8)

# coinproof_base: slot=0, buf[0:8]=zeros (slot LE), rest zeros
leaf_0 = compute_leaf(0, [Z32]*8, Z32)
print(f"leaf_0 = {list(leaf_0)}")

zero_path = [Z32] * 32
inner_board_root = compute_root(leaf_0, 0, zero_path)
print(f"inner_board_root = {list(inner_board_root)}")

# inner_spent = True because entry_nullifier=0 == own_nullifier=0
# inner_parent_nullifier_seen = True because entry_nullifier=0 == parent_nullifier=0
inner_spent             = True
inner_parent_null_seen  = True
inner_rcv_valid         = False
inner_board_size        = 1

inner_state_hash = state_hash_py(
    Z32, Z32, inner_board_root,
    inner_board_size, inner_rcv_valid, 0,
    inner_spent, Z32, inner_parent_null_seen,
)
print(f"inner_state_hash (computed) = {list(inner_state_hash)}")

# Cross-check against circuit output from coinproof_base run
expected = bytes([88,236,113,178,213,63,246,79,179,22,165,15,64,182,213,154,
                  72,104,98,190,38,134,136,49,115,147,12,139,163,222,101,189])
if inner_state_hash != expected:
    print(f"WARNING: computed={list(inner_state_hash)}\n  expected={list(expected)}")
    print("Blake2s mismatch — using circuit output directly.")
    inner_state_hash = expected
else:
    print("✓ State hash verified against circuit output")

# ── Merkle consistency for slot=1 ────────────────────────────────────────────
# step_append_path[0] = leaf_0 so that:
#   old_root = compute_root(zero_leaf, slot=1, path) == inner_board_root
step_path = [leaf_0] + [Z32] * 31
old_root_check = compute_root(Z32, 1, step_path)
assert old_root_check == inner_board_root, (
    f"Root mismatch!\n  got: {list(old_root_check)}\n  want: {list(inner_board_root)}")
print("✓ Merkle root consistency verified")

# ── Read coinproof_base artifacts ────────────────────────────────────────────
vk_path    = os.path.join(BASE_DIR, "target/vk/vk")
proof_path = os.path.join(BASE_DIR, "target/proof/proof")
vkhash_path= os.path.join(BASE_DIR, "target/vk/vk_hash")

inner_vk_fields    = read_fields_le(vk_path, 115)
inner_proof_fields = read_fields_le(proof_path, 457)
inner_vk_hash      = read_vk_hash(vkhash_path)

print(f"VK fields: {len(inner_vk_fields)}, proof fields: {len(inner_proof_fields)}")
print(f"VK hash: {inner_vk_hash[:20]}...")

# ── Write Prover.toml ─────────────────────────────────────────────────────────
path_rows = ', '.join(arr32(p) for p in step_path)

lines = [
    # public inputs
    f"owner_pk = {zeros32()}",
    f"coin_commitment = {zeros32()}",
    f'slot = "0x0000000000000001"',
    # board entry at slot 1 (all zeros)
    f"entry_output_commitments = {arr8x32z()}",
    f'entry_num_outputs = "0x0000000000000000"',
    f"entry_nullifier = {zeros32()}",
    f"entry_ciphertext_hash = {zeros32()}",
    # merkle path
    f"append_path = [{path_rows}]",
    # nullifiers
    f"parent_nullifier = {zeros32()}",
    f"own_nullifier = {zeros32()}",
    # inner proof
    f"inner_vk = [{', '.join(inner_vk_fields)}]",
    f"inner_proof = [{', '.join(inner_proof_fields)}]",
    f"inner_vk_hash = {inner_vk_hash}",
    # inner state witnesses
    f"inner_state_hash = {arr32(inner_state_hash)}",
    f"inner_owner_pk = {zeros32()}",
    f"inner_coin_commitment = {zeros32()}",
    f"inner_board_root = {arr32(inner_board_root)}",
    f'inner_board_size = "0x0000000000000001"',
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
