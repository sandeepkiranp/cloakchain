#!/usr/bin/env python3
"""Generate Prover.toml for coinproof_base (slot 0, no recursion)."""

import hashlib

def blake2s(data: bytes) -> bytes:
    return hashlib.blake2s(data, digest_size=32).digest()

def arr32(b=bytes(32)):
    return '[' + ', '.join(f'"0x{x:02x}"' for x in b) + ']'

def arr8x32():
    return '[' + ', '.join([arr32()] * 8) + ']'

# Proper empty subtree hashes: Z[0] = [0;32], Z[h] = blake2s(Z[h-1] || Z[h-1])
Z = [bytes(32)]
for _ in range(32):
    Z.append(blake2s(Z[-1] + Z[-1]))

# append_path for slot 0: at every depth h, the sibling is the empty subtree Z[h].
append_path = '[' + ', '.join(arr32(Z[h]) for h in range(32)) + ']'

lines = [
    f'owner_pk = {arr32()}',
    f'coin_commitment = {arr32()}',
    f'slot = "0x0000000000000000"',
    f'parent_nullifier = {arr32()}',
    f'entry_output_commitments = {arr8x32()}',
    f'entry_num_outputs = "0x0000000000000000"',
    f'entry_nullifier = {arr32()}',
    f'entry_ciphertext_hash = {arr32()}',
    f'own_nullifier = {arr32()}',
    f'append_path = {append_path}',
    f'is_receipt_hint = false',
]

with open('Prover.toml', 'w') as f:
    f.write('\n'.join(lines) + '\n')

print("Prover.toml written.")
