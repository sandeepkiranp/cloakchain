#!/usr/bin/env python3
"""Generate Prover.toml for coinproof_base (slot 0, no recursion)."""

def arr32():
    return '[' + ', '.join(['"0x00"'] * 32) + ']'

def arr8x32():
    row = '[' + ', '.join(['"0x00"'] * 32) + ']'
    return '[' + ', '.join([row] * 8) + ']'

def arr32x32():
    row = '[' + ', '.join(['"0x00"'] * 32) + ']'
    return '[' + ', '.join([row] * 32) + ']'

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
    f'append_path = {arr32x32()}',
    f'is_receipt_hint = false',
]

with open('Prover.toml', 'w') as f:
    f.write('\n'.join(lines) + '\n')

print("Prover.toml written.")
