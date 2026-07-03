#!/usr/bin/env python3
"""Generate Prover.toml for the coinproof base case (slot 0, no inner proof, no spend proof)."""
import subprocess, sys

def b32():
    """32-byte zero array as TOML inline array of hex strings."""
    return '["0x00"] * 32'

def arr32():
    return '[' + ', '.join(['"0x00"'] * 32) + ']'

def arr8x32():
    """[[u8;32];8] — 8 rows of 32 zero bytes each."""
    row = '[' + ', '.join(['"0x00"'] * 32) + ']'
    return '[' + ', '.join([row] * 8) + ']'

def arr_fields(n):
    """[Field; n] — n zero field elements."""
    return '[' + ', '.join(['"0x0000000000000000000000000000000000000000000000000000000000000000"'] * n) + ']'

def arr32x32():
    """[[u8;32];32] — 32 rows of 32 zero bytes (Merkle path)."""
    row = '[' + ', '.join(['"0x00"'] * 32) + ']'
    return '[' + ', '.join([row] * 32) + ']'

lines = []

# --- coin being tracked (public) ---
lines.append(f'owner_pk = {arr32()}')
lines.append(f'coin_commitment = {arr32()}')

# --- current board slot (public) ---
lines.append(f'slot = "0x0000000000000000"')

# --- board entry at slot 0 ---
lines.append(f'entry_output_commitments = {arr8x32()}')
lines.append(f'entry_num_outputs = "0x0000000000000000"')
lines.append(f'entry_nullifier = {arr32()}')
lines.append(f'entry_ciphertext_hash = {arr32()}')

# --- Merkle append path (32 siblings) ---
lines.append(f'append_path = {arr32x32()}')

# --- nullifiers (public) ---
lines.append(f'parent_nullifier = {arr32()}')
lines.append(f'own_nullifier = {arr32()}')

# --- inner proof (not used when has_inner = false) ---
lines.append(f'has_inner = false')
lines.append(f'inner_vk = {arr_fields(115)}')   # UltraHonkVerificationKey = [Field; 115]
lines.append(f'inner_proof = {arr_fields(457)}') # UltraHonkProof = [Field; 457]
lines.append(f'inner_vk_hash = "0x0000000000000000000000000000000000000000000000000000000000000000"')
lines.append(f'inner_state_hash = {arr32()}')
lines.append(f'inner_owner_pk = {arr32()}')
lines.append(f'inner_coin_commitment = {arr32()}')
lines.append(f'inner_board_root = {arr32()}')
lines.append(f'inner_board_size = "0x0000000000000000"')
lines.append(f'inner_received_at_valid = false')
lines.append(f'inner_received_at = "0x0000000000000000"')
lines.append(f'inner_spent = false')
lines.append(f'inner_parent_nullifier = {arr32()}')
lines.append(f'inner_parent_nullifier_seen = false')

# --- spend proof (not used when has_spend_proof = false) ---
lines.append(f'has_spend_proof = false')
lines.append(f'spend_vk = {arr_fields(115)}')
lines.append(f'spend_proof = {arr_fields(457)}')
lines.append(f'spend_vk_hash = "0x0000000000000000000000000000000000000000000000000000000000000000"')
lines.append(f'spend_proof_state_hash = {arr32()}')
lines.append(f'spend_board_root = {arr32()}')
lines.append(f'spend_output_commitments = {arr8x32()}')
lines.append(f'spend_num_outputs = "0x0000000000000000"')

with open('Prover.toml', 'w') as f:
    f.write('\n'.join(lines) + '\n')

print("Prover.toml written.")
