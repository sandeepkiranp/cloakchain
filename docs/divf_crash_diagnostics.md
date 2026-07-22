# SP1 6.2.3 DivF Crash — Diagnostic Summary

## Update 3: `contains_first_shard` was also wrong — real cause is `exit_code=1` in the deferred (VFY-G16) proof

A second nsac run with the `contains_first_shard` print (marker `75xxxxxxx`) showed all 4
compress-batch entries with clean boolean values (0, 0, 1, 0) — that check also passes. So
**neither** `vk_root` **nor** `contains_first_shard` is the bug.

Re-reading the crash trace against `deferred.rs` (not `compress.rs`) instead: the `800000000`
marker (the deferred-proof `vk_root` check, for the externally-supplied proof passed via
`write_proof`) appears with no success dump before the crash, meaning **the crashing program
is the deferred verifier**, not a compress fold. Right after `deferred.rs`'s (passing) 8-word
`vk_root` loop, the code calls `assert_recursion_public_values_valid` (an 8-word Poseidon2
digest check — matches the Poseidon2 ops + 8-word SubF/DivF loop seen at steps
174490–174552), then:
```rust
builder.assert_felt_eq(current_public_values.is_complete, SP1Field::one());  // passes
builder.assert_felt_eq(current_public_values.exit_code, SP1Field::zero());   // CRASHES
```
This matches exactly: step 174553/174554 (`is_complete==1`, dynamic-vs-dynamic, passes),
step 174555 (`exit_code==0`, rhs is the literal zero constant at 316465, **fails**).

**Root cause:** the externally-supplied deferred proof — VFY-G16's compressed proof, fed into
coinproof via `write_proof` — has `exit_code=1`. In `program-vfy-g16/src/main.rs`:
```rust
verify_sp1_spend_proof(&spend_proof_bytes, &pv_encode, &spend_vkey_hash)
    .expect("Groth16 spend proof verification failed");
```
A panic in an SP1 guest converts to a clean `halt(1)` — proving still succeeds (no crash, no
visible error), just with `exit_code=1` instead of 0. SP1's deferred verifier then correctly
rejects it, three layers removed from where the real problem is.

Note this is **not** the same check that already passed: `client.verify(&genesis_proof, ...)`
in `script/src/bin/main.rs` (right after generating the genesis Groth16 proof) uses SP1's own
official verifier and succeeds. `verify_sp1_spend_proof` is this project's own hand-rolled
verifier (`groth16-verifier/src/lib.rs`, built on the vendored `snark-bn254-verifier` crate
instead of the official `ark-bn254`-based `sp1-verifier`), so the proof being valid per SP1
doesn't mean it's valid per this custom implementation — the bug is in the custom one.

**Ruled out so far:**
- VK staleness — `groth16-verifier/vk-artifacts/groth16_vk.bin` is byte-identical
  (sha256 `4388a21c...`) to nsac's actual cached `~/.sp1/circuits/groth16/v6.1.0/groth16_vk.bin`.
- Byte layout / hash scheme in `groth16-verifier/src/lib.rs` — matches the official
  `sp1-verifier-6.2.3` reference implementation exactly (same offsets, same
  SHA256-with-top-3-bits-masked digest, same public input ordering).
- An off-by-4-byte issue found in `vendor/snark-bn254-verifier/src/groth16/converter.rs`'s
  `commitment_key_g`/`commitment_key_g_root_sigma_neg` parsing (relative to
  `groth16-verifier`'s `build_padded_vk()` padding boundary) — confirmed harmless, since
  `verify_groth16` in `vendor/snark-bn254-verifier/src/groth16/verify.rs` never reads
  `vk.commitment_key` at all.

**Added diagnostic** (`script/src/bin/main.rs`, `run_internal_prove`'s `"vfy-g16"` branch):
a `client.execute(...)` pre-check mirroring the existing `coinproof` diagnostic, since a
guest panic converting to `halt(1)` produces no visible error during `.prove()` — this
should surface the actual panic message/exit behavior directly on the next run.

**Next step:** run on nsac and grep for `[VFY-G16-DIAG]` to see whether execute() surfaces
the panic directly. If it does, the fix is in `groth16-verifier`'s custom Groth16
verification logic (likely in `vendor/snark-bn254-verifier`'s pairing/point-encoding
assumptions, or a mismatch between what `snark_bn254_verifier::Groth16Verifier` expects for
proof/VK point encoding and what SP1's gnark backend actually produces) — not in the SP1
recursion internals this whole investigation started with.

---

## Update 2: the `vk_root` theory was wrong — real suspect is `contains_first_shard`

With the `vk not allowed` blocker fixed (see below) and the print diagnostics from
`compress.rs`/`deferred.rs` in place, coinproof reached the exact same
`DivFOutOfDomain` crash (step 174554/174555, addr 316465) as originally reported. The
`PRINTF=` output from the run (`~/coinproof_run.log`) shows:

- Compress-batch `vk_root` check (marker `7000000xx`): **4 proofs (i=0..3), all matching**
  — expected and actual `vk_root` are identical (8/8 words) for every entry.
- Deferred-verifier `vk_root` check (marker `8000000xx`): **1 proof (idx 0), also matching.**

So the multi-week `vk_root` mismatch hypothesis is **not the actual bug** — every vk_root
comparison in the batch passes. The crash trace itself confirms this a different way: its
post-mortem shows `in2_last_writer: step=1 [Mem::Write @316465=0x00000000]` — address
316465 is the recursion program's single shared **compile-time zero constant**
(`Imm::F(SP1Field::zero())`, cached by the compiler and reused as the divisor for every
`assert_felt_eq(x, y)` → `SubF(diff,x,y); DivF(out,diff,ZERO)` in the whole program), not a
witnessed `vk_root[1]` value. It was never going to change no matter what chip-activation
fix was tried, because it was never derived from proof data in the first place.

The crash trace shows exactly two more `SubF`/`DivF` pairs immediately after the (passing)
8-word `vk_root` loop for batch index `i=3`:
- step 174553/174554: `in1@194` vs `in2@317646` — **passes** (both dynamic values, equal).
  This lines up with `C::range_check_felt(..., current_public_values.num_included_shard, ...)`
  in `compress.rs`, which decomposes into bits then asserts the reconstruction matches.
- step 174555 (crashes on the following `DivF`): `in1@196` vs `in2@316465` (the zero
  constant) — this matches `compress.rs`'s very next check:
  ```rust
  // Verify that `contains_first_shard` is boolean.
  builder.assert_felt_eq(
      current_public_values.contains_first_shard
          * (current_public_values.contains_first_shard - SP1Field::one()),
      SP1Field::zero(),
  );
  ```
  A literal `SP1Field::zero()` rhs is the signature of this exact check (not a
  proof-to-proof comparison). `X * (X - 1) = 1` (the crashing value) implies
  `current_public_values.contains_first_shard` for batch entry `i=3` is some field element
  that is **neither 0 nor 1** — i.e. not boolean, for whichever proof (normalize or the
  deferred-lifted one) sits at position 3 in this compress fold.

**Added diagnostic** (`vendor/sp1-recursion-circuit/src/machine/compress.rs`): a
`RECURSION_DIAG`-gated print of `(750_000_000 + i, contains_first_shard)` right before this
assertion, to confirm the exact non-boolean value and which batch index it comes from on
the next run. Grep the next log for `PRINTF=75` to find it (should be the very last
`PRINTF=` line before the crash).

If confirmed, the fix is in whichever code path produces `current_public_values` for batch
index 3 (either a `get_normalize_witness`-derived proof or the deferred-lifted proof) —
that path is failing to correctly set `contains_first_shard` to a clean 0/1 value.

---

## Update: earlier, unrelated blocker — `vk not allowed`

Before the `DivFOutOfDomain` crash below can even be reproduced, a first nsac run hit a
**different, earlier** failure during VFY-G16 compression (before coinproof is even reached):

```
ERROR task failed with fatal error: vk not allowed
ERROR Controller: task failed: Fatal(Reduction task local_worker_... failed)
```

This is not a runtime ASM crash — it's `RecursionVks::open()`/`verify()` in
`sp1-prover-6.2.3/src/worker/prover/recursion.rs` rejecting a recursion-circuit
verifying-key hash that isn't present in SP1's embedded `vk_map.bin` allow-list. That
check is controlled by `vk_verification`, which **defaults to `true`** for the CPU
prover (`RecursionProverConfig::default()`), meaning every normalize/compress/deferred/
shrink shape produced while proving a custom program must already be registered in
Succinct's shipped map. VFY-G16 and coinproof are custom, BN254-heavy guest programs —
not part of that registered set — so this fails immediately.

SP1 ships an escape hatch for exactly this (local/dev proving of custom programs):
`WITHOUT_VK_VERIFICATION=1`, read in `cpu_worker_builder_with_machine`
(`sp1-prover-6.2.3/src/worker/builder.rs:328`) — **but only when compiled with
`sp1-prover`'s `experimental` Cargo feature**, which `script/Cargo.toml` did not enable.
Without it, the whole `#[cfg(feature = "experimental")]` block (including the env var
check) is compiled out and `vk_verification` can never be turned off.

**Fix applied:**
- `script/Cargo.toml` — added `"experimental"` to `sp1-sdk`'s feature list.
- `script/src/bin/main.rs` (`prove_subprocess`) — added `.env("WITHOUT_VK_VERIFICATION", "1")`
  alongside the existing `SHARD_SIZE`/`RECURSION_DIAG` env vars for both the `vfy-g16` and
  `coinproof` subprocess branches.

This should let proving get past VFY-G16 and back to reproducing the `DivFOutOfDomain`
crash described below (if it's still present — note that running with
`vk_verification=false` also changes `RecursionVks` to its `dummy()` mode, i.e. a
padding-index-based root rather than a real vk-hash Merkle tree, which may itself
interact with the `vk_root` mismatch investigation below).

---

## The Crash

**Error:** `RuntimeError::DivFOutOfDomain { in1: 1, in2: 0 }`  
**Step:** 174554 of the **compress** recursion program  
**Triggered by:** `coinproof` via `client.prove(...).compressed().run()`

---

## What `base_assert_eq` compiles to

In `sp1-recursion-compiler-6.2.3/src/circuit/compiler.rs`:

```rust
fn base_assert_eq(lhs, rhs) {
    SubF(diff, lhs, rhs)       // diff = lhs - rhs
    DivF(out, diff, Imm::F(0)) // crashes if diff ≠ 0 (i.e. lhs ≠ rhs)
}
```

The `DivF` denominator is always the constant zero (`Imm::F(SP1Field::zero())`), cached at a single ASM address. If `diff = 0`, then `0/0 = 1` by convention (OK). If `diff ≠ 0`, the executor raises `DivFOutOfDomain`.

---

## Exact Assertion Failing

In `sp1-recursion-circuit-6.2.3/src/machine/compress.rs` (lines 199–201):

```rust
for (expected, actual) in vk_root.iter().zip_eq(current_public_values.vk_root.iter()) {
    builder.assert_felt_eq(*expected, *actual);
}
```

- `vk_root` = root from the Merkle witness (`vk_merkle_data.root`) = **[1, 1, …]** in the failing run
- `current_public_values.vk_root[1]` = from some shard proof's public values = **0**

Element **[0]** passes (both = 1). Element **[1]** fails (Merkle=1, shard proof=0).

---

## Key Address in the Executor

| Address | Role | Value (coinproof) | Value (VFY-G16) |
|---------|------|-------------------|-----------------|
| **316465** | `pv.vk_root[1]` from a shard proof (hint-loaded) | **0** ← WRONG | non-zero (correct) |

- Written at execution step 1 via the **Hint** instruction (from the compress witness stream).
- Because it is 0 instead of the expected `vk_root[1]` from the Merkle witness, `SubF` produces `diff = 1`, and `DivF(out, 1, const_zero)` crashes.

---

## Root Cause Hypothesis

Some **shard proof** in the compress batch has `pv.vk_root = [1, 0, …]` instead of the expected `[1, 1, …]` (the dummy `recursion_vks.root()`).

**Why VFY-G16 is fine:** VFY-G16 does not call `verify_sp1_proof` inside its guest program, so it has no deferred proofs and its compress batch only contains normalize proofs, all correctly tagged with `recursion_vks.root()`.

**Why coinproof may differ:** `program-coinproof/src/main.rs` calls `verify_sp1_proof(&vkey, …)` (and optionally `verify_sp1_proof(&vfy_g16_vkey, …)`), creating **deferred proofs**. The deferred circuit sets `pv.vk_root = vk_merkle_data.root`. If the `recursion_vks` used when building the deferred witness differs from the `recursion_vks` used by the outer compress circuit, element [1] of the root will mismatch.

---

## Hypotheses Ruled Out

| Hypothesis | Outcome |
|---|---|
| Missing `Uint256MulMod` chip activation | ❌ Adding it left addr@316465 still = 0 |
| 8 dummy BN254 ecalls | ❌ Did not change addr@316465 value |
| Constant-zero address aliased with hint address | ❌ They are distinct addresses (compiler panics on double-write) |

---

## Diagnostics Infrastructure

**File:** `vendor/sp1-recursion-executor/src/lib.rs`  
**Env var:** `RECURSION_DIAG=1`

When enabled, on any `DivFOutOfDomain`:
1. Dumps the **last-write** history for watched addresses (including addr@316465 ± 5).
2. Dumps **all Mem::Write** ops in the first 300 execution steps (to identify which witness element lands at addr@316465).
3. Dumps the **last 100 instructions** before the crash.
4. Logs every **Hint write** to watched addresses with its sequence number and full block value.

**Watched addresses:** `316460–316470` and `2013019–2013020`.

---

## Next Diagnostic Step (superseded — see "Circuit-Level Print Diagnostics" below)

Run coinproof with `RECURSION_DIAG=1` and collect the init-dump output. Map address 316465 to its **hint sequence number** and identify which compress-witness field (which shard proof, which PV offset) it corresponds to. This will confirm whether the mismatched proof is:

- A **normalize** shard proof (vk_root set by `get_normalize_witness` → `recursion_vk_root()`)
- The **deferred certificate** (vk_root set by the deferred circuit from `vk_merkle_data.root`)
- Some other element

Once the offending witness field is identified, the fix is to ensure both it and the compress Merkle witness use the same `recursion_vks.root()` value.

The raw-address approach above requires reverse-engineering which witness field lands at
addr@316465 from a list of `Mem::Write`/`Hint` operations — doable, but indirect. We added a
more direct diagnostic instead (below): the circuit itself now prints the exact values being
compared, labeled by proof-batch index, right before the assertion that crashes.

---

## Circuit-Level Print Diagnostics (current approach)

Both `compress.rs:199` and `deferred.rs:182` (the two places in SP1 6.2.3 that assert
`vk_root` consistency — see table below) run an identical pattern:

```rust
for (expected, actual) in vk_root.iter().zip_eq(current_public_values.vk_root.iter()) {
    builder.assert_felt_eq(*expected, *actual);   // ← crashes here via SubF+DivF
}
```

`vk_root` and `current_public_values.vk_root` are DSL `Felt` variables — their concrete
values are only known when the compiled recursion program *executes*, not when the Rust
circuit-building code runs. The SP1 DSL has a `Builder::print_f`/`print_debug` API that
compiles to a `Print` ASM instruction, which the executor unconditionally writes to
`debug_stdout` (inherited stdout, since `prove_subprocess` doesn't redirect the child's
stdout) as `PRINTF=<value>` at the point in execution where it's reached.

We vendored `sp1-recursion-circuit-6.2.3` (previously only `sp1-recursion-executor` was
vendored) into `vendor/sp1-recursion-circuit`, patched via `[patch.crates-io]` in the
workspace `Cargo.toml`, and added `RECURSION_DIAG`-gated prints immediately before each
assertion loop:

- **`compress.rs`** (outer compress fold, `vks_and_proofs.into_iter().enumerate()`): prints
  `PRINTF=700000000+i` (marker), then the 8 words of `vk_root` (expected — the compress
  circuit's own Merkle-witness root), then the 8 words of `current_public_values.vk_root`
  (actual — this shard proof's baked-in root), where `i` is the position of the offending
  proof in the compress batch.
- **`deferred.rs`** (verifying externally-supplied deferred proofs, e.g. the previously
  compressed inner coin-proof / vfy-g16 proof passed in via `write_proof`): prints
  `PRINTF=800000000+deferred_idx` (marker), then the shard proof's `vk_root` (actual), then
  the witnessed `vk_root` (expected).

Since `Print` instructions execute in program order, the **last `PRINTF=` block emitted
before the `DivFOutOfDomain` crash** is exactly the offending proof: its marker tells you
whether it's a compress-batch entry or an externally-supplied deferred proof, and its index,
and the two 8-word blocks show precisely which word (expected to be word[1], per the earlier
raw-address finding) disagrees and what the two conflicting values are.

### How to run (on nsac, where the actual proving happens)

`RECURSION_DIAG=1` is already auto-set for the `coinproof` subprocess in
`script/src/bin/main.rs` (`prove_subprocess`), so no extra env var is needed — just run the
normal proving command and capture stdout:

```shell
RUST_LOG=info cargo run --release -- --prove 2>&1 | tee /tmp/coinproof_run.log
```

Then, once it crashes:

```shell
grep -n "PRINTF=" /tmp/coinproof_run.log | tail -40
```

Look at the last marker line (`700000000+i` or `800000000+deferred_idx`) before the crash
and its following 16 values (8 expected, 8 actual) — word[1] of the "actual" block should be
the `0` we've been chasing. If the marker is in the `7xxxxxxxx` range, the culprit is at
batch position `i` in the outer compress fold (need to cross-reference with the reduce-tree
order — normalize shards vs. the deferred-lifted proof — to know which). If it's in the
`8xxxxxxxx` range, the culprit is one of the *externally supplied* proofs from an earlier
`write_proof` call (previous coin-proof or vfy-g16), meaning that proof's `vk_root` was baked
in under a different `recursion_vks` state than the current run's — pointing at a
cross-run/cross-process `recursion_vks` mismatch rather than an in-process one.

**Files changed:**
- `Cargo.toml` — added `sp1-recursion-circuit = { path = "vendor/sp1-recursion-circuit" }` to `[patch.crates-io]`
- `vendor/sp1-recursion-circuit/` — new vendored crate (copied from the 6.2.3 crates.io source)
- `vendor/sp1-recursion-circuit/src/machine/compress.rs` — added print diagnostics before the vk_root assertion loop
- `vendor/sp1-recursion-circuit/src/machine/deferred.rs` — added print diagnostics before its vk_root assertion loop (also added `.enumerate()` to the batch loop to get an index)

This is a temporary diagnostic patch — once the culprit is identified and fixed, the
`if std::env::var("RECURSION_DIAG")...` blocks in both files can be removed (or left, since
they're zero-cost when the env var isn't set to `"1"`).

---

## Relevant Source Locations

| File | Line(s) | What |
|------|---------|------|
| `sp1-recursion-compiler-6.2.3/.../compiler.rs` | 214–224 | `base_assert_eq` → SubF + DivF pattern |
| `sp1-recursion-circuit-6.2.3/.../compress.rs` | 199–201 | Unconditional `vk_root` assertion loop |
| `sp1-recursion-circuit-6.2.3/.../deferred.rs` | 135, 271 | `vk_root = vk_merkle_data.root` |
| `sp1-prover-6.2.3/.../recursion.rs` | 899–903 | `get_normalize_witness` sets `vk_root = recursion_vk_root()` |
| `sp1-prover-6.2.3/.../recursion.rs` | 864–866 | `recursion_vk_root()` → `recursion_vks.root()` |
| `sp1-prover-6.2.3/.../recursion.rs` | 84, 113 | `RecursionVks::from_map` → `MerkleTree::commit` |
| `vendor/sp1-recursion-executor/src/lib.rs` | 83–113, 611–630 | Diagnostic infrastructure |
