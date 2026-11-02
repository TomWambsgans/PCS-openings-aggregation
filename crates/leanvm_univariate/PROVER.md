<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# The prover of the univariate PIOP (milestone 2)

`src/prover/` proves SPEC.md's statement on real leanVM 42422001 traces. It writes the stream that
`verifier::reduce` reads (through the contract's Keccak-256 chain) and one WHIR opening per commitment.

## Status

**End to end, with BLAKE2s's argument**, on the point-claim ABI, in the variant `Blake2s::Flock(FLOCK_LEANVM_SKIP)`:
Flock (a′) with leanVM's skip of 6. It runs through:

- `C1`, the challenges, then leanVM's own Flock prover: zerocheck, lincheck, the 64 slices;
- the matrices' reduction and the ring map;
- the heap and every quotient, `C2`, the values at `t`;
- the batching sumcheck and the three WHIR openings;
- Flock's two setup claims, on `A0` and `B0` (the BLAKE2s R1CS, `2^28` words each), each committed and opened with
  WHIR (`matrices.rs`).

On the reference trace (1,000 leanXMSS signatures, 1,023,109 cycles):

- the Rust verifier accepts the proof, and all five WHIR openings verify (`C1`, `C2`, setup, `A0`, `B0`);
- the EVM contract accepts the proof's real calldata (283,941 gas of execution). Its `PCS_OPEN` mock attests
  exactly the five claims the WHIR openings prove;
- flipped stream bytes are rejected.

The same holds without BLAKE2s's argument (`Blake2s::Omitted`), at 73,836 gas, which is SPEC §10's number on
random streams.

**Not built** (§ "What is missing"):

- (a′)'s skip of 3 (`FLOCK_MAIN`): leanVM's zerocheck prover hard-codes a skip of 6;
- extension W's openings.

## How it runs

1. **Traces.** `src/prover/dump/apply.sh <leanVM 42422001 checkout>` adds `trace_dump.rs` to leanVM's
   `leanvm_core`. Then any leanVM proof made with `LEANVM_TRACE_DUMP=<dir>` writes, right after leanVM's witness
   build:
   - every column it commits or carries, the stacked bytecode and the sizes;
   - Flock's prover inputs (`z`, `A z`, `B z`, the lincheck's packed bytes).

   That is leanVM's own execution and trace generation, unchanged. On h1, with the gas-dump command of
   `crates/leanvm_flock_gas/dump` applied first:

   ```sh
   cd /root/pcs-quotient-fv/leanvm-univariate-prover/leanvm-42422001
   LEANVM_TRACE_DUMP=../traces/xmss1000 ./target/release/leanvm --log-inv-rate 1 gas-dump --xmss 1000 --out ../traces/proof1000
   ```

   `xmss32` (38,209 cycles) and `xmss1000` (1,023,109 cycles) are in `/root/pcs-quotient-fv/leanvm-univariate-prover/traces/`
   (0.16 GB and 3.0 GB).
2. **Proving and checking.** Build with `RUSTFLAGS="-C target-cpu=native"`, as leanVM's own `.cargo/config.toml`
   does. Without it the field falls back to software carry-less products, 25× slower.

   ```sh
   LEANVM_TRACE=<trace dir> RUSTFLAGS="-C target-cpu=native" \
     cargo test --release -p leanvm_univariate --test prove_real -- --ignored --nocapture --test-threads 1
   ```

   - `identities_hold_on_the_domain`: SPEC's identities on the domain itself.
   - `proves_and_verifies_with_flock` and `proves_and_verifies` (without Flock): the proof, the quotients'
     degrees, every commitment's combined relations against its stack, the Rust verifier, the EVM contract on the
     real calldata, and mutations.
   - `unused_words_are_not_relied_on`: the stacks' words past their blocks filled with pseudo-random words.

   `tests/prove_kernels.rs` times the NTT kernels alone.

## The prover, phase by phase (`src/prover/prove.rs`)

1. **`C1`** (`columns.rs`, `stack.rs`).
   - Every table column, its values on `V_r`, goes through the inverse additive NTT of `crates/quotient/src/domain.rs`
     (novel basis), then a subset-sum transform to basis `B` (`b_k = Σ_{j ⊆ k} a_j`).
   - This applies to BLAKE2S's 18 limbs (the copies), the counter inverses `z_T` (`1/Π c_j` on active rows, 0 on
     padding rows), the memory's four columns and the bytecode's final counts.
   - `q_flock` is leanVM's packed witness, as values.
   - The stack is `stacks::StackLayout::new` on the verifier's column list (rebuilt in `stack.rs`, and checked
     against `Reduced::stack_vars`).
   - The commit is leanVM's WHIR (`pcs::whir::commit_tree_in`), rate 1/2, 64 lanes.
2. **Setup `F`.** The 16 tuple slots, interleaved (word `slot + 16 k`): slot 0 `SEP_BYTECODE`, 1 the pc `g^i`, 2
   zero, 3..16 leanVM's stacked bytecode, whose slots 0..2 are zero (checked). Also the addresses `g^i` on `V_lm`.
3. **The challenges** `α, β, γ` (`KeccakWriter`, the contract's chain).
4. **Flock** (`flock.rs`, behind one call).
   - `lv42_flock::hash::Blake2sSetup::prove_reduction_precomputed` is leanVM's prover, vendored unchanged
     (`crates/lv42_*`). It runs on leanVM's witness buffers and writes to the Keccak chain through
     `lv42_fiat_shamir::transcript::Transcript` (`flock::Chain`). It produces the zerocheck (skip 6, 64 values, 26
     rounds, `v_a`, `v_b`), the lincheck (8 rounds) and the 64 slices.
   - The challenges it drew are kept. From them, the matrices' reduction (`k + 6 = 12` rounds of `Σ L(x) s(y) G'(x,
     y)`, then `a`, `b`) is written as `flock_min::reduce_terminal` reads it.
   - Then the ring map's 6 challenges. The point the slices are at is checked against the one the verifier derives.
5. **The heap** (`bus.rs`).
   - Every leaf: `Π D'/Π D` per active row, 1 per padding row, `D_init/D_fin` per memory cell and per instruction.
   - One batch inversion each, then the products up the tree.
   - The root is checked against `fp(final)/fp(initial)`.
6. **The quotients** (`quotients.rs`).
   - Each numerator is evaluated on the extension coset `D_m = ω_{2^m} + V_m`, `2^m ≥` the verifier's count, and
     divided there by the vanishing polynomial. The inverse NTT on `D_m` gives the quotient's novel coefficients.
   - The sub-cosets of `V_r` are taken one at a time. `w_r`, and the lift `w_{r_W}/w_r`, are constant on them.
   - Chunks: `Q = Q_0 + w_{e_0}(Q_1 + w_{e_1} Q_2)` are slices of the novel coefficients, since
     `X_{2^e + k} = w_e X_k`. Each is put in basis `B`.
   - `ℓ_j` on a sub-coset is the slot's multilinear on a shifted cube `bits(i) + y(ω_first)`: per variable,
     `(v_0, v_1) ↦ (v_0 + δ(v_0 + v_1), v_1 + δ(v_0 + v_1))`, in `K`.
   - A quotient whose numerator does not vanish on its domain has full degree. Every quotient's degree is checked
     below the verifier's count.
7. **`C2`**: the heap (basis `B`, three limbs), `Q_tree`'s two chunks, `Q_W`'s and every leaf quotient's chunks.
8. **`t`, and the 84 values** in the verifier's order (`sent_columns`, then the fingerprints whose tuple reads an
   unsent column, the memory's, the bytecode's, `T(t)`, `Q_W(t)`).
9. **`ρ`.** The prover runs `verifier::reduce` in weighted mode on the stream so far, which reads nothing after
   `ρ`, to learn each commitment's combined claim. The check `Σ_u W_k(u) S_k(u) = v_k` is made against the
   committed stacks.
10. **The batching sumcheck** (`batch.rs`, behind one call).
    - Each commitment's weight is written out on its stack (`dense_weight`: the verifier's `weight_at`, term by
      term, one eq table per point).
    - The ring switch's 64 Frobenius-twisted terms on `q_flock` read one eq table: on the cube
      `eq(φ^k(P), u) = eq(P, u)^(2^k)`, so their sum is one GF(2)-linear map of it (24 byte tables).
    - The rounds go low variable first. A stack shorter than the longest is folded as zero-padded, so its
      zero-extension's `(1 + r_j)` factors fall out of the same folds.
    - The prover sends two scalars a round (`q(0)` and `q`'s `X^2` coefficient), then each stack's value at its
      part of the end point.
11. **The openings** (`opening.rs`).
    - One point claim per commitment, proven with leanVM's WHIR (`recursive_prover_with_lane_tensors`) and checked
      with its verifier (`verifier::whir::verify_whir`), in the transcript shape of `crates/quotient/src/opening.rs`.
    - WHIR commits only the lanes that carry data. Its prover needs a weight that vanishes on the absent lanes, so
      the claim's `eq(point, ·)` is restricted to the committed lanes. That is the same claim, since the stack is
      zero there.
    - So the opening's verifier must know `placed` (the words the blocks fill), which the layout word must fix.

## Measured (h1: AMD Ryzen 7 PRO 8700GE, 16 threads; `RUSTFLAGS="-C target-cpu=native"`)

**Reference workload**: 1,000 signatures, 1,023,109 cycles. Tables have 183,266 / 195,439 / 223,851 / 137,591 /
80,937 / 202,025 rows. The variant is `Flock(FLOCK_LEANVM_SKIP)`.

| phase | seconds |
|---|---:|
| `C1` and setup: inverse NTTs to basis `B` | 0.47 |
| `C1` and setup: WHIR commits (`2^27`, `2^24`) | 0.91 |
| Flock: zerocheck, lincheck, slices (leanVM's), matrices' reduction | 0.54 |
| heap: leaves, products, inverse NTT (`2^23` E) | 0.49 |
| quotient: tree (`T` on a coset of `2^24`) | 0.73 |
| quotients: leaves (8 blocks) | 4.82 |
| quotient: constraints `Q_W` | 1.85 |
| `C2`: chunks in basis `B` | 0.94 |
| `C2`: WHIR commit (`2^27`) | 0.50 |
| values at `t` | 0.02 |
| claims: dense weights (with the ring switch's) and the combined-claims check | 3.06 |
| batching sumcheck (27 rounds over `2^27 + 2^27 + 2^24`) | 2.11 |
| openings: WHIR (3) | 1.81 |
| **total** (the trace's generation, by leanVM, apart) | **18.56** |

- **Peak RSS 15.7 GB.** Without Flock it is 13.5 GB and 18.0 s. The dense weights (`2^27` E each for `C1` and
  `C2`) and their first fold dominate it.
- **Proof.** The stream is 8,824 bytes: two roots, Flock's 224 scalars (5,376 bytes), 84 values, 27 rounds of 2
  scalars, and 3 values. The WHIR openings are 295,576 / 300,168 / 240,728 bytes (`C1`, `C2`, setup), which the
  block's `PCS_OPEN` aggregation carries.
- **Verifier.** In Rust, reduce and three WHIR openings take 13 ms. The contract runs 283,941 gas of execution on the
  real calldata.

**leanVM 42422001's own prover, same workload, same machine** (`leanvm --tracing gas-dump --xmss 1000`,
measured): 2.12–2.46 s for the whole proof, peak RSS 10.1 GB. That is execute 0.12 s, witness 0.24 s, commit
0.34 s, bus GKR 0.20 s, constraints 0.07 s, Flock 0.39 s and PCS opening 0.76 s.

- The trace generation this prover reuses (execute and witness) is 0.36 s of it.
- This prover is about 8× leanVM's whole prover, measured. SPEC §11 estimated 2–3×.
- Flock costs the same in both (0.39 s leanVM, 0.54 s here with the matrices' reduction).

**Where the time goes** (`tests/prove_kernels.rs`: a K-NTT of `2^18` on a coset takes 1.4 ms, an E-NTT 4.4 ms):

- The leaf quotients are NTT-bound.
  - BLAKE2S's numerator has degree 20.2 n, so its coset is `2^23`, 32 sub-cosets of `V_18`. Each evaluates its 36
    columns: 1,152 NTTs of `2^18`, about 1.6 s.
  - XOR, MUL and DEREF take 16 sub-cosets of about 15 columns each.
  - A batched multi-column NTT, as leanVM's interleaved encode, would cut this.
- The dense weights are written out instead of kept as eq tensors.
- The batching sumcheck's first rounds run over `2^27` E-weights.

**Small trace** (32 signatures, 38,209 cycles): 2.66 s with Flock, 2.1 GB; stream 8,440 bytes; 257,890 gas. leanVM
takes 0.14 s.

## Checked on real traces (32 and 1,000 signatures)

- **On the domain** (`check.rs`, no randomness but the bus's challenges):
  - JUMP's two constraints on every row;
  - every counter nonzero on active rows;
  - padding rows hold `padRow` (informative only);
  - memory cells 0 and 1 are the public input;
  - BLAKE2S's 18 limbs equal `q_flock`'s slots on every row (4,718,592 entries);
  - leanVM's stacked bytecode slots 0..2 are zero;
  - no pull fingerprint vanishes;
  - **the bus balances**: the heap's root is `fp(final)/fp(initial)`;
  - the unused leaves are 1, and the tree holds on `V_H \ V_1`.

  Every one holds.
- **The quotients' degrees are exactly the verifier's counts minus one**, for every quotient at both sizes: tree
  `2^23`; memory `2^21 - 2`; bytecode `2^19 - 2`; XOR 2,176,021; MUL 2,163,848; SET 1,086,864; DEREF 2,221,696;
  BLAKE2S 5,302,978; JUMP 1,098,702; `Q_W` 2,681,548. SPEC's degree formulas are tight, not over-estimates.
- **At `t`**: each commitment's relations, combined by `ρ` (`C1` 82 with the ring switch's, `C2` 13, setup 2 at
  1,000 signatures), against the committed stacks.
- **Flock**:
  - `flock_min::verify(skip 6, slices sent)` accepts leanVM's own Flock prover's messages on the Keccak chain. That
    is the first run of `flock_min` against a real prover.
  - The matrices' terminal holds.
  - The ring switch's target is `q_flock`'s.
  - `A0`'s and `B0`'s claims are the matrices' values: direct evaluation and a WHIR opening each.
  - `A0` and `B0` are built by one walk of the circuit per 64 columns, the weights bits of a word (the walk is
    additive): 0.2 s. A WHIR commit at `2^28` takes 1.2 s each, and an opening 1.7 s.
- **End to end**: the Rust verifier, five WHIR openings, and the EVM contract on the calldata, with `PCS_OPEN`
  registering exactly the proven claims.
- **The stacks' unused words**: past every block, inside the last committed lane, filled with pseudo-random words,
  the proof is accepted all the same. `StackLayout` places the blocks contiguously, so the only unused words are
  the tail. The weights are zero there, and the point claims are on the whole stack's multilinear, whatever the
  tail holds.

## What is missing

1. **(a′)'s skip of 3** (`FLOCK_MAIN`; the prover returns an error).
   - leanVM's zerocheck prover hard-codes `K_SKIP = 6` in its bit-sliced kernels (its round 1 extracts the 6
     packing bits of each K-word).
   - A skip of 3 needs a new round-1 kernel and new bit rounds. The lincheck, the slices, the matrices' reduction
     (`k + 6` rounds) and the ring switch here take `k` as a parameter already.
2. **Extension W** (weighted claims): no opening prover. `PCS_OPEN` would run the weight itself.
3. **The setup roots in the contract** are placeholder constants (`contract::setup_root`). The prover computes the
   real ones (`F`'s; `A0`'s begins `93cd9a03…` and `B0`'s `c0755650…`), which a deployment must put in the code.
4. **The `A0`, `B0` openings run in the test**, after the proof (`tests/prove_real.rs`), not in `prove`. They are
   fixed commitments, opened per proof: about 3 s for the two, not in the phase table above.

## Notes for the verifier and SPEC (from building the prover)

- The verifier needs no change to accept these proofs (`Blake2s::Omitted` or `Flock(FLOCK_LEANVM_SKIP)`,
  `Claims::Point`).
- `PCS_OPEN`'s layout word must fix each stack's `vars` and `placed`: WHIR's verifier needs `placed` to know the
  committed lanes.
- SPEC §3's setup size is `2^23.32` (`2^23 + 2^21` words), not `2^23.2`.
- SPEC §5.3's SET is `4.15 n` at 1,000 signatures (`5(n - 1) + (n - rows) - n`), not `4.6 n`. XOR 8.30 n, MUL 8.25
  n, DEREF 8.48 n, JUMP 8.38 n and BLAKE2S 20.23 n agree with it.
- SPEC §11's estimate (2–3× leanVM's prover) is 8× measured, unoptimized (above).
- The public input in calldata is four big-endian words `(cell0.c0, cell0.c1, cell1.c0, cell1.c1)`
  (`contract::rust_verifier`), not leanVM's little-endian digest bytes. The prover writes it so
  (`Trace::public_input`).
- The program's IV in the seed (`shapes::PROGRAM_IV`, leanVM's BLAKE2s digest of the R1CS and the bytecode) binds
  the setup only through the bytecode. `F` is a deterministic function of the bytecode, so this is enough if the
  contract's `F` root is the one computed from it.
