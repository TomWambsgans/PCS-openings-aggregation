<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# Review M1: the univariate PIOP for leanVM 42422001 (`leanvm-univariate` @ `cee6363`)

An adversarial review of `SPEC.md`, `SPEC-FLOCK.md`, `src/{verifier,claims,heap,domain,stacks,contract}.rs` and
`review/leanvm_univariate_params.py`. I tried to make the verifier accept a false statement, and compared its
statement with leanVM 42422001's (`crates/verifier` there, its port in `crates/leanvm_flock_gas`, and the Lean
relation `M3Holds` on branch `lean-lv42`).

**Verdict.** I found no soundness break. The fixed-shape statement the contract proves is leanVM's relation
`M3Holds`, and the PIOP's error is about 2^-142 after the union bound over the level-0 lists. The findings below are
ranked. The most serious are a narrower statement than leanVM's (F1), unbound setup and layout identifiers (F2),
and a soundness headline that leaves out the openings (F3). None of them lets a prover forge a proof.

**Method.**

- **An independent honest prover** (`tests/review_honest.rs`), written from SPEC.md and leanVM's tables, not from
  the verifier's code:
  - polynomials in the monomial basis, every identity divided exactly by its vanishing polynomial;
  - basis `B` by interpolation on `V_r`, the values at `t` by monomial evaluation;
  - the batching sumcheck's prover over the stacks;
  - a real VM execution of 15 to 31 cycles over all six tables. Flock is omitted (`Blake2s::Omitted`), so
    BLAKE2S's rows are bus rows only.
- **Experiments on that prover**, all run on h1 (`/root/pcs-quotient-fv/review-univariate-m1`).
- **The soundness recomputed from the code's layouts** (`review/review_m1_soundness.py`).

```sh
cargo test --release -p leanvm_univariate --test review_honest -- --nocapture   # 8 tests: honest, controls, experiments, contracts
cargo test --release -p leanvm_univariate --test review_probe -- --nocapture    # every shape's heap, stacks, relations
python3 -I review/review_m1_soundness.py                                         # the recomputed soundness
```

## Findings, most severe first

### F1. The statement is narrower than leanVM's: one fixed shape per contract (statement; completeness)

- **What.** The contract fixes all six table row counts, the memory size and the bytecode size as constants
  (`Shape`, "no announced sizes"). `Z_act`, `Z_pad`, the heap layout and every quotient's size are compiled in.
  leanVM 42422001 reads these sizes from the proof and absorbs them into the transcript (`walk`, step 1).
- **Impact.** Every accepted proof is still a true leanVM statement, so soundness is unaffected. But the contract
  rejects every true statement whose execution has other row counts. The "1,000 signatures" contract accepts only
  runs with exactly 183,266 XOR rows, 195,439 MUL rows, and so on. `shapes.rs` has one measured run per signature
  count, so nothing yet shows that a different set of 1,000 signatures (other keys, messages or encodings) gives
  the same six counts.
- **Constraint on the fix.** Padding rows cannot hold no-op rows to make up a shortfall: every row moves the state
  `pc → g·pc` or jumps, so no row is a no-op. A count can only change by moving the boundary between active and
  padding rows.
- **Fix.** Keep the heights fixed per contract, since the heap layout and the stacks depend only on them, and
  announce the row counts:
  - send `rows_T` in calldata and absorb them in the seed;
  - compute `Z_act` and `Z_pad` from the counts' bits. A factor is `1 + bit_b (w_b + ω_{s >> b} + 1)`, and
    `ω_{s >> b}` is GF(2)-linear in the bits above `b`, so this is at most `r` products per table;
  - size each leaf quotient for the smallest count of its height, `2^(r-1) + 1`, the largest `(n - rows)`.

  The cost is about 6 scalars of calldata and a few hundred gas.

### F2. The setup roots, the layout ids and the seed's IV are not tied to the program or the shape (integration)

- **Setup roots.** `contract::setup_root(k)` returns `word([0x1111·k, 0x2222, 0x3333])`, a placeholder. No code
  derives the bytecode and address setup `F`, or Flock's `A0` and `B0`, from the program and the BLAKE2s R1CS.
  Nothing ties those roots to the IV either.
- **The IV.** SPEC §4 says the IV "must bind the setup and the shape". The code accepts any IV, and the tests pass
  leanVM's `PROGRAM_IV`, which binds leanVM's bytecode and R1CS digest but neither these roots nor the shape.
- **Layout ids.** The `PCS_OPEN` layout ids `0x5501`–`0x5505` are the same for every shape, but the stacks they
  name range from `2^22` to `2^28` words. A precompile shared by the block cannot tell them apart, and the mock
  accepts any id.
- **Impact.** This is not a PIOP break: each contract's setup is fixed, so Fiat–Shamir soundness does not need it
  hashed. But a deployment whose roots do not come from the program verifies another program. Two shapes that
  share a layout id cannot both be opened correctly.
- **Fix.**
  - Compute the setup roots in code from the program and the R1CS, as `crates/quotient` does for its circuit.
  - Bind them and the shape in the IV: `keccak(leanVM IV ‖ setup roots ‖ shape)`.
  - Give each shape's stacks their own layout ids, or put the layout's hash in the call, as AGENTS.md's opening
    seed does.

### F3. The 142-bit figure is the PIOP alone; the openings bound the system at about 125.7 bits (accounting)

- **The PIOP's figure.** `review/review_m1_soundness.py` reproduces SPEC §9 from the code's own layouts. At 1,000
  signatures that is 142.4 bits; over all six shapes, 142.0 to 142.8 bits (details below).
- **The system.** The main line makes 5 `PCS_OPEN` openings (`C1`, `C2`, the setup, `A0`, `B0`). leanVM's WHIR
  parameters target 128 bits an opening (`review/whir_params.py`, `optimize(target=128)`). The union over the
  openings is about 125.7 bits end to end, whatever the PIOP's margin. SPEC §9 says WHIR is not counted, but §0
  and the table read as the protocol's soundness.
- **Small shapes.** The certified level-0 lists exist only for stacks of `2^24` words and up. At 32 signatures
  `C1` is `2^22`, and at 128 it is `2^24`, so those shapes' lists are not certified. A smaller stack has a larger
  list, so the union there is understated. My script uses the `2^24` value as a stand-in.
- **Fix.** State the end-to-end figure as the minimum with the PCS. Certify the lists at `2^22` and `2^23`, or drop
  the shapes below `2^24` from the claims.

### F4. The parity tests never ran a verifying contract, and nothing tested an accepting stream (tests; now covered)

- **What the old tests cover.** `contract_is_the_rust_verifier` and `deployable_is_the_rust_verifier` run the
  measuring build on random streams. The measuring build jumps over failed checks and returns every checked value.
  These tests do show that the compiled graph computes what the Rust does.
- **What they did not cover.**
  - whether each check requires zero or nonzero;
  - that a failed check reverts;
  - that a `PCS_OPEN` reply other than 1 reverts;
  - the calldata length and the selector.
- **Never run before this review.** `measure_deployable` deploys the verifying build but calls only the measuring
  one. `rust_verifier` runs with `Checks::Collect`. So no verifying contract, and no verifier enforcing its checks,
  had ever run on a stream it should accept.
- **Now covered.** `verifying_contract_accepts_the_honest_proof_and_rejects_mutations` runs two builds on the
  honest proof: the straight verifying contract, and the linked build cut into 5 contracts of at most 4 KB.
  - Both return 1 when exactly their 3 `PCS_OPEN` calls are attested, and those calls are true point claims on
    what was committed.
  - They revert when any one of 121 stream scalars or root halves is changed, when one call is not attested, on a
    wrong selector, and when the stream is one byte short or long.
  - The measuring build agrees with the Rust word for word on this accepting stream.
- **Remaining gap.** Flock has no honest end-to-end test at the main line's skip `k = 3`. `flock_min`'s tests check
  only the matrices' reduction at `k = 3`; leanVM's real proofs use `k = 6` and leanVM's terminal walk.
- **Fix.** When the prover exists, run the same accept and reject test at the reference shape with Flock (a′).

### F5. Small heights make `reduce` panic (robustness)

- **What.** Several quotient degrees are `u64` expressions that wrap for small heights:
  - `r (n/2) - n`, for BLAKE2S at height ≤ 1;
  - `n - 2`, for JUMP at height 0;
  - `2 (n - 1) - n`, for a memory or bytecode of one cell;
  - `… + (n - rows) - n`, at `n = rows = 1`.

  The chunk list then comes out empty, and `Relations::push` indexes `terms[0]` of an empty relation. This happens
  for the recorder (no contract can be built) and for the Rust verifier alike.
- **Test.** `small_heights_make_reduce_panic` reproduces it with BLAKE2S at 2 rows and with JUMP at 1 row.
- **Impact.** A panic, not a wrong verdict. No measured shape is affected: every height is ≥ 14.
- **Fix.** Validate `Shape` (heights ≥ 2, `log_memory`, `log_bytecode` ≥ 2), or compute the degrees with
  saturating arithmetic.

### F6. Two SPEC statements do not match the code or leanVM's relation (documentation)

- **The restriction formula (SPEC §2).** Read literally, `R(z) = Σ_k c_k B_{k mod 2^r}(z) B_{k - k mod 2^r}(o)`
  gives `B_{k - k mod 2^r}(o)` the low factors `Π_{l<r} (1 + w_l(o))`, which scale `R` by a constant. The mixed
  point the same paragraph gives, and the code uses, is right: `(w_{<r}(t) + w_{<r}(o), w_{≥r}(o))`. It is
  validated on 4 heap layouts, including the bytecode's block before the memory's as at 128 signatures.
- **padRow substitution (§5.2, §12.4).** These sections say the extractor replaces padding rows by `padRow`. That
  is not needed:
  - `M3Holds` leaves padding rows free but for `ConstraintsVanish` on every row (`Spine/Instance.lean`), and this
    verifier enforces JUMP's constraints on every row too;
  - for BLAKE2S, substituting `padRow` would also have to replace `q_flock`'s instance, whose bits Flock's R1CS
    constrains.
- **Fix.** Say that the extracted witness is `C1` as committed, with BLAKE2S's limbs read from `q_flock`.

### F7. The public input's encoding differs from leanVM's (interface, informational)

- **What.** Calldata carries the public input as four big-endian 64-bit words. leanVM's statement reads its
  32-byte digest as little-endian words (`Digest::words`). This is the baseline contract's convention too.
- **Impact.** A caller who passes leanVM's digest bytes unchanged gets a statement about a different public input.
- **Fix.** Document the conversion in the ABI, or take the digest and convert in the contract.

### F8. Small inaccuracies in `review/leanvm_univariate_params.py` (accounting, informational)

- It takes the honest quotients' degrees, not the committed capacities. `chunks` rounds the third chunk up to a
  power of two, and a cheating prover fills the whole capacity.
- It omits the unused blocks' identities, which have degree `< 2^r`.
- It counts the bus polynomial as degree 5 per tuple; it is 4, since `eq(α, s)` is multilinear in 4 variables.
- It merges `λ` and the batching sumcheck into "ρ, 120".

Each moves the result by less than 0.1 bit. `review/review_m1_soundness.py` does them as the code does.

## What I checked and found sound

**Bus and heap**
- **Tree identity on `V_H \ V_1`.** `w_1` vanishes exactly on `{ω_0, ω_1}`. Positions `i ≥ 2` give
  `T_{i>>1} = T_i T_{i⊕1}`, so node 1 is the product of all leaves; node 0 is free and nothing reads it
  (`heap_node_zero_is_free_and_unused`).
- **Block alignment.** Blocks are placed largest first from `2^(H-1)`, so every block is aligned, and the unused
  blocks tile the rest.
- **Restriction to a block.** `T̂(w_{<r}(t) + w_{<r}(o), w_{≥r}(o))` is `R_b(t)` for the degree-`< 2^r` polynomial
  with `R_b(ω_i) = T(ω_{a+i})`, because each `w_l` is GF(2)-linear (validated by exact division).
- **Unused blocks.** `R_u(t) = 1` forces `R_u ≡ 1`, except with probability `2^r/|E|`.
- **Root and boundary.** `T(1) · fp(STATE, 1, 1) = fp(STATE, g^(2^19 - 1), 1)`. It is leanVM's framework state
  push and pull, with the memory and bytecode blocks as `D_init/D_fin` (`bus.rs` `fingerprints`, identical).
- **Padding rows.** Their leaves are 1 whatever they hold, and the active count is the contract's constant.
  Garbage rows that "write" a fake public input are accepted and reach nothing (`padding_rows_are_inert`).
- **Derived push fingerprints.** `D' = D + Σ_s eq(α,s)(push_s − pull_s)`, linear in the sent values. The prover
  sends exactly the fingerprints `linearise` cannot derive.
- **Counters.** `z_T Π c_j = 1` on active rows is equivalent to leanVM's nonzero count product. Final counts are
  nonzero in neither protocol, and need not be: a zero final count has no push to match.
- **No counter or address cycles.** `g = x` is primitive in `K` (order `2^64 − 1`, checked on h1).
- **Exactly leanVM's tuples.**
  - The flushes are identical to leanVM 42422001's `layout.rs` (diffed).
  - leanVM's stacked bytecode is zero in slots 0–2 (`leaf.rs`, `BYTECODE_PUBLIC_SLOT = 3`), as the setup's
    `(SEP, g^i, 0, instruction)` assumes.
  - An inconsistent read is rejected (`inconsistent_read_is_rejected`).

**Constraints**
- **Table constraints.** leanVM has only JUMP's two (`b + v_cond w`, `v_cond (b + 1)`), on every row there as here.
- **Public input.** leanVM's lines `(w0, w2)`, `(w1, w3)`, `(0, 0)` on cells 0 and 1, as
  `(mem_k − I_k) w_{r_W}/w_1`. A false public input is rejected (`wrong_public_input_is_rejected`).
- **BLAKE2S limb copies.** Checked on every row, so the limbs equal `q_flock`'s slot `j` of instance `i`
  (`y_l(ω_i) = i_l`, `deg ℓ ≤ r 2^(r-1)`).

**Evaluation and claims**
- **Basis `B`.** Every `B_k` has degree `2^r − 1`, and the family is unitriangular in the novel basis, so it is a
  basis. `f(t) = ĉ(w(t))` needs no inversion, so no denominator can vanish: the novel basis's `w/(1+w)` is never
  used.
- **Stacks.** Each column is an aligned block. Every claim and the batch's weight read only blocks (eq times
  selector), so nothing relies on unused words or on entries past a column's block in its last lane.
- **Batching sumcheck.** Degree 2 (two scalars a round), as many rounds as the longest stack's variables, and the
  final check `Σ λ^k W_k(r_low) eq(0, r_high)^2 C_k(r_low)`. The square is both factors' zero-extension. Validated
  in both claim modes.
- **One opening per commitment.** Each commitment gets one `PCS_OPEN` call: `C1`'s also carries the bit-slice claim
  under extension B. `A0` and `B0` get one each.

**Fiat–Shamir**
- **Absorption.** `KeccakChannel` absorbs every byte read before the next challenge, by construction.
- **Order.** The order matches SPEC §4: `C1` root; `α`, `β`, `γ`; Flock (its `r` before its skip values, `α` after
  `v_a` and `v_b`, the ring map after `a` and `b`); `C2` root; `t`; values; `ρ`; `λ`; rounds; end values.
- **Seed.** It binds the name, the IV and the public input (but see F2).

**Soundness accounting** (recomputed, 1,000 signatures)

| round | bits after the union |
|---|---:|
| `t`: `Σ deg = 2^25.34` with committed capacities, `L_1 L_2 = 2^24.25` | 142.4 |
| `α`, `β` (degree `4N` per side, over `L_1`) | 154.9 |
| a pull fingerprint vanishes | 156.9 |
| `γ` (29 constraints) | 175.1 |
| Flock, `k = 3` | 171.8 |
| `ρ` (82 relations on `C1`, 97 in all, as the probe counts) | 161.4 |
| `λ` and 27 rounds | 161.9 |

- **Every challenge drawn after a root is union-bounded.** Flock's, `α`, `β` and `γ` over `L_1`; everything after
  `C2` over `L_1 L_2`; the setup has `L = 1`.

**Flock**
- **Fixed zerocheck coordinates at skip `k = 3`.** Soundness needs only that `eq(c, ·)` on `{0,1}^7` is
  GF(2)-independent, since `Az ∘ Bz + Cz` is GF(2)-valued at every boolean point. It does not matter which variables
  the coordinates sit on, so moving the skip from 6 to 3 changes nothing. This rests on leanVM's own assumption
  about the constants.

**Contract**
- **Contract and Rust.** The graph is compiled from the same code, and the verifying builds accept and reject as the
  Rust does (F4).
- **Completeness at other sizes.** Memory larger and smaller than the bytecode, tables of 8 rows, DEREF's gated store
  with `f_fp = 0` and `1`, three-chunk quotients and every unused-block arrangement these give
  (`honest_proofs_at_other_sizes`).
