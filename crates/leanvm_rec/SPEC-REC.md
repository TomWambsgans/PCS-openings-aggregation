<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# Recursion: an EVM verifier for leanVM 42422001 near 100K gas

**Status: milestone R1 done (measure, size, specify); R2 step 1 done (π1-rec in code, §1.4, §7); R2 steps 2–6 done
(π2's circuit compiled and its witness on the real proofs, §10: D16v × π1-rec is `2^24` positions, 85.7% used); R3
steps 1–3 done (π2's prover, verifier and contract, measured end to end on the real proof, §11 and `PI2.md`: 73,550 at
`c = 0`, 94,550 with the base); the review (R3 step 4, `REVIEW-REC.md`) found no attack, its fixes are in; the
optimisation (§12, branch `leanvm-rec-opt`): D16v × π1-rec3, measured end to end on the real proof, **44,792 at
`c = 0`** (980 B, execution 29,832), 65,792 with the base.** §0–§11 are the design before §12; where they differ,
§12 and `PI2.md` §8–§9 hold.
Branch `leanvm-rec`, from `leanvm-univariate` @ 29d3095; π1-rec on `leanvm-rec-pi1`; π2's circuit on
`leanvm-rec-circuit`; π2's PIOP on `leanvm-rec-piop`.
No Lean for now (the user's instruction: no proofs until the gas is close to 100K). Every number is marked:

- **measured**: by `crates/leanvm_rec`'s tests on h1, or by the univariate crate's revm runs;
- **modelled**: computed by `review/leanvm_rec_params.py` from measured counts.

```sh
RUSTFLAGS="-C target-cpu=native" cargo test --release -p leanvm_rec -- --include-ignored --nocapture --test-threads 1   # §1, §2.1 (measured)
python3 -I review/leanvm_rec_params.py                                                # §2-§6 (modelled)
```

## 0. Summary

The design has three parts:

- **π1** is the univariate PIOP of `crates/leanvm_univariate` (SPEC.md §13, the main line), with one change to its
  Fiat–Shamir shape, **π1-rec** (§1.4): two runs of challenges are derived as squares of one challenge. They are
  `α_2..α_4` and Flock's zerocheck eq point. π1-rec has 107 Keccak-f permutations instead of 131. The statement, the
  proof's content and the claims are unchanged.
- **π2** is a univariate quotient SNARK, in the family of `crates/quotient`. It proves that π1-rec's Rust verifier,
  without its PCS openings, accepts on the public inputs and outputs these `PCS_OPEN` claims. Its arithmetization
  is **D16v** (§2.4):
  - one copy argument, in which a position's **push is a degree-2 expression of its row** (a "virtual push"), so
    nothing but the wiring is checked;
  - rows of 16 positions;
  - Keccak-f in 130,736 positions;
  - `E` in `K`-limbs.
- **The contract** verifies π2 and passes π1's five claims and π2's four to `PCS_OPEN` (point claims, `machine.rs`'s
  ABI).

| | π2 = D16v, π1 = π1-rec (**recommended**) | today (π1 on chain) |
|---|---|---|
| π2's positions | `2^24`, 86% used (modelled) | |
| π2's commitments | witness `W` `2^24` words; quotient table `Q` `2^27.91` words (`≤ 2^28`); setup `(σ, κ)` `2^25` | |
| proof commitments, union bound | 2 (`W`, `Q`); π2's PIOP 140.6 bits; π1-rec's 142.3 | 2; 142.3 |
| calldata | 1,844 B (π1's claims 1,224 of it) | 7,108 B |
| execution | ≈ 41.4K (modelled) | 192,392 (measured) |
| claims / calls | 9 / 8 | 5 / 5 |
| **EIP-7623, `c` = 0 / 2K / 5K / 20K** (no base) | **73,370** / 88,769 / 115,769 / 250,769 | 305,808 / 315,808 / 330,808 / 405,808 |
| with the 21,000 base, `c = 0` | **94,370** | 326,808 |
| EIP-7976 (64 a byte), `c` = 0 / 20K | 118,016 / 250,769 | 454,912 / 454,912 |

What the table shows:

- **Recursion cuts the cost about 4× at `c = 0`.** Above `c ≈ 2K` the claims' price dominates, with 9 claims a
  proof.
- **The floor is π1's claims, whatever π2 is.** They are 46 distinct coordinates and 5 values: 1,224 B, which is
  49K gas at EIP-7623's floor and 78K at EIP-7976's (§1.5).

**What does not fit.** π2 with `crates/quotient`'s own gate (a χ on bits, every XOR a row) needs 14.8M rows for
π1's 131 permutations. That is a `2^29.8`-word quotient table, 3.5× over WHIR's `2^28` (§2.2). With cell outputs:

- rows of 16 cells (C16) need `2^25` positions and a `2^28.2`-word quotient table;
- split into three proof commitments, C16's `t` keeps 128.5 bits, no margin (§3).

**The fallback**, if D16v's 6% margin on `2^28` is lost: **D32v** (slice rows of 32 positions, §2.6). It needs no
change to π1 (`2^23` positions, `Q` `2^26.91`) and sends 34 values: 88,670 at `c = 0`.

## 1. π1's verifier, measured

### 1.1 Method

The univariate verifier, run on the recorder's symbol (`leanvm_flock_gas::evm::record`), is a hash-consed graph. Its
nodes are:

- the stream's reads;
- the Keccak-256 chain (`Hash(state, from, to)`: one Keccak-256 of the 32-byte state and the stream's bytes
  `from..to`; `Low`: its low 192 bits);
- `E`'s `Add` and `Mul`, and constants;
- bit fields of the row counts;
- the ring switch's kernel;
- the checks;
- the `PCS_OPEN` calls' words.

This graph is the circuit π2 proves. `crates/leanvm_rec`:

- **`src/count.rs`** counts the **live** nodes: those the calls or the checks read, through their operands. The ring
  kernel is expanded by recording `ring_tower::weight_at` on fresh symbols.
- **`src/eval.rs`** evaluates every node on a real proof. Test `the_graph_is_the_verifier_on_real_proofs`: on the 5
  committed 1,000-signature vectors (main line, π1-rec, leanVM's skip, Flock omitted, extension B), the evaluated
  graph writes exactly the vectors' `PCS_OPEN` inputs, all 13 (12) zero checks hold, and a flipped stream byte breaks
  them. **Measured.** This is the core of π2's witness generator.
- **`src/fs.rs`** records the verifier with chosen challenges derived as squares of the previous one (a channel
  wrapping the recorder). That is how π1-rec was measured before it was in code; it is now the check that π1-rec's
  code records this graph (`tests/counts.rs`, `pi1_rec_is_record_derived`: node for node).

### 1.2 The counts (measured, 1,000 signatures, `Claims::Point`)

| | main line (skip 3, tower) | **π1-rec** (skip 3) | leanVM skip (6, weighted) | skip 6, tower | skip 5, tower | skip 4, tower | π1-rec, skip 6 | BLAKE2s omitted (scale) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Keccak-256 calls (seed included) | 104 | **80** | 98 | 98 | 100 | 102 | 77 | 37 |
| Keccak-f[1600] permutations | 131 | **107** | 135 | 135 | 131 | 131 | 114 | 52 |
| challenges (hashed) | 103 | 79 | 97 | 97 | 99 | 101 | 76 | 36 |
| bytes hashed (states included) | 10,328 | 9,560 | 11,336 | 11,336 | 10,680 | 10,408 | 10,664 | 4,632 |
| stream bytes (hashed) | 7,072 (6,952) | 7,072 (6,952) | 8,272 (8,152) | 8,272 | 7,552 | 7,216 | 8,272 | 3,472 |
| `E` products: `x·y` / squares | 4,083 / 2,330 | 4,083 / 2,354 | 5,025 / 5,777 | 4,449 / 2,330 | 4,261 / 2,330 | 4,139 / 2,330 | 4,449 / 2,351 | 1,960 / 49 |
| `E` linear: adds / `+const` / `×const` | 4,309 / 411 / 498 | 4,309 / 411 / 498 | 3,952 / 522 / 547 | 4,459 / 522 / 610 | 4,367 / 459 / 546 | 4,325 / 427 / 514 | 4,459 / 522 / 610 | 1,253 / 380 / 349 |
| inversions | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| constants (distinct, live) | 385 | 385 | 458 | 461 | 418 | 394 | 461 | 367 |
| live reads: scalars + integers | 291 + 6 | 291 + 6 | 341 + 6 | 341 + 6 | 311 + 6 | 297 + 6 | 341 + 6 | 141 + 6 |
| reads never hashed (the batch's end values) | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 3 |
| row counts' bit fields | 125 | 125 | 125 | 125 | 125 | 125 | 125 | 125 |
| checks: zero / nonzero | 13 / 0 | 13 / 0 | 13 / 0 | 13 / 0 | 13 / 0 | 13 / 0 | 13 / 0 | 13 / 0 |
| packings `E` ↔ bits (reads + challenges) | 400 | 376 | 444 | 444 | 416 | 404 | 423 | 183 |
| claims: points / coordinates / distinct coordinates | 3 / 134 / 46 | 3 / 134 / 46 | 3 / 134 / 43 | 3 / 134 / 43 | 3 / 134 / 44 | 3 / 134 / 45 | 3 / 134 / 43 | 2 / 78 / 27 |

Notes on the table:

- **The tower variants carry one ring-switch kernel.** It is the main line's 64 Frobenius-twisted eq products and the
  map's six stages: 1,663 products, 1,896 squarings and 1,727 additions, included above. The 1,638 squarings of the
  26 coordinates' conjugates dominate it.
- **leanVM's skip (`Slices::Weighted`) has no kernel**, but 64 twisted terms in the batch's weights: 10,802 products.
- **The verifier is linearised.** It inverts nothing and checks 13 values against zero, none against nonzero.
- **Extension W (`Claims::Weighted`, not the ABI) for scale:** 85 calls, 112 permutations, 2,158 products. The
  batching sumcheck costs 19 permutations, the price of point claims.

### 1.3 The transcript (measured, main line)

| step | Keccak-256 calls | stream bytes absorbed (besides the 32-byte state) | Keccak-f |
|---|---:|---|---:|
| seed: name, the contract's IV, the public input | 1 | (80 B, no state) | 1 |
| the six row counts and `C1`'s root → `α_1` | 1 | 56 | 1 |
| `α_2..α_4`, `β`, `γ`, then Flock's zerocheck eq point (22 coordinates) | 27 | 0 | 27 |
| the skip's 8 coset values → `z` | 1 | 192 | 2 |
| the zerocheck's 29 rounds, `(v_a, v_b)` → `α_F`, the lincheck's 8 rounds | 38 | 48 each | 38 |
| the 64 slices → the ring map's `f_0` | 1 | 1,536 | 12 |
| `f_1..f_5` | 5 | 0 | 5 |
| `C2`'s root → `t` | 1 | 32 | 1 |
| the 84 values at `t` → `ρ` | 1 | 2,016 | 16 |
| `λ` | 1 | 0 | 1 |
| the batching sumcheck's 27 rounds | 27 | 48 each | 27 |
| the three stack values and `a`, `b` (120 B, never hashed) | | | |
| **total** | **104** | 6,952 | **131** |

Where the permutations go:

- **One challenge costs at least one permutation.** A sumcheck round (48 B and the state) fits one block.
- **Data costs one more permutation per 136 bytes.** The slices and the values at `t` cost 26 permutations beyond
  their two challenges.
- **The sumchecks' 64 rounds and their 2 values are inherent** to this π1: 65 permutations.
- **Draws with no new bytes are the only waste: 33** (27, then 5, then `λ`). π1-rec removes 24 of them.

### 1.4 π1-rec: the challenges that may be derived

**Decision: π1-rec derives `α_2, α_3, α_4` from `α_1`, and Flock's zerocheck coordinates 2..22 from coordinate 1, each
the square of the one before.** Measured with `fs::record_derived`: 80 Keccak-256 calls, 107 permutations, 24 more
squarings. The claims and the stream are unchanged.

- **The zerocheck's eq point.** `Σ_x eq(r, x) P(x)` is multilinear in each `r_i`. So the substitution
  `r_i = c^(2^i)` maps distinct monomials to distinct powers of `c` (a base-2 Kronecker substitution), and the
  polynomial stays nonzero when `P ≠ 0` on the cube. Its degree in `c` is `2^22 - 1`: the error goes from 22/|E| to
  `2^22/|E|`, which is 170.0 bits alone and 157.9 after `C1`'s list.
- **The bus's `α`.** Each fingerprint `Σ_s eq(α, s) τ_s` is multilinear in `α`, so with `α = (c, c², c⁴, c⁸)` it is a
  polynomial `f_τ(c)` of degree ≤ 15. Distinct tuples give distinct `f_τ`, since the 16 eq polynomials at the power
  point are a basis of the polynomials of degree < 16. `β` stays an independent challenge. Then `Π(β + f_τ(c))` as
  polynomials in `β` over `E[c]` are equal only if the multisets `{f_τ}` are, because the factors are irreducible in
  `β`. Schwartz–Zippel over `(β, c)` at degree 16 a factor gives 164.6 bits alone and 152.5 after the list.
- **Not derived:**
  - **`β` from `α`.** Products of the monic degree-16 polynomials `c^16 + f_τ(c)` can coincide for different
    multisets.
  - **The ring map's `f_0..f_5`.** The tower argument needs an independent `f_j` a level.
  - **`γ`.** One permutation; it could be `β²` by a union bound, which saves one.
- **A sponge squeeze (SHAKE-like, 5 challenges a permutation) is not taken.** The constraint is Keccak-256.
- **Larger skips do not help.** At skip 6, π1-rec is 114 permutations: the 64 coset values cost 11 blocks.
- **Merging sumchecks does not help.** Their rounds are already one permutation each, and the lincheck cannot join the
  batch (SPEC.md §13, dropped levers).

**π1-rec in code** (R2 step 1, branch `leanvm-rec-pi1`; measured on h1):

- **The parameter.** `leanvm_flock_gas::transcript::FsShape { Main, Rec }` (re-exported by `leanvm_univariate`), a
  field `fs` of Flock's `flock_min::Variant`, so it reaches every function that takes the verifier's configuration
  (`Blake2s`): `leanvm_univariate::FLOCK_REC` is `FLOCK_MAIN` with `fs: FsShape::Rec`, and `Blake2s::fs()` reads it
  (`Blake2s::Omitted` is `Main`). `FsShape::draw(channel, n)` draws a run: `n` challenges, or one and its `n - 1`
  successive squares. `flock_min::zerocheck` draws its coordinates after the seven fixed ones with it; `reduce` draws
  `α` with it. The main line is unchanged: its graph, gas (`gas_report`, `deployable_report`: identical output), vector
  and real proof (stream keccak `6b03217e…`) are the same.
- **The prover.** `lv42_flock::zerocheck::skip::EqPoint { Sampled, Squares }`, a parameter of `prove_skip` and
  `Blake2sSetup::prove_reduction_skip` (with `Squares` the skip module's zerocheck runs at every skip, 6 included); the
  univariate prover maps the variant's `fs` to it and squares `α` in `E` as the verifier does.
- **The check.** π1-rec's recorded graph is `fs::record_derived`'s, node for node (phases, checks, kernels, the
  calls' words, the reads), at skip 3 and 6: **80 Keccak-256 calls, 107 Keccak-f permutations** (skip 6: 77, 114).
- **The real proof** (1,000 signatures, `prove_real`'s `proves_and_verifies_main_line_rec`): 4.86 s, 10.4 GB; the Rust
  verifier, the five openings (`C1`, `C2`, `F`, `A0`, `B0`) and both contract builds accept, mutations are rejected.
  Stream keccak `53c06ada652d58b2…`. Vector `crates/leanvm_univariate/tests/vectors/main_line_rec.txt`, replayed with 17
  mutations by `evm_vectors`; the main line's contract rejects it and π1-rec's rejects the main line's.
  `leanvm_rec::eval` reproduces its five `PCS_OPEN` inputs.
- **Gas** (`rec_gas_report`; the real vector's runs agree): execution 181,019 straight, 191,296 deployed in 3
  contracts (main line 182,104 and 192,392), so 1,085 less. The transcript saves 1,717; the squarings and the code
  around them cost 660 (Flock's zerocheck 579, `α` 81); the other phases move by at most 15. The calldata is the same
  7,108 B, so EIP-7623 at `c = 0` is 304,712 deployed (305,808).

### 1.5 The claims, and what the contract must carry

Measured, main line and π1-rec:

| claim | point | coordinates |
|---|---|---:|
| `C1` | `r` (the batch's 27 challenges) | 27 |
| `C2` | `r` | 27 |
| setup `F` | `r[..24]` | 24 |
| `A0`, `B0` | `p = (r[0..3], row_low (3), χ_in (8), r[3..9], χ_in' (8))` (Flock's matrices) | 28 |

So the contract needs `r` (27 coordinates), the 19 coordinates of `p` not in `r`, and the 5 values: **51 elements,
1,224 B**. They are π1's challenges, computed inside π2 and never on chain, so they must be in calldata.

They cannot be made shorter:

- **Sumcheck challenges are sequential.** A point derived from one seed would let the prover know them in advance.
- **The batching sumcheck is what turns π1's weighted relations into one point claim per commitment.** A univariate
  batch would need a `2^28.6`-word quotient.
- **`A0`, `B0` are `2^28`-word R1CS matrices.** π2 cannot evaluate them.

So 1,224 B is this design's calldata floor: 49K gas at 40 a byte, 78K at 64.

*Lever 1(b), [`SPEC-POINTS.md`](SPEC-POINTS.md) (modelled, not built):*

- *The point `r` must stay fresh: `q_flock`'s ring switch needs a sumcheck over its variables. DEEP, Gemini, Zeromorph
  and a univariate batch save no coordinate.*
- *Its 27 coordinates can come from 14 challenges if the batch runs two variables a round on `V_2`'s coordinate
  functionals. That costs no Keccak-f, 56K of π2's positions and −312 B: −6.0K gas on `leanvm-rec-opt` (where the
  `A0`, `B0` claims are gone), −10.5K on R3.*
- *Three variables a round would cost 18 Keccak-f.*

## 2. π2's arithmetization

### 2.1 The reference: `crates/quotient` (measured, `tests/quotient_reference.rs`)

- **One gate, `V = X + C + Y·C`, four cells a row.** It is a χ on bits, an XOR when `Y = 0`, and a NOT.
- **The wiring:** one logarithmic-derivative copy argument, with unique tags on both sides. It is sound in
  characteristic 2, since both sides are sets.
- **One quotient identity at `t`.** The verifier is sent 5 values.

| | measured |
|---|---|
| rows per Keccak-f (one Keccak-256 of a 64-byte block) | **113,114** |
| the Merkle path: 34 permutations | 3,878,612 of `2^22` rows (92.5%); at most 37 permutations fit |
| words per row at `2^22` rows | witness 5.00 (hidden), wiring 4.00, quotient **63.00** (`2^27.98`, hidden) |
| words per cell (4 a row) | quotient 15.75 hidden; 13.75 without hiding (`h` 3, `q` 9, gate 1.75) |

π2 needs no zero knowledge. π1 has none, and π2's witness is π1's proof, which is not secret.

### 2.2 Why bit-level wiring does not fit (modelled)

| π2 with `crates/quotient`'s gate | rows | quotient table |
|---|---:|---:|
| π1 main line (131 permutations) | 14.8M (`2^23.82`) | `2^29.80` words: **3.5× over `2^28`** |
| π1-rec (107) | 12.1M (`2^23.53`) | `2^29.51`: **2.8× over** |

The copy argument costs about 9 words a wired cell (`h` 3, `q` 6, both in `E`), whatever the gate. So what matters is
the number of wired cells a Keccak round needs:

- **The XOR-per-row circuit spends about 18,900 a round.** That is 113,114 rows a permutation, of 4 cells.
- **The floor with cell outputs is about 3,840 a round.** Every state bit must be written once and read once across
  ρπ's rotations, and θ adds its column parities.
- **Rotations cannot be algebraic in characteristic 2.** `z ↦ z + r mod 64` is not GF(2)-affine: no affine map of
  `GF(2)^6` has order 64. And there is no element of order 64 for a multiplicative "next" map. So ρ is always wiring.
- **The constraint on the other side is the verifier's calldata.** Every relation the verifier checks at `t` among
  `L` cells costs `L` values, or a sumcheck.

### 2.3 Virtual pushes

**Decision: the copy argument carries the computation.** Every position `i` of the witness `w` (a `K`-word, `N = 2^m`
positions on the Cantor subspace `V_m`) has:

- a **pull** `(w(ω_i), ω_i)`: its value, tagged with its own point;
- a **push** `(P(ω_i), σ(ω_i))`: a value `P(ω_i)` sent to the position `σ(ω_i)`, a fixed permutation of the
  positions (setup), or to a tag outside `V_m` (§2.4.6).

`P(ω_i)` is one of:

- a **forward**: its own pull, `P = w`;
- an **expression slot**: a polynomial `E_{b,k}` of degree ≤ 2 in the 16 values of its row, chosen by the position's
  **role** `k` (its low 4 index bits) and its row's **region block** `b` (an aligned block of rows);
- a **constant**: `κ(ω_i)`, a setup column that is zero off the constant positions.

So `P = w + Σ_(b,k) I_(b,k)·(E_(b,k) − w) + κ`, where:

- `I_(b,k)` is the indicator of the positions of role `k` in block `b`;
- the constant region's formula pushes 0.

That set is a coset of `U_s = span(β_4, …, β_(3+s))`, for a block of `2^s` rows. So
`I_(b,k)(x) = w_m(x) / ((Z_(U_s)(x) + Z_(U_s)(c_(b,k))) κ_(b,k))`: `w_m = Z_(V_m)` factors through `Z_(U_s)`. It has
degree `N − 2^s < N`. The verifier needs one `Z_(U_s)(t)` per block size, a short linearized recursion, and then one
division per pair.

The checks are:

- `h(x) = 1/(α + w(x) + βx) + 1/(α + P(x) + βσ(x))` on `V_m`;
- the identity `h·d_pull·d_push + d_pull + d_push = q·w_m(x)`, with `w_m = Z_{V_m}`;
- the sum `Σ_{V_m} h = Σ_J 1/(α + F_J + βτ_J)`, the public side (§2.4.6).

**Soundness of the multiset step.** The pulls' tags are the positions, all distinct. The pushes' tags are `σ`'s
values, also distinct. So both sides are sets of (value, tag) pairs, and mod-2 equality of sets is equality (as in
`crates/quotient`, SPEC.md §5.1). Hence every position's value is the push meant for it. Each value then travels from
its producing expression slot through forwards to exactly one consumer whose own push is an expression (its *end*).

**The layout's invariant** (review R1, finding 1). A position's push is a formula of its *row*, not of its own pull,
so a pull constrains nothing unless some formula of its row reads it, or it is forwarded. So:

- every pull that is an end is an input of its row's formula;
- the only exception is a segment of a constant, ending in a spare slot, whose value is irrelevant.

The Keccak rows of §2.4.1 satisfy it:

- `A_{j-1}` and `D_j` are read by the χ formula;
- `P_{y'-1}` is read by the partial sum;
- `C[x-1][z]` is read by the D unit.

R2's layout compiler checks it for every row type.

**Booleanity.** A free bit is a self-loop pushing `b²` to itself, so `b = b²`. Every other value is a degree-2
function of bits and limbs, so by induction every Keccak value is a bit.

**What it costs.**

- **The degree.** The indicators have degree `N − 2^s < N` (about `N` for a small block) and `E` degree `≤ 2N`, so
  `deg P < 3N`. The identity has degree `< 5N`, and `q` has degree `< 4N`. A product of a region selector by a role
  selector, unreduced, would make it `4N`: the indicators must be those of the (block, role) cosets.
- **The words.** The quotient table is `h` (`3N` words) plus `q` in 4 chunks (`12N`): **`15N` words**.
- **What it saves.** No position is spent on outputs, and no gate quotient is needed: every constraint is a push.

### 2.4 D16v: the recommended layout

Positions `i = 16y + k`, with role `k < 16` and row `y`. A row is the coset `ω_{16y} + V_4`. From position `x` of role
`k`, the row's cells are `w(x + ω_{k⊕c})` for `c < 16`. So at `t` the verifier needs the 16 values
`v_c = w(t + ω_c)`, and every role's formula reads them permuted by `XOR k`.

#### 2.4.1 Keccak-f in 130,736 positions

A round `j` (θ, ρπ, χ, ι) takes its input state `A_{j-1}`:

- `C_j[x][z] = Σ_y A_{j-1}[x,y][z]`;
- `D_j[x][z] = C_j[x-1][z] + C_j[x+1][z-1]`;
- `b_j[π(x,y)][z + r(x,y)] = A_{j-1}[x,y][z] + D_j[x][z]`;
- `A_j[x',y'][z'] = b + (1 + b_{x'+1}) b_{x'+2} + RC_j[z'][x' = y' = 0]`.

| row type (region) | rows a round | pulls (role: what) | pushes | positions |
|---|---:|---|---|---:|
| **K0**, plane `y' = 0` (split K0a / K0b by `RC_j[z'] = 0 / 1`) | 64 | 0–4: `A_{j-1}` of the 5 source lanes `π⁻¹(x', 0)` at `z' - r`; 5–9: their `D_j`; 10–15: three D units | 0–4: `A_j[x', 0]` (to round `j+1`); 5–9: `P_0[x'] = A_j[x', 0]` (to plane 1); D units: `D_{j+1}`, and a forward of `C` | 16 |
| **K1**, planes `y' = 1..4` | 256 | 0–4: `A_{j-1}`; 5–9: `D_j`; 10–14: `P_{y'-1}`; 15: a self-loop | 0–4: `A_j[x', y']`; 5–9: forwards (`D`'s chain); 10–14: `P_{y'} = P_{y'-1} + A_j[x', y']`, whose `P_4 = C_{j+1}[x'][z']` | 16 |
| **KD**, D units | 16 | 8 units: `C[x-1][z]` (end), `C[x+1][z-1]` (forward) | `D[x][z]` (expression), `C`'s forward | 16 |
| **Kprep**, round 0's `C_0` | 107 a permutation | 3 units of 5 input bits | `C_0[x][z]`, 4 forwards | 16 |

Per permutation: `24 · 336 · 16 + 107 · 16` = **130,736 positions**, against `crates/quotient`'s 452,456, a 3.5×
saving. The chains balance:

- `A_{j-1}` ends in its K0/K1 pull, fan-out 1: the partial sums use `A_j` where it is produced.
- `D` ends in its one plane-0 consumer. Each `D[x][z]` feeds the 5 lanes `(x, y)`, whose planes `2x + 3y` are
  distinct, so exactly one is plane 0. It is forwarded through the other four.
- `C` ends in one D unit and is forwarded through the other.

Degree 2 throughout.

#### 2.4.2 Keccak-256 calls

- **One fresh sponge a call.** The first block is `A_{-1}` = the 32-byte state, the data and the padding (constants
  `0x01` and `0x80`), with zeros in the capacity lanes.
- **Later blocks** are XOR units into the rate lanes: 2 pulls a bit.
- **The digest** is `A_23`'s lanes 0–3. It is forwarded into the next call's state bytes, and packed into the challenge
  (`transcript::challenge_of`: the low 192 bits, limb 0 the lowest).
- **The seed**, `keccak(name ‖ IV ‖ public input)`, is one call on constants and the public input's bits.
- **π1-rec: 80 calls, 107 permutations, 27 later blocks** (59K positions).

#### 2.4.3 Packing, bytes ↔ `E`

- A scalar is 24 bytes, big-endian `c2 ‖ c1 ‖ c0`. A limb is `Σ_e bit_e x^e` in `K`'s polynomial basis.
- Packing rows: 15 bits and an accumulator a row, 5 row types by the exponents' offset. That is 5 rows a limb, 15 an
  element.
- 376 packings (297 reads, 79 challenges): about 90K positions.
- The stream's 56,576 bits (and the public input's 256) are free cells: a self-loop pushing `b²`, and a slot that
  produces `b`. That is 2 positions a bit, 114K in all.

#### 2.4.4 `E` arithmetic on `K`-limbs

`E = K[y]/(y³ + y + 1)`. A product's limbs are degree-2 expressions in its operands' limbs:

- `c₀ = a₀b₀ + a₁b₂ + a₂b₁`;
- `c₁ = a₀b₁ + a₁b₀ + a₁b₂ + a₂b₁ + a₂b₂`;
- `c₂ = a₀b₂ + a₁b₁ + a₂b₀ + a₂b₂`.

How the operations are laid out:

| what | how | positions |
|---|---|---:|
| products, squares (6,437) and sums (5,218) | units of 6 pulls, 3 expression pushes and 3 forwards; 2 units a row | 93K |
| constants (385 distinct) | positions whose push is `κ`, the setup's constants column; as many segments as their fan-out needs | in the above |
| bit fields (125) | the counts' bits are free cells; a wider field is a packing | — |
| zero checks (13) | pushed to an outside tag with the value 0 | — |
| the ring kernel | expanded (§1.2) | — |
| spare slots | an expression slot with nothing to end pulls a constant's segment | — |

#### 2.4.5 Totals (modelled; π1-rec)

| | positions |
|---|---:|
| Keccak-f: 107 × 130,736 | 13.99M |
| later blocks' XORs | 0.06M |
| packings and free bits | 0.20M |
| `E` arithmetic | 0.09M |
| public, constants | 0.002M |
| **total** | **14.35M of `2^24` = 16.78M (86%)** |

With π1's main line (131 permutations) it is 17.49M. That is over `2^24`, which is why π1-rec is part of the
recommendation.

#### 2.4.6 Public inputs

The public inputs are:

- the 32-byte public input;
- the six row counts;
- π1's two roots;
- π1's claims: 46 coordinates and 5 values.

That is 57 elements and 13 zero checks.

**Each element `J` binds through one outside tag `τ_J ∉ V_m`.** Its producing row pushes a fingerprint `F_J` there,
and the verifier adds `1/(α + F_J + βτ_J)` to the sum's target: 70 fractions in one batched inversion. *As built
(PI2.md §4.2; REVIEW-REC.md N4) the fingerprint is not `c₀ + γc₁ + γ²c₂ (+ γ³c₃)`: a three-limb port's is the element
itself, `L₀ + YL₁ + Y²L₂`, and a four-limb port's (the statement, a root) `(L₀ + YL₁) + γ(L₂ + YL₃)`.*

**Measured (§10.4, 2–3):** the row counts need not be public (67 fractions), and the ports' positions are holes of `σ`
(nothing pushes to them), whose pulls (0) are in the target too: 3 coset sums.

**Not the alternative.** `crates/quotient` adds the public weight inside `h`'s identity: `(h + weight·w)·d·d'`. Here
that would raise `q` to `5N` (an `18N`-word table, `2^28.17`). The outside tags keep the identity at `5N`.

The verifier also hashes the public data into π2's seed (§4).

### 2.5 Sizes against `2^28` (modelled)

| commitment | content | words | stack, list |
|---|---|---:|---|
| `W` (proof) | `w`: `2^24` `K`-words | `2^24` | `2^24`, 9,952 |
| `Q` (proof, after `α, β, γ`) | `h` (`3N`), `q` in 4 chunks (`12N`) | `2^27.91` (252M; 6% under `2^28`) | `2^28`, 3,564 |
| setup | `σ` (`N`), `κ` (`N`) | `2^25` | `L = 1` |

### 2.6 D32v: the fallback

**Rows = slices.** One row per `(round, z)`, 32 positions:

- pulls: `b_j[·][z]` (25) and `C_{j+1}[·][z-1]` (5);
- pushes: 25 expressions `a'_{j+1} = A_j + C[x-1] + C_prev[x+1]` (with `A_j = χ(b) + RC`, `C = Σ_y A_j`), and 5
  `C`'s.

There are no forwards in Keccak at all. Per permutation, 25 × 64 × 32 = 51,200 positions, a θ-prep slice row
included. π1 needs no change (131 permutations): 7.07M positions in `2^23` (84%), `Q` `2^26.91`. The verifier gets 32
values plus `σ`, `κ`: 34 values, +384 B.

## 3. Options and their sizes (modelled; `review/leanvm_rec_params.py`)

| option | positions a Keccak-f | π1 | `N` (used) | `Q` words | proof commitments | values at `t` | π2's PIOP after the lists | calldata | EIP-7623 `c = 0` |
|---|---:|---|---|---:|---:|---:|---:|---:|---:|
| B4: `crates/quotient`'s gate | 452,456 | main / rec | `2^26` | `2^29.78` ✗ | — | 5 | — | — | — |
| C16: cell outputs, 16-cell rows | 196,608 | rec | `2^25` (64%) | `2^28.20` ✗ | 3 if split | 18 | 128.5 (split) | 1,876 B | 74,650 |
| C64: cell outputs, slice rows | 98,304 | main | `2^24` (79%) | `2^27.18` | 2 | 66 | ≈ 141 | 2,996 B | 119,300 |
| **D16v** | 130,736 | **rec** | **`2^24` (86%)** | **`2^27.91`** | **2** | **18** | **140.6** | **1,844 B** | **73,370** |
| D16v | 130,736 | main | `2^25` (52%) | `2^28.91` ✗ | — | 18 | — | — | — |
| **D32v** (fallback) | 51,200 | main | `2^23` (84%) | `2^26.91` | 2 | 34 | 141.3 | 2,228 B | 88,670 |
| chain π1 → π2 (D32v) → π3 (D16v of π2's verifier) | | main | `2^23`, then `2^21` | | 2 + 2 | 18 | ≥ 140 | 2,052 B | 81,660 |

What each option shows:

- **Splitting π2's quotient (C16).** `h` and `q` go into two commitments drawn in one round. Then `t` pays three lists
  (`7,908 · 4,473 · 3,564 = 2^36.9`), which leaves 128.5 bits: at the target, with no margin. Rejected.
- **The chain.**
  - π2's verifier is about 11 permutations and 2.5K `E` operations, so π3 is about 1.5M positions (`2^21`).
  - The chain adds π2's claims to calldata (`t_2`, `ρ_2`, 4 values: 144 B) and 4 more claims.
  - It is 8K gas more than D16v. Kept only if D16v and D32v fail for another reason.
- **A leaner Keccak** is what D16v and D32v are: 3.5× and 8.8× fewer positions than the bit gate.
- **Fewer challenges** is π1-rec. Larger skips and merged sumchecks do not help (§1.4).
- **Not possible within these constraints:**
  - **A π2 with fewer values and a fitting `Q`.** The bit gate (5 values) is 3.5× over.
  - **Calldata below π1's 1,224 B of claims.**

## 4. π2's protocol

- **Setup** (code constants in the contract):
  - the root of `(σ, κ)`;
  - π2's IV: `keccak("leanvm-rec-iv" ‖ π1's contract IV (SPEC.md §13, F2) ‖ the setup root ‖ the shape ‖ π2's layout
    words)`; *as built (`prover::iv`; REVIEW-REC.md N4, M1): `keccak("leanvm-rec-iv-v2" ‖ π1's contract IV ‖ the setup
    root ‖ the circuit's digest ‖ the three layout words)`, the layout words `prover::layout_word`'s;*
  - π1's setup roots (`F`, `A0`, `B0`) and layout words, which π1's calls need.
- **Public inputs:**
  - the public input (32 B);
  - the six row counts (4 B each);
  - π1's roots `C1`, `C2`;
  - π1's claims: `r` (27), `p`'s other 19 coordinates, and the values `C1(r)`, `C2(r)`, `F(r)`, `a`, `b`.
- **The transcript** (Keccak-256, on chain, `KeccakChannel`'s shape):
  1. The seed `keccak("leanvm-rec-v1" ‖ IV ‖ D)`, where `D = keccak(public data)`, about 1.35 KB. *As built (PI2.md
     §4.7; N4): the seed is `keccak("leanvm-rec-pi2v1" ‖ IV ‖ the public input)`, and the public data is in the stream,
     absorbed by the first challenge.*
  2. `W`'s root, then `α`, `β`, `γ`.
  3. `Q`'s root, then `t`.
  4. The 18 values: the row's 16 fold values `a_k = ĉ_W(k, w_4(t), …, w_23(t))`, then `σ(t)`, `κ(t)`. Then `ρ`.
- **The verifier**, at `t`:
  1. The digits `w_0..w_24`.
  2. The row's cells `v_c = w(t + ω_c)` from the `a_k`, by multilinear interpolation at `(w_l(t) + ω_{c>>l})_{l<4}`.
  3. The indicators `I_(b,k)(t)` of the about 200 (region block, expression role) pairs, by one batched inversion
     (§2.3).
  4. `P(t) = v_0 + Σ I_(b,k)(t)(E_(b,k)(v) − v_0) + κ(t)`, `d_pull = α + v_0 + βt`, `d_push = α + P(t) + βσ(t)`.
  5. The public target `Σ_J 1/(α + F_J + βτ_J)`.
- **Claims** (4 in 3 calls):
  - `W`: one point claim, at `(ρ, ρ², ρ⁴, ρ⁸, w_4(t), …, w_23(t))` with value `Σ_k eq(ρ, k) a_k`;
  - `Q`: the identity at `t`, `h(t)·d_pull·d_push + q(t)·w_24(t) = d_pull + d_push`, as one point claim over `h` and
    `q`'s chunks (the chunk digits as coordinates, as `crates/quotient`); and the sum, `Σ_V h` = the public target,
    at the top coefficient's fixed point;
  - setup: `σ(t) + ρ'κ(t)`, one point claim.
- **The contract**, in order:
  1. Hashes the public data into the seed.
  2. Runs π2's verifier.
  3. Calls `PCS_OPEN` 5 times for π1's claims, with π1's roots, layout words and setup roots, as the univariate
     contract does today.
  4. Calls `PCS_OPEN` 3 times for π2's.

## 5. Soundness (modelled; `review/leanvm_rec_params.py`)

Each challenge's error is its Schwartz–Zippel bound times the lists of the commitments it is drawn against (WHIR
takes no OOD sample at level 0). The setup is honest, so `L = 1`.

| round | alone | after the union |
|---|---:|---:|
| π1-rec: the bus `(α = (c, c², c⁴, c⁸), β)`, degree 16 a tuple | 164.6 | 152.5 |
| π1-rec: Flock before `C2`, the eq point as powers (`2^22`) | 170.0 | 157.9 |
| π1-rec: `t` (unchanged; the PIOP's minimum) | 166.6 | **142.3** |
| π1-rec: `γ`, `ρ`, `λ` and the batch | ≥ 185.7 | ≥ 161.4 |
| π2: the copy argument `(α, β)` (`4N/2^192`, over `W`'s list 9,952) | 166.0 | 152.7 |
| π2: `γ`, the four-limb ports' fingerprints, degree 1 (3 ports; the three-limb ones are the element) | 190.4 | 177.1 |
| π2: `t`, the identity of degree `5N` (over `W` and `Q`: `2^25.1`) | 165.7 | **140.6** |
| π2: `ρ`, W's fold (degree 15), Q's and the setup's combinations (degree 1): three commitments, the errors add, `(15 L_W + L_Q + 1)/2^192` (ρ is reused for the setup claim, PI2.md §4.5) | 192.0 | 174.8 |

**The openings.** WHIR's openings are 8: π1's 5 and π2's 3, at 128.97 bits each. That is 126.0 bits by a plain union,
about 129 in the query-bounded random-permutation model, as SPEC.md §9 counts π1's 5.

**The composition.** π2's knowledge soundness gives a π1-rec transcript on which π1's verifier (exactly its graph,
Keccak-256 bit for bit) outputs the claimed claims. Those claims are then opened by `PCS_OPEN`, and π1's soundness
applies. The errors add.

**Fiat–Shamir.** Both layers are random-oracle Fiat–Shamir over Keccak-256. A cheating prover can grind π1's
challenges offline, as it could on chain: the per-query bounds above hold, with `Q` queries.

**D32v** gives 141.3 bits for π2's `t`. **The chain's π3** is above 140.

## 6. Gas (modelled)

**Calldata** (D16v):

| part | bytes |
|---|---:|
| selector, public input, six counts | 4 + 32 + 24 |
| π1's roots | 64 |
| π1's claims: 46 coordinates and 5 values | 1,224 |
| π2's roots `W`, `Q` | 64 |
| π2's 18 values | 432 |
| **total** | **1,844** (about 13 zero bytes) |

**Execution.** π2's verifier is about 2,505 `E` operations at 13.85 gas each:

| part | operations |
|---|---:|
| digits | 50 |
| the fold (the 16 cells from the `a_k`) | 180 |
| push formulas | 345 |
| their selection: about 200 (block, role) indicators, 6 operations each, one inversion | 1,270 |
| the identity | 100 |
| the public fractions | 560 |

The 13.85 gas an operation is measured on π1's main line: `(182,104 − 11,175 − 6,442 − 3,444) / 11,631`, that is
its execution less its transcript, reads and calls, over its `E` operations. Add:

- `PCS_OPEN` marshalling: 15 gas a word, 277 words, and 100 a call for 8 calls;
- calldata reads, the transcript (two hashes of the public data, four challenges) and the entry;

which is ≈ 41.4K in all.

**EIP-7623's floor binds at `c = 0`**, by 2.6K (`40 B` = 73.4K, against `16 B` + execution = 70.8K). Above that, `c`
adds 9 claims' worth.

| configuration | calldata | execution | claims | EIP-7623 `c` = 0 / 2K / 5K / 20K | + 21K base (`c = 0`) | EIP-7976 `c` = 0 / 20K |
|---|---:|---:|---:|---|---:|---|
| **D16v × π1-rec** | 1,844 B | 41,421 | 9 | **73,370** / 88,769 / 115,769 / 250,769 | **94,370** | 118,016 / 250,769 |
| D32v × π1 (fallback) | 2,228 B | 50,226 | 9 | 88,670 / 103,694 / 130,694 / 265,694 | 109,670 | 142,592 / 265,694 |
| C64 × π1 | 2,996 B | 48,992 | 9 | 119,300 / 119,300 / 141,712 / 276,712 | 140,300 | 191,744 / 276,712 |
| C16 × π1-rec, 3 commitments | 1,876 B | 27,831 | 10 | 74,650 / 77,691 / 107,691 / 257,691 | 95,650 | 120,064 / 257,691 |
| chain π1 → π2 → π3 | 2,052 B | 43,626 | 13 | 81,660 / 102,290 / 141,290 / 336,290 | 102,660 | 131,328 / 336,290 |
| *today: π1 on chain (measured)* | 7,108 B | 192,392 | 5 | 305,808 / 315,808 / 330,808 / 405,808 | 326,808 | 454,912 / 454,912 |

## 7. Build plan

### R2: π2's circuit, compiled from the recorded verifier, and its witness from real proofs

1. **π1-rec in code.** **Done** (§1.4).
   - `flock_min::zerocheck` takes its 22 coordinates as `c, c², …`, and the univariate `reduce` takes `α` as
     `(c, c², c⁴, c⁸)`. Both are behind a transcript-shape parameter (`FsShape`): the main line stays as is.
   - The prover: the Flock zerocheck's point and the bus's `α`.
   - New vectors from the 1,000-signature trace on h1 (`prove_real`): `main_line_rec.txt`.
   - `fs::record_derived` is the check: the recorded graph equals π1-rec's (`pi1_rec_is_record_derived`).
2. **The layout framework** (`crates/leanvm_rec/src/circuit/`):
   - positions, roles, regions;
   - expression slots and forwards, with the balancing rule (each value's segment ends at exactly one expression
     slot; spare slots end constants' segments);
   - `σ` and `κ`, and the region placement.
3. **The Keccak-f template** of §2.4.1, and Keccak-256 (padding, later blocks, the state prefix, the digest).
   - Tested against `revm`'s `keccak256` on random inputs: every pull equals its push.
4. **The compiler from `Recorded` to the circuit:**
   - `Hash` → a Keccak-256 instance;
   - `Low` and `Input` → bits and packings;
   - `Add` / `Mul` → `E` units;
   - `Const` → `κ`;
   - `Bits` → wiring;
   - `RingWeight` → `weight_at` expanded;
   - checks and the call words → outside tags.
5. **The witness generator.** `eval::evaluate` (done) gives every node. A bit-level Keccak trace gives every round's
   `A`, `D` and `P`.
6. **Tests:**
   - on the real vectors, every position's pull equals its push, and the public side holds;
   - mutations break it;
   - the circuit's `N` and fill match §2.4.5. If `Q` would exceed `2^28`, switch to D32v.

### R3: π2's prover, its verifier compiled to EVM, real gas

1. **π2's prover:**
   - `w`'s coefficients (`crates/quotient/src/ntt.rs`);
   - `h` on `V_24`;
   - `P`, `d_pull`, `d_push` on an extension coset of `8N` points;
   - `q`;
   - WHIR commits of `W` (`2^24`) and `Q` (`2^28`), and the three openings.

   Modelled: 5–8 s and about 3 GB beyond π1's 6.2 s.
2. **π2's verifier in Rust, generic over `Scalar`** (as `quotient::protocol::reduce`). Recorded and compiled by
   `leanvm_flock_gas::evm` and `evm_link`, with π1's five calls appended.
3. **Measured gas on revm** with the mock `PCS_OPEN`:
   - parity: the contract is the Rust verifier, word for word;
   - end to end on the real trace: π1-rec's proof, then π2's proof, and the contract accepts with `PCS_OPEN`
     attesting the 9 claims the openings prove;
   - 13 or more mutations revert.
4. **Then** a review, and Lean for the virtual-push copy argument and the composition.

## 8. Risks

1. **D16v's margins.** 86% of `2^24` positions, and `Q` at `2^27.91` (6% under `2^28`). Any underestimate pushes `N`
   to `2^25` and `Q` over `2^28`, for instance:
   - forwards for values of high fan-out;
   - sink slots;
   - an identity of higher degree.

   R2 measures it. The fallback (D32v, `2^26.91`) costs 15K gas.
2. **The virtual-push copy argument is new.** Its soundness is the set argument of §2.3, which `crates/quotient`'s
   relies on too. But the balancing of slots, the selectors' degree and the outside tags need a written proof and an
   adversarial review before R3's numbers mean much.
3. **π1-rec changes π1's protocol.** The new Fiat–Shamir shape needs prover changes, new vectors, and an update of
   SPEC.md §9's analysis (§1.4 here). The derivations are standard (a power point for a multilinear eq; `α`'s
   Kronecker substitution with `β` independent), but they are not leanVM's.
4. **The execution is modelled** from π1's per-operation cost. The (block, role) indicators (about 200, 1,270
   operations) and the public fractions (560) are its largest parts, and may cost more on chain. At `c = 0` the
   calldata floor still binds with up to 2.6K of extra execution. Beyond that the transaction is execution-bound.
   Fewer region blocks or fewer expression roles lower it.
5. **The claims dominate above `c ≈ 2K`.** There are 9 claims (π1's 5, π2's 4); at `c = 20K` that is 251K.
   Extension W or B would cut π1's batch, not its claims.
6. **EIP-7976.** π1's claims alone are 78K at 64 a byte; the total is 118K at `c = 0`.
7. **The prover's time and memory are modelled.** π2's extension coset is `8N = 2^27` `E`-values (3 GB). *Measured
   (§11): the coset is `4N`; 8.4 s and 11.7 GB at `2^24`.*
8. **WHIR's certified lists** exist for `2^24..2^28` stacks only. π2's `W` and setup are `2^24` and `2^25`, so they
   are covered. *D32v's `W` (`2^23` words) is committed on a `2^24` stack (§11).*

## 9. Measured vs modelled

- **Measured:**
  - π1's counts, transcript and claims (§1.2, §1.3, §1.5), on the recorded graph;
  - the evaluator, against the 5 real vectors (π1-rec's among them);
  - π1-rec's counts, via `fs::record_derived` and on π1-rec's code (the same graph);
  - π1-rec's real proof and its gas (§1.4);
  - `crates/quotient`'s rows and words (§2.1);
  - today's gas (`crates/leanvm_univariate`, SPEC.md §13).
  - π2's circuit, its witness on the real proofs and its counts (§10);
  - π2's prover, its proof on the real witness, the contract's gas and its acceptance end to end (§11, `PI2.md`);
- **Modelled:** everything else about π2: its soundness, and π1-rec's.

## 10. R2: π2's circuit, measured (steps 2–6)

Branch `leanvm-rec-circuit`, `crates/leanvm_rec/src/circuit/`. Measured on h1 by `tests/circuit.rs`, on the real
1,000-signature proofs: π1-rec's `main_line_rec`, and the main line's `main_line`.

```sh
RUSTFLAGS="-C target-cpu=native" cargo test --release -p leanvm_rec --test circuit -- --nocapture --test-threads 1   # 4 configurations, about 190 s
RUSTFLAGS="-C target-cpu=native" cargo test --release -p leanvm_rec --lib                                           # templates, packings, spec
```

### 10.1 What exists

| module | what |
|---|---|
| `spec.rs` | **the PIOP's interface** (committed first, `adb3e6f`): rows of `W = 2^log_width` positions; region blocks of `W` role formulas (`Forward`, `Expr`: degree ≤ 2, `K` coefficients, no constant term; `Port`: `Σ γ^l` limbs); `σ` as tag indices (a position, or `N + J` for port `J`); `κ` sparse; the ports and their `Source`s; `π1`'s call words. `Circuit::check` checks every pull against its push, the holes and the public limbs; `example()` is a toy for the PIOP's tests |
| `layout.rs` | the framework: values placed at cells, `σ` derived, the invariant checked, blocks placed and padded, the witness |
| `keccak.rs` | D32v's Keccak-f; Keccak-256's sponge (padding, later blocks by XOR units, the digest); constants |
| `keccak16.rs` | D16v's Keccak-f (`k0`, `k1`, `kd`, `kprep`) |
| `units.rs` | free bits, packings, `E` units, ports |
| `compile.rs` | `Recorded` → circuit and witness; `pi2(recorded, Layout::D16v / D32v, inputs)` |

### 10.2 The tests (all pass)

- **The templates on random inputs** (lib): Keccak-256 of 9 messages (0–300 bytes, multi-block) in each layout.
  - Every pull equals its push, and the digests are `revm`'s `keccak256`.
  - 20 changed words at wired positions are each caught.
  - Packings of 1- to 64-bit words, sparse ones included, are their words.
  - D16v measures 8,184 rows a permutation.
- **The real proofs** (`tests/circuit.rs`, each of π1-rec and the main line, in each layout):
  - `Circuit::check` holds: every pull equals its push, the holes are 0, every port's limbs are the public ones.
  - The circuit's calls on its public inputs are exactly the vector's 5 `PCS_OPEN` inputs, and the public inputs read
    back from them are the circuit's.
  - Every Keccak-256 digest (80; 104 on the main line) and every live element's limbs (12,545) equal
    `eval::evaluate`'s.
  - Mutations are caught:
    - a changed statement byte, element limb or root byte (`Failure::Public`);
    - 30 changed witness words at wired positions;
    - a flipped stream byte: its witness, which holds the formulas, gives other public limbs. `σ` and `κ` do not
      change: the circuit depends on the recorded graph only.
  - The counts are asserted: `N`, the fill's bounds, Keccak-f's positions a permutation, at most two blocks a region.

### 10.3 The counts (measured)

| | **π1-rec, D16v** | π1-rec, D32v | main line, D16v | **main line, D32v** |
|---|---:|---:|---:|---:|
| `N` | **`2^24`** | `2^23` | `2^25` | **`2^23`** |
| positions used | **14,370,656 (85.7%)** | 5,810,496 (69.3%) | 17,518,080 (52.2%) | 7,044,160 (84.0%) |
| Keccak-f (positions a permutation × permutations) | 130,944 × 107 | 51,200 × 107 | 130,944 × 131 | 51,200 × 131 |
| the rest | 359,648 | 332,096 | 364,416 | 336,960 |
| rows used / in blocks (padding) / `N/W` | 898,166 / 986,179 / 1,048,576 | 181,578 / 196,035 / 262,144 | | |
| `Q = 15N` (SPEC's `h` and `q`) | **`2^27.91` ≤ `2^28`** | `2^26.91` | `2^28.91` ✗ | `2^26.91` |
| regions / blocks / **selector pairs** | 14 / 18 / **120** | 14 / 16 / 267 | 14 / 15 / 85 | 14 / 16 / 267 |
| the verifier's formulas: terms / products | 322 / 124 | 1,240 / 312 | 322 / 124 | 1,240 / 312 |
| ports (fractions) / hole cosets | 67 / 3 | 67 / 3 | 67 / 3 | 67 / 3 |

The rest, π1-rec in D16v:

| part | positions |
|---|---:|
| free bits: 55,872 a self-loop and a copy (the stream's 6,952 hashed bytes, the public input) | 111,744 |
| `E` units (products 2,275 rows, sums 2,212, forwarded 2,682) | 114,704 |
| packings (`pack` 4,452 rows, `pack-top4` 373) | 77,200 |
| later blocks' XORs | 54,928 |
| ports | 1,072 |

SPEC §2.4.5 modelled 14.35M positions (86%) for D16v × π1-rec; measured, 14.37M (85.7%). **Decision: D16v × π1-rec**
is π2's layout. It fits `2^24` with 2.4M positions (14%) to spare, and `Q` is 6% under `2^28`. **D32v** is measured as
the fallback: it fits `2^23` on either π1, π1-rec at 69% and the main line at 84%. D16v on the main line needs `2^25`,
whose `Q` exceeds `2^28`.

**What D32v costs the verifier.** D32v's Keccak rows have 25–30 expression roles. Each is a formula of about 19 terms,
evaluated at `t` on the row's cells permuted by its role (`v_(k⊕c)`), so it shares nothing across roles. That gives
1,240 formula terms and 267 selector pairs, against D16v's 322 and 120. With about 6 operations a pair, D32v's push
side is roughly 2,850 operations, against D16v's 1,040. At 13.85 gas an operation that is about 25K gas more, beyond
§6's model.

### 10.4 Decisions and deviations from §2.3–§2.6

1. **The balancing is automatic.** Each value is placed at its readers: forwards, and at most one expression slot
   (its end).
   - A value with no slot placement ends at a **free end**: a slot whose pull nothing places and no formula of its
     row reads.
   - A slot whose push nothing asks for, but whose pull is placed, pushes **junk**.
   - Every non-port slot produces one value and every placed slot ends one. So the values without an end and the
     free ends are equally many, and any matching closes every chain.
   - Examples: the last call's unused lanes, round 23's `C_24`, and bits read only by forwards.
   - A slot with neither a placed pull nor a requested push is **dead**: a self-loop of 0, and its formula must
     vanish on its row.
   - The invariant, checked by `Builder::finish`:
     - a value is placed at most at one slot, and a free value at none;
     - every cell a live formula reads is placed (an end is read by its row; nothing live reads a free end or an
       unplaced forward);
     - every placed cell is read by some formula of its row.
2. **The public side has holes (a correction to §2.4.6).**
   - A push to an outside tag leaves its position's tag unpushed: `σ` has as many holes as ports, and their pulls
     must be in the target too.
   - *Superseded by PI2.md §4.1 (REVIEW-REC.md N1, N4): the PIOP leaves the holes out of the pulls (the identity's
     pull term times `1 + 1_S`) instead of summing them into the target, so a hole's value is unconstrained, which is
     harmless because no formula reads a hole (`pi2::circuit::Circuit::validate`, asserted by `Spec::of` and
     `Setup::new`). The text below is the R2 design.*
   - The holes are the ports' own positions, with pull 0. A port is the last role of a port row, and the port rows
     are blocks, so the holes are cosets.
   - The target is `Σ_J 1/D(F_J, τ_J) + Σ_holes 1/D(0, ω_h)`. Each coset's sum is `Z_U'/(β·Z_U(α/β + c))`, a short
     linearized recursion; there are 3 cosets.
3. **The row counts are not public.** They are stream bytes hashed by π1's transcript, and nothing on chain reads
   them.
   - The ports: the statement (4 limbs), the 2 roots (4 limbs), the calls' 51 distinct elements and the 13 zero
     checks (3 limbs). That is 67 fractions instead of 70.
   - The calls' constant words stay constants.
4. **ι by `κ`:** `κ` is allowed at any expression slot, and the formulas have no constant term.
   - D16v: no `K0a/K0b` split; `κ = RC_j[z]` at `k0` roles 0 and 5.
   - D32v: at the 7 roles whose push holds `A[0,0]`.
5. **D16v's Keccak-f is 130,944 positions a permutation** (SPEC: 130,736).
   - `kprep` is 160 rows: two `C_0` units of 5 forwards and a sum, and two D units. The input ends at round 0's χ
     slot, so its `kprep` reads are forwards.
   - `kd` is 344 rows, with the D units drawn from a pool (`k0`'s, `kprep`'s, then `kd`'s).
   - Every round's rows are made first.
6. **Constants live in the Keccak rows' spare roles**: D16v's `k1` role 15; D32v's roles 30–31 and the last round's
   25–31. A spare is an expression slot pushing 0, dead when unused. So there is no constants region.
7. **D32v's rounds:** `prep` (θ of the input), and `prep-first` for a first block, whose capacity lanes are not
   read. Then 23 `round`s (χ, ι, the next θ), and `last` (χ and ι only).
8. **`E` units:**
   - The operand that ends at the unit is the one with fewer uses left.
   - A unit where neither operand can end (each ends once) forwards both and has three more slots: 9 positions
     instead of 6.
   - Squares are products with `b = a`.
   - The limbs of a statement word, integer or bit field are fresh zero constants beyond the low one.
9. **Packings** are Horner by 15-bit windows from the top: `pack` is `acc·x^15 + Σ b_i x^i`, and `pack-top4` is a
   64-bit limb's top 4 bits. Absent bits read a shared zero, and a wider top window starts from a fresh zero. This
   replaces §2.4.3's five row types by offset.
10. **Free bits:** every bit is a self-loop with a copy (one region). A bit at a first block's slot uses the copy;
    the others leave it junk.
11. **Reads never hashed** (the batch's 5 end values, 15 limbs) are **free values**: cycles of forwards, any word,
    bound by the ports.
12. **Blocks are padded.** Each region's rows are padded with empty rows to one or two binary digits, within the `N`
    the unpadded layout needs, taking first the region whose next digit saves the most rows a pair. Port regions are
    not padded. With 6, 8 and 10, the pairs fall from 756 to 120 (D16v) and from 1,678 to 267 (D32v).
13. **The witness generator evaluates the circuit's own formulas**, from the free inputs (bits, never-hashed limbs).
    `eval::evaluate` is the reference it is checked against (every digest and element), rather than its source.

### 10.5 For R3

- The PIOP builds on `spec.rs`: `pi2(recorded, Layout::D16v, inputs)` gives the circuit, the witness and the public
  inputs. `σ` and `κ` depend on the graph only.
- The verifier's push side is 120 selector pairs and 322 formula terms, plus 67 public fractions and 3 hole cosets.

## 11. R3: π2's PIOP, measured (steps 1–3)

Branch `leanvm-rec-piop`, `crates/leanvm_rec/src/pi2/`; the protocol, the decisions and every number are in
[`PI2.md`](PI2.md). Measured on h1 (`tests/pi2.rs`, `tests/pi2_real.rs`), on the real circuit and witness of π1-rec's
1,000-signature proof:

| | D16v × π1-rec (**the layout**) | D32v (fallback; π1-rec or π1) | §6 model, D16v / D32v |
|---|---:|---:|---:|
| calldata | 1,844 B | 2,228 B | 1,844 / 2,228 B |
| execution, `c = 0` (straight) | **39,674** | 71,097 (76,241 deployable, 2 contracts) | 41,421 / 50,226 |
| **EIP-7623, `c` = 0 / 2K / 5K / 20K** | **73,550** / 87,094 / 114,094 / 249,094 | 106,649 / 124,649 / 151,649 / 286,649 | 73,370 / 88,670 at `c = 0` |
| + 21K base, `c = 0` | **94,550** | 127,649 | 94,370 / 109,670 |
| EIP-7976, `c` = 0 / 20K | 118,016 / 249,094 | 142,592 / 286,649 | 118,016 / 142,592 at `c = 0` |
| the prover: prove / open / peak memory | 8.4 s / 1.4 s / 11.7 GB | 5.6 s / 0.7 s / 6.9 GB | 5–8 s, 3 GB beyond π1 |

- **End to end:** π1-rec's real proof → π2's proof → its three openings verify (`quotient::opening::verify`) → the
  contract accepts, `PCS_OPEN` attesting exactly the 9 claims in 8 calls; 18 flipped calldata bytes each revert. The
  contract is the Rust verifier word for word, straight and deployable.
- **Deviations from §2–§4** (`PI2.md` §4): the holes are left out of the pulls (the identity's pull term times
  `1 + 1_S`) rather than summed into the target; the ports' fingerprints are the element itself (3 limbs) and a root's
  halves `+ γ ·` (4 limbs); `h(t)` is sent (19 values, not 18) to spare a second inversion; `W` and the setup in the `B`
  basis, `Q` in the novel one; the extension coset is `4N`; the public data is absorbed by the first challenge; the
  target shapes' stacks are at least `2^24` words (leanerVM's certified range: D32v's `W` sits on a `2^24` stack).
- **What remains:** R3 step 4, a review, then Lean.

## 12. Optimisation toward 50K (branch `leanvm-rec-opt`): the change list

Each change says whether it touches π1's Fiat–Shamir shape or claims, π2's, or only the contract. Measured numbers are
in `PI2.md` §9.

1. **The review's fixes** (REVIEW-REC.md M1, L1, L2, N2, N4, N5; `PI2.md` §8). π1's FS: its contract IV now binds the
   variant (`contract_iv_for`: π1-rec's seed changes, not its shape); the vector is regenerated. The claims: one
   `PCS_OPEN` ABI (π1's roots as `machine.rs`'s root words, π2's layout words structured). No gas change.
2. **π2's values 19 → 17** (π2's claims change; π1 unchanged). `ξ = κ(t) + βσ(t)` replaces `σ(t)`, `κ(t)` (the setup
   committed as `κ`, `κ + σ`, its claim at `β`); `h(t)` is no longer sent, `Q`'s claim being the identity's combination
   of `h(t)` and `q(t)`, with one inversion at the end. 1,844 → 1,796 B; execution 39,674 → 35,787; 73,550 → 71,630.
3. **The fold's siblings** (π2's verifier only). The row's cells fold with half the products (`ω_{2k+1} = ω_{2k} + 1`).
   Execution 35,787 → 35,212; the floor binds (71,630).
4. **π1-rec2: no claims on `A0`, `B0`** (**π1's Fiat–Shamir shape and claims change**; `FLOCK_REC2`,
   `Slices::TowerWalk`). Flock's lincheck terminal is checked by π1's verifier walking the BLAKE2s circuit (leanVM's
   check), so the matrices' reduction leaves the batching sumcheck, `a`, `b` leave the stream (7,072 → 7,024 B), and the
   claims are three, `C1`, `C2`, `F`, all at the batch's point `r` (27 coordinates; was 46). π2 grows to 94.7% of
   `2^24`. π2's public elements 51 → 30, calls 8 → 6. 1,796 → 1,292 B; execution 35,212 → 32,646; EIP-7623 `c = 0`
   71,630 → 53,270. This is lever 1(a) taken further: `A0`, `B0` need no point at all. For lever 1(b)'s design
   (branch `leanvm-rec-points`) it removes the matrices' claims from the problem.
5. **`PCS_OPEN`'s inputs written once** (the contract only: `evm_link`'s `reuse`; π2's call order `W`, setup, `Q`).
   Execution 32,646 → 31,103; EIP-7623 `c = 0` 53,270 → 51,727.
6. **The zero checks' coset in closed form** (π2's circuit: the zero ports first, padded to a power of two; π2's
   verifier). Execution 31,103 → 30,182; EIP-7623 `c = 0` 51,727 → 51,560 (the floor binds). The same commit adds the
   narrow-challenge plumbing (`Channel::sample_narrow`, `record::Node::Narrow`, `FsShape::Rec2`, the prover's batch),
   inert until item 7.
7. **π1-rec2's batch challenges narrow** (**π1's Fiat–Shamir shape changes**: `FLOCK_REC2` takes `FsShape::Rec2`).
   The batching sumcheck's challenges are the hash's low 160 bits, so the claims' 27 coordinates have four zero bytes
   each in calldata. 130.0 bits after the lists (`review/leanvm_rec_params.py`). The vector regenerated. On the real
   calldata (110 zero bytes): EIP-7623 `c = 0` 51,560 → **49,534** (the standard price binds; the floor is 48,380).
8. **π1-rec3: the batch two variables a round** (**π1's Fiat–Shamir shape changes**: `FLOCK_REC3`, `FsShape::Rec3`;
   the design is `SPEC-POINTS.md`'s, branch `leanvm-rec-points` merged). 14 narrow challenges for the 27 coordinates;
   π2's ports bind the 14 challenges and the contract derives the coordinates (`CallWord::Pair`). 129.0 bits after the
   lists. On the real calldata (980 B, 60 zero): EIP-7623 `c = 0` 49,534 → **44,792**; EIP-7976 82,688 → 62,720.

### Where it stands (measured on h1, the real 1,000-signature proof, `c = 0`, no base)

| | calldata | execution | EIP-7623 | EIP-7976 | claims / calls | π2's positions |
|---|---:|---:|---:|---:|---:|---|
| D16v × π1-rec, before (9d1bf46) | 1,844 B | 39,674 | 73,550 | 118,016 | 9 / 8 | 14.37M of `2^24` |
| D16v × π1-rec2 (f7a0b28) | 1,292 B (110 zero) | 30,182 | 49,534 | 82,688 | 7 / 6 | 15.88M of `2^24` (94.6%) |
| **D16v × π1-rec3, now** (§12 item 8) | 980 B (60 zero) | 29,832 | **44,792** | 62,720 | 7 / 6 | 15.93M of `2^24` (94.9%) |

The calldata (π1-rec3): the selector 4, the public input 32, π1's roots 64, π1's claims 408 (14 narrow challenges and 3
values), π2's roots 64, π2's 17 values 408. EIP-7623's standard price binds (`16 · 920 + 4 · 60 + 29,832`); its floor is
37,400, so execution counts in full from here down to it: the push side (156 selector pairs in 66 groups, 14.8K) is the
largest part. Soundness after the union bounds: π1-rec3's PIOP 129.0 bits (the narrow pairs; `t` 142.3), π2's 140.6
(`t`), the six WHIR openings 126.4 by a plain union (about 129 in the query-bounded model). π2's circuit is at 94.9% of
`2^24`.

**Dropped or left:**

- **The claims' point from 1–3 scalars** (lever 1(b)): not possible, by the points agent's analysis (`SPEC-POINTS.md`
  §2: `q_flock`'s ring switch needs a fresh sumcheck over its 26 variables; DEEP, Gemini, Zeromorph give the
  coordinates back as values). Its pairs (14 challenges for 27 coordinates) are item 8.
- **D8v**: Keccak-f does not fit `2^24` in rows of 8 (`PI2.md` §9).
- **20-byte reads of the narrow coordinates**: 432 gas at the standard price, a read width of its own in π2's stream.
- **Hand-scheduled kernels for the push side** (14.8K of the execution: 156 pairs, 66 groups): its generic code is at
  about 11 gas an operation already; fewer pairs would need slack in `2^24` that π1-rec2 and π1-rec3 used up (98–99.7%
  of the rows are in blocks).
- **The selector** (4 B, 64 gas): every contract of the repository's codegen takes it.
