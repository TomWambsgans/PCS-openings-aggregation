<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# Flock's verifier, minimised (the Flock section of `SPEC.md`)

**Scope.** Option A keeps leanVM 42422001's proof of the BLAKE2s precompile: Flock's zerocheck and lincheck on
`q_flock`, which packs 64 bits per `K`-word. That is `2^14` bits per compression, `2^18` compressions at 1,290
signatures, `log_n = 32`. This section measures what each lever removes from Flock's verifier, keeping
Flock's semantics and its soundness.

**Answer, at 1,290 signatures:**

| | scalars | calldata | execution |
|---|---:|---:|---:|
| leanVM's verifier, as the baseline contract runs it | 224 | 5,376 B | 193,108 |
| the slices left to one **bit-slice combination claim** (lever a) | 160 | 3,840 B | 34,666 |
| that, plus a smaller univariate skip (lever c, `k = 0`–`4`) | 96 to 112 | 2,304 to 2,688 B | 20,000 to 23,000 |

**The floor.** Any Flock with a sumcheck in the contract costs at least `2 (log_n + 14) + 4 = 96` scalars. That is
2.3 KB, or 92,000 gas at EIP-7623's floor. So the whole PIOP cannot get below 100,000 gas while BLAKE2s is proved
in the contract at this size.

**Lever (a) is not a WHIR claim.** The slices' combination is `GF(2)`-linear in the committed words, not
`E`-linear. So lever (a) needs a `PCS_OPEN` claim type that ring-switches inside the opening. With WHIR's
`E`-linear claims alone, weighted ones included, 64 values must stay in calldata, and the best is 3,840 to
5,376 B and about 87,000 gas of execution.

Measured: every number in the tables, on revm, by `crates/leanvm_flock_gas/tests/flock_levers.rs`. The build is
`flock_min.rs` recorded, compiled and run on a stream of the right length, its claims kept live and not counted,
as `keccak_estimate` measures Flock alone. The levers' algebra is tested. With the slices sent, the honest
matrices' reduction verifies at skips 6, 3 and 0. Without them, the combination left holds of the true slices and
fails for others (`flock_min::tests`). Modelled: the prover's costs, and the claim types' implementations.

```sh
cargo test --release -p leanvm_flock_gas --test flock_levers -- --ignored --nocapture   # the tables below
cargo test --release -p leanvm_flock_gas --lib flock_min                                # the levers' algebra
```

## Flock as leanVM verifies it

The sizes are at `log_n = 14 + 18`. Each line gives the scalars the verifier reads.

1. **Zerocheck** of `Az ∘ Bz + Cz = 0` (`C = I`) on the `2^32` bits:
   - a univariate skip over the 6 packing bits: `P` on a 64-point coset (64 scalars);
   - 26 rounds of 2 scalars, the eq factor split off;
   - `v_a`, `v_b` (2 scalars). `v_c` is derived.
2. **Lincheck** of `v_a + α v_b + α² v_c + α³` (the constant's pin): 8 rounds of 2 scalars on the column's slot
   bits, then the 64 slices `s_i = ẑ(i, p)`, `i < 64` the packing bits and `p ∈ E^26` the words' coordinates.
3. **The terminal**, without walking the circuit (`matrices.rs`): 12 rounds of 2 scalars (6 row bits, 6 column
   bits), then claims `a`, `b` on the fixed `A0`, `B0`.
4. **Ring switch**: a map `Φ` of 6 stages (Frobenius shifts 32, 16, 8, 4, 2, 1), the target
   `T = Σ_i x^i Φ(s_i)`, and the weighted claim `⟨Φ(eq(p, ·)), q_flock⟩ = T`. The baseline contract reduces it
   to an evaluation claim. It computes the weight at the stack batch's point, and the stack's batching sumcheck
   carries it.

That is `64 + 52 + 2 + 16 + 64 + 24 + 2 = 224` scalars.

## Lever (a): what the verifier needs of the slices

**They enter only linearly, and one combination suffices.** The matrices' reduction reads three linear forms of
the slices: `Σ_i e_i s_i` (the `C = I` claim, `e` the row's packing weights), `s_0` (the pin) and `ŝ(σ)` (its
terminal). Each enters its check linearly. The first two shift the sumcheck's initial claim, and a degree-2 round
maps its claim `c` to `c_0 + (c + c_2) r + c_2 r²`. So the final claim is `running + λ · (their part)`, with `λ`
the product of the rounds' challenges. The terminal becomes one equation with known weights `μ` and a known
value:

`Σ_i μ_i s_i = running`, `μ = (a + α b) L̂(ρ) eq(σ, ·) + λ α² eq(χ_in, χ_in') e + λ α³ eq(bits(512 ≫ 6), χ_in') [· = 0]`.

The transcript does not change: no round's challenge depends on the derived coefficient. And `μ` costs the
contract 5,200 gas.

**Not an `E`-linear claim.** Since `q_flock(u) = Σ_i z(i, u) x^i`:
- `Σ_i μ_i ẑ(i, p) = Σ_u eq(p, u) ℓ(q_flock(u))`, with `ℓ(y) = Σ_i μ_i bit_i(y) = Σ_(k<64) ν_k y^(2^k)`;
- that is `Σ_k ν_k Frob^k(q̂_flock(Frob^(-k) p))`.

A WHIR claim, weighted or not, is an `E`-linear form of the words, `y ↦ ν y` on each. That is one of the 64
`E`-dimensions of the `GF(2)`-linear maps `K → E`. So the combination is 64 claims at Frobenius-twisted points
whose values are unknown: ring switching's 64 values cannot be compressed with `E`-linear claims alone. This is
the information-theoretic content of leanVM's ring switch (and of Diamond–Posen's): its message is an element
of `E ⊗ K`.

**Three ways to place the ring switch:**

| | slices in calldata | ring switch in the contract | `PCS_OPEN` claim type needed |
|---|---|---|---|
| leanVM (baseline) | 64 | map, coefficients, target, weight at a point, plus the stack's batching sumcheck (55 scalars) | evaluation claims (as today) |
| (a′) weighted claim | 64 | target only (66,288) | a weighted claim with weight `Φ(eq(p, ·))`. The precompile evaluates it, as leanVM's WHIR verifier does |
| (a) bit-slice combination | 0 | none | `Σ_i μ_i ẑ(i, p) = v` on a packed block of the stack. The opening ring-switches inside: leanVM's `ring_switch_open`, the builder's slices, `Φ` drawn from the opening's transcript, one weighted WHIR claim |

(a) carries the point (26 coordinates), the 64 weights and the value: 91 words of `PCS_OPEN` input, about 300
gas of `MSTORE`s. It goes in the stack's call, with every other claim on the stack, as WHIR's lack of an
out-of-domain sample at level 0 requires.

**Soundness.** The bit-slice claim is true exactly when leanVM's terminal check holds of the committed slices. So
(a) proves what leanVM's verifier checks. The check is moved into the opening, not dropped. leanerVM proves that
dropping it loses all security (`linEnd_unchecked_no_security`, mumbai `f0393df4`,
`ToArkLib/Flock/Security.lean`). Ring switching's errors (one per coefficient, and injectivity `hinj`) move with
it into the opening's proof. The claim is drawn after the stack's root, so it pays the Johnson-list union bound
with every other challenge (below).

## Lever (b): batching

- **Within Flock, nothing to batch.** The zerocheck, the lincheck and the matrices' reduction are sequential: each
  one's claim is the last one's output (`α` after `v_a`, `v_b`; the lincheck's row weights at the zerocheck's
  point).
- **Merging the lincheck and the matrices' reduction** into one sumcheck over the column's 14 bits and the skip's
  `k` row bits gives the same rounds: `8 + (k + 6)`.
- **Batching with another sumcheck of the PIOP** (a bus tree layer, for instance) shares a round's message, but at
  different eq points it loses the eq split. That is 3 scalars a shared round instead of `2 + 2`, so it saves at
  most 1 scalar per round of the shorter sumcheck. Not pursued.

## Lever (c): the univariate skip's size

The skip need not be the packing. A skip over `k` bits:
- sends `2^k` values and leaves `log_n - k` rounds;
- vanishes on `Λ = φ(0..2^k)`, with `2^k` values on the coset `φ(2^k..2^(k+1))`;
- leaves the matrices' reduction `k + 6` rounds (the skip's `k` row bits, the column's 6 packing bits). The row's
  other `6 - k` packing bits are already eq coordinates of `A0`'s point.

So Flock reads `2^k + 2 (log_n - k) + 2 + 16 + 2 (k + 6) + 2` scalars, plus 64 if the slices are sent:
`2^k + 96` with lever (a), which is `2^k + 2 + 2 (log_n + 14) + 2`.

The verifier's soundness is unchanged:
- the skip's error is `(2^(k+1) - 1)/|E|`;
- the seven fixed coordinates still see Boolean values (`hfixed`).

The prover is not. leanVM's skip over the 64 packed bits is an additive NTT on bytes, after which the folded
tables have `2^26` entries. With `k < 6`, the first `6 - k` rounds are over packed bits:
- leanVM's `bit_round_pair` passes do two rounds per pass over the bits;
- or the folded tables are `2^(32 - k)` entries.

Modelled: about `2^(6 - k)`× the skip's work and memory, for `6 - k` rounds out of 32. `k = 4` keeps most of the
saving, 48 of 64 scalars. leanerVM's `Flock.flock` ties the skip to the packing (`s = 6` for both), so `k < 6`
needs that parameter split.

## Lever (d): the messages

- **Every round is already minimal.** A degree-2 round sends 2 scalars: the zerocheck's after its eq factor is
  split off, the lincheck's and the matrices' with `c_1` derived from the claim.
- **One skip value can go.** `deg P ≤ 2^(k+1) - 2` and `P` vanishes on `Λ`, so `2^k - 1` values determine it. That
  is one scalar, not done.
- **`v_b` cannot go.** `α` must come after both `v_a` and `v_b`. A `v_b` derived after `α` lets the prover fit
  the batched claim (leanerVM's `alphaDraw_noConst_one_le` is the same point for the pin).
- **`a` and `b` cannot be merged.** They are claims on two commitments; stacked, `A0` and `B0` would be `2^29`
  words.

## Lever (e): the rest

- **Transcript hashing**, about 7,000 gas: one `KECCAK256` per challenge, which is the minimum for 192-bit
  challenges.
- **The combination's weights**, 5,200 gas: they could be sent as three structured terms (eq at `σ`, the skip's
  Lagrange weights times eq, a unit vector) for the precompile to expand.
- **The skip's interpolation** costs 10,400 gas at `k = 6` and 1,150 at `k = 3`.
- **The ring map** (66,288 when the slices are sent) is `64 × 63` squarings: every Frobenius power of every slice.
  A map with fewer powers would leave a nonzero `δ ∈ E ⊗ K` that it sends to zero. So it is inherent once the
  contract computes `T`.

## Measured

`log_n = 32`, 1,290 signatures, `2^18` compressions:

| variant | scalars | calldata bytes | execution | `FIELD_MUL` | `KECCAK256` | claims | at 40 B (floor) | 16 B + execution |
|---|---:|---:|---:|---:|---:|---|---:|---:|
| leanVM: slices sent, ring switch in the contract (map, coefficients, target, weight) | 224 | 5,376 | 193,108 | 8,867 | 74 | stack (via its batch), `A0`, `B0` | 215,040 | 279,124 |
| (a′) slices sent, target only, weight to a weighted claim | 224 | 5,376 | 101,835 | 5,380 | 74 | 1 weighted, `A0`, `B0` | 215,040 | 187,851 |
| **(a)** no slices: one bit-slice combination claim | 160 | 3,840 | 34,666 | 974 | 68 | 1 bit-slice, `A0`, `B0` | 153,600 | 96,106 |
| (a) + (c) skip 5 | 128 | 3,072 | 26,966 | 718 | 69 | 〃 | 122,880 | 76,118 |
| **(a) + (c) skip 4** | 112 | 2,688 | 22,726 | 560 | 70 | 〃 | 107,520 | 65,734 |
| (a) + (c) skip 3 | 104 | 2,496 | 20,778 | 484 | 71 | 〃 | 99,840 | 60,714 |
| (a) + (c) skip 1 | 98 | 2,352 | 20,298 | 446 | 73 | 〃 | 94,080 | 57,930 |
| (a) + (c) no skip | 96 | 2,304 | 20,033 | 400 | 73 | 〃 | 92,160 | 56,897 |
| (a′) + (c) skip 3 | 168 | 4,032 | 87,516 | 4,893 | 77 | 1 weighted, `A0`, `B0` | 161,280 | 152,028 |
| (a′) + (c) no skip | 160 | 3,840 | 86,880 | 4,817 | 79 | 〃 | 153,600 | 148,320 |

The same at `log_n = 27` (32 signatures, `2^13` compressions):

| variant | scalars | calldata bytes | execution |
|---|---:|---:|---:|
| leanVM | 214 | 5,136 | 174,907 |
| (a′) | 214 | 5,136 | 100,439 |
| (a) | 150 | 3,600 | 33,227 |
| (a) + skip 4 | 102 | 2,448 | 21,288 |
| (a) + no skip | 86 | 2,064 | 18,596 |

How to read the last two columns of the first table:
- **The floor column** is Flock's calldata at EIP-7623's 40 a byte. The PIOP pays that when its whole execution
  is below 24 gas per byte of calldata.
- **The 16 B + execution column** applies otherwise.
- **Flock's share of a transaction** is the larger of the two once the rest of the PIOP is added. Its share at
  EIP-7976 (64 a byte) is 1.6× the floor column.

**Breakdown of (a) at `k = 6`** (34,666):

| phase | gas |
|---|---:|
| the skip's interpolation | 10,388 |
| transcript | 7,181 |
| the matrices' terminal (the skip's weights at `ρ`, the pin and `C`-claim weights) | 6,092 |
| the combination's weights | 5,618 |
| calldata reads | 2,604 |
| zerocheck rounds | 1,737 |
| matrices rounds | 564 |
| lincheck rounds | 482 |

**Breakdown of the baseline** (193,108): ring switch 157,498 (its weight at a point 87,559; map, coefficients and
target 69,939) and Flock 35,610.

**Claims and calls at a price `c`:**
- **(a):**
  - one claim joins the stack's call: the bit-slice claim, beside the stack's other claims;
  - `A0` and `B0` are two claims in two calls on fixed roots (cold `SLOAD`s, about 6,300 gas with the calls,
    `crates/leanvm_flock_gas/README.md`);
  - so Flock adds `3c`.
- **The baseline** adds `2c`. Its ring switch's claim is folded into the stack's one claim by the batching
  sumcheck, which costs 1,320 B and about 6,700 of execution, not counted above.

So with lever (a), a transaction pays `3c` against `2c`, and saves 1,536 B, 157,000 of execution, and the batch's
1,320 B.

## Soundness, after the levers

Each of Flock's challenges is drawn after the stack's root. So its error is multiplied by the stack's Johnson list:
`≤ 7,908 ≈ 2^13` at leanerVM's parameters (`review/whir_params.py`).

leanerVM bounds Flock's errors at `(4 κ + 302 + 2^31 + 2^15) / |E|` along every path (`flockErrorsOf_bounded`, `κ`
the batch bits). That is `2^-161`, or `2^-148` after the union bound.

The levers change these terms:
- **(c)** makes the skip's term `2^(k+1) - 1` instead of 127, and turns its other `6 - k` bits into ordinary rounds
  (error 2 each).
- **(a)** moves the six ring-switching terms (`1` each) and the terminal check into the opening. The opening's own
  transcript (seeded by the claims, as `PCS_OPEN`'s are) draws `Φ`.
- **Both stay above 140 bits.**

## The floor, and the target

Flock is Spartan's two sumchecks on `2^log_n` bits:
- a zerocheck of `log_n` variables;
- a lincheck of the 14 within-compression column variables (the skip's `k` row bits add `k` rounds to it and
  remove `k` from the zerocheck);
- degree-2 rounds of 2 scalars each;
- four values (`v_a`, `v_b`, `a`, `b`).

That is `2 (log_n + 14) + 4 = 96` scalars at `2^18` compressions, plus the skip's `2^k` and the slices' 64 if
they are not left to a claim. The other options do not escape it:
- a univariate quotient instead cannot read packed bits (`SPEC-B.md`);
- the rounds' messages must be in calldata, each bound before its challenge;
- none of them is an evaluation of a committed polynomial.

So a contract that verifies Flock reads at least 2.3 KB at 1,290 signatures, about 92,000 gas at EIP-7623's floor.
The `< 100,000` target for the whole PIOP is out of reach while BLAKE2s is proved by a sumcheck in the contract at
this size.

The lever that remains is a claim type for the R1CS validity of a packed block: "the block of the stack is a valid
Flock witness of `2^κ` compressions". The block's builder would run the whole Flock argument (zerocheck, lincheck,
ring switch) inside the aggregated proof, as it opens the stack. BLAKE2s would then cost the contract one claim
and no calldata. That widens `PCS_OPEN` from openings to one fixed relation, a decision for the design note.

**Recommendation for option A.** Take (a) with `k = 4`: 112 scalars, 22,700 of execution, and a bit-slice claim
type, about 2.7 KB of calldata. If `PCS_OPEN` must stay `E`-linear, take (a′) with `k = 3`: 168 scalars, 87,500
of execution, and a weighted claim type.

## BLAKE2s's share: baseline, option A, option B

The table is at about 1M cycles. The spec's reference workload (1,000 signatures, 202,025 compressions) and the
1,290-signature proof both have `2^18` compressions and `log_n = 32`, so the numbers are the same.
- **Flock's own part**, from the measured table above:
  - calldata;
  - execution, plus `A0`'s and `B0`'s two calls. The calls are not measured here: about 1,500 each with the roots
    in code, as `SPEC.md` has them, or 6,300 for both with the baseline's `SLOAD`s.
- **Claims:** Flock's claims on `q_flock` join `C1`'s one claim (`SPEC.md` §8), so Flock adds `A0` and `B0`: `2c`
  in every row.
- **The transaction's share** is shown both ways, the floor at 40 a byte and 16 a byte plus execution. The PIOP
  pays the larger of its totals, not of its parts.

| | calldata | execution | claims / calls added | share at 40 B | 16 B + execution | `+ c` per claim (0 / 2K / 5K / 20K) | committed for BLAKE2s | prover |
|---|---:|---:|---|---:|---:|---|---|---|
| baseline (leanVM's Flock, ring switch in the contract) | 5,376 B | 193,108 + calls; the stack batch's 1,320 B are not counted | 2 / 2 | 215,040 | 279,124 | +0 / 4K / 10K / 40K | `q_flock` `2^26`; `A0`, `B0` `2^28` each (setup) | leanVM's (2.59 s for the whole proof, measured on h1) |
| A, (a′) `k = 6` (`SPEC.md` §7 as written) | 5,376 B | 101,835 + calls | 2 / 2 | 215,040 | 187,851 | 〃 | 〃 | leanVM's |
| A, (a) `k = 6` | 3,840 B | 34,666 + calls | 2 / 2, and a bit-slice term on `C1` | 153,600 | 96,106 | 〃 | 〃 | leanVM's; the ring switch moves to the block's builder |
| **A, (a) `k = 4`** | **2,688 B** | **22,726** + calls | 〃 | **107,520** | **65,734** | 〃 | 〃 | plus one pass over the packed bits (modelled, a few %) |
| A, (a) `k = 0` | 2,304 B | 20,033 + calls | 〃 | 92,160 | 56,897 | 〃 | 〃 | 6 rounds on packed bits (modelled, about 2×+ the zerocheck) |
| B-word (`SPEC-B.md`), if it fitted | ≈ 850 B | ≈ 12,000 | 3–4 / 1 | ≈ 34,000 | ≈ 26,000 | +0 / 6–8K / 15–20K / 60–80K | `2^33.6 + 2^33.1` words: **does not fit `2^28`** | ≥ 100× the baseline's committed words |
| B-plonk, if it fitted | ≈ 100 B | ≈ 10,000 | 4 / 1 | ≈ 4,000 | ≈ 11,600 | 〃 | `2^35.4 + 2^39.0`: **does not fit** | infeasible |

At 32 signatures (`2^13` compressions, `log_n = 27`):
- option A's (a) with `k = 4` reads 2,448 B for 21,288 of execution;
- the baseline reads 5,136 B for 174,907;
- B fits there only as the unreachable B-ideal bound (`SPEC-B.md`).
