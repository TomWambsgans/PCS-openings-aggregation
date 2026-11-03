<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# π1's claims' points on chain (lever 1(b))

**Status: designed and modelled; the core is in code and tested. Not built into π1, π2 or the contract, because it
wins about 6.0K gas on top of `leanvm-rec-opt` and 10.5K on R3's 73,550, below the ~15K bar (§8).**

- Branch `leanvm-rec-points`, from `leanvm-rec` @ 4a57c61.
- The core is `leanvm_flock_gas::transcript::sumcheck_pairs`.
- Every number is marked **measured** (on h1) or **modelled** (`review/leanvm_rec_params.py`, its last section).

```sh
RUSTFLAGS="-C target-cpu=native" cargo test --release -p leanvm_flock_gas --lib transcript -- --nocapture
RUSTFLAGS="-C target-cpu=native" cargo test --release -p leanvm_univariate --lib domain
python3 -I review/leanvm_rec_params.py   # the last section: "the claims' points"
```

## 0. Summary

- **What the contract carries.** On R3, π1's claims put 46 coordinates and 5 values in calldata (1,224 B). On
  `leanvm-rec-opt` there are no claims on `A0`, `B0` (π1-rec2 walks the BLAKE2s circuit inside π2), so 27
  coordinates and 3 values remain (720 B). The 27 coordinates are the batching sumcheck's point `r`.
- **Why `r` stays.** `C1` carries Flock's ring switch, a claim on `q_flock` at 64 Frobenius twists of a 26-coordinate
  point that Flock's sumchecks drew. With `PCS_OPEN`'s point claims, a sumcheck over `q_flock`'s variables is the
  only reduction of that claim, so its point needs fresh challenges.
  - DEEP does not remove that sumcheck, so it saves no coordinate.
  - Gemini, Zeromorph and the univariate sumcheck give each coordinate back as a claim's value, or worse (§2).
- **What can change:** how many challenges generate `r`. The batch is run two variables a round, on `V_2`'s
  coordinate functionals. Then `r` is 13 pairs `(y_0(z_j), y_1(z_j))` and one plain coordinate: 14 elements instead
  of 27. This costs no Keccak-f, and π2 grows by only 56K positions (§3, §6). Three variables a round would cost 18
  more Keccak-f, which π2 cannot hold.
- **Gas** (modelled, EIP-7623, `c = 0`, without the base): `leanvm-rec-opt`'s 51,727 → 45,717 (−6,010). R3's 73,550 →
  63,084 (−10,466). The 312 bytes saved are worth 6.0K to 12.5K at any execution: 16 or 40 gas a byte. Under
  EIP-7976 they are worth 20.0K.

## 1. The claims and their points (measured)

| | R3, π1-rec (`leanvm-rec` @ 4a57c61) | π1-rec2 (`leanvm-rec-opt` @ 5e0ea89) |
|---|---|---|
| π1's claims | `C1`, `C2` at `r` (27); `F` at `r[..24]`; `A0`, `B0` at `p` (28: 9 from `r`, `row_low` 3, `χ_in` 8, `χ_in'` 8) | `C1`, `C2`, `F` at `r` |
| their public elements | 46 coordinates and 5 values: 1,224 B | 27 coordinates and 3 values: 720 B |
| calldata / execution / EIP-7623 `c = 0` | 1,844 B / 39,674 / 73,550 | 1,292 B / 31,103 / 51,727 |
| π2's positions, ports | 14,370,656 (85.7%), 67 | 15,880,064 (94.7%), 47 |

`leanvm-rec-opt`'s lever 1a′ takes the matrices' claims out of this problem. What is left is `r`: 27 coordinates,
648 B, the batching sumcheck's 27 challenges.

## 2. Why the batch's point stays

### 2.1 The ring switch needs a sumcheck over `q_flock`

Flock (a′)'s ring switch is one of `C1`'s relations:

`Σ_u Φ(eq(P, u)) q_flock(u) = target`, with `Φ(eq(P, ·)) = Σ_(k<64) c_k eq(P^(2^k), ·)`.

`P = (χ_in', χ_rest)` holds 26 challenges of Flock's lincheck and zerocheck rounds.

- `PCS_OPEN` takes point claims (`E`-linear evaluations), so this 64-point claim must become point claims on `C1`.
- The 64 values `q̂(P^(2^k))` are not known. Sending them would make 64 claims and 64 values on chain.
- So it is reduced by a sumcheck over `q_flock`'s 26 variables. Binius's ring switch ends the same way.
- A sumcheck's challenge must be drawn after its round's message. A challenge known earlier lets the prover answer
  any claim.
- That sumcheck is the batch, whose point every other relation shares at no extra coordinate.

Even if Flock's own rounds were paired (§2.4), `P` would be 13 fresh elements, and its twists still 64 points.

### 2.2 DEEP and interleaved layouts

The other relations are at points derived from `t` and `c`:

- columns at `t`, `t + 1`, `s(t)`;
- the heap's restrictions at mixed points;
- `Q_W`'s copies at `y(t)`;
- `F`'s point `(α, w(t))`.

DEEP could fold the univariate ones into one quotient `G` in a new commitment `C3`, with claims at a fresh `z`. With a
group's column index as the low coordinates, `Σ_j eq(w_(<c)(x), j) col_j(w_c(x))` is the interleaved polynomial's
value at `x`: one point claim for each height group. But:

- **It saves no coordinate.** The batch stays for `q_flock` (§2.1), and its point already carries every other claim.
- **It costs π2 more than π2 has.** Every column's value at every point must be sent: about 80 more values, 1.9 KB of
  π1's stream, about 14 Keccak-f, or 1.9M positions. π2 on π1-rec2 has 0.90M left.
- **It costs a commitment and claims.** `C3` is E-valued, up to the columns' size, and its list joins the union bound.
  Each height group needs its own claim, because its DEEP identity has its own denominator: at least 4 on `C1`.
- **The heap's restrictions are not univariate evaluations of `T`.** They are multilinear claims at
  `(w_(<r)(t) + w_(<r)(o), w_(≥r)(o))`. Per-table heaps would turn them into `T_b(β_r + t)`, but that means
  rewriting π1's prover.

### 2.3 Gemini, Zeromorph, the univariate sumcheck

Each would replace `q_flock`'s claim at a fresh point `r_q` by univariate evaluations at one random `z`.

- **Gemini in characteristic 2.** The additive fold is `F_(j+1)(s(x)) = F_j(x) + (x + r_j)(F_j(x) + F_j(x + 1))`, since
  `s(x) = s(x + 1)`.
  - It commits `F_1 … F_25`, E-valued, about `2^26.6` words.
  - It needs `F_j` at `w_j(z)` and at `w_j(z) + 1`: two claims at each level, at different points.
  - That is about 50 values on chain (1,200 B) to save 26 coordinates (624 B).
- **Zeromorph.** It writes `q̂(u) − v = Σ_l (u_l + r_l) q̂_l(u_(>l))`. In basis `B` that is
  `q(x) − v = Σ_l (w_l(x) + r_l) Q_l(w_(l+1)(x))`, each `Q_l` read at the digits of `w_(l+1)(z)`.
  - Zeromorph merges the `Q_l` through its commitment's homomorphism (KZG). WHIR's Merkle roots have none.
  - One stack can hold every `Q_l` at the positions whose lowest set bit is `l`. At `digits(z)` it gives
    `Σ_l Π_(j<l)(1 + w_j(z)) w_l(z) Q_l(w_(l+1)(z))`: one combination, with weights fixed by `z`.
  - The identity needs the weights `w_l(z) + r_l`, which carry `r`. So each `Q_l(w_(l+1)(z))` is its own claim:
    about one value for each coordinate saved.
- **The univariate sumcheck over `q_flock`'s values.** It writes `q̂(r) = Σ_(x ∈ V_26) E_r(x) Q(x)`.
  - It needs E-valued quotients of `2^26` points, about `2^27.6` words.
  - `E_r(z)` is a sum of `2^26` terms.
  - SPEC-REC §1.5 already found that a univariate batch needs a `2^28.6`-word quotient.

In each case the coordinates come back as claim values, at least as many of them.

### 2.4 What can change: the challenges per round

A round of `k` variables on `V_k`'s coordinate functionals works as follows:

- The functionals satisfy `y_l(ω_i) = i_l` (SPEC.md §2).
- The round sends the summand restricted to the curve `u = y(X)`: a polynomial `G` of degree `2 · k · 2^(k-1)` when
  the summand has degree 2 in each variable.
- Then `Σ_(x ∈ V_k) G(x)` is the sum over the round's `2^k` corners.
- One challenge `z` gives the `k` coordinates `y_l(z)`.
- No curve does better. A curve through the `2^k` corners on `2^k` points has coordinates of
  degree at least `2^(k-1)`: each takes two values there, so the vanishing polynomial divides `y(y + 1)`.

π2 hashes that data. Over the batch's 27 variables (modelled; Keccak-256's rate is 136 bytes):

| rounds of | challenges | scalars | Keccak-f | π2 |
|---|---:|---:|---:|---|
| 1 variable (today) | 27 | 54 | 27 | |
| **2 variables** | **14** | 106 | **27** | **+0 Keccak-f** |
| 3 variables | 9 | 216 | 45 | +18 (2.35M positions) |
| 4 variables | 7 | 408 | 77 | +50 |
| 3 triples, 9 pairs | 12 | 144 | 33 | +6 (0.79M positions) |

- **Pairs cost no permutation.** A plain round's 2 scalars and the 32-byte state are 80 bytes, which fit in one block.
  A pair's 8 scalars and the state are 224 bytes, two blocks.
- **Triples do not pay.** Against pairs, each triple costs 2 more permutations and saves half a challenge. π2 on
  π1-rec2 has 0.90M positions left (6.9 permutations), so 12 challenges would take all of it, to save 48 bytes.

## 3. The design: the batch two variables a round

- **The rounds** (`transcript::sumcheck_pairs`, in code). A pair is `(u_(2j), u_(2j+1))`, low variables first. Its
  polynomial is `G_j(X) = Σ_rest Σ_k λ^k W_k(·) C_k(·)`, read at `(r_(<2j), y_0(X), y_1(X), rest)`. It has degree 8.
  - `V_2 = {0, 1, β_1, 1 + β_1}` is `GF(4)` (`β_1² + β_1 = 1`). So `Σ_(x ∈ V_2) x^e` is 1 for `e ∈ {3, 6}` and 0 for
    every other `e ≤ 8`.
  - The stream holds `c_0, c_1, c_2, c_4, …, c_8`, and `c_3 = claim + c_6`.
  - One challenge `z_j` gives `r_(2j) = y_0(z_j) = z_j + β_1 y_1` and `r_(2j+1) = y_1(z_j) = z_j² + z_j`.
  - 27 variables are 13 pairs, then one plain round, with `r_26 = z_13`.
- **What stays.** The rest of π1 is unchanged: the weights `W_k(r)`, the three values, and the claims `C1(r)`, `C2(r)`,
  `F(r[..24])`. Only the rounds and their challenges change.
- **The Fiat–Shamir shape.** One more shape beside `Rec`: π1-rec2 with the batch's rounds paired. `Rec` and `Rec2` are
  kept.
- **π2.** The circuit is compiled from the recorded verifier, as now. Its public elements are the 14 `z_j` and the 3
  values instead of `r`'s 27 coordinates. A pair's two call words are `y_0`, `y_1` of a port, not ports themselves:
  - 34 ports instead of 47;
  - the map `z ↦ (y_0(z), y_1(z))` is injective (`y_0 + β_1 y_1 = z`), so binding the `z_j` binds `r`.
- **The contract.** It reads the 14 `z_j` and derives the 27 coordinates of the three `PCS_OPEN` calls: 13 times one
  squaring, one product by `β_1` and two XORs. `leanvm-rec-opt`'s lever 3b already writes `r` once for the three calls.

**Measured** (`leanvm_flock_gas` `transcript::tests`, `leanvm_univariate` `domain::tests`):

- the paired sumcheck is complete on honest product sums of 1, 2 and 3 tables, at odd and even variable counts;
- a wrong claim, and each flipped scalar, ends on a claim the tables do not give;
- `pair_point` is `V_2`'s coordinate functionals, and `cantor_beta1` is `domain::beta()[1]`;
- recorded over 27 variables at degree 2: 27 Keccak-f either way, 14 challenges against 27, and 278 E operations
  against 135.

## 4. Calldata and gas (modelled; EIP-7623 `c = 0`, without the base)

| | calldata | execution | transaction | change | EIP-7976 `c = 0` |
|---|---:|---:|---:|---:|---:|
| π1-rec2 (`leanvm-rec-opt` @ 5e0ea89), measured | 1,292 B | 31,103 | 51,727 | | 82,688 |
| **+ pairs** | **980 B** | ≈ 30,085 | **≈ 45,717** | **−6,010** | 62,720 (−19,968) |
| + `r` from one element (a bound; not reachable, §2) | 668 B | ≈ 28,365 | ≈ 39,005 | −12,722 | 42,752 |
| R3, π1-rec (`leanvm-rec` @ 4a57c61), measured | 1,844 B | 39,674 | 73,550 | | 118,016 |
| **+ pairs** | 1,532 B | ≈ 38,656 | ≈ 63,084 | −10,466 | 98,048 (−19,968) |

- **The execution saving.** There are 13 fewer ports at 103.6 gas each. That figure is measured: `leanvm-rec-opt`'s
  lever 1a′ took 67 ports to 47 and the public side from 6,794 to 4,723 gas. There are also 13 fewer reads, and
  312 bytes fewer in π2's first hash.
- **The execution cost.** The 13 pairs' derivation costs about 50 gas each.
- **Why the gain is small.** On π1-rec2 the transaction sits at EIP-7623's crossover: `16 B + X` = 51,727, against a
  floor of 51,560. Below the floor a byte costs 16, not 40. So the 312 bytes are worth between 6.0K and 12.5K:
  - 6.0K at 16 a byte, as now, with execution binding;
  - 12.5K at 40 a byte, if execution fell far enough for the floor to bind on both sides.
  - Even all of `r` from one element would win 12.7K now.
- **Claims.** The claims and the calls are unchanged (3 and 4 claims, 6 calls), so `c > 0` adds the same.

## 5. Soundness (modelled)

- **A pair's error.** Its polynomial has degree 8, so its Schwartz–Zippel error is `8/|E|`. It is drawn after `C2`,
  over `C1`'s and `C2`'s lists (4,473²).
- **The batch.** `λ` and the batch keep 185.2 bits alone and 161.0 after the union (plain rounds: 186.2 and 161.9).
- **The PIOP.** Its minimum is still `t`'s 142.3 bits.
- **The point is not uniform.** Each pair of coordinates lies on a curve. Neither argument needs uniformity: the
  sumcheck makes one Schwartz–Zippel step a round, in `z_j`, and WHIR's openings are sound at every point.
- **No new list.** There is no new commitment, and the openings are the same 6 (π1's 3, π2's 3).

## 6. π2's size

- **Keccak-f: 107, unchanged** (measured, recorded: the batch's 27 permutations either way).
- **Positions** (modelled from SPEC-REC §10.3's per-item counts):
  - 52 more stream scalars, 1,248 B of π1's stream: free bits and packings;
  - 13 fewer challenge packings;
  - 13 more later blocks (a pair's second block);
  - 143 more E operations (measured).

  That is +55.8K positions: π1-rec2's π2 goes from 15,880,064 to about 15,936K of `2^24` (95.0%). `Q = 15N` stays
  `2^27.91`.
- **π2's verifier** has 13 fewer ports.

## 7. The prover (modelled)

- **The batch today** is 0.57 s of π1's 6.2 s (PROVER.md). Its first 6 rounds are memory-bound, 43 ms each over the
  stacks' 2 GB.
- **A pair round takes nine sums.** For each piece of the weights and each group of four words, it takes
  `Σ W(a, b, ·) C(a, b, ·)` for `a, b ∈ {0, 1, ∞}`. These are the coefficients of `G̃`, and then
  `G = G̃(y_0, y_1)`. It folds the tables at the pair's two coordinates.
- **Two ways to write it.**
  - A two-variable kernel in `weight.rs` (factored, dense and twisted pieces) reads the stacks once a pair: about
    −0.1 s.
  - The existing `Weight::round` and `Weight::fold` can be reused: each base pair binds its low variable at 0, 1
    and a third point on clones of the weights, then takes one round on the high variable. That is four passes a
    pair instead of two, about +0.25 s.
- **No extra memory, no new commitment.** The stream grows by 1,248 B.

## 8. Decision, and what building it takes

**Decision: not built beyond the core.**

- **The bar.** The brief sets ~15K. Pairs win 6.0K on `leanvm-rec-opt`, 10.5K on R3, and at most 12.5K at any
  execution under EIP-7623. Nothing in §2 reaches fewer challenges at the 0.90M positions π2 has left. Even the
  unreachable bound is 12.7K on `leanvm-rec-opt`.
- **For it.** Pairs are cheap: no commitment, no Keccak-f, about 56K positions. They take `leanvm-rec-opt` from 51.7K
  to about 45.7K, and save 20.0K under EIP-7976. Worth building if the target moves there, or once execution falls
  enough for the floor to bind (then 12.5K).

**Steps, on top of `leanvm-rec-opt`** (its π1-rec2, π2 and contract; not on `leanvm-rec`):

1. **π1's verifier.** A shape `Rec2` with paired rounds. `verifier::batch` calls `sumcheck_pairs(channel, target, 2,
   vars)` instead of `sumcheck(…, 3, …)`, and `contract_iv_for` binds the shape.
2. **π1's prover.** `prover/batch.rs` sends a pair's 8 coefficients and folds at `pair_point(z)` (§7), with the last
   variable a plain round. `prove_real` regenerates the vector.
3. **π2:**
   - `circuit::compile` takes each pair's challenge as the port, in place of its two coordinates;
   - `circuit::spec`'s call words gain "`y_0` / `y_1` of a port";
   - `pi2::contract` derives them before the calls;
   - recompile, then `real_gas` and `real_end_to_end`.
4. **Tests:**
   - the paired batch against an honest prover at every shape;
   - the contract equal to the Rust verifier, word for word;
   - flipped `z_j` bytes revert.
