<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The construction adapts the padding of leanVM's
flock::membership (https://github.com/leanEthereum/leanVM, branch PCS-openings-aggregation,
crates/flock/membership-zk.md), whose Lemma 4, Lemma 5 and "the siblings" this argument follows. -->

# Hiding the commitments and their openings

The reduction (`protocol::reduce`) leaves two roots, five field elements and four claims; its masks make the
four `a_j` uniform given the statement and `t`, and the fifth, `next = σ(t)`, is not masked but is public: the
wiring polynomial, a function of the circuit, at `t`. This note is about the rest of what a prover publishes for its two secret tables: the
**roots** (in calldata) and the **WHIR openings** of the claims. Before this change both were deterministic
functions of the witness: the witness table `R1` held `w_hat` and the masks in clear lanes, so a verifier who
guesses a witness could recompute the root from it (the four `a_j` pin the twelve masks), and the opened rows of
`R1` and `R2` matched the guessed witness's rows. Now both tables are committed in **hidden layouts**, leanVM's
WHIR verifier is unchanged (`verifier::whir::verify_whir`, a stack of at most `2^28` words in 64 lanes, claims as
weights), the claims and the contract are unchanged, and the prover is the memory-lean one (a lane tensor a claim
on the blocks, one on the overflow lane, two for the gadget). The wiring table is public and keeps its plain layout.

## What is hidden

Notation: `K = GF(2^64)`, `E = GF(2^192)`; a stack has `L ≤ 64` lanes of `2^ℓ` words (`ℓ = log_n - 6`); `s =
LOG_PIECE = 8`, `D = 2^s - GADGET = 247`; leanVM's WHIR folds the six lane variables first (`φ ∈ E^6`, lane `l`
weighs `e_l = eq(φ, l)`, variable `j` is bit `j` of `l`), batches the claims with powers of one challenge `λ`,
opens the first commitment at a set `Q` of positions of its domain of `2^(ℓ+1)` points (222 to 225 queries at
rate 1/2, so `|Q| ≤ 225`), and takes no out-of-domain sample there.

**Theorem.** Fix the challenges of an opening. Let `T` and `T'` be two tables of a hidden layout on which every
claim of the opening has the same value. If

- **(Q)** `|Q| < D`,
- **(S)** the fold weights `e_r` of the random lanes span `E` over `K`,
- **(R)** the randomness reaches all 33 dimensions of the lane rounds (defined below),

then a translation of the padding (a bijection) maps the opening's view of `T` up to WHIR's first fold onto that
of `T'`: the six lane rounds, the folded table `f¹`, and every opened row. Everything WHIR shows after the first
fold (the first in-lane message, the commitments to `f¹` and the deeper levels, their out-of-domain values, rounds,
the grinding nonces, rows, the final polynomial) is a function of `f¹` and the challenges (a nonce is the
smallest valid one, a function of the transcript before it), so the whole opening of `T` is distributed
as that of `T'`. Given the view, every unopened row of the first commitment keeps `L - 3` uniform `K`-elements,
`64(L - 3)` bits: `2368` for `R1` (40 lanes), `3840` for `R2` (63 lanes). Modelling Keccak-256, where it hashes the
first commitment's rows, as a random oracle, the **roots and the openings** of `T` and `T'` are then
indistinguishable but with probability `2·H·2^(ℓ+1)·2^(-64(L-3))` for `H` oracle queries ("the siblings" of
`membership-zk.md`, unchanged: exchange the oracle's values on each pair of corresponding unopened rows; inner
nodes and the root then agree).

**(Q) holds always, and (S) and (R) hold for every challenge outside**

`B = {λ = 0} ∪ {some φ_i ∈ {0, 1}} ∪ {two of φ_0, φ_1, φ_2 lie in K}`, `Pr[B] ≤ 13·2^-192 + 3·2^-256 < 2^-188`,

**whatever the claims, their points and values** ("Condition (R) for every challenge: the gadget"). Before the
gadget, (R) was only observed at random challenges (the provable bound was about `2^-54`, through the
`K`-coordinates of `φ`) and (S) was bounded by `2^-127 + 13·2^-192`.

With the reduction's own masking (the `a_j` uniform given the statement and `t`, `next = σ(t)` public, so the
claims are functions of uniform and public values), the prover's whole output for one statement is the same for
any two witnesses. What is not
hidden: the statement, the circuit, the wiring table and its opening, the sizes.

**Assumptions.** Keccak-256 as a random oracle on the first commitment's rows; the transcript hashes as
programmable random oracles for Fiat–Shamir (the standard transfer, as in `membership-zk.md`, not redone here);
the masks and the padding seed are secret, uniform and fresh per proof, never reused (below); an honest verifier's
challenges, outside `B`.

## The layout

`opening::Layout::hidden`, for a table that `Layout::new` would stack as whole blocks of `2^ℓ` entries plus the
tails of its chunks:

- **Every lane's first piece** (entries `0 .. 2^s`, the coefficients of the basis polynomials of degree below
  `2^s`) is uniform, but for the gadget's values (below).
- **Block lanes** hold a whole block each but its first piece, which is on the overflow lane. The first 32 blocks
  are on lanes `0 .. 32` (random lanes there if there are fewer), the others from lane 40 on.
- **The overflow lane** is lane 32 (`opening::OVERFLOW_LANE`): its pieces `1 .. H` hold the blocks' first pieces,
  then the chunks' tails (the masks' piece; for `R2` the three spills of `q`, 37 pieces each, and the gate
  quotient's 64 entries); its pieces past `H` are uniform.
- **The random lanes** are lanes `33 .. 40`: with the overflow lane, the cube of lanes `32 .. 40` (bits 0, 1, 2
  free, bits 3 and 4 zero, bit 5 one).
- **The gadget** (`opening::GADGET`, `gadget_lanes`, `Layout::gadget_entry`): at the last nine entries of every
  lane's first piece, three patterns of three entries. Pattern `g` weighs its lanes by `μ·β_i` at its entry
  `D + 3g + i`, `β = 1, t, t²` the basis of `E` over `K` and `μ = λ^m` the power of the challenge after the `m`
  claims'. Pattern 0 is lanes 0 and 31, which hold one random value there; pattern 1 lanes 1 and 30, likewise
  (pairs complementary in bits 0 to 4, in the lower half); pattern 2 the overflow lane (in the upper half), which
  holds zero there.

| table | before | hidden | random lanes | stack |
|---|---|---|---|---|
| `R1` (witness, one claim) | 33 lanes | 32 blocks, overflow (33 pieces), 7 random: **40 lanes** | `WITNESS_RANDOM_LANES = 7` | `2^25` words, unchanged |
| `R2` (quotient, two claims) | 59 lanes | 55 blocks, overflow (167 pieces), 7 random: **63 lanes** | `QUOTIENT_RANDOM_LANES = 7` | `2^28` words, unchanged |

**The claims do not change.** A claim at `p` is the table's `eq(p, ·)` carried to the stack: `ω_l · eq(p_low, y)`
on block lane `l` past its first piece (`ω_l = eq(p_high, block)`), `ψ_k · eq(p_{<s}, ·)` on piece `k` of the
overflow lane (`ψ_k = eq(p_{≥s}, k-th held piece)`), zero elsewhere: every claim's value is the table's, and it
weighs nothing of the randomness. The opening proves `Σ_c λ^c v_c = Σ W·T` for `W = Σ_c λ^c W_c + λ^m G`, `G` the
gadget: **the gadget is one more claim, of value zero**, which an honest stack meets (`μβ_i·z + μβ_i·z = 0` on a
pair, `μβ_i·0` on the overflow lane). Batched with its own power, the opening binds a stack to it as to the claims;
weighed with the first claim instead, a cheating prover could set the gadget's entries (words of the first piece,
not of the table) to add any element of `E` to that claim's value (`opening::tests`,
`claims_open_against_a_hidden_table`: such a stack opens neither the offset claim nor the true ones). As lane
tensors the weight is one a claim on the blocks, one on the overflow lane (the claims' and pattern 2) and one for
each of patterns 0 and 1: 4 for `R1`, 5 for `R2` (they were 3 and 6), which is what
`pcs::whir::recursive_prover_with_lane_tensors` takes (`Layout::weight`); the verifier's closure costs `O(L + H·ℓ)`
products a claim and nine more. `R1`'s and `R2`'s reductions, points, values, and so the EVM contract, are those
of the plain layouts.

**Soundness does not change**: the WHIR verifier is leanVM's, the table a stack encodes is held on the same blocks
and pieces as before or fewer (the spills now take 37 pieces, not a lane), which `fits` checks, and the batch has
one term more (the gadget's), `m + 1` instead of `m` in front of the Johnson list.

**Randomness.** The masks and the padding's seed must be uniform, secret, and **fresh per proof, never
reused**: two proofs that share the padding's seed have the same random first pieces, which their opened rows
then pin across both proofs' positions (about 446 > 256), and two that share the masks let the second proof's
`a_j` be predicted from the first's for a guessed witness; either confirms the guess (`review_hiding.rs`,
`reused_seed_confirms_the_witness`, `reused_masks_confirm_the_witness`). So `protocol::prove` draws its own: a
32-byte seed per proof from the operating system (`protocol::fresh_seed`, `rand`'s `OsRng`, which keeps no
state in the process and so does not repeat in a fork), from which `protocol::Randomness::derive` makes both by
Keccak-256 with distinct tags, a key binding the seed, the circuit's commitment, the statement and a digest of
the witness's cells: a seed that repeats anyway (a restored snapshot) gives unrelated randomness for another
witness or statement, and the same proof again for the same ones. `protocol::prove_with_seed` takes the seed,
deterministic, for tests and reproducible benchmarks, with the same requirement; randomness given directly
(`prove_with_randomness`) is crate-private, for the tests that show what reuse reveals.
A table's seed is Keccak-256(`"pcs-quotient-pad-" ‖ table ‖ seed`); lane `l` is filled by ChaCha12 (`rand_chacha`'s
`ChaCha12Rng`, by name) keyed by Keccak-256(table seed ‖ `l`), so the prover is deterministic given the seed and fills lanes in
parallel; then each gadget pair's second lane takes its first lane's values there, and the overflow lane's
pattern-2 entries are set to zero. Tests and the benchmark draw the proof's seed from `primitives::test_rng`.

## Why it hides

The view up to the first fold is `K`-linear in the stack: **(V1)** the six lane rounds, two `E`-values each,
`h_j(0)` and `h_j`'s quadratic coefficient `c_j`, with
`h_j(X) = Σ_{l, l' agreeing above bit j} eq(φ_{<j}, l) eq(φ_{<j}, l') eq(X, l_j) eq(X, l'_j) ⟨W_l, T_l'⟩`;
**(V2)** `f¹ = Σ_l e_l T_l`; **(V3)** each lane's codeword at each `x ∈ Q`, `Σ_y T_l(y) X_y(x)` in the novel basis
(`X_y` of degree `y`). Let `Δ` be `T' - T` on the table's entries; it keeps every claim.

1. *Past the first pieces.* The claims' weight vanishes on first pieces. At an entry `y` past the first piece, the
   random unknowns there (the random lanes, and the overflow lane where it holds none of the table) span `E` by
   (S): pick a change of them that cancels `Δf¹(y)`. The change of (V1) left over keeps the claims (the gadget's
   zero claim too: `Δ` and these changes are zero on the gadget's entries) and the last round's value at its
   challenge, `h_5(φ_5) = Σ_y W̃(y, φ) f¹(y)`: it lies in `H = ker lastMap`, a 33-dimensional `K`-space (an
   `E`-hyperplane of `E^12`). **Condition (R)**: the changes of the random unknowns at single entries that keep
   `f¹` and the claims span all of `H` through (V1). Then the leftover is cancelled too, by such changes at the
   gadget's entries (in the first piece, above `D`).
2. *First pieces below the gadget.* Each lane's codeword at `Q` changed by `M·Δ_l`. Polynomials of degree below
   `D` take any values on `|Q| ≤ D` points, so a right inverse `N` of the evaluation at `Q` of entries `0 .. D`
   exists: change them by `-N(M·Δ_l)`, lane by lane. Every opened row agrees, `f¹` there changes by
   `-N(M·Σ_l e_l Δ_l) = 0` (every entry of `f¹` already agrees), and (V1) does not see entries below `D`.
3. *An unopened row* `x ∉ Q`: with `|Q| < D` (Q), some `u` of degree below `D` vanishes on `Q` and is 1 at `x`.
   Translating entries `0 .. D` by `c_l·u` with `Σ_l e_l c_l = 0` keeps (V1)–(V3) and moves row `x` by `c`:
   `L - 3` free `K`-elements.

## Condition (R) for every challenge: the gadget

**Statement.** For every `λ ≠ 0` and every `φ` with **(a)** `φ_i ∉ {0, 1}` for every `i` and **(b)** at most one
of `φ_0, φ_1, φ_2` in `K`, the changes of the randomness at the gadget's nine entries alone that keep `f¹` and every
claim reach all of `H` through the rounds, whatever the claims (the claims weigh nothing there). (a) and (b) also
give (S).

Write `B(w, τ) ∈ E^12` for the twelve values the rounds of one entry give a weight `w` and a table `τ` on the 64
lane indices; the rounds of a stack are `Σ_y B(W(·, y), T(·, y))`, bilinear.

1. **Solvers.** At pattern 0's and 1's entries the weight is on the lower half (bit 5 zero), at pattern 2's on the
   upper half. A lane `r` of the other half meets a weighted lane only in `c_5`: rounds `j < 5` pair lanes that
   agree above bit `j`, bit 5 included, and `h_5(0)` pairs lanes whose bit 5 is zero. So `B(w, e_r) ∈ E·e_{c_5}`.
   The other half's values at the entry include a cube of lanes in bits 0, 1, 2 (lanes `32 .. 40` in the upper
   half, the witness table has no others; `0 .. 8` in the lower), whose fold weights are `c·eq(φ_{012}, x)`,
   `x ∈ {0,1}^3`, `c` a product of `φ_i`, `1 + φ_i` (nonzero by (a)), so their `K`-span is `c` times that of the
   eight multilinear monomials in `φ_0, φ_1, φ_2`: all of `E` by (b) and *the lemma*: if `span_K{1, x, y, xy} ≠ E`
   then `x` or `y` lies in `K` (if `x ∉ K` the span is `span{1, x}`; `y = a + bx` and `xy ∈ span{1, x}` force
   `bx² ∈ span{1, x}`, and `x` has degree 3 over `K`, `E` having no quadratic subfield over `K`, so `b = 0`); with
   three coordinates, two must lie in `K`. Hence any change `τ` of the weighted half's values that keeps the claims
   is completed, by `K`-values on the other half, into one that keeps `f¹(y)`, and the completion moves the rounds
   only along `e_{c_5}`.
2. **Forgetting `c_5`.** The completed change keeps the claims and `f¹`: its rounds lie in `H`. `c_5`'s coefficient
   in `lastMap` is `φ_5 + φ_5² ≠ 0` (a), so `H ∩ E·e_{c_5} = 0` and `π`, forgetting `c_5`, is injective on `H`, with
   `π(completed) = π(B(w, τ))`: the completion's `K`-coefficients, Frobenius-twisted functions of `φ` (the solution
   of a `K`-linear system with `E`-coefficients), are gone. This is what the previous design lacked: its
   completions moved every round, and their twist is why (R) could only be bounded through the `K`-coordinates.
3. **`β`.** A pattern weighs its lanes `v_g ∈ {0, 1}^64` by `μβ_i` at its entry `i`. Over `i` and over `K`-valued
   `τ ∈ ker v_g`, the `K`-span of `π(μβ_i·B(v_g, τ))` is the `E`-span of `π(B(v_g, ker_E v_g))`: from here
   everything is `E`-linear, and the reached space contains `Σ_g π(B(v_g, ker v_g))`.
4. **The lower patterns.** For a weight `w` and tables `τ` on the lower half, rounds 0 to 4 are those of the
   5-variable sumcheck of `Σ w·τ`, and `h_5(0) = s_5`, the running claim after round 4 (as `h_5(1) = 0`). *The
   sumcheck lemma*: for weights `w, w'` on `{0,1}^k` (one entry each) such that, for each round `j < k - 1`, `w`'s
   and `w'`'s `j`-folded tables have linearly independent halves (by variable `j`), and their `(k-1)`-folded lines
   are not proportional, every `(claim, messages) ∈ E × E^{2k}` is the sum of one of `w` against a table and one of
   `w'` against another; and with claims zero, every message vector (induction on `k`: tables `τ` with
   `fold_φ(τ) = 0` change only the claim and round 0, within the plane where `h_0(φ_0)` is unchanged, all of it when
   the halves are independent; lifts of the folded tables give the rest; base `k = 1`: two non-proportional lines;
   a claim is moved to zero along round 0). Pattern 0's `j`-folded weight has the two entries `eq(φ_{<j}, 0…0)` at
   `(0, 0…0)` and `eq(φ_{<j}, 1…1)` at `(1, 1…1)`: independent halves by (a); its 4-folded line is `(P, Q)`,
   `P = Π_{i<4}(1 + φ_i)`, `Q = Π_{i<4} φ_i`; pattern 1's is `(φ_0 Π_{1≤i<4}(1 + φ_i), (1 + φ_0) Π_{1≤i<4} φ_i)`.
   Proportional iff `(1 + φ_0)² = φ_0²`: never. So the lower patterns reach `{(r, ℓ(r)) : r ∈ E^10}`, `ℓ(r)` the
   running claim after round 4.
5. **The upper pattern.** Against a weight on the upper half, a table on the upper half has `h_5(0) = 0`, so `π`
   gives `(r, 0)`. Pattern 2 (the overflow lane, holding zero) against the unit table of lane 33: `ℓ(r) = s_5 =
   eq(φ_{<5}, 0)·eq(φ_{<5}, 1) ≠ 0` (a), the product of its 5-folded weight and table. With step 4,
   `(0, ℓ(r))`: all of `E^11`, so the reached space is `H`. ∎

`Pr[B]`: `λ = 0` has probability `2^-192`; some `φ_i ∈ {0,1}` at most `12·2^-192`; two of `φ_0, φ_1, φ_2` in `K`
at most `3·(2^64/2^192)^2`. **(S)** holds outside the same set: the random lanes `33 .. 40` are the cube `32 .. 40`
but its corner 32, and its three faces avoiding the corner give `c·φ_a·span_K{1, φ_b, φ_c, φ_bφ_c}`, so (S)
fails only if two of `φ_0, φ_1, φ_2` lie in `K`.

**Why these three patterns.** One entry's moves reach at most 10 of `H`'s 11 `E`-dimensions (its last round is a
product of two lines, so vanishes at the weight's root), so (R) needs two kinds of entries; patterns on one half
give `(r, ℓ(r))` only, so `h_5(0)` needs the other half; a lane weight of tensor rank one (one lane, or two
adjacent lanes) reaches 5 dimensions (its messages are values of `τ̃` along one staircase of points), the
complementary pair 9; two lower patterns must have distinct roots (the same pair mirrored in the upper half has the
same 4-folded line and stops at 10). Through the gadget's entries alone (`hiding.rs`): three patterns 33, any two
30, one lower 27, the upper one 9; at random challenges the data entries' (twisted) moves make up the rest with a
single lower pattern, which is how the previous design reached 33 without any guarantee.

## The exact checks

`src/hiding.rs`, in the real fields, with WHIR's own subspace polynomials:

- `model_matches_the_prover`: the model of (V1) is the real prover's, round for round (replaying a real opening's
  transcript with `verifier::Transcript`), with the gadget scaled as the prover does; the gadget weighs nothing of
  the stack; (V3) is the real committed codeword.
- `openings_hide_the_tables`: the whole view (V1)–(V3) as a `K`-matrix `M_R·r + M_D·d` on scaled-down layouts built
  by the same `Layout::hidden_with` (lanes of `2^8` in pieces of `2^4`, `D = 7`; the witness's claim shape on eight
  blocks and the masks' piece, the quotient's two claims, a generic point but its limbs and the sum's fixed point,
  on eleven blocks of four of its chunks; 40 lanes each; random challenges). It hides the table given the claims if
  and only if `rank [[M_R, M_D], [0, C]] = rank M_R + rank C`: equal for both with 3 and with `D = 7` opened
  positions, and an unopened row keeps `L - 3 = 37` elements. Without the gadget the view reveals the table.
- `round_freedom_predicts_the_exact_test`: with all or part of the gadget, the view reveals nothing exactly when
  (R)'s span is 33, and at most what it misses; through the gadget alone 33 / 30 / 27 / 9.
- `rounds_are_free_at_full_size`, and the review's `rounds_are_free_at_every_size` (`2^17` to `2^22` rows, eight
  draws each): on the real layouts at the reduction's own claim points, the gadget's entries alone give 33 and (S)
  holds; with sampled data entries too, 33; the data entries without the gadget reach at most 30.
- `rounds_are_free_for_every_challenge`: the argument's parts on both real layouts: (1) across the halves lanes
  meet only in `c_5`, for every lane pair; at challenges chosen against the argument but outside `B` (all but two
  of `φ_0, φ_1, φ_2` in `K`, all coordinates equal, alternating `x` and `1 + x`, `φ_4` at a pair's root), (2) the
  `E`-linear core exactly: each lower pattern reaches 9 dimensions of rounds 0 to 4 with `h_5(0)` its running
  claim, the upper one has `h_5(0) = 0` and a nonzero running claim, all together 11; (3) (R) itself, the `K`-span
  through the twisted completions: 33, and (S); (4) with two of `φ_0, φ_1, φ_2` in `K`, (S) fails.
- `review_hiding.rs`, `translation_holds_on_real_openings` (`2^17` rows) and `translation_holds_at_the_benchmark_size`
  (`2^22`, ignored, about 8 GB): the translation run with the real prover, (R) solved at the gadget's entries; the
  second table's opening is the first's byte for byte but the first level's root and siblings.

## How much randomness is necessary

- **The first piece**: the rows show each lane's codeword at `Q` separately, so every lane holding the table needs
  `|Q|` uniform values of its own there below `D`, and one more for an unopened row to keep any entropy (q < D
  strictly): `D = 247 > 225`, in the low coefficients (in a binary field the high ones are a subspace polynomial
  times something, and vanish on part of the domain). The first piece is 0.05% of `R1` and 0.006% of `R2`, against
  half of every lane in `membership-zk.md`.
- **`f¹`**: at every entry, random values whose fold weights span `E`: at least 3 random lanes; seven, the cube
  `32 .. 40` but the overflow lane's corner, make (S) fail only with two of `φ_0, φ_1, φ_2` in `K`.
- **The rounds**: the gadget, nine words a lane, two lane tensors. The previous design (a share lane holding a
  share `ρ` of the overflow lane's pieces, odd block lanes swapping piece pairs for a second in-lane weight, seven
  random lanes spread over odd lanes; HIDING.md at 875c9f6 has its exploration) reached the 33 dimensions with the
  data entries' moves, at random challenges only.

## Options rejected

- **leanVM's 4× padding** (the table in a quarter: half of each lane, half of the lanes): `R1` would fit
  (`2^24` words in `2^26`), `R2` would not: 59 lanes of `2^22` words in four times that is `2^29.9 > 2^28`.
- **2×, the table on even lanes only** (which handles round 0 without a share): at most 32 data lanes, `R2` has 55.
- **2×, the table in the high half of each lane** (random low halves): `R2` needs 118 lanes.
- **Splitting `R2` into commitments**: two (each at most `2^27` words of data on one parity, at `2^28`) or four
  (with the 4× padding). Each split adds a root to the calldata and the transcript (+64 bytes, a different contract,
  which must also not reveal the split), turns the quotient and sum claims into a claim per part (+2 `E`-values
  sent a part, partial evaluations that leak unless masked by more machinery), and adds a WHIR opening (~330 KiB).
- **More data-entry randomness** (random lanes, in-lane weights, shares): its moves at data entries are completed
  by `K`-values whose coefficients are Frobenius-twisted, so whatever their number (R) stays a condition on the
  `K`-coordinates of `φ`, bounded near `deg/2^64`; and solver lanes confined to `c_5` at data entries would need a
  half without data, which `R2`'s 55 blocks do not leave.
- **A gadget in one pattern, or in one half**: at most 10 of the 11 `E`-dimensions (above).
- **The gadget weighed with the first claim**: unsound (above).

## Parameters and their conditions

- `LOG_PIECE = 8`, `GADGET = 9`: `D = 247` against at most 225 first-level queries (`|Q| < D`, strict); at rate
  1/4 there would be 112.
- leanVM's WHIR: six lane folds first (bit 5, the last folded, separates the halves), no out-of-domain sample at the
  first commitment (an `eq` weight there would be a full tensor that also weighs the randomness), `LOG_INV_RATE = 1`.
- Lanes: blocks on `0 .. 32` and from 40, the overflow lane 32, random lanes `33 .. 40` (`L ≥ 40`); the gadget's
  pairs `(0, 31)`, `(1, 30)` and the overflow lane.
- The overflow lane holds its pieces: `H < 2^(ℓ-s)`. For `R1` (`H = 33`) this needs `ℓ ≥ 14`, so at least
  `2^17` rows (`protocol::MIN_LOG_ROWS`); the `PCS_OPEN` mock (`crates/evm/src/machine.rs`) knows layouts for
  `2^17` to `2^22` rows.
- The layout's id (`opening::layout_id`) encodes the gadget (its patterns' lanes and entries) where it encoded the
  share lane; a public layout's encoding, so the wiring table's prefix, is unchanged.

## The review's two attacks

- **Calldata alone** (`review_zk_calldata_only`): the four `a_j` still pin the twelve masks for a candidate witness
  (the test checks it for the true one), but `R1`'s root is now a Merkle root of rows that each hold
  `64·37` bits of padding the verifier never sees, so recomputing it from (cells, masks) confirms nothing: in the
  random-oracle model the root is independent of the witness but with probability `2·H·2^20·2^-2368`.
  `calldata_alone_does_not_confirm_a_witness`: the recomputed root matches for neither candidate, and the same
  cells and masks under another seed commit to another root. `R2`'s root (whose `q`, `q_G` depend on the masks
  and `h` on the cells) is hidden the same way.
- **Openings** (`review_zk_distinguish_and_unmask`): every lane, the masks' included, has a random first piece,
  and by the theorem the opening is the same for any two tables with the same claims, which are functions of the
  `a_j`; the masks are entries of the table like any other. `opened_rows_do_not_identify_the_witness`: no opened
  row of `R1` is a row of either candidate's commitment, and at the opened positions (223 distinct) the overflow
  lane's first piece below the gadget alone has full rank, so the masks' columns lie in its span: the rows say
  nothing of them.

## Cost (the membership benchmark, `2^22` rows)

Eight runs of each, alternating, on a machine under load (load average about 10); medians (minimum in brackets);
base `c004698` (the share design).

| | share design | gadget |
|---|---|---|
| reduction (commit both tables) | 1.76 s (1.69) | 1.80 s (1.60) |
| openings (three WHIR) | 0.88 s (0.81) | 0.88 s (0.84) |
| prover total | 2.71 s (2.52) | 2.68 s (2.47) |
| peak memory | 5.88 GiB | 5.80 GiB (5.67 to 5.89) |
| opening: witness / wiring / quotient | 247.1 / 278.6 / 333.8 KiB | 247.2 / 277.6 / 334.2 KiB |
| calldata | 248 bytes | 248 bytes |
| verify: openings | 5 ms | 5 ms |
| lane tensors (`R1` / `R2`) | 3 / 6 | 4 / 5 |

No difference beyond the noise: the stacks have the same lanes, the gadget's two tensors replace the odd lanes'
(one a claim), and the opened rows have the same width (the sizes move with duplicate queries). Against the plain
layouts (not hiding, `2e2d17d`), the hidden ones cost about +9% of prover time and +0.3 GiB, as before.

## What remains open

- Nothing of the theorem itself: its conditions hold outside `B`, by the argument above, checked in its parts
  exactly, and the Lean proof covers the deployed layouts at every supported size (`deployed_prEvent_le`, below).
- The Fiat–Shamir transfer (the roots, Merkle siblings, nonces and the programmable oracle) and the reduction's
  own hiding are now proved in Lean too (`formal/QuotientZk`, F1's honest-verifier zero knowledge), and end to
  end in the random-permutation model (`PcsQuotient.EndToEnd.zeroKnowledge_closed`, `formal/README.md`). That
  statement is single-proof: the distinguisher queries the permutation only after the proof, with no query
  before it and no second proof under the same permutation.
- The exact test of the whole view is on scaled-down layouts; at full size the Lean theorem is about
  `Layout::hidden_with` and `Table::hidden` as transcribed (`DeployedLayout.lean`, `hiddenWord_eq`): the
  transcription is read against the Rust, not proved equal to it.
- The model's padding is uniform; deployed it is ChaCha12 keyed from a 32-byte OS seed, so the hiding is
  computational in that generator. Side channels (timing, memory) are not considered; the padding is only as
  good as the seed.

## The Lean statement

Proven in `formal/QuotientSecurity/Hiding` (no `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`,
guarded in `Hiding.lean`):

- `Sumcheck.lean`, one entry (a column of the stack, tables on the 64 lane indices): `rounds_lower_upper` (the
  solvers: a weight on one half against a table on the other moves only the last quadratic coefficient),
  `last_fst_lower`, `last_fst_upper`, `lastClaim_upper` (the last round on each half), `kernel_move`,
  `two_weights_reach`, `two_weights_reach_zero` (the sumcheck lemma, by induction on the rounds), `reach_all`, and
  the bridge from a stack change on one entry to that entry (`laneRounds_column`, `laneRounds_smul_left`).
- `Gadget.lean`: `deployed_nd` (the pairs `(0, 31)`, `(1, 30)` are nondegenerate for every `φ` with no coordinate in
  `{0, 1}` and `2φ_0 ≠ 1`), `runClaim_move2`, `deployed_reach_all`, `piv_inj` (forgetting `c_5` is injective on
  `ker lastMap`), `reach_multiple` (the `β` entries and the twisted completions), `reach_table`, `column_reach`.
- `Solve.lean` (another agent): the solvers' span from the cube lemma (`hsolve_of_cube`, `span_cube_erase`: the
  eight eq-values of a cube of lanes span `E` unless two of `φ_0, φ_1, φ_2` lie in `K`, `E` having no quadratic
  subfield over `K`), and `prob_not_solvable_le`: `Pr[some φ_i ∈ {0,1} or two of φ_0, φ_1, φ_2 in K] ≤
  (12·|E| + 3·|K|²)/|E|²`.
- `GadgetLayout.lean`: the model of the layouts with the gadget (`GadgetLayout`: the weightless first entries
  `0 .. D`, the gadget's entries `gent p i` with the pairs' copies and the overflow lane's zeros, the random lanes,
  the overflow lane; `stackR`, `stackD`, `gadgetW`, `WeightsFit`, the gadget as the last claim `withGadget`), and
  **`GadgetLayout.roundsReached`: condition (R) for every `φ` with no coordinate in `{0, 1}`**, any claims, any
  `μ ≠ 0`, given the lanes the argument uses and the solvers' span; `claims_stackR` (the randomness weighs nothing in
  the claims nor in the gadget, characteristic 2), `combinedW_gent`, `onFirst_mem_range`, `foldSpans_moves`.
- `GadgetTheorem.lean`: **`GadgetLayout.view_evalDistEq`**, `HIDING.md`'s theorem for the gadget layouts at every
  challenge with `μ ≠ 0`, no coordinate of `φ` in `{0, 1}` and at most one of `φ_0, φ_1, φ_2` in `K` ((S) and (R)
  proven, (Q) a hypothesis), and **`GadgetLayout.prEvent_le_bound`**: averaged over uniform challenges, the two
  tables' experiments differ on any event by at most `Pr[μ = 0] + (12·|E| + 3·|K|²)/|E|²`.

- **The deployed layouts** (`DeployedLayout.lean`, `DeployedWeights.lean`, `NovelBasis.lean`, `Deployed.lean`):
  (Q) for WHIR's novel basis at the positions a level-0 opening reads (`|Q| ≤ 225 < D = 247`;
  `novel_firstEval_surjective`, after `Interp.lean`'s (Q) for a degree-graded basis), the witness and quotient
  layouts as `GadgetLayout`s at `2^17 .. 2^22` rows, `WeightsFit` for `opening::verify`'s weight closure, and
  **`deployed_prEvent_le`**: two tables with the same claims give experiments that differ on any event by at most
  `1/|E| + (12·|E| + 3·|K|²)/|E|² < 2^-188`. Nothing of this layer remains open.

The F2 mirror of the layouts (`formal/WhirBridge`:
`Layout.hidden`, `readHidden`, `HiddenOK`, `Layouts.lean`, the weight closure with the gadget's term, the layout id's
encoding) follows the gadget layout (`gadget_holds_iff`; `Test/Check.lean` accepts real proofs of both hidden openings
and rejects the honest proof checked without the gadget's term).
