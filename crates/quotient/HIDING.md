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
weights), the claims and the contract are unchanged, and the prover is the memory-lean one (three lane tensors a
claim). The wiring table is public and keeps its plain layout.

## What is hidden

Notation: `K = GF(2^64)`, `E = GF(2^192)`; a stack has `L ≤ 64` lanes of `2^ℓ` words (`ℓ = log_n - 6`); `s =
LOG_PIECE = 8`; leanVM's WHIR folds the six lane variables first (`φ ∈ E^6`, lane `l` weighs `e_l = eq(φ, l)`),
opens the first commitment at a set `Q` of positions of its domain of `2^(ℓ+1)` points (222 to 225 queries at
rate 1/2, so `|Q| ≤ 225`), and takes no out-of-domain sample there.

**Theorem.** Fix the challenges of an opening. Let `T` and `T'` be two tables of a hidden layout on which every
claim of the opening has the same value. If

- **(Q)** `|Q| < 2^s`,
- **(S)** the fold weights `e_r` of the random lanes other than the share span `E` over `K`,
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

With the reduction's own masking (the `a_j` uniform given the statement and `t`, `next = σ(t)` public, so the
claims are functions of uniform and public values), the prover's whole output for one statement is the same for
any two witnesses. What is not
hidden: the statement, the circuit, the wiring table and its opening, the sizes.

**Assumptions.** Keccak-256 as a random oracle on the first commitment's rows; the transcript hashes as
programmable random oracles for Fiat–Shamir (the standard transfer, as in `membership-zk.md`, not redone here);
the masks and the padding seed are secret, uniform and fresh per proof, never reused (below); an honest verifier's challenges (conditions (S) and (R) are
on them, see "What remains open").

## The layout

`opening::Layout::hidden`, for a table that `Layout::new` would stack as whole blocks of `2^ℓ` entries plus the
tails of its chunks:

- **Every lane's first piece** (entries `0 .. 2^s`, the coefficients of the basis polynomials of degree below
  `2^s`) is uniform.
- **Block lanes** hold a whole block each: lane `l` holds its block's piece `k ⊕ (l mod 2)` at its piece `k ≥ 1`
  (odd lanes swap the pieces of each pair). It gives up the block's piece `l mod 2`.
- **The overflow lane** (`L - 2`) holds at its pieces `1 .. H` the pieces the blocks give up, then the chunks'
  tails (the masks' piece; for `R2` the three spills of `q`, 37 pieces each, and the gate quotient's 64 entries),
  each plus a share `ρ`; its pieces past `H` are uniform.
- **The share lane** (`L - 1`) is a random lane whose pieces `1 .. H` are `ρ`: the table's piece there is the sum
  of the overflow lane's and the share lane's.
- **The other random lanes** sit on odd lanes `2⌊k·P/(R-1)⌋ + 1`, `P = ⌊(L-2)/2⌋`, from lane 1 up.

| table | before | hidden | random lanes | stack |
|---|---|---|---|---|
| `R1` (witness, one claim) | 33 lanes | 32 blocks, overflow (33 pieces), 7 random: **40 lanes** | `WITNESS_RANDOM_LANES = 7` | `2^25` words, unchanged |
| `R2` (quotient, two claims) | 59 lanes | 55 blocks, overflow (167 pieces), 7 random: **63 lanes** | `QUOTIENT_RANDOM_LANES = 7` | `2^28` words, unchanged |

**The claims do not change.** A claim at `p` is the table's `eq(p, ·)` carried to the stack: `ω_l · eq(p_low, y ⊕
(l mod 2)·2^s)` on block lane `l` past its first piece (`ω_l = eq(p_high, block)`), `ψ_k · eq(p_{<s}, ·)` on piece
`k` of the overflow **and** share lanes (`ψ_k = eq(p_{≥s}, k-th held piece)`), zero elsewhere. The random entries
weigh nothing, and `ρ` weighs the same on both lanes, so it cancels (characteristic 2): every claim's value is
the table's. The weight is three lane tensors a claim (even blocks, odd blocks, overflow and share; a tensor that
is zero is left out), which is what `pcs::whir::recursive_prover_with_lane_tensors` takes, and the verifier's
closure costs `O(L + H·ℓ)` products a claim. `R1`'s and `R2`'s reductions, points, values, and so the EVM
contract, are those of the plain layouts.

**Soundness does not change**: the WHIR verifier is leanVM's, and the table a stack encodes is held on the same
blocks and pieces as before or fewer (the spills now take 37 pieces, not a lane), which `fits` checks.

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
parallel. Tests and the benchmark draw the proof's seed from `primitives::test_rng`.

## Why it hides

The view up to the first fold is `K`-linear in the stack: **(V1)** the six lane rounds, two `E`-values each,
`h_j(0)` and `h_j`'s quadratic coefficient, with
`h_j(X) = Σ_{l, l' agreeing above bit j} eq(φ_{<j}, l) eq(φ_{<j}, l') eq(X, l_j) eq(X, l'_j) ⟨W_l, T_l'⟩`;
**(V2)** `f¹ = Σ_l e_l T_l`; **(V3)** each lane's codeword at each `x ∈ Q`, `Σ_y T_l(y) X_y(x)` in the novel basis
(`X_y` of degree `y`). Let `Δ` be `T' - T` on the table's entries; it keeps every claim.

1. *Past the first pieces.* The weight vanishes on first pieces, so (V1) sees only the rest. At an entry `y` past
   the first piece, the random unknowns there (the random lanes; `ρ(y)`, of fold weight `e_O + e_S`, where the
   overflow lane holds the table; the overflow lane where it does not) span `E` by (S): pick a change of them
   that cancels `Δf¹(y)`. The change of (V1) left over keeps the claim (`Δ(h_0(0) + h_0(1)) = 0`) and the last
   round's value at its challenge, `h_5(φ_5) = Σ_y W̃(y, φ) f¹(y)`; those changes form a 33-dimensional `K`-space
   `H₁₁`. The changes of the random unknowns that keep `f¹` (the kernel of the fold at each `y`) move (V1) by
   `Σ_l W_l(y) Σ_u k_u Σ_{r ∈ u} pairing(l, r)`; **condition (R)** is that these span all of `H₁₁`. Then the
   leftover is cancelled too, and (V1) and (V2) past the first pieces agree.
2. *First pieces.* Each lane's codeword at `Q` changed by `M·Δhigh_l`. Polynomials of degree below `2^s` take any
   values on `|Q| ≤ 2^s` points, so a right inverse `N` of the first piece's evaluation at `Q` exists: change the
   first piece by `-N(M·Δhigh_l)`. Every opened row agrees, and `f¹`'s first piece changes by
   `-N(M·Σ_l e_l Δhigh_l) = -N(M·Δf¹_high) = 0`. (V1) does not see first pieces.
3. *An unopened row* `x ∉ Q`: with `|Q| < 2^s` (Q), some `u` of degree below `2^s` vanishes on `Q` and is 1 at
   `x`. Translating the first pieces by `c_l·u` with `Σ_l e_l c_l = 0` keeps (V1)–(V3) and moves row `x` by `c`:
   `L - 3` free `K`-elements.

**The exact checks** (`src/hiding.rs`, in the real fields, with WHIR's own subspace polynomials):

- `model_matches_the_prover`: the model of (V1) is the real prover's, round for round (replaying a real opening's
  transcript with `verifier::Transcript`), and (V3) is the real committed codeword.
- `openings_hide_the_tables`: the whole view (V1)–(V3) as a `K`-matrix `M_R·r + M_D·d` on scaled-down layouts
  built by the same `Layout::hidden` (`R2`: 55 blocks, the overflow, 7 random lanes, 63 lanes of `2^9`; `R1`: 40
  lanes of `2^8`; pieces of 4, 3 opened positions, both tables' claim shapes, random challenges). It hides the
  table given the claims if and only if `rank [[M_R, M_D], [0, C]] = rank M_R + rank C`: equal for both, and an
  unopened row keeps exactly `L - 3` elements (60 and 37). With 6 random lanes the view reveals the table; with as
  many opened positions as a first piece has entries it still hides it, but an unopened row has fewer left.
- `round_freedom_predicts_the_exact_test`: on those layouts, what the view reveals is exactly `33 - dim F`, `F`
  the span of condition (R), for 4, 6 and 7 random lanes: condition (R) is the whole story.
- `rounds_are_free_at_full_size`: condition (R) holds (`dim F = 33`) and (S) holds on the real layouts at `2^17`
  and `2^22` rows, at the reduction's own claim points (from `reduce` at random challenges) and random opening
  challenges, three draws each; with one random lane fewer it fails. `dim F` is computed at sampled entries, a
  lower bound that is exact once it reaches the maximum, 33.

## How much randomness is necessary

- **The first piece**: the rows show each lane's codeword at `Q` separately, so every lane holding the table needs
  `|Q|` uniform values of its own there, and one more for an unopened row to keep any entropy (q < 2^d strictly):
  a piece of `2^8 = 256 > 225`, in the low coefficients (in a binary field the high ones are a subspace polynomial
  times something, and vanish on part of the domain). That is 0.05% of `R1` and 0.006% of `R2`, against half of
  every lane in `membership-zk.md`.
- **`f¹`**: at every entry, random values whose fold weights span `E`: at least 3 random lanes. With exactly 3,
  `f¹` uses them all and nothing is left for the rounds (`dim F ≤ 27`).
- **Round 0's value at 0** is `Σ_{even l} ⟨W_l, T_l⟩`: no lane is paired with another there, so randomness of zero
  weight never reaches it, and it is the even lanes' share of the claim. Either every lane that holds the table
  has the same parity (leanVM's layout: at most 32 lanes of data, impossible for `R2`'s 55), or some randomness
  has weight and cancels in the claims: **the share**. Without it, `dim F ≤ 30`.
- **Rounds 1 to 5** see a random lane `r` only through `⟨W_l, R_r⟩`. If every block lane has the same in-lane
  weight, that is one `E`-number a random lane, and `F` stays below 33 for every count of random lanes that
  fits. Different in-lane weights on different lanes are new directions. `dim F` at `2^22` rows (witness /
  quotient; 33 is the maximum), the chosen row with the final layout, the others with an earlier variant whose
  share covered the overflow lane's first held piece only:

| in-lane weights on block lanes | 3 random | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|
| one (no permutation) | 3 / 3 | 12 / 12 | 15 / 18 | | | 27 / 30 |
| two (odd lanes swap piece pairs) — **chosen** | 6 / 6 | 15 / 15 | 21 / 24 | 27 / 30 | **33 / 33** | 33 / 33 |
| four (pairs and quadruples) | 12 / 12 | 30 / 30 | 33 / 33 | 33 / 30 | 33 / 33 | 33 / 33 |
| 64 (lane `l` XORs its pieces with `l`) | 18 / 27 | 33 / 33 | 33 / 33 | 33 / 30 | 33 / 33 | 33 / 33 |

  (A 30 between 33s is the placement's: with that many random lanes, the rule above puts them where they miss
  one direction.) Each in-lane weight is one lane tensor of `2^ℓ` `E`-values a claim for the memory-lean prover
  (100 MB at `R2`'s size), so two weights and 7 random lanes (3 tensors a claim) is the cheapest that hides: 64
  weights would need 4 random lanes but 64 tensors a claim (or the dense weight, 6 GB).

## Options rejected

- **leanVM's 4× padding** (the table in a quarter: half of each lane, half of the lanes): `R1` would fit
  (`2^24` words in `2^26`), `R2` would not: 59 lanes of `2^22` words in four times that is `2^29.9 > 2^28`.
- **2×, the table on even lanes only** (which handles round 0 without a share): at most 32 data lanes, `R2` has 55.
- **2×, the table in the high half of each lane** (random low halves): `R2` needs 118 lanes.
- **Splitting `R2` into commitments**: two (each at most `2^27` words of data on one parity, at `2^28`) or four
  (with the 4× padding). Each split adds a root to the calldata and the transcript (+64 bytes, a different contract,
  which must also not reveal the split), turns the quotient and sum claims into a claim per part (+2 `E`-values
  sent a part, partial evaluations that leak unless masked by more machinery), and adds a WHIR opening (~330 KiB).
- **Every lane its own in-lane weight** (4 random lanes): see the table; incompatible with the lane-tensor prover.

## Parameters and their conditions

- `LOG_PIECE = 8` against at most 225 first-level queries (`|Q| < 2^s`, strict); at rate 1/4 there would be 112.
- leanVM's WHIR: six lane folds first, no out-of-domain sample at the first commitment (an `eq` weight there would
  be a full tensor that also weighs the randomness), `LOG_INV_RATE = 1`.
- 7 random lanes, placed as above (checked exactly; the placement matters).
- The overflow lane holds its pieces: `H < 2^(ℓ-s)`. For `R1` (`H = 33`) this needs `ℓ ≥ 14`, so at least
  `2^17` rows (`protocol::MIN_LOG_ROWS`); the `PCS_OPEN` mock (`crates/evm/src/machine.rs`) now knows layouts for
  `2^17` to `2^22` rows (it knew `2^13` to `2^22`).

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
  lane's first piece alone has full rank, so the masks' columns lie in its span: the rows say nothing of them.

## Cost (the membership benchmark, `2^22` rows; median of 3; base `2e2d17d`)

| | base (not hiding) | hidden |
|---|---|---|
| reduction (commit both tables) | 1.359 s | 1.459 s |
| openings (three WHIR) | 0.667 s | 0.756 s |
| prover total | 2.034 s | 2.221 s (+9%) |
| peak memory | 5.58 GiB | 5.89 GiB (+0.31) |
| opening: witness / wiring / quotient | 234.1 / 279.3 / 326.4 KiB | 247.9 / 277.9 / 333.2 KiB |
| calldata | 248 bytes | 248 bytes |
| verify: openings | 5 ms | 5 ms |

The memory is the quotient table's stack and the half codeword its commitment encodes in, four lanes (`2^22`
words) more each, and the witness's coefficients, read back from the hidden stack where they are needed rather
than kept. The openings grow by the extra lanes in each opened row; the wiring's opening is the same up to
duplicate queries.

## What remains open

- Conditions (S) and (R) are polynomial conditions on the opening's challenges and the claim points. They are
  checked exactly at the reduction's own claim points for random challenges, at `2^17` and `2^22` rows, and never
  failed; for a fixed claim point, (R) is a polynomial of degree below `2^11` in the `K`-coordinates of `φ` and
  `λ`, so if it is not identically zero for that point it fails with probability below `2^-53`. That it is not
  identically zero for **every** point the reduction can output is not proven, only observed at random ones.
- The Fiat–Shamir transfer (programmable random oracle) and the reduction's own hiding are taken from
  `membership-zk.md` and the protocol's analysis, not redone.
- The exact test of the whole view is on scaled-down layouts; at full size the argument rests on the steps above
  and the exact check of (R) and (S).
- Side channels (timing, memory) are not considered; the padding is only as good as the seed.
