<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# Option B: BLAKE2s proven without any sumcheck

**Question.** Can leanVM 42422001's BLAKE2s precompile, proved there by Flock (a zerocheck and a lincheck on
`q_flock`, then a ring switch), instead be proved like this repository's Keccak circuit (`crates/quotient`: a
gate on the cells of a row, a wiring permutation and a log-derivative copy argument, all as univariate
quotient identities at one random point), so that the PIOP has no sumcheck at all?

**Answer: not at the target size, nor at any of the baseline's sizes.** The verifier would be cheap: 4 to 35
scalars of calldata, about 10,000 gas of execution and 3 or 4 claims. But a quotient identity cannot read
packed bits. Every cell costs one committed 64-bit word, even a cell that holds one bit. BLAKE2s needs at least
15,616 bit-cells per compression, and at about 1M cycles there are `2^18` compressions, so at least `2^31.9`
words before any quotient. WHIR takes at most `2^28` words per commitment, and the baseline's whole proof
commits `2^26.68`. Every concrete design is between 4× and 200× worse than that lower bound. They fit up to
128, 4,096 or (ideally) 16,384 compressions; the 32-signature proof already has 6,489.

Measured vs modelled: everything here is modelled (counts and sizes). The verifier's share is modelled on the
measured `crates/evm` contract, which has the same structure. No EVM prototype was built: no instance fits, so
it would be the price of a proof nobody can make.

## What has to be proved

The interface stays leanVM's (`crates/leanvm_core/src/tables.rs`, `hash_flock.rs` at 42422001). A `BLAKE2S` row
pushes and pulls the state, reads its bytecode tuple and reads nine memory cells: the four 128-bit message
cells, the chaining value's and the output's two cells each, and the metadata cell. Their 18 64-bit lanes
`[a0..a3, b0..b3, c0..c3, cv0..cv3, md_lo, md_hi]` are virtual columns. In leanVM they are slots of `q_flock`.
The relation is one standard compression (`flock::hash::blake2s_compress`): `c = compress(cv, a‖b, counter,
f0, f1)`. It has 10 rounds of 8 `G` calls, each two three-operand and two two-operand 32-bit additions, four
XORs and four rotations (16, 12, 8, 7). leanerVM formalises the same circuit (mumbai `f0393df4`,
`Protocol/Blake2sCircuit.lean`, `Protocol/FlockSpec.lean`). Any option B would prove that relation, so
`blake2s_sound`/`_complete` would carry over to the cells.

Flock's encoding (`flock.rs`, `blake2s_row_values`) is the most compact one known. It uses `2^14` bit
positions per compression and materialises only the nonlinear bits: 31 carries per two-operand addition, and
61 per three-operand one (31 majority bits, then 30 ripple bits). That is `80 × 184 = 14,720` gate bits. The
896 input bits (`cv`, the message, the metadata) are free cells. Every XOR, rotation and output is a linear
form in those. So **any bit-level encoding has at least 15,616 = 2^13.93 cells per compression**.

Compressions per proof (the BLAKE2S table's rows, padded to a power of two): 6,489 (`2^13`), 25,881 (`2^15`),
80,825 (`2^17`), 260,605 (`2^18`) and 404,025 (`2^19`) for 32, 128, 400, 1,290 and 2,000 signatures.

## Why a quotient identity cannot use packed cells

1. **What a claim reads.** A univariate identity `C(f(X), f(X + δ), …) = Z(X) q(X)` holds on an evaluation
   domain `V`, and the verifier checks it at one random `t`. `f(t)` is a PCS claim only because the committed
   table is `f`'s coefficients in the novel basis. In the Cantor basis, a multilinear claim at the point
   `(w_k(t) / (1 + w_k(t)))_k` is `f(t)` up to a scale (`formal/`: `mle_eq_tablePoly_eval`). For bits on `V`
   those coefficients are general elements of `K = GF(2^64)`. So the table has one word per cell, whatever the
   cells hold.
2. **Committing the values instead** (`q_flock` packs 64 bits a word) makes `f(t)` equal to
   `Σ_j v_j L_j(t)` with `L_j(t) = Z_V(t) / (Z_V' · (t + p_j))`, since a linearised `Z_V` has a constant
   derivative. That weight is not a product over coordinates. No multilinear claim, weighted or not, evaluates
   it at a cost the verifier or `PCS_OPEN` can pay.
3. **Checking packed words pointwise** would need bitwise AND on `K`. In a basis, bit `i` of `x` is
   `Tr(δ_i x)`, a polynomial of degree `2^63`, so AND has degree `2^64` in the cells. The Frobenius route
   (Hashcaster) needs multilinear values: pointwise Frobenius of a multilinear table is a twisted multilinear,
   evaluated at a twisted point. On a univariate domain it is `f^(2^k)` of degree `2^k |V|`, unless `V` is a
   subfield, and then it is a permutation of the cells, not an evaluation. Multilinear values then need a
   zerocheck, which is a sumcheck.
4. **Subfields.** If the domain lies in `GF(2^32)` (the Cantor span of `β_0..β_31`), the coefficients do too.
   They pack two to a word, and a two-slice ring switch reads them. That is a factor of 2 (`2^30.9` at `2^18`
   compressions), and it needs a weighted claim.
5. **Limbs.** Addition mod `2^32` has no algebraic form in characteristic 2: no subgroup of `K^*` (odd order)
   or of `(K, +)` (exponent 2) is cyclic of order `2^32`. So a limb needs its carries as bits, or a lookup.
   - **logUp is unsound here.** It proves multiset equality only mod 2, because a multiplicity of 2 is 0. So a
     lookup needs a grand product: an `E`-valued running product (3 words per entry) and its quotient.
   - With byte limbs, the 480 32-bit additions per compression are 1,920 byte additions. Each costs at least its
     output limb plus about 3 words of product and quotient. That is `≥ 7,680 = 2^12.9` words per compression,
     `2^30.9` at `2^18`, before the nibble and bit splits that rotations by 12 and 7 need.

Spreading the cells over more commitments does not help either. The coordinator caps the proof at 2
commitments (the list-union margin). And `2^32` to `2^35` committed words would be 40 to 300 times the
baseline's prover: 2.59 s and about 15 GB for `2^26.68` words, measured on h1 for 1,290 signatures. That is
hundreds of GB of memory.

## Three designs, sized

All at one random point `t ∈ E = GF(2^192)`, with `≤ 2` proof commitments. Commitment 1 holds the witness.
Commitment 2 holds the quotients and copy helpers, drawn after the challenges. A fixed index commitment holds
the wiring and selectors, recomputable by anyone from the public circuit.

| design | cells / compression | words / compression (commitment 1 + 2) | fits `2^28` up to | 32 sigs (`2^13`) | 1,290 sigs (`2^18`) |
|---|---:|---:|---:|---:|---:|
| **B-ideal**: Flock's bit positions with every constraint local (fixed offsets) and one `K`-valued degree-2 quotient. A lower bound: no such layout of BLAKE2s is known, see below | 15,616 | `2^13.9 + 2^13.9` | `2^14` compressions | `2^26.9 + 2^26.9` | `2^31.9 + 2^31.9` |
| **B-word**: a word-level AIR, one row per 32-bit addition, holding its input and output words, the bits of both inputs and the 31 carries (≈ 100 cells), with a word-level copy argument for the data flow (≈ 6 word cells a row) and an `E`-valued row quotient | ≈ 48,000 | `2^15.6 + 2^15.1` | `2^12` | `2^28.6 + 2^28.1` | `2^33.6 + 2^33.1` |
| **B-plonk**: this repository's model, a 4-cell gate row, σ wiring and a log-derivative copy argument (sound here: every cell's identity is distinct, so multiplicities are 0 or 1) | ≈ 169,600 (42,400 rows) | `2^17.4 + 2^21.0` | `2^7` | `2^30.4 + 2^34.0` | `2^35.4 + 2^39.0` |

- **B-ideal is not reachable.** The constraints of a bit-level AIR on an additive domain reference cells at
  fixed XOR-offsets. Rotation by 16 is one (`i ↦ i ⊕ 16`). Rotations by 12, 8 and 7 are not: `π(i + r) =
  π(i) ⊕ δ` for every `i` forces `2r ≡ 0 mod 32`. Nor are `G`'s column and diagonal schedule or the message
  permutation. Each pattern then needs selectors or wiring.
  - A periodic selector, a coordinate of the cell index, is a linearised polynomial vanishing on a hyperplane,
    so its degree is `|V| / 2`. Several of them multiply the quotient.
  - Flock's own rows read linear forms with hundreds of terms (`blake2s_row_values` materialises no
    intermediate word). Without a sumcheck, checking `a = A z` needs either holography (Aurora/Marlin) or a
    walk over the matrix's nonzeros. Holography commits `A`'s sparse form over all instances. The bivariate
    Lagrange kernel of an additive domain does not factor over a block-diagonal `I ⊗ A0`, because the shift
    `X + w_j` couples instance and position.
- **B-word:**
  - Commitment 1: 480 rows of about 100 cells.
  - Commitment 2: the copy argument's `E`-valued `h` and quotient, 12 words per word cell, and a `3 × 480`-word
    row quotient.
  - Rotations are free, because a row holds the bits of the word it rotates. A word is `Σ x^i b_i` in the
    polynomial basis, so packing a word from its bits is linear.
- **B-plonk**: per `G`, 128 + 32 + 64 + 32 + 128 + 32 + 64 + 32 = 512 rows:
  - a three-operand addition is a majority row and an XOR row per bit, then a two-operand addition;
  - a two-operand addition is a majority gate and a three-input XOR per bit, selected by a public selector;
  - the XORs that feed the next addition are materialised;
  - the inputs, the IV constants and the 512 output XORs come on top.

  The quotient commitment holds the `E`-valued `h` (3 words a cell), the copy quotient (9) and the gate
  quotient (about 0.5), as in `quotient_layout`.

None fits at 32 signatures, the smallest baseline proof. B-word would fit a proof with at most 4,096
compressions, about 20,000 cycles of this aggregation guest. Hashing less, a program of about 1M cycles with
at most 4,096 BLAKE2s calls would fit. B-plonk fits 128 compressions.

## The verifier's share, if it fitted

The coordinator's linearisation rule applies:
- calldata carries only one factor of each product in the identities;
- every other evaluation of a committed polynomial goes into claims;
- per commitment, one scalar splits a batched identity whose terms span two commitments (its value on the
  witness side).

One further trick is specific to characteristic 2. Booleanity of many columns needs a single scalar, because
`Σ_k ρ^k b_k(t)^2 = (Σ_k ρ^(k/2) b_k(t))^2` (squaring is additive), where `ρ^(k/2)` is the Frobenius inverse.

| design | calldata scalars (24 B each) | execution, modelled | claims added | calls added |
|---|---|---:|---|---|
| B-plonk | 4: the cell `X(t)`, the gate's factor `Y(t)`, the wiring's `σ(t)`, the witness side of the batched gate identity (the repo sends 5) | ≈ 10,000 (the `crates/evm` membership contract is 14,289 with its three calls, the inversion and the public-bit weights) | witness 1, wiring 1, quotient 2 (identity, sum) | 1 (the wiring's fixed root) |
| B-word | ≈ 35: one factor per carry column (31), booleanity (1), the copy argument (2), the witness split (1) | ≈ 10,000 to 15,000 (≈ 100 column forms, 31 products, the copy identity) | witness 1, index 1, quotient 2 | 1 |

So B would add about 100 to 850 bytes of calldata (4,000 to 34,000 gas at 40 a byte) and about 10,000 of
execution. Flock adds about 4.8 KB (190,000 at 40 a byte) and, through the ring switch, about 170,000 of
execution (`crates/leanvm_flock_gas/README.md`). That gap is why option B was worth sizing. It cannot be had at
these sizes with WHIR on `K`-words.

## Soundness terms (B-word, for the sizes it fits)

- **Each quotient identity at `t`** errs with probability `deg/|E|`, at most `2^(log N + 2) / 2^192 ≈ 2^-161`
  for `N ≤ 2^28`.
- **The word-level copy argument**, as `crates/quotient`, has error `(2N^2 + 4N + words)/|E| ≈ 2^-135` for
  `N = 2^28`. It is sound in characteristic 2, because the cells' identities are distinct.
- **The batching challenges** (`ρ`, and the booleanity's square roots) add `(#identities)/|E|`.
- **Union bound.** Every challenge drawn after a commitment is union-bounded over that commitment's level-0
  Johnson list (≤ 323 at the code's parameters, ≤ 7,908 at leanerVM's: `review/whir_params.py`). That costs
  `log 7,908 ≈ 13` bits, so about 122 bits remain for the copy argument at `N = 2^28`. It needs `N ≤ 2^25`, or
  a second, independent copy challenge, to stay at 128 bits.
- **Lookups**, if any (none above), must be grand products. logUp is sound only mod 2.

## What would make B possible

- A commitment that reads packed bits through univariate evaluations. WHIR on `K`-words does not.
- Or a `PCS_OPEN` claim type that evaluates the Lagrange weight of item 2 at the opening's point. That is not
  multilinear, and a sumcheck would remain inside the precompile.
- Or fewer BLAKE2s calls per proof: B-word up to 4,096.

At leanVM's scale, the lever on BLAKE2s's gas is Flock itself: its calldata and its ring switch.
