<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# π2's PIOP: prover, verifier, contract, gas (SPEC-REC.md §7 R3)

**Status: R3 steps 1–3 done.** Branch `leanvm-rec-piop`, from `leanvm-rec` @ 0862503, with `leanvm-rec-circuit` (π2's
circuit, SPEC-REC.md §10) merged. Code in `crates/leanvm_rec/src/pi2/`. No formal proofs (the user's instruction).
Every number below is **measured** on h1 (AMD Ryzen 7 PRO 8700GE, 8 cores, 16 threads), unless marked modelled.

```sh
export RUSTFLAGS="-C target-cpu=native"   # the field's AVX-512/GFNI paths: without it the real prover takes 547 s, not 8.4 s
cargo test --release -p leanvm_rec --lib pi2                                                  # indicators, inverse, WHIR queries
cargo test --release -p leanvm_rec --test pi2 -- --nocapture                                   # synthetic circuits, contract parity
cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture real_gas            # the real circuits' gas
cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture real_end_to_end     # 2^24 prover, end to end (12 GB)
PI2_LAYOUT=d32v cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture real_end_to_end
cargo test --release -p leanvm_rec --test pi2 -- --ignored --nocapture gas_report               # the synthetic target shapes
```

## 0. Results

**The contract, on the real circuit** (D16v × π1-rec, from `main_line_rec.txt`), against SPEC-REC §6's model:

| | measured | SPEC-REC §6 (modelled) |
|---|---:|---:|
| calldata | 1,844 B (7 zero bytes) | 1,844 B |
| execution, `c = 0` | **39,674** | 41,421 |
| code | 17,654 B, one contract (deployment: 3.57M execution, 3.84M transaction) | |
| claims / calls | 9 / 8 | 9 / 8 |
| **EIP-7623, `c` = 0 / 2K / 5K / 20K** (no base) | **73,550** / 87,094 / 114,094 / 249,094 | 73,370 / 88,769 / 115,769 / 250,769 |
| with the 21,000 base, `c = 0` | **94,550** | 94,370 |
| EIP-7976, `c` = 0 / 20K | 118,016 / 249,094 | 118,016 / 250,769 |

At `c = 0` the transaction is EIP-7623's calldata floor (`40 · 1,837 + 10 · 7`); the standard price is 29,420 for the
calldata plus 39,674, 4.5K below it. Above `c ≈ 500` the execution and the claims bind.

**The fallback, D32v** (the real circuit, π1-rec or π1's main line: the same verifier):

| | straight | deployable (2 contracts, 24,519 + 7,973 B) | SPEC-REC §6 |
|---|---:|---:|---:|
| calldata | 2,228 B | 2,228 B | 2,228 B |
| execution, `c = 0` | 71,097 | 76,241 | 50,226 |
| EIP-7623, `c` = 0 / 2K / 5K / 20K | 106,649 / 124,649 / 151,649 / 286,649 | 111,793 / 129,793 / 156,793 / 291,793 | 88,670 / 103,694 / 130,694 / 265,694 |
| + 21K, `c = 0` | 127,649 | 132,793 | 109,670 |
| EIP-7976, `c` = 0 / 20K | 142,592 / 286,649 | 142,592 / 291,793 | 142,592 / 265,694 |

D32v's push side is 267 pairs in 228 groups (D16v: 120 in 66), its formulas about four times D16v's, as SPEC-REC §10.3
foresaw: 21K more execution than the model.

**The execution by phase**, real D16v (gas):

| phase | gas | | phase | gas |
|---|---:|---|---|---:|
| batched inversion (94 elements) | 6,997 | | the row's cells (fold) | 2,839 |
| public side (67 fractions) | 6,815 | | calldata reads | 1,494 |
| `PCS_OPEN`: 274 words, 8 calls | 5,705 | | identity and claims | 1,219 |
| indicators: 120 pairs' denominators | 5,309 | | the inversion | 1,217 |
| push formulas (66 groups) | 5,077 | | transcript (6 Keccak-256) | 1,156 |
| digits | 902 | | the blocks' vanishing polynomials | 898 |

925 `FIELD_MUL`s, 978 `XOR`s, 2 checks (the selector and length; one nonzero product).

**The prover** on the real witness (π1-rec's 1,000-signature proof), 16 threads, jemalloc:

| | D16v, `N = 2^24` | D32v, `N = 2^23` |
|---|---:|---:|
| `W` (transform, `B` coefficients, commit) | 0.12 s | 0.06 s |
| `h` on `V_m`, its coefficients | 0.39 s | 0.23 s |
| `q` on the extension coset (`4N` points), its coefficients | 6.12 s | 4.40 s |
| `Q` (`15N` words), commit | 1.69 s | 0.81 s |
| the values at `t` | 0.14 s | 0.07 s |
| **prove / open (3 WHIR openings)** | **8.4 s / 1.4 s** | 5.6 s / 0.7 s |
| the setup (`σ`, `κ`; once per circuit) | 0.7 s | |
| peak memory (the circuit's compilation included) | 11.7 GB | 6.9 GB |

SPEC-REC §7 modelled 5–8 s and about 3 GB beyond π1's prover.

**End to end** (`real_end_to_end`, both layouts): π1-rec's real proof → its circuit and witness → π2's proof → its
three openings verify (`quotient::opening::verify`, what `PCS_OPEN` checks) → the contract accepts, `PCS_OPEN`
attesting exactly its nine claims in eight calls (π1's five are the vector's inputs, which π1's openings prove) → 18
flipped calldata bytes (the public input, π1's roots and elements, `W`'s and `Q`'s roots, the values) each revert.

## 1. What π2 proves

`crate::circuit::spec` is the interface (SPEC-REC.md §10.1); `pi2::adapt` turns it into the PIOP's
`pi2::circuit::Circuit`:

- `N = 2^m` positions on `V_m`, rows of `2^r` (D16v `r = 4`, D32v `r = 5`); position `i` at `ω_i`.
- Every position pushes `(P(ω_i), σ(ω_i))`: `P = w + Σ_p I_p (E_p + w) + κ`, `I_p` the indicator of pair `p`'s coset
  (a (block, role) pair whose formula is not a forward), `E_p` its formula of the row's cells.
- Every position but the **holes** pulls `(w(ω_i), ω_i)`. A hole is a port's own position: its push goes to an outside
  tag `ω_{N+J}`, and no formula reads its value.
- The public side: for each port `J`, the verifier adds `1/(α + F_J + β ω_{N+J})`.

So the copy argument is: `h = (1 + 1_S)/(α + w + βx) + 1/(α + P + βσ)` on `V_m`, `1_S` the holes' indicator (the
sum of the port pairs'), and `Σ_V h = Σ_J 1/(α + F_J + β τ_J)`. The identity is
`h d_pull d_push + (1 + 1_S) d_push + d_pull = q Z_V`, of degree below `5N` (`1_S d_push` is below `4N`), so `q` is
below `4N` as in SPEC-REC §2.3. Both sides are sets of (value, tag) pairs: the pulls' tags are the non-hole positions,
the pushes' are `σ`'s values (injective), the public tags are outside `V_m`.

## 2. The protocol

**Transcript** (`KeccakChannel`): the seed `keccak(NAME ‖ IV ‖ public input)`, `NAME = "leanvm-rec-pi2v1"`, then the
stream:

1. the public data: π1's roots `C1`, `C2` (32 bytes each, as π1's calls take them: `PCS_OPEN`'s root words, §8), π1's
   claims' 51 distinct elements (24 bytes each);
2. `W`'s root; `α, β, γ`;
3. `Q`'s root; `t`;
4. the `2^r` fold values `a_k` and `ξ = κ(t) + β σ(t)` (17 values for D16v, 33 for D32v; §9 lever 2: until then also
   `σ(t)`, `κ(t)` apart and `h(t)`, 19 and 35); `ρ`.

The first challenge hashes the state and everything before it: the public data is bound there, not by a separate
`keccak(public data)`. The **IV** is `keccak("leanvm-rec-iv-v2" ‖ π1's contract IV ‖ the setup root ‖ the circuit's
digest ‖ the three layout words)` (`prover::iv`), a constant of the code.

**The tables.**

| table | content | variables | stack | basis |
|---|---|---:|---:|---|
| `W` | `w` | `m` | `max(m, 24)` | `B` (`B_k = Π_l (w_l or 1 + w_l)`) |
| `Q` | `h` (degree `< N`) and `q`'s four chunks, three limbs each: 15 chunks of `N` | `m + 5` (position, 2 digits, `h` or `q`, 2 limbs) | `m + 4`: 60 lanes of `2^(m-2)` | novel |
| setup | `κ` then `κ + σ` (§9; until then `σ` then `κ`) | `m + 1` | `max(m + 1, 24)` | `B` |

The stacks are at least `2^24` words, the smallest leanerVM's certified parameters cover; the query ladders of every
stack are pinned to `review/whir_params.py --large`'s (`stacks_take_the_certified_queries`). D32v's `W` (`2^23` words)
sits on a `2^24` stack, half its lanes absent. Small test circuits take `2^15` stacks.

**The verifier at `t`** (`verifier::reduce`, generic over `Scalar`):

1. the digits `w_0 … w_{m+2}`, `w_{l+1} = w_l² + w_l`;
2. the row's cells `v_c = w(t + ω_c) = Σ_k a_k eq(k, (w_l + ω_{c>>l})_{l<r})`, folding the top variable first:
   `r · 2^r` products;
3. the normalised block polynomials `Ẑ_s(t)`, `Ẑ_s = Ẑ_{s-1} + c_s Ẑ_{s-1}²`, so that
   `I_p(t) = w_m / (Ẑ_s(t) + Ẑ_s(c_p))`: `w_m` factors out of every indicator;
4. each group's indicators (pairs of one role, one formula) summed as one fraction `N_g / D_g`; the public side as one
   fraction `N / D`, its `β ω_τ` along a walk of the tags' bits;
5. (§9) the pushes' sum `A / B = Σ_g (N_g/D_g)(E_g(v_{c⊕k_g}) + v_0)` accumulated as one fraction (a one-pair group
   adds `X/d`, three products; a larger one `N_g X / D_g`, four), the pull-less groups' `S_n / S_d` likewise; then
   `P(t) = v_0 + w_m A/B + κ(t)`, `d_push = α + P(t) + βσ(t) = D_n / B` with `D_n = (α + v_0 + ξ) B + w_m A`,
   `d_pull = α + v_0 + βt`, `1_S = w_m S_n / S_d`;
6. the identity `h d_pull d_push + q w_m = (1 + 1_S) d_push + d_pull` at `t`, one combination of `h(t)` and `q(t)`:
   `Y = d_pull D_n + w_m B = B (d_pull d_push + w_m)`, `X = (S_d + w_m S_n) D_n + d_pull B S_d`;
7. one inversion, of `S_d Y · w_{m+2} · D` (required nonzero: it covers `t ∈ V_{m+2}`, every group denominator and the
   public side's), by the norm (two Frobenius maps from the limbs' shifts, 76 products); `1/w_{m+2}` from it, and
   `1/w_l = (1 + w_l)/w_{l+1}` down to `l = 0`.

**The claims** (4 in 3 calls, after π1's 5):

- `W` at `(ρ, ρ², …, ρ^{2^{r-1}}, w_r, …, w_{m-1})`, value `Σ_k eq(ρ⃗, k) a_k`;
- `Q` at `(u_0, …, u_{m+1}, ρ', y_0, y_1)`, `u_l = w_l/(1 + w_l) = 1 + 1/w_l + 1/w_{l+1}`, `ρ' = w_m B / Y` (the
  identity's `c_q/(c_h + c_q)`), value `s (t / w_{m+2}) X / (S_d Y)`, that is `(1 + ρ') h(t) + ρ' q(t)` (`(y_0, y_1)`
  and `s` the limbs' coordinates and scale, as `crates/quotient`; `Π (1 + w_l)^{-1}` telescopes to `t / w_{m+2}`); and
  at `(1^m, 0, 0, 0, y_0, y_1)`, `h`'s top coefficient `Σ_V h`, value `s T`;
- the setup at `(w_0, …, w_{m-1}, β)`, value `ξ` (its halves `κ`, `κ + σ`: `(1 + β) κ + β (κ + σ) = κ + βσ`).

**The contract** (`contract`): reads the stream, runs the verifier, then calls `PCS_OPEN` 8 times: π1's five (their words
`circuit::spec::Circuit::calls`: constants, the stream's roots, the elements read), then `W`'s (one claim), `Q`'s (two)
and the setup's (one; its root a constant). Layout words: π1's as the vector's; π2's `prover::layout_word` (§8).

## 3. The prover (`prover`)

1. `w`'s novel coefficients (`quotient::ntt`), its `B` coefficients (subset sums): `W`, committed.
2. `α, β, γ`; the pushes on `V_m`; `h` (one batched inversion a run of 4,096), checked to sum to the public target;
   `h`'s novel coefficients.
3. On `D = β_{m+2} + V_{m+2}` (`4N` points, disjoint from `V_m`): `w`, `σ`, `κ`, `h` by transforms. Eight points at a
   time (`quotient::ntt`'s AVX-512 lanes): the row's cells (`x + ω_c` stays in `D`), every pair's indicator (one batched
   inversion over the pairs), the formulas, `P`, `d_pull`, `d_push`, and `q = numerator / Z_V` (`Z_V` takes four values on
   `D`). `q`'s novel coefficients: `q` has degree below `4N`, so `4N` points determine it.
4. `Q`, committed; `t`; the fold values, `σ(t)`, `κ(t)`, `h(t)`; `ρ`; the verifier's claims, opened by `quotient::opening`
   (leanVM's WHIR unchanged, rate 1/2, the claims on one commitment in one opening).

## 4. Decisions and deviations from SPEC-REC

1. **Holes are pull-less, not summed** (SPEC-REC §10.4.2 adds the holes' sums `Σ 1/D(0, ω_h)` to the target). The
   identity's pull term carries `1 + 1_S`, `1_S` the sum of the port pairs' indicators, which the verifier has computed
   anyway; the holes' closed-form sums (one recursion and one fraction a coset) are not needed. A hole's value is then
   unconstrained: `adapt` checks that no formula of a port's region reads a hole (the circuit compiler never places a
   value there), and panics otherwise; since the review (L1) `Circuit::validate` is asserted on the setup path
   (`Spec::of`, `Setup::new`, `contract::Instance::new`) too. Same degree, same soundness argument, with one case to
   account for (REVIEW-REC.md N1): at a hole the identity reads `d_pull (h d_push + 1) = 0`, so if
   `α + w(x) + βx = 0` there, `h(x)` is free, and so is `Σ h`. `w` at a hole is committed in `W` before `α, β`: this is
   the vanishing-denominator event, at most `67 L_W / 2^192`, inside SPEC-REC §5's `4N/2^192` term.
2. **The ports' fingerprints are not `Σ γ^l L_l`.** Three limbs (an element, a zero check) are `L_0 + Y L_1 + Y² L_2`: the
   element itself, so the verifier's term is `α + x + βτ` with no product. Four limbs (the statement, a root) are
   `(L_0 + Y L_1) + γ (L_2 + Y L_3)`: a root's two 16-byte halves as `next_root` reads them, one product. Both bind the
   limbs (injective on `K³`; for all but one `γ` on `K⁴`), as `spec::Circuit::check` compares them.
3. **`h(t)` is sent** (`2^r + 3` values: 19 and 35, not 18 and 34). Otherwise `Q`'s claim needs `1/(d_pull d_push + w_m)`,
   computed after the indicators: a second inversion. With `h(t)` sent, `q(t)` follows from the identity and the claim
   combines them by `ρ`, drawn after.
4. **`W` and the setup in the `B` basis, `Q` in the novel basis.** The `B` basis makes a claim at the digits themselves
   (no inversion); `Q` needs the novel basis for `Σ_V h` to be one entry (the top coefficient), so its point takes the
   `u_l` (SPEC-REC §4 leaves the bases open; its `W` claim is the `B` basis's).
5. **The setup claim and the fold use `ρ`** (SPEC-REC: `ρ'` for the setup). Each claim is a polynomial of degree at most
   `2^r - 1` in `ρ`, on a commitment of its own: a union bound.
6. **The extension coset is `4N`**, not `8N`: `q` has degree below `4N`.
7. **The public data is in the stream**, absorbed by the first challenge, the statement in the seed (SPEC-REC: a
   separate `D = keccak(public data)`).
8. **67 public terms, no row counts** (SPEC-REC §10.4.3).
9. **Stacks of at least `2^24` words** at the target shapes (above).
10. **The verifier's arithmetic** (§2): normalised indicators, fractions by groups, the inverse by the norm. Measured on the
    synthetic D16v target: 56.3K → 46.2K execution.

## 5. The synthetic circuits (`synth`)

Before the real circuit existed, `synth` built circuits with every row kind of SPEC-REC §2.4 / §2.6 (χ formulas, D
units, XORs, packings, free bits, `E` products and sums, constants, ports of every source) and a witness satisfying them
by construction (FIFO wiring), small (`2^11`, `2^12` positions) and at the target shapes (`2^24` and `2^23`, 192 and 280
pairs). Their verifier's gas, for the record: D16v 46,220 execution, 75,640 at `c = 0`; D32v 67,544, 103,096. The real
D16v circuit has fewer pairs (120), hence 39,674.

## 6. Tests

- `lib`: an indicator is one on its coset and zero on `V_m`'s rest (every alignment and size); the inverse; the stacks'
  WHIR query ladders are the certified ones.
- `tests/pi2.rs`, D16v and D32v synthetic circuits and the interface's own example (padded, through `adapt`):
  - the honest proof's four claims hold on the tables and its three openings verify;
  - 24 witness mutations (random constrained positions), a changed element, a changed public input: a false claim;
  - 3 flipped stream bytes: claims the openings do not prove;
  - the contract equals the Rust verifier word for word, straight and deployable, on the honest stream and a random
    one; it accepts the honest proof with `PCS_OPEN` attesting exactly its calls, and rejects 3 flipped bytes.
- `tests/pi2_real.rs`, the real circuits: the gas and parity (straight, deployable) of D16v × π1-rec, D32v × π1-rec and
  D32v × π1; end to end as in §0, in both layouts.

## 7. Soundness (modelled; as SPEC-REC §5)

The rounds are SPEC-REC §5's, with:

- the copy argument `(α, β)`: as §5, the pulls over the non-holes;
- `γ`: the four-limb ports, degree 1;
- `t`: the identity, degree below `5N`, over `W`'s and `Q`'s lists (140.6 bits after the union, §5);
- `ρ`: `W`'s fold (degree `2^r - 1`), `Q`'s combination of `h(t)` and `q(t)` (degree 1), the setup (degree 1).

The review (R3 step 4, `REVIEW-REC.md`) found no attack; its fixes are §8. What remains: Lean for the virtual-push copy
argument and the composition.

## 8. The review's fixes (`REVIEW-REC.md`, branch `leanvm-rec-opt`)

- **M1, one `PCS_OPEN` ABI for the eight calls.** Every call is `machine.rs`'s `root word, layout word, k, k × (point,
  value)`:
  - every root word is `PCS_OPEN`'s, `s_0 · 2^128 + s_1` (`machine::root_word`: each 16-byte half of the hash
    reversed). π2's `W`, `Q` and setup roots were already; π1's `C1`, `C2` are now in calldata so (the circuit's root
    ports pack the stream's root bytes in that order, `circuit::compile`), and π1's setup roots `F`, `A0`, `B0` are
    constants so;
  - every layout word names its stack: π1's are `leanvm_univariate::contract::layout_word`'s (shape, code, variables,
    words placed); π2's are now `prover::layout_word`'s, in the same format (the tag `"pi2"`, `log_n`, the codes
    `0x5601` `W`, `0x5602` `Q`, `0x5603` setup, the variables, the words placed), instead of `quotient::opening::
    layout_id`'s hash. π2's IV hashes these words (`"leanvm-rec-iv-v2"`);
  - a precompile is a registry keyed by the layout word (`contract::registry`): π1's five layouts are opened by
    `leanvm_univariate`'s opening, π2's three by `quotient::opening`; `Q`'s two claims stay in one call (one opening).
  - The mock now decodes (`leanvm_flock_gas::evm::machine::{decode, PcsOpen::decoding}`): an input attests only if it
    decodes under the registry (a known layout word, which fixes the variables; `k ≥ 1`; the exact length; every
    element's top 64 bits zero) into a registered opening (the root as its opening has it, the layout word, the
    claims). The end-to-end tests register π1's openings from the vector's inputs (`contract::pi1_opening`) and π2's
    from the proof's roots and the reduction (`contract::openings`), so a call in another format fails them. The
    measuring runs use the decoding mock too (every well-formed call attested). No gas changes: the words are
    constants or calldata either way.
- **L1, the holes on the setup path.** `Spec::of` and `Setup::new` assert `Circuit::validate`, which now also requires
  `κ` zero off the expression slots. `tests/review_pi2.rs`'s E3b now checks that the forged circuit is refused.
- **L2, derived instances.** The circuit compiler takes the program's IV (`compile::Inputs::program_iv`) and derives
  π1's contract IV from the recorded verifier (`Recorded::iv`: its shape, setup roots and variant), kept as
  `Compiled::pi1_iv`. `contract::Instance::new` builds the instance from the validated circuit, its spec, the setup root,
  π1's IV and calls, and computes π2's IV.
- **N2, π1's IV binds its variant.** `leanvm_univariate::contract::contract_iv_for` appends `"fs-rec"`, the skip and the
  slices' code to the IV's preimage for every Fiat–Shamir shape other than `Main` (the main line's and its measured
  variants' IVs, and so their vectors and the Lean transcription, are unchanged). π1-rec's vector is regenerated:
  `main_line_rec.txt`, stream keccak `f32d7f4b6855f8fc…` (4.93 s, 10.4 GB; 181,019 / 191,296 gas as before).
- **N4, N5, text.** `review/leanvm_rec_params.py`: γ is the four-limb ports' fingerprint, degree 1 (177.1 bits after
  the union); ρ's errors add over the three commitments, `(15 L_W + L_Q + 1)/2^192`, 174.8 bits. SPEC-REC §2.4.6, §4,
  §5 and §10.4.2 and `circuit/spec.rs` say what is built; the commands take `RUSTFLAGS="-C target-cpu=native"`.

## 9. Optimisation levers (branch `leanvm-rec-opt`, toward 50K)

Measured on h1 by `tests/pi2_real.rs` (`real_gas`, `real_end_to_end`), the real circuit of π1-rec's 1,000-signature
proof; transaction gas without the 21,000 base, `c = 0`. Each row is one commit.

| lever | calldata | execution (D16v) | EIP-7623 `c = 0` | D32v execution | what |
|---|---:|---:|---:|---:|---|
| before (9d1bf46, and the review's fixes) | 1,844 B | 39,674 | 73,550 | 71,097 | |
| **2: π2's values 19 → 17**, one final inversion | 1,796 B | 35,787 | 71,630 | 61,659 | `ξ = κ(t) + βσ(t)` sent for `σ(t)`, `κ(t)`; `h(t)` not sent |
| **3a: the fold's siblings** | 1,796 B | 35,212 | 71,630 (floor) | 60,339 | `v_{2k+1} = v_{2k} + d`: 32 products, not 64 |
| **1a′: π1-rec2, the BLAKE2s circuit walked inside π2** | 1,292 B | 32,646 | **53,270** | | no claims on `A0`, `B0`: 51 → 30 elements, 5 → 3 calls |
| **3b: `PCS_OPEN`'s inputs reuse the region** | 1,292 B | 31,103 | **51,727** | 58,014 (π1-rec) | π1-rec: 35,212 → 32,916 |

**Lever 3b: the calls' inputs written once** (`evm_link::front::Source::reuse`, `codegen::Ending::PcsOpenReusing`).
The contract wrote every call's words to their own place, all before the first call: 274 words for π1-rec's 8 calls.
Now each call's input is written at the region's start just before the call, and only where the call before left
another word (a zero of fresh memory is not written either). π1's calls at the batch's point (`C1`, `C2`, `F`) write
`r` once; π2's calls are reordered `W`, the setup, `Q`, so the setup's point reuses `W`'s digits `w_4 … w_{m-1}`. The
node of a word written once is then read once, so it is not kept in a memory slot either. The parity build keeps the
words in place (it returns them all). Measured: `PCS_OPEN` 4,048 → 2,505 gas (π1-rec2), 5,492 → 3,196 (π1-rec, whose
`A0`, `B0` calls share three coordinates with `F`'s and each other's point).

**Lever 1a′: π1-rec2, the lincheck's terminal by the circuit's walk** (`leanvm_univariate::FLOCK_REC2`,
`flock_min::Slices::TowerWalk`; SPEC-REC §12 item 4). π1's `A0`, `B0` claims (28 coordinates, 19 of them outside the
batch's point, and 2 values) are what Flock's matrices' reduction leaves; π1-rec2 drops that reduction and checks the
lincheck's terminal as leanVM's own verifier does, by one walk of the BLAKE2s circuit on the sent slices
(`flock_min::walked_terminal`: `2^14` products for the column weights, `2 · 2^14` for the row sums, the walk's
additions). Too dear for a contract, it costs π2 positions instead:

- **π1-rec2** (measured, real 1,000-signature proof, `prove_real`'s `proves_and_verifies_main_line_rec2`): 6.3 s, 10.4 GB, the
  same prover but no matrices' tables; the stream 7,072 → 7,024 B (no `a`, `b`); 14 zero checks (the terminal's
  added); three claims (`C1`, `C2`, `F`), all at the batch's point `r`; vector `main_line_rec2.txt` (stream keccak
  `92d372ae4324f2c9…`). Its own contract would be 5.5M gas (the walk on chain): it is only for π2.
- **π2 on it** (`tests/circuit.rs`, `pi1_rec2_d16v`): still `N = 2^24`, now 15,880,064 positions used (94.7%, from
  85.7%), 992,504 rows (1,045,551 in blocks), 144 selector pairs in 66 groups (from 120), 47 ports (from 67), 107
  Keccak-f. `Q = 15N = 2^27.91` as before.
- **The contract**: 30 public elements (27 coordinates and 3 values) instead of 51, 6 calls instead of 8, 7 claims:
  1,292 B; execution 32,646 (the public side 6,794 → 4,723, `PCS_OPEN` 5,492 → 4,048; the indicators 4,686 → 6,134 for
  the 24 more pairs). EIP-7623 at `c = 0` **53,270**: the standard price binds now (`16 B + execution`; the floor is
  51,560), so execution counts from here on.
- **Soundness**: no new challenge; the batch combines 3 claims instead of 4 (its terminal no longer the matrices'); the
  openings are 6 (π1's 3, π2's 3): a plain union 128.97 − log₂ 6 = 126.4 bits (from 126.0).
- **The prover of π2** on the real witness: prove 7.9 s, open 1.3 s, 11.9 GB.

**Lever 3a: the fold's siblings.** At every level of the row's fold, the cells `2k` and `2k + 1` fold their parent at
`z = w_l + ω_{2k}` and `z + 1` (`ω_{2k+1} = ω_{2k} + β_0`, `β_0 = 1`), so the odd one is the even one plus the
parent's difference `p_j + p_{j+half}`: `r 2^(r-1)` products instead of `r 2^r` (D16v 32 instead of 64). Measured
2,967 → 2,331 gas for the fold. EIP-7623's floor binds here, so the transaction does not move yet.

**Lever 2.**

- **`σ(t)` and `κ(t)` as one value.** The verifier uses them only in `d_push = α + P(t) + βσ(t)`, `P` holding `κ(t)`:
  as `ξ = κ(t) + βσ(t)`. The setup's halves are now `κ` and `κ + σ`, so its one claim at `(w_0, …, w_{m-1}, β)` is
  `(1 + β)κ(t) + β(κ + σ)(t) = ξ`, with no inversion. The setup is honest (`L = 1`) and fixed before `β`: the claim
  binds `ξ` exactly. `ρ` no longer enters the setup's claim.
- **`h(t)` not sent.** §4.3 sent it to spare a second inversion. Now the verifier keeps every quotient as a fraction
  and inverts once at the end (§2, steps 5–7): the pushes' sum `A/B`, `d_push = D_n/B`, and the identity at `t` as the
  one combination of `h(t)` and `q(t)` it is, `c_h h + c_q q = (1 + 1_S) d_push + d_pull` (`c_h = d_pull d_push`,
  `c_q = w_m`). `Q`'s claim is that combination, normalised: `(1 + ρ')h(t) + ρ'q(t)` at `ρ' = c_q/(c_h + c_q)`. This is
  exactly the identity at `t`, so `t`'s error is unchanged (`5N` over `L_W L_Q`, 140.6 bits); `ρ` no longer enters
  `Q`'s claim either, and is only `W`'s fold (degree 15 over `L_W`: 174.8 bits). The one inversion is of
  `S_d Y · w_{m+2} · D`, required nonzero (it covers `t ∈ V_{m+2}`, hence every pair's denominator, and the public
  side's); the digits' inverses follow from `1/w_{m+2}` by `1/w_l = (1 + w_l)/w_{l+1}` (26 products instead of 81 in a
  batched inversion).
- **Measured:** the batched inversion (6,997 gas, 94 elements) is gone; the accumulation costs about as many products
  as the batch's prefix products did, and the digits' inverses a third. D32v, whose 228 groups dominated its inversion,
  falls by 9.4K. The prover: the same tables but the setup's halves; prove 10.8 s, open 2.0 s, 11.8 GB (the end-to-end
  run on the real witness, `real_end_to_end`).
- **D8v (rows of 8, 8 fold values: −192 B) is dropped.** With `Q = 15N` words, `N` must stay `2^24` (`2^25` gives
  `2^28.9`). At 107 permutations and π1's 0.36M other positions, a Keccak-f must fit in 153K positions, 17% more than
  D16v's 130,944. A χ output reads three `b = A + D` of its plane, so a row of 8 holds the inputs of at most two
  outputs, or must materialise `b` (one more position a state bit, and its forwards): about 2× D16v's positions a
  round, well past 153K.
