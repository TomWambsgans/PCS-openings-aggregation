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

1. the public data: π1's roots `C1`, `C2` (32 bytes each, as π1's calls take them), π1's claims' 51 distinct elements
   (24 bytes each);
2. `W`'s root; `α, β, γ`;
3. `Q`'s root; `t`;
4. the `2^r` fold values `a_k`, `σ(t)`, `κ(t)`, `h(t)` (19 values for D16v, 35 for D32v); `ρ`.

The first challenge hashes the state and everything before it: the public data is bound there, not by a separate
`keccak(public data)`. The **IV** is `keccak("leanvm-rec-iv-v1" ‖ π1's contract IV ‖ the setup root ‖ the circuit's
digest ‖ the three layouts' ids)` (`prover::iv`), a constant of the code.

**The tables.**

| table | content | variables | stack | basis |
|---|---|---:|---:|---|
| `W` | `w` | `m` | `max(m, 24)` | `B` (`B_k = Π_l (w_l or 1 + w_l)`) |
| `Q` | `h` (degree `< N`) and `q`'s four chunks, three limbs each: 15 chunks of `N` | `m + 5` (position, 2 digits, `h` or `q`, 2 limbs) | `m + 4`: 60 lanes of `2^(m-2)` | novel |
| setup | `σ` then `κ` | `m + 1` | `max(m + 1, 24)` | `B` |

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
   fraction, its `β ω_τ` along a walk of the tags' bits;
5. one inversion of every `D_g`, the public side's denominator and the digits, by the norm (two Frobenius maps from the
   limbs' shifts, 76 products);
6. `P(t) = v_0 + w_m Σ_g (N_g/D_g)(E_g(v_{c⊕k_g}) + v_0) + κ(t)`, `d_pull = α + v_0 + βt`,
   `d_push = α + P(t) + βσ(t)`, `1_S = w_m Σ_{port groups} N_g/D_g`, `q(t) = ((1 + 1_S) d_push + d_pull + h(t) d_pull d_push) / w_m`.

**The claims** (4 in 3 calls, after π1's 5):

- `W` at `(ρ, ρ², …, ρ^{2^{r-1}}, w_r, …, w_{m-1})`, value `Σ_k eq(ρ⃗, k) a_k`;
- `Q` at `(u_0, …, u_{m+1}, ρ, y_0, y_1)`, `u_l = w_l/(1 + w_l) = 1 + 1/w_l + 1/w_{l+1}`, value
  `s (t / w_{m+2}) ((1 + ρ) h(t) + ρ q(t))` (`(y_0, y_1)` and `s` the limbs' coordinates and scale, as `crates/quotient`;
  `Π (1 + w_l)^{-1}` telescopes to `t / w_{m+2}`); and at `(1^m, 0, 0, 0, y_0, y_1)`, `h`'s top coefficient `Σ_V h`,
  value `s T`;
- the setup at `(w_0, …, w_{m-1}, ρ)`, value `(1 + ρ) σ(t) + ρ κ(t)`.

**The contract** (`contract`): reads the stream, runs the verifier, then calls `PCS_OPEN` 8 times: π1's five (their words
`circuit::spec::Circuit::calls`: constants, the stream's roots, the elements read), then `W`'s (one claim), `Q`'s (two)
and the setup's (one; its root a constant). Layout words: π1's as the vector's; π2's `quotient::opening::layout_id`.

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
