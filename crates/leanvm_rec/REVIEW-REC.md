<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# Adversarial review of π2, the recursive EVM verifier of leanVM 42422001 (R3 step 4)

**Scope.** Branch `review-rec`, from `leanvm-rec-piop` @ 9d1bf46:

- `SPEC-REC.md` §2.3, §2.4, §4, §5, §10, §11 and `PI2.md` §4;
- `src/circuit/` and `src/pi2/`;
- π1-rec's Fiat–Shamir shape: `leanvm_univariate`'s `reduce`, and `leanvm_flock_gas`'s `flock_min` and `transcript`.

**The goal** was to make the contract accept while one of π1's `PCS_OPEN` claims is false, or while π1's verifier
rejects. A second goal was to find any way the statement differs from "π1 is an accepting π1-rec proof of leanVM
42422001's relation". There are no formal proofs here: experiments and arguments only. All runs were on h1, under
`/root/pcs-quotient-fv/review-rec/`.

**Verdict: no attack found.** There is no critical or high finding. One medium finding is about deployment, not
soundness: the eight `PCS_OPEN` calls use two input formats. Three low findings are setup hazards and test coverage.
The rest are notes. The central question is whether the virtual-push copy argument and the compiled circuit really
compute π1's verifier. The answer is yes:

- **Free inputs (E1).** In the real circuit, the only free inputs the ports depend on are the stream's and the public
  input's bits (`b = b²`) and the 15 limbs that are never hashed. Every other cell the ports read is determined
  acyclically, and it is a bit wherever a bit formula reads it. This holds for every satisfying witness, in both
  layouts.
- **Ports (E2).** On mutated and random streams, the ports carry exactly π1's graph evaluated on that stream.
- **Graph (fork test).** That graph is π1-rec's Rust verifier on random streams.

## Findings, most severe first

### M1 (medium, deployment). The eight `PCS_OPEN` calls use two input formats, and the byte-string mock hides it

**What.** π1's five calls and π2's three follow different families.

| | π1's five calls | π2's three calls |
|---|---|---|
| family | `leanvm_univariate`'s | `quotient::opening`'s, `crates/evm`'s ABI |
| root word | the raw hash (π1's prover writes each half big-endian, `leanvm_univariate/src/prover/prove.rs:102`) | `root_word(h)`, each 16-byte half byte-reversed (`pi2/contract.rs:93`, as `evm/src/machine.rs:95`); W's and Q's stream bytes are this encoding, and so is the setup's constant |
| layout word | structured: shape bytes, code, vars at byte 24, placed words at 25..32 (`leanvm_univariate/src/contract.rs:91`) | `layout_id`, a Keccak hash of the layout |
| checked by | `leanvm_univariate::prover::opening::verify`, label `leanvm-univariate-op` | `quotient::opening::verify`, label `pcs-quotient-opening` |
| claims per call | one | one, two (`Q`), one |

The mock (`leanvm_flock_gas/src/evm/machine.rs:88-95`) attests raw byte strings and decodes nothing. So "`PCS_OPEN` =
`opening::verify`" holds per family, and no test runs one precompile on all eight calls.

**Impact.**

- **Soundness is not affected.** In both families the root bytes are bound by the transcript before any challenge,
  and any fixed injective decoding keeps them bound.
- **At deployment:**
  - a precompile with one decoding rejects one of the two honest families;
  - `layout_id` is a hash, so a real precompile needs a registry of π2's three layouts;
  - if π2's `Q` went to a one-claim-per-call precompile like π1's, split into two calls, that is AGENTS.md's
    separate-openings forgery (about 2^111 work). `Q`'s call must keep its two claims together.

**Fix.**

- Specify `PCS_OPEN` as a registry keyed by the layout word, with each family's root encoding, label and claim count.
- Or move both families to one ABI: open π1 under `quotient::opening`, or have the contract byte-reverse π2's root
  words as `crates/evm`'s `reverse_halves` does.
- Replace the byte-string mock in the end-to-end tests with a decoding mock that runs the right verifier per call.
  `tests/review_pcs_contract.rs`'s `decode()` already does this for π2's three calls: decoded as `crates/evm`'s ABI,
  they verify under `quotient::opening::verify`, and `Q`'s call carries k = 2.

### R1 (follow-up to M1, completeness). π1's stream carried its roots as hashes, which its contract passed as root words

*Found after M1's fix, by the Lean composition (`formal/RecStatement`, `formal/RecCircuit`): the root π2's call names
for `C1` (`rootOfWord (pcsWord …)`, `digestOfBytes32 raw`) was not the root π1-rec3's verifier opens
(`UniStatement.rootOf (halves raw)`, `raw` the stream's 32 bytes). Fixed on branch `fix-pi1-root`.*

**What.** Three readings of π1's 32 stream bytes `raw` for `C1` (and `C2`) disagreed:

| | the root they name |
|---|---|
| π1's prover (`prove::halves`, before) | `raw` is the hash `h` as it is; its WHIR opening's first two scalars are `hash_to_scalars(h)` |
| π1's verifier, contract and `formal/UniStatement` (`rootOf (halves raw)`) | `raw` is the root word: its two big-endian halves are the opening's first two scalars, so the root is `root_word(raw)` |
| π2 after M1 (`root_word(raw)` in calldata) | `raw` is the hash: right for the prover's commitments, not what π1's own contract or its Lean statement say |

On the real π1-rec3 proof: `C1`'s commitment is `f30c504d…b05f` (its WHIR opening's first two scalars are that hash's);
the stream carried `f30c504d…b05f`; π1's contract passed it as the word, which `machine.rs` decodes to the root
`b25c056f…cef8`, a root nobody committed; π2 passed `b25c056f…cef8`, which decodes to `f30c504d…b05f`.

**Impact.** Soundness: none (every reading is a fixed bijection of bound bytes). Completeness at a real precompile:
π1's own contract asked to open `C1`, `C2` at roots that were not their commitments. π2's calls were right for the
prover's commitments, but then π2 did not make π1's contract's calls (the composition's statement), and its tests could
not tell: the vector's `pcs_open` lines were π1's contract's words (byte-string mock), which `pi1_opening` reinterpreted.

**Fix** (at the source: π1's prover streams what its verifier reads):

- `leanvm_univariate::prover::prove::halves` sends a root as its two WHIR scalars (`hash_to_scalars`), as π2's prover
  sends `W` and `Q`: the stream's 32 bytes are the root word, `root_word(h)`. π1's contract's `C1`, `C2` words then
  decode to the commitments, and `UniStatement.rootOf (halves raw)` is the commitment, unchanged.
- π2's circuit packs a root's limbs from the stream's bytes as they are (`circuit::compile`, big-endian words of bytes
  `24 − 8l`), and its calls pass π1's stream root words as π1's contract does; a setup root's word stays
  `root_word` of the hash π1's contract holds. π2's calldata carries the same words as before.
- π1's setup roots: π1's own contract still holds `F`, `A0`, `B0` as hashes and passes them as its root words, which
  `machine.rs` reads as other roots. π2 is not affected (it passes `root_word(F)`); π1's contract deployed alone needs
  `Word::Const(root_word(..))` (free), and `formal/RecGraph`'s emitted graph and `UniStatement`'s reading of the
  setup's constant would follow.

**Tests.** The vectors record each call's committed root (`whir_root`, from the prover's output: each opening's root,
whose `hash_to_scalars` `prove_real` checks are the WHIR opening's first two scalars). `prove_real` checks that π1's
contract's `C1`, `C2` words decode to them; `tests/circuit.rs` (every vector, every layout) that π2's calls decode to
them and that the pre-R1 word (`root_word` of the stream's word: the hash as it is) names another root; `real_end_to_end`
registers π1's openings on them (`contract::pi1_opening(input, root)`), and checks that the pre-R1 words are not
attested and that π1's openings on the other roots make the contract reject.

### L1 (low, setup hazard). Nothing on the verifier's side guarantees that no formula reads a hole

**What.** PI2.md §4.1 leaves the holes (the ports' own positions) out of the pulls. A hole's value is then
unconstrained, which is safe only if no formula reads one. Two checks enforce that, and neither is on the
construction path:

- `adapt` (`pi2/adapt.rs:83-93`), at circuit construction;
- `pi2::circuit::Circuit::validate` (`circuit.rs:397-467`, rows 451-465), which only `Circuit::check` calls, in
  tests.

`Spec::of`, `Setup::new`, `prover::iv`, `contract::record_verifier` and `contract::compile_verifier` take any `Circuit`.
`validate` also does not check that `κ` is zero off expression slots, which `spec::Circuit::check_shape` does check.

**Attack (E3b, `tests/review_pi2.rs::review_hole_read_is_forgeable`).** Take the interface's example, padded to
`2^11`. Change the port's fingerprint to read its own position (the hole) for limb 0, building the PIOP's `Circuit`
directly as `adapt` would refuse to; `validate` rejects this circuit. Put a forged limb in the hole and the forged
element in the public data. The proof's four claims hold and its three openings verify: the verifier accepts a public
element the circuit never computed.

**Impact.** None for the circuit `adapt` builds today: `pi2_real::real_end_to_end` runs `check`, hence `validate`, on
the real adapted circuit. The risk is a future circuit built or edited without `adapt`, or a change to `adapt`'s
check. The verifier, the IV and the contract would accept it silently.

**Fix.**

- Make `validate` part of the setup: `Setup::new` or `Spec::of` asserts `circuit.validate()`. It is `O(N)`, done once
  per circuit.
- Add `κ = 0` off expression pairs to `validate`.
- Better still, build `Instance` and the IV only from a validated circuit (see L2).

### L2 (low, setup hazard). π1's contract IV and π2's `Instance` are unchecked parameters

**What.**

- `compile::Inputs::iv` (`compile.rs:61-66`) becomes κ constants in the circuit's seed call (`compile.rs:212-216`).
  Nothing ties it to:
  - `contract_iv(&recorded.shape, PROGRAM_IV, &recorded.roots)`, which binds the setup roots that π1's call words take
    as constants;
  - the `pi1_iv` that `prover::iv` hashes (`prover.rs:133-147`).
- `contract::Instance { spec, iv, setup_root, pi1 }` (`pi2/contract.rs:31-36`) is likewise assembled by hand. Nothing
  checks that `iv` was derived from `setup_root`, the circuit's digest and the layouts.
- π1's own contract derives its IV from `recorded` (`leanvm_univariate/src/contract.rs:241-245`). π2's path loses
  that.

**Experiment** (`tests/review_fs_statement.rs`, the ignored test). Compile under another IV: σ is unchanged and κ
changes in 103 entries. So the IV lives in κ only, which the circuit digest and the setup root bind. The deployed
artifact is consistent, but only by the deployer's care.

**Impact.** A mis-deployment could compile π1's seed with one setup (one F, A0, B0, or one shape) while π1's claims
go to `PCS_OPEN` against another. That loses review M1 F2's property that π1's transcript binds the setup its claims
are checked against. A prover cannot cause this against an honest deployer.

**Fix.**

- `compile` takes the program IV and derives `contract_iv` from `recorded`, or asserts equality.
- One constructor builds `Instance` from the validated circuit, the setup and π1's IV, and computes `iv` and
  `setup_root` itself.

### L3 (low, test coverage). Repository tests compared semantics on the honest inputs only

**What.**

- `tests/circuit.rs` compares digests and limbs with `eval::evaluate` on the honest stream only. On a flipped byte it
  asserts only `Failure::Public`.
- Contract parity ran on the honest stream and one random stream (`tests/pi2.rs:327-333`,
  `tests/pi2_real.rs:208`).
- The verifying build's `PCS_OPEN` marshalling was exercised on honest streams only.

**Impact.** No bug found: the review's tests below cover all three in both layouts. The gap could hide a circuit
whose formulas agree with the graph only on the real proof.

**Fix.** Keep these tests, and run the first two in CI:

- `review_circuit::review_mutated_streams` (7 streams, about a minute a layout);
- `review_pcs_contract` (every calldata region; 18 s);
- `review_circuit::review_free_inputs` (10 s a layout).

### N1 (note). π2 proves `spec::Circuit::check`'s (1), (2) and (4), not (3); the interface's documentation describes the superseded target

**What.** With pull-less holes, a hole holding garbage is accepted (E3,
`tests/review_pi2.rs::review_hole_is_unconstrained`). `spec::Circuit::check` rejects that witness with
`Failure::Hole`; π2 accepts it with all four claims holding and the openings verifying. This is harmless while L1's
property holds. These texts still state the relation with holes of value 0 summed into the target:

- `circuit/spec.rs:21-30`, the module's "what holds" item (3) and "the copy argument this is";
- `SPEC-REC.md` §10.4.2;
- `SPEC-REC.md` §2.4.6's "their pulls (0) are in the target too".

**A case to account for** (with the PCS fork). At a hole the identity reads `d_pull · (h·d_push + 1) = 0`. If
`α + w(x) + βx = 0` there, `h(x)` is free, and so is `Σ h`. `w` at a hole is committed in `W` before α and β, so this
is the vanishing-denominator event: at most `67 · L_W / 2^192`, inside SPEC §5's `4N/2^192` term.

**Fix.** Rewrite `spec.rs`'s copy-argument statement as the pull-less one (PI2.md §1), with `Failure::Hole` marked
stronger than the PIOP. Name the hole case in PI2.md §4.1's soundness sentence.

### N2 (note). π1's contract IV does not bind the Fiat–Shamir shape or the Flock variant

**What.** `contract_iv` (`leanvm_univariate/src/contract.rs:115-127`) hashes:

- the program IV;
- F, A0, B0;
- the shape and the layout words.

It does not hash `FsShape`, the skip or the slices. So the main line's and π1-rec's contracts for one shape share a
seed: the hash that gives π1-rec's β is the main line's α_2.

**Impact.** No break. Each verifier is sound on its own in the random-oracle model, and the vectors show each contract
rejects the other's proof.

**Fix.** Hash the variant into `contract_iv`. It costs no gas, but changes π1-rec's vector.

### N3 (note, inherited from leanVM). Seven fixed zerocheck coordinates are not in SPEC §9's count

**What.** leanVM's zerocheck has 7 fixed coordinates (`flock.rs:38-50`) before the 22 drawn ones. π1-rec derives only
the 22, after the 7. So π1-rec adds no new interaction.

**Impact.** It inherits leanVM's unstated assumption: the 128 fixed eq weights on those 7 variables must not cancel a
nonzero bit-valued constraint vector.

**Fix.** State the assumption, or check it, in SPEC.md §9.

### N4 (note). Stale or loose text

- **`review/leanvm_rec_params.py` describes γ's fingerprint as `c0 + γc1 + γ²c2` (≤ 128).** As built (`adapt.rs:24-35`):
  - three-limb ports are the element itself, with no γ;
  - four-limb ports are degree 1 in γ.

  The modelled bound is conservative.
- **SPEC §5's ρ line (160.9 bits) multiplies the lists.** ρ's claims are on three separate commitments, so their errors
  add: `(15·L_W + L_Q + 1)/2^192` gives about 174.8 bits. The line also does not say that ρ is reused for the setup
  claim (PI2.md §4.5 does).
- **SPEC §2.4.6's fingerprint** `c₀ + γc₁ + γ²c₂ (+ γ³c₃)` and **§4's** `D = keccak(public data)` are superseded by
  PI2.md §4.2 and §4.7.
- **SPEC §4's π2 IV** (`"leanvm-rec-iv" ‖ π1's IV ‖ setup root ‖ shape ‖ layout words`) is, as built,
  `"leanvm-rec-iv-v1" ‖ π1's IV ‖ setup root ‖ circuit digest ‖ the three layout ids` (`prover::iv`).

**Fix.** Update the text.

### N5 (note, reproducibility). PI2.md's prover timings need `-C target-cpu=native`, which its commands omit

**What.** I ran `real_end_to_end` with PI2.md's command line, on the same h1, built without `RUSTFLAGS`. Prove took
547 s and open 91 s, against PI2.md's 8.4 s and 1.4 s.

| step | this run | PI2.md |
|---|---:|---:|
| `W` | 4.5 s | 0.12 s |
| `h` | 14.4 s | 0.39 s |
| `q` on the coset | 464 s | 6.12 s |
| `Q` | 49.7 s | 1.69 s |
| the values | 15.0 s | 0.14 s |

Peak memory was the same, 11.7 GB. A uniform slowdown like this is the generic field arithmetic, without the
AVX-512/GFNI paths that `primitives` gates on `target_feature`. `leanvm_univariate`'s README and PROVER.md state
`RUSTFLAGS="-C target-cpu=native"`.

**Fix.** Add the flag to PI2.md's and SPEC-REC's command lines, or to the workspace's `.cargo/config.toml` as leanVM
does.

## The experiments

The review's tests are in `crates/leanvm_rec/tests/review_*.rs` and `review/review_fs_powers.py`. All of them pass on
h1.

```sh
cargo test --release -p leanvm_rec --test review_circuit -- --ignored --nocapture --test-threads 1   # E1, E2 (D16v)
REVIEW_LAYOUT=d32v cargo test --release -p leanvm_rec --test review_circuit -- --ignored --nocapture --test-threads 1
cargo test --release -p leanvm_rec --test review_pi2 -- --nocapture                                  # E3, E3b
cargo test --release -p leanvm_rec --test review_pcs_contract -- --nocapture                         # calldata regions
cargo test --release -p leanvm_rec --test review_fs_statement -- --include-ignored --nocapture --test-threads 1
python3 -I review/review_fs_powers.py                                                                # §1.4's bounds
```

### E1: the free inputs, by strongly connected components (`review_free_inputs`)

**Method.** This test reads `spec::Circuit` only (σ, regions, blocks, ports), not the compiler's bookkeeping:

1. Every non-hole cell `j` has exactly one defining equation, `w_j = P_i` for the `i` with `σ_i = j`. Build the graph
   from each cell to the cells its equation reads.
2. Take its SCCs (iterative Tarjan) and classify the cyclic ones:
   - a cycle of forwards is a *free value*: any word;
   - one `b²` slot (coefficient 1, no κ) on a forward cycle is a *bit*;
   - anything else is *other*.
3. Take the ports' limb cells' backward closure: the cells the ports depend on.

**Result** (π1-rec's real circuit):

| | D16v (`N = 2^24`) | D32v (`N = 2^23`) |
|---|---:|---|
| cells in the ports' closure | 13,336,626 | 5,215,026 |
| free inputs in it: bits | **55,872** | **55,872** |
| free inputs in it: free values | **15** (cycles of 2) | **15** (cycles of 2) |
| holes read | 0 | 0 |
| expression cycles in the closure | 0 | 0 |
| outside the closure: free self-loops (unplaced forwards, padding) | 1,675,920 | 2,199,248 |
| outside the closure: padding rows' expression self-loops | 414,139 (31 kinds, e.g. `k0` χ, `kd` D units, `pack` 15) | 28,155 (46 kinds) |

- **The inputs are the intended ones.** 55,872 = 6,952 hashed stream bytes × 8 + 256 public-input bits, exactly the
  compiler's free bits. The 15 free values are the batch's 5 end values, which are never hashed.
- **Constants are not free inputs.** The IV and the name enter as κ constants.
- **Every cell the ports read is determined** acyclically by those inputs. No formula reads a hole, a free end, junk
  or a dead slot.

**Booleanity.** The test also infers which cells are bits in every satisfying witness: a cell is a bit if it is on a
`b²` cycle, a forward of a bit, or a coefficient-1 formula of bits with κ ∈ {0, 1}. It then checks every bit formula's
reads in the closure:

- every Keccak row (`k0`, `k1`, `kd`, `kprep`; D32v's `prep`, `prep-first`, `round`, `last`);
- every XOR, and every bit copy;
- every packing window's cells: 4,440 `pack` and 1,113 `pack-top4` slots.

All of them read bits. So no packing takes a non-bit input, and no Keccak value can leave GF(2).

### E2: the circuit is π1's graph on any stream (`review_mutated_streams`)

**Method.** Compile the circuit on each stream, then check two things:

1. **Internal pushes.** Every non-port push equals its target's pull.
2. **Ports.** Each port's limbs, read from the witness's port cells, equal `eval::evaluate` of π1's recorded graph on
   the same stream:
   - the statement's four words;
   - the roots' stream bytes;
   - the 51 elements, from the evaluated calls' words;
   - the 13 zero checks' values, in order.

**The streams:**

- the honest stream;
- one bit flipped, twice;
- 300 random bytes;
- a fully random stream with a random public input;
- the six counts all ones;
- the six counts zero.

**Result.** All 7 pass in both layouts. The failing zero checks are 0, 1, 1, 1, 9, 13 and 1. Every element in π1's
calls has a port, and so does every non-constant zero check.

The PCS fork's `review_fs_statement` covers the other half. On random streams and random public inputs, the evaluated
graph equals π1-rec's Rust verifier (`rust_verifier_with`, `Checks::Collect`): the 81 opening words, the 28 matrix
coordinates, a, b and the 13 checks. Its D32v/D16v test also matches all 80 digests and 12,545 limbs on a random
stream with out-of-range counts and a random IV.

**Together with E1:** any witness π2 accepts carries in its ports π1-rec's verifier's outputs on the stream its free
bits encode.

### E3: the holes (`review_pi2`)

- **E3, a garbage hole is accepted.** That is the documented behaviour, harmless while nothing reads a hole (N1).
- **E3b, a hole read is accepted with a forged public element** when the circuit was not validated (L1).

## Checked and found sound

### The copy argument (SPEC-REC §2.3, PI2.md §1, §4)

- **Set-based logUp in characteristic 2.** Each tag occurs in exactly two entries, so characteristic 2 forces the two
  values equal:
  - pull tags are the non-hole positions, distinct;
  - push tags are σ's values, injective, onto the non-holes plus one outside tag per port (`validate`);
  - public tags are the outside tags, once each;
  - tags are `ω_j = Σ j_b β_b` on `TAG_BITS` independent basis elements, and `log_n + 3 ≤ TAG_BITS`.

  Two pulls with the same (value, tag) cannot occur.
- **Pull-less holes.** On `V_m`, `1_S` is the holes' indicator: the port pairs' indicators, disjoint. At a hole the
  identity gives `h = 1/d_push`, apart from N1's vanishing case. `1_S · d_push` has degree below `4N`, so the degree
  is unchanged.
- **Indicators.** A pair is an aligned block (`first_row` a multiple of `2^s`) times a role: a coset
  `ω_c + span(β_r … β_{r+s−1})`.
  - Its indicator is `w_m/(Ẑ_s(t) + Ẑ_s(c_p))`, with `w_m` and `Ẑ_s` both of linear coefficient 1, of degree
    `N − 2^s`.
  - Pairs are disjoint (`pair_of` asserts it), and groups sum the pairs of one (role, formula, pulls).
  - The verifier evaluates a role-`k` formula on `v_{c⊕k}`, since `ω_{16y+c} = ω_{16y+k} + ω_{k⊕c}`.
- **Degrees.** `P < 3N` (indicator `N − 2^s` times a formula of degree 2 in cells of degree `< N`), the identity
  `< 5N`, `q < 4N`. `q`'s 4N coefficients and `h`'s N are fixed by `Q`'s table shape, and absent lanes have weight 0
  in `quotient::opening`.
- **`h(t)` is sent and checked.** It is bound by `Q`'s claim `(1 + ρ)h(t) + ρ q(t)`, with `q(t)` computed from the
  identity. `Σ_V h` is `h`'s novel coefficient `N − 1`, by `Σ_{V_m} X_j = [j = N−1]` under the Cantor normalisation.
- **ρ reused across W, Q and the setup.** Each claim is its own polynomial in ρ, so the errors add:
  - degree ≤ 15 for W's fold, its 16 eq polynomials at `(ρ, ρ², ρ⁴, ρ⁸)` unitriangular;
  - degree 1 for Q and the setup.
- **Port fingerprints.**
  - Three limbs give `L0 + YL1 + Y²L2`, the element itself, injective on `K³`.
  - Four limbs give `(L0 + YL1) + γ(L2 + YL3)`, nonzero in γ for distinct limbs since `{1, Y}` is K-independent. The
    public side is `half1 + γ·half0` as `next_root` reads them, and `(S0 + YS1) + γ(S2 + YS3)` as `statement_words`
    reads them (`adapt.rs:122-145`).
- **π2's transcript.**
  - The seed hashes the public input.
  - The public data, then W's root, come before α, β, γ.
  - Q's root comes before t.
  - The `2^r + 3` values come before ρ.
  - The stream must be read whole (`finish`; the contract checks the exact length).
- **The verifier's arithmetic.**
  - Digits `w_{l+1} = w_l² + w_l`.
  - The cells' fold at `w_l + ω_{c>>l}`, as `Ŵ_l(ω_c) = ω_{c>>l}`.
  - `u_l = 1 + 1/w_l + 1/w_{l+1} = w_l/(1 + w_l)`, and `Π(1 + w_l)^{-1} = t/w_{m+2}`.
  - The batched inverse rejects a zero product, covering `t ∈ V_{m+2}`, every group denominator and the public side's.
  - The norm inverse is checked by hand: Frobenius `(c0, c1, c2) ↦ (c0, c2, c1 + c2)`, since `Y^(2^64) = Y²`. The
    Itoh–Tsujii chain reaches `N^(2^63 − 1)`.
  - The tag walk equals `β ω_τ` by linearity.
- **Union bounds** (recomputed by the PCS fork):
  - copy argument: `4N/2^192` over W's list 9,952, 152.7 bits;
  - `t`: `5N · L_W · L_Q` with L_Q = 3,564 at `2^28`, 140.6 bits (D32v 141.3);
  - no challenge is drawn after an uncounted commitment;
  - 8 openings at 128.97 bits, 126.0 by a plain union;
  - π2's stacks take the certified ladders (`stacks_take_the_certified_queries`).

### The circuit (SPEC-REC §2.4, §10)

- **E1 and E2** above: the inputs, determinism, booleanity, and the ports equal to π1's graph on any stream.
- **D16v's Keccak-f**, by hand:
  - θ through `kprep`'s `C_0` and `D = C[x−1][z] + C[x+1][z−1]` D units: each C ends at one unit and is forwarded
    through another;
  - ρπ placement: lane `l` bit `z` goes to plane `π(l)/5`, cell `π(l) mod 5`, slice `z + ρ_l`, its D at `5 + x'`;
  - χ is `b_x + b_{x+2} + b_{x+1}b_{x+2}` with `b = c_x + c_{5+x}`, and no term cancels in `PolyBuilder`;
  - ι as κ = RC bit at `k0` roles 0 and 5, `P_0` included;
  - `P_{y'} = P_{y'−1} + χ` gives `C_{j+1}`;
  - D ends at its one plane-0 consumer.
- **D32v's rounds**, by hand: κ at the 7 roles whose push holds `A[0,0]`; `prep-first`'s capacity is known zero.
- **The sponge.**
  - pad10*1: `0x01` after the message, `0x80` in the last byte, and a full block when the message fills the rate.
  - The first block holds 104 data bytes after the 32-byte state.
  - Later blocks are XOR units (the state ends there, the bit is forwarded).
  - The digest is lanes 0–3.
  - Tested against `revm`'s Keccak on 0–300-byte messages (lib), and on every real call through E2.
- **`E` units.**
  - The product limbs (`y³ = y + 1`) are checked by hand.
  - A square is the product with two copies of `a` (slot and forward).
  - Sums are limbwise.
  - The 9-position unit forwards both operands, and its slots' pulls are free ends.
- **Packings.**
  - Horner by 15-bit windows: the slot reads its accumulator with `x^15` and the window bits with `x^i`.
  - The top window has at most 4 bits.
  - Absent exponents read one shared zero constant.
  - `be_bits` matches big-endian bytes, low bit first.
  - Limbs match `challenge_of`'s low 192 bits and `word_limbs`.
- **The layout invariant** (`layout.rs` `finish`): a free end, junk or a dead slot is never read by a live formula
  (E1 confirms this). Padding rows and unused forwards are unconstrained but outside every port's closure.

### π1's side and π1-rec (the statement/FS fork)

- **The graph's control flow does not depend on the stream.** `reduce` requires only lengths and the fixed shape, and
  the graph equals the Rust verifier on random streams.
- **The 13 zero checks:** each count's two range checks (`count ≤ 2^r`), then the batching sumcheck's terminal. There
  are no nonzero checks.
- **The row counts** are prover messages: stream bytes 0..24, hashed with C1's root by the first challenge. Leaving
  them out of π2's public inputs changes nothing.
- **Every stream byte is read by exactly one input**, so "fully consumed" is the fixed length. The five reads never
  hashed are the batch's end values, each a port-bound element. Any 24 bytes is an element.
- **The seed.** The name and π1's IV are κ constants. The public input enters through its bits' copies, and the same
  bits are packed into the Statement port.
- **Zerocheck point `r_i = c^(2^i)`.**
  - It is used only as the rounds' eq factors.
  - `eq(r(c), x) = Σ_{y⊇x} c^y` is unitriangular, so the sum is identically zero only if `P = 0` on the cube.
  - Degree `2^22 − 1`: 170.0 bits alone, 157.9 after C1's list (`review_fs_powers.py`).
- **Bus `α = (c, c², c⁴, c⁸)`.**
  - It is used only in the fingerprints and in the bytecode claim's point, which holds for any α.
  - Its 16 eq polynomials are a basis, so the fingerprint is injective in the tuple.
  - The bus is a product heap, so characteristic 2 adds nothing.
  - Joint Schwartz–Zippel over `(β, c)` at degree 16 gives 164.6 bits, 152.5 after the list.
- **`Circuit::digest`** covers everything `Spec` is built from. π1's call words are contract constants applied to
  values π2 proves.

### The contract (the PCS fork)

- **The entry** checks the exact calldata length, the selector and a zero call value.
- **Each `PCS_OPEN` call** is a `STATICCALL` to `0x12`, accepted only on success with 32 bytes returned and the word 1.
- **The call words.**
  - π1's words come from the circuit's `calls`.
  - Roots and elements are the very bytes the transcript absorbed.
  - The order is π1's five, then W (k = 1), Q (k = 2), setup (k = 1).
  - The setup root is a constant also bound in the IV.
- **Every calldata region flipped** (`review_pcs_contract`): in both layouts, parity with the Rust verifier holds,
  `PCS_OPEN` gets exactly `expected_calls`, and some claim is false on the honest tables.

### Baseline

On h1 these pass:

- `leanvm_rec`'s lib tests (9);
- `tests/pi2.rs` (5);
- `tests/circuit.rs` (4 configurations, 186 s);
- `pi2_real::real_end_to_end`, D16v × π1-rec: π2's proof of the real π1-rec proof (1,844 B of calldata), its three
  openings, the contract accepting with the 9 claims attested, and 18 flipped bytes rejected. 667 s without
  `target-cpu=native` (N5).
