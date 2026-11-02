# Formal verification of `crates/quotient`

Goal: knowledge soundness, completeness and statistical zero knowledge of the membership proof that
`crates/quotient` builds and `crates/evm` verifies, proved in Lean 4 end to end, with the **extractor and the
simulator as explicit, computable definitions in the statements** so that a reviewer can check that they are
efficient (the target: F1's extractor reads the proof's polynomials in the ideal model, and F1's extractor and
simulator are `noncomputable`; the computable ones are the `Statement` package's work, F4/F5) (Lean has no running-time theorem; the convention is leanerVM's: a fixed straight-line extractor
that reads only the adversary's oracle transcript, its cost read off its loops).

Toolchain and dependency revisions are leanerVM `mumbai`'s (Lean `v4.34.1`, Mathlib `d13f23b7`, VCVio
`afa6593f`, CompPoly `572f9973`, ArkLib `4dae3acf`), so its results can be imported rather than reproved. The
starting point is leanVM's `formal/quotient` (branch `PCS-openings-aggregation`), whose README is kept as
[`README.upstream.md`](README.upstream.md): sorry-free proofs of the reduction for the BLAKE2s/full-adder
circuit, with ideal commitments.

## Layers

| | What | Source | Status |
|---|---|---|---|
| F0 | The circuit: a Lean definition of the deployed wiring (`quotient::circuit::membership`), proof that a satisfying assignment is its computation and that this computation is Keccak-256 membership; the constants (Cantor basis, `τ`, `b`, the bit weights) as computable definitions whose hypotheses are checked | new (found missing by the Lean review: `Instance.soundness` holds for every wiring, so for a degenerate one it says nothing) | **done for a circuit given as a parameter** (`CircuitLayout.lean`, `Pinning.lean`, `Statement.lean`): `Instance.soundness_circuit`: for an instance whose wiring lays a loop-free χ circuit `C` (`Laid`: input cells on the cycle of what they read, word 5's 128 bits on the zero's cycle, word 4's bit 0 the one's anchor and its other bits on the zero's) and whose weights are `coordinate_weight`'s (`bit_weight(j)` = `x^j`, `Y x^(j-64)`, with `x ≠ 1`, `Y ≠ 1`), an accepted proof of `statementWords x Y y root` (`statement::halves` of `y`, `root`, then `(1, 0, 0, 0)`) holds `C`'s computation on some input bits with public words 0–3 the halves of `(y, root)`, except with probability `(Q + 3) / 2^128`; `soundness_circuit_bits`: with the 128 bit weights independent over `GF(2)`, its public bits are the bytes' bits as `circuit::public_words` reads them. Derived from `Instance.soundness` and `cells_determined` (bridged by `Instance.cells_determined`; zero then one pinned by `zero_pinned`, `one_pinned`); the cone of both reaches the circuit argument. Not vacuous: `wiringOf C` meets `Laid` (`laid_wiringOf`) and the cells of every computation of `C` satisfy the relation on it (`relation_wiringOf`, `relation_statementWords`). Sorry-free, on `propext`, `Classical.choice`, `Quot.sound`. **To do**: the deployed circuit as a Lean `C : ChiCircuit (Fin (2^22))` with `Laid` for the deployed wiring (or `I.wiring = wiringOf C`), its computation being Keccak-256 membership, and `x`, `Y` of `F192` with independent bit weights |
| F1 | The reduction (five field elements → four claims): round-by-round knowledge soundness, completeness, honest-verifier ZK, Fiat–Shamir in the ROM, **ideal commitments** | ported from leanVM `formal/quotient` and adapted (below): `2^22` rows, the χ gate on bits (degree 2), degree bounds, the circuit argument (bits, no carries) | done for the reduction: `lake build` green, sorry-free, end theorems on `propext`, `Classical.choice`, `Quot.sound` (761 declarations swept, `formal/Review/Axioms.lean`). Its zero knowledge is for ideal *hiding* commitments only: the deployed roots and openings are F3's (and the masks of the five values have no slack, so nothing else may reveal an evaluation of a witness polynomial). `Instance.soundness`, `zero_knowledge`, `completeness` hold for every wiring; `soundness_circuit` (F0) is for a wiring that lays a χ circuit |
| F2 | WHIR openings list-sound for our claims (some member of the root's level-0 list satisfies all claims of one opening) | leanerVM `mumbai`, `lean_vm` `Whir/Sound`: `stackedSpec` holds for any multiaffine weights; ours are | round-by-round soundness and the table meaning proved in [`WhirBridge/`](WhirBridge/README.md), and Fiat–Shamir in the ROM for leanVM's transcript shape (claims chosen by the adversary); the Rust transcript now has that shape (`opening::iv`; the old one, root hashed into the seed, was the stated gap); level-0 candidates per root exported: ≤ 9,952 (wiring), 7,908 (witness), 3,564 (quotient), leanerVM's certified codes; the Lean mirror `openingVerifyWithHash` and `Test/Check.lean` still model the old seed |
| F3 | Hiding openings: the padded tables (base field `K = GF(2^64)`, challenges in `E = GF(2^192)`, first fold 6); then (F3b) the roots, Merkle siblings, nonces and Fiat–Shamir in the random-oracle and random-permutation models, with an explicit simulator | new (the ZK-WHIR note, adapted to `K ⊂ E`; `membership-zk.md` of leanVM's branch for the sibling argument) | Lean: `formal/QuotientSecurity/Hiding/` (sorry-free): for two tables with the same claims, the views (lane rounds, the folded table, every opened row) have the same distribution on the good challenges (`hidden_view_evalDistEq`), and differ by at most Pr[(R) fails] + ~2^-127 on any event (`hidden_prEvent_le_bound`; (S) bounded by `card_not_span_four_le`); unopened rows keep ≥ 2,368 / 3,840 bits (`unopened_row_le`). Condition (R) (`RoundsReached`) is a hypothesis with no bound in Lean (estimated ≈ 2^-53 in `HIDING.md`, not proven); a layout change that makes it hold for all challenges is being designed. The view is the linear part only: not modelled are the level-0 roots (in calldata), the Merkle siblings, the grinding nonces and Fiat–Shamir (F3b, in progress; `formal/Review/HidingReview.lean`'s `stack_ne_of_entry_ne`: hiding of the roots rests on that random-oracle step). Per table, interactive, honest verifier; (Q) and `WeightsFit` are hypotheses, not yet instantiated with the deployed layout. The padding is uniform here; the prover's comes from a CSPRNG (ChaCha12 keyed by a Keccak-256 KDF of an OS seed), so as deployed the hiding is computational in that generator |
| F4 | Composition: commitments as Merkle trees over Keccak-256 in the random-permutation model, the reduction's Keccak-256 chain, the openings' duplex; extraction from the adversary's transcript (`mumbai`'s `Statement/Extractor.lean` decodes WHIR words by Guruswami–Sudan) | `mumbai` `common` (sponge indifferentiability, ROM→RPM), `lean_vm` extraction | **the chain (F4a) done** in [`QuotientRpm/`](#the-keccak-256-chain-f4a) (sorry-free, `propext`, `Classical.choice`, `Quot.sound`): the reduction with `transcript.rs`'s chain, byte for byte, in the ROM and in leanerVM's RPM, ideal commitments (a root is Keccak-256 of an injective encoding of the message). **Real commitments composed with the openings (F4b)** in [`Compose/`](Compose/README.md) (sorry-free, same three axioms), in the ROM: the chain absorbs the proof's roots, every round union-bounded over the roots' candidate lists (`L₁` for `(α, β, γ)`, `L₁ L₂` for `t`, `ρ`; `≤ 2^-128` per query for lists up to `2^18`, `2^-138` with the certified `7908` / `3564`), the Merkle extraction from the transcript (computable, stable), the extractor the witness root's decoded list; `knowledgeSoundness_merkle`: the three openings' doomed events (F2's `family_sound` events, hypotheses here; F2 covers the wiring opening's layout only so far) plus `(Q + 6 + QV) (2^-128 + 4 (Q + 6 + QV) / 2^256)`. To do: the openings' events in the same model (two oracles, or the RPM), F2 for the hidden layouts, the decoder as mumbai's exact Johnson-list decoder read back through the hidden layouts, the RPM transfer |
| F5 | The implementation is the model: the EVM contract and the Rust verifier are generated from one recorded operation graph (`crates/evm/src/record.rs`); emit that graph as a Lean term too and prove it equals the model's verifier | new | to do |

## The Keccak-256 chain (F4a)

`QuotientRpm/` (library `QuotientRpm`, which needs leanerVM `mumbai`'s `statement` and `common` packages,
pinned in `lakefile.toml`) lifts the reduction's knowledge soundness from an abstract random oracle on
`(statement, messages)` to the transcript `crates/quotient/src/transcript.rs` computes.

- **The chain** (`Bytes.lean`, `Chain.lean`): the seed is Keccak-256 of the label `pcs-quotient-kc1 ‖
  index_root ‖ y ‖ root` (112 bytes); each challenge is Keccak-256 of the state and of the scalars sent since
  the last one, each a 32-byte big-endian word (`[0; 8] ‖ c2 ‖ c1 ‖ c0`, `scalarWord`), and is the state's low
  192 bits (`stateLimbs`: limb `i` is bytes `24 − 8i .. 32 − 8i`, big-endian); a root is two scalars, its
  128-bit halves read as little-endian words (`rootScalars`), i.e. sixteen zero bytes and the half reversed
  (`rootWords_eq`). The verifier (`Wire.verifyWith`, over any hash in any monad): root, `α`, `β`, `γ`, root,
  `t`, five values, `ρ`, as in `reduce`. A `Wire` holds what the chain reads besides the proof: the circuit's
  commitment, how the statement's 64 bytes are read as `Params`' statement, the field's limbs, and the two
  messages' encodings. **Commitments are ideal**: the proof carries the polynomials and the root the chain
  absorbs is Keccak-256 of an injective encoding of them, binding up to a collision (counted).
- **Random oracle on transcripts** (`ChainRom.lean`, `FreshBad.lean`, `Uniform.lean`): against a random oracle
  `H : bytes → 32 bytes`, a fresh query is bad (`chainBad`) when its answer collides with an earlier answer or
  sits where an earlier input holds a state or a root (`Coll`, at most `(3|H| + 2)/2^256`), or when it is a
  chain input whose challenge(s) turn the round's state from lost to won (`FirstBad`, `SecondBad`,
  `ThirdBad`: the first round's three hashes are treated as one triple of uniform states; the parse is unique
  given a collision-free history, so the three are exclusive, each at most `roundError`). The low 192 bits of
  a uniform state are uniform (`prEvent_chal`, every limb triple having `256^8` states). An accepted proof of
  cells that fail the relation makes a fresh query bad (`trace_chainBad`, through `bad_of_accepts` of
  `Joint.lean`); with an eager-table lemma whose bad events see the history (`prEvent_randomOracle_le_of_freshBad`,
  after VCVio's `prEvent_randomOracle_le_of_bad_queries`): **`knowledgeSoundness_chain`**, at most
  `(Q + 8)(roundError + 3(Q + 8)/2^256)` for `Q` adversary queries (the verifier's eight hashes counted).
- **The random-permutation model** (`Rpm.lean`): the experiment `rpmExperiment` has the adversary (coins, `π`,
  `π⁻¹`) and the verifier hashing with Keccak-256 over the same `π`; `common`'s `runK_expand`, `runK_relabel`
  and `keccak256_transfer` move it to the ROM against `advS` (cost `Q²/2^509`, `Q` the permutation calls of
  the whole game), leanerVM's derandomization removes the simulator's coins (`exists_det`).
  **`knowledgeSoundness_rpm`**: `(Q + 8)(roundError + 3(Q + 8)/2^256) + Q²/2^509`; at the protocol's sizes
  (`roundError_le`: `≤ 2^-163`, the identities' degree `2^29` over `2^192`) **`knowledgeSoundness_rpm_bits`**
  and, for every circuit, **`Instance.soundness_rpm`**: `(Q + 8)(2^-163 + 3(Q + 8)/2^256) + Q²/2^509`.

## The port to this protocol (F1)

`README.upstream.md` describes leanVM's circuit; this protocol differs in three ways, and the Lean files now
describe this one.

- **The gate** (`Protocol.lean`'s `gate`, `quotient::protocol`'s `gate`): `V + X + C + Y·C`, that is
  `V = X ⊕ (C ∧ ¬Y)` on bits (Keccak's χ), of degree 2, with no `θ` and no carries. `θ = β_1` stays in `Params`:
  it places a row's four cells at `x, x + 1, x + θ, x + θ + 1`.
- **The circuit argument** (`Circuit.lean`): `ChiCircuit` replaces `AdderCircuit`. An input row reads its own
  output in `X`, `Y` and `C` (`quotient::circuit::Builder::input`), so its gate is `v + v + v + v·v = v^2 + v`
  and `input_is_bit`: it holds `0` or `1`; every other row reads constants or rows of lower rank, and
  `gate_output`: on bits the gate gives `V = chiOf X Y C`, a bit. `ChiCircuit.determined`: two assignments, in
  any field of characteristic 2, that satisfy every gate and agree on the inputs agree everywhere, and every
  output is a bit (no `GF(4)`). `cells_determined`, `copy_iterate`, `word_pins`, `Wired` are as before, on bits.
- **The size**: `2^22` rows, cells named by `m = 24` bits (`22 + 2`, the opaque `le24`), `N = 2^24` cells;
  the tables have `m + 1 = 25` (witness), `m = 24` (wiring) and `m + 6 = 30` (quotient) variables, as
  `claims_iff_accepts_ofCantor` states them (the WHIR stacks of `opening::Layout` are not modelled: a table
  of the layout is a table whose other chunks are zero).

**The bounds, re-derived** (`Degrees.lean`, `Concrete.lean`, `Bits.lean`). `Bounds.identity` is the largest
of the bounds on the terms of the two identities (upstream summed them): with the gate of degree 2 it is
`max (max (2 * denominator) cells + max cells rows + quotient) (2 * denominator + max (pub + cell) (2 * cell))`
(the terms `D D' h`, `v_cells q`, `v_rows (D D' q_gate + v_cells j)`, `pub w D D'`, `D D' gate`; it bounds the
product the verifier inverts too). At the instance's table sizes
(witness polynomials `2^23`, quotients `2^26`, wiring and cells `2^24`, rows `2^22`, public weight
`2^24 + 9 * 2^10`): a cell's polynomial `4 * 2^23 + 3`, a denominator `3 * 2^24 + 4`, and
`Params.ofCantor_identity_eq`: the identities' degree is at most `11 * 2^24 + 8` (`11 N` and a little, the copy
identity's `D D' h`; the sum was `2^28 + 2^22 + 9230`), so `Params.ofCantor_identity_le_margin`: at most `2^28`
(and `Params.ofCantor_identity`: at most `2^29`). The public weight's degree (`natDegree_membershipPub_le`) is
`Σ_{11 ≤ j < 24} 2^j + 11 * 2^10 = 2^24 + 9 * 2^10`. The three round errors over `q = 2^192`
(`rbrError_le`): the copy argument `(4 N + 8) / q = (2^26 + 8) / 2^192`, about `2^-166` (was
`(2 N^2 + 4 N + 8) / q`, about `2^-143`; below), the identities `(11 * 2^24 + 8) / 2^192 < 2^-164`, the last
`3 / 2^192`; each `≤ 2^-128`, so `knowledgeSoundness_bits`, `knowledgeSoundness_ofCantor`,
`knowledgeSoundness_membership`, `Instance.soundness` give `(Q + 3) / 2^128`.

*The first challenge, tight* (`card_consistent_le`, `card_copy_le`, `LogDerivative.lean`). Upstream excluded
`2 N^2` values of `β` (any two poles meeting) and `2 N q^2` triples with a vanishing denominator. Now, if the
copy from `x₁` to `σ x₁` fails: a consistent triple has, at every cell, both denominators zero or neither
(`consistent_denominators`: the copy identity at a cell is `D D' h = D + D' + pub w D D'`), and where none
vanishes the sum of logarithmic derivatives meets the target. The pole `w(σ x₁) + β σ x₁` of the first term of
`σ x₁` is cancelled only by the first term of another cell (`N - 1` values of `β`) or the second term of a
cell other than `x₁` (`N - 1` values; the second term of `x₁` has the same label and another value): outside
these `2 N - 2` values (`poleBetas`) the cleared polynomial in `α` is not zero and of degree at most `2 N`, and
every consistent `α` is a root of it (one at which a cell's two denominators vanish together too). So at most
`(2 N - 2) q + 2 N q` pairs `(α, β)` per `γ`, and with the other cases (a gate fails: `2 N q^2`; a word fails:
`(2 N + words) q^2`) at most `(4 N + words) q^2` triples. This also beats the `(6 N + 8) / q` of the review,
which still counted the triples with a vanishing denominator apart.

*The margin for WHIR's lists* (`rbrError_mul_sq_le`, `rbrError_list_margin`, `rbrError_list_margin_ofCantor`,
`roundError_mul_sq_le`). With WHIR without an out-of-domain sample at level 0, each challenge is
union-bounded over the level-0 Johnson lists involved: `L` for `(α, β, γ)` and for `ρ`, `L^2` for `t`. For any
`L ≤ 2^18` (leanerVM's generic list hypothesis; its certified parameters give `L ≤ 7908`) and identities of
degree at most `2^28`, every round error times `L^2` stays at most `2^-128`: on the instance
`2^36 (2^26 + 8) / 2^192`, about `2^-130`, `2^36 (11 * 2^24 + 8) / 2^192`, about `2^-128.5`, and
`3 * 2^36 / 2^192`. Both tightenings are needed: upstream's first round times `2^18` is `2^-125`, and the
summed degree `2^28 + 2^22 + 9230` times `2^36` exceeds `2^-128`.
Zero knowledge: `zkError = (2 N + 4 * 2^22) / q = 3 * 2^24 / 2^192` (`zkError_le`, the mask's vanishing
polynomial `w_22` in the row variable). The honest messages (`honest_legal`, for a first message of degree
`2^22 + 2`): copy quotient at most `3 * 2^24 + 9249`, gate quotient at most `7 * 2^22 + 22`, both within the
quotient table's `2^26`. Completeness's uncounted rejection (`1 + w_k(t) = 0` for some `k ≤ m + 1`) is now
about `2^26 / q`.

**The claims against the Rust `reduce`.** Reviewed coordinate by coordinate for this protocol: the witness,
wiring and quotient claims' points and values, the sum claim, the cells of the row of `t`, the gate, the
public weight's product, the target, the rows' polynomial and the rejection; the comparison is written out
above `claims_iff_accepts_ofCantor` (`Concrete.lean`). No mismatch; `reduce` is leanVM's but for the gate,
which is the model's `gate` on `cellAt`.

## What will be trusted (the target)

The Keccak-f\[1600\] permutation behaves as a random permutation (leanerVM's model; note that one Keccak-256 serves
the reduction's transcript, the WHIR Merkle trees and the statement's own Merkle tree, so the model must be the
shared random permutation, not a private oracle as in F1); the Lean kernel and the three standard axioms; until
F0 is done, that the circuit committed as the index root is a Lean `C` meeting `Laid` whose computation is the statement (the step from such a `C` to the end theorem is proved: `soundness_circuit`); the EVM bytecode generator and revm with `FIELD_MUL` (differential tests, not proofs);
the PCS_OPEN aggregation layer, which must check all the claims of each call in one opening; the Rust prover (only completeness depends on it).
