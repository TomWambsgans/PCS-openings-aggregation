# Formal verification of `crates/quotient`

Goal: knowledge soundness, completeness and statistical zero knowledge of the membership proof that
`crates/quotient` builds and `crates/evm` verifies, proved in Lean 4 end to end, with the **extractor and the
simulator as explicit, computable definitions in the statements** so that a reviewer can check that they are
efficient (Lean has no running-time theorem; the convention is leanerVM's: a fixed straight-line extractor
that reads only the adversary's oracle transcript, its cost read off its loops).

Toolchain and dependency revisions are leanerVM `mumbai`'s (Lean `v4.34.1`, Mathlib `d13f23b7`, VCVio
`afa6593f`, CompPoly `572f9973`, ArkLib `4dae3acf`), so its results can be imported rather than reproved. The
starting point is leanVM's `formal/quotient` (branch `PCS-openings-aggregation`), whose README is kept as
[`README.upstream.md`](README.upstream.md): sorry-free proofs of the reduction for the BLAKE2s/full-adder
circuit, with ideal commitments.

## Layers

| | What | Source | Status |
|---|---|---|---|
| F1 | The reduction (five field elements → four claims): round-by-round knowledge soundness, completeness, honest-verifier ZK, Fiat–Shamir in the ROM, **ideal commitments** | ported from leanVM `formal/quotient` and adapted (below): `2^22` rows, the χ gate on bits (degree 2), degree bounds, the circuit argument (bits, no carries) | done: `lake build` green, sorry-free, end theorems on `propext`, `Classical.choice`, `Quot.sound` |
| F2 | WHIR openings sound for our claims (a λ-combination of `eq` weights on a stack of lanes) | leanerVM `mumbai`, `lean_vm` `Whir/Sound`: `whirSpec` holds for any multiaffine weight; our weight is one | to import |
| F3 | Hiding openings: the padded tables (base field `K = GF(2^64)`, challenges in `E = GF(2^192)`, first fold 6) and the Merkle siblings in the random-permutation model | new (the ZK-WHIR note, adapted to `K ⊂ E`; `membership-zk.md` of leanVM's branch for the sibling argument) | to do; padding not built in Rust yet |
| F4 | Composition: commitments as Merkle trees over Keccak-256 in the random-permutation model, the reduction's Keccak-256 chain, the openings' duplex; extraction from the adversary's transcript (`mumbai`'s `Statement/Extractor.lean` decodes WHIR words by Guruswami–Sudan) | `mumbai` `common` (sponge indifferentiability, ROM→RPM), `lean_vm` extraction | to do |
| F5 | The implementation is the model: the EVM contract and the Rust verifier are generated from one recorded operation graph (`crates/evm/src/record.rs`); emit that graph as a Lean term too and prove it equals the model's verifier | new | to do |

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

**The bounds, re-derived** (`Degrees.lean`, `Concrete.lean`, `Bits.lean`). `Bounds.identity` sums a bound on
every term of the two identities; with the gate of degree 2 it is
`2 * denominator + cells + rows + quotient + pub + 2 * cell` (was `4 * cell`). At the instance's table sizes
(witness polynomials `2^23`, quotients `2^26`, wiring and cells `2^24`, rows `2^22`, public weight
`2^24 + 9 * 2^10`): a cell's polynomial `4 * 2^23 + 3`, a denominator `3 * 2^24 + 4`, and
`Params.ofCantor_identity_eq`: the identities' degree is `2^28 + 2^22 + 9230` (`16.25 N` and a little), so
`Params.ofCantor_identity`: at most `2^29`. The public weight's degree (`natDegree_membershipPub_le`) is
`Σ_{11 ≤ j < 24} 2^j + 11 * 2^10 = 2^24 + 9 * 2^10`. The three round errors over `q = 2^192`
(`rbrError_le`): the copy argument `(2 N^2 + 4 N + 8) / q = (2^49 + 2^26 + 8) / 2^192 < 2^-142`, the
identities `≤ 2^29 / 2^192 = 2^-163`, the last `3 / 2^192`; each `≤ 2^-128`, so `knowledgeSoundness_bits`,
`knowledgeSoundness_ofCantor`, `knowledgeSoundness_membership`, `Instance.soundness` give `(Q + 3) / 2^128`.
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

The Keccak-f\[1600\] permutation behaves as a random permutation (leanerVM's model); the Lean kernel and the
three standard axioms; the EVM bytecode generator and revm with `FIELD_MUL` (differential tests, not proofs);
the PCS_OPEN aggregation layer that checks claims; the Rust prover (only completeness depends on it).
