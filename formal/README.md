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
| F1 | The reduction (five field elements → four claims): round-by-round knowledge soundness, completeness, honest-verifier ZK, Fiat–Shamir in the ROM, **ideal commitments** | ported from leanVM `formal/quotient`; to adapt: `2^22` rows, the χ gate on bits (degree 2), degree bounds, the circuit argument (bits, no carries) | building on the new pins |
| F2 | WHIR openings sound for our claims (a λ-combination of `eq` weights on a stack of lanes) | leanerVM `mumbai`, `lean_vm` `Whir/Sound`: `stackedSpec` holds for any multiaffine weights; ours are | round-by-round soundness and the table meaning proved in [`WhirBridge/`](WhirBridge/README.md), and Fiat–Shamir in the ROM for leanVM's transcript shape (claims chosen by the adversary); our own transcript (root hashed into the seed) is a stated gap |
| F3 | Hiding openings: the padded tables (base field `K = GF(2^64)`, challenges in `E = GF(2^192)`, first fold 6) and the Merkle siblings in the random-permutation model | new (the ZK-WHIR note, adapted to `K ⊂ E`; `membership-zk.md` of leanVM's branch for the sibling argument) | to do; padding not built in Rust yet |
| F4 | Composition: commitments as Merkle trees over Keccak-256 in the random-permutation model, the reduction's Keccak-256 chain, the openings' duplex; extraction from the adversary's transcript (`mumbai`'s `Statement/Extractor.lean` decodes WHIR words by Guruswami–Sudan) | `mumbai` `common` (sponge indifferentiability, ROM→RPM), `lean_vm` extraction | to do |
| F5 | The implementation is the model: the EVM contract and the Rust verifier are generated from one recorded operation graph (`crates/evm/src/record.rs`); emit that graph as a Lean term too and prove it equals the model's verifier | new | to do |

## What will be trusted (the target)

The Keccak-f\[1600\] permutation behaves as a random permutation (leanerVM's model); the Lean kernel and the
three standard axioms; the EVM bytecode generator and revm with `FIELD_MUL` (differential tests, not proofs);
the PCS_OPEN aggregation layer that checks claims; the Rust prover (only completeness depends on it).
