<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# RecCompose: the recursive verifier's end theorems

The recursive EVM verifier for leanVM 42422001 proofs (`crates/leanvm_rec`): the contract runs π2's verifier, then six
`PCS_OPEN` calls (π1's `C1`, `C2`, `F`; π2's `W`, the setup, `Q`). Its statements are `RecStatement`'s
(`RecStatement/Security.lean`), in two parts, since π2's circuit computes π1-rec3's Fiat–Shamir with the real
Keccak-f[1600] while π1-rec3's soundness is proved in the random-permutation model:

1. **π2's part, in the random-permutation model**: `RecKnowledgeSoundness2 D ε2` (if the contract accepts, π2's
   extractor outputs π1's stream on which π1-rec3's recorded graph over Keccak-f[1600] accepts, its three calls the
   contract's), `RecCompleteness2 D P1 P2 δ2`;
2. **end to end, against Lv42's `M3Holds`**: `RecKnowledgeSoundness D ε2 ε1 εh`, `RecCompleteness D P1 P2 δ1 δh δ2`,
   Props whose own hypotheses are `RecGraph.Pi1.Pi1GraphIsVerifier`, `Pi1FsKeccak ε1`, `Pi1HazardKeccak εh` (and the
   completeness analogues): the Fiat–Shamir heuristic for Keccak-f[1600], justified by π1-rec3's random-permutation
   theorems (`UniSound.Rec3Ref.uniKnowledgeSoundness_closed_rec3`, `UniComplete.Rec3.uniCompletenessRec3_end_closed`)
   and `RecGraph.hazard_prob`.

This library proves part 1 from π2's layers, its bound in bits, and part 1 ⇒ part 2.

```sh
cd formal/EndToEnd   # on h1, under /root/pcs-quotient-fv/ only
systemd-run --scope -p MemoryMax=10G lake build RecCompose     # the theorems; #guard_msgs checks their axioms
python3 -I Review/RecSoundnessNumbers.py                        # ε2 = pi2Bound in exact rationals
```

## The end theorems (`End.lean`)

See the section "The recursive verifier" of [`../README.md`](../README.md) for the statements verbatim and the list of
named inputs; the files:

| File | What |
|---|---|
| `Basic.lean` | π2's outcome's fields; `W`'s candidates and their witness values as π2's extractor reads them; `pi1GraphAcceptsB_iff`; `recExtractFrom2_of_mem` (one accepted candidate suffices). |
| `Part1.lean` | `CallsPure`, `Pi2Extraction`, `Pi2Layers`; **`recKnowledgeSoundness2_of_layers`**. |
| `Circuit.lean` | `Pi2Layers.circuit` from RecCircuit's `pi1rec3_end` and `CircuitBridge`; `compile_ok` from the compiler's run on the emitted graph and `GraphsAgree`. |
| `Numbers.lean` | **`pi2Bound`** (`ε2`), `pi2_rounds_le` (RecPiop's three rounds times their lists, at most `2^-140.60`), **`pi2Bound_le_bits`** (`≤ 2^-64` for `Q ≤ 2^64`). |
| `Part2.lean` | the derived adversaries (`hazardAdversary`, `pi1Adversary`), the three events, `ExperimentsAgree`, `HazardCoupling`, `Pi1Coupling`; **`recKnowledgeSoundness_of_part1`**. |
| `Complete.lean` | `CompletenessAgree`, `CompletenessPi1Coupling`; **`recCompleteness_of_part1`**. |
| `End.lean` | **`recKnowledgeSoundness2_real`**, **`recKnowledgeSoundness_end`**, **`recCompleteness_end`**. |

## The statements' fixes (in `RecStatement/Security.lean`, found by this composition)

1. **π2's extractor searches by the whole acceptance.** It searched `W`'s list for the first candidate whose π1
   stream passes the graph's checks. A word within the list-decoding radius of two codewords (rate `1/2`: both within
   Johnson's `0.29`, the first within `1/4`, so the unique decoder lists it first) can make that candidate's stream an
   honest π1 proof of another transcript while the openings' claims hold of the second: the extractor would output a
   stream whose calls are not the contract's, and `RecKnowledgeSoundness2` would fail. It now searches by
   `pi1GraphAcceptsB` against the contract's π1 openings read off the calldata (`pi1OpsOf`).
2. **The derived π1 adversaries are given the setup's evaluations.** π2's extractor reads them. With the roots alone,
   the adversary built from π2's must recompute the setup: `ε1` would be charged at its `2^27` and more extra calls, not
   at `Q`, and π1-rec3's extractor would read a transcript that holds them, not π2's adversary's.
3. **π2's completeness is for π1-rec3's prover, on honest statements.** Stated for every `P1`, a `P1` of unbounded
   queries can grind its proof (the graph still accepting) until π2's honest run hits a degenerate challenge (`all = 0`).
