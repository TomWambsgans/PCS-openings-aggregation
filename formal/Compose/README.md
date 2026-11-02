<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# Compose: the reduction with real commitments, composed with the openings (F4)

F1 (`QuotientSecurity`) proves the reduction sound with **ideal** commitments, and F4a
(`QuotientRpm`) runs it on the deployed Keccak-256 chain, the roots still hashes of the
polynomials. Here the roots are the proof's: Merkle roots whose openings (F2, `WhirBridge`) are
only **list**-sound (no out-of-domain sample at WHIR's level 0). Everything is sorry-free and
depends on `propext`, `Classical.choice` and `Quot.sound` only (`Compose/Axioms.lean`).

| File | What |
|---|---|
| `Compose/ListChain.lean` | The reduction with real roots in the random-oracle model `H : bytes → 32 bytes` (F4a's): the chain of `transcript.rs` absorbs the two roots, the verifier then runs any computation `post` (the openings). A **list commitment** (`ListCommit`) reads candidates for a digest off the inputs asked so far, at most `L` of them, stable once the inputs below the digest are asked. Each fresh query is bad with probability at most `(4 \|H\| + 3)/2^256 + max L₁ (L₁ L₂) · roundError` (`prob_listBad`: every round union-bounded over the candidates of the roots before it, `L₁` for `(α, β, γ)`, `L₁ L₂` pairs for `t` and `ρ`); a winning run asks one (`trace_listBad`). **`knowledgeSoundness_list`**. |
| `Compose/Merkle.lean` | The Merkle tree's list commitment (`merkleCommit`): climb down from the root through the transcript's answered inputs (a unique preimage at each step, `uniq`), then any list decoder. Computable; `merkleWord_stable` proves the stability. |
| `Compose/Openings.lean` | The deployed verifier: `Params.Accepts` is the witness claim, the wiring claim, the reduction's own check and the two quotient claims (`accepts_iff`); the verifier accepts when its check holds and the three openings accept (`Accepted`). The **extractor** (`extractor`) returns the witness root's candidate list read off the transcript. A broken run has a doomed opening or wins the list game (`breaks_imp`). **`knowledgeSoundness_composed`**. |
| `Compose/Bits.lean` | The numbers: `max L₁ (L₁ L₂) · roundError ≤ 2^-128` for lists up to `2^18` (F1's margin `roundError_mul_sq_le`), `≤ 2^-138` for the certified `7908` / `3564`. |
| `Compose/Final.lean` | **`knowledgeSoundness_merkle`** / `_certified`: the composed statement with the Merkle extractor `witnessExtractor`. |
| `Compose/TwoOracle.lean` | **The same in leanerVM `mumbai`'s two-oracle model** `KeccakCalls` (Keccak-256 and Keccak-f[1600], the model of F2's `family_sound`): the bad-query engine for dependent answer types (`prEvent_randomOracle_le_of_freshBad_dep`); Keccak-256's answers read as 32 bytes (`Digest.toRpm`, `viewT`); a uniform table of both oracles read through the view is a uniform table of 32-byte answers (`prEvent_view`), so each fresh query is bad with `listBad`'s probability (`prob_kcBad`); the chain on Keccak-256, the openings any computation of both oracles, the transcript of the Keccak-256 queries (`kcExperiment`); **`knowledgeSoundness_list_kc`**. |
| `Compose/ComposedKC.lean` | **`knowledgeSoundness_composed_kc`**, **`knowledgeSoundness_merkle_kc`**: the composed statements in mumbai's model, the three openings' doomed events now events of the experiment `family_sound` lives in. |
| `Compose/AdversaryLog.lean` | **The extractor reads the adversary's queries only** (`adversaryExtractor`: an explicit, computable function of the adversary's Keccak-256 query log and the proof): a fresh answer after the adversary's last query that is a root it announced is bad (`rootBad`, `2/2^256`, `prob_rootBad`); without it the candidates read off the adversary's log are those read off the whole run's (`trace_adv`); **`knowledgeSoundness_merkle_adv`**: the openings' terms plus `(Q + 6 + QV) (2^-128 + 5 (Q + 6 + QV) / 2^256)`. |
| `Compose/Coupling.lean` | The logged run is the random oracle's run (`map_run_loggedKC`) and its transcript is the oracle's cache (`consistent_run_loggedKC`), so an event of a stage's cache is an event of its transcript (`prEvent_loggedPrefix`: the logged prefix is `romExperiment`). |
| `Compose/Deployed.lean` | **The deployed composition**: the setup computes the circuit's commitment with the oracle (`withSetup`, `wiringSetup`); the chain, then `opening::verify` (F2's `ourVerifier`) for the witness, wiring and quotient tables (`deployedExp`); **`prEvent_EW_le`, `prEvent_EQ_le`**: the witness and quotient terms are F2's `ours_sound`; `trace_deployed`; **`knowledgeSoundness_deployed_setup`**. |
| `Compose/Extract.lean` | **The Merkle extraction is mumbai's `extract` without collisions**: a climb through the history's answers is `merkleWord`'s descent and conversely (`leafAt_of_climb`, `leafAt_some`); with answers injective on the history, at every position of the tree `merkleWord`'s row read as words is mumbai's `Rom.extract` row (`wordOfMerkle_eq_extract`). |

## The statement

```lean
theorem knowledgeSoundness_merkle (hq : Fintype.card F = 2 ^ 192) (hN : P.nCells = 2 ^ 24)
    (hw : P.words = 8) (hd : B.identity ≤ 2 ^ 28)
    (c₁ : TableCode B.Msg₁) (c₂ : TableCode B.Msg₂) (h₁ : c₁.bound ≤ 2 ^ 18)
    (h₂ : c₂.bound ≤ 2 ^ 18)
    (A : OracleComp HashSpec (RootProof F × O))
    (openings : RootProof F × O → Chals F → OracleComp HashSpec Verdicts) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (openings p ch) QV)
    (εW εσ εQ : ℝ≥0∞)
    (hW : Pr{let z ← (simulateQ randomOracle (rootExperiment W A openings)).run' ∅}[
      WitnessDoomed c₁.commit z] ≤ εW)
    (hσ : Pr{let z ← (simulateQ randomOracle (rootExperiment W A openings)).run' ∅}[
      WiringDoomed (P := P) z] ≤ εσ)
    (hQd : Pr{let z ← (simulateQ randomOracle (rootExperiment W A openings)).run' ∅}[
      QuotientDoomed W c₂.commit z] ≤ εQ) :
    Pr{let z ← (simulateQ randomOracle (rootExperiment W A openings)).run' ∅}[
        Accepted (P := P) z ∧
          ∀ g ∈ witnessExtractor c₁ z, ¬ P.Sat (W.decode z.1.proof.stmt) (P.cells g.1)] ≤
      εW + εσ + εQ + ((Q + 6 + QV : ℕ) : ℝ≥0∞) * (((1 / 2 ^ 128 : ℝ≥0) : ℝ≥0∞) +
        4 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256)
```

`rootExperiment W A openings` runs the adversary, the chain on its two roots and five values, then
the openings' verifier, against one lazily sampled random oracle, and logs every query with its
answer (the transcript). `witnessExtractor c₁ z` reads the transcript and the first root, climbs
the witness table's Merkle tree (height `c₁.height`, leaves of `c₁.leafLen` bytes) and decodes the
word with `c₁.dec` (lists of at most `c₁.bound`). `_certified`: `2^-138` in place of `2^-128` for
`c₁.bound ≤ 7908`, `c₂.bound ≤ 3564`, identities of degree at most `2^29`.

## The statement in mumbai's model

`knowledgeSoundness_merkle_kc` is `knowledgeSoundness_merkle` with `OracleComp KeccakCalls` in
place of `OracleComp HashSpec` and `kcExperiment` in place of `rootExperiment`: same bound,
`εW + εσ + εQ + (Q + 6 + QV) (2^-128 + 4 (Q + 6 + QV) / 2^256)`, the extractor reading the
transcript of every Keccak-256 query of the run.

## What stays a hypothesis

* **The openings' terms.** In the general statements (`knowledgeSoundness_merkle`, `_kc`, `_adv`)
  `hW`, `hσ`, `hQd` are events in F2's oracle model, **not** literally F2's: the openings' verifier is
  any computation, the candidates are `merkleWord` and a decoder (not `extract`, `Candidates`,
  `Layout.tableEval`), the claims are F1's polynomial identities (not `reduce`'s multilinear claims),
  and the word is read off the final transcript (not the cache at the end of the opening). In the
  deployed composition (`Deployed.lean`) the witness and quotient terms **are** F2's `ours_sound`
  (`prEvent_EW_le`, `prEvent_EQ_le`), what remains being:
  1. **`WitnessMatch`, `QuotientMatch`**: the decoder lists every candidate of mumbai's extraction
     (an exact enumeration of `Candidates`), read back as F1's message, and a candidate whose table
     satisfies the opening's claims (`ourVerifier`'s, `Layout.tableEval`) reads back as a message
     satisfying F1's claim (`Concrete.lean`'s `claims_iff_accepts_ofCantor` is the starting point);
  2. **the wiring term `εσ`**: the experiment now computes the circuit's commitment with the oracle
     before the adversary runs (`withSetup`, `wiringSetup`), so its discharge is meaningful: the
     setup's queries make the index root's word the honest codeword, whose Johnson list is itself
     (at rate `1/2` the Johnson radius `1 − √ρ ≈ 0.293` is below the relative distance `1/2`, to be
     proved for mumbai's `Candidates` of stacked tables), and its doom is then the wiring claim's
     failure (to do).
* **The decoder's list bound** `c.bound`: `WhirBridge.candidates_ours` (`7908`, `3564`) for
  mumbai's `Candidates`; an exact decoder inherits it.
* **The `Wire`** (F4a's): the circuit's commitment, the statement's decoding, the limbs, as in
  `QuotientRpm`; and **the circuit** (F0): the relation is `Params.Sat` for the deployed wiring.
* **The model**: one random oracle for Keccak-256 (the random-permutation model, mumbai's
  `common` transfer as F4a's `Rpm.lean` applies it, is not taken here).
* **The extractor's reads**: `witnessExtractor` and `extractor` (ROM, two-oracle) read every
  Keccak-256 query of the run; `adversaryExtractor` (`AdversaryLog.lean`, `Deployed.lean`) reads the
  adversary's queries (and the setup's, which are public) only.
* **Computability**: `witnessExtractor` is computable given a computable decoder; the
  one-witness extractor `extractorOne` is `noncomputable` (F1's cells are `Polynomial`
  evaluations).

## Building

As `WhirBridge`: against a built leanerVM `6175f1a0` at `../leanervm`, sharing `lean_vm`'s
packages; the libraries `QuotientSecurity`, `QuotientRpm`, `WhirBridge` compile from their sources
in `formal/` (`srcDir`), which checks that `formal/` builds against `lean_vm`'s package set (it
does: 9,925 jobs, ArkLib's `OracleReduction.Security.RoundByRound` and VCVio's `FreshQuery` added).
On `h1`: `/root/pcs-quotient-fv/compose/formal/Compose`, `lake build`; `Compose` itself builds in
about a minute.
