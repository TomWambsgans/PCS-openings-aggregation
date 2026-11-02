-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Compose.Bits
import Compose.Merkle

/-!
# The composed statement, with the Merkle extractor

`knowledgeSoundness_merkle`: the composition of `Openings.lean` with the two roots' list
commitments the Merkle trees of `Merkle.lean`, so that **the extractor is explicit and
computable** (`witnessExtractor`): it reads the transcript of **every** query of the run (the
adversary's, the chain's, the openings'; `AdversaryLog.lean`'s `adversaryExtractor` reads the
adversary's only) and the proof's first root, climbs the witness table's Merkle tree down from the root through the answered inputs
(`merkleWord`), and list-decodes the word with `dec₁` (for the deployed witness table, the
level-0 Johnson list of WHIR's certified code: at most `7908` stacks, mumbai's `fastStacks` /
Guruswami–Sudan `decodeStacks`, each read back as a table and as the first message).

The bound: the three openings' terms, plus `(Q + 6 + QV) (2^-128 + 4 (Q + 6 + QV) / 2^256)`
for decoders of lists of at most `2^18`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm QuotientSecurity QuotientSecurity.Params

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : Params F} {B : P.Bounds} (W : Wire P B) {O : Type}

/-- The Merkle shape and list decoder of a table: the tree's height, a leaf's byte length, and a
decoder of the word under a root to at most `bound` candidates. -/
structure TableCode (M : Type) where
  height : ℕ
  leafLen : ℕ
  bound : ℕ
  dec : (Fin (2 ^ height) → Option (List UInt8)) → List M
  length_dec : ∀ w, (dec w).length ≤ bound

/-- A table's list commitment: its Merkle tree, then its decoder. -/
def TableCode.commit {M : Type} (c : TableCode M) : ListCommit M :=
  merkleCommit c.height c.leafLen c.bound c.dec c.length_dec

/-- **The extractor**: the witness table's Merkle tree climbed down from the proof's first root
through the transcript's answered inputs, then decoded. Computable when the decoder is. -/
def witnessExtractor (c₁ : TableCode B.Msg₁) (z : Run F O Verdicts × Transcript) : List B.Msg₁ :=
  c₁.dec (merkleWord (histOfTr z.2) (tableOfTr z.2) c₁.height c₁.leafLen z.1.proof.r₁)

theorem witnessExtractor_eq (c₁ : TableCode B.Msg₁) (z : Run F O Verdicts × Transcript) :
    witnessExtractor c₁ z = extractor c₁.commit z :=
  rfl

/-- **Knowledge soundness of the reduction composed with the openings, with the Merkle
extractor, in the random-oracle model, at the sizes of `quotient::protocol`.** For every
adversary making at most `Q` queries of the random oracle `H : bytes → 32 bytes` that outputs a
statement, the two roots, the five values and the openings, and every openings' verifier of at
most `QV` queries whose three doomed events (each opening accepts while every candidate of its
root's decoded word violates one of its claims) have probabilities at most `εW`, `εσ`, `εQ`: the
verifier accepts while no table the extractor returns holds a witness of the statement with
probability at most `εW + εσ + εQ + (Q + 6 + QV) (2^-128 + 4 (Q + 6 + QV) / 2^256)`. -/
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
        4 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) :=
  knowledgeSoundness_composed_bits W c₁.commit c₂.commit hq hN hw hd h₁ h₂ A openings Q QV hQ hV
    εW εσ εQ hW hσ hQd

/-- **The same with the certified lists** (`WhirBridge.candidates_ours`: at most `7908` witness and
`3564` quotient candidates per root) and identities of degree at most `2^29`: the reduction's part
is `(Q + 6 + QV) (2^-138 + 4 (Q + 6 + QV) / 2^256)`. -/
theorem knowledgeSoundness_merkle_certified (hq : Fintype.card F = 2 ^ 192)
    (hN : P.nCells = 2 ^ 24) (hw : P.words = 8) (hd : B.identity ≤ 2 ^ 29)
    (c₁ : TableCode B.Msg₁) (c₂ : TableCode B.Msg₂) (h₁ : c₁.bound ≤ 7908)
    (h₂ : c₂.bound ≤ 3564)
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
      εW + εσ + εQ + ((Q + 6 + QV : ℕ) : ℝ≥0∞) * (((1 / 2 ^ 138 : ℝ≥0) : ℝ≥0∞) +
        4 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  refine (knowledgeSoundness_composed W c₁.commit c₂.commit A openings Q QV hQ hV εW εσ εQ hW hσ
    hQd).trans ?_
  gcongr
  exact listError_le_certified hq hN hw hd h₁ h₂

end Compose
