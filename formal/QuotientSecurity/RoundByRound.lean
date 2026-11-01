-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/RoundByRound.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Spec

/-!
# Round-by-round knowledge soundness

The three challenges' bounds, as the round-by-round knowledge soundness of the verifier, in the
worst case over the transcript before each challenge.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp ProtocolSpec NNReal Finset

namespace QuotientSecurity

theorem card_div_le {A b q k : ℕ} (hq : 0 < q) (h : A ≤ b * q ^ k) :
    (A : ENNReal) / ((q ^ (k + 1) : ℕ) : ENNReal) ≤ (((b : ℝ≥0) / (q : ℝ≥0) : ℝ≥0) : ENNReal) := by
  have hq0 : (q : ℝ≥0) ≠ 0 := by exact_mod_cast hq.ne'
  have hqE : (q : ENNReal) ≠ 0 := by exact_mod_cast hq.ne'
  rw [ENNReal.coe_div hq0]
  push_cast
  calc (A : ENNReal) / (q : ENNReal) ^ (k + 1)
      ≤ ((b : ENNReal) * (q : ENNReal) ^ k) / (q : ENNReal) ^ (k + 1) := by
        gcongr
        exact_mod_cast h
    _ = (b : ENNReal) / (q : ENNReal) := by
        rw [pow_succ, mul_comm ((q : ENNReal) ^ k) (q : ENNReal)]
        exact ENNReal.mul_div_mul_right _ _ (pow_ne_zero _ hqE)
          (ENNReal.pow_ne_top (ENNReal.natCast_ne_top q))

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable (P : Params F) (B : P.Bounds)
variable {ι : Type} (oSpec : OracleSpec ι)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

open Params

/-- The error of each challenge: the copy argument, the degree of the identities, and three. -/
noncomputable def rbrError : (pSpec P B).ChallengeIdx → ℝ≥0
  | ⟨⟨1, _⟩, _⟩ => ((2 * P.nCells ^ 2 + 4 * P.nCells + P.words : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0)
  | ⟨⟨3, _⟩, _⟩ => ((B.identity : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0)
  | _ => ((3 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0)

open Classical in
theorem prob_first (stmt : Fin P.words → F) (g : B.Msg₁) :
    Pr{let c ← $ᵗ (F × F × F)}[¬ State₁ stmt g ∧ State₂ stmt g c]
      ≤ (((2 * P.nCells ^ 2 + 4 * P.nCells + P.words : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0) := by
  rw [SampleableType.prEvent_uniformSample]
  have hcard : (Fintype.card (F × F × F) : ENNReal) = ((Fintype.card F ^ (2 + 1) : ℕ) : ENNReal) := by
    rw [Fintype.card_prod, Fintype.card_prod]; push_cast; ring
  rw [hcard]
  refine card_div_le Fintype.card_pos ?_
  by_cases hs : State₁ stmt g
  · simp [hs]
  · refine le_trans (Finset.card_le_card fun c hc => ?_) (P.card_consistent_le stmt g.1 hs)
    rw [Finset.mem_filter] at hc ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hc.2.2 with h | ⟨R, hR⟩
    · exact absurd h hs
    · exact ⟨R.1, hR⟩

open Classical in
theorem prob_second (stmt : Fin P.words → F) (g : B.Msg₁) (c : F × F × F) (R : B.Msg₂) :
    Pr{let t ← $ᵗ F}[¬ State₃ stmt g c R ∧ State₄ stmt g c R t]
      ≤ (((B.identity : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0) := by
  rw [SampleableType.prEvent_uniformSample]
  have hcard : (Fintype.card F : ENNReal) = ((Fintype.card F ^ (0 + 1) : ℕ) : ENNReal) := by simp
  rw [hcard]
  refine card_div_le Fintype.card_pos ?_
  rw [pow_zero, mul_one]
  by_cases hs : State₃ stmt g c R
  · simp [hs]
  · have hcons : ¬ P.Consistent stmt g.1 R.1 c.1 c.2.1 c.2.2 := fun h => hs (Or.inr h)
    refine le_trans (Finset.card_le_card fun t ht => ?_)
      ((P.card_consistentAt_le stmt g.1 R.1 c.1 c.2.1 c.2.2 hcons).trans
        (max_le (natDegree_copyDefect_le B g R _ _ _) (natDegree_gateDefect_le B g R _ _)))
    rw [Finset.mem_filter] at ht ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases ht.2.2 with h | h
    · exact absurd h hs
    · exact h

open Classical in
theorem prob_third (stmt : Fin P.words → F) (g : B.Msg₁) (c : F × F × F) (R : B.Msg₂) (t : F)
    (v : (Fin 4 → F) × F) :
    Pr{let ρ ← $ᵗ F}[¬ State₄ stmt g c R t ∧ State₆ stmt g c R t v ρ]
      ≤ (((3 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0) := by
  rw [SampleableType.prEvent_uniformSample]
  have hcard : (Fintype.card F : ENNReal) = ((Fintype.card F ^ (0 + 1) : ℕ) : ENNReal) := by simp
  rw [hcard]
  refine card_div_le Fintype.card_pos ?_
  rw [pow_zero, mul_one]
  by_cases hs : State₄ stmt g c R t
  · simp [hs]
  · have hat : ¬ P.ConsistentAt stmt g.1 R.1 c.1 c.2.1 c.2.2 t := fun h => hs (Or.inr h)
    refine le_trans (Finset.card_le_card fun ρ hρ => ?_)
      (P.card_accepts_le stmt g.1 R.1 c.1 c.2.1 c.2.2 t hat v.1 v.2)
    rw [Finset.mem_filter] at hρ ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hρ.2.2 with h | h
    · exact absurd h hs
    · exact h

set_option maxHeartbeats 4000000 in
/-- **Round-by-round knowledge soundness.** With ideal commitments, the verifier of
`flock::quotient` is round-by-round knowledge sound for the relation "the cells satisfy every gate,
every copy and the public words", the extractor reading the cells off the first message. -/
theorem verifier_rbrKnowledgeSoundness :
    (verifier P B oSpec).rbrKnowledgeSoundness init impl (relIn P) acceptRejectRel
      (rbrError P B) := by
  apply Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness
  refine ⟨_, extractor P B oSpec, knowledgeStateFunction P B oSpec init impl, ?_⟩
  intro stmt i tr
  match i, tr with
  | ⟨⟨0, _⟩, h⟩, _ => exact Direction.noConfusion (show Direction.P_to_V = Direction.V_to_P from h)
  | ⟨⟨1, _⟩, _⟩, tr =>
    refine le_trans (prEvent_mono _ _ _ ?_) (prob_first P B stmt (show B.Msg₁ from tr ⟨0, by simp⟩))
    rintro c ⟨w, h1, h2⟩
    exact ⟨h1, h2⟩
  | ⟨⟨2, _⟩, h⟩, _ => exact Direction.noConfusion (show Direction.P_to_V = Direction.V_to_P from h)
  | ⟨⟨3, _⟩, _⟩, tr =>
    refine le_trans (prEvent_mono _ _ _ ?_) (prob_second P B stmt (show B.Msg₁ from tr ⟨0, by simp⟩)
      (show F × F × F from tr ⟨1, by simp⟩) (show B.Msg₂ from tr ⟨2, by simp⟩))
    rintro t ⟨w, h1, h2⟩
    exact ⟨h1, h2⟩
  | ⟨⟨4, _⟩, h⟩, _ => exact Direction.noConfusion (show Direction.P_to_V = Direction.V_to_P from h)
  | ⟨⟨5, _⟩, _⟩, tr =>
    refine le_trans (prEvent_mono _ _ _ ?_) (prob_third P B stmt (show B.Msg₁ from tr ⟨0, by simp⟩)
      (show F × F × F from tr ⟨1, by simp⟩) (show B.Msg₂ from tr ⟨2, by simp⟩) (show F from tr ⟨3, by simp⟩)
      (show (Fin 4 → F) × F from tr ⟨4, by simp⟩))
    rintro ρ ⟨w, h1, h2⟩
    exact ⟨h1, h2⟩

end QuotientSecurity
