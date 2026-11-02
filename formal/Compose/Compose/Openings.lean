-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Compose.ListChain

/-!
# The reduction composed with the openings

The deployed verifier (`quotient::protocol::verify`, then `verify_openings`) runs the reduction's
chain on the proof's two roots and five values, checks the one thing the reduction checks itself
(the product it inverts is not zero, `reductionCheck`), and hands four claims to three WHIR
openings: the **witness** claim to the witness table's root, the **wiring** claim to the circuit's
commitment, and the **two quotient** claims, together, to the quotient table's root
(`Params.Accepts` is exactly these, `accepts_iff`).

**The extractor** (`extractor`) reads the transcript of **every** Keccak-256 query of the run (the
adversary's, the chain's and the openings'; `AdversaryLog.lean`'s reads the adversary's only) and
the witness table's root,
and returns the root's candidate list (`ListCommit.cands`): the tables the root's word may stand
for. Knowledge soundness is broken (`Breaks`) when the verifier accepts while no candidate's cells
satisfy the relation for the statement. `extractorOne` picks the first satisfying candidate
(`breaksOne_iff`: the same event).

**The openings' guarantees**, each an event of the same experiment. These are **not** F2's events
literally: here the openings' verifier is any computation, the candidates are `merkleWord` and a
decoder rather than mumbai's `extract`, `Candidates` and `Layout.tableEval`, the claims are F1's
polynomial identities rather than `reduce`'s multilinear claims, and the word is read off the final
transcript rather than the cache at the end of the opening. They are reduced to F2's `ours_sound` for
the deployed openings in `Deployed.lean` (the witness and quotient terms; the wiring term remains):

* `WitnessDoomed`: the witness opening accepts while every candidate of its root violates the
  witness claim;
* `WiringDoomed`: the wiring opening accepts while the wiring claim is false (to be discharged once
  the experiment computes the circuit's commitment with the oracle, `Deployed.lean`'s `withSetup`:
  its only candidate is then the wiring table);
* `QuotientDoomed`: the quotient opening accepts while every candidate of its root violates one
  of the two quotient claims. **One opening holds both claims**: a candidate that is not doomed
  satisfies both (F2's `joint_of_not_doom`); split over two openings each claim would get its own
  candidate, and the reduction's last round would not bind them.

`breaks_imp`: a broken run has a doomed opening, or wins the list game of `ListChain.lean`.
**`knowledgeSoundness_composed`**: the probability that the verifier accepts while the extracted
list holds no witness of the statement is at most the three openings' terms plus
`(Q + 6 + QV) (max L₁ (L₁ L₂) · roundError + 4 (Q + 6 + QV) / 2^256)`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm QuotientSecurity QuotientSecurity.Params

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : Params F} {B : P.Bounds}

/-! ## The claims, table by table -/

/-- The witness claim: the four row polynomials of the witness table, combined with the weights
of `ρ`, at `t`, against the four values. -/
def witnessClaim (g : Witness F) (t ρ : F) (a : Fin 4 → F) : Prop :=
  ∑ j, opening ρ j * ((g j).comp rowPoly).eval t = ∑ j, opening ρ j * a j

variable (P) in
/-- The wiring claim: the wiring polynomial at `t` is the fifth value. -/
def wiringClaim (t s : F) : Prop := P.sigmaPoly.eval t = s

variable (P) in
/-- What the reduction checks itself: the product it inverts is not zero. -/
def reductionCheck (α β t : F) (a : Fin 4 → F) (s : F) : Prop :=
  let x := cellAt P a t 0
  let d := α + x + β * t
  let d' := α + x + β * s
  let den := d * d' + P.vCells.eval t
  den * P.vRows.eval t ≠ 0

variable (P) in
/-- The two quotient claims: the identities' combination at `t`, and the sum. -/
def quotientClaims (stmt : Fin P.words → F) (R : Quotients F) (α β γ t : F) (a : Fin 4 → F)
    (s ρ : F) : Prop :=
  let x := cellAt P a t 0
  let d := α + x + β * t
  let d' := α + x + β * s
  let gt := gate x (cellAt P a t 1) (cellAt P a t 2) (cellAt P a t 3)
  let copies := d + d' + (P.pub γ).eval t * x * (d * d')
  let den := d * d' + P.vCells.eval t
  let e := P.vCells.eval t / den
  (1 + ρ) * ((1 + e) * (R.h P).eval t + e * R.q.eval t)
        + ρ * ((1 + e) * R.qGate.eval t + e * R.junk.eval t)
      = ((1 + ρ) * copies * P.vRows.eval t + ρ * (d * d') * gt) / (den * P.vRows.eval t) ∧
    R.top P = P.target stmt γ

/-- **The verifier's decision is the four claims and its own check.** -/
theorem accepts_iff (stmt : Fin P.words → F) (g : Witness F) (R : Quotients F)
    (α β γ t : F) (a : Fin 4 → F) (s ρ : F) :
    P.Accepts stmt g R α β γ t a s ρ ↔ witnessClaim g t ρ a ∧ wiringClaim P t s ∧
      reductionCheck P α β t a s ∧ quotientClaims P stmt R α β γ t a s ρ :=
  Iff.rfl

/-! ## The deployed verifier and the extractor -/

/-- The three openings' verdicts: the witness table's, the wiring table's, the quotient
table's. -/
abbrev Verdicts := Bool × Bool × Bool

variable (W : Wire P B) (C₁ : ListCommit B.Msg₁) (C₂ : ListCommit B.Msg₂) {O : Type}

/-- **The verifier accepts** a run: its own check holds and the three openings accept. -/
def Accepted (z : Run F O Verdicts × Transcript) : Prop :=
  reductionCheck P z.1.chals.α z.1.chals.β z.1.chals.t z.1.proof.v.1 z.1.proof.v.2 ∧
    z.1.out = (true, true, true)

/-- **The extractor**: the candidates of the witness table's root, read off the transcript of every
query. It is as computable as the list commitment's `cands`. -/
def extractor (z : Run F O Verdicts × Transcript) : List B.Msg₁ :=
  C₁.cands (histOfTr z.2) (tableOfTr z.2) z.1.proof.r₁

/-- **Knowledge soundness is broken**: the verifier accepts while no extracted candidate's cells
satisfy the relation for the statement the proof's bytes stand for. -/
def Breaks (z : Run F O Verdicts × Transcript) : Prop :=
  Accepted (P := P) z ∧ ∀ g ∈ extractor C₁ z, ¬ P.Sat (W.decode z.1.proof.stmt) (P.cells g.1)

open Classical in
/-- The extractor that returns one witness: the first candidate whose cells satisfy the relation
(`noncomputable`: the cells are evaluations of `Polynomial`s). -/
noncomputable def extractorOne (z : Run F O Verdicts × Transcript) : Option B.Msg₁ :=
  (extractor C₁ z).find? fun g => decide (P.Sat (W.decode z.1.proof.stmt) (P.cells g.1))

/-- With the one-witness extractor, the same event. -/
theorem breaksOne_iff (z : Run F O Verdicts × Transcript) :
    (Accepted (P := P) z ∧ ¬ ∃ g, extractorOne W C₁ z = some g ∧
        P.Sat (W.decode z.1.proof.stmt) (P.cells g.1)) ↔ Breaks W C₁ z := by
  classical
  unfold Breaks extractorOne
  refine and_congr_right fun _ => ⟨fun h g hg hs => h ?_, fun h ⟨g, hg, hs⟩ => ?_⟩
  · cases hf : (extractor C₁ z).find? fun g => decide (P.Sat (W.decode z.1.proof.stmt)
        (P.cells g.1)) with
    | none =>
      exact absurd (decide_eq_true hs) (List.find?_eq_none.mp hf g hg)
    | some g' =>
      have hp := List.find?_some hf
      exact ⟨g', rfl, of_decide_eq_true hp⟩
  · exact h g (List.mem_of_find?_eq_some hg) hs

/-! ## The openings' guarantees -/

/-- The witness opening accepts while every candidate of the witness root violates the witness
claim. -/
def WitnessDoomed (z : Run F O Verdicts × Transcript) : Prop :=
  z.1.out.1 = true ∧ ∀ g ∈ extractor C₁ z,
    ¬ witnessClaim g.1 z.1.chals.t z.1.chals.ρ z.1.proof.v.1

/-- The wiring opening accepts while the wiring claim is false. -/
def WiringDoomed (z : Run F O Verdicts × Transcript) : Prop :=
  z.1.out.2.1 = true ∧ ¬ wiringClaim P z.1.chals.t z.1.proof.v.2

/-- The quotient opening accepts while every candidate of the quotient root violates one of the
two quotient claims. -/
def QuotientDoomed (z : Run F O Verdicts × Transcript) : Prop :=
  z.1.out.2.2 = true ∧ ∀ R ∈ C₂.cands (histOfTr z.2) (tableOfTr z.2) z.1.proof.r₂,
    ¬ quotientClaims P (W.decode z.1.proof.stmt) R.1 z.1.chals.α z.1.chals.β z.1.chals.γ
      z.1.chals.t z.1.proof.v.1 z.1.proof.v.2 z.1.chals.ρ

/-- **A broken run has a doomed opening, or wins the list game.** -/
theorem breaks_imp (z : Run F O Verdicts × Transcript) (h : Breaks W C₁ z) :
    WitnessDoomed C₁ z ∨ WiringDoomed (P := P) z ∨ QuotientDoomed W C₂ z ∨ ListWins W C₁ C₂ z := by
  obtain ⟨⟨hchk, hout⟩, hsat⟩ := h
  have h1 : z.1.out.1 = true := by rw [hout]
  have h2 : z.1.out.2.1 = true := by rw [hout]
  have h3 : z.1.out.2.2 = true := by rw [hout]
  by_contra hno
  simp only [not_or] at hno
  obtain ⟨hW, hσ, hQ, hL⟩ := hno
  have hW' : ∃ g ∈ extractor C₁ z, witnessClaim g.1 z.1.chals.t z.1.chals.ρ z.1.proof.v.1 := by
    by_contra hc
    push Not at hc
    exact hW ⟨h1, hc⟩
  have hσ' : wiringClaim P z.1.chals.t z.1.proof.v.2 := by
    by_contra hc
    exact hσ ⟨h2, hc⟩
  have hQ' : ∃ R ∈ C₂.cands (histOfTr z.2) (tableOfTr z.2) z.1.proof.r₂,
      quotientClaims P (W.decode z.1.proof.stmt) R.1 z.1.chals.α z.1.chals.β z.1.chals.γ
        z.1.chals.t z.1.proof.v.1 z.1.proof.v.2 z.1.chals.ρ := by
    by_contra hc
    push Not at hc
    exact hQ ⟨h3, hc⟩
  obtain ⟨g, hg, hgc⟩ := hW'
  obtain ⟨R, hR, hRc⟩ := hQ'
  exact hL ⟨g, hg, R, hR, (accepts_iff _ _ _ _ _ _ _ _ _ _).mpr ⟨hgc, hσ', hchk, hRc⟩,
    hsat g hg⟩

/-! ## Knowledge soundness -/

/-- **Knowledge soundness of the reduction composed with the openings, in the random-oracle
model.** For every adversary making at most `Q` queries of the random oracle
`H : bytes → 32 bytes` that outputs a statement, the two roots, the five values and the openings,
and every openings' verifier `openings` of at most `QV` queries: if the three openings' doomed
events have probabilities at most `εW`, `εσ`, `εQ` (each opening's soundness, F2's `family_sound`
for its seed), the verifier accepts while the extractor's list holds no witness of the statement
with probability at most `εW + εσ + εQ + (Q + 6 + QV) (max L₁ (L₁ L₂) · roundError +
4 (Q + 6 + QV) / 2^256)`. -/
theorem knowledgeSoundness_composed (A : OracleComp HashSpec (RootProof F × O))
    (openings : RootProof F × O → Chals F → OracleComp HashSpec Verdicts) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (openings p ch) QV)
    (εW εσ εQ : ℝ≥0∞)
    (hW : Pr{let z ← (simulateQ randomOracle (rootExperiment W A openings)).run' ∅}[
      WitnessDoomed C₁ z] ≤ εW)
    (hσ : Pr{let z ← (simulateQ randomOracle (rootExperiment W A openings)).run' ∅}[
      WiringDoomed (P := P) z] ≤ εσ)
    (hQd : Pr{let z ← (simulateQ randomOracle (rootExperiment W A openings)).run' ∅}[
      QuotientDoomed W C₂ z] ≤ εQ) :
    Pr{let z ← (simulateQ randomOracle (rootExperiment W A openings)).run' ∅}[Breaks W C₁ z] ≤
      εW + εσ + εQ + ((Q + 6 + QV : ℕ) : ℝ≥0∞) * ((listFactor C₁.bound C₂.bound : ℝ≥0∞) *
        (roundError P B : ℝ≥0∞) + 4 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  set mx := (simulateQ randomOracle (rootExperiment W A openings)).run' ∅
  have hL := knowledgeSoundness_list W C₁ C₂ A openings Q QV hQ hV
  refine (prEvent_mono mx _ _ (breaks_imp W C₁ C₂)).trans ?_
  refine (prEvent_or_le _ _ _).trans ?_
  refine (add_le_add hW ((prEvent_or_le _ _ _).trans (add_le_add hσ
    ((prEvent_or_le _ _ _).trans (add_le_add hQd hL))))).trans ?_
  simp only [add_assoc, le_refl]

end Compose
