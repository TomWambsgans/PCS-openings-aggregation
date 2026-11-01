-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/Spec.lean. MIT OR Apache-2.0; see NOTICE.md.
import ArkLib.OracleReduction.Security.RoundByRound
import QuotientSecurity.RoundOne
import QuotientSecurity.RoundTwo
import QuotientSecurity.RoundThree
import QuotientSecurity.Degrees

/-!
# The reduction as an interactive proof with ideal commitments

Six moves: the first message, the triple `(α, β, γ)`, the second message, `t`, the five values,
`ρ`. A commitment is ideal: the message is the polynomials themselves, and the verifier's four
claims are checked against them, which is `Params.Accepts`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp ProtocolSpec

namespace QuotientSecurity

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable (P : Params F) (B : P.Bounds)
variable {ι : Type} (oSpec : OracleSpec ι)

/-- The six moves. -/
@[reducible]
def pSpec : ProtocolSpec 6 :=
  ⟨!v[.P_to_V, .V_to_P, .P_to_V, .V_to_P, .P_to_V, .V_to_P],
    !v[B.Msg₁, F × F × F, B.Msg₂, F, (Fin 4 → F) × F, F]⟩

instance : ∀ i, SampleableType ((pSpec P B).Challenge i)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => (inferInstance : SampleableType (F × F × F))
  | ⟨2, h⟩ => nomatch h
  | ⟨3, _⟩ => (inferInstance : SampleableType F)
  | ⟨4, h⟩ => nomatch h
  | ⟨5, _⟩ => (inferInstance : SampleableType F)

open Classical in
/-- The verifier: it accepts when its four claims are true of the messages. -/
noncomputable def verifier : Verifier oSpec (Fin P.words → F) Bool (pSpec P B) where
  verify := fun stmt tr =>
    let g : B.Msg₁ := tr 0
    let c : F × F × F := tr 1
    let R : B.Msg₂ := tr 2
    let t : F := tr 3
    let v : (Fin 4 → F) × F := tr 4
    let ρ : F := tr 5
    pure (decide (P.Accepts stmt g.1 R.1 c.1 c.2.1 c.2.2 t v.1 v.2 ρ))

/-- The relation proved: the cells satisfy the gates, the copies and the public words. -/
def relIn : Set ((Fin P.words → F) × (P.T × Fin 4 → F)) := { p | P.Sat p.1 p.2 }

namespace Params

variable {P} {B}

/-- The states of the proof, after the first message, the first challenge, the second message,
the second challenge, and the last one. A state is true when the prover can still win. -/
def State₁ (stmt : Fin P.words → F) (g : B.Msg₁) : Prop := P.Sat stmt (P.cells g.1)

def State₂ (stmt : Fin P.words → F) (g : B.Msg₁) (c : F × F × F) : Prop :=
  State₁ stmt g ∨ ∃ R : B.Msg₂, P.Consistent stmt g.1 R.1 c.1 c.2.1 c.2.2

def State₃ (stmt : Fin P.words → F) (g : B.Msg₁) (c : F × F × F) (R : B.Msg₂) : Prop :=
  State₁ stmt g ∨ P.Consistent stmt g.1 R.1 c.1 c.2.1 c.2.2

def State₄ (stmt : Fin P.words → F) (g : B.Msg₁) (c : F × F × F) (R : B.Msg₂) (t : F) : Prop :=
  State₃ stmt g c R ∨ P.ConsistentAt stmt g.1 R.1 c.1 c.2.1 c.2.2 t

def State₆ (stmt : Fin P.words → F) (g : B.Msg₁) (c : F × F × F) (R : B.Msg₂) (t : F)
    (v : (Fin 4 → F) × F) (ρ : F) : Prop :=
  State₄ stmt g c R t ∨ P.Accepts stmt g.1 R.1 c.1 c.2.1 c.2.2 t v.1 v.2 ρ

end Params

open Params

/-- The extractor reads the cells off the first message. -/
noncomputable def extractor : Extractor.RoundByRound oSpec (Fin P.words → F)
    (P.T × Fin 4 → F) Unit (pSpec P B) (fun _ => P.T × Fin 4 → F) where
  eqIn := rfl
  extractMid := fun m _ tr w =>
    match m, tr with
    | ⟨0, _⟩, tr => P.cells (show B.Msg₁ from tr ⟨0, Nat.zero_lt_one⟩).1
    | _, _ => w
  extractOut := fun _ tr _ => P.cells (show B.Msg₁ from tr 0).1

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- The knowledge state function. -/
noncomputable def stateFun : (m : Fin 7) → (Fin P.words → F) → Transcript m (pSpec P B) →
    (P.T × Fin 4 → F) → Prop
  | ⟨0, _⟩ => fun stmt _ w => P.Sat stmt w
  | ⟨1, _⟩ => fun stmt tr _ => State₁ stmt (show B.Msg₁ from tr 0)
  | ⟨2, _⟩ => fun stmt tr _ => State₂ stmt (show B.Msg₁ from tr 0) (show F × F × F from tr 1)
  | ⟨3, _⟩ => fun stmt tr _ =>
      State₃ stmt (show B.Msg₁ from tr 0) (show F × F × F from tr 1) (show B.Msg₂ from tr 2)
  | ⟨4, _⟩ => fun stmt tr _ =>
      State₄ stmt (show B.Msg₁ from tr 0) (show F × F × F from tr 1) (show B.Msg₂ from tr 2)
        (show F from tr 3)
  | ⟨5, _⟩ => fun stmt tr _ =>
      State₄ stmt (show B.Msg₁ from tr 0) (show F × F × F from tr 1) (show B.Msg₂ from tr 2)
        (show F from tr 3)
  | ⟨6, _⟩ => fun stmt tr _ =>
      State₆ stmt (show B.Msg₁ from tr 0) (show F × F × F from tr 1) (show B.Msg₂ from tr 2)
        (show F from tr 3) (show (Fin 4 → F) × F from tr 4) (show F from tr 5)

/-- The state function is a knowledge state function for the verifier and the extractor. -/
noncomputable def knowledgeStateFunction :
    (verifier P B oSpec).KnowledgeStateFunction init impl (relIn P) acceptRejectRel
      (extractor P B oSpec) where
  toFun := stateFun P B
  toFun_empty := fun _ _ => Iff.rfl
  toFun_next := fun m hm stmt tr msg w h => by
    match m, hm, tr, msg, h with
    | ⟨0, _⟩, _, tr, msg, h => exact h
    | ⟨1, _⟩, hm, _, _, _ => exact Direction.noConfusion (show Direction.V_to_P = Direction.P_to_V from hm)
    | ⟨2, _⟩, _, tr, msg, h =>
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨_, h⟩
    | ⟨3, _⟩, hm, _, _, _ => exact Direction.noConfusion (show Direction.V_to_P = Direction.P_to_V from hm)
    | ⟨4, _⟩, _, tr, msg, h => exact h
    | ⟨5, _⟩, hm, _, _, _ => exact Direction.noConfusion (show Direction.V_to_P = Direction.P_to_V from hm)
  toFun_full := fun stmt tr witOut h => by
    rw [gt_iff_lt, OracleComp.OptionT.prEvent_mk_pos_iff] at h
    obtain ⟨x, hx, hRel⟩ := h
    simp only [Verifier.run, verifier, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    erw [simulateQ_pure] at hx
    simp only [StateT.run'_eq, StateT.run_pure, map_pure, support_pure,
      Set.mem_singleton_iff, Option.some.injEq] at hx
    subst x
    refine Or.inr ?_
    simp only [acceptRejectRel, Set.mem_singleton_iff, Prod.mk.injEq, decide_eq_true_eq] at hRel
    exact hRel.1

end QuotientSecurity
