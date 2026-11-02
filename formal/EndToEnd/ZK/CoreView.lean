-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The WHIR prover's arrays (`stackTableA`, `foldPairsW`, `roundC0A`, `roundC2A`, `powers`) are
-- leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0: `Statement/Prover/Whir.lean`,
-- `Statement/LeanVmVerifier.lean`).
import ZK.CoreViewWeights

/-!
# The openings' level-0 views are mumbai's arrays (`ViewW`, `ViewQ`)

The joint model's level-0 view of a secret table's opening (`Gadget.levelMap`: the lane rounds of the
batched weight against the lifted stack, the folded table `f¹`, the opened rows) against mumbai's WHIR
prover on the statement's arrays (`ZK/CoreSpec.lean`). With the stack table represented
(`stack_rep`, `ZK/CoreViewArrays.lean`) and the weight table represented (`weight_rep`,
`ZK/CoreViewWeights.lean`), the lane rounds are mumbai's round messages after the folds
(`laneRounds_arr`) and the folded table is mumbai's after the six folds (`foldAll_arr`, through
`foldAll_lift`):

* **`viewW`**: `Core.ViewW`, the witness opening (`40` lanes of `2^19`, the claim at `pointW c`);
* **`viewQ`**: `Core.ViewQ`, the quotient opening (`63` lanes of `2^22`, the claims at `pointQ` and
  `pointS`).
-/

open QuotientSecurity.Hiding
open LeanVM.Parameters LeanVM.Prover
open QuotientZk.Joint QuotientZk.Instance
open Primitives

namespace PcsQuotient.EndToEnd.Core

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

/-- **The witness opening's level-0 view is mumbai's arrays'.** -/
theorem viewW : ViewW := by
  intro c T A hT hA v Q _ _ enc
  dsimp only
  have hf : ArrRep 6 (2 ^ Lw.logLane) (stackTableA 25 A) (lift (E := E) Lw.pos T) :=
    stack_rep (P := 2 ^ 19) okW.lanes_le (by rw [logLane_W]) (by norm_num) (by rw [logLane_W])
      Lw.pos (fun _ => rfl) T A hT (by rw [hA, lanes_W])
  have hW := weight_rep sameLayout_W okW ![⟨pointW c, v⟩] [⟨pointW c, v⟩] (by simp)
    (fun _ => pointW c) (fun c' => by fin_cases c'; rfl)
    (fun _ => by rw [logLane_W, pointW, List.length_ofFn]; norm_num) (lam₁ c)
  refine ⟨fun j => laneRounds_arr 6 (phi₁ c) _ _ _ _ hW hf j, ?_⟩
  have hfold : (foldMap (HiddenLayout.foldW Lw.pos (phi₁ c)) T : YW → E) =
      foldAll 6 (phi₁ c) (lift Lw.pos T) :=
    funext fun y => (foldAll_lift Lw.pos (phi₁ c) T y).symm
  exact (congrArg Array.ofFn hfold).trans (foldAll_arr 6 (phi₁ c) _ _ hf)

/-- **The quotient opening's level-0 view is mumbai's arrays'.** -/
theorem viewQ : ViewQ := by
  intro c vals T A hT hA v₁ v₂ Q _ _ enc
  dsimp only
  have hf : ArrRep 6 (2 ^ Lq.logLane) (stackTableA 28 A) (lift (E := E) Lq.pos T) :=
    stack_rep (P := 2 ^ 22) okQ.lanes_le (by rw [logLane_Q]) (by norm_num) (by rw [logLane_Q])
      Lq.pos (fun _ => rfl) T A hT (by rw [hA, lanes_Q])
  have hW := weight_rep sameLayout_Q okQ
    ![⟨pointQ P₀D F192.Y c vals, v₁⟩, ⟨pointS F192.Y, v₂⟩]
    [⟨pointQ P₀D F192.Y c vals, v₁⟩, ⟨pointS F192.Y, v₂⟩] (by simp)
    ![pointQ P₀D F192.Y c vals, pointS F192.Y] (fun c' => by fin_cases c' <;> rfl)
    (fun c' => by
      fin_cases c'
      · show Lq.logLane ≤ (pointQ P₀D F192.Y c vals).length
        rw [logLane_Q, pointQ, List.length_ofFn]
        norm_num
      · show Lq.logLane ≤ (pointS F192.Y).length
        rw [logLane_Q, pointS, List.length_ofFn]
        norm_num) (lam₂ c)
  refine ⟨fun j => laneRounds_arr 6 (phi₂ c) _ _ _ _ hW hf j, ?_⟩
  have hfold : (foldMap (HiddenLayout.foldW Lq.pos (phi₂ c)) T : YQ → E) =
      foldAll 6 (phi₂ c) (lift Lq.pos T) :=
    funext fun y => (foldAll_lift Lq.pos (phi₂ c) T y).symm
  exact (congrArg Array.ofFn hfold).trans (foldAll_arr 6 (phi₂ c) _ _ hf)

/-- info: 'PcsQuotient.EndToEnd.Core.viewW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.viewW

/-- info: 'PcsQuotient.EndToEnd.Core.viewQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.Core.viewQ

end PcsQuotient.EndToEnd.Core
