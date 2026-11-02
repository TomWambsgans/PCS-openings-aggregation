-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.Witness

/-!
# The prover's setup is the deployment's

The honest prover recomputes the setup's trees from its trace (`setupTreesOf`, `setupStackOf`); the experiment
commits `setupStack D.prog D.shape` (`setupTreesWith`). On the placed trace of a witness they are the same stack:
the trace's 16 slots are the program's `tupleSlot`s, its addresses the same `g^i`.
-/

namespace UniComplete

open UniStatement LeanVM.Parameters

theorem honestTrace_shape (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    (honestTrace D input rows q).shape = D.shape := rfl

theorem honestTrace_slots_getD (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows)
    {s : ℕ} (hs : s < 16) :
    (honestTrace D input rows q).slots.getD s #[] =
      Array.ofFn (n := 2 ^ D.shape.logBytecode) fun i ↦
        if h : i.val < 2 ^ D.prog.logSize then tupleSlot D.prog ⟨i.val, h⟩ s else 0 := by
  simp [honestTrace, List.getD_eq_getElem?_getD, hs]

/-- **The prover's setup stack is the deployment's.** -/
theorem setupStackOf_honestTrace (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    setupStackOf (honestTrace D input rows q) = setupStack D.prog D.shape := by
  have hlb := D.logBytecode_eq
  unfold setupStackOf setupStack
  simp only [honestTrace_shape]
  congr 1
  funext w
  have hslot : ∀ s : Fin 16, bCoefficients D.shape.logBytecode ((honestTrace D input rows q).slots.getD s.val #[]) =
      bCoefficients D.prog.logSize (Array.ofFn (n := 2 ^ D.prog.logSize) fun i ↦ tupleSlot D.prog i s.val) := by
    intro s
    rw [honestTrace_slots_getD D input rows q s.isLt]
    revert hlb
    generalize D.shape.logBytecode = lb
    intro hlb
    subst hlb
    congr 1
    refine Array.ext (by simp) fun i h1 _ ↦ ?_
    simp only [Array.getElem_ofFn]
    rw [dif_pos (by simpa using h1)]
  simp only [addressColumn, hslot]
  rw [hlb]

end UniComplete
