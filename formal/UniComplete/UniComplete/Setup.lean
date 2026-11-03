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
open Lv42.Semantics (Program)

theorem honestTrace_shape (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    (honestTrace D input rows q).shape = D.shape := rfl

theorem honestTrace_slots_getD (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows)
    {s : ℕ} (hs : s < 16) :
    (honestTrace D input rows q).slots.getD s #[] =
      Array.ofFn (n := 2 ^ D.shape.logBytecode) fun i ↦
        if h : i.val < 2 ^ D.prog.logSize then tupleSlot D.prog ⟨i.val, h⟩ s else 0 := by
  simp [honestTrace, List.getD_eq_getElem?_getD, hs]

theorem bCoefficients_slot (prog : Program) (s lb : ℕ) (hlb : lb = prog.logSize) :
    bCoefficients lb (Array.ofFn (n := 2 ^ lb) fun i ↦
        if h : i.val < 2 ^ prog.logSize then tupleSlot prog ⟨i.val, h⟩ s else 0) =
      bCoefficients prog.logSize (Array.ofFn (n := 2 ^ prog.logSize) fun i ↦ tupleSlot prog i s) := by
  subst hlb
  congr 1
  refine Array.ext (by simp) fun i h1 _ ↦ ?_
  simp only [Array.getElem_ofFn]
  split_ifs with h
  · rfl
  · exact absurd (by simpa using h1) h

/-- The setup stack of a trace whose slots are the program's. -/
theorem setupStackOf_eq (tr : Trace) (prog : Program) (hlb : tr.shape.logBytecode = prog.logSize)
    (hslots : ∀ s < 16, tr.slots.getD s #[] = Array.ofFn (n := 2 ^ tr.shape.logBytecode) fun i ↦
        if h : i.val < 2 ^ prog.logSize then tupleSlot prog ⟨i.val, h⟩ s else 0) :
    setupStackOf tr = setupStack prog tr.shape := by
  have hs : ∀ s : Fin 16, bCoefficients tr.shape.logBytecode (tr.slots.getD s.val #[]) =
      bCoefficients prog.logSize (Array.ofFn (n := 2 ^ prog.logSize) fun i ↦ tupleSlot prog i s.val) := by
    intro s
    rw [hslots s s.isLt]
    exact bCoefficients_slot prog s.val _ hlb
  unfold setupStackOf setupStack
  simp only [addressColumn, hs]

/-- **The prover's setup stack is the deployment's.** -/
theorem setupStackOf_honestTrace (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    setupStackOf (honestTrace D input rows q) = setupStack D.prog D.shape :=
  setupStackOf_eq _ D.prog D.logBytecode_eq fun _ hs ↦ honestTrace_slots_getD D input rows q hs

end UniComplete

/-- info: 'UniComplete.setupStackOf_honestTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.setupStackOf_honestTrace
