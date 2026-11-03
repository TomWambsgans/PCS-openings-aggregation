-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.Basic

/-!
# The simulation's framework: the arithmetic operations

* `op_pstep`: an arithmetic operation (`constant`, `statement`, `add`, `mul`, `bits`, `ringWeight`) on held operands is
  a pure step, and its node represents the operation's value (`Op.value`).
* The channel's operations, coupled with `UniStatement`'s: `nextScalar_couple`, `nextInteger_couple`,
  `nextRoot_couple`, `sample_couple` (low or narrow), `requireZero_couple`; `takeBytes_run`.
* `Couple.step`: a step that only moves the cursor keeps the coupling, the channel's cursor moved with it.
-/

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

/-- The arithmetic operations: neither the channel nor a challenge. -/
def Op.Arith : Op → Prop
  | .constant _ | .statement _ | .add _ _ | .mul _ _ | .bits _ _ _ | .ringWeight _ _ _ => True
  | _ => False

theorem new_fields (st : RecState) (n : Node) :
    (st.new n).2.cursor = st.cursor ∧ (st.new n).2.absorbed = st.absorbed ∧ (st.new n).2.state = st.state ∧
      (st.new n).2.zero = st.zero := by
  unfold RecState.new
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- Recording a node that is no hash and no challenge keeps `Fresh` and the challenge nodes. -/
theorem new_fresh_chal (st : RecState) (n : Node) (hh : ∀ s f u, n ≠ .hash s f u) (hc : isChal n = false)
    (hf : Fresh st) : Fresh (st.new n).2 ∧ chIds (st.new n).2 = chIds st := by
  unfold RecState.new
  split
  · exact ⟨hf, rfl⟩
  · refine ⟨?_, ?_⟩
    · intro i hi s f u he
      simp only [Array.size_push] at hi
      rcases Nat.lt_or_ge i st.nodes.size with hlt | hge
      · have : (st.nodes.push n)[i] = st.nodes[i] := Array.getElem_push_lt hlt
        exact hf i hlt s f u (by rw [← this]; exact he)
      · have hieq : i = st.nodes.size := by omega
        subst hieq
        simp only [Array.getElem_push_eq] at he
        exact absurd he (hh s f u)
    · rw [chIds_push st n _ rfl _ rfl, hc]
      simp

section Ops

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- Recording an arithmetic node is a pure step. -/
theorem new_pstep (st : RecState) (n : Node) (hg : Good st) (hh : ∀ s f u, n ≠ .hash s f u)
    (hc : isChal n = false) (hr : ∀ a ∈ reads st.kernels n, a < st.nodes.size)
    (hk : ∀ k, readsKernel n k → k < st.kernels.size) : PStep st (st.new n).2 := by
  obtain ⟨h1, h2, h3, h4⟩ := new_fields st n
  obtain ⟨hf, hch⟩ := new_fresh_chal st n hh hc hg.fresh
  exact ⟨⟨new_inv st hg.inv n hr hk, hf⟩, new_grows st n, h1, h2, h3, h4, hch⟩

theorem noKernel' {n : Node} (h : ∀ k m, n ≠ .ringWeight k m) (k : Nat) : ¬ readsKernel n k :=
  fun ⟨m, e⟩ ↦ h k m e

/-- **An arithmetic operation on held operands**: a pure step, its node worth the operation's value. -/
theorem op_pstep (st : RecState) (hg : Good st) (o : Op) (ho : Op.Arith o) (hok : OpOK st o) :
    PStep st (st.op o).2 ∧
      Rp π iv publicInput stream (st.op o).2 (st.op o).1 (Op.value π publicInput stream st (evalAll π iv publicInput stream st) o) := by
  refine ⟨?_, op_lt st hg.inv o hok, op_val π iv publicInput stream st hg.inv o hok⟩
  have plain : ∀ n : Node, (∀ s f u, n ≠ .hash s f u) → isChal n = false →
      (∀ a ∈ reads st.kernels n, a < st.nodes.size) → (∀ k m, n ≠ .ringWeight k m) → PStep st (st.new n).2 :=
    fun n hh hc hr hk ↦ new_pstep st n hg hh hc hr fun k h ↦ absurd h (noKernel' hk k)
  have constOk : ∀ x : E, PStep st (st.constant x).2 := fun x ↦
    plain _ (fun _ _ _ h ↦ by cases h) rfl (by simp [reads, Node.operands]) (fun _ _ h ↦ by cases h)
  cases o with
  | constant x => exact constOk x
  | statement k => exact plain _ (fun _ _ _ h ↦ by cases h) rfl (by simp [reads, Node.operands]) (fun _ _ h ↦ by cases h)
  | add a b =>
    show PStep st (st.add a b).2
    unfold RecState.add
    split
    · exact constOk _
    · split
      · exact PStep.refl st hg
      · split
        · exact PStep.refl st hg
        · split
          · exact constOk _
          · exact plain _ (fun _ _ _ h ↦ by cases h) rfl (by
              simp only [reads, Node.operands, List.mem_cons, List.mem_nil_iff, or_false]
              have := hok.1; have := hok.2
              rintro x (rfl | rfl) <;> omega) (fun _ _ h ↦ by cases h)
  | mul a b =>
    show PStep st (st.mul a b).2
    unfold RecState.mul
    split
    · exact constOk _
    · split
      · exact constOk _
      · split
        · exact PStep.refl st hg
        · split
          · exact PStep.refl st hg
          · exact plain _ (fun _ _ _ h ↦ by cases h) rfl (by
              simp only [reads, Node.operands, List.mem_cons, List.mem_nil_iff, or_false]
              have := hok.1; have := hok.2
              rintro x (rfl | rfl) <;> omega) (fun _ _ h ↦ by cases h)
  | bits v s w =>
    show PStep st (st.bits v s w).2
    unfold RecState.bits
    split
    · exact constOk _
    · exact plain _ (fun _ _ _ h ↦ by cases h) rfl (by
        simp only [reads, Node.operands, List.mem_singleton]
        have : v < st.nodes.size := hok
        rintro x rfl; exact this) (fun _ _ h ↦ by cases h)
  | ringWeight p o' m =>
    have h1 := withKernel_inv st hg.inv (p ++ o' ++ m)
    have hget : (withKernel st (p ++ o' ++ m)).kernels.getD ((withKernel st (p ++ o' ++ m)).kernels.size - 1) [] =
        p ++ o' ++ m := by simp [withKernel]
    show PStep st ((withKernel st (p ++ o' ++ m)).new
      (.ringWeight ((withKernel st (p ++ o' ++ m)).kernels.size - 1) p.length)).2
    have hs := new_pstep (withKernel st (p ++ o' ++ m))
      (.ringWeight ((withKernel st (p ++ o' ++ m)).kernels.size - 1) p.length) ⟨h1, hg.fresh⟩
      (fun _ _ _ h ↦ by cases h) rfl (by simp only [reads, hget]; exact hok) fun k hk ↦ by
        obtain ⟨_, e⟩ := hk
        cases e
        simp [withKernel]
    have g0 : PStep st (withKernel st (p ++ o' ++ m)) :=
      ⟨⟨h1, hg.fresh⟩, ⟨⟨[], by simp [withKernel]⟩, ⟨[p ++ o' ++ m], by simp [withKernel]⟩⟩, rfl, rfl, rfl, rfl, rfl⟩
    exact g0.trans hs
  | input len => exact absurd ho id
  | sample narrow => exact absurd ho id

end Ops

end RecGraph.Sim
