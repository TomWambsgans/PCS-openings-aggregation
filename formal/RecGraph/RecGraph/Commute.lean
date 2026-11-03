-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Record

/-!
# Recording commutes with evaluation

For every program (`Prog`), pure permutation `π`, IV, public input and stream:

* `run_vals`: the values `Prog.run` computes as it records (each new node evaluated when it is made) are the
  recorded graph's (`evalAll`, which is `evalNodes` of the recorded graph: `evalAll_eq`), and `Prog.run` records
  what `Prog.record` records; the kernel invariant `KInv` holds throughout.
-/

namespace RecGraph

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement

section Proofs

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- A node's value over the pure permutation `π` (`stepNode` in `Id`). -/
def stepP (K : Array (List Nat)) (vals : Array Value) (n : Node) : Value :=
  Id.run (stepNode (m := Id) (fun s ↦ pure (π s)) K iv publicInput stream vals n)

/-- The values of a list of nodes after `vals` (`evalList` in `Id`). -/
def evalP (K : Array (List Nat)) : Array Value → List Node → Array Value
  | vals, [] => vals
  | vals, n :: ns => evalP K (vals.push (stepP π iv publicInput stream K vals n)) ns

/-- **The values of a recorder's nodes**: its graph's `evalNodes` over `π` (`evalAll_eq`). -/
def evalAll (st : RecState) : Array Value := evalP π iv publicInput stream st.kernels #[] st.nodes.toList

theorem evalList_eq (K : Array (List Nat)) (vals : Array Value) (ns : List Node) :
    Id.run (evalList (m := Id) (fun s ↦ pure (π s)) K iv publicInput stream vals ns) =
      evalP π iv publicInput stream K vals ns := by
  induction ns generalizing vals with
  | nil => rfl
  | cons n ns ih => exact ih _

/-- `evalAll` is the recorded graph's `evalNodes`. -/
theorem evalAll_eq (st : RecState) (calls : List (List Word)) (len : Nat) :
    Id.run (evalNodes (m := Id) (fun s ↦ pure (π s)) (st.graph calls len) iv publicInput stream) =
      evalAll π iv publicInput stream st :=
  evalList_eq π iv publicInput stream _ _ _

theorem evalP_append (K : Array (List Nat)) (vals : Array Value) (xs ys : List Node) :
    evalP π iv publicInput stream K vals (xs ++ ys) =
      evalP π iv publicInput stream K (evalP π iv publicInput stream K vals xs) ys := by
  induction xs generalizing vals with
  | nil => rfl
  | cons n ns ih => exact ih _

/-- The kernels a node reads, where it is a ring weight. -/
def readsKernel (n : Node) (k : Nat) : Prop := ∃ m, n = .ringWeight k m

/-- A node's value depends on the kernels it reads only. -/
theorem stepP_kernels (K K' : Array (List Nat)) (vals : Array Value) (n : Node)
    (h : ∀ k, readsKernel n k → K.getD k [] = K'.getD k []) :
    stepP π iv publicInput stream K vals n = stepP π iv publicInput stream K' vals n := by
  cases n with
  | ringWeight k m => simp only [stepP, stepNode, h k ⟨m, rfl⟩]
  | _ => rfl

theorem evalP_kernels (K K' : Array (List Nat)) (vals : Array Value) (ns : List Node)
    (h : ∀ n ∈ ns, ∀ k, readsKernel n k → K.getD k [] = K'.getD k []) :
    evalP π iv publicInput stream K vals ns = evalP π iv publicInput stream K' vals ns := by
  induction ns generalizing vals with
  | nil => rfl
  | cons n ns ih =>
    simp only [evalP]
    rw [stepP_kernels π iv publicInput stream K K' vals n (h n List.mem_cons_self)]
    exact ih _ fun n' hn' ↦ h n' (List.mem_cons_of_mem _ hn')

/-- **The kernel invariant**: every ring-weight node reads a kernel the state holds. -/
def KInv (st : RecState) : Prop := ∀ n ∈ st.nodes.toList, ∀ k, readsKernel n k → k < st.kernels.size

/-- **`st'` grows `st`**: its nodes and its kernels extend `st`'s. -/
def Grows (st st' : RecState) : Prop :=
  (∃ ys, st'.nodes.toList = st.nodes.toList ++ ys) ∧ (∃ ks, st'.kernels.toList = st.kernels.toList ++ ks)

theorem Grows.refl (st : RecState) : Grows st st := ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩

theorem Grows.trans {a b c : RecState} (h1 : Grows a b) (h2 : Grows b c) : Grows a c := by
  obtain ⟨⟨y1, e1⟩, ⟨k1, f1⟩⟩ := h1
  obtain ⟨⟨y2, e2⟩, ⟨k2, f2⟩⟩ := h2
  exact ⟨⟨y1 ++ y2, by rw [e2, e1, List.append_assoc]⟩, ⟨k1 ++ k2, by rw [f2, f1, List.append_assoc]⟩⟩

theorem getD_of_grows {K K' : Array (List Nat)} (h : ∃ ks, K'.toList = K.toList ++ ks) (k : Nat)
    (hk : k < K.size) : K.getD k [] = K'.getD k [] := by
  obtain ⟨ks, e⟩ := h
  have hk' : k < K'.size := by
    have := congrArg List.length e
    simp only [Array.length_toList, List.length_append] at this
    omega
  have : K'.toList[k]'(by simpa using hk') = K.toList[k]'(by simpa using hk) := by
    simp only [e]
    exact List.getElem_append_left (by simpa using hk)
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Array.getElem?_eq_getElem hk',
    Option.getD_some]
  simpa using this.symm

theorem new_grows (st : RecState) (n : Node) : Grows st (st.new n).2 := by
  unfold RecState.new
  split
  · exact Grows.refl st
  · exact ⟨⟨[n], by simp⟩, ⟨[], by simp⟩⟩

theorem new_kinv (st : RecState) (n : Node) (hk : KInv st) (hn : ∀ k, readsKernel n k → k < st.kernels.size) :
    KInv (st.new n).2 := by
  unfold RecState.new
  split
  · exact hk
  · intro n' hn' k hr
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hn'
    rcases hn' with hn' | rfl
    · exact hk n' hn' k hr
    · exact hn k hr

/-- A node that is no ring weight reads no kernel. -/
theorem noKernel {n : Node} (h : ∀ k m, n ≠ .ringWeight k m) (k : Nat) : ¬ readsKernel n k :=
  fun ⟨m, e⟩ ↦ h k m e

/-- Recording a node that reads no kernel grows the state and keeps the invariant. -/
theorem plain (st : RecState) (n : Node) (hk : KInv st) (hn : ∀ k m, n ≠ .ringWeight k m) :
    Grows st (st.new n).2 ∧ KInv (st.new n).2 :=
  ⟨new_grows st n, new_kinv st n hk fun k h ↦ absurd h (noKernel hn k)⟩

/-- **Every operation grows the state and keeps the kernel invariant.** -/
theorem op_grows_kinv (st : RecState) (o : Op) (hk : KInv st) : Grows st (st.op o).2 ∧ KInv (st.op o).2 := by
  cases o with
  | constant x => exact plain st _ hk fun _ _ h ↦ by cases h
  | statement k => exact plain st _ hk fun _ _ h ↦ by cases h
  | input len =>
    have h := plain st (.input st.cursor len) hk fun _ _ h ↦ by cases h
    exact ⟨⟨h.1.1, h.1.2⟩, h.2⟩
  | sample narrow =>
    have h1 := plain st (.hash st.state st.absorbed st.cursor) hk fun _ _ h ↦ by cases h
    have h2 := plain { (st.new (.hash st.state st.absorbed st.cursor)).2 with
        state := (st.new (.hash st.state st.absorbed st.cursor)).1,
        absorbed := (st.new (.hash st.state st.absorbed st.cursor)).2.cursor }
      (if narrow then .narrow (st.new (.hash st.state st.absorbed st.cursor)).1
        else .low (st.new (.hash st.state st.absorbed st.cursor)).1) h1.2
      fun _ _ h ↦ by split at h <;> cases h
    exact ⟨h1.1.trans h2.1, h2.2⟩
  | add a b =>
    simp only [RecState.op, RecState.add, RecState.constant]
    split
    · exact plain st _ hk fun _ _ h ↦ by cases h
    · split
      · exact ⟨Grows.refl st, hk⟩
      · split
        · exact ⟨Grows.refl st, hk⟩
        · split
          · exact plain st _ hk fun _ _ h ↦ by cases h
          · exact plain st _ hk fun _ _ h ↦ by cases h
  | mul a b =>
    simp only [RecState.op, RecState.mul, RecState.constant]
    split
    · exact plain st _ hk fun _ _ h ↦ by cases h
    · split
      · exact plain st _ hk fun _ _ h ↦ by cases h
      · split
        · exact ⟨Grows.refl st, hk⟩
        · split
          · exact ⟨Grows.refl st, hk⟩
          · exact plain st _ hk fun _ _ h ↦ by cases h
  | bits v s w =>
    simp only [RecState.op, RecState.bits, RecState.constant]
    split
    · exact plain st _ hk fun _ _ h ↦ by cases h
    · exact plain st _ hk fun _ _ h ↦ by cases h
  | ringWeight p o' m =>
    have g1 : Grows st { st with kernels := st.kernels.push (p ++ o' ++ m) } :=
      ⟨⟨[], by simp⟩, ⟨[p ++ o' ++ m], by simp⟩⟩
    have k1 : KInv { st with kernels := st.kernels.push (p ++ o' ++ m) } := fun n hn k hr ↦ by
      have := hk n hn k hr
      simp only [Array.size_push]; omega
    have h2 := new_kinv { st with kernels := st.kernels.push (p ++ o' ++ m) }
      (.ringWeight ((st.kernels.push (p ++ o' ++ m)).size - 1) p.length) k1 fun k ⟨_, e⟩ ↦ by
        cases e; simp
    exact ⟨g1.trans (new_grows _ _), h2⟩

/-- Extending a state's values by the nodes it grew is evaluating the grown state. -/
theorem extend_evalAll (st st' : RecState) (hk : KInv st) (hg : Grows st st') :
    Prog.extend π iv publicInput stream st' st.nodes.size (evalAll π iv publicInput stream st) =
      evalAll π iv publicInput stream st' := by
  obtain ⟨⟨ys, e⟩, hks⟩ := hg
  unfold Prog.extend evalAll
  rw [evalList_eq, e, evalP_append]
  have hdrop : (st.nodes.toList ++ ys).drop st.nodes.size = ys := by
    simp
  rw [hdrop, evalP_kernels π iv publicInput stream st'.kernels st.kernels #[] st.nodes.toList]
  intro n hn k hr
  exact (getD_of_grows hks k (hk n hn k hr)).symm

/-- **Recording commutes with evaluation**: for every program, pure permutation, IV, public input and stream,
`Prog.run` (the program on `E`, each node evaluated as it is made) computes the recorded graph's values (`evalAll`,
its `evalNodes`: `evalAll_eq`), records what `Prog.record` records, and keeps the kernel invariant. -/
theorem run_vals {α : Type} (p : Prog α) (st : RecState) (hk : KInv st) :
    (p.run π iv publicInput stream (st, evalAll π iv publicInput stream st)).2.2 =
        evalAll π iv publicInput stream (p.run π iv publicInput stream (st, evalAll π iv publicInput stream st)).2.1 ∧
      ((p.run π iv publicInput stream (st, evalAll π iv publicInput stream st)).1,
        (p.run π iv publicInput stream (st, evalAll π iv publicInput stream st)).2.1) = p.record st ∧
      KInv (p.run π iv publicInput stream (st, evalAll π iv publicInput stream st)).2.1 := by
  induction p generalizing st with
  | pure a => exact ⟨rfl, rfl, hk⟩
  | op o k ih =>
    obtain ⟨hg, hk'⟩ := op_grows_kinv st o hk
    simp only [Prog.run, Prog.record]
    rw [extend_evalAll π iv publicInput stream st _ hk hg]
    exact ih _ _ hk'
  | zero v k ih =>
    simp only [Prog.run, Prog.record]
    exact ih { st with zero := st.zero.push v } hk
  | nonzero v k ih =>
    simp only [Prog.run, Prog.record]
    exact ih { st with nonzero := st.nonzero.push v } hk

/-- The recorder starts with the kernel invariant (no kernel, one seed node). -/
theorem start_kinv : KInv RecState.start := by
  intro n hn k ⟨m, e⟩
  simp [RecState.start, RecState.new] at hn
  subst hn
  cases e

/-- **A program recorded from the start**: its graph's evaluation (`evalNodes` over `π`) is what `Prog.run` computes
on `E` from the start. -/
theorem record_eval {α : Type} (p : Prog α) (calls : List (List Word)) (len : Nat) :
    Id.run (evalNodes (m := Id) (fun s ↦ pure (π s)) ((p.record RecState.start).2.graph calls len) iv publicInput
        stream) =
      (p.run π iv publicInput stream (RecState.start, evalAll π iv publicInput stream RecState.start)).2.2 := by
  obtain ⟨h1, h2, _⟩ := run_vals π iv publicInput stream p RecState.start start_kinv
  rw [evalAll_eq, ← h2]
  exact h1.symm

end Proofs

end RecGraph
