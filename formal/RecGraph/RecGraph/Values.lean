-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Commute
import LeanVM.Parameters.Field
import Mathlib.Algebra.CharP.Two

/-!
# The smart constructors' values

`Sym`'s operations do not always make the node they name: two constants fold, a zero or a one is dropped, `x + x` is
zero, the operands are ordered, and a node already recorded is found by the index (hash-consing). Here: whatever
the operation returns has, in the recorded graph's evaluation, the value of the operation on its operands' values.
For a recorder state with the invariant `RecInv` (the index names only nodes it holds; every node reads only nodes
before it, a ring weight a kernel the state holds) and operands it holds:

* `constant_val`: `Scalar::constant(x)`'s node is `x` (`E`'s limbs rebuild it);
* `add_val`: `a + b` is `val a + val b` (`x + x = 0`: characteristic 2);
* `mul_val`: `a * b` is `val a * val b`;
* `new_val`: any node `n` (found or appended) has the value `stepNode` gives `n` on the state's values: so `input`,
  `sample` (the hash, then its challenge), `statement`, `bits` and `ringWeight` have their nodes' meaning;
* `new_inv`, `constant_inv`, `add_inv`, `mul_inv` keep the invariant, and the index returned names a node held.

With `Commute.lean`'s `run_vals`, a verifier written as a `Prog` computes on `E` exactly what its recorded graph does.
-/

namespace RecGraph

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement

instance : LawfulHashable Node := ⟨fun {a b} h ↦ by rw [eq_of_beq h]⟩

section Values

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

theorem evalP_size (K : Array (List Nat)) (vals : Array Value) (ns : List Node) :
    (evalP π iv publicInput stream K vals ns).size = vals.size + ns.length := by
  induction ns generalizing vals with
  | nil => simp [evalP]
  | cons n ns ih => simp only [evalP, ih, Array.size_push, List.length_cons]; omega

/-- Evaluation only appends. -/
theorem evalP_prefix (K : Array (List Nat)) (vals : Array Value) (ns : List Node) (j : Nat) (hj : j < vals.size) :
    (evalP π iv publicInput stream K vals ns)[j]? = vals[j]? := by
  induction ns generalizing vals with
  | nil => rfl
  | cons n ns ih =>
    simp only [evalP]
    rw [ih _ (by simp; omega), Array.getElem?_push]
    simp [Nat.ne_of_lt hj]

/-- What a node reads: its operands, and a ring weight its kernel's entries. -/
def reads (K : Array (List Nat)) : Node → List Nat
  | .ringWeight k _ => K.getD k []
  | n => n.operands

theorem valE_congr {P V : Array Value} {j : Nat} (h : P[j]? = V[j]?) : valE P j = valE V j := by
  simp only [valE, h]

theorem valState_congr {P V : Array Value} {j : Nat} (h : P[j]? = V[j]?) : valState P j = valState V j := by
  simp only [valState, h]

/-- A node's value depends on the values it reads only. -/
theorem stepP_local (K : Array (List Nat)) (P V : Array Value) (n : Node) (i : Nat)
    (hr : ∀ a ∈ reads K n, a < i) (hag : ∀ j < i, P[j]? = V[j]?) :
    stepP π iv publicInput stream K P n = stepP π iv publicInput stream K V n := by
  have e : ∀ a ∈ reads K n, P[a]? = V[a]? := fun a ha ↦ hag a (hr a ha)
  cases n with
  | add a b =>
    simp only [reads, Node.operands, List.mem_cons, List.mem_nil_iff, or_false] at e
    simp only [stepP, stepNode, valE_congr (e a (Or.inl rfl)), valE_congr (e b (Or.inr rfl))]
  | mul a b =>
    simp only [reads, Node.operands, List.mem_cons, List.mem_nil_iff, or_false] at e
    simp only [stepP, stepNode, valE_congr (e a (Or.inl rfl)), valE_congr (e b (Or.inr rfl))]
  | hash s fr upto =>
    simp only [reads, Node.operands, List.mem_cons, List.mem_nil_iff, or_false] at e
    simp only [stepP, stepNode, valState_congr (e s rfl)]
  | low h =>
    simp only [reads, Node.operands, List.mem_cons, List.mem_nil_iff, or_false] at e
    simp only [stepP, stepNode, valState_congr (e h rfl)]
  | narrow h =>
    simp only [reads, Node.operands, List.mem_cons, List.mem_nil_iff, or_false] at e
    simp only [stepP, stepNode, valState_congr (e h rfl)]
  | bits v s w =>
    simp only [reads, Node.operands, List.mem_cons, List.mem_nil_iff, or_false] at e
    simp only [stepP, stepNode, valE_congr (e v rfl)]
  | ringWeight k m =>
    simp only [reads] at e
    simp only [stepP, stepNode]
    rw [List.map_congr_left fun a ha ↦ valE_congr (e a ha)]
  | const => rfl
  | statement => rfl
  | input => rfl
  | seed => rfl

/-- The value of node `i` of a list: its step on the values before it. -/
theorem evalP_get (K : Array (List Nat)) (ns : List Node) (i : Nat) (hi : i < ns.length) :
    (evalP π iv publicInput stream K #[] ns)[i]? =
      some (stepP π iv publicInput stream K (evalP π iv publicInput stream K #[] (ns.take i)) ns[i]) := by
  have hsplit : ns = ns.take i ++ ns[i] :: ns.drop (i + 1) := by
    simp
  conv_lhs => rw [hsplit, evalP_append]
  simp only [evalP]
  have hsize : (evalP π iv publicInput stream K #[] (ns.take i)).size = i := by
    rw [evalP_size]; simp; omega
  rw [evalP_prefix _ _ _ _ _ _ _ i (by simp [hsize]), Array.getElem?_push]
  simp [hsize]

/-- The values before node `i` are the whole list's. -/
theorem evalP_take_agree (K : Array (List Nat)) (ns : List Node) (i : Nat) (hi : i ≤ ns.length) (j : Nat)
    (hj : j < i) :
    (evalP π iv publicInput stream K #[] (ns.take i))[j]? = (evalP π iv publicInput stream K #[] ns)[j]? := by
  conv_rhs => rw [← List.take_append_drop i ns, evalP_append]
  rw [evalP_prefix π iv publicInput stream K (evalP π iv publicInput stream K #[] (ns.take i)) (ns.drop i) j
    (by rw [evalP_size]; simp; omega)]

/-- **The recorder's invariant**: the index names only nodes the state holds at that index; every node reads only
nodes before it; every ring weight reads a kernel the state holds. -/
structure RecInv (st : RecState) : Prop where
  index : ∀ (n : Node) (i : Nat), st.index[n]? = some i → st.nodes[i]? = some n
  before : ∀ (i : Nat) (h : i < st.nodes.size), ∀ a ∈ reads st.kernels st.nodes[i], a < i
  kinv : KInv st
  state : st.state < st.nodes.size

theorem evalAll_size (st : RecState) : (evalAll π iv publicInput stream st).size = st.nodes.size := by
  simp [evalAll, evalP_size]

/-- **A node's value** in a state with the invariant: its step on the state's values. -/
theorem evalAll_node (st : RecState) (h : RecInv st) (i : Nat) (hi : i < st.nodes.size) :
    (evalAll π iv publicInput stream st)[i]? =
      some (stepP π iv publicInput stream st.kernels (evalAll π iv publicInput stream st) st.nodes[i]) := by
  have hi' : i < st.nodes.toList.length := by simpa using hi
  rw [evalAll, evalP_get _ _ _ _ _ _ _ hi']
  congr 1
  simp only [Array.getElem_toList]
  apply stepP_local _ _ _ _ _ _ _ _ i (h.before i hi)
  intro j hj
  exact evalP_take_agree _ _ _ _ _ _ _ (by omega) j hj

/-- The values of a grown state extend the state's. -/
theorem evalAll_grows (st st' : RecState) (hk : KInv st) (hg : Grows st st') (j : Nat) (hj : j < st.nodes.size) :
    (evalAll π iv publicInput stream st')[j]? = (evalAll π iv publicInput stream st)[j]? := by
  rw [← extend_evalAll π iv publicInput stream st st' hk hg, Prog.extend, evalList_eq, evalP_prefix]
  rw [evalAll_size]; exact hj

/-- **`Sym::new(n)`'s value**: found or appended, its node's step on the state's values. -/
theorem new_val (st : RecState) (h : RecInv st) (n : Node) (_hn : ∀ a ∈ reads st.kernels n, a < st.nodes.size) :
    (evalAll π iv publicInput stream (st.new n).2)[(st.new n).1]? =
      some (stepP π iv publicInput stream st.kernels (evalAll π iv publicInput stream st) n) := by
  unfold RecState.new
  split
  · rename_i i hidx
    have hn' := h.index n i hidx
    have hi : i < st.nodes.size := by
      rcases Nat.lt_or_ge i st.nodes.size with hlt | hge
      · exact hlt
      · simp [Array.getElem?_eq_none hge] at hn'
    rw [evalAll_node π iv publicInput stream st h i hi]
    have : st.nodes[i] = n := by
      rw [Array.getElem?_eq_getElem hi] at hn'
      exact Option.some.inj hn'
    rw [this]
  · simp only [evalAll, Array.toList_push, evalP_append, evalP]
    rw [Array.getElem?_push]
    have hs : st.nodes.size = (evalP π iv publicInput stream st.kernels #[] st.nodes.toList).size := by
      rw [evalP_size]; simp
    simp [← hs]

/-- **`Sym::new(n)` keeps the invariant**, for a node reading only held nodes and a held kernel. -/
theorem new_inv (st : RecState) (h : RecInv st) (n : Node) (hn : ∀ a ∈ reads st.kernels n, a < st.nodes.size)
    (hk : ∀ k, readsKernel n k → k < st.kernels.size) : RecInv (st.new n).2 := by
  unfold RecState.new
  split
  · exact h
  · rename_i hnone
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro n' i hi
      simp only [Std.HashMap.getElem?_insert] at hi
      split at hi
      · rename_i heq
        have : n = n' := eq_of_beq heq
        subst this
        cases hi
        simp
      · have h' := h.index n' i hi
        have hlt : i < st.nodes.size := by
          rcases Nat.lt_or_ge i st.nodes.size with hlt | hge
          · exact hlt
          · simp [Array.getElem?_eq_none hge] at h'
        rw [Array.getElem?_push]
        simp [Nat.ne_of_lt hlt, h']
    · intro i hi a ha
      simp only [Array.size_push] at hi
      rcases Nat.lt_or_ge i st.nodes.size with hlt | hge
      · have : (st.nodes.push n)[i] = st.nodes[i] := Array.getElem_push_lt hlt
        simp only [this] at ha
        exact h.before i hlt a ha
      · have hieq : i = st.nodes.size := by omega
        subst hieq
        simp only [Array.getElem_push_eq] at ha
        exact hn a ha
    · have hk' := new_kinv st n h.kinv hk
      simp only [RecState.new, hnone] at hk'
      exact hk'
    · have := h.state
      simp only [Array.size_push]
      omega

/-- The index `Sym::new(n)` returns names a node of the new state. -/
theorem new_lt (st : RecState) (h : RecInv st) (n : Node) : (st.new n).1 < (st.new n).2.nodes.size := by
  unfold RecState.new
  split
  · rename_i i hidx
    have hn' := h.index n i hidx
    rcases Nat.lt_or_ge i st.nodes.size with hlt | hge
    · exact hlt
    · simp [Array.getElem?_eq_none hge] at hn'
  · simp

/-- `Sym::new` grows the state's nodes. -/
theorem new_size (st : RecState) (n : Node) : st.nodes.size ≤ (st.new n).2.nodes.size := by
  unfold RecState.new
  split
  · exact le_refl _
  · simp

/-- A constant's value: `E`'s limbs rebuild it. -/
theorem eNew_limbs (x : E) : eNew (x.limb 0).lane (x.limb 1).lane (x.limb 2).lane = x := ofLimbs_limb x

/-- **`Scalar::constant(x)`'s value is `x`.** -/
theorem constant_val (st : RecState) (h : RecInv st) (x : E) :
    valE (evalAll π iv publicInput stream (st.constant x).2) (st.constant x).1 = x := by
  unfold RecState.constant
  rw [valE, new_val π iv publicInput stream st h _ (by simp [reads, Node.operands])]
  simp [stepP, stepNode, eNew_limbs]

theorem constant_inv (st : RecState) (h : RecInv st) (x : E) : RecInv (st.constant x).2 :=
  new_inv st h _ (by simp [reads, Node.operands]) fun _ ⟨_, e⟩ ↦ by cases e

/-- A node the state calls a constant has that value. -/
theorem constAt_val (st : RecState) (h : RecInv st) (a : Nat) (x : E) (hc : st.constAt a = some x) :
    valE (evalAll π iv publicInput stream st) a = x := by
  unfold RecState.constAt at hc
  split at hc
  · rename_i c0 c1 c2 hnode
    cases hc
    have ha : a < st.nodes.size := by
      rcases Nat.lt_or_ge a st.nodes.size with hlt | hge
      · exact hlt
      · simp [Array.getElem?_eq_none hge] at hnode
    have : st.nodes[a] = .const c0 c1 c2 := by
      rw [Array.getElem?_eq_getElem ha] at hnode
      exact Option.some.inj hnode
    rw [valE, evalAll_node π iv publicInput stream st h a ha, this]
    rfl
  · cases hc

theorem add_self_E (x : E) : x + x = 0 := CharTwo.add_self_eq_zero x

/-- **`Sym + Sym`'s value** is the sum of its operands' values (a fold, a dropped zero, `x + x = 0`, a new or a found
node). -/
theorem add_val (st : RecState) (h : RecInv st) (a b : Nat) (ha : a < st.nodes.size) (hb : b < st.nodes.size) :
    valE (evalAll π iv publicInput stream (st.add a b).2) (st.add a b).1 =
      valE (evalAll π iv publicInput stream st) a + valE (evalAll π iv publicInput stream st) b := by
  unfold RecState.add
  split
  · rename_i x y hx hy
    rw [constant_val π iv publicInput stream st h, constAt_val π iv publicInput stream st h a x hx,
      constAt_val π iv publicInput stream st h b y hy]
  · rename_i ca cb _
    split
    · rename_i h0
      rw [constAt_val π iv publicInput stream st h a 0 h0, zero_add]
    · split
      · rename_i _ h0
        rw [constAt_val π iv publicInput stream st h b 0 h0, add_zero]
      · split
        · rename_i _ _ hab
          subst hab
          rw [constant_val π iv publicInput stream st h, add_self_E]
        · rw [valE, new_val π iv publicInput stream st h _ (by
            simp only [reads, Node.operands, List.mem_cons, List.mem_nil_iff, or_false]
            rintro x (rfl | rfl) <;> omega)]
          simp only [stepP, stepNode, Id.run]
          rcases Nat.le_total a b with hab | hab
          · rw [Nat.min_eq_left hab, Nat.max_eq_right hab]; rfl
          · rw [Nat.min_eq_right hab, Nat.max_eq_left hab, add_comm (valE _ b) (valE _ a)]; rfl

theorem add_inv (st : RecState) (h : RecInv st) (a b : Nat) (ha : a < st.nodes.size) (hb : b < st.nodes.size) :
    RecInv (st.add a b).2 := by
  unfold RecState.add
  split
  · exact constant_inv st h _
  · split
    · exact h
    · split
      · exact h
      · split
        · exact constant_inv st h _
        · exact new_inv st h _ (by
            simp only [reads, Node.operands, List.mem_cons, List.mem_nil_iff, or_false]
            rintro x (rfl | rfl) <;> omega) fun _ ⟨_, e⟩ ↦ by cases e

/-- **`Sym * Sym`'s value** is the product of its operands' values (a fold, a zero that absorbs, a dropped one, a
new or a found node). -/
theorem mul_val (st : RecState) (h : RecInv st) (a b : Nat) (ha : a < st.nodes.size) (hb : b < st.nodes.size) :
    valE (evalAll π iv publicInput stream (st.mul a b).2) (st.mul a b).1 =
      valE (evalAll π iv publicInput stream st) a * valE (evalAll π iv publicInput stream st) b := by
  unfold RecState.mul
  split
  · rename_i x y hx hy
    rw [constant_val π iv publicInput stream st h, constAt_val π iv publicInput stream st h a x hx,
      constAt_val π iv publicInput stream st h b y hy]
  · rename_i ca cb _
    split
    · rename_i h0
      rw [constant_val π iv publicInput stream st h]
      rcases h0 with h0 | h0
      · rw [constAt_val π iv publicInput stream st h a 0 h0, zero_mul]
      · rw [constAt_val π iv publicInput stream st h b 0 h0, mul_zero]
    · split
      · rename_i _ h1
        rw [constAt_val π iv publicInput stream st h a 1 h1, one_mul]
      · split
        · rename_i _ _ h1
          rw [constAt_val π iv publicInput stream st h b 1 h1, mul_one]
        · rw [valE, new_val π iv publicInput stream st h _ (by
            simp only [reads, Node.operands, List.mem_cons, List.mem_nil_iff, or_false]
            rintro x (rfl | rfl) <;> omega)]
          simp only [stepP, stepNode, Id.run]
          rcases Nat.le_total a b with hab | hab
          · rw [Nat.min_eq_left hab, Nat.max_eq_right hab]; rfl
          · rw [Nat.min_eq_right hab, Nat.max_eq_left hab, mul_comm (valE _ b) (valE _ a)]; rfl

theorem mul_inv (st : RecState) (h : RecInv st) (a b : Nat) (ha : a < st.nodes.size) (hb : b < st.nodes.size) :
    RecInv (st.mul a b).2 := by
  unfold RecState.mul
  split
  · exact constant_inv st h _
  · split
    · exact constant_inv st h _
    · split
      · exact h
      · split
        · exact h
        · exact new_inv st h _ (by
            simp only [reads, Node.operands, List.mem_cons, List.mem_nil_iff, or_false]
            rintro x (rfl | rfl) <;> omega) fun _ ⟨_, e⟩ ↦ by cases e

/-- The recorder starts with the invariant. -/
theorem start_inv : RecInv RecState.start := by
  refine ⟨?_, ?_, start_kinv, by simp [RecState.start, RecState.new]⟩
  · intro n i hi
    simp only [RecState.start, RecState.new, Std.HashMap.getElem?_empty, Std.HashMap.getElem?_insert] at hi ⊢
    split at hi
    · rename_i heq
      have : Node.seed = n := eq_of_beq heq
      subst this
      cases hi
      simp
    · cases hi
  · intro i hi a ha
    have hn : RecState.start.nodes = #[Node.seed] := by simp [RecState.start, RecState.new]
    have h0 : i = 0 := by
      have hi' := hi
      rw [hn] at hi'
      simp at hi'
      omega
    subst h0
    have hs : RecState.start.nodes[0] = Node.seed := by simp [hn]
    simp only [hs] at ha
    simp [reads, Node.operands] at ha

/-! ### The channel's operations -/

/-- **`Recorder::input(len)`'s value**: the stream's `len` bytes at the cursor, read as `eval.rs` reads them. -/
theorem input_val (st : RecState) (h : RecInv st) (len : Nat) :
    (evalAll π iv publicInput stream (st.input len).2)[(st.input len).1]? =
      some (.elem (inputValue (stream.extract st.cursor (st.cursor + len)) len)) := by
  have := new_val π iv publicInput stream st h (.input st.cursor len) (by simp [reads, Node.operands])
  exact this

theorem input_inv (st : RecState) (h : RecInv st) (len : Nat) : RecInv (st.input len).2 := by
  have h' := new_inv st h (.input st.cursor len) (by simp [reads, Node.operands]) fun _ ⟨_, e⟩ ↦ by cases e
  exact ⟨h'.index, h'.before, h'.kinv, h'.state⟩

/-- **`Recorder::statement(k)`'s value**: the public input's word `k`. -/
theorem statement_val (st : RecState) (h : RecInv st) (k : Nat) :
    (evalAll π iv publicInput stream (st.statement k).2)[(st.statement k).1]? =
      some (.elem (eK (beWordAt publicInput.toArray (8 * k)))) :=
  new_val π iv publicInput stream st h (.statement k) (by simp [reads, Node.operands])

theorem statement_inv (st : RecState) (h : RecInv st) (k : Nat) : RecInv (st.statement k).2 :=
  new_inv st h (.statement k) (by simp [reads, Node.operands]) fun _ ⟨_, e⟩ ↦ by cases e

/-- The state after the hash of a sample: the hash's node is the new state, the bytes read are absorbed. -/
def afterHash (st : RecState) : RecState :=
  { (st.new (.hash st.state st.absorbed st.cursor)).2 with
    state := (st.new (.hash st.state st.absorbed st.cursor)).1,
    absorbed := (st.new (.hash st.state st.absorbed st.cursor)).2.cursor }

theorem afterHash_inv (st : RecState) (h : RecInv st) : RecInv (afterHash st) := by
  have h' := new_inv st h (.hash st.state st.absorbed st.cursor)
    (by simp only [reads, Node.operands, List.mem_singleton]; rintro a rfl; exact h.state)
    fun _ ⟨_, e⟩ ↦ by cases e
  exact ⟨h'.index, h'.before, h'.kinv, new_lt st h _⟩

/-- **The transcript's state after a sample**: the Keccak-256 over `π` of the state's bytes and the stream's bytes
read since the last challenge. -/
theorem afterHash_val (st : RecState) (h : RecInv st) :
    valState (evalAll π iv publicInput stream (afterHash st)) (afterHash st).state =
      Id.run (keccak256With (m := Id) (fun s ↦ pure (π s))
        (digestBytes (valState (evalAll π iv publicInput stream st) st.state) ++
          (stream.extract st.absorbed st.cursor).toList)) := by
  have := new_val π iv publicInput stream st h (.hash st.state st.absorbed st.cursor)
    (by simp only [reads, Node.operands, List.mem_singleton]; rintro a rfl; exact h.state)
  have e : evalAll π iv publicInput stream (afterHash st) =
      evalAll π iv publicInput stream (st.new (.hash st.state st.absorbed st.cursor)).2 := rfl
  rw [e]
  simp only [afterHash, valState, this]
  rfl

theorem sample_eq (st : RecState) (narrow : Bool) :
    st.sample narrow = (afterHash st).new (if narrow then .narrow (afterHash st).state else .low (afterHash st).state) :=
  rfl

/-- **`Recorder::sample`'s value** (`sample_narrow` with `narrow`): the challenge of the transcript's new state, cut
to 160 bits when narrow. -/
theorem sample_val (st : RecState) (h : RecInv st) (narrow : Bool) :
    valE (evalAll π iv publicInput stream (st.sample narrow).2) (st.sample narrow).1 =
      (if narrow then narrowE else id) (PcsQuotient.Transcript.challengeOf
        (valState (evalAll π iv publicInput stream (afterHash st)) (afterHash st).state)) := by
  have h1 := afterHash_inv st h
  rw [sample_eq, valE, new_val π iv publicInput stream (afterHash st) h1 _ (by
    split <;> simp only [reads, Node.operands, List.mem_singleton] <;> rintro a rfl <;> exact h1.state)]
  cases narrow <;> rfl

theorem sample_inv (st : RecState) (h : RecInv st) (narrow : Bool) : RecInv (st.sample narrow).2 := by
  have h1 := afterHash_inv st h
  rw [sample_eq]
  exact new_inv (afterHash st) h1 _ (by
    split <;> simp only [reads, Node.operands, List.mem_singleton] <;> rintro a rfl <;> exact h1.state)
    fun _ ⟨_, e⟩ ↦ by split at e <;> cases e

/-- A width past 64 masks nothing more (`Scalar::bits`), so the node's width cut to 255 means the same. -/
theorem bitsValue_min (x : E) (s w : Nat) : bitsValue x s (min w 255) = bitsValue x s w := by
  have e : min (min w 255) 64 = min w 64 := by omega
  simp only [bitsValue, intBits, e]

/-- **`Scalar::bits`' value**: `bits` of its operand's value (a constant folds). -/
theorem bits_val (st : RecState) (h : RecInv st) (v s w : Nat) (hv : v < st.nodes.size) :
    valE (evalAll π iv publicInput stream (st.bits v s w).2) (st.bits v s w).1 =
      bitsValue (valE (evalAll π iv publicInput stream st) v) s w := by
  unfold RecState.bits
  split
  · rename_i x hx
    rw [constant_val π iv publicInput stream st h, constAt_val π iv publicInput stream st h v x hx]
  · rw [valE, new_val π iv publicInput stream st h _ (by
      simp only [reads, Node.operands, List.mem_singleton]; rintro a rfl; exact hv), ← bitsValue_min]
    rfl

theorem bits_inv (st : RecState) (h : RecInv st) (v s w : Nat) (hv : v < st.nodes.size) :
    RecInv (st.bits v s w).2 := by
  unfold RecState.bits
  split
  · exact constant_inv st h _
  · exact new_inv st h _ (by simp only [reads, Node.operands, List.mem_singleton]; rintro a rfl; exact hv)
      fun _ ⟨_, e⟩ ↦ by cases e

/-- The state with a new kernel, before its ring-weight node. -/
def withKernel (st : RecState) (ops : List Nat) : RecState := { st with kernels := st.kernels.push ops }

theorem getD_push_lt (K : Array (List Nat)) (x : List Nat) (k : Nat) (hk : k < K.size) :
    (K.push x).getD k [] = K.getD k [] :=
  (getD_of_grows ⟨[x], by simp⟩ k hk).symm

theorem withKernel_evalAll (st : RecState) (h : RecInv st) (ops : List Nat) :
    evalAll π iv publicInput stream (withKernel st ops) = evalAll π iv publicInput stream st := by
  unfold evalAll withKernel
  refine evalP_kernels π iv publicInput stream _ _ _ _ fun n hn k hr ↦ ?_
  exact getD_push_lt _ _ k (h.kinv n hn k hr)

theorem withKernel_inv (st : RecState) (h : RecInv st) (ops : List Nat) : RecInv (withKernel st ops) := by
  refine ⟨h.index, ?_, ?_, h.state⟩
  · intro i hi a ha
    have hi' : i < st.nodes.size := hi
    have e : reads (st.kernels.push ops) st.nodes[i] = reads st.kernels st.nodes[i] := by
      cases hn : st.nodes[i] with
      | ringWeight k m =>
        have hk := h.kinv st.nodes[i] (by simp) k ⟨m, hn⟩
        simp only [reads, getD_push_lt _ _ k hk]
      | _ => rfl
    exact h.before i hi' a (by simpa [withKernel, e] using ha)
  · intro n hn k hr
    have := h.kinv n hn k hr
    simp only [withKernel, Array.size_push]
    omega

/-- **`Scalar::ring_weight`'s value**: `ring_tower::weight_at` of its operands' values. -/
theorem ringWeight_val (st : RecState) (h : RecInv st) (p o m : List Nat)
    (hops : ∀ a ∈ p ++ o ++ m, a < st.nodes.size) :
    valE (evalAll π iv publicInput stream (st.ringWeight p o m).2) (st.ringWeight p o m).1 =
      ringWeightValue ((p ++ o ++ m).map (valE (evalAll π iv publicInput stream st))) p.length := by
  have h1 := withKernel_inv st h (p ++ o ++ m)
  have hget : (withKernel st (p ++ o ++ m)).kernels.getD ((withKernel st (p ++ o ++ m)).kernels.size - 1) [] =
      p ++ o ++ m := by
    simp [withKernel]
  show valE (evalAll π iv publicInput stream ((withKernel st (p ++ o ++ m)).new
      (.ringWeight ((withKernel st (p ++ o ++ m)).kernels.size - 1) p.length)).2)
    ((withKernel st (p ++ o ++ m)).new (.ringWeight ((withKernel st (p ++ o ++ m)).kernels.size - 1) p.length)).1 = _
  rw [valE, new_val π iv publicInput stream _ h1 _ (by simp only [reads, hget]; exact hops),
    withKernel_evalAll π iv publicInput stream st h]
  simp only [stepP, stepNode, hget]
  rfl

theorem ringWeight_inv (st : RecState) (h : RecInv st) (p o m : List Nat)
    (hops : ∀ a ∈ p ++ o ++ m, a < st.nodes.size) : RecInv (st.ringWeight p o m).2 := by
  have h1 := withKernel_inv st h (p ++ o ++ m)
  have hget : (withKernel st (p ++ o ++ m)).kernels.getD ((withKernel st (p ++ o ++ m)).kernels.size - 1) [] =
      p ++ o ++ m := by
    simp [withKernel]
  show RecInv ((withKernel st (p ++ o ++ m)).new
      (.ringWeight ((withKernel st (p ++ o ++ m)).kernels.size - 1) p.length)).2
  exact new_inv _ h1 _ (by simp only [reads, hget]; exact hops) fun k ⟨_, e⟩ ↦ by
    cases e; simp [withKernel]

/-! ### Every operation -/

/-- **An operation's operands are held**: each index it reads names a node of the state. -/
def OpOK (st : RecState) : Op → Prop
  | .add a b | .mul a b => a < st.nodes.size ∧ b < st.nodes.size
  | .bits v _ _ => v < st.nodes.size
  | .ringWeight p o m => ∀ a ∈ p ++ o ++ m, a < st.nodes.size
  | _ => True

/-- **An operation's meaning on `E`**, on the values `vals` of the state's nodes: what its node must be worth. -/
def Op.value (st : RecState) (vals : Array Value) : Op → E
  | .constant x => x
  | .statement k => eK (beWordAt publicInput.toArray (8 * k))
  | .input len => inputValue (stream.extract st.cursor (st.cursor + len)) len
  | .sample narrow => (if narrow then narrowE else id) (PcsQuotient.Transcript.challengeOf
      (Id.run (keccak256With (m := Id) (fun s ↦ pure (π s))
        (digestBytes (valState vals st.state) ++ (stream.extract st.absorbed st.cursor).toList))))
  | .add a b => valE vals a + valE vals b
  | .mul a b => valE vals a * valE vals b
  | .bits v s w => bitsValue (valE vals v) s w
  | .ringWeight p o m => ringWeightValue ((p ++ o ++ m).map (valE vals)) p.length

/-- **Every operation's node has the operation's meaning** in the recorded graph's evaluation: the smart
constructors' folds, dropped zeros and ones, `x + x = 0` and hash-consed nodes included. -/
theorem op_val (st : RecState) (h : RecInv st) (o : Op) (hok : OpOK st o) :
    valE (evalAll π iv publicInput stream (st.op o).2) (st.op o).1 =
      Op.value π publicInput stream st (evalAll π iv publicInput stream st) o := by
  cases o with
  | constant x => exact constant_val π iv publicInput stream st h x
  | statement k => simp only [RecState.op, valE, statement_val π iv publicInput stream st h k, Op.value]
  | input len => simp only [RecState.op, valE, input_val π iv publicInput stream st h len, Op.value]
  | sample narrow =>
    simp only [RecState.op, Op.value]
    rw [sample_val π iv publicInput stream st h narrow, afterHash_val π iv publicInput stream st h]
  | add a b => exact add_val π iv publicInput stream st h a b hok.1 hok.2
  | mul a b => exact mul_val π iv publicInput stream st h a b hok.1 hok.2
  | bits v s w => exact bits_val π iv publicInput stream st h v s w hok
  | ringWeight p o m => exact ringWeight_val π iv publicInput stream st h p o m hok

/-- **Every operation keeps the invariant.** -/
theorem op_inv (st : RecState) (h : RecInv st) (o : Op) (hok : OpOK st o) : RecInv (st.op o).2 := by
  cases o with
  | constant x => exact constant_inv st h x
  | statement k => exact statement_inv st h k
  | input len => exact input_inv st h len
  | sample narrow => exact sample_inv st h narrow
  | add a b => exact add_inv st h a b hok.1 hok.2
  | mul a b => exact mul_inv st h a b hok.1 hok.2
  | bits v s w => exact bits_inv st h v s w hok
  | ringWeight p o m => exact ringWeight_inv st h p o m hok

/-- The index an operation returns names a node of the new state. -/
theorem op_lt (st : RecState) (h : RecInv st) (o : Op) (hok : OpOK st o) : (st.op o).1 < (st.op o).2.nodes.size := by
  cases o with
  | add a b =>
    show (st.add a b).1 < (st.add a b).2.nodes.size
    unfold RecState.add
    split
    · exact new_lt st h _
    · split
      · exact hok.2
      · split
        · exact hok.1
        · split
          · exact new_lt st h _
          · exact new_lt st h _
  | mul a b =>
    show (st.mul a b).1 < (st.mul a b).2.nodes.size
    unfold RecState.mul
    split
    · exact new_lt st h _
    · split
      · exact new_lt st h _
      · split
        · exact hok.2
        · split
          · exact hok.1
          · exact new_lt st h _
  | constant x => exact new_lt st h _
  | statement k => exact new_lt st h _
  | input len => exact new_lt st h _
  | sample narrow =>
    show (st.sample narrow).1 < (st.sample narrow).2.nodes.size
    rw [sample_eq]
    exact new_lt _ (afterHash_inv st h) _
  | bits v s w =>
    show (st.bits v s w).1 < (st.bits v s w).2.nodes.size
    unfold RecState.bits
    split
    · exact new_lt st h _
    · exact new_lt st h _
  | ringWeight p o m => exact new_lt _ (withKernel_inv st h (p ++ o ++ m)) _

/-- **A scoped program**: every operation it makes reads nodes already held, every check names one. -/
def Prog.Scoped {α : Type} : Prog α → RecState → Prop
  | .pure _, _ => True
  | .op o k, st => OpOK st o ∧ (k (st.op o).1).Scoped (st.op o).2
  | .zero v k, st => v < st.nodes.size ∧ k.Scoped { st with zero := st.zero.push v }
  | .nonzero v k, st => v < st.nodes.size ∧ k.Scoped { st with nonzero := st.nonzero.push v }

/-- **A scoped program keeps the invariant**: every operation of it then has its meaning (`op_val`). -/
theorem record_inv {α : Type} (p : Prog α) (st : RecState) (h : RecInv st) (hs : p.Scoped st) :
    RecInv (p.record st).2 := by
  induction p generalizing st with
  | pure a => exact h
  | op o k ih => exact ih _ _ (op_inv st h o hs.1) hs.2
  | zero v k ih => exact ih { st with zero := st.zero.push v } ⟨h.index, h.before, h.kinv, h.state⟩ hs.2
  | nonzero v k ih => exact ih { st with nonzero := st.nonzero.push v } ⟨h.index, h.before, h.kinv, h.state⟩ hs.2

end Values

end RecGraph
