-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Pi1.Main
import RecGraph.Values

/-!
# The simulation's framework: π1-rec3's program against `UniStatement`'s verifier

For the pure permutation `π`, the IV, the public input and the stream (the section's variables), a recorder state
`st` gives each node a value (`val st i`, the recorded graph's evaluation, `evalAll`). The simulation relates:

* a node index and an element: `Rp st i x` (`i` is a node of `st`, worth `x`), lists pointwise (`RpL`);
* the recorder's state and `UniStatement`'s channel: `Couple st c` (the same stream, cursor and absorbed bytes, the
  channel's Keccak state the value of the recorder's state node, the zeros the values of the recorder's zero checks,
  the challenges the values of the recorder's challenge nodes, `chIds`), with the recorder's invariants (`Good`:
  `RecInv`, and the state node the newest hash, `Fresh`).

A pure step (`PStep st st'`: only arithmetic, the channel's fields unchanged) keeps `Couple`, and every `Rp` grows
with the state (`Rp.grow`). The channel's operations are coupled one by one: `nextScalar_couple`,
`nextInteger_couple`, `nextRoot_couple`, `sample_couple` (low or narrow), `requireZero_couple`. A component's lemma
then says: from `Couple st c` with enough bytes left, the program part's recording and the `UniStatement` function's
run end coupled, the bytes read the same, the outputs represented.
-/

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

/-! ## The program monad's laws, for `record` -/

theorem record_bind {α β : Type} (p : Prog α) (k : α → Prog β) (st : RecState) :
    (p >>= k).record st = (k (p.record st).1).record (p.record st).2 := by
  induction p generalizing st with
  | pure a => rfl
  | op o k' ih => exact ih _ _
  | zero v k' ih => exact ih _
  | nonzero v k' ih => exact ih _

theorem record_pure {α : Type} (a : α) (st : RecState) : (pure a : Prog α).record st = (a, st) := rfl

theorem record_op (o : Op) (st : RecState) : (Pi1.op o).record st = st.op o := rfl

/-! ## Challenge nodes and freshness -/

/-- A challenge node (`low`, `narrow`). -/
def isChal : Node → Bool
  | .low _ | .narrow _ => true
  | _ => false

/-- The challenge nodes, in creation order. -/
def chIds (st : RecState) : List Nat :=
  ((st.nodes.toList.zip (List.range st.nodes.size)).filter fun p ↦ isChal p.1).map (·.2)

/-- **The state node is the newest hash.** -/
def Fresh (st : RecState) : Prop :=
  ∀ (i : Nat) (h : i < st.nodes.size) (s f u : Nat), st.nodes[i] = .hash s f u → i ≤ st.state

/-- The recorder's invariants. -/
structure Good (st : RecState) : Prop where
  inv : RecInv st
  fresh : Fresh st

theorem chIds_push (st : RecState) (n : Node) (nodes : Array Node) (hn : nodes = st.nodes.push n)
    (st' : RecState) (h' : st'.nodes = nodes) :
    chIds st' = chIds st ++ (if isChal n then [st.nodes.size] else []) := by
  unfold chIds
  rw [h', hn, Array.toList_push, Array.size_push, List.range_succ, List.zip_append (by simp)]
  rw [List.filter_append, List.map_append]
  congr 1
  cases hc : isChal n <;> simp [hc]

section Values

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- A node's value in a recorder state. -/
def val (st : RecState) (i : Nat) : E := valE (evalAll π iv publicInput stream st) i

/-- **`i` represents `x`**: a node of `st`, worth `x`. -/
def Rp (st : RecState) (i : Nat) (x : E) : Prop := i < st.nodes.size ∧ val π iv publicInput stream st i = x

/-- Lists, pointwise. -/
def RpL (st : RecState) (is : List Nat) (xs : List E) : Prop := List.Forall₂ (Rp π iv publicInput stream st) is xs

theorem Grows.size_le {st st' : RecState} (h : Grows st st') : st.nodes.size ≤ st'.nodes.size := by
  obtain ⟨⟨ys, e⟩, _⟩ := h
  have := congrArg List.length e
  simp only [Array.length_toList, List.length_append] at this
  omega

/-- Values of the nodes held do not change as the state grows. -/
theorem val_grow {st st' : RecState} (hk : KInv st) (hg : Grows st st') {i : Nat} (hi : i < st.nodes.size) :
    val π iv publicInput stream st' i = val π iv publicInput stream st i := by
  unfold val valE
  rw [evalAll_grows π iv publicInput stream st st' hk hg i hi]

theorem Rp.grow {st st' : RecState} (hk : KInv st) (hg : Grows st st') {i : Nat} {x : E}
    (h : Rp π iv publicInput stream st i x) : Rp π iv publicInput stream st' i x :=
  ⟨lt_of_lt_of_le h.1 (Grows.size_le hg), by rw [val_grow π iv publicInput stream hk hg h.1]; exact h.2⟩

theorem RpL.grow {st st' : RecState} (hk : KInv st) (hg : Grows st st') {is : List Nat} {xs : List E}
    (h : RpL π iv publicInput stream st is xs) : RpL π iv publicInput stream st' is xs :=
  h.imp fun _ _ hr ↦ hr.grow π iv publicInput stream hk hg

/-- The state node's value as a Keccak state. -/
def stateVal (st : RecState) : Digest := valState (evalAll π iv publicInput stream st) st.state

/-- **The recorder and `UniStatement`'s channel, coupled.** -/
structure Couple (st : RecState) (c : Chan) : Prop where
  good : Good st
  data : c.data = stream
  cursor : c.cursor = st.cursor
  absorbed : c.absorbed = st.absorbed
  state : c.state = stateVal π iv publicInput stream st
  zeroLt : ∀ z ∈ st.zero.toList, z < st.nodes.size
  zeros : c.zeros.toList = st.zero.toList.map (val π iv publicInput stream st)
  chal : c.challenges.toList = (chIds st).map (val π iv publicInput stream st)

/-- **A pure step**: the recorder's invariants kept, the state grown, the channel's fields and the challenge nodes
unchanged. -/
structure PStep (st st' : RecState) : Prop where
  good : Good st'
  grows : Grows st st'
  cursor : st'.cursor = st.cursor
  absorbed : st'.absorbed = st.absorbed
  state : st'.state = st.state
  zero : st'.zero = st.zero
  chal : chIds st' = chIds st

theorem PStep.refl (st : RecState) (h : Good st) : PStep st st := ⟨h, Grows.refl st, rfl, rfl, rfl, rfl, rfl⟩

theorem PStep.trans {a b c : RecState} (h1 : PStep a b) (h2 : PStep b c) : PStep a c :=
  ⟨h2.good, h1.grows.trans h2.grows, h2.cursor.trans h1.cursor, h2.absorbed.trans h1.absorbed,
    h2.state.trans h1.state, h2.zero.trans h1.zero, h2.chal.trans h1.chal⟩

/-- **A pure step keeps the coupling.** -/
theorem Couple.pstep {st st' : RecState} {c : Chan} (hc : Couple π iv publicInput stream st c) (h : PStep st st') :
    Couple π iv publicInput stream st' c := by
  have hk := hc.good.inv.kinv
  refine ⟨h.good, hc.data, hc.cursor.trans h.cursor.symm, hc.absorbed.trans h.absorbed.symm, ?_, ?_, ?_, ?_⟩
  · rw [hc.state, stateVal, stateVal, h.state]
    have hs := hc.good.inv.state
    unfold valState
    rw [evalAll_grows π iv publicInput stream st st' hk h.grows _ hs]
  · intro z hz
    rw [h.zero] at hz
    exact lt_of_lt_of_le (hc.zeroLt z hz) (Grows.size_le h.grows)
  · rw [hc.zeros, h.zero]
    exact List.map_congr_left fun z hz ↦ (val_grow π iv publicInput stream hk h.grows (hc.zeroLt z hz)).symm
  · rw [hc.chal, h.chal]
    refine List.map_congr_left fun i hi ↦ (val_grow π iv publicInput stream hk h.grows ?_).symm
    unfold chIds at hi
    simp only [List.mem_map, List.mem_filter] at hi
    obtain ⟨⟨n, j⟩, ⟨hm, _⟩, rfl⟩ := hi
    exact List.mem_range.mp (List.of_mem_zip hm).2

end Values

end RecGraph.Sim
