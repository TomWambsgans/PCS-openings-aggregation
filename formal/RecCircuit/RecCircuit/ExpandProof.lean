-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCircuit.SoundRG
import RecCircuit.WeightSim

/-!
# The expansion keeps `RecGraph`'s meaning (`ExpandSound`, proved)

`compile.rs`'s `expand` replays π1's graph on the recorder's symbol (`RecGraph.RecState`, from `RecState.start`) with
every ring-switch weight computed on symbols (`weightSym`). On an accepted graph (`Graph.typed`: node 0 the seed,
every node reading earlier nodes, a hash or a challenge reading a state, a ring weight's map six stages), every
original node's image has the node's value in `RecGraph`'s semantics (`expandSound`), by induction over the original
nodes (`expandList_inv`), with the recorder's lemmas (`RecGraph.add_val`, `mul_val`, `bits_val`, `new_val`,
`constant_val`) and the symbolic weight's simulation (`weightSym_sim`, `weightAt_eq_tower`).

The invariant (`EInv`): the recorder keeps `RecInv`, holds no kernel, has the seed at node 0, and the image of every
node replayed denotes the node's element (`Rel`), the image of a state node having the node's value itself (a hash's
state operand is read by `valState`).
-/

namespace RecCircuit

open Primitives LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement
open RecGraph (RecState RecInv Grows evalAll evalP stepP valE valState)

/-! ## The recorder keeps its kernels -/

theorem new_kernels (st : RecState) (n : RecGraph.Node) : (st.new n).2.kernels = st.kernels := by
  unfold RecGraph.RecState.new
  split <;> rfl

theorem constant_kernels (st : RecState) (x : E) : (st.constant x).2.kernels = st.kernels := new_kernels st _

theorem add_kernels (st : RecState) (a b : ℕ) : (st.add a b).2.kernels = st.kernels := by
  unfold RecGraph.RecState.add
  split
  · exact constant_kernels st _
  · split
    · rfl
    · split
      · rfl
      · split
        · exact constant_kernels st _
        · exact new_kernels st _

theorem mul_kernels (st : RecState) (a b : ℕ) : (st.mul a b).2.kernels = st.kernels := by
  unfold RecGraph.RecState.mul
  split
  · exact constant_kernels st _
  · split
    · exact constant_kernels st _
    · split
      · rfl
      · split
        · rfl
        · exact new_kernels st _

theorem bits_kernels (st : RecState) (v s w : ℕ) : (st.bits v s w).2.kernels = st.kernels := by
  unfold RecGraph.RecState.bits
  split
  · exact constant_kernels st _
  · exact new_kernels st _

theorem grows_get {st st' : RecState} (hg : Grows st st') {a : ℕ} (ha : a < st.nodes.size) :
    st'.nodes[a]? = st.nodes[a]? := by
  obtain ⟨⟨ys, e⟩, _⟩ := hg
  have h1 : st'.nodes[a]? = st'.nodes.toList[a]? := by simp
  have h2 : st.nodes[a]? = st.nodes.toList[a]? := by simp
  rw [h1, h2, e, List.getElem?_append_left (by simpa using ha)]

theorem grows_size {st st' : RecState} (hg : Grows st st') : st.nodes.size ≤ st'.nodes.size := by
  obtain ⟨⟨ys, e⟩, _⟩ := hg
  have := congrArg List.length e
  simp only [Array.length_toList, List.length_append] at this
  omega

theorem valE_of {P Q : Array RecGraph.Value} {i j : ℕ} (h : P[i]? = Q[j]?) : valE P i = valE Q j := by
  simp only [RecGraph.valE, h]

theorem valState_of {P Q : Array RecGraph.Value} {i j : ℕ} (h : P[i]? = Q[j]?) : valState P i = valState Q j := by
  simp only [RecGraph.valState, h]

/-! ## The replay, one node -/

/-- `expandList`'s step. -/
theorem expandList_cons {K : Array (List ℕ)} {n : Node} {ns : List Node} {st : RecState} {map : Array ℕ}
    {res : RecState × Array ℕ} (h : expandList K (n :: ns) (st, map) = .ok res) :
    ∃ i st', expandNode K map st n = .ok (i, st') ∧ expandList K ns (st', map.push i) = .ok res := by
  simp only [expandList] at h
  cases he : expandNode K map st n with
  | error e => rw [he] at h; cases h
  | ok p =>
    rw [he] at h
    obtain ⟨i, st'⟩ := p
    exact ⟨i, st', rfl, h⟩

section Replay

variable (π : KeccakState → KeccakState) (iv pub : List UInt8) (stream : Array UInt8)

/-- The original graph's values, over `π` (`RecGraph.evalNodes`). -/
def origVals (g : RecGraph.Graph) : Array RecGraph.Value := evalP π iv pub stream g.kernels #[] g.nodes.toList

/-- **The replay's invariant** after the original nodes `0 .. j`. -/
structure EInv (g : RecGraph.Graph) (j : ℕ) (st : RecState) (map : Array ℕ) : Prop where
  inv : RecInv st
  kernels : st.kernels = #[]
  seed : st.nodes[0]? = some .seed
  size : map.size = j
  rel : ∀ a < j, Rel π iv pub stream st (map.getD a 0) (valE (origVals π iv pub stream g) a)
  state : ∀ a < j, (ofRGNode (g.nodes.getD a default)).isState = true →
    (evalAll π iv pub stream st)[map.getD a 0]? = (origVals π iv pub stream g)[a]?

/-- What one node's replay gives: the recorder grown with its invariant, the node's image denoting its element, a
state node's image its value. -/
structure Out (g : RecGraph.Graph) (j : ℕ) (st st' : RecState) (i : ℕ) : Prop where
  inv : RecInv st'
  grows : Grows st st'
  kernels : st'.kernels = st.kernels
  lt : i < st'.nodes.size
  val : valE (evalAll π iv pub stream st') i = valE (origVals π iv pub stream g) j
  state : (ofRGNode (g.nodes.getD j default)).isState = true →
    (evalAll π iv pub stream st')[i]? = (origVals π iv pub stream g)[j]?

variable {π iv pub stream}

/-- The original graph's node `j`: its step on the graph's values, its reads before it. -/
theorem orig_get {g : RecGraph.Graph} (hb : ∀ j (hj : j < g.nodes.size), ∀ a ∈ RecGraph.reads g.kernels g.nodes[j], a < j)
    {j : ℕ} (hj : j < g.nodes.size) :
    (origVals π iv pub stream g)[j]? =
      some (stepP π iv pub stream g.kernels (origVals π iv pub stream g) g.nodes[j]) := by
  have hj' : j < g.nodes.toList.length := by simpa using hj
  unfold origVals
  rw [RecGraph.evalP_get π iv pub stream _ _ _ hj']
  congr 1
  simp only [Array.getElem_toList]
  apply RecGraph.stepP_local π iv pub stream _ _ _ _ j (hb j hj)
  intro a ha
  exact RecGraph.evalP_take_agree π iv pub stream _ _ _ (by omega) a ha

theorem rel_grows {st st' : RecState} (h : RecInv st) (hg : Grows st st') {i : ℕ} {x : E}
    (hr : Rel π iv pub stream st i x) : Rel π iv pub stream st' i x := by
  refine ⟨lt_of_lt_of_le hr.1 (grows_size hg), ?_⟩
  rw [← hr.2]
  exact valE_of (RecGraph.evalAll_grows π iv pub stream st st' h.kinv hg i hr.1)

/-- The seed at node 0 denotes `0`. -/
theorem rel_seed {st : RecState} (h : RecInv st) (hs : st.nodes[0]? = some .seed) : Rel π iv pub stream st 0 0 := by
  have h0 : 0 < st.nodes.size := by
    rcases Nat.lt_or_ge 0 st.nodes.size with hlt | hge
    · exact hlt
    · simp [Array.getElem?_eq_none hge] at hs
  refine ⟨h0, ?_⟩
  have hn : st.nodes[0] = .seed := by
    rw [Array.getElem?_eq_getElem h0] at hs; exact Option.some.inj hs
  rw [RecGraph.valE, RecGraph.evalAll_node π iv pub stream st h 0 h0, hn]
  rfl

theorem valE_elem {V : Array RecGraph.Value} {j : ℕ} {x : E} (h : V[j]? = some (.elem x)) : valE V j = x := by
  simp only [RecGraph.valE, h]

theorem stepP_const (K : Array (List ℕ)) (vals : Array RecGraph.Value) (c0 c1 c2 : UInt64) :
    stepP π iv pub stream K vals (.const c0 c1 c2) = .elem (eNew c0 c1 c2) := rfl

theorem stepP_add (K : Array (List ℕ)) (vals : Array RecGraph.Value) (a b : ℕ) :
    stepP π iv pub stream K vals (.add a b) = .elem (valE vals a + valE vals b) := rfl

theorem stepP_mul (K : Array (List ℕ)) (vals : Array RecGraph.Value) (a b : ℕ) :
    stepP π iv pub stream K vals (.mul a b) = .elem (valE vals a * valE vals b) := rfl

theorem stepP_bits (K : Array (List ℕ)) (vals : Array RecGraph.Value) (v s w : ℕ) :
    stepP π iv pub stream K vals (.bits v s w) = .elem (RecGraph.bitsValue (valE vals v) s w) := rfl

theorem stepP_ringWeight (K : Array (List ℕ)) (vals : Array RecGraph.Value) (k n : ℕ) :
    stepP π iv pub stream K vals (.ringWeight k n) =
      .elem (RecGraph.ringWeightValue ((K.getD k []).map (valE vals)) n) := rfl

/-- A node reading nothing has one value whatever the kernels and the values before it. -/
theorem stepP_free (K K' : Array (List ℕ)) (P V : Array RecGraph.Value) (n : RecGraph.Node)
    (hr : RecGraph.reads K n = []) (hk : ∀ k, ¬ RecGraph.readsKernel n k) :
    stepP π iv pub stream K P n = stepP π iv pub stream K' V n :=
  (RecGraph.stepP_kernels π iv pub stream K K' P n fun k h => absurd h (hk k)).trans
    (RecGraph.stepP_local π iv pub stream K' P V n 0 (by
      intro a ha
      rw [show RecGraph.reads K' n = RecGraph.reads K n by
        cases n <;> first | rfl | exact absurd ⟨_, rfl⟩ (hk _), hr] at ha
      cases ha) fun _ h => absurd h (Nat.not_lt_zero _))

theorem getD_ofRG (g : RecGraph.Graph) {s : ℕ} (hs : s < g.nodes.size) :
    (g.nodes.map ofRGNode).getD s default = ofRGNode (g.nodes.getD s default) := by
  simp [Array.getD_eq_getD_getElem?, hs]

/-- **One node's replay** (`expandNode`) on the invariant: what it gives (`Out`). -/
theorem node_out {g : RecGraph.Graph} {G : Graph} (hG : G.nodes = g.nodes.map ofRGNode)
    (hK : G.kernels = g.kernels) {j : ℕ} (hj : j < g.nodes.size) {st : RecState} {map : Array ℕ}
    (hI : EInv π iv pub stream g j st map) {n : RecGraph.Node} (hn : g.nodes.getD j default = n)
    (htj : G.typedAt j (ofRGNode n) = true)
    (hV : (origVals π iv pub stream g)[j]? = some (stepP π iv pub stream g.kernels (origVals π iv pub stream g) n))
    {i : ℕ} {st' : RecState} (he : expandNode G.kernels map st (ofRGNode n) = .ok (i, st')) :
    Out π iv pub stream g j st st' i := by
  have hst : ∀ {a : ℕ}, a < j → (G.nodes.getD a default).isState = true →
      (evalAll π iv pub stream st)[map.getD a 0]? = (origVals π iv pub stream g)[a]? := by
    intro a ha hs
    rw [hG, getD_ofRG g (by omega)] at hs
    exact hI.state a ha hs
  have nst : (ofRGNode n).isState = false → (ofRGNode (g.nodes.getD j default)).isState = true →
      (evalAll π iv pub stream st')[i]? = (origVals π iv pub stream g)[j]? := by
    intro h1 h2; rw [hn, h1] at h2; cases h2
  cases n with
  | const c0 c1 c2 =>
    simp only [ofRGNode, expandNode, pure, Except.pure, Except.ok.injEq] at he
    obtain ⟨rfl, rfl⟩ : i = _ ∧ st' = _ := ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩
    refine ⟨RecGraph.constant_inv st hI.inv _, (RecGraph.op_grows_kinv st (.constant _) hI.inv.kinv).1,
      constant_kernels st _, RecGraph.op_lt st hI.inv (.constant _) trivial, ?_, nst rfl⟩
    rw [stepP_const] at hV
    rw [RecGraph.constant_val π iv pub stream st hI.inv, valE_elem hV]
  | statement k =>
    simp only [ofRGNode, expandNode, toRGNode, pure, Except.pure, Except.ok.injEq] at he
    obtain ⟨rfl, rfl⟩ : i = _ ∧ st' = _ := ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩
    have hopt : (evalAll π iv pub stream (st.new (.statement k)).2)[(st.new (.statement k)).1]? =
        (origVals π iv pub stream g)[j]? := by
      rw [RecGraph.new_val π iv pub stream st hI.inv _ (by simp [RecGraph.reads, RecGraph.Node.operands]), hV,
        stepP_free _ _ _ _ _ (by simp [RecGraph.reads, RecGraph.Node.operands]) (fun _ ⟨_, e⟩ => by cases e)]
    exact ⟨RecGraph.new_inv st hI.inv _ (by simp [RecGraph.reads, RecGraph.Node.operands]) (fun _ ⟨_, e⟩ => by
      cases e), RecGraph.new_grows st _, new_kernels st _, RecGraph.new_lt st hI.inv _, valE_of hopt, fun _ => hopt⟩
  | input o l =>
    simp only [ofRGNode, expandNode, toRGNode, pure, Except.pure, Except.ok.injEq] at he
    obtain ⟨rfl, rfl⟩ : i = _ ∧ st' = _ := ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩
    have hopt : (evalAll π iv pub stream (st.new (.input o l)).2)[(st.new (.input o l)).1]? =
        (origVals π iv pub stream g)[j]? := by
      rw [RecGraph.new_val π iv pub stream st hI.inv _ (by simp [RecGraph.reads, RecGraph.Node.operands]), hV,
        stepP_free _ _ _ _ _ (by simp [RecGraph.reads, RecGraph.Node.operands]) (fun _ ⟨_, e⟩ => by cases e)]
    exact ⟨RecGraph.new_inv st hI.inv _ (by simp [RecGraph.reads, RecGraph.Node.operands]) (fun _ ⟨_, e⟩ => by
      cases e), RecGraph.new_grows st _, new_kernels st _, RecGraph.new_lt st hI.inv _, valE_of hopt, fun _ => hopt⟩
  | seed =>
    simp only [ofRGNode, expandNode, toRGNode, pure, Except.pure, Except.ok.injEq] at he
    obtain ⟨rfl, rfl⟩ : i = _ ∧ st' = _ := ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩
    have hopt : (evalAll π iv pub stream (st.new .seed).2)[(st.new .seed).1]? =
        (origVals π iv pub stream g)[j]? := by
      rw [RecGraph.new_val π iv pub stream st hI.inv _ (by simp [RecGraph.reads, RecGraph.Node.operands]), hV,
        stepP_free _ _ _ _ _ (by simp [RecGraph.reads, RecGraph.Node.operands]) (fun _ ⟨_, e⟩ => by cases e)]
    exact ⟨RecGraph.new_inv st hI.inv _ (by simp [RecGraph.reads, RecGraph.Node.operands]) (fun _ ⟨_, e⟩ => by
      cases e), RecGraph.new_grows st _, new_kernels st _, RecGraph.new_lt st hI.inv _, valE_of hopt, fun _ => hopt⟩
  | add a b =>
    simp only [ofRGNode, Graph.typedAt, Bool.and_eq_true, decide_eq_true_eq] at htj
    have ha : a < j := htj.1.1.1
    have hb : b < j := htj.1.1.2
    simp only [ofRGNode, expandNode, pure, Except.pure, Except.ok.injEq] at he
    obtain ⟨rfl, rfl⟩ : i = _ ∧ st' = _ := ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩
    have ra := hI.rel a ha
    have rb := hI.rel b hb
    refine ⟨RecGraph.add_inv st hI.inv _ _ ra.1 rb.1, (RecGraph.op_grows_kinv st (.add _ _) hI.inv.kinv).1,
      add_kernels st _ _, RecGraph.op_lt st hI.inv (.add _ _) ⟨ra.1, rb.1⟩, ?_, nst rfl⟩
    rw [stepP_add] at hV
    rw [RecGraph.add_val π iv pub stream st hI.inv _ _ ra.1 rb.1, ra.2, rb.2, valE_elem hV]
  | mul a b =>
    simp only [ofRGNode, Graph.typedAt, Bool.and_eq_true, decide_eq_true_eq] at htj
    have ha : a < j := htj.1.1.1
    have hb : b < j := htj.1.1.2
    simp only [ofRGNode, expandNode, pure, Except.pure, Except.ok.injEq] at he
    obtain ⟨rfl, rfl⟩ : i = _ ∧ st' = _ := ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩
    have ra := hI.rel a ha
    have rb := hI.rel b hb
    refine ⟨RecGraph.mul_inv st hI.inv _ _ ra.1 rb.1, (RecGraph.op_grows_kinv st (.mul _ _) hI.inv.kinv).1,
      mul_kernels st _ _, RecGraph.op_lt st hI.inv (.mul _ _) ⟨ra.1, rb.1⟩, ?_, nst rfl⟩
    rw [stepP_mul] at hV
    rw [RecGraph.mul_val π iv pub stream st hI.inv _ _ ra.1 rb.1, ra.2, rb.2, valE_elem hV]
  | hash s f t =>
    simp only [ofRGNode, Graph.typedAt, Bool.and_eq_true, decide_eq_true_eq] at htj
    have hs : s < j := htj.1
    have hss := hst hs htj.2
    simp only [ofRGNode, expandNode, pure, Except.pure, Except.ok.injEq] at he
    obtain ⟨rfl, rfl⟩ : i = _ ∧ st' = _ := ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩
    have rs := hI.rel s hs
    have hr : ∀ a ∈ RecGraph.reads st.kernels (.hash (map.getD s 0) f t), a < st.nodes.size := by
      simp only [RecGraph.reads, RecGraph.Node.operands, List.mem_singleton]; rintro a rfl; exact rs.1
    have hopt : (evalAll π iv pub stream (st.new (.hash (map.getD s 0) f t)).2)[(st.new
        (.hash (map.getD s 0) f t)).1]? = (origVals π iv pub stream g)[j]? := by
      rw [RecGraph.new_val π iv pub stream st hI.inv _ hr, hV]
      simp only [RecGraph.stepP, RecGraph.stepNode, valState_of hss]
    exact ⟨RecGraph.new_inv st hI.inv _ hr (fun _ ⟨_, e⟩ => by cases e), RecGraph.new_grows st _,
      new_kernels st _, RecGraph.new_lt st hI.inv _, valE_of hopt, fun _ => hopt⟩
  | low h =>
    simp only [ofRGNode, Graph.typedAt, Bool.and_eq_true, decide_eq_true_eq] at htj
    have hs : h < j := htj.1
    have hss := hst hs htj.2
    simp only [ofRGNode, expandNode, pure, Except.pure, Except.ok.injEq] at he
    obtain ⟨rfl, rfl⟩ : i = _ ∧ st' = _ := ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩
    have rs := hI.rel h hs
    have hr : ∀ a ∈ RecGraph.reads st.kernels (.low (map.getD h 0)), a < st.nodes.size := by
      simp only [RecGraph.reads, RecGraph.Node.operands, List.mem_singleton]; rintro a rfl; exact rs.1
    have hopt : (evalAll π iv pub stream (st.new (.low (map.getD h 0))).2)[(st.new
        (.low (map.getD h 0))).1]? = (origVals π iv pub stream g)[j]? := by
      rw [RecGraph.new_val π iv pub stream st hI.inv _ hr, hV]
      simp only [RecGraph.stepP, RecGraph.stepNode, valState_of hss]
    exact ⟨RecGraph.new_inv st hI.inv _ hr (fun _ ⟨_, e⟩ => by cases e), RecGraph.new_grows st _,
      new_kernels st _, RecGraph.new_lt st hI.inv _, valE_of hopt, fun _ => hopt⟩
  | narrow h =>
    simp only [ofRGNode, Graph.typedAt, Bool.and_eq_true, decide_eq_true_eq] at htj
    have hs : h < j := htj.1
    have hss := hst hs htj.2
    simp only [ofRGNode, expandNode, pure, Except.pure, Except.ok.injEq] at he
    obtain ⟨rfl, rfl⟩ : i = _ ∧ st' = _ := ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩
    have rs := hI.rel h hs
    have hr : ∀ a ∈ RecGraph.reads st.kernels (.narrow (map.getD h 0)), a < st.nodes.size := by
      simp only [RecGraph.reads, RecGraph.Node.operands, List.mem_singleton]; rintro a rfl; exact rs.1
    have hopt : (evalAll π iv pub stream (st.new (.narrow (map.getD h 0))).2)[(st.new
        (.narrow (map.getD h 0))).1]? = (origVals π iv pub stream g)[j]? := by
      rw [RecGraph.new_val π iv pub stream st hI.inv _ hr, hV]
      simp only [RecGraph.stepP, RecGraph.stepNode, valState_of hss]
    exact ⟨RecGraph.new_inv st hI.inv _ hr (fun _ ⟨_, e⟩ => by cases e), RecGraph.new_grows st _,
      new_kernels st _, RecGraph.new_lt st hI.inv _, valE_of hopt, fun _ => hopt⟩
  | bits v s w =>
    simp only [ofRGNode, Graph.typedAt, Bool.and_eq_true, decide_eq_true_eq] at htj
    have hv : v < j := htj.1
    have he' : st.bits (map.getD v 0) s w = (i, st') := by
      simp only [ofRGNode, expandNode] at he
      split at he
      · split at he
        · exact Except.ok.inj he
        · cases he
      · exact Except.ok.inj he
    obtain ⟨rfl, rfl⟩ : i = _ ∧ st' = _ := ⟨(congrArg Prod.fst he').symm, (congrArg Prod.snd he').symm⟩
    have rv := hI.rel v hv
    refine ⟨RecGraph.bits_inv st hI.inv _ s w rv.1, (RecGraph.op_grows_kinv st (.bits _ s w) hI.inv.kinv).1,
      bits_kernels st _ s w, RecGraph.op_lt st hI.inv (.bits _ s w) rv.1, ?_, nst rfl⟩
    rw [stepP_bits] at hV
    rw [RecGraph.bits_val π iv pub stream st hI.inv _ s w rv.1, rv.2, valE_elem hV]
  | ringWeight k n =>
    simp only [ofRGNode, Graph.typedAt, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
      hK] at htj
    obtain ⟨hall, hlen⟩ := htj
    have he' : weightRun st (((g.kernels.getD k []).map fun id => map.getD id 0).take n)
        ((((g.kernels.getD k []).map fun id => map.getD id 0).drop n).take n)
        (((g.kernels.getD k []).map fun id => map.getD id 0).drop (2 * n)) = (i, st') := by
      simp only [ofRGNode, expandNode, hK] at he
      split at he
      · exact Except.ok.inj he
      · cases he
    have hrel : List.Forall₂ (Rel π iv pub stream st) ((g.kernels.getD k []).map fun id => map.getD id 0)
        ((g.kernels.getD k []).map (valE (origVals π iv pub stream g))) := by
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
      intro a ha
      exact hI.rel a (hall a ha).1
    have sim := weightSym_sim π iv pub stream st hI.inv (rel_seed hI.inv hI.seed) (List.forall₂_take n hrel)
      (List.forall₂_take n (List.forall₂_drop n hrel)) (List.forall₂_drop (2 * n) hrel)
    rw [he'] at sim
    obtain ⟨s1, s2, s3, s4, s5⟩ := sim
    refine ⟨s1, s2, s3, s4, ?_, nst rfl⟩
    rw [stepP_ringWeight] at hV
    rw [s5, weightAt_eq_tower _ _ _ (by
      rw [List.length_drop, List.length_map, hlen, show Flock.towerStages = 6 from rfl]; omega),
      valE_elem hV, RecGraph.ringWeightValue]

theorem getD_push_lt (map : Array ℕ) (x : ℕ) {a : ℕ} (ha : a < map.size) :
    (map.push x).getD a 0 = map.getD a 0 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, Nat.ne_of_lt ha]

theorem getD_push_eq (map : Array ℕ) (x : ℕ) : (map.push x).getD map.size 0 = x := by
  simp [Array.getD_eq_getD_getElem?]

/-- The invariant, one node further. -/
theorem einv_step {g : RecGraph.Graph} {j : ℕ} {st st' : RecState} {map : Array ℕ} {i : ℕ}
    (hI : EInv π iv pub stream g j st map) (ho : Out π iv pub stream g j st st' i) :
    EInv π iv pub stream g (j + 1) st' (map.push i) := by
  have h0 : 0 < st.nodes.size := by
    rcases Nat.lt_or_ge 0 st.nodes.size with hlt | hge
    · exact hlt
    · have := hI.seed; simp [Array.getElem?_eq_none hge] at this
  refine ⟨ho.inv, ho.kernels.trans hI.kernels, by rw [grows_get ho.grows h0]; exact hI.seed,
    by simp [hI.size], ?_, ?_⟩
  · intro a ha
    rcases Nat.lt_or_ge a j with h | h
    · rw [getD_push_lt map i (by rw [hI.size]; exact h)]
      exact rel_grows hI.inv ho.grows (hI.rel a h)
    · obtain rfl : a = j := by omega
      rw [← hI.size, getD_push_eq, hI.size]
      exact ⟨ho.lt, ho.val⟩
  · intro a ha hs
    rcases Nat.lt_or_ge a j with h | h
    · rw [getD_push_lt map i (by rw [hI.size]; exact h)]
      rw [RecGraph.evalAll_grows π iv pub stream st st' hI.inv.kinv ho.grows _ (hI.rel a h).1]
      exact hI.state a h hs
    · obtain rfl : a = j := by omega
      rw [← hI.size, getD_push_eq, hI.size]
      exact ho.state hs

/-! ## The replay, every node -/

/-- An accepted graph's types, node by node (`Graph.typed`). -/
theorem typed_parts {g : RecGraph.Graph} {G : Graph} (hG : G.nodes = g.nodes.map ofRGNode) (ht : G.typed = true) :
    ∀ j < g.nodes.size, G.typedAt j (ofRGNode (g.nodes.getD j default)) = true := by
  simp only [Graph.typed, Bool.and_eq_true, List.all_eq_true, List.mem_range] at ht
  intro j hj
  have h := ht.1.2 j (by rw [hG, Array.size_map]; exact hj)
  rwa [hG, getD_ofRG g hj] at h

/-- On a well-typed graph, every node reads earlier nodes only. -/
theorem typed_before {g : RecGraph.Graph} {G : Graph} (hK : G.kernels = g.kernels)
    (ht : ∀ j < g.nodes.size, G.typedAt j (ofRGNode (g.nodes.getD j default)) = true) :
    ∀ j (hj : j < g.nodes.size), ∀ a ∈ RecGraph.reads g.kernels g.nodes[j], a < j := by
  intro j hj a ha
  have h := ht j hj
  rw [show g.nodes.getD j default = g.nodes[j] by simp [Array.getD_eq_getD_getElem?, hj]] at h
  generalize g.nodes[j] = n at h ha
  cases n with
  | add x y =>
    simp only [ofRGNode, Graph.typedAt, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [RecGraph.reads, RecGraph.Node.operands, List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl
    · exact h.1.1.1
    · exact h.1.1.2
  | mul x y =>
    simp only [ofRGNode, Graph.typedAt, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [RecGraph.reads, RecGraph.Node.operands, List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl
    · exact h.1.1.1
    · exact h.1.1.2
  | hash s f t =>
    simp only [ofRGNode, Graph.typedAt, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [RecGraph.reads, RecGraph.Node.operands, List.mem_singleton] at ha
    rw [ha]; exact h.1
  | low x =>
    simp only [ofRGNode, Graph.typedAt, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [RecGraph.reads, RecGraph.Node.operands, List.mem_singleton] at ha
    rw [ha]; exact h.1
  | narrow x =>
    simp only [ofRGNode, Graph.typedAt, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [RecGraph.reads, RecGraph.Node.operands, List.mem_singleton] at ha
    rw [ha]; exact h.1
  | bits v s w =>
    simp only [ofRGNode, Graph.typedAt, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [RecGraph.reads, RecGraph.Node.operands, List.mem_singleton] at ha
    rw [ha]; exact h.1
  | ringWeight k m =>
    simp only [ofRGNode, Graph.typedAt, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, hK] at h
    simp only [RecGraph.reads] at ha
    exact (h.1 a ha).1
  | const => simp [RecGraph.reads, RecGraph.Node.operands] at ha
  | statement => simp [RecGraph.reads, RecGraph.Node.operands] at ha
  | input => simp [RecGraph.reads, RecGraph.Node.operands] at ha
  | seed => simp [RecGraph.reads, RecGraph.Node.operands] at ha

/-- **The replay keeps the invariant**, by induction over the original nodes. -/
theorem expandList_inv {g : RecGraph.Graph} {G : Graph} (hG : G.nodes = g.nodes.map ofRGNode)
    (hK : G.kernels = g.kernels) (ht : ∀ j < g.nodes.size, G.typedAt j (ofRGNode (g.nodes.getD j default)) = true) :
    ∀ (ns : List RecGraph.Node) (j : ℕ) (st : RecState) (map : Array ℕ) (res : RecState × Array ℕ),
      j ≤ g.nodes.size → ns = g.nodes.toList.drop j → EInv π iv pub stream g j st map →
      expandList G.kernels (ns.map ofRGNode) (st, map) = .ok res →
      EInv π iv pub stream g g.nodes.size res.1 res.2
  | [], j, st, map, res, hj, hns, hI, he => by
    simp only [List.map_nil, expandList, pure, Except.pure, Except.ok.injEq] at he
    subst he
    have hlen := congrArg List.length hns
    simp only [List.length_nil, List.length_drop, Array.length_toList] at hlen
    obtain rfl : j = g.nodes.size := by omega
    exact hI
  | n :: ns, j, st, map, res, _, hns, hI, he => by
    rw [List.map_cons] at he
    obtain ⟨i, st', hn, hrest⟩ := expandList_cons he
    have hlt : j < g.nodes.size := by
      rcases Nat.lt_or_ge j g.nodes.size with h | h
      · exact h
      · rw [List.drop_eq_nil_of_le (by simpa using h)] at hns; cases hns
    have hd : g.nodes.toList.drop j = g.nodes[j] :: g.nodes.toList.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hlt)]; simp
    rw [hd] at hns
    obtain ⟨hn1, hn2⟩ := List.cons.inj hns
    subst hn1
    have hgd : g.nodes.getD j default = g.nodes[j] := by simp [Array.getD_eq_getD_getElem?, hlt]
    have hjt := ht j hlt
    rw [hgd] at hjt
    have ho := node_out hG hK hlt hI hgd hjt (orig_get (typed_before hK ht) hlt) hn
    exact expandList_inv hG hK ht ns (j + 1) st' (map.push i) res hlt hn2 (einv_step hI ho) hrest

theorem einv_start (g : RecGraph.Graph) : EInv π iv pub stream g 0 RecGraph.RecState.start #[] where
  inv := RecGraph.start_inv
  kernels := by simp [RecGraph.RecState.start, RecGraph.RecState.new]
  seed := by simp [RecGraph.RecState.start, RecGraph.RecState.new]
  size := rfl
  rel := fun _ ha => absurd ha (Nat.not_lt_zero _)
  state := fun _ ha => absurd ha (Nat.not_lt_zero _)

theorem expand_ok {G : Graph} {nodes : Array Node} {map : Array ℕ} (h : expand G = .ok (nodes, map)) :
    ∃ st, expandList G.kernels G.nodes.toList (RecGraph.RecState.start, #[]) = .ok (st, map) ∧
      nodes = st.nodes.map ofRGNode := by
  unfold expand at h
  by_cases hs : (G.nodes.getD 0 default != .seed) = true
  · simp only [hs, ite_true] at h
    cases h
  · simp only [hs, Bool.false_eq_true, ite_false] at h
    cases he : expandList G.kernels G.nodes.toList (RecGraph.RecState.start, #[]) with
    | error e =>
      rw [he] at h
      cases h
    | ok p =>
      obtain ⟨st, m⟩ := p
      rw [he] at h
      cases h
      exact ⟨st, rfl, rfl⟩

/-- **The expansion of an accepted graph keeps the invariant to its end.** -/
theorem expand_einv {g : RecGraph.Graph} {G : Graph} (hG : G.nodes = g.nodes.map ofRGNode)
    (hK : G.kernels = g.kernels) (ht : G.typed = true) {nodes : Array Node} {map : Array ℕ}
    (he : expand G = .ok (nodes, map)) :
    ∃ st : RecState, nodes = st.nodes.map ofRGNode ∧ EInv π iv pub stream g g.nodes.size st map := by
  obtain ⟨st, hl, hn⟩ := expand_ok he
  refine ⟨st, hn, ?_⟩
  have hl' : expandList G.kernels (g.nodes.toList.map ofRGNode) (RecGraph.RecState.start, #[]) =
      .ok (st, map) := by
    rw [← hl, hG, Array.toList_map]
  exact expandList_inv hG hK (typed_parts hG ht) _ 0 _ _ (st, map) (Nat.zero_le _) List.drop_zero.symm
    (einv_start g) hl'

end Replay

/-! ## `ExpandSound` -/

theorem compileRaw_of_compile {r : Recorded} {c : Compiled} (h : compile r = .ok c) : compileRaw r = .ok c := by
  unfold compile at h
  cases hr : compileRaw r with
  | error e => rw [hr] at h; cases h
  | ok c' =>
    rw [hr] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · cases h; rfl

/-- What `compileRaw` checks and records: a well-typed graph, and its expansion's nodes and map. -/
theorem compileRaw_ok {r : Recorded} {c : Compiled} (h : compileRaw r = .ok c) :
    r.graph.typed = true ∧ expand r.graph = .ok (c.nodes, c.map) := by
  unfold compileRaw at h
  by_cases ht : r.graph.typed = true
  · refine ⟨ht, ?_⟩
    simp only [ht, Bool.not_true, Bool.false_eq_true, ite_false] at h
    cases he : expand r.graph with
    | error e =>
      rw [he] at h
      cases h
    | ok p =>
      obtain ⟨g', m'⟩ := p
      rw [he] at h
      simp only [bind, Except.bind] at h
      cases hm : (Builder.compileM r g' m').run { logWidth := 4 } with
      | error e =>
        rw [hm] at h
        cases h
      | ok q =>
        rw [hm] at h
        cases h
        rfl
  · simp only [ht, Bool.not_false, ite_true] at h
    cases h

/-- **The expansion keeps `RecGraph`'s meaning**, on every graph the compiler accepts: `ExpandSound`, proved. -/
theorem expandSound {g : RecGraph.Graph} {rootsAt : List ℕ} {iv : List UInt8} {c : Compiled}
    (hc : compile (ofRG g rootsAt iv) = .ok c) : ExpandSound g c := by
  intro iv' pub stream k hk
  obtain ⟨ht, he⟩ := compileRaw_ok (compileRaw_of_compile hc)
  obtain ⟨st, hn, hI⟩ := expand_einv (π := keccakF1600) (iv := iv') (pub := pub) (stream := stream.toArray)
    (g := g) (G := (ofRG g rootsAt iv).graph) rfl rfl ht he
  have hX : c.rgX iv' pub stream = evalAll keccakF1600 iv' pub stream.toArray st := by
    unfold Compiled.rgX RecGraph.evalAll
    have hid : (toRGNode ∘ ofRGNode) = id := funext toRG_ofRG
    rw [hn, hI.kernels, Array.toList_map, List.map_map, hid, List.map_id]
  have hV : rgVals g iv' pub stream = origVals keccakF1600 iv' pub stream.toArray g :=
    RecGraph.evalList_eq keccakF1600 iv' pub stream.toArray g.kernels #[] g.nodes.toList
  rw [hX, hV]
  exact (hI.rel k hk).2

end RecCircuit
