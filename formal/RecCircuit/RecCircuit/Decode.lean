-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCircuit.Words

/-!
# What an accepted circuit gives, and what its witness encodes

`checked_of_compile`: `compile r = .ok c` gives every check (`Checked`). `Graph.eval_step`: a node's value is its step on
the values of its operands. The decoders: a free bit's word is the bit of the stream (or the public input) the witness
encodes (`stream_bit`, `public_bit`).
-/

namespace RecCircuit

open Primitives PcsCircuit

/-! ## The checks -/

namespace Compiled

/-- **What the checker established** of a compiled circuit. -/
structure Checked (c : Compiled) (r : Recorded) : Prop where
  view : c.ctx.viewOk = true
  keccak : ∀ t ∈ c.st.keccaks, c.ctx.keccakOk t = true
  sponge : ∀ s ∈ c.st.sponges, c.ctx.spongeOk c.st.keccaks s = true
  pack : ∀ p ∈ c.st.packs, c.ctx.packOk p = true
  bits : c.bitsOk c.ctx = true
  statement : c.statementOk c.packOf = true
  roots : c.rootsOk r.rootsAt c.packOf = true
  free : c.freeReadsOk r.graph.streamLen = true
  graph : c.graphOk r = true
  nodes : ∀ id < c.nodes.size, c.live.getD id false = true → c.nodeOk c.ctx r.iv c.packOf id = true
  ports : c.portsOk c.ctx = true
  sources : c.sourcesOk = true
  calls : c.callsOk r = true
  zeroConst : c.zeroConstOk r = true
  sizes : c.live.size = c.nodes.size ∧ c.limbs.size = c.nodes.size ∧ c.digests.size = c.nodes.size ∧
    c.bitSelf.size = 8 * r.graph.streamLen ∧ c.circuit.logWidth = 4 ∧ c.circuit.logWidth ≤ c.circuit.logN
  /-- The completeness checks (`Complete.lean`). -/
  cSlots : c.completeSlots = true
  cValues : c.completeValues = true
  cGiven : c.completeGiven = true
  cCover : c.completeCover r.graph.streamLen = true

theorem checked_of_compile {r : Recorded} {c : Compiled} (h : compile r = .ok c) : c.Checked r := by
  unfold compile at h
  cases hr : compileRaw r with
  | error e => rw [hr] at h; cases h
  | ok c' =>
    rw [hr] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i hfind
      cases h
      have hall : ∀ t ∈ c.checks r, t.2 = true := by
        intro t ht
        by_contra hne
        have : ((c.checks r).find? fun t => !t.2).isSome := by
          rw [List.find?_isSome]; exact ⟨t, ht, by simpa using hne⟩
        rw [hfind] at this; simp at this
      have g := fun (name : String) (b : Bool) (hm : (name, b) ∈ c.checks r) => hall _ hm
      simp only [checks, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hall
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h11', h11'', h13, hc1, hc2, hc3, hc4, h12⟩ := hall
      simp only [Array.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2 h3 h4 h12
      refine ⟨h1, ?_, ?_, ?_, h5, h6, h7, h8, h9, ?_, h11, h11', h11'', h13, ?_, hc1, hc2, hc3, hc4⟩
      · intro t ht; obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp ht; exact h2 i hi
      · intro t ht; obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp ht; exact h3 i hi
      · intro t ht; obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp ht; exact h4 i hi
      · intro id hid hl
        have := allBelow_spec h10 id hid
        simpa [hl] using this
      · exact ⟨h12.1.1.1.1.1, h12.1.1.1.1.2, h12.1.1.1.2, h12.1.1.2, h12.1.2, h12.2⟩

theorem Checked.good {r : Recorded} {c : Compiled} (h : c.Checked r) {w : ℕ → K} (hw : c.circuit.Satisfied w) :
    c.ctx.Good w := ⟨h.view, rfl, hw⟩

end Compiled

/-! ## The graph's evaluation, node by node -/

section Eval

variable (g : Graph) (iv pub stream : List UInt8)

theorem foldl_push_size (L : List Node) (init : Array Value) :
    (L.foldl (fun values node => values.push (g.step iv pub stream values node)) init).size = init.size + L.length := by
  induction L generalizing init with
  | nil => simp
  | cons n L ih => rw [List.foldl_cons, ih]; simp; omega

theorem foldl_push_getD_lt (L : List Node) (init : Array Value) (i : ℕ) (hi : i < init.size) :
    (L.foldl (fun values node => values.push (g.step iv pub stream values node)) init).getD i default = init.getD i default := by
  induction L generalizing init with
  | nil => rfl
  | cons n L ih =>
    rw [List.foldl_cons, ih _ (by simp; omega)]
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, hi, show i ≠ init.size by omega]

theorem foldl_push_getD (L : List Node) (init : Array Value) (i : ℕ) (hi : i < L.length) :
    (L.foldl (fun values node => values.push (g.step iv pub stream values node)) init).getD (init.size + i) default =
      g.step iv pub stream ((L.take i).foldl (fun values node => values.push (g.step iv pub stream values node)) init)
        (L.getD i default) := by
  induction L generalizing init i with
  | nil => simp at hi
  | cons n L ih =>
    cases i with
    | zero =>
      rw [List.foldl_cons, Nat.add_zero, foldl_push_getD_lt g iv pub stream L _ init.size (by simp)]
      simp [Array.getD_eq_getD_getElem?]
    | succ i =>
      rw [List.foldl_cons, show init.size + (i + 1) = (init.push (g.step iv pub stream init n)).size + i by simp; omega,
        ih _ i (by simpa using hi)]
      simp

/-- A step reads its node's operands only (but a ring weight's kernel). -/
theorem step_congr {v v' : Array Value} {node : Node} (hrw : ∀ k n, node ≠ .ringWeight k n)
    (h : ∀ o ∈ node.ops, v.getD o default = v'.getD o default) :
    g.step iv pub stream v node = g.step iv pub stream v' node := by
  cases node with
  | add a b => simp only [Node.ops, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at h
               simp [Graph.step, h.1, h.2]
  | mul a b => simp only [Node.ops, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at h
               simp [Graph.step, h.1, h.2]
  | hash s f t => simp only [Node.ops, List.mem_cons, List.mem_nil_iff, or_false, forall_eq] at h; simp [Graph.step, h]
  | low a => simp only [Node.ops, List.mem_cons, List.mem_nil_iff, or_false, forall_eq] at h; simp [Graph.step, h]
  | narrow a => simp only [Node.ops, List.mem_cons, List.mem_nil_iff, or_false, forall_eq] at h; simp [Graph.step, h]
  | bits a s w => simp only [Node.ops, List.mem_cons, List.mem_nil_iff, or_false, forall_eq] at h; simp [Graph.step, h]
  | ringWeight k n => exact absurd rfl (hrw k n)
  | _ => rfl

/-- **A node's value is its step on its operands' values.** -/
theorem Graph.eval_step (i : ℕ) (hi : i < g.nodes.size) (hrw : ∀ k n, g.nodes.getD i default ≠ .ringWeight k n)
    (hops : ∀ o ∈ (g.nodes.getD i default).ops, o < i) :
    (g.eval iv pub stream).getD i default = g.step iv pub stream (g.eval iv pub stream) (g.nodes.getD i default) := by
  unfold Graph.eval
  rw [← Array.foldl_toList]
  have hL : i < g.nodes.toList.length := by simpa using hi
  have := foldl_push_getD g iv pub stream g.nodes.toList #[] i hL
  simp only [Array.size_empty, zero_add] at this
  rw [this]
  have hgi : g.nodes.toList.getD i default = g.nodes.getD i default := by
    simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]
  rw [hgi]
  apply step_congr g iv pub stream hrw
  intro o ho
  have hoi := hops o ho
  have hsplit : g.nodes.toList = g.nodes.toList.take i ++ g.nodes.toList.drop i := (List.take_append_drop _ _).symm
  have hsz : o < ((g.nodes.toList.take i).foldl (fun values node => values.push (g.step iv pub stream values node)) #[]).size := by
    rw [foldl_push_size]; simp [List.length_take]; omega
  conv => rhs; rw [hsplit, List.foldl_append, foldl_push_getD_lt g iv pub stream _ _ o hsz]

end Eval

/-! ## The free bits the witness encodes -/

namespace Compiled

variable {c : Compiled} {r : Recorded} {w : ℕ → K}

theorem bitsOk_parts (h : c.bitsOk c.ctx = true) :
    (∀ k < c.bitSelf.size, ∀ v, c.bitSelf.getD k none = some v → c.ctx.bitOk v = true ∧
      ∀ cp, c.bitCopy.getD k none = some cp → c.ctx.copyOk v cp = true) ∧
    (∀ k < 256, c.ctx.bitOk (c.publicSelf.getD k NONE) = true ∧
      c.ctx.copyOk (c.publicSelf.getD k NONE) (c.publicCopy.getD k NONE) = true) ∧
    c.publicSelf.size = 256 := by
  unfold bitsOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hb, _⟩, hps⟩, _⟩, hp⟩ := h
  refine ⟨fun k hk v hv => ?_, fun k hk => ?_, hps⟩
  · have := allBelow_spec hb k hk
    rw [hv] at this
    simp only [Bool.and_eq_true] at this
    refine ⟨this.1, fun cp hcp => ?_⟩
    have h2 := this.2
    rw [hcp] at h2
    exact h2
  · have := allBelow_spec hp k hk
    simpa only [Bool.and_eq_true] using this

/-- A stream bit's word, in the witness's stream. -/
theorem stream_bit (hc : c.Checked r) (hw : c.circuit.Satisfied w) {i j : ℕ} (hi : i < r.graph.streamLen) (hj : j < 8)
    (hsome : ∀ j' < 8, (c.bitSelf.getD (8 * i + j') none).isSome) :
    c.ctx.val w (c.streamBit (8 * i + j)) =
      ofBool (((c.decodeStream r.graph.streamLen (c.ctx.val w)).getD i 0).toNat.testBit j) := by
  have G := hc.good hw
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hsome j hj)
  have hk : 8 * i + j < c.bitSelf.size := by rw [hc.sizes.2.2.2.1]; omega
  have hbit := ((bitsOk_parts hc.bits).1 _ hk v hv).1
  have hsb : c.streamBit (8 * i + j) = v := by simp [streamBit, hv]
  rw [hsb]
  unfold decodeStream
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some]
  have h0 : (c.bitSelf.getD (8 * i) none).isSome = true := by simpa using hsome 0 (by norm_num)
  rw [if_pos h0, decoded_byte_testBit _ j hj, hsb]
  exact ofBool_bitOfWord (Ctx.bit_isBit G hbit)

/-- A public-input bit's word, in the witness's public input. -/
theorem public_bit (hc : c.Checked r) (hw : c.circuit.Satisfied w) {i j : ℕ} (hi : i < 32) (hj : j < 8) :
    c.ctx.val w (c.publicSelf.getD (8 * i + j) NONE) =
      ofBool (((c.decodePublic (c.ctx.val w)).getD i 0).toNat.testBit j) := by
  have G := hc.good hw
  have hbit := ((bitsOk_parts hc.bits).2.1 (8 * i + j) (by omega)).1
  unfold decodePublic
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some,
    decoded_byte_testBit _ j hj]
  exact ofBool_bitOfWord (Ctx.bit_isBit G hbit)

theorem decodePublic_length (val : ℕ → K) : (c.decodePublic val).length = 32 := by simp [decodePublic]

theorem decodeStream_length (n : ℕ) (val : ℕ → K) : (c.decodeStream n val).length = n := by simp [decodeStream]

end Compiled

end RecCircuit
