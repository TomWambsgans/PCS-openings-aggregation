-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCircuit.Decode

/-!
# Every live node's limbs carry its value

By induction over the expanded graph's nodes (`node_inv`): on a satisfied accepted circuit, every live element node's
three limb values are its value's limbs (`ofLimbs` of their words is its value in `E`), and every live seed or hash
node's 256 digest values are its Keccak state's bits; the graph evaluated on the public input and the stream the
witness's free bits encode (`decodePublic`, `decodeStream`).
-/

namespace RecCircuit

open Primitives PcsCircuit

theorem F64.ofNat_zero : F64.ofNat 0 = 0 := by decide

theorem F64.ofU64_toU64 (x : F64) : F64.ofU64 (F64.toU64 x) = x := rfl

theorem lookup_map_range (g : ℕ → ℕ) : ∀ (n e : ℕ),
    ((List.range n).map fun i => (i, g i)).lookup e = if e < n then some (g e) else none := by
  intro n e
  have := Ctx.lookup_range_map g 0 n e
  have h2 := Ctx.lookup_range_map_none g 0 n e
  simp only [Nat.zero_add] at this h2
  split
  · exact this (by assumption)
  · exact h2 (Or.inr (by omega))

theorem beBits_lookup (bitv : ℕ → ℕ) (first n e : ℕ) :
    (beBits bitv first n).lookup e = if e < 8 * n then some (bitv (8 * (first + n - 1 - e / 8) + e % 8)) else none :=
  lookup_map_range _ _ _

theorem leBits_lookup (bitv : ℕ → ℕ) (first n e : ℕ) :
    (leBits bitv first n).lookup e = if e < 8 * n then some (bitv (8 * (first + e / 8) + e % 8)) else none :=
  lookup_map_range _ _ _

namespace Compiled

variable {c : Compiled} {r : Recorded} {w : ℕ → K}

/-- The expanded graph, as the compiler reads it. -/
def egraph (c : Compiled) (r : Recorded) : Graph := { r.graph with nodes := c.nodes }

/-- The public input, the stream and every node's value, on the witness. -/
def pubW (c : Compiled) (w : ℕ → K) : List UInt8 := c.decodePublic (c.ctx.val w)
def streamW (c : Compiled) (r : Recorded) (w : ℕ → K) : List UInt8 := c.decodeStream r.graph.streamLen (c.ctx.val w)
def valsW (c : Compiled) (r : Recorded) (w : ℕ → K) : Array Value := (c.egraph r).eval r.iv (c.pubW w) (c.streamW r w)

/-- An element node's limbs carry its value. -/
def ElemInv (c : Compiled) (r : Recorded) (w : ℕ → K) (id : ℕ) : Prop :=
  (c.limbsOf id).size = 3 ∧
    F192.ofLimbs (c.ctx.val w ((c.limbsOf id).getD 0 NONE)) (c.ctx.val w ((c.limbsOf id).getD 1 NONE))
      (c.ctx.val w ((c.limbsOf id).getD 2 NONE)) = ((c.valsW r w).getD id default).toE

/-- A seed's or hash's digest values carry its state's bits. -/
def StateInv (c : Compiled) (r : Recorded) (w : ℕ → K) (id : ℕ) : Prop :=
  ∃ d, c.digests.getD id none = some d ∧ d.size = 256 ∧ ((c.valsW r w).getD id default).toState.length = 32 ∧
    ∀ k < 256, c.ctx.val w (d.getD k NONE) = ofBool (bitOf ((c.valsW r w).getD id default).toState k)

def NodeInv (c : Compiled) (r : Recorded) (w : ℕ → K) (id : ℕ) : Prop :=
  if isStateNode (c.nodes.getD id default) then c.StateInv r w id else c.ElemInv r w id

/-! ## Packings of known bits -/

theorem packIs_word (hc : c.Checked r) (G : c.ctx.Good w) {u : ℕ} {bits : List (ℕ × ℕ)}
    (h : c.packIs c.packOf u bits = true) (M : ℕ) (hM : ∀ e < 64, c.ctx.bitAt w bits e = ofBool (M.testBit e)) :
    c.ctx.val w u = F64.ofNat M := by
  unfold packIs at h
  split at h
  · rename_i t _
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨ht, hout⟩, hbits⟩ := h
    have hok := hc.pack _ (Ctx.getD_mem default ht)
    rw [← hout, Ctx.pack_val G hok, hbits]
    exact sum_bits_word _ M hM
  · cases h

/-- The bits of a big-endian packing of bits that carry a byte string's bits. -/
theorem packBE_word (hc : c.Checked r) (G : c.ctx.Good w) {u : ℕ} (bitv : ℕ → ℕ) (bytes : List UInt8) (first n : ℕ)
    (hlen : first + n ≤ bytes.length)
    (hbits : ∀ i < n, ∀ j < 8, c.ctx.val w (bitv (8 * (first + i) + j)) =
      ofBool ((bytes.getD (first + i) 0).toNat.testBit j))
    (h : c.packIs c.packOf u (beBits bitv first n) = true) :
    c.ctx.val w u = F64.ofNat (beNat (slice bytes first n)) := by
  apply packIs_word hc G h
  intro e he
  rw [Ctx.bitAt, beBits_lookup, beNat_testBit, slice_length _ _ _ hlen]
  by_cases h8 : e < 8 * n
  · simp only [h8, ite_true, decide_true, Bool.true_and]
    have hi : n - 1 - e / 8 < n := by omega
    rw [slice_getD _ _ _ _ hi, show first + n - 1 - e / 8 = first + (n - 1 - e / 8) by omega]
    exact hbits _ hi _ (Nat.mod_lt _ (by norm_num))
  · simp only [h8, ite_false, decide_false, Bool.false_and]; rfl

/-- The bits of a little-endian packing. -/
theorem packLE_word (hc : c.Checked r) (G : c.ctx.Good w) {u : ℕ} (bitv : ℕ → ℕ) (bytes : List UInt8) (first n : ℕ)
    (hlen : first + n ≤ bytes.length)
    (hbits : ∀ i < n, ∀ j < 8, c.ctx.val w (bitv (8 * (first + i) + j)) =
      ofBool ((bytes.getD (first + i) 0).toNat.testBit j))
    (h : c.packIs c.packOf u (leBits bitv first n) = true) :
    c.ctx.val w u = F64.ofNat (leNat (slice bytes first n)) := by
  apply packIs_word hc G h
  intro e he
  rw [Ctx.bitAt, leBits_lookup, leNat_testBit, slice_length _ _ _ hlen]
  by_cases h8 : e < 8 * n
  · simp only [h8, ite_true, decide_true, Bool.true_and]
    have hi : e / 8 < n := by omega
    rw [slice_getD _ _ _ _ hi]
    exact hbits _ hi _ (Nat.mod_lt _ (by norm_num))
  · simp only [h8, ite_false, decide_false, Bool.false_and]; rfl

/-! ## A node's value -/

theorem graphOk_parts (h : c.graphOk r = true) :
    (∀ id < c.nodes.size, c.live.getD id false = true →
      ∀ o ∈ (c.nodes.getD id default).ops, o < id ∧ c.live.getD o false = true) ∧
    c.zero = r.graph.zero.map (fun id => c.map.getD id 0) ∧
    (∀ id ∈ c.zeroNodes ++ c.elementNodes.toList, id < c.nodes.size ∧ c.live.getD id false = true) ∧
    r.iv.length = 32 := by
  unfold graphOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun id hid hl o ho => ?_, h2, h3, h4⟩
  have := allBelow_spec h1 id hid
  simp only [hl, Bool.not_true, Bool.false_or, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this o ho

theorem not_ringWeight (hc : c.Checked r) {id : ℕ} (hid : id < c.nodes.size) (hl : c.live.getD id false = true) :
    ∀ k n, c.nodes.getD id default ≠ .ringWeight k n := by
  intro k n he
  have := hc.nodes id hid hl
  simp [nodeOk, he] at this

/-- **A live node's value is its step.** -/
theorem valsW_step (hc : c.Checked r) {id : ℕ} (hid : id < c.nodes.size) (hl : c.live.getD id false = true) :
    (c.valsW r w).getD id default =
      (c.egraph r).step r.iv (c.pubW w) (c.streamW r w) (c.valsW r w) (c.nodes.getD id default) :=
  Graph.eval_step (c.egraph r) _ _ _ id hid (not_ringWeight hc hid hl)
    (fun o ho => ((graphOk_parts hc.graph).1 id hid hl o ho).1)

/-! ## The nodes, kind by kind -/

theorem inv_const (hc : c.Checked r) (G : c.ctx.Good w) {id : ℕ} (hid : id < c.nodes.size)
    (hl : c.live.getD id false = true) {c0 c1 c2 : UInt64} (hnode : c.nodes.getD id default = .const c0 c1 c2) :
    c.ElemInv r w id := by
  have hok := hc.nodes id hid hl
  simp only [nodeOk, hnode, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨hs, h0⟩, h1⟩, h2⟩ := hok
  refine ⟨hs, ?_⟩
  rw [valsW_step hc hid hl, hnode, Ctx.const_val G h0, Ctx.const_val G h1, Ctx.const_val G h2]
  rfl

theorem inv_statement (hc : c.Checked r) (G : c.ctx.Good w) (hw : c.circuit.Satisfied w) {id : ℕ}
    (hid : id < c.nodes.size) (hl : c.live.getD id false = true) {k : ℕ} (hnode : c.nodes.getD id default = .statement k) :
    c.ElemInv r w id := by
  have hok := hc.nodes id hid hl
  simp only [nodeOk, hnode, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hk, hs⟩, h0⟩, h1⟩, h2⟩ := hok
  have hst := hc.statement
  unfold statementOk at hst
  simp only [Bool.and_eq_true, beq_iff_eq] at hst
  have hpk := allBelow_spec hst.2 k hk
  have hw0 := packBE_word hc G (fun i => c.publicSelf.getD i NONE) (c.pubW w) (8 * k) 8
    (by rw [pubW, decodePublic_length]; omega)
    (fun i hi j hj => by rw [show 8 * (8 * k + i) + j = 8 * (8 * k + i) + j from rfl]; exact public_bit hc hw (by omega) hj)
    hpk
  refine ⟨hs, ?_⟩
  rw [valsW_step hc hid hl, hnode, h0, hw0, Ctx.const_val G h1, Ctx.const_val G h2]
  simp [Graph.step, Value.toE, elemOfNats, F64.ofNat_zero, pubW]

/-- A state node's digest bits, as packings read them. -/
theorem digest_bits {id : ℕ} (hs : c.StateInv r w id) {d : Array ℕ} (hd : c.digests.getD id none = some d)
    (first i j : ℕ) (hq : 8 * (first + i) + j < 256) (hj : j < 8) :
    c.ctx.val w (d.getD (8 * (first + i) + j) NONE) =
      ofBool ((((c.valsW r w).getD id default).toState.getD (first + i) 0).toNat.testBit j) := by
  obtain ⟨d', hd', _, _, hbits⟩ := hs
  rw [hd] at hd'; cases hd'
  rw [hbits _ hq, bitOf, show (8 * (first + i) + j) / 8 = first + i by omega,
    show (8 * (first + i) + j) % 8 = j by omega]

theorem beNat_slice_mod (state : List UInt8) (h32 : state.length = 32) :
    beNat (slice state 8 8) % 2 ^ 32 = beNat (slice state 12 4) := by
  apply Nat.eq_of_testBit_eq
  intro e
  rw [Nat.testBit_mod_two_pow, beNat_testBit, beNat_testBit, slice_length _ _ _ (by omega),
    slice_length _ _ _ (by omega)]
  by_cases h : e < 32
  · have hi : 8 - 1 - e / 8 < 8 := by omega
    have hi' : 4 - 1 - e / 8 < 4 := by omega
    simp only [h, decide_true, Bool.true_and, show e < 8 * 8 by omega, show e < 8 * 4 by omega]
    rw [slice_getD _ _ _ _ hi, slice_getD _ _ _ _ hi', show 8 + (8 - 1 - e / 8) = 12 + (4 - 1 - e / 8) by omega]
  · simp [h, show ¬ e < 8 * 4 by omega]

theorem inv_low (hc : c.Checked r) (G : c.ctx.Good w) {id : ℕ} (hid : id < c.nodes.size)
    (hl : c.live.getD id false = true) {h : ℕ} (hnode : c.nodes.getD id default = .low h)
    (ih : c.StateInv r w h) : c.ElemInv r w id := by
  have hok := hc.nodes id hid hl
  simp only [nodeOk, hnode, Bool.and_eq_true, beq_iff_eq] at hok
  have h2 := hok.2.2
  have h1 := hok.2.1.2
  have h0 := hok.2.1.1.2
  have hs := hok.2.1.1.1.2
  have ⟨d, hd, _, hlen, _⟩ := ih
  rw [hd, Option.getD_some] at h0 h1 h2
  have W := fun (first : ℕ) (hf : first + 8 ≤ 32) (u : ℕ)
      (hp : c.packIs c.packOf u (beBits (fun i => d.getD i NONE) first 8) = true) =>
    packBE_word hc G (fun i => d.getD i NONE) (((c.valsW r w).getD h default).toState) first 8 (by omega)
      (fun i hi j hj => digest_bits ih hd first i j (by omega) hj) hp
  refine ⟨hs, ?_⟩
  rw [valsW_step hc hid hl, hnode, W 24 (by norm_num) _ h0, W 16 (by norm_num) _ h1, W 8 (by norm_num) _ h2]
  rfl

theorem inv_narrow (hc : c.Checked r) (G : c.ctx.Good w) {id : ℕ} (hid : id < c.nodes.size)
    (hl : c.live.getD id false = true) {h : ℕ} (hnode : c.nodes.getD id default = .narrow h)
    (ih : c.StateInv r w h) : c.ElemInv r w id := by
  have hok := hc.nodes id hid hl
  simp only [nodeOk, hnode, Bool.and_eq_true, beq_iff_eq] at hok
  have h2 := hok.2.2
  have h1 := hok.2.1.2
  have h0 := hok.2.1.1.2
  have hs := hok.2.1.1.1.2
  have ⟨d, hd, _, hlen, _⟩ := ih
  rw [hd, Option.getD_some] at h0 h1 h2
  have W := fun (first n : ℕ) (hf : first + n ≤ 32) (u : ℕ)
      (hp : c.packIs c.packOf u (beBits (fun i => d.getD i NONE) first n) = true) =>
    packBE_word hc G (fun i => d.getD i NONE) (((c.valsW r w).getD h default).toState) first n (by omega)
      (fun i hi j hj => digest_bits ih hd first i j (by omega) hj) hp
  refine ⟨hs, ?_⟩
  rw [valsW_step hc hid hl, hnode, W 24 8 (by norm_num) _ h0, W 16 8 (by norm_num) _ h1, W 12 4 (by norm_num) _ h2]
  simp only [Graph.step, Value.toE, narrowOf, elemOfNats]
  rw [beNat_slice_mod _ hlen]

/-! ## `E` units -/

theorem cells_lookup_A (base : ℕ) (A B : List ℕ) (i : ℕ) (hi : i < 3) :
    ((List.range 3).map (fun i => (base + i, A.getD i NONE)) ++
      (List.range 3).map (fun i => (base + 3 + i, B.getD i NONE))).lookup (base + i) = some (A.getD i NONE) := by
  rw [List.lookup_append, Ctx.lookup_range_map (fun i => A.getD i NONE) base 3 i hi]; rfl

theorem cells_lookup_B (base : ℕ) (A B : List ℕ) (i : ℕ) (hi : i < 3) :
    ((List.range 3).map (fun i => (base + i, A.getD i NONE)) ++
      (List.range 3).map (fun i => (base + 3 + i, B.getD i NONE))).lookup (base + 3 + i) = some (B.getD i NONE) := by
  rw [List.lookup_append, Ctx.lookup_range_map_none _ base 3 _ (Or.inr (by omega)),
    Ctx.lookup_range_map (fun i => B.getD i NONE) (base + 3) 3 i hi]; rfl

/-- The three limbs' words as an element. -/
def limbsE (c : Compiled) (w : ℕ → K) (l : List ℕ) : F192 :=
  F192.ofLimbs (c.ctx.val w (l.getD 0 NONE)) (c.ctx.val w (l.getD 1 NONE)) (c.ctx.val w (l.getD 2 NONE))

theorem toList_getD (a : Array ℕ) (i : ℕ) : a.toList.getD i NONE = a.getD i NONE := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- **An `E` unit's limbs are the sum or the product of its cells' elements.** -/
theorem unit_val (G : c.ctx.Good w) {base : ℕ} {A B : List ℕ} {out : Array ℕ} (op : Op)
    (h : ∀ l < 3, c.ctx.gate (out.getD l NONE) (Ctx.unitPolyL op base l) 0
      ((List.range 3).map (fun i => (base + i, A.getD i NONE)) ++
        (List.range 3).map (fun i => (base + 3 + i, B.getD i NONE))) = true) :
    c.limbsE w out.toList = if op = .add then c.limbsE w A + c.limbsE w B else c.limbsE w A * c.limbsE w B := by
  set cells := (List.range 3).map (fun i => (base + i, A.getD i NONE)) ++
    (List.range 3).map (fun i => (base + 3 + i, B.getD i NONE)) with hcells
  set f := c.ctx.cellVal w cells
  have fa : ∀ i < 3, f (base + i) = c.ctx.val w (A.getD i NONE) := fun i hi => by
    simp only [f, Ctx.cellVal, hcells, cells_lookup_A base A B i hi, Option.getD_some]
  have fb : ∀ i < 3, f (base + 3 + i) = c.ctx.val w (B.getD i NONE) := fun i hi => by
    simp only [f, Ctx.cellVal, hcells, cells_lookup_B base A B i hi, Option.getD_some]
  have hv : ∀ l < 3, c.ctx.val w (out.getD l NONE) = (Ctx.unitPolyL op base l).eval f := fun l hl => by
    rw [G.gate (h l hl), add_zero]
  unfold limbsE
  rw [toList_getD, toList_getD, toList_getD, hv 0 (by norm_num), hv 1 (by norm_num), hv 2 (by norm_num)]
  have a0 : f base = c.ctx.val w (A.getD 0 NONE) := fa 0 (by norm_num)
  have a1 := fa 1 (by norm_num)
  have a2 := fa 2 (by norm_num)
  have b0 : f (base + 3) = c.ctx.val w (B.getD 0 NONE) := fb 0 (by norm_num)
  have b1 : f (base + 4) = c.ctx.val w (B.getD 1 NONE) := by
    have := fb 1 (by norm_num); rwa [show base + 3 + 1 = base + 4 by omega] at this
  have b2 : f (base + 5) = c.ctx.val w (B.getD 2 NONE) := by
    have := fb 2 (by norm_num); rwa [show base + 3 + 2 = base + 5 by omega] at this
  cases op with
  | add =>
    rw [Ctx.eval_unit_add, Ctx.eval_unit_add, Ctx.eval_unit_add, fa 0 (by norm_num), fb 0 (by norm_num), a1,
      fb 1 (by norm_num), a2, fb 2 (by norm_num), if_pos rfl, F192.ofLimbs_add_ofLimbs]
  | mul =>
    obtain ⟨m0, m1, m2⟩ := Ctx.eval_unit_mul base f
    rw [m0, m1, m2, a0, a1, a2, b0, b1, b2, if_neg (by decide), F192.ofLimbs_mul_ofLimbs]
  | square =>
    obtain ⟨m0, m1, m2⟩ := Ctx.eval_unit_mul base f
    simp only [Ctx.unitPolyL] at m0 m1 m2 ⊢
    rw [m0, m1, m2, a0, a1, a2, b0, b1, b2, if_neg (by decide), F192.ofLimbs_mul_ofLimbs]

/-- An `E` operation (a square ignores its second operand). -/
def opE : Op → F192 → F192 → F192
  | .add, a, b => a + b
  | .mul, a, b => a * b
  | .square, a, _ => a * a

/-- A unit's operands, either order, carry the operands' elements. -/
theorem arith_try (G : c.ctx.Good w) (op : Op) {out lx ly : Array ℕ} {base : ℕ} {A B : List ℕ}
    (hg : ∀ l < 3, c.ctx.gate (out.getD l NONE) (Ctx.unitPolyL (if (op == .add) = true then .add else .mul) base l) 0
      ((List.range 3).map (fun i => (base + i, A.getD i NONE)) ++
        (List.range 3).map (fun i => (base + 3 + i, B.getD i NONE))) = true)
    (hab : (if op == .square then A == lx.toList && B == lx.toList
      else (A == lx.toList && B == ly.toList) || (A == ly.toList && B == lx.toList)) = true) :
    c.limbsE w out.toList = opE op (c.limbsE w lx.toList) (c.limbsE w ly.toList) := by
  rw [unit_val G _ hg]
  cases op with
  | add =>
    have h2 : (Op.add == Op.square) = false := rfl
    simp only [h2, Bool.false_eq_true, ite_false, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hab
    simp only [ite_true, opE]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact add_comm _ _
  | mul =>
    have h2 : (Op.mul == Op.square) = false := rfl
    simp only [h2, Bool.false_eq_true, ite_false, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hab
    simp only [reduceCtorEq, ite_false, opE]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact mul_comm _ _
  | square =>
    simp only [beq_self_eq_true, ite_true, Bool.and_eq_true, beq_iff_eq] at hab
    simp only [reduceCtorEq, ite_false, opE]
    obtain ⟨rfl, rfl⟩ := hab
    rfl

theorem arith_ok (G : c.ctx.Good w) {op : Op} {out lx ly : Array ℕ} (h : arithOk c.ctx op out lx ly = true) :
    out.size = 3 ∧ lx.size = 3 ∧ ly.size = 3 ∧ c.limbsE w out.toList = opE op (c.limbsE w lx.toList) (c.limbsE w ly.toList) := by
  unfold arithOk at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨hs, hx⟩, hy⟩, htry⟩ := h
  refine ⟨beq_iff_eq.mp hs, beq_iff_eq.mp hx, beq_iff_eq.mp hy, ?_⟩
  rcases htry with ⟨_, ⟨hg, hab⟩⟩ | ⟨_, ⟨hg, hab⟩⟩
  · exact arith_try G op (fun l hl => (hg l hl).1) hab
  · exact arith_try G op (fun l hl => (hg l hl).1) hab

theorem limbsE_toList (a : Array ℕ) :
    c.limbsE w a.toList = F192.ofLimbs (c.ctx.val w (a.getD 0 NONE)) (c.ctx.val w (a.getD 1 NONE))
      (c.ctx.val w (a.getD 2 NONE)) := by
  simp only [limbsE, toList_getD]

/-- A live node with three limbs is an element node. -/
theorem elem_of_limbs3 (hc : c.Checked r) {x : ℕ} (hx : x < c.nodes.size) (hlx : c.live.getD x false = true)
    (h3 : (c.limbsOf x).size = 3) : isStateNode (c.nodes.getD x default) = false := by
  have hok := hc.nodes x hx hlx
  cases hn : c.nodes.getD x default with
  | seed =>
    simp only [nodeOk, hn] at hok
    split at hok
    · simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hok
      simp [limbsOf, hok.1.2] at h3
    · cases hok
  | hash s f t =>
    simp only [nodeOk, hn] at hok
    split at hok
    · simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hok
      simp [limbsOf, hok.1.1.1.1.1.2] at h3
    · cases hok
  | _ => rfl

theorem inv_add (hc : c.Checked r) (G : c.ctx.Good w) {id : ℕ} (hid : id < c.nodes.size)
    (hl : c.live.getD id false = true) {x y : ℕ} (hnode : c.nodes.getD id default = .add x y)
    (ihx : c.ElemInv r w x) (ihy : c.ElemInv r w y) : c.ElemInv r w id := by
  have hok := hc.nodes id hid hl
  simp only [nodeOk, hnode] at hok
  obtain ⟨hs, -, -, he⟩ := arith_ok G hok
  refine ⟨hs, ?_⟩
  rw [limbsE_toList, limbsE_toList, limbsE_toList] at he
  rw [he, ihx.2, ihy.2, valsW_step hc hid hl, hnode]
  rfl

theorem inv_mul (hc : c.Checked r) (G : c.ctx.Good w) {id : ℕ} (hid : id < c.nodes.size)
    (hl : c.live.getD id false = true) {x y : ℕ} (hnode : c.nodes.getD id default = .mul x y)
    (ihx : c.ElemInv r w x) (ihy : c.ElemInv r w y) : c.ElemInv r w id := by
  have hok := hc.nodes id hid hl
  simp only [nodeOk, hnode] at hok
  obtain ⟨hs, -, -, he⟩ := arith_ok G hok
  refine ⟨hs, ?_⟩
  rw [limbsE_toList, limbsE_toList, limbsE_toList] at he
  rw [he, valsW_step hc hid hl, hnode]
  by_cases hxy : x = y
  · subst hxy
    simp only [beq_self_eq_true, ite_true, opE] at he ⊢
    rw [ihx.2]; rfl
  · have : (x == y) = false := by simpa using hxy
    simp only [this, Bool.false_eq_true, ite_false, opE]
    rw [ihx.2, ihy.2]; rfl

/-! ## Reads -/

/-- A hashed read's bytes are the stream's, its bits the free bits. -/
theorem read_bits (hc : c.Checked r) (hw : c.circuit.Satisfied w) {off len : ℕ} (hlen1 : 1 ≤ len)
    (hall : ∀ k < 8 * len, (c.bitSelf.getD (8 * off + k) none).isSome) :
    off + len ≤ r.graph.streamLen ∧ ∀ i < len, ∀ j < 8, c.ctx.val w (c.streamBit (8 * (off + i) + j)) =
      ofBool (((c.streamW r w).getD (off + i) 0).toNat.testBit j) := by
  have hsz := hc.sizes.2.2.2.1
  have hb : off + len ≤ r.graph.streamLen := by
    have := hall (8 * len - 1) (by omega)
    by_contra hcon
    have : c.bitSelf.size ≤ 8 * off + (8 * len - 1) := by omega
    simp [Array.getD_eq_getD_getElem?, this] at *
  refine ⟨hb, fun i hi j hj => ?_⟩
  exact stream_bit hc hw (by omega) hj (fun j' hj' => by
    have := hall (8 * i + j') (by omega)
    rwa [show 8 * off + (8 * i + j') = 8 * (off + i) + j' by ring] at this)

theorem streamW_length : (c.streamW r w).length = r.graph.streamLen := by
  simp [streamW, decodeStream_length]

/-- The big-endian packing of a hashed read's bytes `off + a .. off + a + n`. -/
theorem read_pack (hc : c.Checked r) (G : c.ctx.Good w) (hw : c.circuit.Satisfied w) {off len a n u : ℕ}
    (hlen1 : 1 ≤ len) (hall : ∀ k < 8 * len, (c.bitSelf.getD (8 * off + k) none).isSome) (han : a + n ≤ len)
    (h : c.packIs c.packOf u (beBits c.streamBit (off + a) n) = true) :
    c.ctx.val w u = F64.ofNat (beNat (slice (c.streamW r w) (off + a) n)) := by
  obtain ⟨hb, hbits⟩ := read_bits hc hw hlen1 hall
  apply packBE_word hc G c.streamBit (c.streamW r w) (off + a) n (by rw [streamW_length]; omega) _ h
  intro i hi j hj
  have := hbits (a + i) (by omega) j hj
  rwa [show off + (a + i) = off + a + i by ring] at this

theorem inv_input_hashed (hc : c.Checked r) (G : c.ctx.Good w) (hw : c.circuit.Satisfied w) {id : ℕ}
    (hid : id < c.nodes.size) (hl : c.live.getD id false = true) {off len : ℕ}
    (hnode : c.nodes.getD id default = .input off len)
    (hfree : (c.freeReads.any fun e => e.1 == off && e.2 == c.limbsOf id) = false) : c.ElemInv r w id := by
  have hok := hc.nodes id hid hl
  simp only [nodeOk, hnode, hfree, Bool.false_eq_true, ite_false, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨hs, ⟨hlen1, hall⟩, hcase⟩ := hok
  refine ⟨hs, ?_⟩
  rw [valsW_step hc hid hl, hnode]
  simp only [Graph.step, Value.toE, inputValue]
  set S := c.streamW r w
  by_cases h24 : len = 24
  · subst h24
    rw [if_pos rfl] at hcase
    simp only [Bool.and_eq_true] at hcase
    obtain ⟨⟨p0, p1⟩, p2⟩ := hcase
    have q0 := read_pack hc G hw hlen1 hall (a := 16) (n := 8) (by norm_num) p0
    have q1 := read_pack hc G hw hlen1 hall (a := 8) (n := 8) (by norm_num) p1
    have q2 := read_pack hc G hw hlen1 hall (a := 0) (n := 8) (by norm_num) p2
    rw [q0, q1, q2, if_pos rfl, elemOfNats, slice_slice _ _ _ _ _ (by norm_num : 16 + 8 ≤ 24),
      slice_slice _ _ _ _ _ (by norm_num : 8 + 8 ≤ 24), slice_slice _ _ _ _ _ (by norm_num : 0 + 8 ≤ 24)]
  · by_cases h16 : len = 16
    · subst h16
      rw [if_neg (by decide), if_pos rfl] at hcase
      simp only [Bool.and_eq_true] at hcase
      obtain ⟨⟨p0, p1⟩, p2⟩ := hcase
      have q0 := read_pack hc G hw hlen1 hall (a := 8) (n := 8) (by norm_num) p0
      have q1 := read_pack hc G hw hlen1 hall (a := 0) (n := 8) (by norm_num) p1
      rw [q0, q1, Ctx.const_val G p2, if_neg (by decide), if_pos rfl, elemOfNats,
        slice_slice _ _ _ _ _ (by norm_num : 8 + 8 ≤ 16), slice_slice _ _ _ _ _ (by norm_num : 0 + 8 ≤ 16),
        Primitives.F64.ofNat_zero]
    · rw [if_neg h24, if_neg h16] at hcase
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcase
      obtain ⟨⟨⟨_, p0⟩, p1⟩, p2⟩ := hcase
      have q0 := read_pack hc G hw hlen1 hall (a := 0) (n := len) (by omega) p0
      rw [q0, Ctx.const_val G p1, Ctx.const_val G p2, if_neg h24, if_neg h16, elemOfNats,
        Primitives.F64.ofNat_zero]
      rfl

/-! ## Never-hashed reads -/

theorem freeReads_parts (h : c.freeReadsOk r.graph.streamLen = true) :
    (∀ a < c.freeReads.size, (c.freeReads.getD a default).2.size = 3 ∧
      (c.freeReads.getD a default).1 + 24 ≤ r.graph.streamLen ∧
      ∀ k < 192, c.bitSelf.getD (8 * (c.freeReads.getD a default).1 + k) none = none) ∧
    (∀ a < c.freeReads.size, ∀ b < c.freeReads.size, a = b ∨
      (c.freeReads.getD a default).1 + 24 ≤ (c.freeReads.getD b default).1 ∨
      (c.freeReads.getD b default).1 + 24 ≤ (c.freeReads.getD a default).1) := by
  unfold freeReadsOk at h
  simp only [Bool.and_eq_true, Array.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun a ha => ?_, fun a ha b hb => ?_⟩
  · have := h1 a ha
    have hg : c.freeReads.getD a default = c.freeReads[a] := by simp [Array.getD_eq_getD_getElem?, ha]
    rw [hg]
    obtain ⟨⟨hs, hb⟩, hn⟩ := this
    exact ⟨hs, hb, fun k hk => by simpa using allBelow_spec hn k hk⟩
  · have := allBelow_spec (allBelow_spec h2 a ha) b hb
    simpa [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, or_assoc] using this

/-- A byte of a never-hashed read is found in it. -/
theorem find_free (hc : c.Checked r) {a : ℕ} (ha : a < c.freeReads.size) {i : ℕ}
    (hi : (c.freeReads.getD a default).1 ≤ i ∧ i < (c.freeReads.getD a default).1 + 24) :
    c.freeReads.find? (fun e => e.1 ≤ i && i < e.1 + 24) = some (c.freeReads.getD a default) := by
  have hdis := (freeReads_parts hc.free).2
  have hmem : c.freeReads.getD a default ∈ c.freeReads := Ctx.getD_mem _ ha
  have hsome : (c.freeReads.find? (fun e => e.1 ≤ i && i < e.1 + 24)).isSome := by
    rw [Array.find?_isSome]; exact ⟨_, hmem, by simpa using hi⟩
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hsome
  rw [hy]
  have hpy := Array.find?_some hy
  have hym := Array.mem_of_find?_eq_some hy
  obtain ⟨b, hb, rfl⟩ := Array.mem_iff_getElem.mp hym
  have hgb : c.freeReads.getD b default = c.freeReads[b] := by simp [Array.getD_eq_getD_getElem?, hb]
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpy
  rcases hdis a ha b hb with rfl | h | h
  · rw [hgb]
  · rw [hgb] at h; omega
  · rw [hgb] at h; omega

/-- The decoded bytes of a never-hashed read are its free limbs' big-endian words. -/
theorem free_word (hc : c.Checked r) {a : ℕ} (ha : a < c.freeReads.size) (m : ℕ) (hm : m < 3) :
    beNat (slice (c.streamW r w) ((c.freeReads.getD a default).1 + 8 * m) 8) =
      (F64.toU64 (c.ctx.val w ((c.freeReads.getD a default).2.getD (2 - m) NONE))).toNat := by
  obtain ⟨_, hb, hnone⟩ := (freeReads_parts hc.free).1 a ha
  set off := (c.freeReads.getD a default).1
  set X := (F64.toU64 (c.ctx.val w ((c.freeReads.getD a default).2.getD (2 - m) NONE))).toNat
  have hX : X < 2 ^ 64 := UInt64.toNat_lt _
  apply Nat.eq_of_testBit_eq
  intro e
  rw [beNat_testBit, slice_length _ _ _ (by rw [streamW_length]; omega)]
  by_cases he : e < 64
  · simp only [show e < 8 * 8 by omega, decide_true, Bool.true_and]
    rw [slice_getD _ _ _ _ (by omega)]
    set i := off + 8 * m + (8 - 1 - e / 8)
    have hiL : i < r.graph.streamLen := by omega
    -- The decoder's byte `i`: not hashed, found in this read.
    have hns : (c.bitSelf.getD (8 * i) none).isSome = false := by
      have := hnone (8 * (i - off)) (by omega)
      rw [show 8 * off + 8 * (i - off) = 8 * i by omega] at this
      simp [this]
    have hf := find_free hc ha (i := i) ⟨by omega, by omega⟩
    simp only [streamW, decodeStream, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hiL,
      Option.map_some, Option.getD_some, hns, Bool.false_eq_true, ite_false]
    rw [hf]
    simp only
    have hk : i - off = 8 * m + (7 - e / 8) := by omega
    rw [hk, show (8 * m + (7 - e / 8)) / 8 = m by omega, show (8 * m + (7 - e / 8)) % 8 = 7 - e / 8 by omega,
      show 7 - (7 - e / 8) = e / 8 by omega]
    rw [Nat.toUInt8, UInt8.toNat_ofNat_of_lt' (by simp [UInt8.size]; omega)]
    rw [show (256 : ℕ) = 2 ^ 8 by norm_num, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    simp only [Nat.mod_lt _ (show 8 > 0 by norm_num), decide_true, Bool.true_and]
    congr 1; omega
  · simp only [show ¬ e < 8 * 8 by omega, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hX (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

theorem inv_input_free (hc : c.Checked r) (hw : c.circuit.Satisfied w) {id : ℕ}
    (hid : id < c.nodes.size) (hl : c.live.getD id false = true) {off len : ℕ}
    (hnode : c.nodes.getD id default = .input off len)
    (hfree : (c.freeReads.any fun e => e.1 == off && e.2 == c.limbsOf id) = true) : c.ElemInv r w id := by
  have hok := hc.nodes id hid hl
  simp only [nodeOk, hnode, hfree, ite_true, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨hs, h24⟩ := hok
  subst h24
  obtain ⟨a, ha, hpa⟩ := Array.any_eq_true.mp hfree
  simp only [Bool.and_eq_true, beq_iff_eq] at hpa
  have hg : c.freeReads.getD a default = c.freeReads[a] := by simp [Array.getD_eq_getD_getElem?, ha]
  have hoff : (c.freeReads.getD a default).1 = off := by rw [hg]; exact hpa.1
  have hls : (c.freeReads.getD a default).2 = c.limbsOf id := by rw [hg]; exact hpa.2
  refine ⟨hs, ?_⟩
  rw [valsW_step hc hid hl, hnode]
  simp only [Graph.step, Value.toE, inputValue]
  rw [if_pos trivial, elemOfNats, slice_slice _ _ _ _ _ (by norm_num : 16 + 8 ≤ 24),
    slice_slice _ _ _ _ _ (by norm_num : 8 + 8 ≤ 24), slice_slice _ _ _ _ _ (by norm_num : 0 + 8 ≤ 24)]
  simp only [Nat.add_zero]
  have w2 := free_word (w := w) hc ha 2 (by norm_num)
  have w1 := free_word (w := w) hc ha 1 (by norm_num)
  have w0 := free_word (w := w) hc ha 0 (by norm_num)
  rw [hoff, hls] at w2 w1 w0
  simp only [Nat.mul_zero, Nat.add_zero, show 8 * 2 = 16 by rfl, show 8 * 1 = 8 by rfl,
    show (2 : ℕ) - 2 = 0 from rfl, show (2 : ℕ) - 1 = 1 from rfl, show (2 : ℕ) - 0 = 2 from rfl] at w2 w1 w0
  rw [w2, w1, w0, ← F64.ofU64_eq_ofNat, ← F64.ofU64_eq_ofNat, ← F64.ofU64_eq_ofNat, F64.ofU64_toU64,
    F64.ofU64_toU64, F64.ofU64_toU64]

/-! ## Bit fields -/

theorem filterMap_lookup (bv : ℕ → ℕ) (shift width : ℕ) : ∀ (N e : ℕ),
    (((List.range N).map fun e => (e, bv e)).filterMap fun t =>
        if shift ≤ t.1 && t.1 < shift + width then some (t.1 - shift, t.2) else none).lookup e =
      if e < width ∧ shift + e < N then some (bv (shift + e)) else none
  | 0, e => by simp
  | N + 1, e => by
    rw [List.range_succ, List.map_append, List.filterMap_append, List.lookup_append, filterMap_lookup bv shift width N e]
    by_cases h1 : e < width ∧ shift + e < N
    · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩]; rfl
    · rw [if_neg h1]
      simp only [Option.none_or, List.map_cons, List.map_nil, List.filterMap_cons, List.filterMap_nil]
      by_cases hN : shift ≤ N ∧ N < shift + width
      · have hc : (decide (shift ≤ N) && decide (N < shift + width)) = true := by simp [hN.1, hN.2]
        rw [if_pos hc]
        by_cases he : e = N - shift
        · subst he
          simp only [List.lookup_cons, beq_self_eq_true, ite_true]
          rw [if_pos ⟨by omega, by omega⟩, show shift + (N - shift) = N by omega]
        · have : (e == N - shift) = false := by simpa using he
          simp only [List.lookup_cons, this, Bool.false_eq_true, ite_false, List.lookup_nil]
          rw [if_neg (by omega)]
      · have hc : (decide (shift ≤ N) && decide (N < shift + width)) = false := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
        rw [if_neg (by simp [hc])]
        simp only [List.lookup_nil]
        rw [if_neg (by omega)]

theorem bitField_lookup (sb : ℕ → ℕ) (off len shift width e : ℕ) :
    (bitField sb off len shift width).lookup e =
      if e < width ∧ shift + e < 8 * len then some (sb (8 * (off + len - 1 - (shift + e) / 8) + (shift + e) % 8))
      else none :=
  filterMap_lookup (fun e => sb (8 * (off + len - 1 - e / 8) + e % 8)) shift width (8 * len) e

theorem c0_ofLimbs (a b d : F64) : (F192.ofLimbs a b d).c0 = F64.toU64 a := by simp [F192.c0]

theorem toU64_ofNat (n : ℕ) : (F64.toU64 (F64.ofNat n)).toNat = n % 2 ^ 64 := by
  show (BitVec.ofNat 64 n).toNat = n % 2 ^ 64
  simp

theorem ofNat_ofBool (b : Bool) : F64.ofNat (if b then 1 else 0) = ofBool b := by
  cases b
  · simp [ofBool]
  · show F64.ofNat 1 = 1; decide

theorem inv_bits (hc : c.Checked r) (G : c.ctx.Good w) (hw : c.circuit.Satisfied w) {id : ℕ}
    (hid : id < c.nodes.size) (hl : c.live.getD id false = true) {v shift width : ℕ}
    (hnode : c.nodes.getD id default = .bits v shift width) : c.ElemInv r w id := by
  have hok := hc.nodes id hid hl
  simp only [nodeOk, hnode] at hok
  obtain ⟨hvid, hvl⟩ := (graphOk_parts hc.graph).1 id hid hl v (by simp [hnode, Node.ops])
  generalize hv : c.nodes.getD v default = nv at hok
  cases nv with
  | input off len =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
    obtain ⟨⟨⟨⟨⟨h8, hs⟩, h1⟩, h2⟩, hall⟩, hcase⟩ := hok
    set S := c.streamW r w
    set N0 := beNat (slice S off len)
    set M := N0 / 2 ^ shift % 2 ^ width
    -- The semantics: the field of the read's integer.
    have hval : ((c.valsW r w).getD id default).toE = F192.ofLimbs (F64.ofNat M) 0 0 := by
      rw [valsW_step hc hid hl, hnode]
      simp only [Graph.step, Value.toE, bitsOf, elemOfNats]
      rw [valsW_step hc (lt_trans hvid hid) hvl, hv]
      simp only [Graph.step, Value.toE, inputValue]
      rw [if_neg (by omega), if_neg (by omega), elemOfNats, c0_ofLimbs, toU64_ofNat, Primitives.F64.ofNat_zero]
      have hN : N0 < 2 ^ 64 := by
        have := beNat_lt (slice S off len)
        exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by
          have := slice_length_le S off len; omega))
      rw [Nat.mod_eq_of_lt hN]
    -- M's bits are the field's.
    have hMbit : ∀ e, M.testBit e = (decide (e < width) && N0.testBit (shift + e)) := by
      intro e
      simp only [M, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm e shift]
    have hlook := bitField_lookup c.streamBit off len shift width
    refine ⟨hs, ?_⟩
    rw [hval, Ctx.const_val G h1, Ctx.const_val G h2]
    -- The field's bits are the stream's.
    have hstream : ∀ e, e < width → shift + e < 8 * len →
        c.ctx.val w (c.streamBit (8 * (off + len - 1 - (shift + e) / 8) + (shift + e) % 8)) = ofBool (M.testBit e) := by
      intro e hew hel
      have hlen1 : 1 ≤ len := by omega
      obtain ⟨hb, hbits⟩ := read_bits hc hw hlen1 (fun k hk => hall k hk)
      have := hbits (len - 1 - (shift + e) / 8) (by omega) ((shift + e) % 8) (Nat.mod_lt _ (by norm_num))
      rw [show off + len - 1 - (shift + e) / 8 = off + (len - 1 - (shift + e) / 8) by omega, this, hMbit,
        decide_eq_true hew, Bool.true_and, beNat_testBit, slice_length _ _ _ (by rw [streamW_length]; omega),
        decide_eq_true hel, Bool.true_and, slice_getD _ _ _ _ (by omega)]
    split at hcase
    · -- No bit in the field: zero.
      rename_i hF
      rw [Ctx.const_val G hcase]
      have hM : M = 0 := by
        apply Nat.eq_of_testBit_eq
        intro e
        rw [hMbit, Nat.zero_testBit]
        have := hlook e
        rw [hF, List.lookup_nil] at this
        by_cases hew : e < width
        · have hel : ¬ shift + e < 8 * len := fun h => by rw [if_pos ⟨hew, h⟩] at this; cases this
          rw [beNat_testBit, decide_eq_false (show ¬ (shift + e < 8 * (slice S off len).length) by
            have := slice_length_le S off len; omega)]; simp
        · simp [hew]
      rw [hM, Primitives.F64.ofNat_zero]
    · -- One bit, at exponent 0: the bit itself.
      rename_i x hF
      simp only [beq_iff_eq] at hcase
      rw [hcase]
      have h0 := hlook 0
      rw [hF, List.lookup_cons_self] at h0
      by_cases hc0 : 0 < width ∧ shift + 0 < 8 * len
      · rw [if_pos hc0] at h0
        cases h0
        rw [hstream 0 hc0.1 hc0.2]
        have hM : M = if M.testBit 0 then 1 else 0 := by
          apply Nat.eq_of_testBit_eq
          intro e
          rcases Nat.eq_zero_or_pos e with rfl | he
          · cases M.testBit 0 <;> simp
          · have := hlook e
            have hne : (e == 0) = false := by simpa using he.ne'
            simp only [hF, List.lookup_cons, hne, List.lookup_nil] at this
            have hfalse : M.testBit e = false := by
              rw [hMbit]
              by_cases hew : e < width
              · have hel : ¬ shift + e < 8 * len := fun h => by rw [if_pos ⟨hew, h⟩] at this; cases this
                rw [beNat_testBit, decide_eq_false (show ¬ (shift + e < 8 * (slice S off len).length) by
                  have := slice_length_le S off len; omega)]; simp
              · simp [hew]
            rw [hfalse]
            have h1 : (1 : ℕ).testBit e = false := Nat.testBit_eq_false_of_lt (Nat.one_lt_two_pow (by omega))
            cases M.testBit 0
            · simp
            · simp only [ite_true]; exact h1.symm
        rw [show F64.ofNat M = F64.ofNat (if M.testBit 0 then 1 else 0) from by rw [← hM], ofNat_ofBool]
      · rw [if_neg hc0] at h0; cases h0
    · -- A packing of the field.
      rw [packIs_word hc G hcase M]
      intro e he
      rw [Ctx.bitAt, hlook]
      by_cases hc' : e < width ∧ shift + e < 8 * len
      · rw [if_pos hc']; exact hstream e hc'.1 hc'.2
      · rw [if_neg hc', hMbit]
        by_cases hew : e < width
        · have hel : ¬ shift + e < 8 * len := fun h => hc' ⟨hew, h⟩
          rw [beNat_testBit, decide_eq_false (show ¬ (shift + e < 8 * (slice S off len).length) by
            have := slice_length_le S off len; omega)]; simp [ofBool]
        · simp [hew, ofBool]
  | _ => simp at hok

end Compiled

end RecCircuit
