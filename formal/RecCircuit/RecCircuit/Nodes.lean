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

end Compiled

end RecCircuit
