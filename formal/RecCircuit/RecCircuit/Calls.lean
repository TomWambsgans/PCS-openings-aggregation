-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCircuit.ExpandProof

/-!
# π1's `PCS_OPEN` inputs, rebuilt from π2's ports

π2's verifier makes π1's `PCS_OPEN` calls from π2's public inputs, which the ports carry (`spec.rs`'s
`Circuit::call_inputs`): a constant word as it is; a root its port's word (`word_limbs`'s inverse); an element its
port's `element_word`; a pair's coordinate (π1-rec3's paired batch) `element_word` of `pair_point` of its element's
port (`Circuit.callWordBytes`, `Circuit.callInputs`).

On a satisfied circuit the compiler accepted, each of these words is π1's graph's word in `RecGraph`'s semantics over
Keccak-f[1600] (`compile_sound_calls`), word 0 (a call's root, a stream root or a setup root) as `PCS_OPEN`'s root
word (`machine::root_word`, each 16-byte half reversed: `pcsWord`), all other words byte for byte. The calls check
(`callsOk`) ties π2's call words to π1's; the pair's semantics (`pair_val`) is `pair_point`'s on the expanded graph's
values (`y_1 = z·z + z`, `y_0 = z + β_1 y_1`, `β_1 = UniStatement.cantorBeta1`); `expandSound` takes a node's
image's value back to the original graph.
-/

namespace RecCircuit

open Primitives LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement

/-! ## π2's rebuild (`Circuit::call_inputs`) -/

namespace Circuit

variable (C : Circuit)

/-- The 32 bytes whose `word_limbs` are four limbs (limb `l` the big-endian bytes `24 − 8l .. 32 − 8l`). -/
def limbsBytes (ls : List K) : List UInt8 :=
  be64 (K.lane (ls.getD 3 0)) ++ be64 (K.lane (ls.getD 2 0)) ++ be64 (K.lane (ls.getD 1 0)) ++
    be64 (K.lane (ls.getD 0 0))

/-- An element of its three limbs. -/
def limbsE (ls : List K) : E := eNew (K.lane (ls.getD 0 0)) (K.lane (ls.getD 1 0)) (K.lane (ls.getD 2 0))

/-- A source's port's limbs. -/
def sourceLimbs (w : ℕ → K) (s : Source) : List K := C.portLimbs w ((C.portOf s).getD 0)

/-- **π1's `PCS_OPEN` word rebuilt from π2's ports** (`Circuit::call_inputs` on the public inputs the ports carry). -/
def callWordBytes (w : ℕ → K) : CallWord → List UInt8
  | .const x => wordBytes32 x
  | .root i => limbsBytes (C.sourceLimbs w (.root i))
  | .element e => UniStatement.elementWord (limbsE (C.sourceLimbs w (.element e)))
  | .pair e co => UniStatement.elementWord ((pairPoint (limbsE (C.sourceLimbs w (.element e)))).getD co 0)

/-- **π1's `PCS_OPEN` inputs rebuilt from π2's ports**, in call order. -/
def callInputs (w : ℕ → K) : List (List UInt8) := C.calls.map (·.flatMap (C.callWordBytes w))

end Circuit

/-- **The word of a `PCS_OPEN` call at position `k`**, of the graph's word bytes: word 0 (the call's root) as
`PCS_OPEN`'s root word (`machine::root_word`). -/
def pcsWord (k : ℕ) (bytes : List UInt8) : List UInt8 := if k = 0 then rootWordBytes bytes else bytes

/-! ## Bytes -/

theorem leNat_cons (b : UInt8) (bs : List UInt8) : leNat (b :: bs) = b.toNat + 256 * leNat bs := rfl

theorem leNat_lt : ∀ s : List UInt8, leNat s < 256 ^ s.length
  | [] => by simp [leNat]
  | b :: bs => by
    rw [leNat_cons, List.length_cons, pow_succ]
    have := leNat_lt bs
    have := b.toNat_lt
    omega

theorem leNat_digit : ∀ (s : List UInt8) (j : ℕ) (hj : j < s.length), leNat s / 256 ^ j % 256 = (s[j]).toNat
  | [], j, hj => absurd hj (by simp)
  | b :: bs, 0, _ => by
    rw [leNat_cons, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.toNat_lt]
    rfl
  | b :: bs, j + 1, hj => by
    rw [leNat_cons, pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by norm_num),
      Nat.div_eq_of_lt b.toNat_lt, zero_add, leNat_digit bs j (by simpa using hj)]
    rfl

/-- `be64` of a little-endian word is its bytes reversed. -/
theorem be64_leNat (s : List UInt8) (hs : s.length = 8) : be64 (UInt64.ofNat (leNat s)) = s.reverse := by
  have hlt : leNat s < 2 ^ 64 := by
    have := leNat_lt s; rw [hs] at this; simpa using this
  apply List.ext_getElem
  · simp [be64, hs]
  · intro k h1 h2
    have hk : k < 8 := by simpa [be64] using h1
    simp only [be64, List.getElem_map, List.getElem_range, List.getElem_reverse]
    apply UInt8.toNat.inj
    rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]
    have h8 : (8 * (7 - k)).toUInt64.toNat % 64 = 8 * (7 - k) := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [h8, Nat.shiftRight_eq_div_pow, pow_mul, show (2 : ℕ) ^ 8 = 256 by norm_num,
      leNat_digit s (7 - k) (by omega)]
    have : s.length - 1 - k = 7 - k := by omega
    simp only [this]

theorem lane_ofNat (n : ℕ) : K.lane (F64.ofNat n) = UInt64.ofNat n := by
  rw [← ofLane_ofNat, lane_ofLane]

/-- **A root port's word is the root's `PCS_OPEN` word** (the stream's 32 bytes, each half reversed). -/
theorem root_bytes (raw : List UInt8) (hr : raw.length = 32) :
    Circuit.limbsBytes ((List.range 4).map fun l => F64.ofNat (leNat (slice raw ([16, 24, 0, 8].getD l 0) 8))) =
      rootWordBytes raw := by
  have hs : ∀ a, a + 8 ≤ 32 → (slice raw a 8).length = 8 := fun a ha => slice_length raw a 8 (by omega)
  show Circuit.limbsBytes [F64.ofNat (leNat (slice raw 16 8)), F64.ofNat (leNat (slice raw 24 8)),
    F64.ofNat (leNat (slice raw 0 8)), F64.ofNat (leNat (slice raw 8 8))] = _
  simp only [Circuit.limbsBytes, List.getD_cons_succ, List.getD_cons_zero, lane_ofNat]
  rw [be64_leNat _ (hs 8 (by norm_num)), be64_leNat _ (hs 0 (by norm_num)), be64_leNat _ (hs 24 (by norm_num)),
    be64_leNat _ (hs 16 (by norm_num))]
  have ht : raw.take 16 = slice raw 0 8 ++ slice raw 8 8 := by
    rw [show (16 : ℕ) = 8 + 8 from rfl, List.take_add]
    simp [slice]
  have hd : raw.drop 16 = slice raw 16 8 ++ slice raw 24 8 := by
    have hl : (raw.drop 16).length = 8 + 8 := by simp [hr]
    rw [← List.take_length (l := raw.drop 16), hl, List.take_add]
    simp [slice, List.drop_drop]
  rw [rootWordBytes, ht, hd, List.reverse_append, List.reverse_append]
  simp only [List.append_assoc]

/-- `limbsL`'s limbs rebuild the element. -/
theorem limbsE_limbsL (x : E) : Circuit.limbsE (Compiled.limbsL x) = x := by
  simp only [Circuit.limbsE, Compiled.limbsL, List.getD_cons_succ, List.getD_cons_zero]
  exact RecGraph.eNew_limbs x

/-! ## `pair_coordinate`'s shapes -/

theorem pairY1_spec {nodes : Array Node} {i z : ℕ} (h : pairY1 nodes i = some z) :
    ∃ a b, nodes.getD i default = .add a b ∧
      ((nodes.getD a default = .mul z z ∧ b = z) ∨ (nodes.getD b default = .mul z z ∧ a = z)) := by
  unfold pairY1 at h
  split at h
  · rename_i a b hab
    refine ⟨a, b, hab, ?_⟩
    obtain ⟨⟨sq, zz⟩, hmem, hf⟩ := List.exists_of_findSome?_eq_some h
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
    simp only at hf
    split at hf
    · rename_i x y hxy
      split at hf
      · rename_i hcond
        obtain ⟨h1, h2, _⟩ := hcond
        simp only [Option.some.injEq] at hf
        subst h1 h2 hf
        rcases hmem with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · subst h3 h4; exact Or.inl ⟨hxy, rfl⟩
        · subst h3 h4; exact Or.inr ⟨hxy, rfl⟩
      · cases hf
    · cases hf
  · cases h

theorem pairCoordinate_spec {nodes : Array Node} {id z co : ℕ} (h : pairCoordinate nodes id = some (z, co)) :
    (co = 1 ∧ pairY1 nodes id = some z) ∨
    (co = 0 ∧ ∃ a b, nodes.getD id default = .add a b ∧ ∃ p, ((a = z ∧ b = p) ∨ (b = z ∧ a = p)) ∧
      ∃ x y, nodes.getD p default = .mul x y ∧ ∃ cc yy, ((x = cc ∧ y = yy) ∨ (y = cc ∧ x = yy)) ∧
        ∃ l0 l1 l2, nodes.getD cc default = .const l0 l1 l2 ∧ F192.new l0 l1 l2 = UniStatement.cantorBeta1 ∧
          pairY1 nodes yy = some z) := by
  unfold pairCoordinate at h
  split at h
  · rename_i zz hy
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1 h2
    exact Or.inl ⟨rfl, hy⟩
  · right
    split at h
    · rename_i a b hab
      obtain ⟨⟨zz, p⟩, hmem, hf⟩ := List.exists_of_findSome?_eq_some h
      simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
      simp only at hf
      split at hf
      · rename_i x y hxy
        obtain ⟨⟨cc, yy⟩, hmem2, hf2⟩ := List.exists_of_findSome?_eq_some hf
        simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem2
        simp only at hf2
        split at hf2
        · rename_i l0 l1 l2 hcc
          split at hf2
          · rename_i hcond
            simp only [Option.some.injEq, Prod.mk.injEq] at hf2
            obtain ⟨h1, h2⟩ := hf2
            subst h1 h2
            refine ⟨rfl, a, b, hab, p, ?_, x, y, hxy, cc, yy, ?_, l0, l1, l2, hcc, hcond.1, hcond.2⟩
            · rcases hmem with ⟨h3, h4⟩ | ⟨h3, h4⟩
              · exact Or.inl ⟨h3.symm, h4.symm⟩
              · exact Or.inr ⟨h3.symm, h4.symm⟩
            · rcases hmem2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
              · exact Or.inl ⟨h3.symm, h4.symm⟩
              · exact Or.inr ⟨h3.symm, h4.symm⟩
          · cases hf2
        · cases hf2
      · cases hf
    · cases h

/-! ## The expanded graph's values: sums, products, constants, pairs -/

namespace Compiled

variable {c : Compiled} {r : Recorded}

theorem live_lt (hc : c.Checked r) {q : ℕ} (hl : c.live.getD q false = true) : q < c.nodes.size := by
  rw [← hc.sizes.1]
  by_contra h
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt h)] at hl

theorem live_ops (hc : c.Checked r) {q : ℕ} (hl : c.live.getD q false = true) {o : ℕ}
    (ho : o ∈ (c.nodes.getD q default).ops) : c.live.getD o false = true :=
  ((graphOk_parts hc.graph).1 q (live_lt hc hl) hl o ho).2

theorem rgX_live (hc : c.Checked r) (iv pub stream : List UInt8) {q : ℕ} (hl : c.live.getD q false = true) :
    (c.rgX iv pub stream)[q]? = some (rgStep iv pub stream (c.rgX iv pub stream) (c.nodes.getD q default)) :=
  rgX_node c iv pub stream (live_lt hc hl) (not_ringWeight hc (live_lt hc hl) hl)
    fun o ho => ((graphOk_parts hc.graph).1 q (live_lt hc hl) hl o ho).1

theorem rgX_add (hc : c.Checked r) (iv pub stream : List UInt8) {q a b : ℕ} (hl : c.live.getD q false = true)
    (hn : c.nodes.getD q default = .add a b) :
    RecGraph.valE (c.rgX iv pub stream) q =
      RecGraph.valE (c.rgX iv pub stream) a + RecGraph.valE (c.rgX iv pub stream) b := by
  have h := rgX_live hc iv pub stream hl
  rw [hn] at h
  exact valE_elem (h.trans (congrArg some (stepP_add _ _ _ _)))

theorem rgX_mul (hc : c.Checked r) (iv pub stream : List UInt8) {q a b : ℕ} (hl : c.live.getD q false = true)
    (hn : c.nodes.getD q default = .mul a b) :
    RecGraph.valE (c.rgX iv pub stream) q =
      RecGraph.valE (c.rgX iv pub stream) a * RecGraph.valE (c.rgX iv pub stream) b := by
  have h := rgX_live hc iv pub stream hl
  rw [hn] at h
  exact valE_elem (h.trans (congrArg some (stepP_mul _ _ _ _)))

theorem rgX_const (hc : c.Checked r) (iv pub stream : List UInt8) {q : ℕ} {c0 c1 c2 : UInt64}
    (hl : c.live.getD q false = true) (hn : c.nodes.getD q default = .const c0 c1 c2) :
    RecGraph.valE (c.rgX iv pub stream) q = eNew c0 c1 c2 := by
  have h := rgX_live hc iv pub stream hl
  rw [hn] at h
  exact valE_elem (h.trans (congrArg some (stepP_const _ _ _ _ _)))

/-- `y_1(z) = z·z + z` (`pair_coordinate`'s `y1_of`). -/
theorem y1_val (hc : c.Checked r) (iv pub stream : List UInt8) {i z : ℕ} (hl : c.live.getD i false = true)
    (h : pairY1 c.nodes i = some z) :
    RecGraph.valE (c.rgX iv pub stream) i =
      RecGraph.valE (c.rgX iv pub stream) z * RecGraph.valE (c.rgX iv pub stream) z +
        RecGraph.valE (c.rgX iv pub stream) z := by
  obtain ⟨a, b, hab, hcase⟩ := pairY1_spec h
  have hops : ∀ o ∈ [a, b], c.live.getD o false = true := fun o ho => live_ops hc hl (by rw [hab]; exact ho)
  rw [rgX_add hc iv pub stream hl hab]
  rcases hcase with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · rw [rgX_mul hc iv pub stream (hops a (by simp)) ha, hb]
  · rw [rgX_mul hc iv pub stream (hops b (by simp)) hb, ha, add_comm]

/-- **A pair's coordinate is `pair_point`'s** (π1-rec3's paired batch: `y_0 = z + β_1 y_1`, `y_1 = z·z + z`), on the
expanded graph's values. -/
theorem pair_val (hc : c.Checked r) (iv pub stream : List UInt8) {p z co : ℕ} (hl : c.live.getD p false = true)
    (h : pairCoordinate c.nodes p = some (z, co)) :
    RecGraph.valE (c.rgX iv pub stream) p = (pairPoint (RecGraph.valE (c.rgX iv pub stream) z)).getD co 0 := by
  rcases pairCoordinate_spec h with ⟨hco, hy⟩ | ⟨hco, a, b, hab, pp, hzp, x, y, hxy, cc, yy, hcy, l0, l1, l2, hcc,
    hbeta, hyy⟩
  · subst hco
    rw [y1_val hc iv pub stream hl hy]
    simp [pairPoint]
  · subst hco
    have hab' : ∀ o ∈ [a, b], c.live.getD o false = true := fun o ho => live_ops hc hl (by rw [hab]; exact ho)
    have hpp : c.live.getD pp false = true := by
      rcases hzp with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact hab' pp (by simp [← h2])
      · exact hab' pp (by simp [← h2])
    have hxy' : ∀ o ∈ [x, y], c.live.getD o false = true := fun o ho => live_ops hc hpp (by rw [hxy]; exact ho)
    have hccl : c.live.getD cc false = true := by
      rcases hcy with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hxy' cc (by simp [← h1])
      · exact hxy' cc (by simp [← h1])
    have hyyl : c.live.getD yy false = true := by
      rcases hcy with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact hxy' yy (by simp [← h2])
      · exact hxy' yy (by simp [← h2])
    have hne : eNew l0 l1 l2 = F192.new l0 l1 l2 := rfl
    have hcv : RecGraph.valE (c.rgX iv pub stream) cc = UniStatement.cantorBeta1 := by
      rw [rgX_const hc iv pub stream hccl hcc, hne, hbeta]
    have hyv := y1_val hc iv pub stream hyyl hyy
    have hprod : RecGraph.valE (c.rgX iv pub stream) pp = UniStatement.cantorBeta1 *
        (RecGraph.valE (c.rgX iv pub stream) z * RecGraph.valE (c.rgX iv pub stream) z +
          RecGraph.valE (c.rgX iv pub stream) z) := by
      rw [rgX_mul hc iv pub stream hpp hxy]
      rcases hcy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2, hcv, hyv]
      · rw [h1, h2, hcv, hyv, mul_comm]
    rw [rgX_add hc iv pub stream hl hab]
    have hsum : RecGraph.valE (c.rgX iv pub stream) a + RecGraph.valE (c.rgX iv pub stream) b =
        RecGraph.valE (c.rgX iv pub stream) z + RecGraph.valE (c.rgX iv pub stream) pp := by
      rcases hzp with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, add_comm]
    rw [hsum, hprod]
    simp [pairPoint]

/-! ## The calls -/

theorem portOf_spec {C : Circuit} {s : Source} {J : ℕ} (h : C.portOf s = some J) :
    J < C.ports.size ∧ (C.ports.getD J default).source = s := by
  unfold Circuit.portOf at h
  obtain ⟨hJ, hp, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp h
  refine ⟨hJ, ?_⟩
  simp only [beq_iff_eq] at hp
  simpa [Array.getD_eq_getD_getElem?, hJ] using hp

/-- A root's 32 bytes are in the stream. -/
theorem root_in (hc : c.Checked r) {i : ℕ} (hi : i < r.rootsAt.length) :
    r.rootsAt.getD i 0 + 32 ≤ r.graph.streamLen := by
  have hro := hc.roots
  unfold rootsOk at hro
  simp only [Bool.and_eq_true, beq_iff_eq] at hro
  have hr := allBelow_spec hro.2 i hi
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hr
  have h255 := hr.1.2 255 (by norm_num)
  have hsz := hc.sizes.2.2.2.1
  by_contra hcon
  have : c.bitSelf.size ≤ 8 * r.rootsAt.getD i 0 + 255 := by omega
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none this] at h255
  simp at h255

variable {g : RecGraph.Graph} {rootsAt : List ℕ} {iv : List UInt8}

theorem calls_getD (g : RecGraph.Graph) (rootsAt : List ℕ) (iv : List UInt8) {ci : ℕ} (hci : ci < g.calls.length) :
    (ofRG g rootsAt iv).graph.calls.getD ci [] = (g.calls.getD ci []).map ofRGWord := by
  show (g.calls.map (·.map ofRGWord)).getD ci [] = _
  simp [List.getD_eq_getElem?_getD, hci]

theorem word_getD {ws : List RecGraph.Word} {k : ℕ} (hk : k < ws.length) :
    (ws.map ofRGWord).getD k default = ofRGWord (ws.getD k default) := by
  simp [List.getD_eq_getElem?_getD, hk]

/-- A call's node word names a node of the original graph (`Graph.outputsIn`). -/
theorem call_node_lt (hc : compile (ofRG g rootsAt iv) = .ok c) {ci k id : ℕ} (hci : ci < g.calls.length)
    (hk : k < (g.calls.getD ci []).length) (hw : (g.calls.getD ci []).getD k default = .node id) :
    id < g.nodes.size := by
  obtain ⟨ht, -⟩ := compileRaw_ok (compileRaw_of_compile hc)
  simp only [Graph.typed, Graph.outputsIn, Bool.and_eq_true, List.all_eq_true] at ht
  have hm1 : (g.calls.getD ci []).map ofRGWord ∈ (ofRG g rootsAt iv).graph.calls := by
    rw [← calls_getD g rootsAt iv hci, List.getD_eq_getElem _ _ (by simpa [ofRG] using hci)]
    exact List.getElem_mem _
  have hmem : (g.calls.getD ci []).getD k default ∈ g.calls.getD ci [] := by
    rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  rw [hw] at hmem
  have hm2 : Word.node id ∈ (g.calls.getD ci []).map ofRGWord := List.mem_map_of_mem (f := ofRGWord) hmem
  have := ht.2.2 _ hm1 _ hm2
  simpa [ofRG] using this

/-- **π2's `PCS_OPEN` inputs, rebuilt from its ports, are π1's graph's call words**, in `RecGraph`'s semantics over
Keccak-f[1600], on the public input and the stream the witness encodes: word by word, word 0 (each call's root) as
`PCS_OPEN`'s root word (`pcsWord`), pairs' coordinates included. -/
theorem compile_sound_calls (hc : compile (ofRG g rootsAt iv) = .ok c) {pub : ℕ → List F192} {w : ℕ → K}
    (hw : c.circuit.toPiop.Satisfies pub (emb w)) :
    c.circuit.calls.length = g.calls.length ∧
    ∀ ci < g.calls.length, (c.circuit.calls.getD ci []).length = (g.calls.getD ci []).length ∧
      ∀ k < (g.calls.getD ci []).length,
        c.circuit.callWordBytes w ((c.circuit.calls.getD ci []).getD k default) =
          pcsWord k (RecGraph.wordBytes (c.streamW (ofRG g rootsAt iv) w).toArray
            (rgVals g iv (c.pubW w) (c.streamW (ofRG g rootsAt iv) w)) ((g.calls.getD ci []).getD k default)) := by
  have hchk := checked_of_compile hc
  have hcalls := hchk.calls
  unfold callsOk at hcalls
  simp only [Bool.and_eq_true, beq_iff_eq] at hcalls
  have hlen : (ofRG g rootsAt iv).graph.calls.length = g.calls.length := by simp [ofRG]
  refine ⟨hcalls.1.trans hlen, fun ci hci => ?_⟩
  have hcall := allBelow_spec hcalls.2 ci (by rw [hlen]; exact hci)
  simp only [Bool.and_eq_true, beq_iff_eq] at hcall
  rw [calls_getD g rootsAt iv hci, List.length_map] at hcall
  refine ⟨hcall.1, fun k hk => ?_⟩
  have hword := allBelow_spec hcall.2 k hk
  rw [word_getD hk] at hword
  set S := c.streamW (ofRG g rootsAt iv) w
  set P := c.pubW w
  have hE := expandSound hc iv P S
  rcases hgw : (g.calls.getD ci []).getD k default with id | v | at_ <;>
    rw [hgw] at hword <;>
    rcases hcw : (c.circuit.calls.getD ci []).getD k default with x | i | e | ⟨e, co⟩ <;>
    rw [hcw] at hword <;>
    simp only [ofRGWord, wordOk, Bool.false_eq_true] at hword
  · -- a constant element
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hword
    obtain ⟨⟨hk0, hlive⟩, hm⟩ := hword
    split at hm
    · rename_i c0 c1 c2 hn
      rw [beq_iff_eq] at hm
      have hid := call_node_lt hc hci hk hgw
      show wordBytes32 x = pcsWord k (UniStatement.elementWord _)
      rw [hm, pcsWord, ite_eq_right_of_eq_false _ _ (eq_false hk0), ← hE id hid, rgX_const hchk iv P S hlive hn]
    · cases hm
  · -- an element port
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, decide_eq_true_eq] at hword
    obtain ⟨⟨⟨⟨hk0, _⟩, _⟩, hmap⟩, hsome⟩ := hword
    obtain ⟨J, hJs⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨hJ, hs⟩ := portOf_spec hJs
    have hid := call_node_lt hc hci hk hgw
    show UniStatement.elementWord (Circuit.limbsE (c.circuit.portLimbs w ((c.circuit.portOf (.element e)).getD 0))) =
      pcsWord k (UniStatement.elementWord _)
    rw [hJs, Option.getD_some, compile_sound_element hc hw (expandSound hc) hJ hs hid hmap.symm, limbsE_limbsL,
      pcsWord, ite_eq_right_of_eq_false _ _ (eq_false hk0)]
  · -- a pair's coordinate
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, decide_eq_true_eq] at hword
    obtain ⟨⟨⟨⟨⟨hk0, hlive⟩, hesz⟩, _⟩, hpc⟩, hsome⟩ := hword
    obtain ⟨J, hJs⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨hJ, hs⟩ := portOf_spec hJs
    have hid := call_node_lt hc hci hk hgw
    have hzmem := (graphOk_parts hchk.graph).2.2.1 (c.elementNodes.getD e 0) (by
      apply List.mem_append_right
      simp [Array.getD_eq_getD_getElem?, hesz])
    obtain ⟨b, hb, hcorr⟩ := agree hchk P S (decodePublic_length _) streamW_length _ hzmem.1 hzmem.2
    have hz : ((c.valsW (ofRG g rootsAt iv) w).getD (c.elementNodes.getD e 0) default).toE =
        RecGraph.valE (c.rgX iv P S) (c.elementNodes.getD e 0) := Corr.toE hcorr hb
    have hport : c.circuit.portLimbs w J = limbsL (RecGraph.valE (c.rgX iv P S) (c.elementNodes.getD e 0)) := by
      rw [compile_sound hc hw J hJ, portMeaning, hs]
      exact congrArg limbsL hz
    show UniStatement.elementWord ((pairPoint (Circuit.limbsE (c.circuit.portLimbs w
      ((c.circuit.portOf (.element e)).getD 0)))).getD co 0) = pcsWord k (UniStatement.elementWord _)
    rw [hJs, Option.getD_some, hport, limbsE_limbsL, pcsWord, ite_eq_right_of_eq_false _ _ (eq_false hk0), ← hE id hid,
      pair_val hchk iv P S hlive hpc]
  · -- a constant word
    rw [beq_iff_eq] at hword
    show wordBytes32 x = pcsWord k (RecGraph.beBytes32 v)
    rw [hword]
    rfl
  · -- a stream root
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hword
    obtain ⟨⟨⟨hk0, hi⟩, hat⟩, hsome⟩ := hword
    obtain ⟨J, hJs⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨hJ, hs⟩ := portOf_spec hJs
    have hin := root_in hchk hi
    have hraw : ((S.toArray.extract at_ (at_ + 32)).toList).length = 32 := by
      have : S.length = (ofRG g rootsAt iv).graph.streamLen := streamW_length
      simp only [Array.length_toList, Array.size_extract, List.size_toArray]
      rw [hat] at hin
      omega
    show Circuit.limbsBytes (c.circuit.portLimbs w ((c.circuit.portOf (.root i)).getD 0)) =
      pcsWord k ((S.toArray.extract at_ (at_ + 32)).toList)
    rw [hJs, Option.getD_some, compile_sound_root hc hw hJ hs, pcsWord, ite_eq_left_of_eq_true _ _ (eq_true hk0)]
    have hat' : rootsAt.getD i 0 = at_ := hat
    rw [hat']
    exact root_bytes _ hraw

theorem flatMap_range {α β : Type} (l : List α) (d : α) (f : α → List β) :
    l.flatMap f = (List.range l.length).flatMap fun k => f (l.getD k d) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, ih]
    rfl

/-- **π2's `PCS_OPEN` inputs, rebuilt from its ports, call by call**: each call's bytes are π1's graph's, word 0 as
`PCS_OPEN`'s root word. -/
theorem compile_sound_callInputs (hc : compile (ofRG g rootsAt iv) = .ok c) {pub : ℕ → List F192} {w : ℕ → K}
    (hw : c.circuit.toPiop.Satisfies pub (emb w)) :
    c.circuit.callInputs w = g.calls.map fun ws => (List.range ws.length).flatMap fun k =>
      pcsWord k (RecGraph.wordBytes (c.streamW (ofRG g rootsAt iv) w).toArray
        (rgVals g iv (c.pubW w) (c.streamW (ofRG g rootsAt iv) w)) (ws.getD k default)) := by
  obtain ⟨hlen, hcall⟩ := compile_sound_calls hc hw
  unfold Circuit.callInputs
  apply List.ext_getElem
  · simp [hlen]
  · intro ci h1 h2
    have hci : ci < g.calls.length := by simpa using h2
    obtain ⟨hl, hwd⟩ := hcall ci hci
    simp only [List.getElem_map]
    have e1 : c.circuit.calls[ci]'(by simpa using h1) = c.circuit.calls.getD ci [] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1 : ci < c.circuit.calls.length)]
    have e2 : g.calls[ci] = g.calls.getD ci [] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hci]
    rw [e1, e2, flatMap_range _ default, hl]
    apply List.flatMap_congr
    intro k hk
    exact hwd k (by simpa using hk)

end Compiled

end RecCircuit
