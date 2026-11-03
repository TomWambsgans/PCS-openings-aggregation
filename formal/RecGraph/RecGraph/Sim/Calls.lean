-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.ComposeSpec

/-!
# The calls' bytes: the graph's words against `pcsCalls`

The recorded graph's `PCS_OPEN` words (`callsOf`: a root as the stream's 32 bytes at its first half's offset, the
layout and setup-root words as constants, the claim count `1`, the point's and the value's elements) read, byte for
byte, as `UniStatement`'s `pcsCalls` (`rootWord` of `next_root`'s halves, the layout words, `numberWord 1`,
`elementWord`):

* `beBytes32_beNat`: a 32-byte word survives `beNat` then `beBytes32`; `beBytes32_one`;
* `be64_beWordAt`: `be64` of the word `beWordAt` reads is the eight bytes it read;
* `rootWord_extract`: a root's halves, read at `off` and `off + 16`, give the stream's 32 bytes at `off`;
* `InputsBelow`, `inputsBelow_record`: every stream read the recorder holds ends below its cursor;
* `calls_eq`: the calls of a run related by `RedR`, on a stream of the record's length.
-/

-- The judgment is `RecGraph.Sim.Sim`.
set_option linter.dupNamespace false

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement RecGraph.Pi1

/-! ## Big-endian numbers -/

theorem beNat_append (l : List UInt8) (b : UInt8) : beNat (l ++ [b]) = beNat l * 256 + b.toNat := by
  unfold beNat; rw [List.foldl_append]; rfl

theorem beNat_lt (l : List UInt8) : beNat l < 256 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [beNat]
  | append_singleton l b ih =>
    rw [beNat_append, List.length_append, List.length_singleton, pow_succ]
    have hb : b.toNat < 256 := b.toNat_lt
    omega

/-- **Digit `j` of `beNat l`** (big-endian, base `256`) is byte `j`. -/
theorem beNat_digit (l : List UInt8) :
    ∀ j (hj : j < l.length), beNat l / 256 ^ (l.length - 1 - j) % 256 = (l[j]).toNat := by
  induction l using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton l b ih =>
    intro j hj
    have hb : b.toNat < 256 := b.toNat_lt
    have hlen : (l ++ [b]).length = l.length + 1 := by simp
    rw [beNat_append]
    rcases Nat.lt_or_ge j l.length with h | h
    · have e : (l ++ [b]).length - 1 - j = (l.length - 1 - j) + 1 := by omega
      rw [List.getElem_append_left h, e, pow_succ', ← Nat.div_div_eq_div_mul,
        show (beNat l * 256 + b.toNat) / 256 = beNat l by omega]
      exact ih j h
    · have hj' : j = l.length := by omega
      subst hj'
      have e : (l ++ [b]).length - 1 - l.length = 0 := by omega
      rw [List.getElem_append_right (le_refl _), e, pow_zero, Nat.div_one]
      simp only [Nat.sub_self, List.getElem_singleton]
      omega

/-- **A 32-byte word**, as a number and back (`beBytes32 (beNat w) = w`). -/
theorem beBytes32_beNat (l : List UInt8) (hl : l.length = 32) : beBytes32 (beNat l) = l := by
  apply List.ext_getElem
  · simp [beBytes32, hl]
  · intro k h1 h2
    have hk : k < 32 := by simpa [beBytes32] using h1
    simp only [beBytes32, List.getElem_map, List.getElem_range]
    have e : beNat l >>> (8 * (31 - k)) % 256 = (l[k]).toNat := by
      rw [Nat.shiftRight_eq_div_pow, show 2 ^ (8 * (31 - k)) = 256 ^ (l.length - 1 - k) by
        rw [hl, pow_mul]; norm_num]
      exact beNat_digit l k (by omega)
    rw [e]
    exact UInt8.ofNat_toNat

theorem beBytes32_one : beBytes32 1 = numberWord 1 := by decide

/-! ## `be64` of `beWordAt` -/

/-- The fold `beWordAt` does, as a number: the bytes' big-endian number. -/
theorem beFold_toNat (f : Nat → UInt8) : ∀ j ≤ 8,
    ((List.range j).foldl (fun (acc : UInt64) k ↦ (acc <<< 8) ||| (f k).toUInt64) (0 : UInt64)).toNat =
      beNat ((List.range j).map f)
  | 0, _ => by simp [beNat]
  | j + 1, hj => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, List.map_append, List.map_singleton,
      beNat_append, UInt64.toNat_or, UInt64.toNat_shiftLeft, beFold_toNat f j (by omega), UInt8.toNat_toUInt64]
    have h8 : (8 : UInt64).toNat % 64 = 8 := rfl
    rw [h8]
    have hlt := beNat_lt ((List.range j).map f)
    simp only [List.length_map, List.length_range] at hlt
    have hpow : (256 : Nat) ^ j ≤ 2 ^ 56 := by
      calc (256 : Nat) ^ j ≤ 256 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 ^ 56 := by norm_num
    have hb : (f j).toNat < 2 ^ 8 := (f j).toNat_lt
    have hsl : beNat ((List.range j).map f) <<< 8 = beNat ((List.range j).map f) * 2 ^ 8 := Nat.shiftLeft_eq _ _
    have hmul : beNat ((List.range j).map f) * 2 ^ 8 < 2 ^ 64 := by
      calc beNat ((List.range j).map f) * 2 ^ 8 < 256 ^ j * 2 ^ 8 :=
            Nat.mul_lt_mul_of_pos_right hlt (by norm_num)
        _ ≤ 2 ^ 56 * 2 ^ 8 := Nat.mul_le_mul_right _ hpow
        _ = 2 ^ 64 := by norm_num
    rw [hsl, Nat.mod_eq_of_lt hmul, ← hsl, ← Nat.shiftLeft_add_eq_or_of_lt hb, hsl]
    norm_num

/-- **`beWordAt`'s word**, as a number: the eight bytes' big-endian number. -/
theorem beWordAt_toNat (b : Array UInt8) (k : Nat) :
    (beWordAt b k).toNat = beNat ((List.range 8).map fun j ↦ b.getD (k + j) 0) :=
  beFold_toNat _ 8 le_rfl

/-- Byte `j` of `be64 w`, as a number: the word's base-256 digit `7 − j`. -/
theorem be64_getElem_toNat (w : UInt64) {j : Nat} (hj : j < 8) :
    ((be64 w)[j]'(by simp [be64, hj])).toNat = w.toNat / 2 ^ (8 * (7 - j)) % 256 := by
  simp only [be64, List.getElem_map, List.getElem_range]
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, UInt64.toNat_ofNat']
  have h1 : 8 * (7 - j) % 2 ^ 64 = 8 * (7 - j) := Nat.mod_eq_of_lt (by omega)
  have h2 : 8 * (7 - j) % 64 = 8 * (7 - j) := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2]

/-- **`be64` of the word at `k`** is the eight bytes there. -/
theorem be64_beWordAt (b : Array UInt8) (k : Nat) :
    be64 (beWordAt b k) = (List.range 8).map fun j ↦ b.getD (k + j) 0 := by
  apply List.ext_getElem
  · simp [be64]
  · intro j h1 h2
    have hj : j < 8 := by simpa [be64] using h1
    apply UInt8.toNat_inj.mp
    rw [be64_getElem_toNat _ hj, beWordAt_toNat, show 2 ^ (8 * (7 - j)) = 256 ^ (((List.range 8).map fun j ↦
      b.getD (k + j) 0).length - 1 - j) by simp only [List.length_map, List.length_range]; rw [pow_mul]; norm_num,
      beNat_digit _ j (by simpa using hj)]

/-! ## A root's word -/

/-- The stream's byte `off + i`, through an extract. -/
theorem getD_extract' (s : Array UInt8) (off n i : Nat) (h : off + n ≤ s.size) (hi : i < n) :
    (s.extract off (off + n)).getD i 0 = s.getD (off + i) 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  rw [ite_eq_left (by omega)]

/-- An extract's bytes, one by one. -/
theorem range_extract (s : Array UInt8) (off n : Nat) (h : off + n ≤ s.size) :
    (s.extract off (off + n)).toList = (List.range n).map fun i ↦ s.getD (off + i) 0 := by
  apply List.ext_getElem
  · simp only [Array.length_toList, Array.size_extract, List.length_map, List.length_range]; omega
  · intro i h1 h2
    have hi : i < n := by simpa using h2
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList, Array.getElem_extract]
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega : off + i < s.size)]

/-- Thirty-two values in four blocks of eight. -/
theorem blocks (f : Nat → UInt8) :
    (List.range 8).map (fun j ↦ f (0 + j)) ++ (List.range 8).map (fun j ↦ f (8 + j)) ++
      (List.range 8).map (fun j ↦ f (16 + j)) ++ (List.range 8).map (fun j ↦ f (24 + j)) =
        (List.range 32).map f := rfl

/-- Eight bytes of a 16-byte extract, as the stream's. -/
theorem block_extract (s : Array UInt8) (off a k c : Nat) (h : a + 16 ≤ s.size) (hk : k + 8 ≤ 16)
    (hc : a + k = off + c) :
    ((List.range 8).map fun j ↦ (s.extract a (a + 16)).getD (k + j) 0) =
      (List.range 8).map fun j ↦ s.getD (off + (c + j)) 0 := by
  refine List.map_congr_left fun j hj ↦ ?_
  have hj8 := List.mem_range.mp hj
  rw [getD_extract' s a 16 _ h (by omega)]
  congr 1
  omega

/-- **A root's halves read at `off` and `off + 16`**: their `rootWord` is the stream's 32 bytes at `off`. -/
theorem rootWord_extract (s : Array UInt8) (off : Nat) (h : off + 32 ≤ s.size) :
    rootWord (inputValue (s.extract off (off + 16)) 16, inputValue (s.extract (off + 16) (off + 16 + 16)) 16) =
      (s.extract off (off + 32)).toList := by
  rw [inputValue_16, inputValue_16, range_extract s off 32 h, ← blocks]
  show be64 (beWordAt (s.extract off (off + 16)) 0) ++ be64 (beWordAt (s.extract off (off + 16)) 8) ++
    be64 (beWordAt (s.extract (off + 16) (off + 16 + 16)) 0) ++
      be64 (beWordAt (s.extract (off + 16) (off + 16 + 16)) 8) = _
  rw [be64_beWordAt, be64_beWordAt, be64_beWordAt, be64_beWordAt,
    block_extract s off off 0 0 (by omega) (by omega) (by omega),
    block_extract s off off 8 8 (by omega) (by omega) (by omega),
    block_extract s off (off + 16) 0 16 (by omega) (by omega) (by omega),
    block_extract s off (off + 16) 8 24 (by omega) (by omega) (by omega)]

theorem layoutWord_length (s : UniStatement.Shape) (code vars placed : Nat) : (layoutWord s code vars placed).length = 32 := by
  simp [layoutWord, shapeBytes]

theorem digestBytes_len (d : Digest) : (KeccakHash.digestBytes d).length = 32 := by
  obtain ⟨⟨l⟩, hl⟩ := d
  match l, hl with
  | [_, _, _, _], _ => rfl

/-! ## The recorder reads below its cursor -/

/-- **Every stream read the recorder holds ends below its cursor.** -/
def InputsBelow (st : RecState) : Prop :=
  ∀ off len, Node.input off len ∈ st.nodes.toList → off + len ≤ st.cursor

theorem new_mem (st : RecState) (n n' : Node) (h : n' ∈ (st.new n).2.nodes.toList) :
    n' ∈ st.nodes.toList ∨ n' = n := by
  unfold RecState.new at h
  split at h
  · exact Or.inl h
  · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at h
    exact h

theorem inputsBelow_new (st : RecState) (n : Node) (hn : ∀ off len, n ≠ .input off len) (h : InputsBelow st) :
    InputsBelow (st.new n).2 := by
  intro off len hm
  rw [(new_fields st n).1]
  rcases new_mem st n _ hm with hm | e
  · exact h off len hm
  · exact absurd e.symm (hn off len)

theorem inputsBelow_op (st : RecState) (o : Op) (h : InputsBelow st) : InputsBelow (st.op o).2 := by
  have nn : ∀ (n : Node), (∀ off len, n ≠ .input off len) → InputsBelow (st.new n).2 :=
    fun n hn ↦ inputsBelow_new st n hn h
  cases o with
  | constant x => exact nn _ fun _ _ e ↦ by cases e
  | statement k => exact nn _ fun _ _ e ↦ by cases e
  | input len =>
    show InputsBelow (st.input len).2
    unfold RecState.input
    have hm0 := new_mem st (.input st.cursor len)
    revert hm0
    cases st.new (.input st.cursor len) with
    | mk i st' =>
      intro hm0 off l hm
      rcases hm0 _ hm with hm' | e'
      · have := h off l hm'
        show off + l ≤ st.cursor + len
        omega
      · cases e'
        exact le_refl _
  | sample narrow =>
    show InputsBelow (st.sample narrow).2
    rw [sample_eq]
    have h1 : InputsBelow (afterHash st) := nn (.hash st.state st.absorbed st.cursor) fun _ _ e ↦ by cases e
    exact inputsBelow_new (afterHash st) _ (fun _ _ e ↦ by split at e <;> cases e) h1
  | add a b =>
    show InputsBelow (st.add a b).2
    unfold RecState.add RecState.constant
    split
    · exact nn _ fun _ _ e ↦ by cases e
    · split
      · exact h
      · split
        · exact h
        · split
          · exact nn _ fun _ _ e ↦ by cases e
          · exact nn _ fun _ _ e ↦ by cases e
  | mul a b =>
    show InputsBelow (st.mul a b).2
    unfold RecState.mul RecState.constant
    split
    · exact nn _ fun _ _ e ↦ by cases e
    · split
      · exact nn _ fun _ _ e ↦ by cases e
      · split
        · exact h
        · split
          · exact h
          · exact nn _ fun _ _ e ↦ by cases e
  | bits v s w =>
    show InputsBelow (st.bits v s w).2
    unfold RecState.bits RecState.constant
    split
    · exact nn _ fun _ _ e ↦ by cases e
    · exact nn _ fun _ _ e ↦ by cases e
  | ringWeight p o m =>
    show InputsBelow (st.ringWeight p o m).2
    unfold RecState.ringWeight
    exact inputsBelow_new _ _ (fun _ _ e ↦ by cases e) h

/-- **Recording keeps the reads below the cursor.** -/
theorem inputsBelow_record {α : Type} (p : Prog α) (st : RecState) (h : InputsBelow st) :
    InputsBelow (p.record st).2 := by
  induction p generalizing st with
  | pure a => exact h
  | op o k ih => exact ih _ _ (inputsBelow_op st o h)
  | zero v k ih => exact ih { st with zero := st.zero.push v } h
  | nonzero v k ih => exact ih { st with nonzero := st.nonzero.push v } h

theorem inputsBelow_start : InputsBelow RecState.start := by
  intro off len hm
  rw [start_nodes] at hm
  simp at hm

/-! ## The calls -/

section Calls

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- A stream read's value. -/
theorem val_input {st : RecState} (h : RecInv st) {i off len : Nat} (hn : st.nodes[i]? = some (.input off len)) :
    val π iv publicInput stream st i = inputValue (stream.extract off (off + len)) len := by
  have hi : i < st.nodes.size := by
    rcases Nat.lt_or_ge i st.nodes.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hn; cases hn
  have he : st.nodes[i] = .input off len := by
    rw [Array.getElem?_eq_getElem hi] at hn; exact Option.some.inj hn
  have := evalAll_node π iv publicInput stream st h i hi
  rw [he] at this
  unfold val valE
  rw [this]
  rfl

theorem valE_evalAll (st : RecState) (i : Nat) :
    valE (evalAll π iv publicInput stream st) i = val π iv publicInput stream st i := rfl

/-- The elements of nodes, as words. -/
theorem flatMap_nodes {st : RecState} {is : List Nat} {xs : List E} (h : RpL π iv publicInput stream st is xs) :
    (is.map Word.node).flatMap (RecGraph.wordBytes stream (evalAll π iv publicInput stream st)) =
      xs.flatMap elementWord := by
  induction h with
  | nil => rfl
  | cons hx _ ih =>
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, ih, ← hx.2]
    rfl

theorem map_eq_of_forall₂ {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ} {l1 : List α} {l2 : List β}
    (h : List.Forall₂ R l1 l2) (hfg : ∀ a b, R a b → f a = g b) : l1.map f = l2.map g := by
  induction h with
  | nil => rfl
  | cons hab _ ih => rw [List.map_cons, List.map_cons, hfg _ _ hab, ih]

/-- A root read at `off`, on a stream long enough. -/
theorem rootWord_of {st : RecState} (hg : Good st) {a : Sym × Sym} {x : E × E} {off : Nat}
    (hR : RootR π iv publicInput stream st a x off) (hb : InputsBelow st) (hs : stream.size = st.cursor) :
    rootWord x = (stream.extract off (off + 32)).toList := by
  obtain ⟨ha, hb', hna, hnb⟩ := hR
  have hle := hb _ _ (List.mem_iff_getElem?.mpr ⟨_, by rw [Array.getElem?_toList]; exact hnb⟩)
  have := rootWord_extract stream off (by omega)
  rw [← val_input π iv publicInput stream hg.inv hna, ← val_input π iv publicInput stream hg.inv hnb, ha.2,
    hb'.2] at this
  exact this

/-- **The calls' bytes are `pcsCalls`'s**, for a run related by `RedR`, on a stream of the record's length. -/
theorem calls_eq {st : RecState} {red : ReducedS} {r : Reduced} (hg : Good st)
    (hR : RedR π iv publicInput stream st red r) (hb : InputsBelow st) (hs : stream.size = st.cursor) :
    (callsOf st red).map (·.flatMap (RecGraph.wordBytes stream (evalAll π iv publicInput stream st))) =
      pcsCalls reference referenceRoots r := by
  obtain ⟨hr1, hr2, hop, hm⟩ := hR
  have hw1 := rootWord_of π iv publicInput stream hg hr1 hb hs
  have hw2 := rootWord_of π iv publicInput stream hg hr2 hb hs
  have h1na := hr1.2.2.1
  have h2na := hr2.2.2.1
  have hl0 : ((layoutWords reference).getD 0 []).length = 32 := by simp [layoutWords, layoutWord_length]
  have hl1 : ((layoutWords reference).getD 1 []).length = 32 := by simp [layoutWords, layoutWord_length]
  have hl2 : ((layoutWords reference).getD 2 []).length = 32 := by simp [layoutWords, layoutWord_length]
  unfold pcsCalls callsOf
  rw [hm]
  simp only [List.append_nil, List.map_map]
  refine map_eq_of_forall₂ hop ?_
  rintro ⟨c, point, value⟩ y ⟨ptE, vE, rfl, hpt, hv⟩
  simp only at hpt hv
  cases c <;>
  simp only [Function.comp_apply, h1na, h2na, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, RecGraph.wordBytes, openingWords, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    Option.map_none, Option.getD_none, flatMap_nodes π iv publicInput stream hpt, valE_evalAll, hv.2, hw1, hw2,
    beBytes32_one, beBytes32_beNat _ hl0, beBytes32_beNat _ hl1, beBytes32_beNat _ hl2,
    beBytes32_beNat _ (digestBytes_len _), List.append_assoc]

end Calls

end RecGraph.Sim
