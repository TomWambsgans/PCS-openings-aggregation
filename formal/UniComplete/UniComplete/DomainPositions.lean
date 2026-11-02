-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniStatement.Mapping

/-!
# The active rows' positions (milestone 4, the domain facts; iteration 2, F1b)

A height-`r` table with `count ≤ 2^r` active rows (`UniStatement.Domain`): bit `b < r` of a non-full count
owns the coset `[2^r − 2^(b+1), 2^r − 2^b)`; `activePositions count r` lists the cosets of the set bits, the
highest bit first (all of `[0, 2^r)` for a full table), and `isActive i count r` decides membership by the
gap `2^r − i`. `rowPosition count r` (`UniStatement.Mapping`) places Lv42's row `x` in `C1`. Here, all for
`count ≤ 2^r` and with no bound on `r`:

* `mem_activePositions_iff`: `i ∈ activePositions count r ↔ isActive i count r = true` (`i < 2^r`);
* `activePositions_length` (`= count`), `activePositions_nodup`, `lt_of_mem_activePositions` (`< 2^r`);
* `rowPosition_of_lt`: `rowPosition count r x = (activePositions count r)[x]` for `x < count`;
  `rowPosition_bijOn`: a bijection of `[0, 2^r)`; `isActive_rowPosition`:
  `isActive (rowPosition count r x) count r = decide (x < count)`.

The proof reads `rowPosition`'s loop (`Id.run`, a `for` over `[0:r]` with an early `return`) as `walk`, a
plain recursion over the bits `r − 1, …, 0` (`rowPosition_of_ne`), and its images as the list
`rowList count r = activePositions count r ++ padList count r` (`padList`: the cosets of the unset bits,
highest first, then the last row `2^r − 1`; empty for a full table), a permutation of `[0, 2^r)`.
-/

namespace UniComplete.Domain

open UniStatement

/-- `if_pos`, which this Mathlib deprecates. -/
theorem ite_pos_of {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

/-- `if_neg`, which this Mathlib deprecates. -/
theorem ite_neg_of {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : ¬c) : (if c then a else b) = b := by
  simp [h]

/-! ### Arithmetic of the cosets -/

theorem two_pow_succ' (b : ℕ) : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [pow_succ, mul_comm]

/-- The top of bit `b`'s coset. -/
theorem coset_top {r b : ℕ} (hb : b < r) : 2 ^ r - 2 ^ (b + 1) + 2 ^ b = 2 ^ r - 2 ^ b := by
  have h1 : 2 ^ (b + 1) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hb
  have := two_pow_succ' b
  omega

/-- **Bit `b`'s coset, read off the gap** `g = 2^r − i`: `i ∈ [2^r − 2^(b+1), 2^r − 2^b)` exactly when
`g ≥ 2` and `⌊log₂ (g − 1)⌋ = b`. -/
theorem coset_iff_log2 {r b i : ℕ} (hb : b < r) (hi : i < 2 ^ r) :
    (2 ^ r - 2 ^ (b + 1) ≤ i ∧ i < 2 ^ r - 2 ^ b) ↔ (2 ≤ 2 ^ r - i ∧ Nat.log2 (2 ^ r - i - 1) = b) := by
  have h1 : 2 ^ (b + 1) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hb
  have h2 := two_pow_succ' b
  have hp : 0 < 2 ^ b := Nat.two_pow_pos b
  constructor
  · rintro ⟨hlo, hhi⟩
    have hne : 2 ^ r - i - 1 ≠ 0 := by omega
    refine ⟨by omega, (Nat.log2_eq_iff hne).mpr ⟨by omega, by omega⟩⟩
  · rintro ⟨hg, hl⟩
    have hne : 2 ^ r - i - 1 ≠ 0 := by omega
    have := (Nat.log2_eq_iff hne).mp hl
    omega

theorem log2_gap_lt {r i : ℕ} (hi : i < 2 ^ r) (hg : 2 ≤ 2 ^ r - i) : Nat.log2 (2 ^ r - i - 1) < r :=
  (Nat.log2_lt (by omega)).mpr (by omega)

/-- **`isActive` on a non-full table**: row `i < 2^r` is active exactly when it is in the coset of a set
bit `b < r`. -/
theorem isActive_iff_exists {i count r : ℕ} (hi : i < 2 ^ r) (hfull : count ≠ 2 ^ r) :
    isActive i count r = true ↔
      ∃ b < r, count.testBit b = true ∧ 2 ^ r - 2 ^ (b + 1) ≤ i ∧ i < 2 ^ r - 2 ^ b := by
  unfold isActive
  rw [ite_neg_of hfull]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hg, hbit⟩
    exact ⟨_, log2_gap_lt hi hg, hbit, (coset_iff_log2 (log2_gap_lt hi hg) hi).mpr ⟨hg, rfl⟩⟩
  · rintro ⟨b, hb, hbit, hmem⟩
    obtain ⟨hg, hl⟩ := (coset_iff_log2 hb hi).mp hmem
    exact ⟨hg, hl ▸ hbit⟩

/-- Two distinct bits' cosets are disjoint. -/
theorem coset_disjoint {r b b' j : ℕ} (hb : b < r) (hb' : b' < r) (hne : b ≠ b')
    (h : 2 ^ r - 2 ^ (b + 1) ≤ j ∧ j < 2 ^ r - 2 ^ (b + 1) + 2 ^ b)
    (h' : 2 ^ r - 2 ^ (b' + 1) ≤ j ∧ j < 2 ^ r - 2 ^ (b' + 1) + 2 ^ b') : False := by
  wlog hlt : b < b' generalizing b b'
  · exact this hb' hb (Ne.symm hne) h' h (by omega)
  have h1 : 2 ^ (b + 1) ≤ 2 ^ b' := Nat.pow_le_pow_right (by norm_num) hlt
  have h2 : 2 ^ (b' + 1) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hb'
  have e1 := two_pow_succ' b
  have e2 := two_pow_succ' b'
  omega

/-! ### Sums of the bits -/

/-- The sum of the set bits below `r`: `n mod 2^r`. -/
theorem sum_bits_true (n r : ℕ) :
    ((List.range r).map fun b ↦ if n.testBit b = true then 2 ^ b else 0).sum = n % 2 ^ r := by
  induction r with
  | zero => simp [Nat.mod_one]
  | succ r ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, List.map_singleton, List.sum_singleton,
      Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ r) with h | h <;> simp [h]

theorem sum_two_pow (r : ℕ) : ((List.range r).map fun b ↦ 2 ^ b).sum + 1 = 2 ^ r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      pow_succ]
    omega

/-- The sum of the unset bits below `r`: `2^r − 1 − n mod 2^r`. -/
theorem sum_bits_false (n r : ℕ) :
    ((List.range r).map fun b ↦ if n.testBit b = false then 2 ^ b else 0).sum = 2 ^ r - 1 - n % 2 ^ r := by
  have hsum : ((List.range r).map fun b ↦ (if n.testBit b = true then 2 ^ b else 0) +
      (if n.testBit b = false then 2 ^ b else 0)).sum = ((List.range r).map fun b ↦ 2 ^ b).sum := by
    congr 1
    refine List.map_congr_left fun b _ ↦ ?_
    cases n.testBit b <;> simp
  rw [List.sum_map_add, sum_bits_true] at hsum
  have h2 := sum_two_pow r
  have h3 := Nat.mod_lt n (Nat.two_pow_pos r)
  omega

/-! ### The cosets of a list of bits -/

/-- **The cosets of the bits `b ∈ bs` of `count` equal to `v`**, in order (bit `b < r` owns
`[2^r − 2^(b+1), 2^r − 2^b)`): `activePositions` of a non-full table at `v = true`. -/
def cosets (count r : ℕ) (v : Bool) (bs : List ℕ) : List ℕ :=
  bs.flatMap fun b ↦ if count.testBit b = v then List.range' (2 ^ r - 2 ^ (b + 1)) (2 ^ b) else []

theorem cosets_cons (count r : ℕ) (v : Bool) (b : ℕ) (bs : List ℕ) :
    cosets count r v (b :: bs) =
      (if count.testBit b = v then List.range' (2 ^ r - 2 ^ (b + 1)) (2 ^ b) else []) ++
        cosets count r v bs := rfl

theorem mem_coset_ite {c : Prop} [Decidable c] {s n j : ℕ} :
    j ∈ (if c then List.range' s n else []) ↔ c ∧ s ≤ j ∧ j < s + n := by
  split_ifs with h
  · rw [List.mem_range'_1]
    exact ⟨fun h' ↦ ⟨h, h'⟩, fun h' ↦ h'.2⟩
  · simp [h]

theorem mem_cosets {count r : ℕ} {v : Bool} {bs : List ℕ} {j : ℕ} :
    j ∈ cosets count r v bs ↔
      ∃ b ∈ bs, count.testBit b = v ∧ 2 ^ r - 2 ^ (b + 1) ≤ j ∧ j < 2 ^ r - 2 ^ (b + 1) + 2 ^ b := by
  unfold cosets
  rw [List.mem_flatMap]
  exact exists_congr fun b ↦ and_congr_right fun _ ↦ mem_coset_ite

theorem length_cosets (count r : ℕ) (v : Bool) (bs : List ℕ) :
    (cosets count r v bs).length = (bs.map fun b ↦ if count.testBit b = v then 2 ^ b else 0).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [cosets_cons, List.length_append, ih, List.map_cons, List.sum_cons]
    split_ifs <;> simp

theorem lt_of_mem_cosets {count r : ℕ} {v : Bool} {bs : List ℕ} (hbs : ∀ b ∈ bs, b < r) {j : ℕ}
    (hj : j ∈ cosets count r v bs) : j < 2 ^ r - 1 := by
  obtain ⟨b, hb, _, _, hhi⟩ := mem_cosets.mp hj
  rw [coset_top (hbs b hb)] at hhi
  have := Nat.two_pow_pos b
  omega

theorem nodup_cosets {count r : ℕ} {v : Bool} {bs : List ℕ} (hnd : bs.Nodup) (hbs : ∀ b ∈ bs, b < r) :
    (cosets count r v bs).Nodup := by
  unfold cosets
  rw [List.nodup_flatMap]
  refine ⟨fun b _ ↦ ?_, hnd.imp_of_mem fun {a b} ha hb hab ↦ ?_⟩
  · split_ifs
    · exact List.nodup_range'
    · exact List.nodup_nil
  · intro j h1 h2
    obtain ⟨-, h1⟩ := mem_coset_ite.mp h1
    obtain ⟨-, h2⟩ := mem_coset_ite.mp h2
    exact coset_disjoint (hbs a ha) (hbs b hb) hab h1 h2

theorem disjoint_cosets {count r : ℕ} {bs : List ℕ} (hbs : ∀ b ∈ bs, b < r) :
    (cosets count r true bs).Disjoint (cosets count r false bs) := by
  intro j h1 h2
  obtain ⟨b, hb, hv, hm⟩ := mem_cosets.mp h1
  obtain ⟨b', hb', hv', hm'⟩ := mem_cosets.mp h2
  have hne : b ≠ b' := by
    rintro rfl
    rw [hv] at hv'
    exact Bool.noConfusion hv'
  exact coset_disjoint (hbs b hb) (hbs b' hb') hne hm hm'

theorem range_reverse_lt (r : ℕ) : ∀ b ∈ (List.range r).reverse, b < r := by
  intro b hb
  simpa using hb

theorem range_reverse_nodup (r : ℕ) : (List.range r).reverse.Nodup :=
  List.nodup_reverse.mpr List.nodup_range

/-! ### `activePositions` -/

theorem activePositions_of_ne {count r : ℕ} (h : count ≠ 2 ^ r) :
    activePositions count r = cosets count r true (List.range r).reverse := by
  unfold activePositions
  rw [ite_neg_of h]
  rfl

theorem activePositions_full (r : ℕ) : activePositions (2 ^ r) r = List.range (2 ^ r) := by
  unfold activePositions
  rw [ite_pos_of rfl]

/-- **`isActive` is membership in `activePositions`**, for `i < 2^r`. -/
theorem mem_activePositions_iff {i count r : ℕ} (hi : i < 2 ^ r) :
    i ∈ activePositions count r ↔ isActive i count r = true := by
  by_cases hf : count = 2 ^ r
  · subst hf
    rw [activePositions_full, List.mem_range]
    simp [isActive, hi]
  · rw [activePositions_of_ne hf, mem_cosets, isActive_iff_exists hi hf]
    simp only [List.mem_reverse, List.mem_range]
    refine exists_congr fun b ↦ ?_
    constructor
    · rintro ⟨hb, hbit, hlo, hhi⟩
      exact ⟨hb, hbit, hlo, by rw [← coset_top hb]; exact hhi⟩
    · rintro ⟨hb, hbit, hlo, hhi⟩
      exact ⟨hb, hbit, hlo, by rw [coset_top hb]; exact hhi⟩

/-- **The active rows are below `2^r`.** -/
theorem lt_of_mem_activePositions {count r j : ℕ} (hj : j ∈ activePositions count r) : j < 2 ^ r := by
  by_cases hf : count = 2 ^ r
  · subst hf
    rw [activePositions_full, List.mem_range] at hj
    exact hj
  · rw [activePositions_of_ne hf] at hj
    have := lt_of_mem_cosets (range_reverse_lt r) hj
    omega

/-- **There are `count` active rows.** -/
theorem activePositions_length {count r : ℕ} (hc : count ≤ 2 ^ r) :
    (activePositions count r).length = count := by
  by_cases hf : count = 2 ^ r
  · subst hf
    rw [activePositions_full, List.length_range]
  · rw [activePositions_of_ne hf, length_cosets, List.map_reverse, List.sum_reverse, sum_bits_true,
      Nat.mod_eq_of_lt (lt_of_le_of_ne hc hf)]

/-- **The active rows are distinct.** -/
theorem activePositions_nodup (count r : ℕ) : (activePositions count r).Nodup := by
  by_cases hf : count = 2 ^ r
  · subst hf
    rw [activePositions_full]
    exact List.nodup_range
  · rw [activePositions_of_ne hf]
    exact nodup_cosets (range_reverse_nodup r) (range_reverse_lt r)

/-! ### The padding rows, and `rowPosition`'s images -/

/-- **The padding rows** in increasing order: the cosets of the unset bits below `r`, highest first, then the
last row `2^r − 1` (none for a full table). -/
def padList (count r : ℕ) : List ℕ :=
  if count = 2 ^ r then [] else cosets count r false (List.range r).reverse ++ [2 ^ r - 1]

/-- **`rowPosition`'s images, in order**: the active rows, then the padding rows. -/
def rowList (count r : ℕ) : List ℕ := activePositions count r ++ padList count r

theorem padList_length {count r : ℕ} (hc : count ≤ 2 ^ r) : (padList count r).length = 2 ^ r - count := by
  unfold padList
  split_ifs with hf
  · rw [hf, Nat.sub_self]
    rfl
  · rw [List.length_append, length_cosets, List.map_reverse, List.sum_reverse, sum_bits_false,
      Nat.mod_eq_of_lt (lt_of_le_of_ne hc hf), List.length_singleton]
    have := lt_of_le_of_ne hc hf
    omega

theorem lt_of_mem_padList {count r j : ℕ} (hj : j ∈ padList count r) : j < 2 ^ r := by
  unfold padList at hj
  split_ifs at hj with hf
  · simp at hj
  · rcases List.mem_append.mp hj with h | h
    · have := lt_of_mem_cosets (range_reverse_lt r) h
      omega
    · rw [List.mem_singleton] at h
      have := Nat.two_pow_pos r
      omega

theorem padList_nodup (count r : ℕ) : (padList count r).Nodup := by
  unfold padList
  split_ifs with hf
  · exact List.nodup_nil
  · refine (nodup_cosets (range_reverse_nodup r) (range_reverse_lt r)).append (List.nodup_singleton _) ?_
    intro j h1 h2
    rw [List.mem_singleton] at h2
    have := lt_of_mem_cosets (range_reverse_lt r) h1
    omega

theorem disjoint_active_pad (count r : ℕ) : (activePositions count r).Disjoint (padList count r) := by
  intro j h1 h2
  unfold padList at h2
  split_ifs at h2 with hf
  · simp at h2
  · rw [activePositions_of_ne hf] at h1
    rcases List.mem_append.mp h2 with h | h
    · exact disjoint_cosets (range_reverse_lt r) h1 h
    · rw [List.mem_singleton] at h
      have := lt_of_mem_cosets (range_reverse_lt r) h1
      omega

theorem rowList_length {count r : ℕ} (hc : count ≤ 2 ^ r) : (rowList count r).length = 2 ^ r := by
  rw [rowList, List.length_append, activePositions_length hc, padList_length hc]
  omega

theorem rowList_nodup (count r : ℕ) : (rowList count r).Nodup :=
  (activePositions_nodup count r).append (padList_nodup count r) (disjoint_active_pad count r)

theorem lt_of_mem_rowList {count r j : ℕ} (hj : j ∈ rowList count r) : j < 2 ^ r := by
  rcases List.mem_append.mp hj with h | h
  · exact lt_of_mem_activePositions h
  · exact lt_of_mem_padList h

/-- A padding row is not active. -/
theorem isActive_of_mem_padList {count r j : ℕ} (hj : j ∈ padList count r) : isActive j count r = false := by
  rw [← Bool.not_eq_true, ← mem_activePositions_iff (lt_of_mem_padList hj)]
  exact fun h ↦ disjoint_active_pad count r h hj

/-! ### `rowPosition`'s loop -/

/-- **`rowPosition`'s loop as a recursion** over the bits `bs` (`r − 1, …, 0`): at a bit equal to `v`, the
row `y` is in its coset if `y < 2^b`, else `y − 2^b` goes on; the state is the loop's `(answer, y)`. -/
def walk (count r : ℕ) (v : Bool) : List ℕ → ℕ → Option ℕ × ℕ
  | [], y => (none, y)
  | b :: bs, y =>
    if count.testBit b = v then
      if y < 2 ^ b then (some (2 ^ r - 2 ^ (b + 1) + y), y) else walk count r v bs (y - 2 ^ b)
    else walk count r v bs y

/-- `walk` finds the entry `y` of the cosets. -/
theorem walk_fst (count r : ℕ) (v : Bool) (bs : List ℕ) (y : ℕ) :
    (walk count r v bs y).1 = (cosets count r v bs)[y]? := by
  induction bs generalizing y with
  | nil => rfl
  | cons b bs ih =>
    rw [walk, cosets_cons]
    split_ifs with h1 h2
    · rw [List.getElem?_append_left (by rw [List.length_range']; exact h2), List.getElem?_range' h2,
        one_mul]
    · rw [ih, List.getElem?_append_right (by rw [List.length_range']; omega), List.length_range']
    · rw [ih, List.nil_append]

/-- **The `for` loop of `rowPosition` is `walk`** over the reversed indices. -/
theorem forIn_walk (count r : ℕ) (v : Bool) (F : ℕ → Option ℕ × ℕ → Id (ForInStep (Option ℕ × ℕ)))
    (hF : ∀ i s, F i s = if (count.testBit (r - 1 - i) == v) = true then
        (if s.2 < 2 ^ (r - 1 - i) then pure (ForInStep.done (some (2 ^ r - 2 ^ (r - 1 - i + 1) + s.2), s.2))
          else pure (ForInStep.yield (none, s.2 - 2 ^ (r - 1 - i))))
        else pure (ForInStep.yield (none, s.2)))
    (L : List ℕ) (y : ℕ) :
    forIn L ((none : Option ℕ), y) F = (walk count r v (L.map fun i ↦ r - 1 - i) y : Id (Option ℕ × ℕ)) := by
  induction L generalizing y with
  | nil => rfl
  | cons i L ih =>
    rw [List.forIn_cons, hF, List.map_cons, walk]
    simp only [beq_iff_eq]
    split_ifs with h1 h2
    · rfl
    · exact ih _
    · exact ih _

theorem range'_map_reverse (r : ℕ) : (List.range' 0 r).map (fun i ↦ r - 1 - i) = (List.range r).reverse := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_range', List.getElem_reverse, List.getElem_range,
      List.length_range]
    omega

/-- **`rowPosition` of a non-full table**, by its loop: the entry `y` of the cosets of the bits equal to
`x < count` (`y = x` for an active row, `x − count` for a padding row), else the last row. -/
theorem rowPosition_of_ne {count r : ℕ} (hf : count ≠ 2 ^ r) (x : ℕ) :
    rowPosition count r x =
      ((cosets count r (decide (x < count)) (List.range r).reverse)[if x < count then x else x - count]?).getD
        (2 ^ r - 1) := by
  unfold rowPosition
  simp only [Id.run, ite_neg_of hf]
  rw [Std.Legacy.Range.forIn_eq_forIn_range', forIn_walk count r (decide (x < count)) _ (fun _ _ ↦ rfl)]
  have hsize : (Std.Legacy.Range.mk 0 r 1 (by omega)).size = r := by
    simp [Std.Legacy.Range.size]
  have hL := range'_map_reverse r
  have hw := walk_fst count r (decide (x < count)) (List.range r).reverse
    (if decide (x < count) = true then x else x - count)
  simp only [decide_eq_true_eq] at hw ⊢
  rw [hsize, hL, ← hw]
  rcases walk count r (decide (x < count)) (List.range r).reverse (if x < count then x else x - count) with
    ⟨_ | v, y'⟩ <;> rfl

theorem rowPosition_full (r x : ℕ) : rowPosition (2 ^ r) r x = x := by
  unfold rowPosition
  simp only [Id.run]
  rfl

/-! ### `rowPosition` is the list `rowList` -/

theorem getD_eq_of_getElem? {L : List ℕ} {x : ℕ} {o : Option ℕ} (h : L[x]? = o) (d : ℕ)
    (hx : x < L.length) : o.getD d = L.getD x 0 := by
  rw [← h, List.getElem?_eq_getElem hx, Option.getD_some, List.getD_eq_getElem _ _ hx]

/-- **`rowPosition` reads `rowList`**: `rowPosition count r x` is its entry `x`, `x < 2^r`. -/
theorem rowPosition_eq_rowList {count r x : ℕ} (hc : count ≤ 2 ^ r) (hx : x < 2 ^ r) :
    rowPosition count r x = (rowList count r).getD x 0 := by
  by_cases hf : count = 2 ^ r
  · subst hf
    rw [rowPosition_full, rowList, padList, ite_pos_of rfl, List.append_nil, activePositions_full,
      List.getD_eq_getElem _ _ (by rw [List.length_range]; exact hx), List.getElem_range]
  · have hlt : count < 2 ^ r := lt_of_le_of_ne hc hf
    have hla := activePositions_length hc
    rw [rowPosition_of_ne hf]
    by_cases hxc : x < count
    · rw [ite_pos_of hxc, decide_eq_true hxc]
      refine getD_eq_of_getElem? ?_ _ (by rw [rowList_length hc]; exact hx)
      rw [rowList, List.getElem?_append_left (by rw [hla]; exact hxc), activePositions_of_ne hf]
    · rw [ite_neg_of hxc, decide_eq_false hxc, rowList, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by rw [hla]; omega), hla, padList, ite_neg_of hf]
      have hlen := padList_length hc
      rw [padList, ite_neg_of hf, List.length_append, List.length_singleton] at hlen
      by_cases hy : x - count < (cosets count r false (List.range r).reverse).length
      · rw [List.getElem?_append_left hy, List.getElem?_eq_getElem hy, Option.getD_some, Option.getD_some]
      · have hy' : x - count = (cosets count r false (List.range r).reverse).length := by omega
        rw [List.getElem?_eq_none (by omega), List.getElem?_append_right (by omega), hy', Nat.sub_self]
        rfl

/-- **An active row's position**: `rowPosition count r x` is the entry `x` of `activePositions`, `x < count`. -/
theorem rowPosition_of_lt {count r x : ℕ} (hc : count ≤ 2 ^ r) (hx : x < count) :
    rowPosition count r x = (activePositions count r)[x]'(by rw [activePositions_length hc]; exact hx) := by
  have hla := activePositions_length hc
  rw [rowPosition_eq_rowList hc (lt_of_lt_of_le hx hc), rowList,
    List.getD_eq_getElem _ _ (by rw [List.length_append]; omega), List.getElem_append_left]

/-- **`rowPosition` maps `[0, 2^r)` into itself.** -/
theorem rowPosition_lt {count r x : ℕ} (hc : count ≤ 2 ^ r) (hx : x < 2 ^ r) : rowPosition count r x < 2 ^ r := by
  rw [rowPosition_eq_rowList hc hx, List.getD_eq_getElem _ _ (by rw [rowList_length hc]; exact hx)]
  exact lt_of_mem_rowList (List.getElem_mem _)

/-- **`rowPosition` is injective on `[0, 2^r)`.** -/
theorem rowPosition_injOn {count r : ℕ} (hc : count ≤ 2 ^ r) :
    Set.InjOn (rowPosition count r) (Set.Iio (2 ^ r)) := by
  intro x hx y hy h
  rw [Set.mem_Iio] at hx hy
  have hl := rowList_length hc
  rw [rowPosition_eq_rowList hc hx, rowPosition_eq_rowList hc hy, List.getD_eq_getElem _ _ (by omega),
    List.getD_eq_getElem _ _ (by omega)] at h
  exact (rowList_nodup count r).getElem_inj_iff.mp h

/-- **`rowPosition` is a bijection of `[0, 2^r)`** (`count ≤ 2^r`). -/
theorem rowPosition_bijOn {count r : ℕ} (hc : count ≤ 2 ^ r) :
    Set.BijOn (rowPosition count r) (Set.Iio (2 ^ r)) (Set.Iio (2 ^ r)) := by
  refine ⟨fun x hx ↦ rowPosition_lt hc hx, rowPosition_injOn hc, fun j hj ↦ ?_⟩
  rw [Set.mem_Iio] at hj
  have hl := rowList_length hc
  have hsub : (rowList count r).toFinset ⊆ Finset.range (2 ^ r) := fun a ha ↦
    Finset.mem_range.mpr (lt_of_mem_rowList (List.mem_toFinset.mp ha))
  have heq := Finset.eq_of_subset_of_card_le hsub
    (by rw [Finset.card_range, List.toFinset_card_of_nodup (rowList_nodup count r), hl])
  have hmem : j ∈ rowList count r := List.mem_toFinset.mp (heq ▸ Finset.mem_range.mpr hj)
  obtain ⟨x, hx, hxj⟩ := List.mem_iff_getElem.mp hmem
  refine ⟨x, Set.mem_Iio.mpr (by omega), ?_⟩
  rw [rowPosition_eq_rowList hc (by omega), List.getD_eq_getElem _ _ hx, hxj]

/-- **Lv42's row `x` lands on an active row exactly when it is an executed row** (`x < count`). -/
theorem isActive_rowPosition {count r x : ℕ} (hc : count ≤ 2 ^ r) (hx : x < 2 ^ r) :
    isActive (rowPosition count r x) count r = decide (x < count) := by
  have hla := activePositions_length hc
  have hlt := rowPosition_lt hc hx
  by_cases hxc : x < count
  · rw [decide_eq_true hxc, ← mem_activePositions_iff hlt, rowPosition_of_lt hc hxc]
    exact List.getElem_mem _
  · rw [decide_eq_false hxc]
    apply isActive_of_mem_padList
    have hlen : x < (activePositions count r ++ padList count r).length := by
      rw [List.length_append, padList_length hc]
      omega
    rw [rowPosition_eq_rowList hc hx, rowList, List.getD_eq_getElem _ _ hlen,
      List.getElem_append_right (by omega)]
    exact List.getElem_mem _

end UniComplete.Domain

/-- info: 'UniComplete.Domain.mem_activePositions_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.mem_activePositions_iff

/-- info: 'UniComplete.Domain.activePositions_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.activePositions_length

/-- info: 'UniComplete.Domain.activePositions_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.activePositions_nodup

/-- info: 'UniComplete.Domain.lt_of_mem_activePositions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.lt_of_mem_activePositions

/-- info: 'UniComplete.Domain.rowPosition_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.rowPosition_of_lt

/-- info: 'UniComplete.Domain.rowPosition_bijOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.rowPosition_bijOn

/-- info: 'UniComplete.Domain.isActive_rowPosition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.isActive_rowPosition
