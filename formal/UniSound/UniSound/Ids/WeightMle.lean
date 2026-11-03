-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The weights are `formal/UniStatement`'s
-- `weightAt` (`Stacks.lean`), the claims `combine`'s (`Claims.lean`).
import UniSound.Ids.Eval
import UniSound.Ids.Facts

/-!
# The batch's weights are multilinear off `Z_bad`'s roots

**`combAt_mle`**: where `Z_bad(t) ≠ 0` (no merge, `NoMerge`) and Flock's point has `q_flock`'s
`8 + h_B` coordinates (`FlockGood`), each commitment's combined claim's weight at the batch's point
`r` is the fold of its values on the cube (`weightAt` is the multilinear extension of its cube
values): the hypothesis `WeightMle` of `UniFinal`'s construction, at every run of the identity model.

* **Multilinear functions** (`Mle V F`: `F` is fixed by `foldAll` on `V` coordinates) are closed
  under sums and scalar multiples; a product of affine factors, one per coordinate, is multilinear
  (`foldAll_prod`, by induction on the point through `foldT`).
* **One block** of a term (`rowEq row len · selector v off`, `mle_block`): a product of affine
  factors when the row reads no coordinate the selector does (`len ≤ v`).
* **A term** (`weightAt_single`, `wSum`): an ordinary column reads its own `v` coordinates
  (`mle_plain`); `q_flock`'s slot at `y(t)` reads `8 + h_B`, its block's (`mle_slot`); the ring-switch
  term is the tower weight `Σ_k d_k Π_n (1 + r_n + p_n^(2^k))` (`towerWeight`) on Flock's point,
  each summand a block (`mle_tower`, `mle_ring`).
* **The terms of the run** (`term_kinds`): every term of the verifier's relations at `t` is untwisted
  and either not a slot or on `C1` at `y(t)`, or it is the ring-switch term on `q_flock` at Flock's
  point; off `Z_bad`'s roots `y(t)` is not merged (`y_self`, `mergedSelf`), and a merged point extends
  its term's (`mergedPrefix`).
* **The combined claim** (`combAt_isMle`): `weightAt` is linear in its terms (`weightAtLinear`) and
  `combine` is the `ρ`-combination of the relations' terms at their merged points (`combineEq`).
-/

namespace UniSound.Ids.Multilin

open LeanVM.Parameters UniStatement Finset Weights

/-! ## Multilinear functions of the batch's point -/

/-- **A multilinear function of the batch's point** on `V` coordinates: its fold (the multilinear
extension of its values on the cube) at every point of `V` coordinates is its value there. -/
def Mle (V : ℕ) (F : List E → E) : Prop :=
  ∀ r : List E, r.length = V → foldAll (fun u ↦ F (bitsE u V)) r 0 = F r

theorem foldAll_congr0 (f g : ℕ → E) (r : List E) (h : ∀ u < 2 ^ r.length, f u = g u) :
    foldAll f r 0 = foldAll g r 0 := by
  rw [foldAll_eq_sum, foldAll_eq_sum]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  simp only [zero_mul, zero_add, h u (Finset.mem_range.mp hu)]

theorem foldAll_add' (f g : ℕ → E) (r : List E) :
    foldAll (fun u ↦ f u + g u) r 0 = foldAll f r 0 + foldAll g r 0 := by
  simp only [foldAll_eq_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun u _ ↦ by ring

theorem foldAll_mul_left (c : E) (f : ℕ → E) (r : List E) :
    foldAll (fun u ↦ c * f u) r 0 = c * foldAll f r 0 := by
  simp only [foldAll_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun u _ ↦ by ring

theorem foldAll_zero' (r : List E) : foldAll (fun _ ↦ (0 : E)) r 0 = 0 := by
  simp [foldAll_eq_sum]

theorem Mle.congr {V : ℕ} {F G : List E → E} (hF : Mle V F) (h : ∀ p, p.length = V → F p = G p) :
    Mle V G := by
  intro r hr
  rw [← h r hr, ← hF r hr]
  exact foldAll_congr0 _ _ r fun u _ ↦ (h _ (bitsE_length u V)).symm

theorem Mle.zero (V : ℕ) : Mle V (fun _ ↦ 0) := fun r _ ↦ foldAll_zero' r

theorem Mle.add {V : ℕ} {F G : List E → E} (hF : Mle V F) (hG : Mle V G) :
    Mle V (fun p ↦ F p + G p) := by
  intro r hr
  show foldAll (fun u ↦ F (bitsE u V) + G (bitsE u V)) r 0 = F r + G r
  rw [foldAll_add' (fun u ↦ F (bitsE u V)) (fun u ↦ G (bitsE u V)), hF r hr, hG r hr]

theorem Mle.const_mul {V : ℕ} {F : List E → E} (c : E) (hF : Mle V F) : Mle V (fun p ↦ c * F p) := by
  intro r hr
  show foldAll (fun u ↦ c * F (bitsE u V)) r 0 = c * F r
  rw [foldAll_mul_left c (fun u ↦ F (bitsE u V)), hF r hr]

theorem Mle.listSum {α : Type} {V : ℕ} (l : List α) (G : α → List E → E) (h : ∀ a ∈ l, Mle V (G a)) :
    Mle V (fun p ↦ (l.map fun a ↦ G a p).sum) := by
  induction l with
  | nil => exact Mle.congr (Mle.zero V) fun p _ ↦ by simp
  | cons a l ih =>
    exact Mle.congr ((h a (List.mem_cons_self ..)).add (ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb)))
      fun p _ ↦ by simp

theorem Mle.finSum {V : ℕ} (n : ℕ) (G : ℕ → List E → E) (h : ∀ k < n, Mle V (G k)) :
    Mle V (fun p ↦ ∑ k ∈ range n, G k p) := by
  induction n with
  | zero => exact Mle.congr (Mle.zero V) fun p _ ↦ by simp
  | succ n ih =>
    exact Mle.congr ((ih fun k hk ↦ h k (by omega)).add (h n (by omega)))
      fun p _ ↦ by rw [Finset.sum_range_succ]

/-! ## Products of affine factors -/

/-- A number's bit `k`, in `E`. -/
def bitN (u k : ℕ) : E := if u.testBit k then 1 else 0

theorem bitN_zero (k : ℕ) : bitN 0 k = 0 := by simp [bitN]

theorem bitN_two_mul (i k : ℕ) : bitN (2 * i) (k + 1) = bitN i k := by
  have h := testBit_two_mul_add i 0 k (by norm_num)
  rw [add_zero] at h
  simp only [bitN, h]

theorem bitN_two_mul_one (i k : ℕ) : bitN (2 * i + 1) (k + 1) = bitN i k := by
  simp only [bitN, testBit_two_mul_add i 1 k (by norm_num)]

theorem bitN_two_mul_zero (i : ℕ) : bitN (2 * i) 0 = 0 := by
  have h := testBit_two_mul_add_zero i 0 (by norm_num)
  rw [add_zero] at h
  simp [bitN, h]

theorem bitN_two_mul_one_zero (i : ℕ) : bitN (2 * i + 1) 0 = 1 := by
  simp [bitN, testBit_two_mul_add_zero i 1 (by norm_num)]

/-- **A product of affine factors is fixed by the fold**: one factor per coordinate, each affine
(`φ_k(y) = φ_k(0) + y (φ_k(0) + φ_k(1))`, characteristic two). -/
theorem foldAll_prod : ∀ (r : List E) (N : ℕ) (φ : ℕ → E → E) (c : E),
    (∀ k y, φ k y = φ k 0 + y * (φ k 0 + φ k 1)) →
      foldAll (fun u ↦ c * ∏ k ∈ range N, φ k (bitN u k)) r 0 = c * ∏ k ∈ range N, φ k (r.getD k 0)
  | [], N, φ, c, _ => by
    simp only [foldAll, List.foldl_nil, bitN_zero, List.getD_nil]
  | x :: r, 0, φ, c, hφ => by
    have h := foldAll_prod r 0 φ c hφ
    simp only [Finset.range_zero, Finset.prod_empty, mul_one] at h ⊢
    simp only [foldAll, List.foldl_cons] at h ⊢
    have hT : foldT (fun _ ↦ c) x = fun _ ↦ c := by
      funext i
      simp only [foldT, CharTwo.add_self_eq_zero, mul_zero, add_zero]
    rw [hT]
    exact h
  | x :: r, n + 1, φ, c, hφ => by
    have hT : foldT (fun u ↦ c * ∏ k ∈ range (n + 1), φ k (bitN u k)) x =
        fun i ↦ (c * φ 0 x) * ∏ k ∈ range n, φ (k + 1) (bitN i k) := by
      funext i
      simp only [foldT, Finset.prod_range_succ', bitN_two_mul, bitN_two_mul_one, bitN_two_mul_zero,
        bitN_two_mul_one_zero]
      rw [hφ 0 x]
      ring
    have h := foldAll_prod r n (fun k ↦ φ (k + 1)) (c * φ 0 x) (fun k y ↦ hφ (k + 1) y)
    simp only [foldAll, List.foldl_cons] at h ⊢
    rw [hT, h]
    simp only [Finset.prod_range_succ', List.getD_cons_succ, List.getD_cons_zero]
    ring

theorem bitsE_getD_lt (u V k : ℕ) (hu : u < 2 ^ V) : (bitsE u V).getD k 0 = bitN u k := by
  rw [bitsE_getD, bitN]
  by_cases hk : k < V
  · simp [hk]
  · have : u.testBit k = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hk, this]

theorem aff_lin (A B : ℕ → E) (k : ℕ) (y : E) :
    A k + B k * y = (A k + B k * 0) + y * ((A k + B k * 0) + (A k + B k * 1)) := by
  linear_combination (-(y * A k)) * (CharTwo.two_eq_zero : (2 : E) = 0)

/-- **A product of affine factors is multilinear.** -/
theorem mle_lin (V N : ℕ) (A B : ℕ → E) (c : E) :
    Mle V (fun p ↦ c * ∏ k ∈ range N, (A k + B k * p.getD k 0)) := by
  intro r hr
  have h := foldAll_prod r N (fun k y ↦ A k + B k * y) c (aff_lin A B)
  refine Eq.trans (foldAll_congr0 _ (fun u ↦ c * ∏ k ∈ range N, (A k + B k * bitN u k)) r
    fun u hu ↦ ?_) h
  rw [hr] at hu
  simp only [bitsE_getD_lt u V _ hu]

/-! ## One block -/

/-- A block's factor's constant: the row's below `len`, the selector's between `v` and `V`. -/
def blkA (row : List E) (len v V off k : ℕ) : E :=
  if k < len then 1 + row.getD k 0 else if v ≤ k ∧ k < V then (if off.testBit k then 0 else 1) else 1

/-- A block's factor's slope. -/
def blkB (len v V k : ℕ) : E := if k < len then 1 else if v ≤ k ∧ k < V then 1 else 0

theorem blk_factor (row : List E) (len v V off k : ℕ) (hlv : len ≤ v) (y : E) :
    blkA row len v V off k + blkB len v V k * y =
      (if k < len then 1 + row.getD k 0 + y else 1) *
        (if v ≤ k ∧ k < V then (if off.testBit k then y else 1 + y) else 1) := by
  unfold blkA blkB
  split_ifs <;> first | (exfalso; omega) | ring1

theorem prod_ite_range (N M : ℕ) (f : ℕ → E) (P : ℕ → Prop) [DecidablePred P] (hMN : M ≤ N)
    (hP : ∀ k, P k → k < M) :
    ∏ k ∈ range N, (if P k then f k else 1) = ∏ k ∈ range M, (if P k then f k else 1) := by
  refine (Finset.prod_subset (fun k hk ↦ Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp hk) hMN)) fun k _ hk ↦ ?_).symm
  rw [ite_eq_right fun h ↦ hk (Finset.mem_range.mpr (hP k h))]

/-- **A block's row times its selector** is a product of affine factors when they read disjoint
coordinates (`len ≤ v`). -/
theorem block_prod (row : List E) (len v V off : ℕ) (hlv : len ≤ v) (p : List E) (hp : p.length = V) :
    1 * ∏ k ∈ range (len + V), (blkA row len v V off k + blkB len v V k * p.getD k 0) =
      rowEq row len p * selector p v off := by
  rw [one_mul, Finset.prod_congr rfl fun k _ ↦ blk_factor row len v V off k hlv (p.getD k 0),
    Finset.prod_mul_distrib]
  congr 1
  · rw [prod_ite_range (len + V) len (fun k ↦ 1 + row.getD k 0 + p.getD k 0) (fun k ↦ k < len)
      (by omega) fun k h ↦ h, rowEq_eq, list_prod_range]
    exact Finset.prod_congr rfl fun k hk ↦ ite_eq_left (Finset.mem_range.mp hk)
  · rw [prod_ite_range (len + V) V
      (fun k ↦ if off.testBit k then p.getD k 0 else 1 + p.getD k 0) (fun k ↦ v ≤ k ∧ k < V)
      (by omega) fun k h ↦ h.2, ← Finset.prod_filter]
    have hset : (range V).filter (fun k ↦ v ≤ k ∧ k < V) = Finset.Ico v V := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hset, Finset.prod_Ico_eq_prod_range]
    unfold selector
    rw [hp, foldl_mul_map, one_mul, List.range'_eq_map_range, List.map_map, list_prod_range]
    try rfl

/-- **One block of a term is multilinear** where the row reads below the selector. -/
theorem mle_block (V len v off : ℕ) (row : List E) (hlv : len ≤ v) :
    Mle V (fun p ↦ rowEq row len p * selector p v off) :=
  Mle.congr (mle_lin V (len + V) (blkA row len v V off) (blkB len v V) 1)
    fun p hp ↦ block_prod row len v V off hlv p hp

/-! ## One term -/

/-- **An ordinary column's term** (untwisted, not a slot) is multilinear at every point. -/
theorem mle_plain (L : StackLayout) (rm : Option (List E)) (V : ℕ) (mp : List E) (col : Column)
    (hcol : ∀ j, col ≠ .qflockSlot j) :
    Mle V (fun p ↦ wSum L p rm mp (twistPt mp 0) col 0) := by
  refine Mle.congr (Mle.listSum (L.limbs col)
    (fun b p ↦ limbScale b.1 * (rowEq mp b.2.1 p * selector p b.2.1 b.2.2))
    fun b _ ↦ (mle_block V b.2.1 b.2.1 b.2.2 mp le_rfl).const_mul _) fun p _ ↦ ?_
  rw [wSum, ite_eq_right zero_ne_ringTwist, slotView_of_ne hcol]
  rfl

/-- **`q_flock`'s slot `j` at `y`** is multilinear where its `8 + |y|` row coordinates are within its
block's variables. -/
theorem mle_slot (L : StackLayout) (rm : Option (List E)) (V j : ℕ) (y : List E)
    (hv : ∀ b ∈ L.limbs .qflock, 8 + y.length ≤ b.2.1) :
    Mle V (fun p ↦ wSum L p rm y (twistPt y 0) (.qflockSlot j) 0) := by
  have hlen : ((List.range 8).map (bitE j) ++ y).length = 8 + y.length := by simp
  have hpos : 0 < 8 + y.length := by omega
  refine Mle.congr (Mle.listSum (L.limbs .qflock) (fun b p ↦ limbScale b.1 *
    (rowEq ((List.range 8).map (bitE j) ++ y) (8 + y.length) p * selector p b.2.1 b.2.2))
    fun b hb ↦ (mle_block V _ b.2.1 b.2.2 _ (hv b hb)).const_mul _) fun p _ ↦ ?_
  have h0 : twistPt y 0 = y := rfl
  rw [wSum, ite_eq_right zero_ne_ringTwist, h0]
  refine congrArg List.sum (List.map_congr_left fun b _ ↦ ?_)
  simp only [slotView, hlen, gt_iff_lt, hpos, ↓reduceIte]

/-- **The ring-switch row at Flock's point**: the tower weight is a sum of blocks
(`towerWeight`). -/
theorem mle_tower (V v off : ℕ) (map mp fp : List E) (hext : mp.take fp.length = fp)
    (hv : v = fp.length) (hvV : v ≤ V) :
    Mle V (fun p ↦ ringRow (some map) mp p v * selector p v off) := by
  refine Mle.congr (Mle.finSum 64 (fun k p ↦ (Flock.towerCoefficients map).getD k 0 *
    (rowEq (fp.map fun x ↦ sqn x k) v p * selector p v off))
    fun k _ ↦ (mle_block V v v off _ le_rfl).const_mul _) fun p hp ↦ ?_
  show ∑ k ∈ range 64, (Flock.towerCoefficients map).getD k 0 *
      (rowEq (fp.map fun x ↦ sqn x k) v p * selector p v off) = ringRow (some map) mp p v * selector p v off
  have hpl : (p.take v).length = fp.length := by rw [List.length_take]; omega
  have htake : mp.take v = fp := by rw [hv]; exact hext
  have htw := towerWeight fp (p.take v) map hpl.symm
  simp only [ringRow]
  rw [htake, ← List.map_take, htw, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [mul_assoc]
  congr 2
  rw [rowEq_eq, list_prod_range, ← hv]
  refine Finset.prod_congr rfl fun n hn ↦ ?_
  have hn' : n < v := Finset.mem_range.mp hn
  have hm : (fp.map fun x ↦ sqn x k).getD n 0 = sqn (fp.getD n 0) k := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show n < fp.length by omega)]
  rw [hm, Eval.take_getD p hn']
  ring

/-- **The ring-switch term** on `q_flock` (one limb of Flock's point's coordinates) is
multilinear. -/
theorem mle_ring (L : StackLayout) (V : ℕ) (map mp fp : List E) (hext : mp.take fp.length = fp)
    (hv : ∀ b ∈ L.limbs .qflock, b.2.1 = fp.length ∧ b.2.1 ≤ V) :
    Mle V (fun p ↦ wSum L p (some map) mp (twistPt mp ringTwist) .qflock ringTwist) := by
  refine Mle.congr (Mle.listSum (L.limbs .qflock) (fun b p ↦ limbScale b.1 *
    (ringRow (some map) mp p b.2.1 * selector p b.2.1 b.2.2))
    fun b hb ↦ (mle_tower V b.2.1 b.2.2 map mp fp hext (hv b hb).1 (hv b hb).2).const_mul _)
    fun p _ ↦ ?_
  rw [wSum, ite_eq_left rfl]
  try rfl

/-- **The ring-switch term without a map** is zero. -/
theorem mle_ring_none (L : StackLayout) (V : ℕ) (mp mp' : List E) :
    Mle V (fun p ↦ wSum L p none mp mp' .qflock ringTwist) := by
  refine Mle.congr (Mle.zero V) fun p _ ↦ ?_
  rw [wSum, ite_eq_left rfl]
  refine (List.sum_eq_zero fun x hx ↦ ?_).symm
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
  simp [ringRow]

/-! ## The terms of the run -/

/-- **A constraint term**: untwisted, and not a slot or at `y`. -/
def SlotAt (y : List E) (tm : Term) : Prop :=
  tm.twist = 0 ∧ ((∀ j, tm.column ≠ .qflockSlot j) ∨ tm.point = y)

theorem copyFold_Q (o r : ℕ) (columns : List String) (w y : List E) (lift gamma : E) :
    ∀ (l : List ℕ) (s : Array Term × E),
      ∀ tm ∈ (l.foldl (Eval.copyStep o r columns w y lift gamma) s).1.toList,
        tm ∈ s.1.toList ∨ SlotAt y tm
  | [], _, _, h => Or.inl h
  | c :: l, s, tm, h => by
    rw [List.foldl_cons] at h
    rcases copyFold_Q o r columns w y lift gamma l _ tm h with h1 | h1
    · unfold Eval.copyStep at h1
      split at h1
      · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at h1
        rcases h1 with (h1 | rfl) | rfl
        · exact Or.inl h1
        · exact Or.inr ⟨rfl, Or.inl fun j h ↦ by simp [term] at h⟩
        · exact Or.inr ⟨rfl, Or.inr rfl⟩
      · exact Or.inl h1
    · exact Or.inr h1

theorem crStep_Q (S : Shape) (gamma t : E) (w : List E) (s : E × Array Term × E × ℕ)
    (x : Table × TablePart) :
    ∀ tm ∈ (Eval.crStep S gamma t w s x).2.1.toList, tm ∈ s.2.1.toList ∨
      SlotAt (coordinatesAt t (coordinateFunctionals (S.heights.getD opBlake2s 0))) tm := by
  intro tm htm
  unfold Eval.crStep at htm
  dsimp only at htm
  by_cases hj : x.1.opcode = opJump
  · have hb : ¬ x.1.opcode = opBlake2s := by rw [hj]; decide
    simp only [ite_eq_left hj, ite_eq_right hb, Array.toList_push, List.mem_append,
      List.mem_singleton] at htm
    rcases htm with (h | rfl) | rfl
    · exact Or.inl h
    · exact Or.inr ⟨rfl, Or.inl fun j h ↦ by simp [term] at h⟩
    · exact Or.inr ⟨rfl, Or.inl fun j h ↦ by simp [term] at h⟩
  · by_cases hb : x.1.opcode = opBlake2s
    · simp only [ite_eq_right hj, ite_eq_left hb] at htm
      rcases copyFold_Q _ _ _ _ _ _ _ _ _ tm htm with h | h
      · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at h
        rcases h with h | rfl
        · exact Or.inl h
        · exact Or.inr ⟨rfl, Or.inl fun j h ↦ by simp [term] at h⟩
      · rw [hb] at h
        exact Or.inr h
    · simp only [ite_eq_right hj, ite_eq_right hb, Array.toList_push, List.mem_append,
        List.mem_singleton] at htm
      rcases htm with h | rfl
      · exact Or.inl h
      · exact Or.inr ⟨rfl, Or.inl fun j h ↦ by simp [term] at h⟩

theorem crFold_Q (S : Shape) (gamma t : E) (w : List E) : ∀ (L : List (Table × TablePart))
    (s : E × Array Term × E × ℕ), ∀ tm ∈ (L.foldl (Eval.crStep S gamma t w) s).2.1.toList,
      tm ∈ s.2.1.toList ∨
        SlotAt (coordinatesAt t (coordinateFunctionals (S.heights.getD opBlake2s 0))) tm
  | [], _, _, h => Or.inl h
  | x :: L, s, tm, h => by
    rw [List.foldl_cons] at h
    rcases crFold_Q S gamma t w L _ tm h with h1 | h1
    · exact crStep_Q S gamma t w s x tm h1
    · exact Or.inr h1

theorem lineFold_Q (S : Shape) (gamma t : E) (w y : List E) : ∀ (l : List ((E × E) × ℕ))
    (s : E × Array Term × E), ∀ tm ∈ (l.foldl (Eval.lineStep S gamma t w) s).2.1.toList,
      tm ∈ s.2.1.toList ∨ SlotAt y tm
  | [], _, _, h => Or.inl h
  | x :: l, s, tm, h => by
    rw [List.foldl_cons] at h
    rcases lineFold_Q S gamma t w y l _ tm h with h1 | h1
    · simp only [Eval.lineStep, Array.toList_push, List.mem_append, List.mem_singleton] at h1
      rcases h1 with h1 | rfl
      · exact Or.inl h1
      · exact Or.inr ⟨rfl, Or.inl fun j h ↦ by simp [term] at h⟩
    · exact Or.inr h1

/-- **The constraint relation's terms**: untwisted, and not a slot or at `y(t)` (the copies'
slots). -/
theorem crOf_Q (S : Shape) (parts : List TablePart) (pw : List E) (gamma t cv : E) (w : List E) :
    ∀ tm ∈ (Eval.crOf S parts pw gamma t cv w).1.terms,
      SlotAt (coordinatesAt t (coordinateFunctionals (S.heights.getD opBlake2s 0))) tm := by
  intro tm htm
  unfold Eval.crOf at htm
  dsimp only at htm
  rcases lineFold_Q S gamma t w (coordinatesAt t (coordinateFunctionals (S.heights.getD opBlake2s 0)))
    _ _ tm htm with h | h
  · rcases crFold_Q S gamma t w _ _ tm h with h' | h'
    · simp at h'
    · exact h'
  · exact h

/-- **Every term of the verifier's relations at `t`**: untwisted and not a slot or on `C1` at
`y(t)`; or the ring-switch term, on `q_flock` at Flock's point. -/
theorem term_kinds (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (s : USt) (ch : List E) (fd : Done)
    (t : E) (vals : List E) :
    ∀ r ∈ relsAt D Fl s ch fd t vals, ∀ tm ∈ r.terms,
      (tm.twist = 0 ∧ ((∀ j, tm.column ≠ .qflockSlot j) ∨ (r.commitment = .c1 ∧ tm.point = Eval.yOf D t))) ∨
        (tm.twist = ringTwist ∧ tm.column = .qflock ∧ tm.point = (Fl.prog.out fd []).1 ∧
          r.commitment = .c1) := by
  intro r hr tm htm
  unfold relsAt relsOf at hr
  simp only [List.mem_append, List.mem_singleton] at hr
  rcases hr with ((((hr | hr) | hr) | rfl) | hr) | hr
  · obtain ⟨tab, -, v', hv⟩ := Eval.tablesPart_rels _ _ _ _ _ _ r hr
    obtain ⟨⟨c, hc⟩, -, htw⟩ := Eval.tablePartOf_terms tab _ _ _ _ v' r hv tm htm
    exact Or.inl ⟨htw, Or.inl fun j h ↦ by rw [hc] at h; simp at h⟩
  · simp only [RelInput.memRels, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp only [Relation.equal, term, List.mem_singleton] at htm
      subst htm
      exact Or.inl ⟨rfl, Or.inl fun j h ↦ by simp at h⟩
    · simp only [Relation.equal, term, List.mem_singleton] at htm
      subst htm
      exact Or.inl ⟨rfl, Or.inl fun j h ↦ by simp at h⟩
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp htm
      exact Or.inl ⟨rfl, Or.inl fun j h ↦ by simp [term] at h⟩
  · simp only [RelInput.bcRels, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [Relation.equal, term, List.mem_singleton] at htm
      subst htm
      exact Or.inl ⟨rfl, Or.inl fun j h ↦ by simp at h⟩
    · simp only [Relation.equal, term, List.mem_singleton] at htm
      subst htm
      exact Or.inl ⟨rfl, Or.inl fun j h ↦ by simp at h⟩
  · have hQ := crOf_Q _ _ _ _ _ _ _ tm (by rw [← Eval.constraintRelation_eq]; exact htm)
    have hc1 := Eval.commitment_c1 (r := (relInput D s ch (Fl.prog.out fd []) t vals).constraint.1)
      fun tm' htm' ↦
      (Eval.crOf_terms _ _ _ _ _ _ _ tm' (by rw [← Eval.constraintRelation_eq]; exact htm')).2.1
    obtain ⟨htw, hq⟩ := hQ
    exact Or.inl ⟨htw, hq.imp id fun h ↦ ⟨hc1, h⟩⟩
  · obtain ⟨hc2, htw⟩ := Eval.heap_terms _ _ _ _ _ _ _ _ _ _ _ _ _ r hr tm htm
    exact Or.inl ⟨htw, Or.inl fun j h ↦ by simp [h, Column.commitment] at hc2⟩
  · unfold RelInput.ringRels at hr
    split at hr
    · simp only [List.mem_singleton] at hr
      subst hr
      simp only [List.mem_singleton] at htm
      subst htm
      exact Or.inr ⟨rfl, rfl, rfl, rfl⟩
    · simp at hr

/-! ## The combined claims -/

theorem fst_mem_zipIdx {α : Type} : ∀ (l : List α) (n : ℕ) (x : α × ℕ), x ∈ l.zipIdx n → x.1 ∈ l
  | [], _, _, h => by simp at h
  | a :: l, n, x, h => by
    rw [List.zipIdx_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (fst_mem_zipIdx l (n + 1) x h)

/-- **A relation term's weight at its merged point is multilinear**, off `Z_bad`'s roots and with
Flock's point of `q_flock`'s coordinates. -/
theorem term_mle (D : Deployment) (Fl : FlockSound (D.shape.heights.getD opBlake2s 0)) (s : USt)
    (ch : List E) (fd : Done) (t : E) (vals : List E) (h2 : 1 ≤ D.shape.heights.getD opBlake2s 0)
    (hfp : (Fl.prog.out fd []).1.length = 8 + D.shape.heights.getD opBlake2s 0)
    (hz : (zBad D.shape ((Fl.prog.out fd []).1.getD 0 0)).eval t ≠ 0) (c : Commitment) (r : Relation)
    (hr : r ∈ mine (relsAt D Fl s ch fd t vals) c) (tm : Term) (htm : tm ∈ r.terms)
    (rm : Option (List E)) :
    Mle (batchVars D.shape) (fun p ↦ weightAt ⟨[mergedPoint (mine (relsAt D Fl s ch fd t vals) c) tm.point],
      [(tm.column, 0, tm.twist, 1)], 0, 1⟩ (layoutOf D.shape c) p rm) := by
  have hmem := List.mem_filter.mp hr
  have hrc : r.commitment = c := by simpa using hmem.2
  refine Mle.congr ?_ fun p _ ↦ (weightAt_single (layoutOf D.shape c) p rm _ tm.column tm.twist).symm
  rcases term_kinds D Fl s ch fd t vals r hmem.1 tm htm with ⟨htw, hk⟩ | ⟨htw, hcol, hpt, hrc1⟩
  · rw [htw]
    by_cases hslot : ∃ j, tm.column = .qflockSlot j
    · obtain ⟨j, hj⟩ := hslot
      obtain ⟨hc1, hy⟩ := hk.resolve_left fun h ↦ h j hj
      rw [hrc] at hc1
      subst hc1
      have hmp : mergedPoint (mine (relsAt D Fl s ch fd t vals) .c1) tm.point = Eval.yOf D t := by
        rw [hy]
        exact mergedSelf _ _ ⟨r, hr, tm, htm, hy⟩ fun r' hr' tm' htm' hlt ↦
          Eval.y_self D Fl s ch fd t vals h2 hz r' (List.mem_filter.mp hr').1
            (by simpa using (List.mem_filter.mp hr').2) tm' htm' hlt
      rw [hmp, hj]
      refine mle_slot _ rm _ j (Eval.yOf D t) fun b hb ↦ ?_
      obtain ⟨-, -, -, -, ⟨off, hoff⟩⟩ := c1Limbs D.shape
      rw [hoff, List.mem_singleton] at hb
      subst hb
      have hy' : (Eval.yOf D t).length = D.shape.heights.getD opBlake2s 0 := by
        rw [Eval.yOf, Eval.coordinatesAt_length, Eval.coordinateFunctionals_size]
      show 8 + (Eval.yOf D t).length ≤ D.shape.heights.getD opBlake2s 0 + 8
      omega
    · simp only [not_exists] at hslot
      exact mle_plain _ rm _ _ tm.column hslot
  · rw [hrc] at hrc1
    subst hrc1
    have hext := (mergedPrefix (mine (relsAt D Fl s ch fd t vals) .c1) (Fl.prog.out fd []).1
      ⟨r, hr, tm, htm, hpt⟩).1
    rw [htw, hcol, hpt]
    cases rm with
    | none => exact mle_ring_none _ _ _ _
    | some map =>
      refine mle_ring _ _ map _ (Fl.prog.out fd []).1 hext fun b hb ↦ ?_
      have hle := (Eval.c1_limbs D.shape .qflock b hb).2
      obtain ⟨-, -, -, -, ⟨off, hoff⟩⟩ := c1Limbs D.shape
      rw [hoff, List.mem_singleton] at hb
      subst hb
      refine ⟨?_, hle⟩
      show D.shape.heights.getD opBlake2s 0 + 8 = (Fl.prog.out fd []).1.length
      omega

/-- **A combined claim's weight is multilinear in the batch's point**, off `Z_bad`'s roots and
with Flock's point of `q_flock`'s `8 + h_B` coordinates. -/
theorem combAt_isMle (D : Deployment) (Fl : FlockSound (D.shape.heights.getD opBlake2s 0)) (s : USt)
    (ch : List E) (fd : Done) (t : E) (vals : List E) (ρ : E)
    (h2 : 1 ≤ D.shape.heights.getD opBlake2s 0)
    (hfp : (Fl.prog.out fd []).1.length = 8 + D.shape.heights.getD opBlake2s 0)
    (hz : (zBad D.shape ((Fl.prog.out fd []).1.getD 0 0)).eval t ≠ 0) (c : Commitment) :
    Mle (batchVars D.shape) (fun p ↦
      weightAt (combAt D Fl s ch fd t vals ρ c) (layoutOf D.shape c) p (ringMapAt Fl fd)) := by
  by_cases hm : mine (relsAt D Fl s ch fd t vals) c = []
  · have hnone : combine (relsAt D Fl s ch fd t vals) c ρ = none := by
      unfold combine
      simp only [mine] at hm
      simp [hm]
    refine Mle.congr (Mle.zero _) fun p _ ↦ ?_
    simp only [combAt, hnone, Option.getD_none]
    rfl
  · obtain ⟨cb, hcb, -, hF⟩ := combineEq (relsAt D Fl s ch fd t vals) c ρ hm
    have hca : combAt D Fl s ch fd t vals ρ c = cb := by
      simp only [combAt, hcb, Option.getD_some]
    rw [hca]
    refine Mle.congr (Mle.listSum (mine (relsAt D Fl s ch fd t vals) c).zipIdx
      (fun ri p ↦ ρ ^ ri.2 * (ri.1.terms.map fun tm ↦ tm.coefficient *
        weightAt ⟨[mergedPoint (mine (relsAt D Fl s ch fd t vals) c) tm.point],
          [(tm.column, 0, tm.twist, 1)], 0, 1⟩ (layoutOf D.shape c) p (ringMapAt Fl fd)).sum)
      fun ri hri ↦ Mle.const_mul _ (Mle.listSum ri.1.terms _ fun tm htm ↦ Mle.const_mul _
        (term_mle D Fl s ch fd t vals h2 hfp hz c ri.1 (fst_mem_zipIdx _ _ _ hri) tm htm _)))
      fun p _ ↦ ?_
    rw [weightAtLinear cb (layoutOf D.shape c) p (ringMapAt Fl fd)]
    exact (hF fun col pt tw ↦
      weightAt ⟨[pt], [(col, 0, tw, 1)], 0, 1⟩ (layoutOf D.shape c) p (ringMapAt Fl fd)).symm

end UniSound.Ids.Multilin

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Multilin

/-- **The weights are multilinear off `Z_bad`'s roots** (`UniFinal`'s `WeightMle`, per commitment):
where `Z_bad(t) ≠ 0` and Flock's result is the main line's (`FlockGood`), each commitment's combined
claim's weight at a point `r` of the batch's variables is the fold of its values on the cube. -/
theorem combAt_mle (D : Deployment) (Fl : FlockSound (D.shape.heights.getD opBlake2s 0)) (s : USt)
    (ch : List E) (fd : Done) (t : E) (vals : List E) (ρ : E)
    (h2 : 1 ≤ D.shape.heights.getD opBlake2s 0)
    (hgood : FlockGood (D.shape.heights.getD opBlake2s 0) (batchVars D.shape) (Fl.prog.out fd []))
    (hz : (zBad D.shape ((Fl.prog.out fd []).1.getD 0 0)).eval t ≠ 0)
    (r : List E) (hr : r.length = batchVars D.shape) (c : Commitment) :
    foldAll (fun u ↦ weightAt (combAt D Fl s ch fd t vals ρ c) (layoutOf D.shape c)
        (bitsE u (batchVars D.shape)) (ringMapAt Fl fd)) r 0 =
      weightAt (combAt D Fl s ch fd t vals ρ c) (layoutOf D.shape c) r (ringMapAt Fl fd) :=
  combAt_isMle D Fl s ch fd t vals ρ h2 hgood.2.1 hz c r hr

/-- **`combAt_mle` at the reference shape** (`h_B = 18`). -/
theorem combAt_mle_ref (D : Deployment) (hS : D.shape = reference)
    (Fl : FlockSound (D.shape.heights.getD opBlake2s 0)) (s : USt) (ch : List E) (fd : Done) (t : E)
    (vals : List E) (ρ : E)
    (hgood : FlockGood (D.shape.heights.getD opBlake2s 0) (batchVars D.shape) (Fl.prog.out fd []))
    (hz : (zBad D.shape ((Fl.prog.out fd []).1.getD 0 0)).eval t ≠ 0)
    (r : List E) (hr : r.length = batchVars D.shape) (c : Commitment) :
    foldAll (fun u ↦ weightAt (combAt D Fl s ch fd t vals ρ c) (layoutOf D.shape c)
        (bitsE u (batchVars D.shape)) (ringMapAt Fl fd)) r 0 =
      weightAt (combAt D Fl s ch fd t vals ρ c) (layoutOf D.shape c) r (ringMapAt Fl fd) :=
  combAt_mle D Fl s ch fd t vals ρ (by rw [hS, reference_eq]; decide) hgood hz r hr c

end UniSound.Ids

/-- info: 'UniSound.Ids.combAt_mle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.combAt_mle

/-- info: 'UniSound.Ids.combAt_mle_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.combAt_mle_ref

/-- info: 'UniSound.Ids.Multilin.term_kinds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.Multilin.term_kinds
