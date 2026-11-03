-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The walk is `formal/UniStatement`'s `Rec.lean`
-- (`Flock.walkedTerminal`, `Flock.blake2sRowValues`), restated as folds in `WalkCode.lean`.
import FlockSoundUni.WalkCode
import FlockSoundUni.Rec3Walk

/-!
# The walked terminal is the pending reduction's sum: the algebra

`walkLemma_of_rows`: **`WalkLemma`** (`Rec3Walk.lean`: the walk's zero gives the pending claim) from **the rows'
specification** `RowsSpec` (the walk's `left`, `right` are the BLAKE2s R1CS's `A0 w`, `B0 w`: `Walk.lean`'s
circuit simulation, `rowValues_spec`). The walked terminal is `matrixSum + known` (`WalkCode.lean`'s
`walkedTerminal_eq`), `known` the pending claim's own known part (the same `knownWeights`, `rowLowWeights`); so the
zero `walked + r_lc = 0` says the claim `r_lc + known` is `matrixSum`, and `matrixSum` is the pending sum
(`pendingHolds_iff`'s `Σ_cy matPart … · s(cy)`): reindexing the rows `h · 64 + low` and the columns
`ch · 64 + cy` by `posFin`, `eq(chi_in)` and the low weights are `rowW`, the column weights `s ⊗ eq(chi_in')` are the
slices against `eqP χ'`.
-/

namespace FlockSound.Uni

open UniStatement UniStatement.Flock UniSound LeanVM.Parameters Finset FlockSound.Uni.Walk

/-- **The walk's rows**: `left`, `right` are the R1CS's `A0 w`, `B0 w` for column weights `w` of `2^14` entries. -/
def RowsSpec : Prop :=
  ∀ (cw : Array E), cw.size = 2 ^ 14 → ∀ j : Fin (2 ^ 14),
    (blake2sRowValues cw).1.getD j 0 =
        ∑ i : Fin (2 ^ 14), (if Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs.A j i then cw.getD i 0 else 0) ∧
      (blake2sRowValues cw).2.getD j 0 =
        ∑ i : Fin (2 ^ 14), (if Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs.B j i then cw.getD i 0 else 0)

/-! ## Folds as sums -/

theorem foldl_pair_add {α : Type*} (f g : α → E) : ∀ (l : List α) (a b : E),
    l.foldl (fun st x ↦ (st.1 + f x, st.2 + g x)) (a, b) = (a + (l.map f).sum, b + (l.map g).sum)
  | [], a, b => by simp
  | x :: l, a, b => by
    rw [List.foldl_cons, foldl_pair_add f g l]
    simp only [List.map_cons, List.sum_cons, Prod.mk.injEq]
    constructor <;> ring

theorem sum_range'_map (f : ℕ → E) : ∀ n : ℕ, ((List.range' 0 n).map f).sum = ∑ i ∈ range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range'_1_concat, List.map_append, List.sum_append, sum_range'_map f n, Finset.sum_range_succ]
    simp

theorem foldl_add_range' (f : ℕ → E) (n : ℕ) (a : E) :
    (List.range' 0 n).foldl (fun m i ↦ m + f i) a = a + ∑ i ∈ range n, f i := by
  rw [tx_foldl_add, sum_range'_map]

/-- **`matrixSum` as sums.** -/
theorem matrixSum_eq (lw rows left right : Array E) (alpha : E) :
    matrixSum lw rows left right alpha = ∑ h ∈ range rows.size, rows.getD h 0 *
      (∑ low ∈ range lw.size, lw.getD low 0 * left.getD (h * kBits + low) 0 +
        alpha * ∑ low ∈ range lw.size, lw.getD low 0 * right.getD (h * kBits + low) 0) := by
  unfold matrixSum
  simp only [foldl_pair_add, zero_add, sum_range'_map]
  rw [foldl_add_range', zero_add]

/-! ## The column weights -/

theorem getD_set!' (a : Array E) (i j : ℕ) (v : E) (hi : i < a.size) :
    (a.set! i v).getD j 0 = if i = j then v else a.getD j 0 := by
  rw [Array.set!_eq_setIfInBounds]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt hi,
      Option.getD_some]
  · rw [ite_eq_right hij, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_ne hij]

theorem size_set!' (a : Array E) (i : ℕ) (v : E) : (a.set! i v).size = a.size := by
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

/-- The inner loop over a row `h` of the column weights. -/
theorem colInner (s : List E) (hs : s.length = 64) (hv : E) (h : ℕ) (hh : h < 256) :
    ∀ (n : ℕ) (w : Array E), n ≤ 64 → w.size = 2 ^ 14 →
      ((List.range' 0 n).foldl (fun w l ↦ w.set! (h * kBits + l) (s.toArray.getD l 0 * hv)) w).size = 2 ^ 14 ∧
      ∀ j, ((List.range' 0 n).foldl (fun w l ↦ w.set! (h * kBits + l) (s.toArray.getD l 0 * hv)) w).getD j 0 =
        if j / 64 = h ∧ j % 64 < n then s.getD (j % 64) 0 * hv else w.getD j 0
  | 0, w, _, hw => ⟨hw, fun j ↦ by simp⟩
  | n + 1, w, hn, hw => by
    obtain ⟨ih1, ih2⟩ := colInner s hs hv h hh n w (by omega) hw
    rw [show List.range' 0 (n + 1) = List.range' 0 n ++ [0 + n] from List.range'_1_concat,
      List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add]
    have hk : Flock.kBits = 64 := rfl
    have hlt : h * kBits + n < 2 ^ 14 := by rw [hk]; omega
    refine ⟨by rw [size_set!', ih1], fun j ↦ ?_⟩
    rw [getD_set!' _ _ _ _ (by rw [ih1]; exact hlt), ih2]
    by_cases hj : h * kBits + n = j
    · rw [ite_eq_left hj]
      rw [hk] at hj
      have h1 : j / 64 = h := by omega
      have h2 : j % 64 = n := by omega
      rw [ite_eq_left ⟨h1, by omega⟩, h2, Array.getD_eq_getD_getElem?, List.getElem?_toArray]
      rfl
    · rw [ite_eq_right hj]
      rw [hk] at hj
      by_cases hc : j / 64 = h ∧ j % 64 < n
      · rw [ite_eq_left hc, ite_eq_left ⟨hc.1, by omega⟩]
      · rw [ite_eq_right hc]
        by_cases hc' : j / 64 = h ∧ j % 64 < n + 1
        · exfalso
          have : j % 64 = n := by omega
          omega
        · rw [ite_eq_right hc']

/-- **The column weights**: `w[i] = s[i mod 64] · eq(chi_in')[i / 64]`. -/
theorem colWeights_getD (s : List E) (hs : s.length = 64) (high : Array E) (hh : high.size = 256) :
    (colWeights s high).size = 2 ^ 14 ∧ ∀ i, i < 2 ^ 14 →
      (colWeights s high).getD i 0 = s.getD (i % 64) 0 * high.getD (i / 64) 0 := by
  have hk : Flock.kBits = 64 := rfl
  have hsz : s.toArray.size = 64 := by rw [List.size_toArray, hs]
  have outer : ∀ n : ℕ, n ≤ 256 →
      ((List.range' 0 n).foldl (fun w h ↦ (List.range' 0 64).foldl
        (fun w l ↦ w.set! (h * kBits + l) (s.toArray.getD l 0 * high.getD h 0)) w)
        (Array.replicate (2 ^ 14) 0)).size = 2 ^ 14 ∧
      ∀ j, ((List.range' 0 n).foldl (fun w h ↦ (List.range' 0 64).foldl
        (fun w l ↦ w.set! (h * kBits + l) (s.toArray.getD l 0 * high.getD h 0)) w)
        (Array.replicate (2 ^ 14) 0)).getD j 0 =
          if j / 64 < n then s.getD (j % 64) 0 * high.getD (j / 64) 0 else 0 := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨Array.size_replicate .., fun j ↦ ?_⟩
      simp only [List.range'_zero, List.foldl_nil, Nat.not_lt_zero, ite_false]
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split_ifs <;> rfl
    | succ n ih =>
      intro hn
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      rw [show List.range' 0 (n + 1) = List.range' 0 n ++ [0 + n] from List.range'_1_concat,
        List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add]
      obtain ⟨c1, c2⟩ := colInner s hs (high.getD n 0) n (by omega) 64 _ le_rfl ih1
      refine ⟨c1, fun j ↦ ?_⟩
      rw [c2, ih2]
      by_cases hj : j / 64 = n ∧ j % 64 < 64
      · rw [ite_eq_left hj, ite_eq_left (by omega), hj.1]
      · rw [ite_eq_right hj]
        have : ¬ j / 64 = n := fun h ↦ hj ⟨h, Nat.mod_lt _ (by norm_num)⟩
        by_cases h2 : j / 64 < n
        · rw [ite_eq_left h2, ite_eq_left (by omega)]
        · rw [ite_eq_right h2, ite_eq_right (by omega)]
  obtain ⟨o1, o2⟩ := outer 256 le_rfl
  unfold colWeights
  rw [hh, hsz, show (2 : ℕ) ^ blake2sR1csLogSize = 2 ^ 14 from rfl]
  refine ⟨o1, fun i hi ↦ ?_⟩
  rw [o2, ite_eq_left (by omega)]

/-! ## The weights at the cube's points -/

/-- **The low weights** at a cube point of the row's `6` packing bits: `lowW` (the skip's Lagrange weight times `eq`
on the other `3`). -/
theorem lowWeights_cube (z : E) (rowLow : List E) (hl : rowLow.length = 3) (cy : Cube (3 + 3)) :
    (rowLowWeights (some z) rowLow).2.getD (cubeFin (3 + 3) cy) 0 =
      lowW (skipNodes 3 (by decide)) z (ptOf rowLow 3) cy := by
  have hpk : Flock.packing - rowLow.length = 3 := by simp only [Flock.packing, hl]
  simp only [rowLowWeights, hpk]
  have hS : (Flock.lagrangeWeights (2 ^ 3) z).length = 2 ^ 3 := lagrangeWeights_length _ _
  have hM : (eqKernel rowLow).toList.length = 2 ^ 3 := by
    rw [Array.length_toList, eqKernel_size, hl]
  rw [tx_cubeFin_split, tx_flatMap_getD _ hS _ (cubeFin 3 (lowPart cy)).isLt
    (by rw [hM]; exact (cubeFin 3 (highPart cy)).isLt), lagrangeWeights_skip 3 (by decide), ← tx_array_getD,
    eqKernel_cube rowLow hl]
  rfl

theorem length_lowWeights (z : E) (rowLow : List E) (hl : rowLow.length = 3) :
    (rowLowWeights (some z) rowLow).2.length = 64 := by
  simp only [rowLowWeights, tx_length_flatMap, lagrangeWeights_length, Array.length_toList, eqKernel_size, hl]
  rfl

theorem posFin_val33 (cy : Cube (3 + 3)) (ch : Cube 8) :
    ((posFin (k := 3) (l := 3) rfl (cy, ch) : Fin _) : ℕ) = cubeFin (3 + 3) cy + 64 * cubeFin 8 ch :=
  tx_posFin_val rfl cy ch

/-- **The walked terminal's matrix part is the pending sum's**: with the rows `A0 w`, `B0 w` (`RowsSpec`), the
fold `matrixSum` is `Σ_cy matPart … · s(cy)`. -/
theorem matrixSum_spec (hR : RowsSpec) (z alpha : E) (rowLow chiIn chiInPrime s : List E) (hl : rowLow.length = 3)
    (h8 : chiIn.length = 8) (h8' : chiInPrime.length = 8) (hs : s.length = 64) :
    matrixSum (rowLowWeights (some z) rowLow).2.toArray (eqKernel chiIn)
        (blake2sRowValues (colWeights s (eqKernel chiInPrime))).1
        (blake2sRowValues (colWeights s (eqKernel chiInPrime))).2 alpha =
      ∑ cy, matPart (cubeMat (k := 3) (l := 3) rfl Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs.A)
        (cubeMat (k := 3) (l := 3) rfl Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs.B) (skipNodes 3 (by decide))
        z (ptOf rowLow 3) (ptOf chiIn 8) (ptOf chiInPrime 8) alpha cy * sliceOf s cy := by
  set A := Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs.A
  set B := Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs.B
  set cw := colWeights s (eqKernel chiInPrime) with hcw
  have hhigh : (eqKernel chiInPrime).size = 256 := by rw [eqKernel_size, h8']; rfl
  obtain ⟨hcs, hcg⟩ := colWeights_getD s hs _ hhigh
  have hk : Flock.kBits = 64 := rfl
  -- The column weights at a position.
  have hcol : ∀ col : Pos 3 3 8, cw.getD (posFin (k := 3) (l := 3) rfl col) 0 =
      sliceOf s col.1 * eqP (ptOf chiInPrime 8) col.2 := by
    rintro ⟨cy, ch⟩
    have hlt := (posFin (k := 3) (l := 3) rfl (cy, ch)).isLt
    rw [hcg _ hlt, posFin_val33]
    have h1 : ((cubeFin (3 + 3) cy : ℕ) + 64 * cubeFin 8 ch) % 64 = cubeFin (3 + 3) cy := by
      have := (cubeFin (3 + 3) cy).isLt
      omega
    have h2 : ((cubeFin (3 + 3) cy : ℕ) + 64 * cubeFin 8 ch) / 64 = cubeFin 8 ch := by
      have := (cubeFin (3 + 3) cy).isLt
      omega
    rw [h1, h2, eqKernel_cube chiInPrime h8' ch]
    rfl
  -- A row of `A0 w` (`B0 w`) as a sum over the positions.
  have hrow : ∀ (M : Fin (2 ^ 14) → Fin (2 ^ 14) → Bool) (left : Array E),
      (∀ j : Fin (2 ^ 14), left.getD j 0 = ∑ i : Fin (2 ^ 14), (if M j i then cw.getD i 0 else 0)) →
      ∀ row : Pos 3 3 8, left.getD (posFin (k := 3) (l := 3) rfl row) 0 =
        ∑ col : Pos 3 3 8, bit (cubeMat (k := 3) (l := 3) rfl M row col) *
          (sliceOf s col.1 * eqP (ptOf chiInPrime 8) col.2) := by
    intro M left hM row
    rw [hM]
    refine (Fintype.sum_equiv (posFin (k := 3) (l := 3) rfl) _ _ fun col ↦ ?_).symm
    rw [← hcol col, cubeMat]
    cases M (posFin rfl row) (posFin rfl col) <;> simp [bit]
  have hA := hrow A _ fun j ↦ (hR cw hcs j).1
  have hB := hrow B _ fun j ↦ (hR cw hcs j).2
  -- The left side as a sum over the rows.
  have hlw : (rowLowWeights (some z) rowLow).2.toArray.size = 2 ^ (3 + 3) := by
    rw [List.size_toArray, length_lowWeights z rowLow hl]
    norm_num
  have hrs : (eqKernel chiIn).size = 2 ^ 8 := by rw [eqKernel_size, h8]
  rw [matrixSum_eq, hrs, hlw, sum_range_eq_sum_cube]
  simp only [sum_range_eq_sum_cube, hk]
  have hidx : ∀ (ch : Cube 8) (cy : Cube (3 + 3)), (cubeFin 8 ch : ℕ) * 64 + cubeFin (3 + 3) cy =
      posFin (k := 3) (l := 3) rfl (cy, ch) := by
    intro ch cy
    rw [posFin_val33]
    ring
  simp only [hidx, hA, hB, eqKernel_cube chiIn h8, Array.getD_eq_getD_getElem?, List.getElem?_toArray]
  -- The right side as a sum over the rows.
  simp only [matPart, mle, rowW, Finset.sum_mul, Finset.mul_sum]
  set F : Pos 3 3 8 → Pos 3 3 8 → E := fun row col ↦
    lowW (skipNodes 3 (by decide)) z (ptOf rowLow 3) row.1 * eqP (ptOf chiIn 8) row.2 *
      (bit (cubeMat (k := 3) (l := 3) rfl A row col) + alpha * bit (cubeMat (k := 3) (l := 3) rfl B row col)) *
        (sliceOf s col.1 * eqP (ptOf chiInPrime 8) col.2) with hF
  calc _ = ∑ ch : Cube 8, ∑ cy : Cube (3 + 3), ∑ col : Pos 3 3 8, F (cy, ch) col := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x1 _ ↦ ?_
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← List.getD_eq_getElem?_getD, lowWeights_cube z rowLow hl, hF]
        ring
    _ = ∑ row : Pos 3 3 8, ∑ col : Pos 3 3 8, F row col := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = ∑ col : Pos 3 3 8, ∑ row : Pos 3 3 8, F row col := Finset.sum_comm
    _ = _ := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun cy _ ↦ Finset.sum_congr rfl fun ch _ ↦
          Finset.sum_congr rfl fun row _ ↦ ?_
        rw [hF]
        simp only [lowW]
        ring

/-! ## The walk's lemma -/

/-- **`WalkLemma` from the rows' specification**: the walk's zero `walkedTerminal … + r_lc = 0` gives the pending
claim (`r_lc` plus the same known terms) equal to `matrixSum`, the pending sum (`matrixSum_spec`, `pendingHolds_iff`). -/
theorem walkLemma_of_rows (hR : RowsSpec) : WalkLemma := by
  intro z rowLow chiIn chiInPrime s alpha rLc hl h8 h8' hs hz
  rw [pendingHolds_iff (k := 3) (l := 3) rfl (by decide) z alpha rLc rowLow chiIn chiInPrime s hl h8,
    ← matrixSum_spec hR z alpha rowLow chiIn chiInPrime s hl h8 h8' hs]
  rw [walkedTerminal_eq] at hz
  have hc : (Flock.Pending.new (some z) rowLow chiIn chiInPrime alpha rLc (some s)).claim =
      rLc + ((knownWeights alpha chiIn chiInPrime).1 * dot (rowLowWeights (some z) rowLow).2 s +
        (knownWeights alpha chiIn chiInPrime).2 * s.getD (constantColumn % kBits) 0) := rfl
  rw [hc]
  exact CharTwo.add_eq_zero.mp (by linear_combination hz)

/-- **The converse** (for completeness): the pending claim its sum gives the walk's zero. -/
theorem walkLemmaConverse_of_rows (hR : RowsSpec) :
    ∀ (z : E) (rowLow chiIn chiInPrime s : List E) (alpha rLc : E), rowLow.length = 3 → chiIn.length = 8 →
      chiInPrime.length = 8 → s.length = 64 →
      PendingHolds (Flock.Pending.new (some z) rowLow chiIn chiInPrime alpha rLc (some s)) →
        Flock.walkedTerminal (some z) rowLow chiIn chiInPrime s alpha + rLc = 0 := by
  intro z rowLow chiIn chiInPrime s alpha rLc hl h8 h8' hs hp
  rw [pendingHolds_iff (k := 3) (l := 3) rfl (by decide) z alpha rLc rowLow chiIn chiInPrime s hl h8,
    ← matrixSum_spec hR z alpha rowLow chiIn chiInPrime s hl h8 h8' hs] at hp
  have hc : (Flock.Pending.new (some z) rowLow chiIn chiInPrime alpha rLc (some s)).claim =
      rLc + ((knownWeights alpha chiIn chiInPrime).1 * dot (rowLowWeights (some z) rowLow).2 s +
        (knownWeights alpha chiIn chiInPrime).2 * s.getD (constantColumn % kBits) 0) := rfl
  rw [hc] at hp
  rw [walkedTerminal_eq, ← hp]
  linear_combination (rLc + (knownWeights alpha chiIn chiInPrime).1 * dot (rowLowWeights (some z) rowLow).2 s +
    (knownWeights alpha chiIn chiInPrime).2 * s.getD (constantColumn % kBits) 0) * two_eq_zero_E

end FlockSound.Uni

/-- info: 'FlockSound.Uni.walkLemmaConverse_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.walkLemmaConverse_of_rows

/-- info: 'FlockSound.Uni.walkLemma_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.walkLemma_of_rows

/-- info: 'FlockSound.Uni.matrixSum_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.matrixSum_spec
