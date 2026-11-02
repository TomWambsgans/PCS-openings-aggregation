-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import FlockSound.Flock
import FlockSound.Fields

/-!
# Flock at leanVM's constants, and its relation as Lv42's `FlockRegion.Holds`

The generic theorems (`Flock.lean`) at leanVM 42422001's Flock (`Lv42.Parameters.Flock`): `E`, the
skip over `k ≤ 6` of the 6 packing bits (`l = 6 - k` left to rounds), `m = 8` slot bits, `κ` batch
bits, the seven fixed coordinates `fixedPoint`, the skip nodes `φ_8(0), …, φ_8(2^(k+1) - 1)`, the
packing weights `x^cy`, the 64 twists, the ring map's shifts in leanVM's order or the tower order.

* `cubeFin`: a cube point as a number, low bit first (`testBit_cubeFin`);
* **`leanvmSetup_valid`**: the constants satisfy `Setup.Valid` (the nodes are distinct, the fixed
  weights `F_2`-independent, ring switching injective, the twists covered), from `Fields.lean`'s
  kernel checks;
* **`r1csHolds_iff`**: the generic relation on the column's bits (`colBits`) is Lv42's
  `BlockR1CS.BatchHolds r1cs constPos (bitTable c)`, i.e. `FlockRegion.Holds`;
* `colPack`: the column's words are its bits packed by `x^cy` (`hpack` of the generic theorems).
-/

namespace FlockSound

open Finset LeanVM.Parameters LeanVM.Protocol Lv42.Parameters Lv42.Protocol CompPoly
  CMlPolynomialEval

/-! ## Cube points as numbers -/

/-- A cube point as a number, low bit first. -/
def cubeFin (n : ℕ) : Cube n ≃ Fin (2 ^ n) :=
  (Equiv.arrowCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finFunctionFinEquiv

theorem cubeFin_symm_apply {n : ℕ} (j : Fin (2 ^ n)) (i : Fin n) :
    (cubeFin n).symm j i = j.val.testBit i := by
  simp only [cubeFin, Equiv.symm_trans_apply, Equiv.arrowCongr_symm, Equiv.arrowCongr_apply,
    Equiv.refl_symm, Equiv.refl_apply, Function.comp, Equiv.symm_symm]
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h := finFunctionFinEquiv_symm_apply_val (m := 2) (n := n) j i
  generalize finFunctionFinEquiv.symm j i = x at h
  have hx : x.val < 2 := x.isLt
  rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl
  · simp only [Fin.val_zero] at h
    rw [← h]
    decide
  · simp only [Fin.val_one] at h
    rw [← h]
    decide

theorem testBit_cubeFin {n : ℕ} (b : Cube n) (i : Fin n) : (cubeFin n b).val.testBit i = b i := by
  rw [← cubeFin_symm_apply, Equiv.symm_apply_apply]

/-- The Lagrange basis at a cube point's index is `eqP`. -/
theorem lagrangeBasis_cubeFin {n : ℕ} (w : Vector E n) (b : Cube n) :
    (lagrangeBasis w)[cubeFin n b] = eqP (fun i ↦ w[i]) b := by
  rw [Fin.getElem_fin, lagrangeBasis_getElem_nat _ (cubeFin n b).isLt]
  simp only [eqP, eq1, testBit_cubeFin]

/-- A cube of `k + l = 6` packing bits as the 64 bit positions of a word. -/
def cube64 {k l : ℕ} (hkl : k + l = 6) : Cube (k + l) ≃ Fin (2 ^ 6) :=
  (cubeFin (k + l)).trans (finCongr (by rw [hkl]))

theorem cube64_val {k l : ℕ} (hkl : k + l = 6) (b : Cube (k + l)) :
    (cube64 hkl b).val = (cubeFin (k + l) b).val := rfl

/-! ## The constants -/

/-- The skip nodes: `φ_8(i)` on the skip domain, `φ_8(2^k + i)` on its coset. -/
def skipNodes (k : ℕ) (hk : k ≤ 6) : Bool × Cube k → E := fun p ↦
  Flock.skipNode ⟨(if p.1 then 2 ^ k else 0) + (cubeFin k p.2).val, by
    have h1 := (cubeFin k p.2).isLt
    have h2 : 2 ^ k ≤ 64 := (Nat.pow_le_pow_right (by norm_num) hk).trans (by norm_num)
    split <;> omega⟩

theorem skipNodes_injective (k : ℕ) (hk : k ≤ 6) : Function.Injective (skipNodes k hk) := by
  rintro ⟨b, i⟩ ⟨b', i'⟩ h
  simp only [skipNodes, Flock.skipNode] at h
  have h2 : 2 ^ k ≤ 64 := (Nat.pow_le_pow_right (by norm_num) hk).trans (by norm_num)
  have hi := (cubeFin k i).isLt
  have hi' := (cubeFin k i').isLt
  have hv := phi8_injOn (by split <;> omega) (by split <;> omega) (ofK_injective h)
  have hb : b = b' := by
    cases b <;> cases b' <;> first | rfl | (simp at hv; omega)
  subst hb
  have : (cubeFin k i).val = (cubeFin k i').val := by omega
  exact Prod.ext rfl ((cubeFin k).injective (Fin.ext this))

/-- The packing weights `x^cy`. -/
def packW {k l : ℕ} (hkl : k + l = 6) (cy : Cube (k + l)) : E := ofK (g ^ (cube64 hkl cy).val)

/-- The fixed coordinates, as a point. -/
def fixedPt : Fin 7 → E := fun i ↦ Flock.fixedPoint[i]

theorem hfixed_leanvm : HFixed fixedPt := by
  intro c hc h
  have h' : ∑ v : Fin (2 ^ 7), (lagrangeBasis Flock.fixedPoint)[v] * c ((cubeFin 7).symm v) = 0 := by
    rw [← h]
    refine Fintype.sum_equiv (cubeFin 7).symm _ _ fun v ↦ ?_
    obtain ⟨b, rfl⟩ := (cubeFin 7).surjective v
    rw [lagrangeBasis_cubeFin, Equiv.symm_apply_apply]
    rfl
  have := fixedWeights_independent (fun v ↦ c ((cubeFin 7).symm v)) (fun v ↦ hc _) h'
  intro v
  simpa using this (cubeFin 7 v)

theorem ringInjective_leanvm {k l : ℕ} (hkl : k + l = 6) (δ : Cube (k + l) → E)
    (h : ∀ j ∈ range 64, frobPair univ (packW hkl) δ j = 0) : δ = 0 := by
  have h' := ringSwitch_injective (fun i ↦ δ ((cube64 hkl).symm i)) fun j hj ↦ by
    rw [← h j (mem_range.mpr hj), frobPair]
    refine Fintype.sum_equiv (cube64 hkl).symm _ _ fun i ↦ ?_
    simp only [packW, Equiv.apply_symm_apply]
    rfl
  funext cy
  simpa using h' (cube64 hkl cy)

/-- **leanVM's Flock constants** at a skip of `k` bits, `κ` batch bits, the ring map's shifts `sh`
and the R1CS of a block: the generic `Setup` with `m = 8`, `f₀ = 7`. -/
def leanvmSetup (k l κ ns : ℕ) (hkl : k + l = 6) (hk : k ≤ 6) (hsize : l + 8 + κ = 7 + ns)
    (sh : List ℕ) (A B : Pos k l 8 → Pos k l 8 → Bool) (cpos : Pos k l 8) : Setup E k l 8 κ 7 ns where
  A := A
  B := B
  cpos := cpos
  node := skipNodes k hk
  fixed := fixedPt
  hsize := hsize
  sh := sh
  w := packW hkl
  twists := range 64

/-- **The constants' facts** for both orders of the ring map. -/
theorem leanvmSetup_valid (k l κ ns : ℕ) (hkl : k + l = 6) (hk : k ≤ 6)
    (hsize : l + 8 + κ = 7 + ns) (sh : List ℕ)
    (hsh : sh = [32, 16, 8, 4, 2, 1] ∨ sh = [1, 2, 4, 8, 16, 32])
    (A B : Pos k l 8 → Pos k l 8 → Bool) (cpos : Pos k l 8) :
    (leanvmSetup k l κ ns hkl hk hsize sh A B cpos).Valid where
  node_injective := skipNodes_injective k hk
  fixed := hfixed_leanvm
  ring_injective := ringInjective_leanvm hkl
  twists_covered := by
    rcases hsh with rfl | rfl
    · exact range_subset_rel_leanvm
    · exact range_subset_rel_tower

/-! ## Lv42's relation -/

/-- A position of a block as Lv42's index `jsk + 64 jin`. -/
def posFin {k l : ℕ} (hkl : k + l = 6) : Pos k l 8 ≃ Fin (2 ^ (Flock.kSkip + Flock.kIn)) :=
  (Equiv.prodCongr (cube64 hkl) (cubeFin 8)).trans (cubeSplit 6 8)

/-- A word of the column as its index `jin + 256 t`. -/
def wordFin (κ : ℕ) : Cube 8 × Cube κ ≃ Fin (2 ^ (8 + κ)) :=
  (Equiv.prodCongr (cubeFin 8) (cubeFin κ)).trans (cubeSplit 8 κ)

/-- **The column's bits** on the cube: packing bits `y`, slot bits `ch`, block `t`. -/
def colBits {k l κ : ℕ} (hkl : k + l = 6) (c : Column (8 + κ)) (y : Cube (k + l)) (ch : Cube 8)
    (t : Cube κ) : E :=
  cellBit (c.values.get (wordFin κ (ch, t))) (cube64 hkl y).val

theorem colBits_bool {k l κ : ℕ} (hkl : k + l = 6) (c : Column (8 + κ)) (y : Cube (k + l))
    (ch : Cube 8) (t : Cube κ) : colBits hkl c y ch t = 0 ∨ colBits hkl c y ch t = 1 := by
  unfold colBits cellBit
  split <;> simp

/-- The matrices on the cube. -/
def cubeMat {k l : ℕ} (hkl : k + l = 6) (M : Fin (2 ^ (Flock.kSkip + Flock.kIn)) →
    Fin (2 ^ (Flock.kSkip + Flock.kIn)) → Bool) (r c : Pos k l 8) : Bool :=
  M (posFin hkl r) (posFin hkl c)

theorem batchBlock_posFin {k l κ : ℕ} (hkl : k + l = 6) (c : Column (8 + κ)) (t : Cube κ)
    (row : Pos k l 8) :
    (BlockR1CS.batchBlock (s := Flock.kSkip) (m := Flock.kIn) (bitTable c) (cubeFin κ t))[posFin hkl row] =
      colBits hkl c row.1 row.2 t := by
  have h := BlockR1CS.batchBlock_cubeIndex (s := Flock.kSkip) (m := Flock.kIn) (bitTable c)
    (cubeFin κ t) (cube64 hkl row.1) (cubeFin 8 row.2)
  simp only [posFin, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, cubeSplit_apply]
  rw [h]
  simp only [bitTable, colBits, wordFin, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map,
    cubeSplit_apply]
  rw [Fin.getElem_fin, Vector.getElem_ofFn]

/-- **Lv42's relation is the generic one**: the column's blocks satisfy `BatchHolds` exactly when
its bits satisfy `R1CSHolds` on the cube. -/
theorem r1csHolds_iff {k l κ : ℕ} (hkl : k + l = 6) (C : BlockR1CS E (Flock.kSkip + Flock.kIn))
    (c : Column (8 + κ)) :
    R1CSHolds (cubeMat hkl C.A) (cubeMat hkl C.B) (colBits hkl c) ((posFin hkl).symm Flock.constPos) ↔
      BlockR1CS.BatchHolds C Flock.constPos (bitTable c) := by
  have hrow : ∀ (M : Fin (2 ^ (Flock.kSkip + Flock.kIn)) → Fin (2 ^ (Flock.kSkip + Flock.kIn)) → Bool)
      (t : Cube κ) (row : Pos k l 8),
      (∑ j, if M (posFin hkl row) j then
        (BlockR1CS.batchBlock (s := Flock.kSkip) (m := Flock.kIn) (bitTable c) (cubeFin κ t))[j] else 0) =
        rowProd (cubeMat hkl M) (colBits hkl c) row t := by
    intro M t row
    rw [rowProd]
    refine (Fintype.sum_equiv (posFin hkl).symm _ _ fun j ↦ ?_)
    obtain ⟨col, rfl⟩ := (posFin hkl).surjective j
    simp only [cubeMat, Equiv.symm_apply_apply, batchBlock_posFin]
  constructor
  · rintro ⟨hc, hp⟩ t
    obtain ⟨t, rfl⟩ := (cubeFin κ).surjective t
    refine ⟨fun j ↦ ?_, ?_⟩
    · obtain ⟨row, rfl⟩ := (posFin hkl).surjective j
      rw [C.rows_fst, C.rows_snd, hrow, hrow, batchBlock_posFin]
      exact hc row t
    · have := hp t
      rw [← Equiv.apply_symm_apply (posFin hkl) Flock.constPos, batchBlock_posFin]
      exact this
  · intro h
    refine ⟨fun row t ↦ ?_, fun t ↦ ?_⟩
    · have := (h (cubeFin κ t)).1 (posFin hkl row)
      rw [C.rows_fst, C.rows_snd, hrow, hrow, batchBlock_posFin] at this
      exact this
    · have := (h (cubeFin κ t)).2
      rw [← Equiv.apply_symm_apply (posFin hkl) Flock.constPos, batchBlock_posFin] at this
      exact this

/-- A word of the column, on the cube of its `8 + κ` coordinates. -/
def colWord {κ : ℕ} (c : Column (8 + κ)) (u : Cube (8 + κ)) : E :=
  ofK (c.values.get (wordFin κ (lowPart u, highPart u)))

/-- **Packing**: a word is its bits weighted by `x^cy`. -/
theorem colPack {k l κ : ℕ} (hkl : k + l = 6) (c : Column (8 + κ)) (u : Cube (8 + κ)) :
    colWord c u = ∑ cy, packW hkl cy * wordBits (colBits hkl c) cy u := by
  rw [colWord, ofK_eq_sum_cellBit]
  refine (Fintype.sum_equiv (cube64 hkl).symm _ _ fun i ↦ ?_)
  simp only [packW, wordBits, colBits, Equiv.apply_symm_apply]

end FlockSound
