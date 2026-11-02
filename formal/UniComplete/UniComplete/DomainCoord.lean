-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.DomainBasis

/-!
# The coordinate functionals (milestone 4, the domain facts)

`UniStatement.coordinatesAt t F` reads `y_l(t) = Σ_m a_{l,m} t^(2^m)` for the rows `a_l` of `F`
(`coordinateFunctionals r`, Gauss–Jordan over `K`). Each `y_l` is additive in characteristic two
(`sqn_add`: `(x + y)^(2^m) = x^(2^m) + y^(2^m)`), so it is determined by its values on the basis
`ω_{2^j}`, `j < r` (`coordinatesAt_add`, `coordinatesAt_zero`):

* `coordinatesAt_pointE`: **if `coordinatesAt (ω_{2^j}) F` is the unit vector `e_j` for each `j < r`, then
  `coordinatesAt (ω_i) F` is the bit vector of `i`** for every `i < 2^r` (any `F` of `r` rows);
* `coordinateFunctionals_size`: `coordinateFunctionals r` has `r` rows; so
  `coordinatesAt_pointE_of_basis` gives the bits of `i` from `CoordinateFunctionalsBasis r`, the hypothesis at
  `coordinateFunctionals r`.

**The instance `r = 18`** (the reference BLAKE2S height) is left as the named proposition
`CoordinateFunctionalsBasis 18`, not proved here. The evidence: `crates/leanvm_univariate`'s unit tests
(`y_l(ω_i) = i_l`, `domain.rs`), and an independent recomputation (this milestone's review script, Python over
`GF(2^64)`: the Gauss–Jordan inverse of `M[j][m] = β_j^(2^m)` and the check `Σ_m a_{l,m} β_j^(2^m) = δ_{lj}`
for all `l, j < 18`). The kernel does not do it in a few minutes: `decide +kernel` of `coordinateFunctionals 8`
against its `64` words takes 28 s (about `1,700` products in `K`, each a CompPoly carry-less product evaluated
on `BitVec`s, about 16 ms), and of `coordinateFunctionals 18` against its `324` words ran for more than 30
minutes at more than 10 GB without finishing (about `13,000` products for the elimination alone, plus about
`6,000` for the check itself); see the report of milestone 4's domain facts.
-/

namespace UniComplete.Domain

open LeanVM.Parameters UniStatement Finset

/-! ### Additivity -/

/-- **The Frobenius is additive**: `(x + y)^(2^m) = x^(2^m) + y^(2^m)` in `E`. -/
theorem sqn_add (x y : E) (m : ℕ) : sqn (x + y) m = sqn x m + sqn y m := by
  induction m generalizing x y with
  | zero => rfl
  | succ m ih =>
    simp only [sqn]
    rw [show (x + y) * (x + y) = x * x + y * y by linear_combination (x * y) * two_eq_zero_E, ih]

theorem sqn_zero (m : ℕ) : sqn (0 : E) m = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [sqn, mul_zero, ih]

/-- One functional's fold is additive in the powers it reads. -/
theorem fold_zip_add (as : List K) (xs ys : List E) (hl : xs.length = ys.length) (c d : E) :
    (as.zip (List.zipWith (· + ·) xs ys)).foldl
        (fun acc (a, x) ↦ if a ≠ 0 then acc + ofK a * x else acc) (c + d) =
      (as.zip xs).foldl (fun acc (a, x) ↦ if a ≠ 0 then acc + ofK a * x else acc) c +
        (as.zip ys).foldl (fun acc (a, x) ↦ if a ≠ 0 then acc + ofK a * x else acc) d := by
  induction as generalizing xs ys c d with
  | nil => simp
  | cons a as ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => simp
      | cons y ys => simp at hl
    | cons x xs =>
      cases ys with
      | nil => simp at hl
      | cons y ys =>
        simp only [List.zipWith_cons_cons, List.zip_cons_cons, List.foldl_cons]
        have hl' : xs.length = ys.length := by simpa using hl
        split_ifs with ha
        · rw [show c + d + ofK a * (x + y) = (c + ofK a * x) + (d + ofK a * y) by ring]
          exact ih xs ys hl' _ _
        · exact ih xs ys hl' _ _

/-- One functional's fold of zeros. -/
theorem fold_zip_zero (as : List K) (xs : List E) (hx : ∀ x ∈ xs, x = 0) (c : E) :
    (as.zip xs).foldl (fun acc (a, x) ↦ if a ≠ 0 then acc + ofK a * x else acc) c = c := by
  induction as generalizing xs c with
  | nil => simp
  | cons a as ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      have h0 : x = 0 := hx x (by simp)
      have hx' : ∀ x ∈ xs, x = 0 := fun x' h ↦ hx x' (by simp [h])
      split_ifs
      · rw [h0, mul_zero, add_zero]
        exact ih xs hx' c
      · exact ih xs hx' c

theorem frobenius_add (t s : E) (r : ℕ) :
    (List.range r).map (fun m ↦ sqn (t + s) m) =
      List.zipWith (· + ·) ((List.range r).map fun m ↦ sqn t m) ((List.range r).map fun m ↦ sqn s m) := by
  rw [List.zipWith_map, List.zipWith_self]
  exact List.map_congr_left fun m _ ↦ sqn_add t s m

/-- **`coordinatesAt` is additive in the point.** -/
theorem coordinatesAt_add (t s : E) (F : Array (Array K)) :
    coordinatesAt (t + s) F = List.zipWith (· + ·) (coordinatesAt t F) (coordinatesAt s F) := by
  unfold coordinatesAt
  dsimp only
  rw [List.zipWith_map, List.zipWith_self]
  refine List.map_congr_left fun row _ ↦ ?_
  rw [frobenius_add]
  have h := fold_zip_add row.toList ((List.range F.size).map fun m ↦ sqn t m)
    ((List.range F.size).map fun m ↦ sqn s m) (by simp) 0 0
  rw [add_zero] at h
  exact h

/-- **`coordinatesAt` at zero** is zero. -/
theorem coordinatesAt_zero (F : Array (Array K)) :
    coordinatesAt 0 F = (List.range F.size).map fun _ ↦ (0 : E) := by
  unfold coordinatesAt
  dsimp only
  rw [show (List.range F.size).map (fun _ ↦ (0 : E)) = F.toList.map (fun _ ↦ (0 : E)) by
    apply List.ext_getElem <;> simp]
  refine List.map_congr_left fun row _ ↦ fold_zip_zero _ _ (fun x hx ↦ ?_) 0
  obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx
  exact sqn_zero m

/-! ### The bits of a point -/

/-- **The coordinate functionals read the bits**: if `coordinatesAt (ω_{2^j}) F = e_j` for every `j < r`
(`F` of `r` rows), then `coordinatesAt (ω_i) F` is the bit vector of `i`, `i < 2^r`. -/
theorem coordinatesAt_pointE {r : ℕ} {F : Array (Array K)} (hsize : F.size = r)
    (hbasis : ∀ j < r, coordinatesAt (pointE (2 ^ j)) F =
      (List.range r).map fun l ↦ if l = j then (1 : E) else 0)
    {i : ℕ} (hi : i < 2 ^ r) :
    coordinatesAt (pointE i) F = (List.range r).map fun l ↦ if i.testBit l then (1 : E) else 0 := by
  have key : ∀ n ≤ r, coordinatesAt (pointE (i % 2 ^ n)) F =
      (List.range r).map fun l ↦ if l < n ∧ i.testBit l = true then (1 : E) else 0 := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [pow_zero, Nat.mod_one, pointE_zero, coordinatesAt_zero, hsize]
      simp
    | succ n ih =>
      intro hn
      rw [Nat.mod_pow_succ]
      rcases Nat.mod_two_eq_zero_or_one (i / 2 ^ n) with hb | hb
      · rw [hb, mul_zero, add_zero, ih (by omega)]
        refine List.map_congr_left fun l _ ↦ ?_
        have : l = n → i.testBit l = false := by
          rintro rfl
          rw [Nat.testBit_eq_decide_div_mod_eq, hb]
          rfl
        by_cases hl : l < n
        · simp [hl, show l < n + 1 by omega]
        · by_cases hln : l = n
          · simp [hl, this hln]
          · simp [hl, show ¬ l < n + 1 by omega]
      · have hlt : i % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
        rw [hb, mul_one, add_comm, Heap.add_eq_xor_of_dvd (dvd_refl _) hlt, pointE_xor,
          coordinatesAt_add, hbasis n (by omega), ih (by omega), List.zipWith_map, List.zipWith_self]
        refine List.map_congr_left fun l _ ↦ ?_
        have hbit : i.testBit n = true := by
          rw [Nat.testBit_eq_decide_div_mod_eq, hb]
          rfl
        by_cases hln : l = n
        · subst hln
          simp [hbit]
        · by_cases hl : l < n
          · simp [hln, hl, show l < n + 1 by omega]
          · simp [hln, hl, show ¬ l < n + 1 by omega]
  rw [← Nat.mod_eq_of_lt hi, key r le_rfl, Nat.mod_eq_of_lt hi]
  refine List.map_congr_left fun l hl ↦ ?_
  rw [List.mem_range] at hl
  simp [hl]

/-! ### At the verifier's functionals -/

theorem coordinateFunctionals_size (r : ℕ) : (coordinateFunctionals r).size = r := by
  unfold coordinateFunctionals
  exact Array.size_ofFn

/-- **The hypothesis of `coordinatesAt_pointE` at the verifier's functionals** `coordinateFunctionals r`:
`y_l(ω_{2^j}) = [l = j]` for `j, l < r`. At the reference height `r = 18` it is the Rust's unit test and a
recomputation (see the module docstring), not a kernel proof. -/
def CoordinateFunctionalsBasis (r : ℕ) : Prop :=
  ∀ j < r, coordinatesAt (pointE (2 ^ j)) (coordinateFunctionals r) =
    (List.range r).map fun l ↦ if l = j then (1 : E) else 0

/-- **`coordinatesAt (ω_i) (coordinateFunctionals r)` is the bit vector of `i`**, `i < 2^r`, given the basis
values (`CoordinateFunctionalsBasis r`). -/
theorem coordinatesAt_pointE_of_basis {r : ℕ} (h : CoordinateFunctionalsBasis r) {i : ℕ} (hi : i < 2 ^ r) :
    coordinatesAt (pointE i) (coordinateFunctionals r) =
      (List.range r).map fun l ↦ if i.testBit l then (1 : E) else 0 :=
  coordinatesAt_pointE (coordinateFunctionals_size r) h hi

end UniComplete.Domain

/-- info: 'UniComplete.Domain.coordinatesAt_pointE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.coordinatesAt_pointE

/-- info: 'UniComplete.Domain.coordinatesAt_pointE_of_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Domain.coordinatesAt_pointE_of_basis
