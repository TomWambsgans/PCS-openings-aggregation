-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCircuit.Sat

/-!
# What the templates' formulas compute

`Poly.eval` as two sums (`Poly.eval_eq`); `PolyBuilder`'s polynomial as the sum of its terms (`build_eval`, through
`insertTerm`'s XOR of equal terms, characteristic 2), so that a formula the transcription builds (D16v's χ) is read
symbolically (`chiB_eval`); the formulas the checker states as literals (constants, bits, copies, XORs, D units,
`kprep`'s sums, the packings' windows, the `E` units), each evaluated.
-/

namespace RecCircuit

open Primitives

theorem foldl_add {α : Type} (g : α → K) :
    ∀ (L : List α) (init : K), L.foldl (fun acc t => acc + g t) init = init + (L.map g).sum
  | [], init => by simp
  | t :: L, init => by rw [List.foldl_cons, foldl_add g L, List.map_cons, List.sum_cons]; ring

theorem Poly.eval_eq (p : Poly) (f : ℕ → K) :
    p.eval f = (p.linear.map fun t => t.2 * f t.1).sum + (p.quadratic.map fun t => t.2.2 * f t.1 * f t.2.1).sum := by
  unfold Poly.eval
  rw [foldl_add (fun t : ℕ × ℕ × K => t.2.2 * f t.1 * f t.2.1), foldl_add (fun t : ℕ × K => t.2 * f t.1)]
  ring

theorem ofU64_one : F64.ofU64 1 = 1 := by decide

theorem ofU64_zero : F64.ofU64 0 = 0 := by decide

theorem Ctx.one_eq : Ctx.one = 1 := ofU64_one

/-- `x^i` is the word `1 << i`, `i < 64`. -/
theorem ofU64_shift (i : ℕ) (hi : i < 64) : F64.ofU64 (1 <<< i.toUInt64) = F64.G ^ i := by
  rw [F64.G_pow i hi, F64.ofU64_eq_ofNat]
  congr 1
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_one]
  have : i.toUInt64.toNat % 64 = i := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  rw [this, Nat.one_shiftLeft, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hi)]

/-! ## `PolyBuilder` -/

/-- A term's monomial: `c_a` for a linear key, `c_a c_b` for a quadratic one. -/
def mono (f : ℕ → K) (key : ℕ × ℕ) : K := if key.2 = LINEAR then f key.1 else f key.1 * f key.2

/-- A builder's polynomial: the sum of its terms. -/
def PolyBuilder.sem (p : PolyBuilder) (f : ℕ → K) : K := (p.terms.map fun t => F64.ofU64 t.2 * mono f t.1).sum

theorem insertTerm_sem (f : ℕ → K) (key : ℕ × ℕ) (k : UInt64) :
    ∀ terms : List ((ℕ × ℕ) × UInt64),
      ((PolyBuilder.insertTerm key k terms).map fun t => F64.ofU64 t.2 * mono f t.1).sum =
        (terms.map fun t => F64.ofU64 t.2 * mono f t.1).sum + F64.ofU64 k * mono f key
  | [] => by simp [PolyBuilder.insertTerm]
  | (key', v) :: rest => by
    unfold PolyBuilder.insertTerm
    by_cases h : key' = key
    · subst h
      simp only [beq_self_eq_true, ite_true, List.map_cons, List.sum_cons, F64.ofU64_xor]
      ring
    · have hb : (key' == key) = false := by simpa using h
      simp only [hb, Bool.false_eq_true, ite_false]
      by_cases hl : PolyBuilder.keyLt key key' = true
      · simp only [hl, ite_true, List.map_cons, List.sum_cons]; ring
      · simp only [hl, Bool.false_eq_true, ite_false, List.map_cons, List.sum_cons, insertTerm_sem f key k rest]; ring

theorem sem_addLinear (p : PolyBuilder) (c : ℕ) (k : UInt64) (f : ℕ → K) :
    (p.addLinear c k).sem f = p.sem f + F64.ofU64 k * f c := by
  unfold PolyBuilder.addLinear PolyBuilder.sem
  rw [insertTerm_sem]
  simp only [mono, ite_true]

theorem sem_linear (p : PolyBuilder) (c : ℕ) (k : UInt64) (f : ℕ → K) :
    (p.linear c k).sem f = p.sem f + F64.ofU64 k * f c := sem_addLinear p c k f

theorem sem_addQuadratic (p : PolyBuilder) (a b : ℕ) (k : UInt64) (f : ℕ → K) (h : max a b ≠ LINEAR) :
    (p.addQuadratic a b k).sem f = p.sem f + F64.ofU64 k * (f a * f b) := by
  unfold PolyBuilder.addQuadratic PolyBuilder.sem
  rw [insertTerm_sem]
  simp only [mono, h, ite_false]
  have : f (min a b) * f (max a b) = f a * f b := by
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab, max_eq_right hab]
    · rw [min_eq_right hab, max_eq_left hab, mul_comm]
  rw [this]

theorem sem_nil (f : ℕ → K) : (PolyBuilder.mk []).sem f = 0 := by simp [PolyBuilder.sem]

/-- **A built polynomial is its builder's sum of terms.** -/
theorem build_eval (p : PolyBuilder) (f : ℕ → K) : p.build.eval f = p.sem f := by
  rw [Poly.eval_eq]
  unfold PolyBuilder.build PolyBuilder.sem
  generalize p.terms = terms
  induction terms with
  | nil => simp
  | cons t rest ih =>
    obtain ⟨⟨a, b⟩, k⟩ := t
    simp only [List.filterMap_cons, List.map_cons, List.sum_cons]
    by_cases hk : k = 0
    · subst hk
      simp only [beq_self_eq_true, Bool.true_or, ite_true, ofU64_zero, zero_mul, zero_add]
      exact ih
    · have hk' : (k == 0) = false := by simpa using hk
      by_cases hb : b = LINEAR
      · subst hb
        simp only [hk', bne_self_eq_false, Bool.or_false, Bool.false_eq_true, ite_false, beq_self_eq_true,
          Bool.or_true, ite_true, List.map_cons, List.sum_cons]
        simp only [mono] at ih ⊢
        simp only [ite_true]
        linear_combination ih
      · have hb' : (b != LINEAR) = true := by simpa using hb
        have hb'' : (b == LINEAR) = false := by simpa using hb
        simp only [hk', hb', hb'', Bool.or_true, Bool.or_false, Bool.false_eq_true, ite_true, ite_false,
          List.map_cons, List.sum_cons]
        simp only [mono] at ih ⊢
        simp only [hb, ite_false]
        linear_combination ih

/-! ## D16v's χ -/

theorem LINEAR_eq : LINEAR = 255 := rfl

/-- **χ's formula** (`keccak16::chi`): `b_x + b_(x+2) + b_(x+1)·b_(x+2)`, `b_i = c_i + c_(5+i)`. -/
theorem chiB_eval (x : ℕ) (f : ℕ → K) :
    (Builder.chiB x).build.eval f =
      (f x + f (5 + x)) + (f ((x + 2) % 5) + f (5 + (x + 2) % 5)) +
        (f ((x + 1) % 5) + f (5 + (x + 1) % 5)) * (f ((x + 2) % 5) + f (5 + (x + 2) % 5)) := by
  have h1 : (x + 1) % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have h2 : (x + 2) % 5 < 5 := Nat.mod_lt _ (by norm_num)
  rw [build_eval]
  simp only [Builder.chiB]
  rw [sem_addQuadratic _ _ _ _ _ (by rw [LINEAR_eq]; omega), sem_addQuadratic _ _ _ _ _ (by rw [LINEAR_eq]; omega),
    sem_addQuadratic _ _ _ _ _ (by rw [LINEAR_eq]; omega), sem_addQuadratic _ _ _ _ _ (by rw [LINEAR_eq]; omega),
    sem_linear, sem_linear, sem_linear, sem_linear, sem_nil, ofU64_one]
  ring

/-- A `k1` partial sum's formula: χ plus the partial sum before. -/
theorem chiB_addLinear_eval (x : ℕ) (f : ℕ → K) :
    ((Builder.chiB x).addLinear (10 + x) 1).build.eval f = (Builder.chiB x).build.eval f + f (10 + x) := by
  rw [build_eval, build_eval, sem_addLinear, ofU64_one, one_mul]

/-! ## The literal formulas -/

namespace Ctx

theorem eval_spare (f : ℕ → K) : sparePoly.eval f = 0 := by simp [Poly.eval_eq, sparePoly]

theorem eval_sq (r : ℕ) (f : ℕ → K) : (sqPoly r).eval f = f r * f r := by
  simp [Poly.eval_eq, sqPoly, one_eq]

theorem eval_copy (r : ℕ) (f : ℕ → K) : (copyPoly r).eval f = f (r - 1) := by
  simp [Poly.eval_eq, copyPoly, one_eq]

theorem eval_xor (r : ℕ) (f : ℕ → K) : (xorPolyL r).eval f = f r + f (r + 1) := by
  simp [Poly.eval_eq, xorPolyL, one_eq]

theorem eval_sum (b : ℕ) (f : ℕ → K) :
    (sumPolyL b).eval f = f b + f (b + 1) + f (b + 2) + f (b + 3) + f (b + 4) := by
  simp [Poly.eval_eq, sumPolyL, one_eq, List.range_succ]; ring

theorem eval_top (b : ℕ) (f : ℕ → K) :
    (topPolyL b).eval f = ((List.range 4).map fun i => F64.G ^ i * f (b + i)).sum := by
  simp only [Poly.eval_eq, topPolyL, List.map_map, List.map_nil, List.sum_nil, add_zero]
  refine congrArg List.sum ?_
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply]
  rw [ofU64_shift i (by simp at hi; omega)]

theorem eval_pack (b : ℕ) (f : ℕ → K) :
    (packPolyL b).eval f = ((List.range 16).map fun i => F64.G ^ i * f (b + i)).sum := by
  simp only [Poly.eval_eq, packPolyL, List.map_map, List.map_nil, List.sum_nil, add_zero]
  refine congrArg List.sum ?_
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply]
  rw [ofU64_shift i (by simp at hi; omega)]

theorem eval_unit_add (b l : ℕ) (f : ℕ → K) : (unitPolyL .add b l).eval f = f (b + l) + f (b + 3 + l) := by
  simp [Poly.eval_eq, unitPolyL, one_eq]

theorem eval_unit_mul (b : ℕ) (f : ℕ → K) :
    (unitPolyL .mul b 0).eval f = f b * f (b + 3) + f (b + 1) * f (b + 5) + f (b + 2) * f (b + 4) ∧
    (unitPolyL .mul b 1).eval f =
      f b * f (b + 4) + f (b + 1) * f (b + 3) + f (b + 1) * f (b + 5) + f (b + 2) * f (b + 4) + f (b + 2) * f (b + 5) ∧
    (unitPolyL .mul b 2).eval f = f b * f (b + 5) + f (b + 1) * f (b + 4) + f (b + 2) * f (b + 3) + f (b + 2) * f (b + 5) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Poly.eval_eq, unitPolyL, one_eq] <;> ring

end Ctx

end RecCircuit
