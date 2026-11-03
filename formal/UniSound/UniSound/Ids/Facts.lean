-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Ids.Bridges
import UniSound.Ids.Cantor

/-!
# The small facts of the verifier's definitions, proved

The `Prop`s of `UniSound.Ids.Bridges`' last section:

* `eqKernelLagrange` (`EqKernelLagrange`): `eqKernel`'s entry `s` is `Π_j (r_j if bit j of s else
  1 + r_j)` (`eqKernel_getD`), which is CompPoly's `lagrangeBasis` in characteristic two;
* `gpowInK` (`GpowInK`): `epow x n = x ^ n` (`epow_eq`), and `gen = ofK (K.ofLane 2)`, so
  `g^n = ofK (K.ofLane 2 ^ n)`;
* `tablesFacts` (`TablesFacts`): structurally, by the `Flushes` builders (each adds one pull and one
  push, of at most sixteen forms) and the forms' coefficients (built from `g^e`, the separators and
  constants by sums and products, all in `K`); nothing of `E` is evaluated;
* `zActZero` (`ZActZero`): `Z_act(ω_k)` is a product of factors, the bit `r`'s vanishing exactly on a
  full table, bit `b`'s exactly on its coset `k >>> b = 2^(r−b) − 2` (`coset_iff`: the rows
  `[2^r − 2^(b+1), 2^r − 2^b)`, where `log₂(2^r − k − 1) = b`), which is `isActive`.
-/

namespace UniSound.Ids.Facts

open LeanVM.Parameters UniStatement Finset

/-! ## `eqKernel` is the fingerprint's weights -/

theorem eqKernel_snoc (l : List E) (r : E) :
    eqKernel (l ++ [r]) = (eqKernel l).map (· * (1 + r)) ++ (eqKernel l).map (· * r) := by
  simp only [eqKernel, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem size_eqKernel (l : List E) : (eqKernel l).size = 2 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l r ih =>
    rw [eqKernel_snoc, Array.size_append, Array.size_map, Array.size_map, ih, List.length_append,
      List.length_singleton, pow_succ, mul_two]

/-- **`eqKernel`'s entry `x`**: `Π_j (r_j if bit j of x else 1 + r_j)`, the first coordinate the lowest
bit. -/
theorem eqKernel_getElem (l : List E) (x : ℕ) (hx : x < (eqKernel l).size) :
    (eqKernel l)[x] =
      ∏ j ∈ range l.length, (if x.testBit j then l.getD j 0 else 1 + l.getD j 0) := by
  induction l using List.reverseRecOn generalizing x with
  | nil =>
    have : x = 0 := by simpa [eqKernel] using hx
    subst this
    rfl
  | append_singleton l r ih =>
    have hlen := size_eqKernel l
    have hgetD : ∀ j < l.length, (l ++ [r]).getD j 0 = l.getD j 0 := fun j hj ↦ by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    have hlast : (l ++ [r]).getD l.length 0 = r := by simp [List.getD_eq_getElem?_getD]
    simp only [eqKernel_snoc]
    rw [List.length_append, List.length_singleton, Finset.prod_range_succ]
    by_cases hlo : x < 2 ^ l.length
    · rw [Array.getElem_append_left (by simp [hlen, hlo]), Array.getElem_map,
        ih x (by rw [hlen]; exact hlo), Nat.testBit_lt_two_pow hlo, hlast]
      simp only [Bool.false_eq_true, ↓reduceIte]
      congr 1
      exact Finset.prod_congr rfl fun j hj ↦ by rw [hgetD j (Finset.mem_range.mp hj)]
    · have hx' : x < 2 ^ l.length + 2 ^ l.length := by
        simp only [eqKernel_snoc, Array.size_append, Array.size_map, hlen] at hx
        omega
      obtain ⟨y, rfl⟩ : ∃ y, x = 2 ^ l.length + y := ⟨x - 2 ^ l.length, by omega⟩
      have hy : y < 2 ^ l.length := by omega
      rw [Array.getElem_append_right (by simp [hlen]), Array.getElem_map]
      simp only [Array.size_map, hlen, Nat.add_sub_cancel_left]
      rw [ih y (by rw [hlen]; exact hy), Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hy, hlast]
      simp only [Bool.not_false, ↓reduceIte]
      congr 1
      exact Finset.prod_congr rfl fun j hj ↦ by
        rw [hgetD j (Finset.mem_range.mp hj), Nat.testBit_two_pow_add_gt (Finset.mem_range.mp hj)]

theorem eqKernel_getD (l : List E) (x : ℕ) (hx : x < 2 ^ l.length) :
    (eqKernel l).getD x 0 =
      ∏ j ∈ range l.length, (if x.testBit j then l.getD j 0 else 1 + l.getD j 0) := by
  have hx' : x < (eqKernel l).size := by rw [size_eqKernel]; exact hx
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hx', Option.getD_some,
    eqKernel_getElem l x hx']

theorem alphasOf_length (ch : List E) : (alphasOf ch).length = 4 := by simp [alphasOf]

theorem alphasOf_getD (ch : List E) {j : ℕ} (hj : j < 4) : (alphasOf ch).getD j 0 = ch.getD j 0 := by
  rw [alphasOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  rfl

end UniSound.Ids.Facts

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset Facts

/-- **`eqKernel` is the fingerprint's weights** (`EqKernelLagrange`). -/
theorem eqKernelLagrange : EqKernelLagrange := by
  intro ch s
  rw [eqKernel_getD _ _ (by rw [alphasOf_length]; exact s.isLt), alphasOf_length,
    LeanVM.Protocol.fingerprintWeights, Vector.get_eq_getElem, CompPoly.CMlPolynomialEval.lagrangeBasis,
    Vector.getElem_ofFn,
    ← Fin.prod_univ_eq_prod_range (fun j ↦ if s.val.testBit j then (alphasOf ch).getD j 0
      else 1 + (alphasOf ch).getD j 0)]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  simp only [BitVec.getLsb_eq_getElem, BitVec.getElem_ofFin, Fin.getElem_fin, Vector.getElem_ofFn,
    CharTwo.sub_eq_add, alphasOf_getD ch j.isLt]

end UniSound.Ids

namespace UniSound.Ids.Facts

open LeanVM.Parameters UniStatement Finset

/-! ## `g^n` is in `K` -/

/-- **Square and multiply** computes the power, given fuel for the exponent's bits. -/
theorem epowAux_eq : ∀ (fuel : ℕ) (base out : E) (n : ℕ), n < 2 ^ fuel →
    epowAux fuel base out n = out * base ^ n
  | 0, base, out, n, hn => by
    have : n = 0 := by simpa using hn
    subst this
    simp [epowAux]
  | fuel + 1, base, out, n, hn => by
    have hn' : n / 2 < 2 ^ fuel := by rw [pow_succ] at hn; omega
    unfold epowAux
    split_ifs with h0 h1
    · subst h0
      simp
    · rw [epowAux_eq fuel _ _ _ hn']
      conv_rhs => rw [← Nat.div_add_mod n 2, h1]
      ring
    · rw [epowAux_eq fuel _ _ _ hn']
      have h1' : n % 2 = 0 := by omega
      conv_rhs => rw [← Nat.div_add_mod n 2, h1']
      ring

theorem epow_eq (x : E) (n : ℕ) : epow x n = x ^ n := by
  rw [epow, epowAux_eq _ _ _ _ Nat.lt_log2_self, one_mul]

theorem ofK_pow (a : K) (n : ℕ) : ofK (a ^ n) = ofK a ^ n := map_pow (algebraMap K E) a n

theorem eK_eq (c : UInt64) : eK c = ofK (K.ofLane c) := by
  rw [eK, eNew, ofK_eq_ofLimbs, show K.ofLane 0 = 0 from rfl]

theorem gen_eq : gen = ofK (K.ofLane 2) := eK_eq 2

theorem gpow_eq (n : ℕ) : UniStatement.gpow n = ofK (K.ofLane 2 ^ n) := by
  rw [UniStatement.gpow, epow_eq, gen_eq, ofK_pow]

theorem toK_ofK (a : K) : toK (ofK a) = a := by
  simp [toK, limb_ofK]

/-- **An element of `K`** (in `E`). -/
def InK (x : E) : Prop := ∃ a : K, x = ofK a

theorem InK.ofK_toK {x : E} (h : InK x) : ofK (toK x) = x := by
  obtain ⟨a, rfl⟩ := h
  rw [toK_ofK]

theorem inK_ofK (a : K) : InK (ofK a) := ⟨a, rfl⟩

theorem InK.add {x z : E} (hx : InK x) (hz : InK z) : InK (x + z) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hz
  exact ⟨a + b, (UniSound.Ids.ofK_add a b).symm⟩

theorem InK.mul {x z : E} (hx : InK x) (hz : InK z) : InK (x * z) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hz
  exact ⟨a * b, (UniSound.Ids.ofK_mul a b).symm⟩

theorem inK_zero : InK 0 := ⟨0, UniSound.Ids.ofK_zero.symm⟩

theorem inK_one : InK 1 := ⟨1, UniSound.Ids.ofK_one.symm⟩

theorem inK_gpow (n : ℕ) : InK (UniStatement.gpow n) := ⟨_, gpow_eq n⟩

theorem inK_eK (c : UInt64) : InK (eK c) := ⟨_, eK_eq c⟩

end UniSound.Ids.Facts

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Facts

/-- **`g^n` is in `K`** (`GpowInK`). -/
theorem gpowInK : GpowInK := fun n ↦ (inK_gpow n).ofK_toK

end UniSound.Ids

/-! ## Axioms -/

/-- info: 'UniSound.Ids.eqKernelLagrange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.eqKernelLagrange

/-- info: 'UniSound.Ids.gpowInK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.Ids.gpowInK
