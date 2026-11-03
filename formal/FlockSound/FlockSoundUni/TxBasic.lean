-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The evaluators are `formal/UniStatement`'s
-- (`UniStatement/Basic.lean`, transcribed from `crates/leanvm_flock_gas`).
import UniSound.FlockInterface
import FlockSound.Main

/-!
# The transcription lemmas' common ground

The verifier's helpers on `E` (`UniStatement/Basic.lean`) as the field's operations, and the bridge
between the code's indexing (a cube point as a number, low bit first; a point as a `List`, read by
`getD`) and the soundness proof's (`Cube n`, points `Fin n → E`):

* `epow_eq`, `sqn_eq`: square and multiply is the power, `k` squarings the `2^k`-th power;
* `eK_eq`, `gen_eq`, `ofLane_xor`: words of `K` as elements of `E`, the generator `x`;
* `ptOf p n`: a list as a point of `E^n` (`ptOf_append`); `sliceOf s`: a list as a table on the cube;
* `cubeFin_val`, `cubeFin_append_val`, `sum_range_eq_sum_cube`: cube points as numbers;
* `cubeEq_cubeFin`: the code's `eq` on a cube point's bits is `eqP` (characteristic two).

Nothing here evaluates `E` in the kernel: every fact is algebra or a rewrite.
-/

namespace FlockSound.Uni

open UniStatement UniSound LeanVM.Parameters Finset

/-! ## Characteristic two -/

theorem two_eq_zero_E : (2 : E) = 0 := CharTwo.two_eq_zero

theorem sub_eq_add_E (a b : E) : a - b = a + b := CharTwo.sub_eq_add a b

theorem add_self_E (a : E) : a + a = 0 := CharTwo.add_self_eq_zero a

/-! ## Powers -/

theorem epowAux_eq : ∀ (fuel : ℕ) (base out : E) (n : ℕ), n < 2 ^ fuel →
    epowAux fuel base out n = out * base ^ n
  | 0, base, out, n, h => by
    have : n = 0 := by simpa using h
    simp [epowAux, this]
  | fuel + 1, base, out, n, h => by
    unfold epowAux
    split_ifs with h0 h1
    · simp [h0]
    · rw [epowAux_eq fuel _ _ _ (by rw [pow_succ] at h; omega), ← pow_two, ← pow_mul, mul_assoc,
        ← pow_succ']
      congr 2
      omega
    · rw [epowAux_eq fuel _ _ _ (by rw [pow_succ] at h; omega), ← pow_two, ← pow_mul]
      congr 2
      omega

/-- **Square and multiply is the power.** -/
theorem epow_eq (x : E) (n : ℕ) : epow x n = x ^ n := by
  rw [epow, epowAux_eq _ _ _ _ (Nat.lt_log2_self), one_mul]

/-- **`k` squarings are the `2^k`-th power.** -/
theorem sqn_eq : ∀ (x : E) (k : ℕ), sqn x k = x ^ 2 ^ k
  | x, 0 => by simp [sqn]
  | x, k + 1 => by
    rw [sqn, sqn_eq (x * x) k, ← pow_two, ← pow_mul, pow_succ']

/-! ## Words -/

theorem ofLane_zero : K.ofLane 0 = 0 := rfl

theorem ofLane_xor (a b : UInt64) : K.ofLane (a ^^^ b) = K.ofLane a + K.ofLane b := by
  simp only [K.ofLane, BF64.add_def, BF64.toBitVec_ofBitVec, UInt64.toBitVec_xor]

theorem eK_eq (c : UInt64) : eK c = ofK (K.ofLane c) := by
  rw [ofK_eq_ofLimbs]
  rfl

theorem gen_eq : gen = ofK g := by
  rw [gen, eK_eq]
  rfl

/-! ## Points and cube points -/

/-- A list as a point of `E^n`: coordinate `i` is entry `i` (`0` past the end). -/
def ptOf (p : List E) (n : ℕ) : Fin n → E := fun i ↦ p.getD i.val 0

/-- A cube point as a number: its bits, low first. -/
theorem cubeFin_val {n : ℕ} (b : Cube n) :
    ((cubeFin n b : Fin (2 ^ n)) : ℕ) = ∑ i : Fin n, (if b i then 1 else 0) * 2 ^ (i : ℕ) := by
  simp only [cubeFin, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.refl_symm,
    Equiv.refl_apply, Function.comp, finFunctionFinEquiv_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  cases b i <;> rfl

/-- A split cube point as a number: the low block, then `2^a` times the high block. -/
theorem cubeFin_append_val {a b : ℕ} (x : Cube a) (y : Cube b) :
    ((cubeFin (a + b) (Fin.append x y) : Fin (2 ^ (a + b))) : ℕ) =
      (cubeFin a x : ℕ) + 2 ^ a * (cubeFin b y : ℕ) := by
  rw [cubeFin_val, cubeFin_val, cubeFin_val, Fin.sum_univ_add, Finset.mul_sum]
  simp only [Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd, pow_add]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- A sum over the numbers below `2^n` is a sum over the cube. -/
theorem sum_range_eq_sum_cube {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ i ∈ range (2 ^ n), f i = ∑ b : Cube n, f (cubeFin n b) := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact (Fintype.sum_equiv (cubeFin n) _ _ fun _ ↦ rfl).symm

/-- **The code's `eq` on a cube point's bits** (`cubeEq`, `Π_k (1 + p_k + x_k)`) is `eqP`. -/
theorem cubeEq_cubeFin (p : List E) {n : ℕ} (b : Cube n) :
    cubeEq p n (cubeFin n b) = eqP (ptOf p n) b := by
  rw [cubeEq, eqP, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [testBit_cubeFin]
  have h2 := two_eq_zero_E
  cases b i
  · simp only [Bool.false_eq_true, ↓reduceIte, add_zero, eq1_false, ptOf, sub_eq_add_E]
  · simp only [↓reduceIte, eq1_true, ptOf]
    linear_combination h2

/-- **A list's entries at a cube point's number** (`s.getD`), as a table on the cube: the slices'
`ŝ(cy)`. -/
def sliceOf (s : List E) {n : ℕ} (cy : Cube n) : E := s.getD (cubeFin n cy) 0

/-- A concatenation of lists is the concatenation of their points. -/
theorem ptOf_append (p q : List E) {a b : ℕ} (hp : p.length = a) :
    ptOf (p ++ q) (a + b) = Fin.append (ptOf p a) (ptOf q b) := by
  funext i
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i
  · simp only [ptOf, Fin.append_left, Fin.val_castAdd]
    rw [List.getD_append _ _ _ _ (by omega)]
  · simp only [ptOf, Fin.append_right, Fin.val_natAdd]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega

end FlockSound.Uni
