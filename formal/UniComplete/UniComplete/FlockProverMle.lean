-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM,
-- branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): `eqEval`, `boolPoint`, `eqEval_cons`, `eqEval_append`,
-- `boolPoint_add`, `boolPoint_two_mul` (`Protocol/Whir/Complete/Tables.lean`), through this repository's
-- `UniComplete.Whir` (`foldl_foldOnce`).
import UniComplete.FlockProver
import UniComplete.Whir

/-!
# Multilinear extensions, as the code computes them

The verifier's `multilinearEval` (folds, low coordinate first), `eqKernel` (the `eq` table) and the prover's sums
(`sumTo`), against sums over the cube with mumbai's kernel `eqB p x = eqEval (boolPoint |p| x) p` (`Π (1 + p_i + x_i)`,
bit `i` of `x` against `p_i`):

* `mle_eq_sum`: `multilinearEval l p = Σ_x l[x] eqB p x` for a table of `2^|p|` entries (`Whir`'s `foldl_foldOnce`);
* `eqKernel_size`, `eqKernel_getD`: `eqKernel p` is the table of `eqB p`;
* `sum_split`, `eqB_append`: the cube of `a + b` coordinates as `x + 2^a y`, `eq` splitting along;
* `sum_eqB`: the partition of unity; `mle_tensor`: a table `T(x + 2^a y) = f(x) g(y)` extends to `f̂(ρ) ĝ(σ)`;
* `sumTo_eq`: the prover's folds are `Finset` sums.

Nothing is evaluated in the kernel: every fact is algebra on arbitrary tables.
-/

namespace UniComplete.FlockP

open UniStatement LeanVM.Parameters Finset
open LeanVM.Protocol.EndToEnd (boolPoint)

/-- **`eq(p, x)`** at the cube point `x` (bit `i` of `x` against `p_i`): `Π_i (1 + p_i + x_i)`. -/
abbrev eqB (p : List E) (x : ℕ) : E := LeanVM.Protocol.Verifier.eqEval (boolPoint p.length x) p

theorem two_eq_zero_E : (2 : E) = 0 := CharTwo.two_eq_zero

theorem add_self_E (a : E) : a + a = 0 := CharTwo.add_self_eq_zero a

/-! ## Sums -/

/-- The prover's sums are `Finset` sums. -/
theorem sumTo_eq (n : ℕ) (f : ℕ → E) : sumTo n f = ∑ i ∈ range n, f i := by
  unfold sumTo
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.foldl_append, ih, sum_range_succ]; rfl

/-- The cube of `a + b` coordinates as `x + 2^a y`. -/
theorem sum_split (a b : ℕ) (f : ℕ → E) :
    ∑ i ∈ range (2 ^ (a + b)), f i = ∑ y ∈ range (2 ^ b), ∑ x ∈ range (2 ^ a), f (x + 2 ^ a * y) := by
  rw [pow_add]
  generalize 2 ^ b = n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]
    congr 1
    refine sum_congr rfl fun x _ ↦ ?_
    congr 1
    ring

/-- Folds of `foldl (· + ·)` over a list's `range`, any start. -/
theorem foldl_add_range (n : ℕ) (f : ℕ → E) (s : E) :
    (List.range n).foldl (fun acc i ↦ acc + f i) s = s + ∑ i ∈ range n, f i := by
  induction n generalizing s with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.foldl_append, ih, sum_range_succ]; simp [add_assoc]

/-! ## `eq` on the cube -/

theorem eqB_cons_even (c : E) (p : List E) (x : ℕ) : eqB (c :: p) (2 * x) = (1 + c) * eqB p x := by
  rw [eqB, List.length_cons, LeanVM.Protocol.Whir.Complete.boolPoint_two_mul,
    LeanVM.Protocol.Whir.Complete.eqEval_cons]
  ring

theorem eqB_cons_odd (c : E) (p : List E) (x : ℕ) : eqB (c :: p) (2 * x + 1) = c * eqB p x := by
  rw [eqB, List.length_cons, LeanVM.Protocol.Whir.Complete.boolPoint_two_mul_add_one,
    LeanVM.Protocol.Whir.Complete.eqEval_cons]
  have h := two_eq_zero_E
  linear_combination (LeanVM.Protocol.Verifier.eqEval (boolPoint p.length x) p) * h

@[simp] theorem eqB_nil (x : ℕ) : eqB [] x = 1 := by
  rw [eqB, List.length_nil, LeanVM.Protocol.Whir.Complete.boolPoint_zero,
    LeanVM.Protocol.Whir.Complete.eqEval_nil_left]

/-- `eq` splits along a concatenation: `eqB (ρ ++ σ) (x + 2^|ρ| y) = eqB ρ x · eqB σ y`. -/
theorem eqB_append (ρ σ : List E) {x : ℕ} (hx : x < 2 ^ ρ.length) (y : ℕ) :
    eqB (ρ ++ σ) (x + 2 ^ ρ.length * y) = eqB ρ x * eqB σ y := by
  rw [eqB, List.length_append, LeanVM.Protocol.Whir.Complete.boolPoint_add _ _ _ _ hx,
    LeanVM.Protocol.Whir.Complete.eqEval_append _ _ _ _ (LeanVM.Protocol.Whir.Complete.length_boolPoint _ _)]

/-- **The partition of unity**: `Σ_x eq(p, x) = 1`. -/
theorem sum_eqB : ∀ p : List E, ∑ x ∈ range (2 ^ p.length), eqB p x = 1
  | [] => by simp
  | c :: p => by
    rw [List.length_cons, pow_succ', UniComplete.sum_range_two_mul]
    simp only [eqB_cons_even, eqB_cons_odd, ← add_mul, ← mul_sum]
    rw [sum_eqB p]
    have h := two_eq_zero_E
    linear_combination h * c

/-! ## `multilinearEval` and `eqKernel` -/

theorem toList_getD {α : Type} (a : Array α) (i : ℕ) (d : α) : a.toList.getD i d = a.getD i d := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

/-- **`multilinearEval` is the sum against `eq`**, for a table of `2^|p|` entries. -/
theorem mle_eq_sum (l : List E) (p : List E) (h : l.length = 2 ^ p.length) :
    multilinearEval l p = ∑ x ∈ range (2 ^ p.length), l.getD x 0 * eqB p x := by
  unfold multilinearEval
  rw [UniComplete.foldl_foldOnce p _ (by simp [h])]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [E2ECompleteness.toArray_getD']

/-- One step of `eqKernel`. -/
def eqStep (out : Array E) (r : E) : Array E := out.map (· * (1 + r)) ++ out.map (· * r)

theorem eqKernel_eq (p : List E) : eqKernel p = p.foldl eqStep #[1] := rfl

theorem eqStep_size (out : Array E) (r : E) : (eqStep out r).size = 2 * out.size := by
  simp [eqStep]; ring

theorem eqStep_getD_low (out : Array E) (r : E) {i : ℕ} (hi : i < out.size) :
    (eqStep out r).getD i 0 = out.getD i 0 * (1 + r) := by
  have h1 : i < (out.map (· * (1 + r))).size := by simpa using hi
  unfold eqStep
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_left h1, Array.getElem?_map,
    Array.getElem?_eq_getElem hi, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  rfl

theorem eqStep_getD_high (out : Array E) (r : E) {i : ℕ} (hi : i < out.size) :
    (eqStep out r).getD (i + out.size) 0 = out.getD i 0 * r := by
  have h1 : (out.map (· * (1 + r))).size ≤ i + out.size := by simp
  unfold eqStep
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_right h1, Array.size_map, Nat.add_sub_cancel,
    Array.getElem?_map, Array.getElem?_eq_getElem hi, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  rfl

/-- `eqKernel`'s folds: from a table `f` of `2^n` entries, `p` adds the high coordinates. -/
theorem foldl_eqStep : ∀ (p : List E) (n : ℕ) (out : Array E), out.size = 2 ^ n →
    (p.foldl eqStep out).size = 2 ^ (n + p.length) ∧
      ∀ x < 2 ^ n, ∀ y < 2 ^ p.length, (p.foldl eqStep out).getD (x + 2 ^ n * y) 0 = out.getD x 0 * eqB p y
  | [], n, out, h => by
    refine ⟨by simpa using h, fun x _ y hy ↦ ?_⟩
    have : y = 0 := by simpa using hy
    subst this
    simp
  | r :: p, n, out, h => by
    have h' : (eqStep out r).size = 2 ^ (n + 1) := by rw [eqStep_size, h, pow_succ]; ring
    obtain ⟨ih1, ih2⟩ := foldl_eqStep p (n + 1) (eqStep out r) h'
    refine ⟨by rw [List.foldl_cons, ih1, List.length_cons]; ring_nf, fun x hx y hy ↦ ?_⟩
    rw [List.foldl_cons]
    rw [List.length_cons, pow_succ'] at hy
    obtain ⟨y', b, hb, rfl⟩ : ∃ y' b, b < 2 ∧ y = 2 * y' + b := ⟨y / 2, y % 2, Nat.mod_lt _ (by norm_num),
      (Nat.div_add_mod y 2).symm⟩
    have hy' : y' < 2 ^ p.length := by omega
    have hidx : x + 2 ^ n * (2 * y' + b) = (x + 2 ^ n * b) + 2 ^ (n + 1) * y' := by ring
    have hxb : x + 2 ^ n * b < 2 ^ (n + 1) := by
      rw [pow_succ]; interval_cases b <;> omega
    rw [hidx, ih2 _ hxb _ hy']
    interval_cases b
    · rw [mul_zero, add_zero, eqStep_getD_low _ _ (by omega), add_zero, eqB_cons_even]; ring
    · rw [mul_one, ← h, eqStep_getD_high _ _ (by omega), eqB_cons_odd]; ring

theorem eqKernel_size (p : List E) : (eqKernel p).size = 2 ^ p.length := by
  rw [eqKernel_eq, (foldl_eqStep p 0 #[1] rfl).1, zero_add]

/-- **`eqKernel p` is the table of `eq(p, ·)`.** -/
theorem eqKernel_getD (p : List E) {y : ℕ} (hy : y < 2 ^ p.length) : (eqKernel p).getD y 0 = eqB p y := by
  have := (foldl_eqStep p 0 #[1] rfl).2 0 (by norm_num) y hy
  rw [eqKernel_eq]
  simpa using this

/-! ## Tensor tables -/

/-- **A tensor table extends to the product**: `T(x + 2^a y) = f(x) g(y)` gives `T̂(ρ ++ σ) = f̂(ρ) ĝ(σ)`. -/
theorem mle_tensor (T f g ρ σ : List E) (hT : T.length = 2 ^ (ρ.length + σ.length)) (hf : f.length = 2 ^ ρ.length)
    (hg : g.length = 2 ^ σ.length)
    (h : ∀ x < 2 ^ ρ.length, ∀ y < 2 ^ σ.length, T.getD (x + 2 ^ ρ.length * y) 0 = f.getD x 0 * g.getD y 0) :
    multilinearEval T (ρ ++ σ) = multilinearEval f ρ * multilinearEval g σ := by
  rw [mle_eq_sum T _ (by simpa using hT), mle_eq_sum f _ hf, mle_eq_sum g _ hg, List.length_append, sum_split,
    sum_mul_sum, sum_comm]
  refine sum_congr rfl fun x hx ↦ sum_congr rfl fun y hy ↦ ?_
  rw [h x (mem_range.mp hx) y (mem_range.mp hy), eqB_append _ _ (mem_range.mp hx)]
  ring

/-- A constant table of ones extends to `1`. -/
theorem mle_ones (σ : List E) : multilinearEval (List.replicate (2 ^ σ.length) 1) σ = 1 := by
  rw [mle_eq_sum _ _ (by simp)]
  calc ∑ x ∈ range (2 ^ σ.length), (List.replicate (2 ^ σ.length) (1 : E)).getD x 0 * eqB σ x
      = ∑ x ∈ range (2 ^ σ.length), eqB σ x := sum_congr rfl fun x hx ↦ by
        rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
        simp [mem_range.mp hx]
    _ = 1 := sum_eqB σ

end UniComplete.FlockP
