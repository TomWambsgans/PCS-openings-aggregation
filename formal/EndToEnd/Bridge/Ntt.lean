-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import PcsQuotient.Domain
import Completeness.Read

/-!
# The statement's additive transform is the novel-basis evaluation

`PcsQuotient.Domain.values m offset c` (`domain.rs:257-260`) takes the `2^m` novel-basis
coefficients `c` of a polynomial to its values at the points `offset + B(i)` of a coset of the span of
the Cantor basis `β₀ … β_{m−1}` (`betaAt`), one butterfly stage per basis vector, and
`Domain.coefficients` undoes it. Here, for every `m` (no evaluation at any size):

* `values_coefficients_K`, `coefficients_values_K` (and `_E`): on arrays of `2^m` entries the two
  transforms are inverse, at any offset, with no hypothesis on the basis (each stage is undone by its
  inverse stage, in characteristic two);
* `values_getD_K`: entry `p < 2^m` of `values m offset c` is `Σ_j c_j X_j(offset + B(p))`, the
  novel-basis polynomial of `c` (`X_j = ∏_{bit t of j} w_t`, `w_t = S^t`), given that `betaAt` is a
  Cantor basis (`IsCantorBasis`, the statement's own decidable property) and `m ≤ 28`; and that is
  F1's `tablePoly` of the table `b ↦ c[idx b]` at the point (`values_getD_tablePoly`), the point
  being F1's `CantorBasis.point` of the bits of `p` for the basis `cantorOf hB` (`point_eq_cantor`);
* `tablePoly_coefficients`: so the table `coefficients m offset v` holds the polynomial taking the
  value `v[p]` at `offset + B(p)`, for every `p < 2^m`.

The proof runs on sequences (`stageF`, `valuesF`, `coefficientsF`): after the stages `m − 1, …, k`,
each block of `2^k` entries holds the novel-basis coefficients (in `w_0 … w_{k−1}`) of a polynomial
that agrees with the whole one on that block's points (`inv_step`), since on the block's coset
`w_k = λ + s`, `λ` the stage's twiddle (`iterate_point`: `S^k(B(n)) = B(n / 2^k)`).
-/

set_option linter.unusedSectionVars false

open LeanVM.Parameters PcsQuotient.Domain QuotientSecurity Finset

namespace Bridge

/-- `K` has characteristic two (a subfield of `E`). -/
instance instCharPK : CharP K 2 := RingHom.charP (algebraMap K E) (algebraMap K E).injective 2

namespace Ntt

/-! ## One stage, on sequences -/

section Core

variable {M : Type} [CommRing M] [Algebra K M] [CharP M 2]

/-- **Stage `k` of the transform on a sequence**, as `Domain.stage` computes each entry: in the
block of `2^(k+1)` entries holding `p`, the pair at `base` and `base + 2^k`, the twiddle `lam` of the
block. -/
def stageF (fwd : Bool) (lam : ℕ → K) (k : ℕ) (a : ℕ → M) (p : ℕ) : M :=
  let half := 2 ^ k
  let r := p % (2 * half)
  let base := p - r + r % half
  let lo := a base
  let hi := a (base + half)
  let l := algebraMap K M (lam (p / (2 * half)))
  if fwd then (if r < half then lo + l * hi else lo + l * hi + hi)
  else (if r < half then lo + l * (lo + hi) else lo + hi)

theorem two_pow_pos' (k : ℕ) : 0 < 2 * 2 ^ k := by positivity

/-- A stage at the position `r` of block `Q`. -/
theorem stageF_at (fwd : Bool) (lam : ℕ → K) (k : ℕ) (a : ℕ → M) (Q r : ℕ)
    (hr : r < 2 * 2 ^ k) :
    stageF fwd lam k a (2 * 2 ^ k * Q + r) =
      if fwd then
        (if r < 2 ^ k then a (2 * 2 ^ k * Q + r % 2 ^ k) +
            algebraMap K M (lam Q) * a (2 * 2 ^ k * Q + r % 2 ^ k + 2 ^ k)
          else a (2 * 2 ^ k * Q + r % 2 ^ k) +
            algebraMap K M (lam Q) * a (2 * 2 ^ k * Q + r % 2 ^ k + 2 ^ k) +
            a (2 * 2 ^ k * Q + r % 2 ^ k + 2 ^ k))
      else
        (if r < 2 ^ k then a (2 * 2 ^ k * Q + r % 2 ^ k) +
            algebraMap K M (lam Q) *
              (a (2 * 2 ^ k * Q + r % 2 ^ k) + a (2 * 2 ^ k * Q + r % 2 ^ k + 2 ^ k))
          else a (2 * 2 ^ k * Q + r % 2 ^ k) + a (2 * 2 ^ k * Q + r % 2 ^ k + 2 ^ k)) := by
  have hm : (2 * 2 ^ k * Q + r) % (2 * 2 ^ k) = r := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  have hd : (2 * 2 ^ k * Q + r) / (2 * 2 ^ k) = Q := by
    rw [Nat.mul_add_div (two_pow_pos' k), Nat.div_eq_of_lt hr, add_zero]
  have hb : 2 * 2 ^ k * Q + r - r = 2 * 2 ^ k * Q := Nat.add_sub_cancel _ _
  simp only [stageF, hm, hd, hb]

/-- Every position is a position in its block. -/
theorem pos_decomp (k p : ℕ) : 2 * 2 ^ k * (p / (2 * 2 ^ k)) + p % (2 * 2 ^ k) = p :=
  Nat.div_add_mod p _

theorem two_eq_zero_M : (2 : M) = 0 := CharTwo.two_eq_zero

/-- **The inverse stage undoes the stage.** -/
theorem stageF_true_false (lam : ℕ → K) (k : ℕ) (a : ℕ → M) :
    stageF true lam k (stageF false lam k a) = a := by
  funext p
  rw [← pos_decomp k p]
  generalize p / (2 * 2 ^ k) = Q
  have hr : p % (2 * 2 ^ k) < 2 * 2 ^ k := Nat.mod_lt _ (two_pow_pos' k)
  generalize p % (2 * 2 ^ k) = r at hr ⊢
  have hh : 0 < 2 ^ k := by positivity
  have h1 : r % 2 ^ k < 2 * 2 ^ k := by have := Nat.mod_lt r hh; omega
  have h2 : r % 2 ^ k + 2 ^ k < 2 * 2 ^ k := by have := Nat.mod_lt r hh; omega
  have e1 := stageF_at false lam k a Q (r % 2 ^ k) h1
  have e2 := stageF_at false lam k a Q (r % 2 ^ k + 2 ^ k) h2
  rw [stageF_at true lam k _ Q r hr]
  simp only [Nat.mod_mod, Nat.mod_lt r hh, Nat.add_mod_right, Bool.false_eq_true,
    ↓reduceIte] at e1 e2 ⊢
  rw [← add_assoc] at e2
  have hn : ¬ (r % 2 ^ k + 2 ^ k < 2 ^ k) := by omega
  rw [if_neg hn] at e2
  rw [e1, e2]
  have h2' := two_eq_zero_M (M := M)
  by_cases hrh : r < 2 ^ k
  · rw [if_pos hrh, Nat.mod_eq_of_lt hrh]
    linear_combination (algebraMap K M (lam Q) *
      (a (2 * 2 ^ k * Q + r) + a (2 * 2 ^ k * Q + r + 2 ^ k))) * h2'
  · rw [if_neg hrh]
    have hrm : r % 2 ^ k = r - 2 ^ k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have he : 2 * 2 ^ k * Q + r % 2 ^ k + 2 ^ k = 2 * 2 ^ k * Q + r := by rw [hrm]; omega
    rw [he]
    linear_combination (a (2 * 2 ^ k * Q + r % 2 ^ k) + algebraMap K M (lam Q) *
      (a (2 * 2 ^ k * Q + r % 2 ^ k) + a (2 * 2 ^ k * Q + r))) * h2'

/-- **The stage undoes the inverse stage.** -/
theorem stageF_false_true (lam : ℕ → K) (k : ℕ) (a : ℕ → M) :
    stageF false lam k (stageF true lam k a) = a := by
  funext p
  rw [← pos_decomp k p]
  generalize p / (2 * 2 ^ k) = Q
  have hr : p % (2 * 2 ^ k) < 2 * 2 ^ k := Nat.mod_lt _ (two_pow_pos' k)
  generalize p % (2 * 2 ^ k) = r at hr ⊢
  have hh : 0 < 2 ^ k := by positivity
  have h1 : r % 2 ^ k < 2 * 2 ^ k := by have := Nat.mod_lt r hh; omega
  have h2 : r % 2 ^ k + 2 ^ k < 2 * 2 ^ k := by have := Nat.mod_lt r hh; omega
  have e1 := stageF_at true lam k a Q (r % 2 ^ k) h1
  have e2 := stageF_at true lam k a Q (r % 2 ^ k + 2 ^ k) h2
  rw [stageF_at false lam k _ Q r hr]
  simp only [Nat.mod_mod, Nat.mod_lt r hh, Nat.add_mod_right, Bool.false_eq_true,
    ↓reduceIte] at e1 e2 ⊢
  rw [← add_assoc] at e2
  have hn : ¬ (r % 2 ^ k + 2 ^ k < 2 ^ k) := by omega
  rw [if_neg hn] at e2
  rw [e1, e2]
  have h2' := two_eq_zero_M (M := M)
  by_cases hrh : r < 2 ^ k
  · rw [if_pos hrh, Nat.mod_eq_of_lt hrh]
    linear_combination (algebraMap K M (lam Q) *
      (a (2 * 2 ^ k * Q + r) + a (2 * 2 ^ k * Q + r + 2 ^ k) +
        algebraMap K M (lam Q) * a (2 * 2 ^ k * Q + r + 2 ^ k))) * h2'
  · rw [if_neg hrh]
    have hrm : r % 2 ^ k = r - 2 ^ k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have he : 2 * 2 ^ k * Q + r % 2 ^ k + 2 ^ k = 2 * 2 ^ k * Q + r := by rw [hrm]; omega
    rw [he]
    linear_combination (a (2 * 2 ^ k * Q + r % 2 ^ k) + algebraMap K M (lam Q) *
      a (2 * 2 ^ k * Q + r)) * h2'

/-! ## The transforms, on sequences -/

/-- `values` on sequences: the stages `m − 1, …, 0`, stage `k` with the twiddles `lamOf k`. -/
def valuesF (lamOf : ℕ → ℕ → K) (m : ℕ) (c : ℕ → M) : ℕ → M :=
  (List.range m).foldr (fun k a ↦ stageF true (lamOf k) k a) c

/-- `coefficients` on sequences: the inverse stages `0, …, m − 1`. -/
def coefficientsF (lamOf : ℕ → ℕ → K) (m : ℕ) (v : ℕ → M) : ℕ → M :=
  (List.range m).foldl (fun a k ↦ stageF false (lamOf k) k a) v

theorem valuesF_succ (lamOf : ℕ → ℕ → K) (m : ℕ) (c : ℕ → M) :
    valuesF lamOf (m + 1) c = valuesF lamOf m (stageF true (lamOf m) m c) := by
  simp [valuesF, List.range_succ, List.foldr_append]

theorem coefficientsF_succ (lamOf : ℕ → ℕ → K) (m : ℕ) (v : ℕ → M) :
    coefficientsF lamOf (m + 1) v = stageF false (lamOf m) m (coefficientsF lamOf m v) := by
  simp [coefficientsF, List.range_succ, List.foldl_append]

theorem valuesF_coefficientsF (lamOf : ℕ → ℕ → K) :
    ∀ (m : ℕ) (v : ℕ → M), valuesF lamOf m (coefficientsF lamOf m v) = v
  | 0, _ => rfl
  | m + 1, v => by
    rw [valuesF_succ, coefficientsF_succ, stageF_true_false, valuesF_coefficientsF lamOf m v]

theorem coefficientsF_valuesF (lamOf : ℕ → ℕ → K) :
    ∀ (m : ℕ) (c : ℕ → M), coefficientsF lamOf m (valuesF lamOf m c) = c
  | 0, _ => rfl
  | m + 1, c => by
    rw [valuesF_succ, coefficientsF_succ, coefficientsF_valuesF lamOf m, stageF_false_true]

end Core

/-! ## Only the entries below `2^m` matter -/

section Congr

variable {M : Type} [CommRing M] [Algebra K M] [CharP M 2]

/-- A stage `k < m` reads, at a position below `2^m`, only entries below `2^m`. -/
theorem stageF_congr {m k : ℕ} (hk : k < m) (fwd : Bool) (lam : ℕ → K) {a b : ℕ → M}
    (h : ∀ i < 2 ^ m, a i = b i) {p : ℕ} (hp : p < 2 ^ m) :
    stageF fwd lam k a p = stageF fwd lam k b p := by
  have hsplit : 2 ^ m = 2 * 2 ^ k * 2 ^ (m - (k + 1)) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  rw [← pos_decomp k p] at hp ⊢
  generalize p / (2 * 2 ^ k) = Q at hp ⊢
  have hr : p % (2 * 2 ^ k) < 2 * 2 ^ k := Nat.mod_lt _ (two_pow_pos' k)
  generalize p % (2 * 2 ^ k) = r at hr hp ⊢
  have hQ' : Q < 2 ^ (m - (k + 1)) := by
    have : 2 * 2 ^ k * Q < 2 * 2 ^ k * 2 ^ (m - (k + 1)) := by
      rw [← hsplit]; exact lt_of_le_of_lt (Nat.le_add_right _ _) hp
    exact Nat.lt_of_mul_lt_mul_left this
  have hQ : 2 * 2 ^ k * Q + 2 * 2 ^ k ≤ 2 ^ m := by
    rw [hsplit, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hQ'
  have hrm : r % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
  rw [stageF_at fwd lam k a Q r hr, stageF_at fwd lam k b Q r hr]
  generalize 2 * 2 ^ k * Q = X at hQ ⊢
  generalize r % 2 ^ k = y at hrm ⊢
  have hb1 : X + y < 2 ^ m := by omega
  have hb2 : X + y + 2 ^ k < 2 ^ m := by omega
  rw [h _ hb1, h _ hb2]

theorem foldr_congr {m : ℕ} (fwd : Bool) (lamOf : ℕ → ℕ → K) :
    ∀ (l : List ℕ), (∀ k ∈ l, k < m) → ∀ {a b : ℕ → M}, (∀ i < 2 ^ m, a i = b i) →
      ∀ i < 2 ^ m, l.foldr (fun k a ↦ stageF fwd (lamOf k) k a) a i =
        l.foldr (fun k a ↦ stageF fwd (lamOf k) k a) b i
  | [], _, _, _, h => h
  | k :: l, hl, a, b, h => fun i hi ↦ by
    simp only [List.foldr_cons]
    exact stageF_congr (hl k List.mem_cons_self) _ _
      (foldr_congr fwd lamOf l (fun k hk ↦ hl k (List.mem_cons_of_mem _ hk)) h) hi

theorem foldl_congr {m : ℕ} (fwd : Bool) (lamOf : ℕ → ℕ → K) :
    ∀ (l : List ℕ), (∀ k ∈ l, k < m) → ∀ {a b : ℕ → M}, (∀ i < 2 ^ m, a i = b i) →
      ∀ i < 2 ^ m, l.foldl (fun a k ↦ stageF fwd (lamOf k) k a) a i =
        l.foldl (fun a k ↦ stageF fwd (lamOf k) k a) b i
  | [], _, _, _, h => h
  | k :: l, hl, a, b, h => fun i hi ↦ by
    simp only [List.foldl_cons]
    exact foldl_congr fwd lamOf l (fun k hk ↦ hl k (List.mem_cons_of_mem _ hk))
      (fun j hj ↦ stageF_congr (hl k List.mem_cons_self) _ _ h hj) i hi

end Congr

/-! ## The arrays: `Domain.stage`, `values`, `coefficients` -/

/-- The twiddles of stage `k` (`Domain.stage`'s `lams`): `w_k(offset) + B(2j)` for block `j`. -/
def lamAt (od : List K) (k j : ℕ) : K := od.getD k 0 + point (2 * j)

theorem stage_size {M : Type} [Scalable M] (fwd : Bool) (od : List K) (k : ℕ) (a : Array M) :
    (stage fwd od k a).size = a.size := by
  simp [stage]

theorem foldr_stage_size {M : Type} [Scalable M] (fwd : Bool) (od : List K) :
    ∀ (l : List ℕ) (a : Array M), (l.foldr (fun k a ↦ stage fwd od k a) a).size = a.size
  | [], _ => rfl
  | k :: l, a => by rw [List.foldr_cons, stage_size, foldr_stage_size fwd od l a]

theorem foldl_stage_size {M : Type} [Scalable M] (fwd : Bool) (od : List K) :
    ∀ (l : List ℕ) (a : Array M), (l.foldl (fun a k ↦ stage fwd od k a) a).size = a.size
  | [], _ => rfl
  | k :: l, a => by rw [List.foldl_cons, foldl_stage_size fwd od l, stage_size]

/-- `values` keeps the size. -/
theorem values_size {M : Type} [Scalable M] (m : ℕ) (offset : K) (a : Array M) :
    (values m offset a).size = a.size :=
  foldr_stage_size true _ _ a

/-- `coefficients` keeps the size. -/
theorem coefficients_size {M : Type} [Scalable M] (m : ℕ) (offset : K) (a : Array M) :
    (coefficients m offset a).size = a.size :=
  foldl_stage_size false _ _ a

theorem lams_lt (p n k : ℕ) (hp : p < n) : p / (2 * 2 ^ k) < n / (2 * 2 ^ k) + 1 :=
  Nat.lt_succ_of_le (Nat.div_le_div_right hp.le)

/-- **A stage of `K` entries is `stageF`**, below the array's size. -/
theorem stage_getD_K (fwd : Bool) (od : List K) (k : ℕ) (a : Array K) (p : ℕ) (hp : p < a.size) :
    (stage fwd od k a).getD p 0 = stageF fwd (lamAt od k) k (fun i ↦ a.getD i 0) p := by
  simp only [stage, stageF, lamAt, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hp,
    lams_lt p a.size k hp, dite_true, Option.getD_some]
  rfl

/-- **A stage of `E` entries is `stageF`**, below the array's size. -/
theorem stage_getD_E (fwd : Bool) (od : List K) (k : ℕ) (a : Array E) (p : ℕ) (hp : p < a.size) :
    (stage fwd od k a).getD p 0 = stageF fwd (lamAt od k) k (fun i ↦ a.getD i 0) p := by
  simp only [stage, stageF, lamAt, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hp,
    lams_lt p a.size k hp, dite_true, Option.getD_some]
  rfl

/-! ### The folds, for `K` -/

theorem foldr_stage_K (fwd : Bool) (od : List K) {m : ℕ} :
    ∀ (l : List ℕ), (∀ k ∈ l, k < m) → ∀ (c : Array K), c.size = 2 ^ m →
      ∀ p < 2 ^ m, (l.foldr (fun k a ↦ stage fwd od k a) c).getD p 0 =
        l.foldr (fun k a ↦ stageF fwd (lamAt od k) k a) (fun i ↦ c.getD i 0) p
  | [], _, _, _ => fun _ _ ↦ rfl
  | k :: l, hl, c, hc => fun p hp ↦ by
    have hs : (l.foldr (fun k a ↦ stage fwd od k a) c).size = 2 ^ m := by
      rw [foldr_stage_size, hc]
    simp only [List.foldr_cons]
    rw [stage_getD_K _ _ _ _ _ (hs ▸ hp)]
    exact stageF_congr (hl k List.mem_cons_self) _ _
      (foldr_stage_K fwd od l (fun k hk ↦ hl k (List.mem_cons_of_mem _ hk)) c hc) hp

theorem foldl_stage_K (fwd : Bool) (od : List K) {m : ℕ} :
    ∀ (l : List ℕ), (∀ k ∈ l, k < m) → ∀ (c : Array K), c.size = 2 ^ m →
      ∀ p < 2 ^ m, (l.foldl (fun a k ↦ stage fwd od k a) c).getD p 0 =
        l.foldl (fun a k ↦ stageF fwd (lamAt od k) k a) (fun i ↦ c.getD i 0) p
  | [], _, _, _ => fun _ _ ↦ rfl
  | k :: l, hl, c, hc => fun p hp ↦ by
    simp only [List.foldl_cons]
    have hl' : ∀ k ∈ l, k < m := fun k hk ↦ hl k (List.mem_cons_of_mem _ hk)
    rw [foldl_stage_K fwd od l hl' (stage fwd od k c) (by rw [stage_size, hc]) p hp]
    exact foldl_congr fwd (lamAt od) l hl'
      (fun i hi ↦ stage_getD_K fwd od k c i (hc ▸ hi)) p hp

theorem values_getD_K' (m : ℕ) (offset : K) (c : Array K) (hc : c.size = 2 ^ m) (p : ℕ)
    (hp : p < 2 ^ m) :
    (values m offset c).getD p 0 =
      valuesF (lamAt (chain offset m)) m (fun i ↦ c.getD i 0) p :=
  foldr_stage_K true (chain offset m) (List.range m) (fun _ hk ↦ List.mem_range.mp hk) c hc p hp

theorem coefficients_getD_K' (m : ℕ) (offset : K) (v : Array K) (hv : v.size = 2 ^ m) (p : ℕ)
    (hp : p < 2 ^ m) :
    (coefficients m offset v).getD p 0 =
      coefficientsF (lamAt (chain offset m)) m (fun i ↦ v.getD i 0) p :=
  foldl_stage_K false (chain offset m) (List.range m) (fun _ hk ↦ List.mem_range.mp hk) v hv p hp

theorem array_ext_getD_K {a b : Array K} (hs : a.size = b.size)
    (h : ∀ p < a.size, a.getD p 0 = b.getD p 0) : a = b := by
  refine Array.ext hs fun i h1 h2 ↦ ?_
  have := h i h1
  simpa [Array.getD_eq_getD_getElem?, h1, h2] using this

/-- **`values` inverts `coefficients`** on `2^m` entries of `K`, at every offset. -/
theorem values_coefficients_K (m : ℕ) (offset : K) (v : Array K) (hv : v.size = 2 ^ m) :
    values m offset (coefficients m offset v) = v := by
  have hs : (coefficients m offset v).size = 2 ^ m := by rw [coefficients_size, hv]
  refine array_ext_getD_K (by rw [values_size, hs, hv]) fun p hp ↦ ?_
  rw [values_size, hs] at hp
  rw [values_getD_K' m offset _ hs p hp]
  unfold valuesF
  rw [foldr_congr true (lamAt (chain offset m)) (List.range m) (fun _ hk ↦ List.mem_range.mp hk)
      (b := coefficientsF (lamAt (chain offset m)) m (fun i ↦ v.getD i 0))
      (fun i hi ↦ coefficients_getD_K' m offset v hv i hi) p hp]
  exact congrFun (valuesF_coefficientsF _ m _) p

/-- **`coefficients` inverts `values`** on `2^m` entries of `K`, at every offset. -/
theorem coefficients_values_K (m : ℕ) (offset : K) (c : Array K) (hc : c.size = 2 ^ m) :
    coefficients m offset (values m offset c) = c := by
  have hs : (values m offset c).size = 2 ^ m := by rw [values_size, hc]
  refine array_ext_getD_K (by rw [coefficients_size, hs, hc]) fun p hp ↦ ?_
  rw [coefficients_size, hs] at hp
  rw [coefficients_getD_K' m offset _ hs p hp]
  unfold coefficientsF
  rw [foldl_congr false (lamAt (chain offset m)) (List.range m) (fun _ hk ↦ List.mem_range.mp hk)
      (b := valuesF (lamAt (chain offset m)) m (fun i ↦ c.getD i 0))
      (fun i hi ↦ values_getD_K' m offset c hc i hi) p hp]
  exact congrFun (coefficientsF_valuesF _ m _) p

/-! ### The folds, for `E` -/

theorem foldr_stage_E (fwd : Bool) (od : List K) {m : ℕ} :
    ∀ (l : List ℕ), (∀ k ∈ l, k < m) → ∀ (c : Array E), c.size = 2 ^ m →
      ∀ p < 2 ^ m, (l.foldr (fun k a ↦ stage fwd od k a) c).getD p 0 =
        l.foldr (fun k a ↦ stageF fwd (lamAt od k) k a) (fun i ↦ c.getD i 0) p
  | [], _, _, _ => fun _ _ ↦ rfl
  | k :: l, hl, c, hc => fun p hp ↦ by
    have hs : (l.foldr (fun k a ↦ stage fwd od k a) c).size = 2 ^ m := by
      rw [foldr_stage_size, hc]
    simp only [List.foldr_cons]
    rw [stage_getD_E _ _ _ _ _ (hs ▸ hp)]
    exact stageF_congr (hl k List.mem_cons_self) _ _
      (foldr_stage_E fwd od l (fun k hk ↦ hl k (List.mem_cons_of_mem _ hk)) c hc) hp

theorem foldl_stage_E (fwd : Bool) (od : List K) {m : ℕ} :
    ∀ (l : List ℕ), (∀ k ∈ l, k < m) → ∀ (c : Array E), c.size = 2 ^ m →
      ∀ p < 2 ^ m, (l.foldl (fun a k ↦ stage fwd od k a) c).getD p 0 =
        l.foldl (fun a k ↦ stageF fwd (lamAt od k) k a) (fun i ↦ c.getD i 0) p
  | [], _, _, _ => fun _ _ ↦ rfl
  | k :: l, hl, c, hc => fun p hp ↦ by
    simp only [List.foldl_cons]
    have hl' : ∀ k ∈ l, k < m := fun k hk ↦ hl k (List.mem_cons_of_mem _ hk)
    rw [foldl_stage_E fwd od l hl' (stage fwd od k c) (by rw [stage_size, hc]) p hp]
    exact foldl_congr fwd (lamAt od) l hl'
      (fun i hi ↦ stage_getD_E fwd od k c i (hc ▸ hi)) p hp

theorem values_getD_E' (m : ℕ) (offset : K) (c : Array E) (hc : c.size = 2 ^ m) (p : ℕ)
    (hp : p < 2 ^ m) :
    (values m offset c).getD p 0 =
      valuesF (lamAt (chain offset m)) m (fun i ↦ c.getD i 0) p :=
  foldr_stage_E true (chain offset m) (List.range m) (fun _ hk ↦ List.mem_range.mp hk) c hc p hp

theorem coefficients_getD_E' (m : ℕ) (offset : K) (v : Array E) (hv : v.size = 2 ^ m) (p : ℕ)
    (hp : p < 2 ^ m) :
    (coefficients m offset v).getD p 0 =
      coefficientsF (lamAt (chain offset m)) m (fun i ↦ v.getD i 0) p :=
  foldl_stage_E false (chain offset m) (List.range m) (fun _ hk ↦ List.mem_range.mp hk) v hv p hp

theorem array_ext_getD_E {a b : Array E} (hs : a.size = b.size)
    (h : ∀ p < a.size, a.getD p 0 = b.getD p 0) : a = b := by
  refine Array.ext hs fun i h1 h2 ↦ ?_
  have := h i h1
  simpa [Array.getD_eq_getD_getElem?, h1, h2] using this

/-- **`values` inverts `coefficients`** on `2^m` entries of `E`, at every offset. -/
theorem values_coefficients_E (m : ℕ) (offset : K) (v : Array E) (hv : v.size = 2 ^ m) :
    values m offset (coefficients m offset v) = v := by
  have hs : (coefficients m offset v).size = 2 ^ m := by rw [coefficients_size, hv]
  refine array_ext_getD_E (by rw [values_size, hs, hv]) fun p hp ↦ ?_
  rw [values_size, hs] at hp
  rw [values_getD_E' m offset _ hs p hp]
  unfold valuesF
  rw [foldr_congr true (lamAt (chain offset m)) (List.range m) (fun _ hk ↦ List.mem_range.mp hk)
      (b := coefficientsF (lamAt (chain offset m)) m (fun i ↦ v.getD i 0))
      (fun i hi ↦ coefficients_getD_E' m offset v hv i hi) p hp]
  exact congrFun (valuesF_coefficientsF _ m _) p

/-- **`coefficients` inverts `values`** on `2^m` entries of `E`, at every offset. -/
theorem coefficients_values_E (m : ℕ) (offset : K) (c : Array E) (hc : c.size = 2 ^ m) :
    coefficients m offset (values m offset c) = c := by
  have hs : (values m offset c).size = 2 ^ m := by rw [values_size, hc]
  refine array_ext_getD_E (by rw [coefficients_size, hs, hc]) fun p hp ↦ ?_
  rw [coefficients_size, hs] at hp
  rw [coefficients_getD_E' m offset _ hs p hp]
  unfold coefficientsF
  rw [foldl_congr false (lamAt (chain offset m)) (List.range m) (fun _ hk ↦ List.mem_range.mp hk)
      (b := valuesF (lamAt (chain offset m)) m (fun i ↦ c.getD i 0))
      (fun i hi ↦ values_getD_E' m offset c hc i hi) p hp]
  exact congrFun (coefficientsF_valuesF _ m _) p

/-! ## The points, the digits, the Cantor basis -/

/-- **The first `N` vectors of the statement's basis are a Cantor basis**: `β₀ = 1`,
`S(β_{k+1}) = β_k` for `k + 1 < N` (Compose's `IsCantor` at `N = 24`; the statement's own
`IsCantorBasis` gives it for every `N ≤ 28`, `cantorUpTo_of_isCantorBasis`). -/
def CantorUpTo (N : ℕ) : Prop := betaAt 0 = 1 ∧ ∀ k, k + 1 < N → S (betaAt (k + 1)) = betaAt k

theorem cantorUpTo_of_isCantorBasis (hB : IsCantorBasis) {N : ℕ} (hN : N ≤ basisSize) :
    CantorUpTo N :=
  ⟨hB.1, fun k hk ↦ hB.2 ⟨k, by unfold basisSize at hN ⊢; omega⟩⟩

/-- The first `N` vectors of the statement's basis as F1's `CantorBasis`. -/
def cantorOf {N : ℕ} (hB : CantorUpTo N) : CantorBasis K N where
  β := betaAt
  zero := hB.1
  succ k hk := hB.2 k hk

theorem S_eq_sq : (S : K → K) = QuotientSecurity.sq := rfl

theorem foldl_point (n : ℕ) : ∀ N : ℕ,
    (List.range N).foldl (fun acc k ↦ if n.testBit k then acc + betaAt k else acc) 0 =
      ∑ t ∈ range N, if n.testBit t then betaAt t else 0
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_point n N, Finset.sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    split_ifs <;> simp

/-- `B(n)` as a sum over the basis. -/
theorem point_eq_sum (n : ℕ) :
    point n = ∑ t ∈ range basisSize, if n.testBit t then betaAt t else 0 :=
  foldl_point n basisSize

/-- `B(n)` as a sum over the first `N` vectors, for `n < 2^N`. -/
theorem point_eq_sum_of_lt {N n : ℕ} (hN : N ≤ basisSize) (hn : n < 2 ^ N) :
    point n = ∑ t ∈ range N, if n.testBit t then betaAt t else 0 := by
  rw [point_eq_sum]
  have e : range basisSize = range (N + (basisSize - N)) := by congr 1; omega
  rw [e, Finset.sum_range_add]
  have z : ∑ x ∈ range (basisSize - N), (if n.testBit (N + x) then betaAt (N + x) else 0) = 0 :=
    Finset.sum_eq_zero fun t _ ↦ by
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num)
        (by omega)))]
      simp
  rw [z, add_zero]

theorem getLastD_append_singleton {α : Type} (a : α) :
    ∀ (l : List α) (d : α), (l ++ [a]).getLastD d = a
  | [], _ => rfl
  | b :: l, _ => by
    rw [List.cons_append, List.getLastD_cons, getLastD_append_singleton a l b]

theorem chain_foldl (x : K) : ∀ n : ℕ,
    (List.range n).foldl (fun ws _ ↦ ws ++ [S (ws.getLastD x)]) [x] =
      (List.range (n + 1)).map fun i ↦ S^[i] x
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ (n := n), List.foldl_append, chain_foldl x n, List.foldl_cons,
      List.foldl_nil, List.range_succ (n := n + 1), List.map_append, List.map_singleton]
    have hl : ((List.range (n + 1)).map fun i ↦ S^[i] x).getLastD x = S^[n] x := by
      rw [List.range_succ (n := n), List.map_append, List.map_singleton,
        getLastD_append_singleton]
    rw [hl, ← Function.iterate_succ_apply' S n x]

/-- **The offset's digits**: entry `k < count` of `chain x count` is `w_k(x) = S^k(x)`. -/
theorem chain_getD (x : K) {count k : ℕ} (hk : k < count) :
    (chain x count).getD k 0 = S^[k] x := by
  rw [chain, chain_foldl, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hk,
    List.getElem?_map, List.getElem?_range (by omega : k < count + 1)]
  rfl

theorem iterate_betaAt {N : ℕ} (hB : CantorUpTo N) {i : ℕ} (hi : i < N) (k : ℕ) :
    S^[k] (betaAt i) = if k ≤ i then betaAt (i - k) else 0 := by
  rw [S_eq_sq]
  exact (cantorOf hB).iterate k i hi

/-- **`w_k` on the span**: `S^k(B(n)) = B(n / 2^k)` for `n < 2^N` (the Cantor basis' digits
shift). -/
theorem iterate_point {N : ℕ} (hB : CantorUpTo N) (hN : N ≤ basisSize) {n : ℕ} (hn : n < 2 ^ N)
    {k : ℕ} (hk : k ≤ N) : S^[k] (point n) = point (n / 2 ^ k) := by
  have hn' : n / 2 ^ k < 2 ^ N := lt_of_le_of_lt (Nat.div_le_self _ _) hn
  rw [point_eq_sum_of_lt hN hn, point_eq_sum_of_lt hN hn', S_eq_sq, sq_iterate_sum]
  have hterm : ∀ t ∈ range N, QuotientSecurity.sq^[k] (if n.testBit t then betaAt t else 0) =
      if n.testBit t then (if k ≤ t then betaAt (t - k) else 0) else 0 := by
    intro t ht
    split_ifs with h1
    · rw [← S_eq_sq, iterate_betaAt hB (Finset.mem_range.mp ht), if_pos (by assumption)]
    · rw [← S_eq_sq, iterate_betaAt hB (Finset.mem_range.mp ht), if_neg (by assumption)]
    · exact sq_iterate_zero k
  rw [Finset.sum_congr rfl hterm]
  have e1 : range N = range (k + (N - k)) := by congr 1; omega
  have e2 : range N = range ((N - k) + k) := by congr 1; omega
  conv_lhs => rw [e1, Finset.sum_range_add]
  conv_rhs => rw [e2, Finset.sum_range_add]
  have z1 : ∑ x ∈ range k, (if n.testBit x then (if k ≤ x then betaAt (x - k) else 0) else 0) =
      0 :=
    Finset.sum_eq_zero fun t ht ↦ by
      have : ¬ k ≤ t := by have := Finset.mem_range.mp ht; omega
      simp [this]
  have z2 : ∑ x ∈ range k, (if (n / 2 ^ k).testBit (N - k + x) then
      betaAt (N - k + x) else 0) = 0 :=
    Finset.sum_eq_zero fun t _ ↦ by
      rw [Nat.testBit_div_two_pow, Nat.testBit_eq_false_of_lt]
      · simp
      · calc n < 2 ^ N := hn
          _ ≤ 2 ^ (N - k + t + k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [z1, z2, zero_add, add_zero]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [Nat.testBit_div_two_pow, if_pos (by omega : k ≤ k + u), Nat.add_sub_cancel_left,
    add_comm u k]

/-- `B(2H + 1) = B(2H) + 1`. -/
theorem point_two_mul_add_one (h0 : betaAt 0 = 1) (H : ℕ) :
    point (2 * H + 1) = point (2 * H) + 1 := by
  rw [point_eq_sum, point_eq_sum, show basisSize = 27 + 1 from rfl]
  conv_lhs => rw [Finset.sum_range_succ']
  conv_rhs => rw [Finset.sum_range_succ']
  have hs : ∀ i ∈ range 27, (if (2 * H + 1).testBit (i + 1) then betaAt (i + 1) else 0) =
      (if (2 * H).testBit (i + 1) then betaAt (i + 1) else 0) := by
    intro i _
    rw [Nat.testBit_succ, Nat.testBit_succ, show (2 * H + 1) / 2 = (2 * H) / 2 by omega]
  rw [Finset.sum_congr rfl hs]
  have h1 : (2 * H + 1).testBit 0 = true := by simp [Nat.testBit_zero]
  have h1' : (2 * H).testBit 0 = false := by simp [Nat.testBit_zero]
  rw [h1, h1', if_pos rfl, h0]
  simp

/-! ## The novel basis -/

/-- `X_j(x) = ∏_{bit t of j, t < n} w_t(x)`, the novel basis on `n` digits. -/
def X (n j : ℕ) (x : K) : K := ∏ t ∈ range n, if j.testBit t then S^[t] x else 1

theorem X_zero (j : ℕ) (x : K) : X 0 j x = 1 := by simp [X]

theorem X_succ_low {k lo : ℕ} (hlo : lo < 2 ^ k) (x : K) : X (k + 1) lo x = X k lo x := by
  rw [X, Finset.prod_range_succ, Nat.testBit_eq_false_of_lt hlo]
  simp [X]

theorem X_succ_high {k lo : ℕ} (hlo : lo < 2 ^ k) (x : K) :
    X (k + 1) (2 ^ k + lo) x = X k lo x * S^[k] x := by
  rw [X, Finset.prod_range_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt hlo]
  simp only [Bool.not_false, if_true]
  congr 1
  refine Finset.prod_congr rfl fun t ht ↦ ?_
  rw [Nat.testBit_two_pow_add_gt (Finset.mem_range.mp ht)]

section Eval

variable {M : Type} [CommRing M] [Algebra K M] [CharP M 2]

/-- **The novel-basis polynomial of `2^m` coefficients at `x`**: `Σ_j X_j(x) c_j`. -/
def nov (m : ℕ) (c : ℕ → M) (x : K) : M := ∑ j ∈ range (2 ^ m), algebraMap K M (X m j x) * c j

/-- The stages `m − 1, …, k`. -/
def after (lamOf : ℕ → ℕ → K) (m k : ℕ) (c : ℕ → M) : ℕ → M :=
  (List.range' k (m - k)).foldr (fun t a ↦ stageF true (lamOf t) t a) c

theorem after_self (lamOf : ℕ → ℕ → K) (m : ℕ) (c : ℕ → M) : after lamOf m m c = c := by
  simp [after]

theorem after_succ (lamOf : ℕ → ℕ → K) {m k : ℕ} (hk : k < m) (c : ℕ → M) :
    after lamOf m k c = stageF true (lamOf k) k (after lamOf m (k + 1) c) := by
  rw [after, show m - k = (m - (k + 1)) + 1 by omega, List.range'_succ]
  rfl

theorem valuesF_eq_after (lamOf : ℕ → ℕ → K) (m : ℕ) (c : ℕ → M) :
    valuesF lamOf m c = after lamOf m 0 c := by
  rw [valuesF, after, List.range_eq_range', Nat.sub_zero]

/-- The invariant: after the stages `m − 1, …, k`, block `hi` of `2^k` entries holds the
coefficients (on `k` digits) of a polynomial equal to the whole one on the block's points. -/
def Inv (offset : K) (m k : ℕ) (c : ℕ → M) : Prop :=
  ∀ hi i', hi < 2 ^ (m - k) → i' < 2 ^ k →
    ∑ lo ∈ range (2 ^ k), algebraMap K M (X k lo (offset + point (hi * 2 ^ k + i'))) *
        after (lamAt (chain offset m)) m k c (hi * 2 ^ k + lo) =
      nov m c (offset + point (hi * 2 ^ k + i'))

theorem inv_top (offset : K) (m : ℕ) (c : ℕ → M) : Inv offset m m c := by
  intro hi i' hhi _
  have : hi = 0 := by simpa using hhi
  subst this
  simp [after_self, nov]

/-- On a block's coset, `w_k` is the stage's twiddle plus the block's half. -/
theorem iterate_at {m : ℕ} (hB : CantorUpTo m) (offset : K) {k hi i' : ℕ} (hm : m ≤ basisSize)
    (hk : k < m) (hhi : hi < 2 ^ (m - k)) (hi' : i' < 2 ^ k) :
    S^[k] (offset + point (hi * 2 ^ k + i')) =
      lamAt (chain offset m) k (hi / 2) + if hi % 2 = 1 then 1 else 0 := by
  have hn : hi * 2 ^ k + i' < 2 ^ m := by
    calc hi * 2 ^ k + i' < hi * 2 ^ k + 2 ^ k := by omega
      _ = (hi + 1) * 2 ^ k := by ring
      _ ≤ 2 ^ (m - k) * 2 ^ k := Nat.mul_le_mul_right _ hhi
      _ = 2 ^ m := by rw [← pow_add]; congr 1; omega
  rw [S_eq_sq, sq_iterate_add, ← S_eq_sq, iterate_point hB hm hn hk.le, lamAt,
    chain_getD offset hk]
  have hdiv : (hi * 2 ^ k + i') / 2 ^ k = hi := by
    rw [mul_comm, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hi', add_zero]
  rw [hdiv, add_assoc]
  congr 1
  rcases Nat.mod_two_eq_zero_or_one hi with h | h
  · rw [if_neg (by omega), add_zero]
    congr 1; omega
  · rw [if_pos h, ← point_two_mul_add_one hB.1]
    congr 1; omega

/-- **The step**: stage `k` takes the invariant at `k + 1` to the invariant at `k`. -/
theorem inv_step {m : ℕ} (hB : CantorUpTo m) (offset : K) {k : ℕ} (hm : m ≤ basisSize) (hk : k < m)
    (c : ℕ → M) (ih : Inv offset m (k + 1) c) : Inv offset m k c := by
  intro hi i' hhi hi'
  have hdec : hi = 2 * (hi / 2) + hi % 2 := (Nat.div_add_mod hi 2).symm
  have hs : hi % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hP : 2 ^ (m - k) = 2 * 2 ^ (m - (k + 1)) := by
    rw [← pow_succ']; congr 1; omega
  have hH : hi / 2 < 2 ^ (m - (k + 1)) := by omega
  have hsk : hi % 2 * 2 ^ k ≤ 2 ^ k := by
    calc hi % 2 * 2 ^ k ≤ 1 * 2 ^ k := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ k := one_mul _
  have hi'' : hi % 2 * 2 ^ k + i' < 2 ^ (k + 1) := by rw [pow_succ]; omega
  have hnum : hi / 2 * 2 ^ (k + 1) + (hi % 2 * 2 ^ k + i') = hi * 2 ^ k + i' := by
    conv_rhs => rw [hdec]
    ring
  have IH := ih (hi / 2) (hi % 2 * 2 ^ k + i') hH hi''
  rw [hnum] at IH
  rw [← IH]
  have hR : range (2 ^ (k + 1)) = range (2 ^ k + 2 ^ k) := by rw [pow_succ, mul_two]
  rw [hR, Finset.sum_range_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun lo hlo ↦ ?_
  have hlo' : lo < 2 ^ k := Finset.mem_range.mp hlo
  rw [X_succ_low hlo', X_succ_high hlo', map_mul, after_succ _ hk]
  have hpos : hi * 2 ^ k + lo = 2 * 2 ^ k * (hi / 2) + (hi % 2 * 2 ^ k + lo) := by
    conv_lhs => rw [hdec]
    ring
  have hr : hi % 2 * 2 ^ k + lo < 2 * 2 ^ k := by omega
  have hmod : (hi % 2 * 2 ^ k + lo) % 2 ^ k = lo := by
    rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlo']
  have hb : 2 * 2 ^ k * (hi / 2) + lo = hi / 2 * 2 ^ (k + 1) + lo := by ring
  have hb' : 2 * 2 ^ k * (hi / 2) + lo + 2 ^ k = hi / 2 * 2 ^ (k + 1) + (2 ^ k + lo) := by ring
  rw [hpos, stageF_at true _ k _ (hi / 2) _ hr, hmod, hb', hb,
    iterate_at hB offset hm hk hhi hi', if_pos rfl]
  rcases Nat.mod_two_eq_zero_or_one hi with h | h
  · rw [if_pos (by rw [h]; omega), if_neg (by omega)]
    simp only [add_zero]
    ring
  · rw [if_neg (by rw [h]; omega), if_pos h, map_add, map_one]
    ring

theorem inv_all {m : ℕ} (hB : CantorUpTo m) (offset : K) (hm : m ≤ basisSize) (c : ℕ → M) :
    ∀ d ≤ m, Inv offset m (m - d) c
  | 0, _ => by simpa using inv_top offset m c
  | d + 1, hd => by
    have := inv_all hB offset hm c d (by omega)
    rw [show m - d = m - (d + 1) + 1 by omega] at this
    exact inv_step hB offset hm (by omega) c this

/-- **The transform evaluates the novel-basis polynomial**: entry `p < 2^m` of `valuesF` is the
polynomial of `c` at `offset + B(p)`. -/
theorem valuesF_eval {m : ℕ} (hB : CantorUpTo m) (offset : K) (hm : m ≤ basisSize) (c : ℕ → M)
    {p : ℕ} (hp : p < 2 ^ m) :
    valuesF (lamAt (chain offset m)) m c p = nov m c (offset + point p) := by
  have h := inv_all hB offset hm c m le_rfl p 0 (by simpa using hp) (by simp)
  simp only [Nat.sub_self, pow_zero, mul_one, add_zero, Finset.range_one,
    Finset.sum_singleton, X_zero, map_one, one_mul] at h
  rw [valuesF_eq_after, h]

end Eval

/-! ## On arrays, and as F1's tables -/

/-- **Entry `p < 2^m` of `values` is the novel-basis polynomial at `offset + B(p)`** (entries in `K`). -/
theorem values_getD_K {m : ℕ} (hB : CantorUpTo m) (hm : m ≤ basisSize) (offset : K) (c : Array K)
    (hc : c.size = 2 ^ m) {p : ℕ} (hp : p < 2 ^ m) :
    (values m offset c).getD p 0 = ∑ j ∈ range (2 ^ m), X m j (offset + point p) * c.getD j 0 := by
  rw [values_getD_K' m offset c hc p hp, valuesF_eval hB offset hm _ hp, nov]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]

/-- **Entry `p < 2^m` of `values` is the novel-basis polynomial at `offset + B(p)`** (entries in `E`,
the digits in `K`). -/
theorem values_getD_E {m : ℕ} (hB : CantorUpTo m) (hm : m ≤ basisSize) (offset : K) (c : Array E)
    (hc : c.size = 2 ^ m) {p : ℕ} (hp : p < 2 ^ m) :
    (values m offset c).getD p 0 =
      ∑ j ∈ range (2 ^ m), ofK (X m j (offset + point p)) * c.getD j 0 := by
  rw [values_getD_E' m offset c hc p hp, valuesF_eval hB offset hm _ hp, nov]
  rfl

/-- A sum over the first `2^m` numbers is a sum over the cube, a number its bits (`Completeness.idx`). -/
theorem sum_range_eq_sum_cube {m : ℕ} (f : ℕ → K) :
    ∑ j ∈ range (2 ^ m), f j = ∑ b : Fin m → Bool, f (Completeness.idx b) := by
  refine Finset.sum_bij' (fun j _ ↦ Completeness.bitsOf m j) (fun b _ ↦ Completeness.idx b)
    (fun _ _ ↦ Finset.mem_univ _) (fun b _ ↦ Finset.mem_range.mpr (Completeness.idx_lt b))
    (fun j hj ↦ Completeness.idx_bitsOf m j (Finset.mem_range.mp hj))
    (fun b _ ↦ Completeness.bitsOf_idx b) (fun j hj ↦ ?_)
  rw [Completeness.idx_bitsOf m j (Finset.mem_range.mp hj)]

/-- `X_{idx b}` is the product of `b`'s digits, as F1's `digitsEval` weighs entry `b`. -/
theorem X_idx {m : ℕ} (b : Fin m → Bool) (x : K) :
    X m (Completeness.idx b) x = ∏ k : Fin m, if b k then QuotientSecurity.sq^[(k : ℕ)] x else 1 := by
  rw [X, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [Completeness.testBit_idx]
  rfl

/-- **The novel-basis sum is F1's `tablePoly`** of the table `b ↦ c[idx b]`. -/
theorem sum_X_eq_tablePoly {m : ℕ} (c : ℕ → K) (x : K) :
    ∑ j ∈ range (2 ^ m), X m j x * c j =
      (tablePoly (fun b : Fin m → Bool ↦ c (Completeness.idx b))).eval x := by
  rw [tablePoly_eval, digitsEval, sum_range_eq_sum_cube]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [X_idx, mul_comm]

/-- **`values` evaluates F1's table polynomial**: entry `p < 2^m` of `values m offset c` is the
`tablePoly` of the table `b ↦ c[idx b]` at `offset + B(p)`. -/
theorem values_getD_tablePoly {m : ℕ} (hB : CantorUpTo m) (hm : m ≤ basisSize) (offset : K)
    (c : Array K) (hc : c.size = 2 ^ m) {p : ℕ} (hp : p < 2 ^ m) :
    (values m offset c).getD p 0 =
      (tablePoly (fun b : Fin m → Bool ↦ c.getD (Completeness.idx b) 0)).eval (offset + point p) := by
  rw [values_getD_K hB hm offset c hc hp, sum_X_eq_tablePoly]

/-- **`B(p)` is F1's point of `p`'s bits** for the statement's basis. -/
theorem point_eq_cantor {m : ℕ} (hB : CantorUpTo m) (hm : m ≤ basisSize) {p : ℕ} (hp : p < 2 ^ m) :
    point p = (cantorOf hB).point (Completeness.bitsOf m p) := by
  rw [point_eq_sum, CantorBasis.point]
  have e : range basisSize = range (m + (basisSize - m)) := by congr 1; omega
  rw [e, Finset.sum_range_add]
  have z : ∑ x ∈ range (basisSize - m), (if p.testBit (m + x) then betaAt (m + x) else 0) = 0 :=
    Finset.sum_eq_zero fun t _ ↦ by
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hp (Nat.pow_le_pow_right (by norm_num)
        (by omega)))]
      simp
  rw [z, add_zero, ← Fin.sum_univ_eq_sum_range (fun t ↦ if p.testBit t then betaAt t else 0) m]
  rfl

/-- **`coefficients` gives F1's table of the values**: the table `coefficients m offset v` holds the
polynomial whose value at `offset + B(p)` is `v[p]`, for every `p < 2^m`. -/
theorem tablePoly_coefficients {m : ℕ} (hB : CantorUpTo m) (hm : m ≤ basisSize) (offset : K)
    (v : Array K) (hv : v.size = 2 ^ m) {p : ℕ} (hp : p < 2 ^ m) :
    (tablePoly (fun b : Fin m → Bool ↦ (coefficients m offset v).getD (Completeness.idx b) 0)).eval
        (offset + point p) = v.getD p 0 := by
  rw [← values_getD_tablePoly hB hm offset _ (by rw [coefficients_size, hv]) hp,
    values_coefficients_K m offset v hv]

/-- **The same at the Cantor points** (offset `0`): at F1's point of the cube point `x`, the
polynomial of the table `coefficients m 0 v` is `v[idx x]`. -/
theorem tablePoly_coefficients_cantor {m : ℕ} (hB : CantorUpTo m) (hm : m ≤ basisSize)
    (v : Array K) (hv : v.size = 2 ^ m) (x : Fin m → Bool) :
    (tablePoly (fun b : Fin m → Bool ↦ (coefficients m 0 v).getD (Completeness.idx b) 0)).eval
        ((cantorOf hB).point x) = v.getD (Completeness.idx x) 0 := by
  have h := tablePoly_coefficients hB hm 0 v hv (Completeness.idx_lt x)
  rwa [zero_add, point_eq_cantor hB hm (Completeness.idx_lt x), Completeness.bitsOf_idx] at h

end Ntt

end Bridge
