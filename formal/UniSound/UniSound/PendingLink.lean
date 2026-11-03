-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The statement is `Mle.lean`'s
-- `PendingTerminalLink`, the restatement of `formal/FlockSound`'s `matFun_append` / `extFun_append`
-- (branch `lean-flock-sound`) on the batch's tables.
import UniSound.Mle

/-!
# The pending matrices' term at the batch's point: `PendingTerminalLink` proved

The batching sumcheck's `λ³` product is `Gext · Llift` (`Mle.lean`): the pending reduction's summand
`G = Â0 + α B̂0` zero-extended above its `k + 6` variables, and `L ŝ` read on them. At the batch's
point `r` its two folds multiply to the verifier's terminal value times the zero extension:

`foldAll Gext r 0 · foldAll Llift r 0 = (a + α b) L̂(ρ) ŝ(σ) · Π_{j ≥ k+6} (1 + r_j)`,

given `Â0`, `B̂0` at the claim's point are `a`, `b` (`MatrixHolds`). The steps:

* `cubeEq_split`: `eq(r, 2^a v + u) = eq(r, u) eq(r_{≥a}, v)` (low coordinates first);
  `sum_cubeEq`: `Σ_v eq(r, v) = 1` (characteristic two); `cubeEq_bitsE`: on a Boolean point `eq` is
  the indicator;
* `foldAll_lift`, `foldAll_ext`: a table read on the low `R` coordinates folds to its `R`-variable
  sum, a zero-extended one to that times `eq(r_{≥R}, 0)`;
* `multilinearEval_eq_sum`: the verifier's `multilinear_eval` is the multilinear extension of a table
  of `2^n` entries (or of none);
* `sum_mleArr_subst`: summing `eq(r, u) M̂(…, bits(u), …)` over the cube substitutes `r` into the
  multilinear extension `M̂` (`Â0`, `B̂0` at the row and column points).

**The statement needs the pending reduction's shape** (`Pending.Shaped`, a premise of
`PendingTerminalLink`): `multilinear_eval` folds pairs, so it is the multilinear
extension only of a table of exactly `2^n` entries (`[a]` at one variable gives `0`, not `a (1 + r)`);
Flock's pending reduction has the skip's `2^k` Lagrange weights, the `64 = 2^6` slices (or none),
and its row and column points inside `A0`'s `28` variables. Without the premise the statement is
false (a pending reduction with three slices).
-/

namespace UniSound

open LeanVM.Parameters UniStatement Finset

/-! ## `eq` on split cube points -/

theorem two_add_self (x : E) : x + x = 0 := by
  have h : (2 : E) = 0 := CharTwo.two_eq_zero
  linear_combination x * h

/-- `eq(r, 2^a v + u) = eq(r, u) · eq(r_{≥ a}, v)`, `u < 2^a`. -/
theorem cubeEq_split (p : List E) (a b u v : ℕ) (hu : u < 2 ^ a) :
    cubeEq p (a + b) (2 ^ a * v + u) = cubeEq p a u * cubeEq (p.drop a) b v := by
  unfold cubeEq
  rw [Finset.prod_range_add]
  congr 1
  · refine Finset.prod_congr rfl fun k hk => ?_
    rw [Nat.testBit_two_pow_mul_add v hu, ite_eq_left (Finset.mem_range.mp hk)]
  · refine Finset.prod_congr rfl fun j _ => ?_
    have hj : ¬ a + j < a := by omega
    rw [Nat.testBit_two_pow_mul_add v hu, ite_eq_right hj, Nat.add_sub_cancel_left]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- A sum over `m n` points as `n` blocks of `m`. -/
theorem sum_range_mul (m : ℕ) (f : ℕ → E) : ∀ n : ℕ,
    ∑ w ∈ range (m * n), f w = ∑ v ∈ range n, ∑ u ∈ range m, f (m * v + u)
  | 0 => by simp
  | n + 1 => by
    rw [Nat.mul_succ, Finset.sum_range_add, sum_range_mul m f n, Finset.sum_range_succ]

theorem mod_two_pow_split (a u v : ℕ) (hu : u < 2 ^ a) : (2 ^ a * v + u) % 2 ^ a = u := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hu]

theorem div_two_pow_split (a u v : ℕ) (hu : u < 2 ^ a) : (2 ^ a * v + u) / 2 ^ a = v := by
  rw [Nat.mul_add_div (Nat.two_pow_pos a), Nat.div_eq_of_lt hu, add_zero]

/-- **The weights `eq(p, ·)` sum to `1`** over the cube (characteristic two). -/
theorem sum_cubeEq : ∀ (b : ℕ) (p : List E), ∑ v ∈ range (2 ^ b), cubeEq p b v = 1
  | 0, p => by simp [cubeEq]
  | b + 1, p => by
    rw [show b + 1 = 1 + b by omega, pow_add, sum_range_mul]
    have h1 : ∑ u ∈ range (2 ^ 1), cubeEq p 1 u = 1 := by
      simp only [cubeEq, pow_one, Finset.sum_range_succ, Finset.sum_range_zero, Finset.prod_range_one,
        zero_add]
      generalize p.getD 0 0 = x
      have h0 : (0 : ℕ).testBit 0 = false := rfl
      have h1 : (1 : ℕ).testBit 0 = true := rfl
      rw [h0, h1, ite_eq_right (by simp), ite_eq_left rfl]
      linear_combination (CharTwo.two_eq_zero : (2 : E) = 0) * (1 + x)
    have h : ∀ v ∈ range (2 ^ b), ∑ u ∈ range (2 ^ 1), cubeEq p (1 + b) (2 ^ 1 * v + u) =
        cubeEq (p.drop 1) b v := by
      intro v _
      rw [Finset.sum_congr rfl fun u hu => cubeEq_split p 1 b u v (Finset.mem_range.mp hu),
        ← Finset.sum_mul, h1, one_mul]
    rw [Finset.sum_congr rfl h, sum_cubeEq b]

/-- `eq` reads only the first `n` coordinates. -/
theorem cubeEq_take (p : List E) (n x : ℕ) : cubeEq (p.take n) n x = cubeEq p n x := by
  unfold cubeEq
  refine Finset.prod_congr rfl fun k hk => ?_
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left (Finset.mem_range.mp hk)]

theorem cubeEq_append_left (A B : List E) (x : ℕ) :
    cubeEq (A ++ B) A.length x = cubeEq A A.length x := by
  unfold cubeEq
  refine Finset.prod_congr rfl fun k hk => ?_
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (Finset.mem_range.mp hk)]

/-- **`eq` on an appended point**: the first list's coordinates on the low bits. -/
theorem cubeEq_append (A B : List E) (n x : ℕ) (h : A.length ≤ n) :
    cubeEq (A ++ B) n x =
      cubeEq A A.length (x % 2 ^ A.length) * cubeEq B (n - A.length) (x / 2 ^ A.length) := by
  conv_lhs => rw [← Nat.add_sub_cancel' h, ← Nat.div_add_mod x (2 ^ A.length)]
  rw [cubeEq_split _ _ _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos _)), cubeEq_append_left,
    List.drop_left]

/-- `eq(p, 0) = Π_{k<b} (1 + p_k)`, the verifier's zero extension. -/
theorem foldl_range'_mul (g : ℕ → E) : ∀ (s m : ℕ) (c : E),
    (List.range' s m).foldl (fun e j => e * g j) c = c * ∏ j ∈ range m, g (s + j)
  | s, 0, c => by simp
  | s, m + 1, c => by
    rw [List.range'_succ, List.foldl_cons, foldl_range'_mul g (s + 1) m, Finset.prod_range_succ',
      add_zero]
    rw [mul_assoc, mul_comm (g s)]
    congr 2
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [show s + (j + 1) = s + 1 + j by omega]

theorem extension_eq_cubeEq (r : List E) (R : ℕ) :
    (List.range' R (r.length - R)).foldl (fun e j => e * (1 + r.getD j 0)) 1 =
      cubeEq (r.drop R) (r.length - R) 0 := by
  rw [foldl_range'_mul, one_mul]
  unfold cubeEq
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Nat.zero_testBit, Bool.false_eq_true, ite_false, add_zero, List.getD_eq_getElem?_getD,
    List.getElem?_drop]

/-- On a Boolean point `eq` is the indicator. -/
theorem cubeEq_bitsE (m u x : ℕ) (hu : u < 2 ^ m) (hx : x < 2 ^ m) :
    cubeEq (bitsE u m) m x = if u = x then 1 else 0 := by
  have hf : ∀ k ∈ range m, (1 + (bitsE u m).getD k 0 + if x.testBit k then 1 else 0 : E) =
      if u.testBit k = x.testBit k then 1 else 0 := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    simp only [bitsE, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk',
      Option.map_some, Option.getD_some]
    cases u.testBit k <;> cases x.testBit k <;> simp [two_add_self]
  unfold cubeEq
  rw [Finset.prod_congr rfl hf]
  split_ifs with h
  · subst h
    simp
  · obtain ⟨k, hk⟩ : ∃ k, u.testBit k ≠ x.testBit k := by
      by_contra hc
      push Not at hc
      exact h (Nat.eq_of_testBit_eq hc)
    have hkm : k < m := by
      by_contra hkm
      have h2 : 2 ^ m ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)] at hk
      exact hk rfl
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hkm) (by simp [hk])

/-! ## Folds of tables on the low coordinates -/

/-- **A table read on the low `R` coordinates** folds to its `R`-variable sum. -/
theorem foldAll_lift (r : List E) (R : ℕ) (hR : R ≤ r.length) (g : ℕ → E) :
    foldAll (fun u => g (u % 2 ^ R)) r 0 = ∑ u ∈ range (2 ^ R), cubeEq r R u * g u := by
  rw [foldAll_eq_sum]
  obtain ⟨b, hb⟩ : ∃ b, r.length = R + b := ⟨r.length - R, by omega⟩
  simp only [zero_mul, zero_add]
  rw [hb, pow_add, sum_range_mul]
  have h : ∀ v ∈ range (2 ^ b), ∑ u ∈ range (2 ^ R),
      cubeEq r (R + b) (2 ^ R * v + u) * g ((2 ^ R * v + u) % 2 ^ R) =
        (∑ u ∈ range (2 ^ R), cubeEq r R u * g u) * cubeEq (r.drop R) b v := by
    intro v _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu' := Finset.mem_range.mp hu
    rw [cubeEq_split _ _ _ _ _ hu', mod_two_pow_split _ _ _ hu']
    ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, sum_cubeEq, mul_one]

/-- **A table zero-extended above `R` coordinates** folds to its sum times `eq(r_{≥R}, 0)`. -/
theorem foldAll_ext (r : List E) (R : ℕ) (hR : R ≤ r.length) (g : ℕ → E) :
    foldAll (fun u => if u < 2 ^ R then g u else 0) r 0 =
      (∑ u ∈ range (2 ^ R), cubeEq r R u * g u) * cubeEq (r.drop R) (r.length - R) 0 := by
  rw [foldAll_eq_sum]
  obtain ⟨b, hb⟩ : ∃ b, r.length = R + b := ⟨r.length - R, by omega⟩
  simp only [zero_mul, zero_add]
  rw [hb, Nat.add_sub_cancel_left, pow_add, sum_range_mul]
  rw [Finset.sum_eq_single 0]
  · rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu' := Finset.mem_range.mp hu
    rw [cubeEq_split _ _ _ _ _ hu', mul_zero, zero_add, ite_eq_left hu']
    ring
  · intro v _ hv
    refine Finset.sum_eq_zero fun u hu => ?_
    have hle : 2 ^ R ≤ 2 ^ R * v + u := by
      have : 2 ^ R ≤ 2 ^ R * v := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hv)
      omega
    rw [ite_eq_right (show ¬ 2 ^ R * v + u < 2 ^ R by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.two_pow_pos b)) h

/-- **A product of a table on the low `k` bits and one on the next `b`**: the sum splits. -/
theorem sum_split_mul (r : List E) (k b : ℕ) (S T : ℕ → E) :
    ∑ u ∈ range (2 ^ (k + b)), cubeEq r (k + b) u * (S (u % 2 ^ k) * T (u / 2 ^ k)) =
      (∑ x ∈ range (2 ^ k), cubeEq r k x * S x) *
        ∑ y ∈ range (2 ^ b), cubeEq (r.drop k) b y * T y := by
  rw [pow_add, sum_range_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' := Finset.mem_range.mp hx
  rw [cubeEq_split _ _ _ _ _ hx', mod_two_pow_split _ _ _ hx', div_two_pow_split _ _ _ hx']
  ring

/-! ## `multilinear_eval` is the multilinear extension -/

theorem foldOnce_getD (cur : Array E) (r : E) (hev : cur.size % 2 = 0) (i : ℕ) :
    (foldOnce cur r).getD i 0 = foldT (fun j => cur.getD j 0) r i := by
  unfold foldOnce foldT
  by_cases hi : i < cur.size / 2
  · simp [hi]
  · have h1 : cur.size ≤ 2 * i := by omega
    have h2 : ¬ 2 * i < cur.size := by omega
    have h3 : ¬ 2 * i + 1 < cur.size := by omega
    simp [hi, h2, h3]

theorem foldl_foldOnce_getD : ∀ (pt : List E) (arr : Array E),
    (arr.size = 2 ^ pt.length ∨ arr.size = 0) →
      ∀ i, (pt.foldl foldOnce arr).getD i 0 = foldAll (fun j => arr.getD j 0) pt i
  | [], arr, _, i => by simp [foldAll]
  | x :: pt, arr, h, i => by
    have hev : arr.size % 2 = 0 := by
      rcases h with h | h
      · rw [h, List.length_cons, pow_succ]
        simp
      · rw [h]
    have hsz : (foldOnce arr x).size = 2 ^ pt.length ∨ (foldOnce arr x).size = 0 := by
      have e : (foldOnce arr x).size = arr.size / 2 := by simp [foldOnce]
      rcases h with h | h
      · left
        rw [e, h, List.length_cons, pow_succ]
        simp
      · right
        rw [e, h]
    rw [List.foldl_cons, foldl_foldOnce_getD pt (foldOnce arr x) hsz i]
    have hf : (fun j => (foldOnce arr x).getD j 0) = foldT (fun j => arr.getD j 0) x :=
      funext fun j => foldOnce_getD arr x hev j
    rw [hf]
    rfl

/-- **`multilinear_eval` is the multilinear extension** of a table of `2^n` entries, or of none. -/
theorem multilinearEval_eq_sum (l pt : List E) (h : l.length = 2 ^ pt.length ∨ l = []) :
    multilinearEval l pt = ∑ x ∈ range (2 ^ pt.length), cubeEq pt pt.length x * l.getD x 0 := by
  have hs : l.toArray.size = 2 ^ pt.length ∨ l.toArray.size = 0 := by
    rcases h with h | h
    · left
      simpa using h
    · right
      simp [h]
  unfold multilinearEval
  rw [foldl_foldOnce_getD pt l.toArray hs 0, foldAll_eq_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [List.getD_eq_getElem?_getD]

/-! ## Substituting into a multilinear extension -/

theorem length_bitsE (u n : ℕ) : (bitsE u n).length = n := by simp [bitsE]

theorem bitsE_mod_lt (u k : ℕ) : u % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)

theorem sum_mul_ite (s x0 : ℕ) (f : ℕ → E) (c : E) (h : x0 < s) :
    ∑ x ∈ range s, f x * (if x = x0 then c else 0) = f x0 * c := by
  rw [Finset.sum_eq_single x0]
  · rw [ite_eq_left rfl]
  · intro x _ hx
    rw [ite_eq_right hx, mul_zero]
  · intro hx
    exact absurd (Finset.mem_range.mpr h) hx

/-- The cube sum against two indicators picks one point. -/
theorem sum_pick (r : List E) (k b x1 x3 : ℕ) (c2 c4 : E) (h1 : x1 < 2 ^ k) (h3 : x3 < 2 ^ b) :
    ∑ u ∈ range (2 ^ (k + b)), cubeEq r (k + b) u * ((if u % 2 ^ k = x1 then 1 else 0) *
        (c2 * ((if u / 2 ^ k = x3 then 1 else 0) * c4))) =
      cubeEq r k x1 * (c2 * (cubeEq (r.drop k) b x3 * c4)) := by
  have e : ∀ u ∈ range (2 ^ (k + b)), cubeEq r (k + b) u * ((if u % 2 ^ k = x1 then 1 else 0) *
        (c2 * ((if u / 2 ^ k = x3 then 1 else 0) * c4))) =
      cubeEq r (k + b) u * ((fun y => if y = x1 then (1 : E) else 0) (u % 2 ^ k) *
        (fun y => if y = x3 then c2 * c4 else 0) (u / 2 ^ k)) := by
    intro u _
    simp only
    split_ifs <;> ring
  rw [Finset.sum_congr rfl e]
  refine (sum_split_mul r k b (fun y => if y = x1 then (1 : E) else 0)
    (fun y => if y = x3 then c2 * c4 else 0)).trans ?_
  rw [sum_mul_ite _ _ _ _ h1, sum_mul_ite _ _ _ _ h3]
  ring

/-- **Summing `eq(r, u)` against `M̂` at `(bits(u_low), P, bits(u_high), Q)` substitutes `r`**:
`Σ_u eq(r, u) M̂(bits(u mod 2^k), P, bits(u / 2^k), Q) = M̂(r_{<k}, P, r_{k…k+b}, Q)`. -/
theorem sum_mleArr_subst (a : Array K) (n : ℕ) (r : List E) (k b : ℕ) (P Q : List E)
    (hn : k + P.length + b ≤ n) (hr : k + b ≤ r.length) :
    ∑ u ∈ range (2 ^ (k + b)),
        cubeEq r (k + b) u * mleArr a n (bitsE (u % 2 ^ k) k ++ P ++ bitsE (u / 2 ^ k) b ++ Q) =
      mleArr a n (r.take k ++ P ++ (r.drop k).take b ++ Q) := by
  unfold mleArr
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [← mul_assoc, ← Finset.sum_mul]
  congr 1
  -- Split both points' `eq` into their four parts.
  have hsplit : ∀ (A B : List E), A.length = k → B.length = b →
      cubeEq (A ++ P ++ B ++ Q) n x.val =
        cubeEq A k (x.val % 2 ^ k) * (cubeEq P P.length (x.val / 2 ^ k % 2 ^ P.length) *
          (cubeEq B b (x.val / 2 ^ k / 2 ^ P.length % 2 ^ b) *
            cubeEq Q (n - k - P.length - b) (x.val / 2 ^ k / 2 ^ P.length / 2 ^ b))) := by
    intro A B hA hB
    rw [List.append_assoc, List.append_assoc, cubeEq_append _ _ _ _ (by omega), hA,
      cubeEq_append _ _ _ _ (by omega), cubeEq_append _ _ _ _ (by omega), hB]
  have h1 : x.val % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
  have h3 : x.val / 2 ^ k / 2 ^ P.length % 2 ^ b < 2 ^ b := Nat.mod_lt _ (Nat.two_pow_pos b)
  rw [hsplit _ _ (by simp; omega) (by simp; omega), cubeEq_take, cubeEq_take]
  have hterm : ∀ u ∈ range (2 ^ (k + b)),
      cubeEq r (k + b) u * cubeEq (bitsE (u % 2 ^ k) k ++ P ++ bitsE (u / 2 ^ k) b ++ Q) n x.val =
        cubeEq r (k + b) u * ((if u % 2 ^ k = x.val % 2 ^ k then 1 else 0) *
          (cubeEq P P.length (x.val / 2 ^ k % 2 ^ P.length) *
            ((if u / 2 ^ k = x.val / 2 ^ k / 2 ^ P.length % 2 ^ b then 1 else 0) *
              cubeEq Q (n - k - P.length - b) (x.val / 2 ^ k / 2 ^ P.length / 2 ^ b)))) := by
    intro u hu
    have hu' := Finset.mem_range.mp hu
    have hdiv : u / 2 ^ k < 2 ^ b := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k), ← pow_add, add_comm]
      exact hu'
    rw [hsplit _ _ (length_bitsE _ _) (length_bitsE _ _),
      cubeEq_bitsE _ _ _ (bitsE_mod_lt u k) h1, cubeEq_bitsE _ _ _ hdiv h3]
  rw [Finset.sum_congr rfl hterm, sum_pick _ _ _ _ _ _ _ h1 h3]

/-! ## The link -/

/-- **`PendingTerminalLink`** (`Mle.lean`): the batch's `λ³` product at its point is the pending
reduction's terminal times the zero extension, for a pending reduction of Flock's shape. -/
theorem pendingTerminalLink : PendingTerminalLink := by
  intro p r a b hsh hR hM
  have hR' : p.k + Flock.packing ≤ r.length := hR
  obtain ⟨hskip, hsl, hpt⟩ := hsh
  -- The two points the claim and the terminal read.
  have hrho : (r.take p.rounds).take p.k = r.take p.k := by
    rw [List.take_take]
    congr 1
    simp [Flock.Pending.rounds]
  have hsigma : (r.take p.rounds).drop p.k = (r.drop p.k).take Flock.packing := by
    rw [List.drop_take]
    congr 1
    simp [Flock.Pending.rounds]
  -- `G`'s fold.
  have hG : foldAll (Pending.Gext p) r 0 =
      (a + p.alpha * b) * cubeEq (r.drop p.rounds) (r.length - p.rounds) 0 := by
    have e : Pending.Gext p = fun u => if u < 2 ^ p.rounds then Pending.G p u else 0 := rfl
    rw [e, foldAll_ext r p.rounds hR]
    congr 1
    obtain ⟨hA, hB⟩ := hM
    simp only [Flock.Pending.matrixClaim, hrho, hsigma] at hA hB
    have hn : p.k + (p.rowLow ++ p.chiIn).length + Flock.packing ≤ matrixVars := hpt
    have hsA := sum_mleArr_subst (flockMatrixStack true) matrixVars r p.k Flock.packing
      (p.rowLow ++ p.chiIn) p.chiInPrime hn hR'
    have hsB := sum_mleArr_subst (flockMatrixStack false) matrixVars r p.k Flock.packing
      (p.rowLow ++ p.chiIn) p.chiInPrime hn hR'
    simp only [← List.append_assoc] at hsA hsB
    rw [hA] at hsA
    rw [hB] at hsB
    simp only [Pending.G]
    rw [show p.rounds = p.k + Flock.packing from rfl, ← hsA, ← hsB, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  -- `L`'s fold.
  have hL : foldAll (Pending.Llift p) r 0 =
      p.skipAt r * multilinearEval (p.slices.getD []) ((r.take p.rounds).drop p.k) := by
    have e : Pending.Llift p = fun u => Pending.L p (u % 2 ^ p.rounds) := rfl
    rw [e, foldAll_lift r p.rounds hR]
    have eL : ∀ u, Pending.L p u =
        (fun x => if p.k > 0 then p.skipWeights.getD x 0 else 1) (u % 2 ^ p.k) *
          (fun y => (p.slices.getD []).getD y 0) (u / 2 ^ p.k) := fun u => rfl
    simp only [eL]
    rw [show p.rounds = p.k + Flock.packing from rfl]
    refine (sum_split_mul r p.k Flock.packing (fun x => if p.k > 0 then p.skipWeights.getD x 0 else 1)
      (fun y => (p.slices.getD []).getD y 0)).trans ?_
    congr 1
    · unfold Flock.Pending.skipAt
      split_ifs with hk
      · rw [hrho, multilinearEval_eq_sum _ _ (Or.inl (by rw [hskip hk]; simp; omega))]
        have hl : (r.take p.k).length = p.k := by simp; omega
        rw [hl]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [cubeEq_take]
      · simp only [Nat.not_lt, Nat.le_zero] at hk
        rw [hk]
        simp [cubeEq]
    · rw [show (r.take (p.k + Flock.packing)).drop p.k = (r.drop p.k).take Flock.packing from hsigma]
      have hl : ((r.drop p.k).take Flock.packing).length = Flock.packing := by simp; omega
      rw [multilinearEval_eq_sum _ _ (by rw [hl]; exact hsl), hl]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [cubeEq_take]
  rw [hG, hL, extension_eq_cubeEq]
  unfold Flock.Pending.terminal
  simp only
  ring

end UniSound
