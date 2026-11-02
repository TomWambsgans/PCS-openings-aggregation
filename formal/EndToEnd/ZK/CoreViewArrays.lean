-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The WHIR prover's arrays (`sumLoop`, `roundC0A`, `roundC2A`, `foldPairsW`, `stackTableA`) are
-- leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0: `Statement/Prover/Whir.lean`).
import ZK.CoreSpec

/-!
# Mumbai's WHIR arrays as the lane rounds' tables

The joint model computes WHIR's lane rounds on tables `LTable E Y k` (lane `b : Fin k → Bool`, lane
variable `0` folded first; `Hiding/Rounds.lean`: `foldFirst`, `msg`, `laneRounds`, `foldAll`), mumbai's
prover on arrays (`foldPairsW`, `roundC0A`, `roundC2A`). Here, for any `k` and any number `N` of
entries:

* **`ArrRep k N A t`**: the array `A` of `2^k · N` entries is the table `t` in WHIR's variable order:
  entry `i` is lane `i mod 2^k` (`bitsOf`, bit `0` first), entry `i / 2^k`;
* `ArrRep.fold`: `foldPairsW r` folds the low bit, the table's lane variable `0` (`foldFirst r`;
  characteristic `2`: `1 - r = 1 + r`);
* `ArrRep.msg`: a round's message of the arrays (`roundC0A`, `roundC2A`) is the table's (`msg`;
  `w₁ - w₀ = w₁ + w₀`), through `sum_lanes`, the sum over lanes and entries as one over the array;
* **`laneRounds_arr`**: the `k` rounds' messages are mumbai's of the arrays folded by the first `j`
  challenges (`roundMsgArr`), and **`foldAll_arr`**: the folded table is the array after all `k` folds;
* **`stack_rep`**: mumbai's stack table of an array of lanes (`stackTableA`, entry `i` the cell
  `i / 64 + 2^(μ-6) · (i mod 64)`) is the joint model's lifted stack (`lift`, lane `l` at the index of
  its bits), the indices past the last lane zero.
-/

open Finset QuotientSecurity.Hiding
open LeanVM.Parameters LeanVM.Prover

namespace PcsQuotient.EndToEnd.Core

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

/-! ## Indices -/

/-- The low `k` bits of an index, bit `0` first: its lane among `2^k`. -/
def bitsOf (k i : ℕ) : Fin k → Bool := fun j => i.testBit j

theorem bitsOf_even (k x : ℕ) : bitsOf (k + 1) (2 * x) = Fin.cons false (bitsOf k x) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · rw [Fin.cons_zero]
    show (2 * x).testBit 0 = false
    rw [Nat.testBit_zero]
    simp
  · rw [Fin.cons_succ]
    show (2 * x).testBit (j + 1) = x.testBit j
    rw [Nat.testBit_succ]
    congr 1
    omega

theorem bitsOf_odd (k x : ℕ) : bitsOf (k + 1) (2 * x + 1) = Fin.cons true (bitsOf k x) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · rw [Fin.cons_zero]
    show (2 * x + 1).testBit 0 = true
    rw [Nat.testBit_zero]
    have h : (2 * x + 1) % 2 = 1 := by omega
    simp [h]
  · rw [Fin.cons_succ]
    show (2 * x + 1).testBit (j + 1) = x.testBit j
    rw [Nat.testBit_succ]
    congr 1
    omega

theorem div_even (k x : ℕ) : 2 * x / 2 ^ (k + 1) = x / 2 ^ k := by
  rw [pow_succ', Nat.mul_div_mul_left _ _ (by norm_num)]

theorem div_odd (k x : ℕ) : (2 * x + 1) / 2 ^ (k + 1) = x / 2 ^ k := by
  rw [pow_succ', ← Nat.div_div_eq_div_mul]
  congr 1
  omega

/-- Two indices below `64` with the same six bits are equal; the bits of `i` are those of
`i mod 64`. -/
theorem bitsOf_eq_iff {l : ℕ} (i : ℕ) (hl : l < 2 ^ 6) : bitsOf 6 l = bitsOf 6 i ↔ l = i % 2 ^ 6 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < 6
    · have h' := congrFun h ⟨j, hj⟩
      simp only [bitsOf] at h'
      rw [h', Nat.testBit_mod_two_pow]
      simp [hj]
    · have h6 : 2 ^ 6 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_eq_false_of_lt (by omega),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) h6)]
  · rintro rfl
    funext j
    show (i % 2 ^ 6).testBit j = i.testBit j
    rw [Nat.testBit_mod_two_pow]
    simp [j.isLt]

/-! ## Sums -/

theorem sum_range_two_mul {M : Type} [AddCommMonoid M] (m : ℕ) (G : ℕ → M) :
    ∑ x ∈ range (2 * m), G x = ∑ x ∈ range m, (G (2 * x) + G (2 * x + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

/-- **The sum over lanes and entries is the sum over the array's indices**, lane `i mod 2^k`, entry
`i / 2^k`. -/
theorem sum_lanes {M : Type} [AddCommMonoid M] :
    ∀ (k N : ℕ) (F : (Fin k → Bool) → ℕ → M),
      ∑ b, ∑ y : Fin N, F b y = ∑ x ∈ range (2 ^ k * N), F (bitsOf k x) (x / 2 ^ k)
  | 0, N, F => by
    calc ∑ b, ∑ y : Fin N, F b y = ∑ y : Fin N, F (bitsOf 0 0) y := by
          rw [Fintype.sum_unique]
          exact sum_congr rfl fun y _ => by congr 1; exact Subsingleton.elim _ _
      _ = ∑ x ∈ range N, F (bitsOf 0 0) x := Fin.sum_univ_eq_sum_range (fun n => F (bitsOf 0 0) n) N
      _ = ∑ x ∈ range (2 ^ 0 * N), F (bitsOf 0 x) (x / 2 ^ 0) := by
          simp only [pow_zero, one_mul, Nat.div_one]
          exact sum_congr rfl fun x _ => by congr 1; exact Subsingleton.elim _ _
  | k + 1, N, F => by
    rw [QuotientSecurity.Hiding.sum_cons (fun b => ∑ y : Fin N, F b y)]
    simp only [← sum_add_distrib]
    rw [sum_lanes k N (fun b n => F (Fin.cons false b) n + F (Fin.cons true b) n),
      show 2 ^ (k + 1) * N = 2 * (2 ^ k * N) by ring, sum_range_two_mul]
    refine sum_congr rfl fun x _ => ?_
    rw [bitsOf_even, bitsOf_odd, div_even, div_odd]

/-- `sumLoop` is a sum. -/
theorem sumLoop_eq (f : ℕ → E) : ∀ (n : ℕ) (acc : E), sumLoop f n acc = acc + ∑ x ∈ range n, f x
  | 0, acc => by simp [sumLoop]
  | n + 1, acc => by
    rw [sumLoop, sumLoop_eq f n, sum_range_succ]
    ring

/-! ## Arrays as tables -/

theorem getD_ofFn {α : Type} {n : ℕ} (f : Fin n → α) {i : ℕ} (h : i < n) (d : α) :
    (Array.ofFn f).getD i d = f ⟨i, h⟩ := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- A table's entry at a natural number, zero past the last. -/
def tAt {k N : ℕ} (t : LTable E (Fin N) k) (b : Fin k → Bool) (n : ℕ) : E :=
  if h : n < N then t b ⟨n, h⟩ else 0

theorem tAt_val {k N : ℕ} (t : LTable E (Fin N) k) (b : Fin k → Bool) (y : Fin N) :
    tAt t b y = t b y := by
  simp [tAt, y.isLt]

/-- **The array `A` is the table `t` in WHIR's variable order**: `2^k · N` entries, entry `i` the
table's at lane `i mod 2^k` (bit `0` first) and entry `i / 2^k`. -/
def ArrRep (k N : ℕ) (A : Array E) (t : LTable E (Fin N) k) : Prop :=
  A.size = 2 ^ k * N ∧ ∀ i < 2 ^ k * N, A.getD i 0 = tAt t (bitsOf k i) (i / 2 ^ k)

theorem size_foldPairsW (r : E) (A : Array E) : (foldPairsW r A).size = A.size / 2 := by
  simp [foldPairsW]

theorem getD_foldPairsW (r : E) (A : Array E) {j : ℕ} (hj : j < A.size / 2) :
    (foldPairsW r A).getD j 0 = A.getD (2 * j) 0 * (1 + r) + A.getD (2 * j + 1) 0 * r := by
  rw [foldPairsW, getD_ofFn _ hj]

theorem two_pow_succ_mul (k N : ℕ) : 2 ^ (k + 1) * N = 2 * (2 ^ k * N) := by ring

/-- **A fold of the array is the fold of the table's lane variable `0`.** -/
theorem ArrRep.fold {k N : ℕ} {A : Array E} {t : LTable E (Fin N) (k + 1)} (h : ArrRep (k + 1) N A t)
    (r : E) : ArrRep k N (foldPairsW r A) (foldFirst r t) := by
  obtain ⟨hs, he⟩ := h
  have hs' : (foldPairsW r A).size = 2 ^ k * N := by
    rw [size_foldPairsW, hs, two_pow_succ_mul]
    omega
  refine ⟨hs', fun j hj => ?_⟩
  have hj2 : j < A.size / 2 := by rw [hs, two_pow_succ_mul]; omega
  have hM := two_pow_succ_mul k N
  rw [getD_foldPairsW r A hj2, he (2 * j) (by omega), he (2 * j + 1) (by omega), bitsOf_even,
    bitsOf_odd, div_even, div_odd]
  have hlt : j / 2 ^ k < N := Nat.div_lt_of_lt_mul hj
  simp only [tAt, dite_eq_left hlt, foldFirst, CharTwo.sub_eq_add]
  ring

/-- **A round's message of the arrays is the tables'.** -/
theorem ArrRep.msg_eq {k N : ℕ} {W f : Array E} {w t : LTable E (Fin N) (k + 1)}
    (hW : ArrRep (k + 1) N W w) (hf : ArrRep (k + 1) N f t) :
    (roundC0A W f, roundC2A W f) = msg w t := by
  obtain ⟨hWs, hWe⟩ := hW
  obtain ⟨hfs, hfe⟩ := hf
  have hM := two_pow_succ_mul k N
  have hmin : min W.size f.size / 2 = 2 ^ k * N := by
    rw [hWs, hfs, min_self, hM]
    omega
  have hx : ∀ x ∈ range (2 ^ k * N), 2 * x < 2 ^ (k + 1) * N ∧ 2 * x + 1 < 2 ^ (k + 1) * N ∧
      x / 2 ^ k < N := by
    intro x hx
    have hx' := mem_range.mp hx
    exact ⟨by omega, by omega, Nat.div_lt_of_lt_mul hx'⟩
  unfold roundC0A roundC2A msg
  rw [hmin, sumLoop_eq, sumLoop_eq, zero_add, zero_add]
  refine Prod.ext ?_ ?_
  · show _ = ∑ b, ∑ y : Fin N, w (Fin.cons false b) y * t (Fin.cons false b) y
    rw [show (∑ b, ∑ y : Fin N, w (Fin.cons false b) y * t (Fin.cons false b) y) =
        ∑ b, ∑ y : Fin N, tAt w (Fin.cons false b) y * tAt t (Fin.cons false b) y by
      simp only [tAt_val],
      sum_lanes k N (fun b n => tAt w (Fin.cons false b) n * tAt t (Fin.cons false b) n)]
    dsimp only
    refine sum_congr rfl fun x hxr => ?_
    obtain ⟨h1, -, -⟩ := hx x hxr
    rw [hWe _ h1, hfe _ h1, bitsOf_even, div_even]
  · show _ = ∑ b, ∑ y : Fin N, (w (Fin.cons true b) y - w (Fin.cons false b) y) *
      (t (Fin.cons true b) y - t (Fin.cons false b) y)
    rw [show (∑ b, ∑ y : Fin N, (w (Fin.cons true b) y - w (Fin.cons false b) y) *
          (t (Fin.cons true b) y - t (Fin.cons false b) y)) =
        ∑ b, ∑ y : Fin N, (tAt w (Fin.cons false b) y + tAt w (Fin.cons true b) y) *
          (tAt t (Fin.cons false b) y + tAt t (Fin.cons true b) y) by
      simp only [tAt_val, CharTwo.sub_eq_add, add_comm],
      sum_lanes k N (fun b n => (tAt w (Fin.cons false b) n + tAt w (Fin.cons true b) n) *
        (tAt t (Fin.cons false b) n + tAt t (Fin.cons true b) n))]
    dsimp only
    refine sum_congr rfl fun x hxr => ?_
    obtain ⟨h1, h2, -⟩ := hx x hxr
    rw [hWe _ h1, hfe _ h1, hWe _ h2, hfe _ h2, bitsOf_even, div_even, bitsOf_odd, div_odd]

/-- **The lane rounds are mumbai's**: round `j`'s message is mumbai's of the arrays after the first
`j` folds. -/
theorem laneRounds_arr {N : ℕ} : ∀ (k : ℕ) (φ : Fin k → E) (W f : Array E)
    (w t : LTable E (Fin N) k), ArrRep k N W w → ArrRep k N f t →
      ∀ j : Fin k, laneRounds k φ w t j = roundMsgArr W f ((List.ofFn φ).take j)
  | 0, _, _, _, _, _, _, _, j => j.elim0
  | k + 1, φ, W, f, w, t, hW, hf, j => by
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [laneRounds, Fin.cons_zero]
      simp only [roundMsgArr, Fin.val_zero, List.take_zero, foldsA, List.foldl_nil]
      exact (hW.msg_eq hf).symm
    · rw [laneRounds, Fin.cons_succ, laneRounds_arr k _ _ _ _ _ (hW.fold (φ 0)) (hf.fold (φ 0)) j]
      simp only [roundMsgArr, foldsA, Fin.val_succ, List.ofFn_succ, List.take_succ_cons,
        List.foldl_cons]
      rfl

/-- **The folded table is the array after all the folds.** -/
theorem foldAll_arr {N : ℕ} : ∀ (k : ℕ) (φ : Fin k → E) (f : Array E) (t : LTable E (Fin N) k),
    ArrRep k N f t → Array.ofFn (foldAll k φ t) = foldsA (List.ofFn φ) f
  | 0, φ, f, t, ⟨hs, he⟩ => by
    simp only [foldAll, List.ofFn_zero, foldsA, List.foldl_nil]
    have hs' : f.size = N := by rw [hs, pow_zero, one_mul]
    apply Array.ext
    · rw [Array.size_ofFn, hs']
    · intro i h1 h2
      have hi : i < N := by simpa using h1
      have hfi := he i (by rw [pow_zero, one_mul]; exact hi)
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h2, Option.getD_some] at hfi
      rw [Array.getElem_ofFn, hfi]
      simp only [tAt, pow_zero, Nat.div_one, dite_eq_left hi]
      congr 1
      exact Subsingleton.elim _ _
  | k + 1, φ, f, t, h => by
    rw [foldAll, foldAll_arr k _ _ _ (h.fold (φ 0))]
    simp only [foldsA, List.ofFn_succ, List.foldl_cons]
    rfl

/-! ## The stack -/

/-- **Mumbai's stack table is the joint model's lifted stack**: for a stack `T` of `nL ≤ 64` lanes
of `N` entries read off the array `A` (lane `l` entry `y` at `l · N + y`), placed at the lane
indices of their bits (`pos`), the stack table of `A` at `2^μ = 64 · N` (`stackTableA`) represents
`lift pos T`. -/
theorem stack_rep {nL N P μ : ℕ} (hnL : nL ≤ 2 ^ 6) (hP : P = N) (hμ : 6 ≤ μ)
    (hμN : 2 ^ (μ - 6) = N) (pos : Fin nL → Fin 6 → Bool) (hpos : ∀ l, pos l = bitsOf 6 l)
    (T : Fin nL → Fin N → K) (A : Array K) (hT : ∀ l y, T l y = A.getD (l * P + y) 0)
    (hA : A.size = nL * P) : ArrRep 6 N (stackTableA μ A) (lift (E := E) pos T) := by
  subst hP
  have hsz : 2 ^ μ = 2 ^ 6 * P := by
    rw [← hμN, ← pow_add]
    congr 1
    omega
  refine ⟨by simp [stackTableA, hsz], fun i hi => ?_⟩
  have hi' : i < 2 ^ μ := by rw [hsz]; exact hi
  rw [stackTableA, getD_ofFn _ hi']
  dsimp only
  have hy : i / 2 ^ 6 < P := Nat.div_lt_of_lt_mul hi
  simp only [tAt, dite_eq_left hy, lift]
  rw [hμN]
  by_cases hli : i % 2 ^ 6 < nL
  · rw [sum_eq_single ⟨i % 2 ^ 6, hli⟩]
    · rw [ite_eq_left (by rw [hpos]; exact (bitsOf_eq_iff i (Nat.mod_lt _ (by norm_num))).mpr rfl), hT]
      show algebraMap K E _ = algebraMap K E _
      congr 2
      dsimp only
      ring
    · intro l _ hne
      rw [ite_eq_right]
      intro he
      apply hne
      rw [hpos] at he
      exact Fin.ext ((bitsOf_eq_iff i (lt_of_lt_of_le l.isLt hnL)).mp he)
    · simp
  · rw [sum_eq_zero]
    · have hle : A.size ≤ i / 2 ^ 6 + P * (i % 2 ^ 6) := by
        rw [hA]
        have : nL * P ≤ (i % 2 ^ 6) * P := Nat.mul_le_mul_right _ (by omega)
        rw [mul_comm P]
        omega
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hle]
      exact map_zero (algebraMap K E)
    · intro l _
      rw [ite_eq_right]
      intro he
      rw [hpos] at he
      have := (bitsOf_eq_iff i (lt_of_lt_of_le l.isLt hnL)).mp he
      have := l.isLt
      omega

end PcsQuotient.EndToEnd.Core
