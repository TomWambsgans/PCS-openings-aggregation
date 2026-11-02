-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Hiding.Sumcheck
import QuotientSecurity.Hiding.Layout

/-!
# The gadget of the hidden layouts: its patterns reach every round value

`crates/quotient/HIDING.md`, "Condition (R) for every challenge: the gadget". The gadget weighs, at
nine entries of every lane's first piece, three patterns: lanes `0` and `31`, lanes `1` and `30`
(pairs complementary in bits `0 .. 4`, on the lower half), and lane `32` (the overflow lane, on the
upper half). Here, for one entry each and with `E`-valued tables:

* `pair_fold`, `pair_halvesDual`, `nd_pair`: a pair's folds are pairs, with independent halves;
* `deployed_nd`: the two lower patterns are nondegenerate at every `φ` with no coordinate in
  `{0, 1}` and `2 φ₀ ≠ 1` (characteristic 2: always);
* `deployed_reach_all`: with the upper pattern against lane `33`, they reach every value of the six
  rounds but the last quadratic coefficient (the step of `HIDING.md` that removes the Frobenius
  twist forgets that coordinate).
-/

namespace QuotientSecurity.Hiding

open Finset

set_option linter.unusedSectionVars false

variable {E : Type} [Field E]

/-- The unit table at lane index `a`. -/
def unitCol {k : ℕ} (a : Fin k → Bool) : Col E k := fun b => if b = a then 1 else 0

/-- `eq` of one bit. -/
def eqb (r : E) (c : Bool) : E := if c then r else 1 - r

theorem eqb_ne_zero {r : E} (h0 : r ≠ 0) (h1 : r ≠ 1) (c : Bool) : eqb r c ≠ 0 := by
  cases c
  · simp only [eqb, Bool.false_eq_true, ite_false]
    exact sub_ne_zero.mpr (Ne.symm h1)
  · simpa [eqb] using h0

theorem cons_eq_iff {k : ℕ} (x : Bool) (b : Fin k → Bool) (a : Fin (k + 1) → Bool) :
    (Fin.cons x b : Fin (k + 1) → Bool) = a ↔ x = a 0 ∧ b = Fin.tail a := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact Fin.cons_self_tail a

theorem colFold_unit {k : ℕ} (r : E) (a : Fin (k + 1) → Bool) :
    colFold r (unitCol a) = eqb r (a 0) • unitCol (Fin.tail a) := by
  funext b
  simp only [colFold, unitCol, Pi.smul_apply, smul_eq_mul, cons_eq_iff]
  by_cases hb : b = Fin.tail a
  · cases h : a 0 <;> simp [hb, h, eqb]
  · simp [hb]

/-- Complement every bit but the last. -/
def flipC {k : ℕ} (a : Fin (k + 1) → Bool) : Fin (k + 1) → Bool :=
  fun i => if i = Fin.last k then a i else !a i

theorem flipC_zero {k : ℕ} (a : Fin (k + 2) → Bool) : flipC a 0 = !a 0 := by
  simp [flipC, Fin.ext_iff]

theorem tail_flipC {k : ℕ} (a : Fin (k + 2) → Bool) : Fin.tail (flipC a) = flipC (Fin.tail a) := by
  funext i
  simp only [Fin.tail, flipC, ← Fin.succ_last, Fin.succ_inj]

theorem flipC_last {k : ℕ} (a : Fin (k + 1) → Bool) : flipC a (Fin.last k) = a (Fin.last k) := by
  simp [flipC]

theorem flipC_ne {k : ℕ} (a : Fin (k + 2) → Bool) : flipC a ≠ a := by
  intro h
  have := congrFun h 0
  rw [flipC_zero] at this
  cases h0 : a 0 <;> simp [h0] at this

/-- A pair of lanes complementary but in the last bit, weighed `d₀` and `d₁`. -/
def pairCol {k : ℕ} (a : Fin (k + 1) → Bool) (d₀ d₁ : E) : Col E (k + 1) :=
  d₀ • unitCol a + d₁ • unitCol (flipC a)

theorem pair_fold {k : ℕ} (r : E) (a : Fin (k + 2) → Bool) (d₀ d₁ : E) :
    colFold r (pairCol a d₀ d₁)
      = pairCol (Fin.tail a) (d₀ * eqb r (a 0)) (d₁ * eqb r (!a 0)) := by
  simp only [pairCol, colFold_add, colFold_smul, colFold_unit, flipC_zero, tail_flipC, smul_smul]

theorem colIp_unit {k : ℕ} (p q : Fin k → Bool) :
    colIp (unitCol (E := E) p) (unitCol q) = if p = q then 1 else 0 := by
  simp only [colIp, unitCol, mul_ite, mul_one, mul_zero]
  rw [sum_eq_single p]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem colIp_smul_left {k : ℕ} (c : E) (w t : Col E k) : colIp (c • w) t = c * colIp w t := by
  simp [colIp, mul_sum, mul_assoc]

theorem colIp_add_left {k : ℕ} (w w' t : Col E k) : colIp (w + w') t = colIp w t + colIp w' t := by
  simp [colIp, add_mul, sum_add_distrib]

theorem half0_pair {k : ℕ} (a : Fin (k + 2) → Bool) (d₀ d₁ : E) :
    half0 (pairCol a d₀ d₁) = (if a 0 then d₁ else d₀) • unitCol (if a 0 then flipC (Fin.tail a) else Fin.tail a) := by
  funext b
  simp only [half0, pairCol, unitCol, Pi.add_apply, Pi.smul_apply, smul_eq_mul, cons_eq_iff,
    flipC_zero, tail_flipC]
  cases h : a 0 <;> simp [h]

theorem half1_pair {k : ℕ} (a : Fin (k + 2) → Bool) (d₀ d₁ : E) :
    half1 (pairCol a d₀ d₁) = (if a 0 then d₀ else d₁) • unitCol (if a 0 then Fin.tail a else flipC (Fin.tail a)) := by
  funext b
  simp only [half1, pairCol, unitCol, Pi.add_apply, Pi.smul_apply, smul_eq_mul, cons_eq_iff,
    flipC_zero, tail_flipC]
  cases h : a 0 <;> simp [h]

theorem lower_unit {n : ℕ} {a : Fin (n + 1) → Bool} (ha : a (Fin.last n) = false) :
    Lower (unitCol (E := E) a) := by
  intro b hb
  have : b ≠ a := fun h => by rw [h, ha] at hb; exact Bool.false_ne_true hb
  simp [unitCol, this]

theorem lower_smul_unit {n : ℕ} (c : E) {a : Fin (n + 1) → Bool} (ha : a (Fin.last n) = false) :
    Lower (c • unitCol (E := E) a) := lower_smul c (lower_unit ha)

/-- **A pair's halves have a dual pair** (two points of the other variables, on the lower half). -/
theorem pair_halvesDual {n : ℕ} (a : Fin (n + 3) → Bool) (ha : a (Fin.last (n + 2)) = false)
    {d₀ d₁ : E} (h₀ : d₀ ≠ 0) (h₁ : d₁ ≠ 0) : HalvesDual (pairCol a d₀ d₁) := by
  have hta : Fin.tail a (Fin.last (n + 1)) = false := by rw [Fin.tail, Fin.succ_last]; exact ha
  have hfta : flipC (Fin.tail a) (Fin.last (n + 1)) = false := by rw [flipC_last]; exact hta
  have hne : flipC (Fin.tail a) ≠ Fin.tail a := flipC_ne _
  rw [HalvesDual, half0_pair, half1_pair]
  cases h : a 0
  · refine ⟨d₀⁻¹ • unitCol (Fin.tail a), d₁⁻¹ • unitCol (flipC (Fin.tail a)),
      lower_smul_unit _ hta, lower_smul_unit _ hfta, ?_, ?_, ?_, ?_⟩ <;>
    simp [colIp_smul_left, colIp_smul, colIp_unit, hne, Ne.symm hne, h₀, h₁]
  · refine ⟨d₁⁻¹ • unitCol (flipC (Fin.tail a)), d₀⁻¹ • unitCol (Fin.tail a),
      lower_smul_unit _ hfta, lower_smul_unit _ hta, ?_, ?_, ?_, ?_⟩ <;>
    simp [colIp_smul_left, colIp_smul, colIp_unit, hne, Ne.symm hne, h₀, h₁]

/-- The condition at the last two rounds for two pairs, on their coefficients folded down to two
variables. -/
def PairBot : (n : ℕ) → (Fin (n + 1) → E) → (Fin (n + 2) → Bool) → (Fin (n + 2) → Bool) → E → E → E → E →
    Prop
  | 0, φ, a, a', d₀, d₁, d₀', d₁' => ND 1 φ (pairCol a d₀ d₁) (pairCol a' d₀' d₁')
  | n + 1, φ, a, a', d₀, d₁, d₀', d₁' => PairBot n (Fin.tail φ) (Fin.tail a) (Fin.tail a')
      (d₀ * eqb (φ 0) (a 0)) (d₁ * eqb (φ 0) (!a 0)) (d₀' * eqb (φ 0) (a' 0)) (d₁' * eqb (φ 0) (!a' 0))

/-- **Two pairs are nondegenerate** given their bottom condition. -/
theorem nd_pair : ∀ (n : ℕ) (φ : Fin (n + 1) → E), (∀ i, φ i ≠ 0 ∧ φ i ≠ 1) →
    ∀ (a a' : Fin (n + 2) → Bool), a (Fin.last (n + 1)) = false → a' (Fin.last (n + 1)) = false →
    ∀ (d₀ d₁ d₀' d₁' : E), d₀ ≠ 0 → d₁ ≠ 0 → d₀' ≠ 0 → d₁' ≠ 0 →
    PairBot n φ a a' d₀ d₁ d₀' d₁' → ND (n + 1) φ (pairCol a d₀ d₁) (pairCol a' d₀' d₁')
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbot => hbot
  | n + 1, φ, hφ, a, a', ha, ha', d₀, d₁, d₀', d₁', h₀, h₁, h₀', h₁', hbot => by
    have hta : Fin.tail a (Fin.last (n + 1)) = false := by rw [Fin.tail, Fin.succ_last]; exact ha
    have hta' : Fin.tail a' (Fin.last (n + 1)) = false := by rw [Fin.tail, Fin.succ_last]; exact ha'
    have he := fun c => eqb_ne_zero (hφ 0).1 (hφ 0).2 c
    refine ⟨pair_halvesDual a ha h₀ h₁, pair_halvesDual a' ha' h₀' h₁', ?_⟩
    rw [pair_fold, pair_fold]
    exact nd_pair n (Fin.tail φ) (fun i => hφ i.succ) _ _ hta hta' _ _ _ _
      (mul_ne_zero h₀ (he _)) (mul_ne_zero h₁ (he _)) (mul_ne_zero h₀' (he _))
      (mul_ne_zero h₁' (he _)) hbot

/-- Lane `l`'s index: its six bits (`laneBits` of `Hiding.Layout`). -/
abbrev lane (l : Fin 64) : Fin 6 → Bool := laneBits l

theorem flipC_lane0 : flipC (lane 0) = lane 31 := by decide
theorem flipC_lane1 : flipC (lane 1) = lane 30 := by decide

/-- The gadget's first pattern: lanes `0` and `31`. -/
def pattern0 : Col E 6 := pairCol (lane 0) 1 1

/-- The second: lanes `1` and `30`. -/
def pattern1 : Col E 6 := pairCol (lane 1) 1 1

/-- **The deployed lower patterns are nondegenerate** at every `φ` with no coordinate in `{0, 1}`
and `2 φ₀ ≠ 1`. -/
theorem deployed_nd (φ : Fin 5 → E) (hφ : ∀ i, φ i ≠ 0 ∧ φ i ≠ 1) (h2 : 2 * φ 0 ≠ 1) :
    ND 5 φ (pattern0 (E := E)) pattern1 := by
  refine nd_pair 4 φ hφ (lane 0) (lane 1) (by decide) (by decide) 1 1 1 1 one_ne_zero one_ne_zero
    one_ne_zero one_ne_zero ?_
  have e : ∀ i, φ i ≠ 0 ∧ 1 - φ i ≠ 0 := fun i => ⟨(hφ i).1, sub_ne_zero.mpr (Ne.symm (hφ i).2)⟩
  have t0 : Fin.tail (Fin.tail (Fin.tail (Fin.tail (lane 0)))) = (Fin.cons false (pt false) : Fin 2 → Bool) := by
    decide
  have t1 : Fin.tail (Fin.tail (Fin.tail (Fin.tail (lane 1)))) = (Fin.cons false (pt false) : Fin 2 → Bool) := by
    decide
  have f00 : flipC (Fin.cons false (pt false) : Fin 2 → Bool) = Fin.cons true (pt false) := by decide
  have ne1 : (Fin.cons true (pt false) : Fin 2 → Bool) ≠ Fin.cons false (pt false) := by decide
  have b00 : lane 0 0 = false := by decide
  have b01 : Fin.tail (lane 0) 0 = false := by decide
  have b02 : Fin.tail (Fin.tail (lane 0)) 0 = false := by decide
  have b03 : Fin.tail (Fin.tail (Fin.tail (lane 0))) 0 = false := by decide
  have b10 : lane 1 0 = true := by decide
  have b11 : Fin.tail (lane 1) 0 = false := by decide
  have b12 : Fin.tail (Fin.tail (lane 1)) 0 = false := by decide
  have b13 : Fin.tail (Fin.tail (Fin.tail (lane 1))) 0 = false := by decide
  have p1 : Fin.tail φ 0 = φ 1 := rfl
  have p2 : Fin.tail (Fin.tail φ) 0 = φ 2 := rfl
  have p3 : Fin.tail (Fin.tail (Fin.tail φ)) 0 = φ 3 := rfl
  simp only [PairBot, ND, pairCol, unitCol, Pi.add_apply, Pi.smul_apply, smul_eq_mul, t0, t1, f00,
    ne1, Ne.symm ne1, b00, b01, b02, b03, b10, b11, b12, b13, p1, p2, p3, ite_true, ite_false, eqb,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, mul_one, mul_zero, add_zero, zero_add, one_mul]
  obtain ⟨e0, e0'⟩ := e 0
  obtain ⟨e1, e1'⟩ := e 1
  obtain ⟨e2, e2'⟩ := e 2
  obtain ⟨e3, e3'⟩ := e 3
  refine ⟨by simp [e0', e1', e2', e3'], fun h => ?_⟩
  have hx : ((1 - φ 1) * (1 - φ 2) * (1 - φ 3) * (φ 1 * φ 2 * φ 3)) * (1 - 2 * φ 0) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp hx with hx | hx
  · simp [e1, e2, e3, e1', e2', e3'] at hx
  · exact h2 (by linear_combination -hx)

/-! ### The upper pattern -/

/-- The product of the first variables' `eq` factors of lane index `a`. -/
def eqProd : (n : ℕ) → (Fin n → E) → (Fin (n + 1) → Bool) → E
  | 0, _, _ => 1
  | n + 1, φ, a => eqb (φ 0) (a 0) * eqProd n (Fin.tail φ) (Fin.tail a)

theorem eqProd_ne_zero : ∀ (n : ℕ) (φ : Fin n → E), (∀ i, φ i ≠ 0 ∧ φ i ≠ 1) →
    ∀ a : Fin (n + 1) → Bool, eqProd n φ a ≠ 0
  | 0, _, _, _ => one_ne_zero
  | n + 1, φ, hφ, _ => mul_ne_zero (eqb_ne_zero (hφ 0).1 (hφ 0).2 _)
      (eqProd_ne_zero n (Fin.tail φ) (fun i => hφ i.succ) _)

theorem colFoldN_smul : ∀ (n : ℕ) (φ : Fin n → E) (c : E) (t : Col E (n + 1)),
    colFoldN n φ (c • t) = c • colFoldN n φ t
  | 0, _, _, _ => rfl
  | n + 1, φ, c, t => by
    simp only [colFoldN, colFold_smul, colFoldN_smul n]

/-- A unit table folded down to its last variable. -/
theorem colFoldN_unit : ∀ (n : ℕ) (φ : Fin n → E) (a : Fin (n + 1) → Bool),
    colFoldN n φ (unitCol a) = eqProd n φ a • unitCol (pt (a (Fin.last n)))
  | 0, _, a => by
    have : pt (a (Fin.last 0)) = a := by funext i; fin_cases i; rfl
    rw [this, eqProd, one_smul]
    rfl
  | n + 1, φ, a => by
    simp only [colFoldN, colFold_unit, colFoldN_smul, colFoldN_unit n, eqProd, smul_smul]
    rw [show Fin.tail a (Fin.last n) = a (Fin.last (n + 1)) by rw [Fin.tail, Fin.succ_last]]

/-- The gadget's third pattern: the overflow lane, `32`. -/
def pattern2 : Col E 6 := unitCol (lane 32)

/-- Its move: the unit table of lane `33`. -/
def move2 : Col E 6 := unitCol (lane 33)

theorem upper_move2 : Upper (move2 (E := E)) := by
  intro b hb
  have : b ≠ lane 33 := fun h => by rw [h] at hb; exact absurd hb (by decide)
  simp [move2, unitCol, this]

/-- **The upper pattern's move has a nonzero running claim** after the rounds but the last. -/
theorem runClaim_move2 (Φ : Fin 6 → E) (hΦ : ∀ i, Φ i ≠ 0 ∧ Φ i ≠ 1) :
    runClaim (Fin.init Φ) (Fin.init (colRounds 6 Φ pattern2 move2)) ≠ 0 := by
  have hc : colIp (pattern2 (E := E)) move2 = 0 := by
    rw [pattern2, move2, colIp_unit]
    simp [show lane 32 ≠ lane 33 by decide]
  have h := lastClaim_upper 5 Φ (w := pattern2) upper_move2
  rw [hc] at h
  rw [runClaim, h, pattern2, move2, colFoldN_unit, colFoldN_unit]
  have h32 : lane 32 (Fin.last 5) = true := by decide
  have h33 : lane 33 (Fin.last 5) = true := by decide
  have hi : ∀ i, Fin.init Φ i ≠ 0 ∧ Fin.init Φ i ≠ 1 := fun i => hΦ _
  simp only [h32, h33, Pi.smul_apply, smul_eq_mul, unitCol, ite_true, mul_one]
  exact mul_ne_zero (eqProd_ne_zero 5 _ hi _) (eqProd_ne_zero 5 _ hi _)

/-- **The gadget's patterns reach every value of the six rounds** but the last quadratic
coefficient, at every `Φ` with no coordinate in `{0, 1}` and `2 Φ₀ ≠ 1`: two lower tables (one
against each lower pattern, each of zero weighted sum) and a multiple of the upper move. -/
theorem deployed_reach_all (Φ : Fin 6 → E) (hΦ : ∀ i, Φ i ≠ 0 ∧ Φ i ≠ 1) (h2 : 2 * Φ 0 ≠ 1)
    (v : Fin 6 → E × E) :
    ∃ (τa τb : Col E 6) (α : E), Lower τa ∧ Lower τb ∧ colIp pattern0 τa = 0 ∧
      colIp pattern1 τb = 0 ∧
      (∀ i : Fin 5, (colRounds 6 Φ pattern0 τa + colRounds 6 Φ pattern1 τb
          + α • colRounds 6 Φ pattern2 move2) i.castSucc = v i.castSucc) ∧
      ((colRounds 6 Φ pattern0 τa + colRounds 6 Φ pattern1 τb
          + α • colRounds 6 Φ pattern2 move2) (Fin.last 5)).1 = (v (Fin.last 5)).1 :=
  reach_all 3 Φ hΦ pattern0 pattern1 (deployed_nd (Fin.init Φ) (fun _ => hΦ _) h2) pattern2 move2
    upper_move2 (runClaim_move2 Φ hΦ) v

/-! ### `K`-valued moves: the twisted completions, `β`, and forgetting the last coefficient -/

section Moves

variable {K : Type} [Field K] [Algebra K E]

/-- A `K`-valued table as one of `E`. -/
def ofK {k : ℕ} (c : (Fin k → Bool) → K) : Col E k := fun b => algebraMap K E (c b)

theorem ofK_add {k : ℕ} (c c' : (Fin k → Bool) → K) : ofK (E := E) (c + c') = ofK c + ofK c' := by
  funext b; simp [ofK]

/-- The gadget's patterns (`E`-valued, of `K`-values `0` and `1`). -/
def patE : Fin 3 → Col E 6
  | 0 => pattern0
  | 1 => pattern1
  | 2 => pattern2

/-- The half a pattern weighs: lower for the pairs, upper for the overflow lane. -/
def OnHalf (p : Fin 3) (t : Col E 6) : Prop := if p.val < 2 then Lower t else Upper t

/-- The other half: the solvers'. -/
def OnOther (p : Fin 3) (t : Col E 6) : Prop := if p.val < 2 then Upper t else Lower t

theorem pattern0_lower : Lower (pattern0 (E := E)) := by
  intro b hb
  have h1 : b ≠ lane 0 := fun h => by rw [h] at hb; exact absurd hb (by decide)
  have h2 : b ≠ flipC (lane 0) := fun h => by rw [h] at hb; exact absurd hb (by decide)
  simp [pattern0, pairCol, unitCol, h1, h2]

theorem pattern1_lower : Lower (pattern1 (E := E)) := by
  intro b hb
  have h1 : b ≠ lane 1 := fun h => by rw [h] at hb; exact absurd hb (by decide)
  have h2 : b ≠ flipC (lane 1) := fun h => by rw [h] at hb; exact absurd hb (by decide)
  simp [pattern1, pairCol, unitCol, h1, h2]

theorem pattern2_upper : Upper (pattern2 (E := E)) := by
  intro b hb
  have h1 : b ≠ lane 32 := fun h => by rw [h] at hb; exact absurd hb (by decide)
  simp [pattern2, unitCol, h1]

/-- A weight on one half and a table on the other weigh zero. -/
theorem colIp_sep {k : ℕ} {w t : Col E (k + 1)} (h : (Lower w ∧ Upper t) ∨ (Upper w ∧ Lower t)) :
    colIp w t = 0 := by
  refine sum_eq_zero fun b _ => ?_
  rcases h with ⟨hw, ht⟩ | ⟨hw, ht⟩ <;> cases hb : b (Fin.last k)
  · simp [ht b hb]
  · simp [hw b hb]
  · simp [hw b hb]
  · simp [ht b hb]

theorem sep_of (p : Fin 3) {s : Col E 6} (hs : OnOther p s) :
    (Lower (patE (E := E) p) ∧ Upper s) ∨ (Upper (patE (E := E) p) ∧ Lower s) := by
  fin_cases p
  · exact Or.inl ⟨pattern0_lower, hs⟩
  · exact Or.inl ⟨pattern1_lower, hs⟩
  · exact Or.inr ⟨pattern2_upper, hs⟩

/-- The rounds' values but the last quadratic coefficient. -/
def piv (x : Fin 6 → E × E) : (Fin 5 → E × E) × E := (Fin.init x, (x (Fin.last 5)).1)

theorem piv_add (x y : Fin 6 → E × E) : piv (x + y) = piv x + piv y := rfl

theorem piv_smul (e : E) (x : Fin 6 → E × E) : piv (e • x) = e • piv x := rfl

theorem piv_sum {ι : Type} (s : Finset ι) (f : ι → Fin 6 → E × E) :
    piv (∑ i ∈ s, f i) = ∑ i ∈ s, piv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, piv_add, ih]

/-- The moves of the gadget: at pattern `p`'s entry `i` (weight `μ β_i` on the pattern), `K`-values
`c` on the pattern's half weighing zero against it and `s` on the other half, folding to zero
together; their rounds. -/
def gadgetMoves (Φ : Fin 6 → E) (μ : E) (β : Module.Basis (Fin 3) K E) : Set (Fin 6 → E × E) :=
  {v | ∃ (p i : Fin 3) (c s : (Fin 6 → Bool) → K), OnHalf p (ofK (E := E) c) ∧
    OnOther p (ofK (E := E) s) ∧ colIp (patE (E := E) p) (ofK c) = 0 ∧
    (∑ b, eqW Φ b * algebraMap K E (c b + s b)) = 0 ∧
    v = (μ * β i) • colRounds 6 Φ (patE p) (ofK (c + s))}

/-- A move keeps the last running claim: its rounds lie in `ker lastMap`. -/
theorem lastClaim_move (Φ : Fin 6 → E) (w t : Col E 6) (hip : colIp w t = 0)
    (hfold : (∑ b, eqW Φ b * t b) = 0) : lastClaim 6 Φ (colRounds 6 Φ w t) 0 = 0 := by
  have h := lastClaim_laneRounds 6 Φ (toT w) (toT t)
  rw [ip_toT, hip] at h
  rw [colRounds, h]
  simp only [Fintype.sum_unique, foldAll_eq, toT]
  rw [hfold, mul_zero]

end Moves

section Reach

variable {K : Type} [Field K] [Algebra K E]

theorem lastClaim_snoc : ∀ (n : ℕ) (φ : Fin (n + 1) → E) (m : Fin (n + 1) → E × E) (s : E),
    lastClaim (n + 1) φ m s
      = nextClaim (φ (Fin.last n)) (m (Fin.last n)) (lastClaim n (Fin.init φ) (Fin.init m) s)
  | 0, _, _, _ => rfl
  | n + 1, φ, m, s => by
    rw [lastClaim, lastClaim_snoc n (Fin.tail φ) (Fin.tail m), lastClaim, Fin.tail_init_eq_init_tail,
      Fin.tail_init_eq_init_tail]
    rfl

theorem lastClaim_zero (k : ℕ) (φ : Fin k → E) : lastClaim k φ 0 0 = 0 := by
  have h := lastClaim_smul k φ 0 0 0
  simpa using h

/-- **Forgetting the last quadratic coefficient is injective on `ker lastMap`** (`Φ₅ ∉ {0, 1}`). -/
theorem piv_inj (Φ : Fin 6 → E) (h5 : Φ 5 ≠ 0 ∧ Φ 5 ≠ 1) (x : Fin 6 → E × E)
    (hx : lastClaim 6 Φ x 0 = 0) (hp : piv x = 0) : x = 0 := by
  have hi : Fin.init x = 0 := congrArg Prod.fst hp
  have h1 : (x (Fin.last 5)).1 = 0 := congrArg Prod.snd hp
  rw [lastClaim_snoc, hi, lastClaim_zero] at hx
  simp only [nextClaim, h1] at hx
  have hc : (x (Fin.last 5)).2 * (Φ 5 * (Φ 5 - 1)) = 0 := by
    have hl : Φ (Fin.last 5) = Φ 5 := rfl
    rw [hl] at hx
    linear_combination hx
  have h2 : (x (Fin.last 5)).2 = 0 := by
    rcases mul_eq_zero.mp hc with h | h
    · exact h
    · exfalso
      rcases mul_eq_zero.mp h with h | h
      · exact h5.1 h
      · exact h5.2 (sub_eq_zero.mp h)
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact Prod.ext h1 h2
  · exact congrFun hi j

/-- The patterns, `K`-valued. -/
def patK : Fin 3 → (Fin 6 → Bool) → K
  | 0 => pattern0
  | 1 => pattern1
  | 2 => pattern2

theorem patE_ofK (p : Fin 3) : patE (E := E) p = ofK (patK (K := K) p) := by
  funext b
  fin_cases p <;>
  simp only [patE, patK, ofK, pattern0, pattern1, pattern2, pairCol, unitCol, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul] <;>
  split_ifs <;> simp

theorem colIp_ofK {k : ℕ} (w c : (Fin k → Bool) → K) :
    colIp (ofK (E := E) w) (ofK c) = algebraMap K E (colIp w c) := by
  simp [colIp, ofK]

/-- **The `E`-multiples of a `K`-move**, through the gadget's three entries (`β`) and a twisted
completion by the solvers (which moves only the last quadratic coefficient). -/
theorem reach_multiple (Φ : Fin 6 → E) (μ : E) (hμ : μ ≠ 0) (β : Module.Basis (Fin 3) K E)
    (p : Fin 3)
    (hsolve : ∀ e : E, ∃ s : (Fin 6 → Bool) → K, OnOther p (ofK (E := E) s) ∧
      (∑ b, eqW Φ b * algebraMap K E (s b)) = e)
    (c : (Fin 6 → Bool) → K) (hc : OnHalf p (ofK (E := E) c)) (hip : colIp (patE (E := E) p) (ofK c) = 0)
    (e : E) :
    ∃ u ∈ Submodule.span K (gadgetMoves Φ μ β),
      piv u = e • piv (colRounds 6 Φ (patE p) (ofK c)) := by
  obtain ⟨sol, hs, hsf⟩ := hsolve (-(∑ b, eqW Φ b * algebraMap K E (c b)))
  set X := colRounds 6 Φ (patE (E := E) p) (ofK (c + sol))
  have hmove : ∀ i, (μ * β i) • X ∈ gadgetMoves Φ μ β := by
    intro i
    refine ⟨p, i, c, sol, hc, hs, hip, ?_, rfl⟩
    simp only [map_add, mul_add, sum_add_distrib, hsf, add_neg_cancel]
  set a := β.repr (e / μ)
  refine ⟨∑ i, a i • ((μ * β i) • X), Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (hmove i)), ?_⟩
  have hX : piv X = piv (colRounds 6 Φ (patE p) (ofK c)) := by
    simp only [X, ofK_add, colRounds_add, piv_add]
    have hsep := (rounds_lower_upper 5 Φ (w := patE p) (t := ofK sol)) (sep_of p hs)
    have h0 : piv (colRounds 6 Φ (patE (E := E) p) (ofK sol)) = 0 := by
      refine Prod.ext ?_ hsep.2
      funext j
      exact hsep.1 j
    rw [h0, add_zero]
  have hsum : ∑ i, a i • ((μ * β i) • X) = (∑ i, algebraMap K E (a i) * (μ * β i)) • X := by
    rw [sum_smul]
    refine sum_congr rfl fun i _ => ?_
    rw [← smul_assoc, show a i • (μ * β i) = algebraMap K E (a i) * (μ * β i) from Algebra.smul_def _ _]
  have hcoef : ∑ i, algebraMap K E (a i) * (μ * β i) = e := by
    have := β.sum_repr (e / μ)
    calc ∑ i, algebraMap K E (a i) * (μ * β i) = μ * ∑ i, a i • β i := by
          rw [mul_sum]
          refine sum_congr rfl fun i _ => ?_
          rw [Algebra.smul_def]
          ring
      _ = e := by rw [this]; field_simp
  rw [hsum, hcoef, piv_smul, hX]

theorem onHalf_mono (p : Fin 3) {τ t : Col E 6} (h : ∀ b, τ b = 0 → t b = 0) (hτ : OnHalf p τ) :
    OnHalf p t := by
  unfold OnHalf at hτ ⊢
  split_ifs at hτ ⊢
  · exact fun b hb => h b (hτ b hb)
  · exact fun b hb => h b (hτ b hb)

/-- **An `E`-valued table of a pattern's half** (weighing zero against it), as `K`-moves: its rounds,
but the last quadratic coefficient, are those of a `K`-combination of the gadget's moves. -/
theorem reach_table (Φ : Fin 6 → E) (μ : E) (hμ : μ ≠ 0) (β : Module.Basis (Fin 3) K E) (p : Fin 3)
    (hsolve : ∀ e : E, ∃ s : (Fin 6 → Bool) → K, OnOther p (ofK (E := E) s) ∧
      (∑ b, eqW Φ b * algebraMap K E (s b)) = e)
    (τ : Col E 6) (hτ : OnHalf p τ) (hip : colIp (patE p) τ = 0) :
    ∃ u ∈ Submodule.span K (gadgetMoves Φ μ β), piv u = piv (colRounds 6 Φ (patE p) τ) := by
  set c : Fin 3 → (Fin 6 → Bool) → K := fun j b => β.repr (τ b) j
  have hdec : τ = β 0 • ofK (c 0) + β 1 • ofK (c 1) + β 2 • ofK (c 2) := by
    funext b
    have h := β.sum_repr (τ b)
    rw [Fin.sum_univ_three] at h
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ofK, c]
    conv_lhs => rw [← h]
    simp only [Algebra.smul_def]
    ring
  have hhalf : ∀ j, OnHalf p (ofK (E := E) (c j)) := fun j =>
    onHalf_mono p (fun b hb => by simp [ofK, c, hb]) hτ
  have hk : ∀ j, colIp (patE (E := E) p) (ofK (c j)) = algebraMap K E (colIp (patK p) (c j)) := fun j => by
    rw [patE_ofK (K := K), colIp_ofK]
  have hzero : ∀ j, colIp (patE (E := E) p) (ofK (c j)) = 0 := by
    have hsum : ∑ j, colIp (patK p) (c j) • β j = 0 := by
      have h := hip
      rw [hdec, colIp_add, colIp_add, colIp_smul, colIp_smul, colIp_smul, hk, hk, hk] at h
      rw [Fin.sum_univ_three]
      simp only [Algebra.smul_def]
      linear_combination h
    have hli := Fintype.linearIndependent_iff.mp β.linearIndependent _ hsum
    intro j
    rw [hk, hli j, map_zero]
  choose u hu hpu using fun j => reach_multiple Φ μ hμ β p hsolve (c j) (hhalf j) (hzero j) (β j)
  refine ⟨u 0 + u 1 + u 2, Submodule.add_mem _ (Submodule.add_mem _ (hu 0) (hu 1)) (hu 2), ?_⟩
  rw [piv_add, piv_add, hpu, hpu, hpu, hdec, colRounds_add, colRounds_add, colRounds_smul,
    colRounds_smul, colRounds_smul, piv_add, piv_add, piv_smul, piv_smul, piv_smul]

/-- `move2` is a `K`-table. -/
theorem move2_ofK : move2 (E := E) = ofK (unitCol (E := K) (lane 33)) := by
  funext b
  simp only [move2, unitCol, ofK]
  split_ifs <;> simp

/-- **Condition (R) for one entry of each of the gadget's patterns**: every value of the six rounds
that keeps the last running claim (`ker lastMap`) is a `K`-combination of the gadget's moves, for
every `Φ` with no coordinate in `{0, 1}` and `2 Φ₀ ≠ 1`, every nonzero scale `μ` and every basis
`β` of `E` over `K`, given the solvers (`K`-values on the other half whose fold reaches every
element of `E`). -/
theorem column_reach (Φ : Fin 6 → E) (hΦ : ∀ i, Φ i ≠ 0 ∧ Φ i ≠ 1) (h2 : 2 * Φ 0 ≠ 1) (μ : E)
    (hμ : μ ≠ 0) (β : Module.Basis (Fin 3) K E)
    (hsolve : ∀ (p : Fin 3) (e : E), ∃ s : (Fin 6 → Bool) → K, OnOther p (ofK (E := E) s) ∧
      (∑ b, eqW Φ b * algebraMap K E (s b)) = e) :
    LinearMap.ker (lastMap (K := K) Φ) ≤ Submodule.span K (gadgetMoves Φ μ β) := by
  intro v hv
  have hv' : lastClaim 6 Φ v 0 = 0 := hv
  obtain ⟨τa, τb, α, hτa, hτb, ha, hb, hcs, hlast⟩ := deployed_reach_all Φ hΦ h2 v
  obtain ⟨ua, hua, hpa⟩ := reach_table Φ μ hμ β 0 (hsolve 0) τa hτa ha
  obtain ⟨ub, hub, hpb⟩ := reach_table Φ μ hμ β 1 (hsolve 1) τb hτb hb
  have hc2 : OnHalf 2 (ofK (E := E) (unitCol (E := K) (lane 33))) := by
    rw [← move2_ofK]; exact upper_move2
  have hip2 : colIp (patE (E := E) 2) (ofK (unitCol (E := K) (lane 33))) = 0 := by
    rw [← move2_ofK]
    show colIp pattern2 move2 = 0
    rw [pattern2, move2, colIp_unit]
    simp [show lane 32 ≠ lane 33 by decide]
  obtain ⟨uc, huc, hpc⟩ := reach_multiple Φ μ hμ β 2 (hsolve 2) _ hc2 hip2 α
  set u := ua + ub + uc
  have hu : u ∈ Submodule.span K (gadgetMoves Φ μ β) :=
    Submodule.add_mem _ (Submodule.add_mem _ hua hub) huc
  have hpiv : piv u = piv v := by
    simp only [u, piv_add, hpa, hpb, hpc, ← move2_ofK]
    have : piv (colRounds 6 Φ pattern0 τa + colRounds 6 Φ pattern1 τb
        + α • colRounds 6 Φ pattern2 move2) = piv v := by
      refine Prod.ext ?_ hlast
      funext i
      exact hcs i
    rw [← this, piv_add, piv_add, piv_smul]
    rfl
  have hspan : Submodule.span K (gadgetMoves Φ μ β) ≤ LinearMap.ker (lastMap (K := K) Φ) := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨p, i, c, sol, hc, hs, hip, hf, rfl⟩
    show lastClaim 6 Φ ((μ * β i) • colRounds 6 Φ (patE p) (ofK (c + sol))) 0 = 0
    have h := lastClaim_smul 6 Φ (μ * β i) (colRounds 6 Φ (patE p) (ofK (c + sol))) 0
    rw [smul_zero] at h
    rw [h, lastClaim_move]
    · simp
    · rw [ofK_add, colIp_add, hip, colIp_sep (sep_of p hs), add_zero]
    · simpa [ofK] using hf
  have hdiff : u - v = 0 := by
    refine piv_inj Φ (hΦ 5) (u - v) ?_ ?_
    · have h1 : lastMap (K := K) Φ (u - v) = 0 := by
        rw [map_sub, LinearMap.mem_ker.mp (hspan hu), LinearMap.mem_ker.mp hv, sub_zero]
      exact h1
    · show piv u - piv v = 0
      rw [hpiv, sub_self]
  rw [← sub_eq_zero.mp hdiff]
  exact hu

end Reach

end QuotientSecurity.Hiding
