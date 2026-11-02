-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Hiding.Rounds

/-!
# The lane rounds of one entry: halves, solvers, and two weights reach every message

`crates/quotient/HIDING.md`, "Condition (R) for every challenge: the gadget", steps 1, 4 and 5, for
one entry (a column of the stack): a weight `w` and a table `t` on the `2^(n+1)` lane indices, the
last lane variable (bit `n`, folded last) splitting them into a lower half (bit `n` false) and an
upper half.

* `rounds_lower_upper`: a weight on one half against a table on the other moves only the last
  round's quadratic coefficient (the gadget's *solvers*).
* `last_fst_lower`, `last_fst_upper`: on the lower half the last round's value at `0` is the running
  claim after the others; on the upper half it is zero.
* `two_weights_reach`: two weights on the lower half whose folds have independent halves at every
  round but the last, and non-proportional lines at the last, reach every value of the claim and of
  the rounds but the last, with tables on the lower half (induction on `n`).
-/

namespace QuotientSecurity.Hiding

open Finset

set_option linter.unusedSectionVars false

variable {E : Type} [Field E]

/-- A table of one entry on `k` lane variables. -/
abbrev Col (E : Type) (k : ℕ) := (Fin k → Bool) → E

/-- One entry's table as a table of `Rounds`. -/
def toT {k : ℕ} (w : Col E k) : LTable E Unit k := fun b _ => w b

/-- One entry's rounds. -/
def colRounds (k : ℕ) (φ : Fin k → E) (w t : Col E k) : Fin k → E × E :=
  laneRounds k φ (toT w) (toT t)

/-- One entry's weighted sum. -/
def colIp {k : ℕ} (w t : Col E k) : E := ∑ b, w b * t b

/-- Fold the first variable of one entry's table. -/
def colFold {k : ℕ} (r : E) (t : Col E (k + 1)) : Col E k :=
  fun b => (1 - r) * t (Fin.cons false b) + r * t (Fin.cons true b)

theorem foldFirst_toT {k : ℕ} (r : E) (t : Col E (k + 1)) :
    foldFirst r (toT t) = toT (colFold r t) := rfl

theorem ip_toT {k : ℕ} (w t : Col E k) : ip (toT w) (toT t) = colIp w t := by
  simp [ip, toT, colIp]

theorem colRounds_succ (k : ℕ) (φ : Fin (k + 1) → E) (w t : Col E (k + 1)) :
    colRounds (k + 1) φ w t
      = Fin.cons (msg (toT w) (toT t)) (colRounds k (Fin.tail φ) (colFold (φ 0) w)
          (colFold (φ 0) t)) := rfl

theorem msg_toT {k : ℕ} (w t : Col E (k + 1)) :
    msg (toT w) (toT t)
      = (∑ b, w (Fin.cons false b) * t (Fin.cons false b),
         ∑ b, (w (Fin.cons true b) - w (Fin.cons false b)) *
           (t (Fin.cons true b) - t (Fin.cons false b))) := by
  simp [msg, toT]

/-! ### Linearity in the table -/

theorem colRounds_add (k : ℕ) (φ : Fin k → E) (w t t' : Col E k) :
    colRounds k φ w (t + t') = colRounds k φ w t + colRounds k φ w t' := by
  have : toT (t + t') = toT t + toT t' := rfl
  simp only [colRounds, this, laneRounds_add]

theorem colRounds_smul (k : ℕ) (φ : Fin k → E) (c : E) (w t : Col E k) :
    colRounds k φ w (c • t) = c • colRounds k φ w t := by
  have : toT (c • t) = c • toT t := rfl
  simp only [colRounds, this, laneRounds_smul]

theorem colRounds_zero (k : ℕ) (φ : Fin k → E) (w : Col E k) : colRounds k φ w 0 = 0 := by
  have h := colRounds_smul k φ 0 w 0
  simpa using h

theorem colIp_add {k : ℕ} (w t t' : Col E k) : colIp w (t + t') = colIp w t + colIp w t' := by
  simp [colIp, mul_add, sum_add_distrib]

theorem colIp_smul {k : ℕ} (c : E) (w t : Col E k) : colIp w (c • t) = c * colIp w t := by
  simp [colIp, mul_sum]
  refine sum_congr rfl fun b _ => ?_
  ring

theorem colFold_add {k : ℕ} (r : E) (t t' : Col E (k + 1)) :
    colFold r (t + t') = colFold r t + colFold r t' := by
  funext b
  simp [colFold]
  ring

theorem colFold_smul {k : ℕ} (r c : E) (t : Col E (k + 1)) :
    colFold r (c • t) = c • colFold r t := by
  funext b
  simp [colFold]
  ring

/-! ### The halves -/

/-- Zero on the upper half: bit `n` (the last variable) set. -/
def Lower {n : ℕ} (t : Col E (n + 1)) : Prop := ∀ b, b (Fin.last n) = true → t b = 0

/-- Zero on the lower half. -/
def Upper {n : ℕ} (t : Col E (n + 1)) : Prop := ∀ b, b (Fin.last n) = false → t b = 0

theorem cons_last {n : ℕ} (c : Bool) (b : Fin (n + 1) → Bool) :
    (Fin.cons c b : Fin (n + 2) → Bool) (Fin.last (n + 1)) = b (Fin.last n) := by
  rw [← Fin.succ_last, Fin.cons_succ]

theorem lower_fold {n : ℕ} (r : E) {t : Col E (n + 2)} (ht : Lower t) : Lower (colFold r t) := by
  intro b hb
  simp [colFold, ht (Fin.cons false b) (by rw [cons_last]; exact hb),
    ht (Fin.cons true b) (by rw [cons_last]; exact hb)]

theorem upper_fold {n : ℕ} (r : E) {t : Col E (n + 2)} (ht : Upper t) : Upper (colFold r t) := by
  intro b hb
  simp [colFold, ht (Fin.cons false b) (by rw [cons_last]; exact hb),
    ht (Fin.cons true b) (by rw [cons_last]; exact hb)]

theorem lower_add {n : ℕ} {t t' : Col E (n + 1)} (ht : Lower t) (ht' : Lower t') : Lower (t + t') :=
  fun b hb => by simp [ht b hb, ht' b hb]

theorem lower_smul {n : ℕ} (c : E) {t : Col E (n + 1)} (ht : Lower t) : Lower (c • t) :=
  fun b hb => by simp [ht b hb]

theorem upper_add {n : ℕ} {t t' : Col E (n + 1)} (ht : Upper t) (ht' : Upper t') : Upper (t + t') :=
  fun b hb => by simp [ht b hb, ht' b hb]

theorem upper_smul {n : ℕ} (c : E) {t : Col E (n + 1)} (ht : Upper t) : Upper (c • t) :=
  fun b hb => by simp [ht b hb]

/-- A weight on one half against a table on the other: every product vanishes. -/
theorem msg_lower_upper {n : ℕ} {w t : Col E (n + 2)}
    (hsame : ∀ b b', b (Fin.last (n + 1)) = b' (Fin.last (n + 1)) →
      (w b = 0 ∨ t b' = 0)) : msg (toT w) (toT t) = 0 := by
  rw [msg_toT]
  refine Prod.ext ?_ ?_
  · refine sum_eq_zero fun b _ => ?_
    rcases hsame (Fin.cons false b) (Fin.cons false b) rfl with h | h <;> simp [h]
  · refine sum_eq_zero fun b _ => ?_
    have h1 := hsame (Fin.cons true b) (Fin.cons true b) rfl
    have h2 := hsame (Fin.cons true b) (Fin.cons false b) (by rw [cons_last, cons_last])
    have h3 := hsame (Fin.cons false b) (Fin.cons true b) (by rw [cons_last, cons_last])
    have h4 := hsame (Fin.cons false b) (Fin.cons false b) rfl
    rcases h1 with h1 | h1 <;> rcases h4 with h4 | h4
    · simp [h1, h4]
    · rcases h3 with h3 | h3
      · simp [h1, h3]
      · simp [h3, h4]
    · rcases h2 with h2 | h2
      · simp [h2, h4]
      · simp [h1, h2]
    · simp [h1, h4]

/-! ### Partial folds and the last round -/

theorem init_cons' {β : Type} {n : ℕ} (a : β) (q : Fin (n + 1) → β) :
    Fin.init (Fin.cons a q : Fin (n + 2) → β) = Fin.cons a (Fin.init q) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [Fin.init, Fin.cons_succ]
    rw [← Fin.succ_castSucc, Fin.cons_succ]

/-- Fold the first `n` variables of a table on `n + 1`, at `φ`: a table on the last variable. -/
def colFoldN : (n : ℕ) → (Fin n → E) → Col E (n + 1) → Col E 1
  | 0, _, t => t
  | n + 1, φ, t => colFoldN n (Fin.tail φ) (colFold (φ 0) t)

theorem lower_foldN : ∀ (n : ℕ) (φ : Fin n → E) {t : Col E (n + 1)}, Lower t → Lower (colFoldN n φ t)
  | 0, _, _, ht => ht
  | n + 1, φ, _, ht => lower_foldN n (Fin.tail φ) (lower_fold (φ 0) ht)

theorem upper_foldN : ∀ (n : ℕ) (φ : Fin n → E) {t : Col E (n + 1)}, Upper t → Upper (colFoldN n φ t)
  | 0, _, _, ht => ht
  | n + 1, φ, _, ht => upper_foldN n (Fin.tail φ) (upper_fold (φ 0) ht)

/-- **The running claim after all rounds but the last** is the weighted sum of the folded tables. -/
theorem lastClaim_init : ∀ (n : ℕ) (φ : Fin (n + 1) → E) (w t : Col E (n + 1)),
    lastClaim n (Fin.init φ) (Fin.init (colRounds (n + 1) φ w t)) (colIp w t)
      = colIp (colFoldN n (Fin.init φ) w) (colFoldN n (Fin.init φ) t)
  | 0, _, _, _ => rfl
  | n + 1, φ, w, t => by
    rw [colRounds_succ, init_cons']
    simp only [lastClaim, Fin.tail_cons, Fin.cons_zero]
    have h0 : Fin.init φ 0 = φ 0 := rfl
    rw [h0, ← ip_toT, nextClaim_msg, foldFirst_toT, foldFirst_toT, ip_toT]
    rw [Fin.tail_init_eq_init_tail, lastClaim_init n (Fin.tail φ)]
    rfl

/-- **The last round** is the message of the folded tables. -/
theorem colRounds_last : ∀ (n : ℕ) (φ : Fin (n + 1) → E) (w t : Col E (n + 1)),
    colRounds (n + 1) φ w t (Fin.last n)
      = msg (toT (colFoldN n (Fin.init φ) w)) (toT (colFoldN n (Fin.init φ) t))
  | 0, _, _, _ => rfl
  | n + 1, φ, w, t => by
    rw [colRounds_succ, ← Fin.succ_last, Fin.cons_succ, colRounds_last n (Fin.tail φ)]
    rw [← Fin.tail_init_eq_init_tail]
    rfl

/-- The two points of one variable. -/
def pt (c : Bool) : Fin 1 → Bool := fun _ => c

theorem cons_one (c : Bool) (f : Fin 0 → Bool) : (Fin.cons c f : Fin 1 → Bool) = pt c := by
  funext i
  fin_cases i
  rfl

theorem col1_sum {M : Type} [AddCommMonoid M] (f : (Fin 1 → Bool) → M) :
    ∑ b, f b = f (pt false) + f (pt true) := by
  rw [sum_cons]
  simp only [Fintype.sum_unique, cons_one]

theorem msg_one (u v : Col E 1) :
    msg (toT u) (toT v) = (u (pt false) * v (pt false),
      (u (pt true) - u (pt false)) * (v (pt true) - v (pt false))) := by
  rw [msg_toT]
  simp only [Fintype.sum_unique, cons_one]

theorem colIp_one (u v : Col E 1) : colIp u v = u (pt false) * v (pt false) + u (pt true) * v (pt true) := by
  rw [colIp, col1_sum]

theorem pt_last (c : Bool) : pt c (Fin.last 0) = c := rfl

/-- On the lower half, **the last round's value at `0` is the running claim** after the others. -/
theorem last_fst_lower (n : ℕ) (φ : Fin (n + 1) → E) {w t : Col E (n + 1)} (ht : Lower t) :
    (colRounds (n + 1) φ w t (Fin.last n)).1
      = lastClaim n (Fin.init φ) (Fin.init (colRounds (n + 1) φ w t)) (colIp w t) := by
  rw [lastClaim_init, colRounds_last, msg_one, colIp_one]
  have h1 : colFoldN n (Fin.init φ) t (pt true) = 0 := lower_foldN n _ ht _ (pt_last true)
  simp [h1]

/-- On the upper half the last round's value at `0` is zero. -/
theorem last_fst_upper (n : ℕ) (φ : Fin (n + 1) → E) {w t : Col E (n + 1)} (ht : Upper t) :
    (colRounds (n + 1) φ w t (Fin.last n)).1 = 0 := by
  rw [colRounds_last, msg_one]
  have h0 : colFoldN n (Fin.init φ) t (pt false) = 0 := upper_foldN n _ ht _ (pt_last false)
  simp [h0]

/-- On the upper half the running claim after all rounds but the last is the product of the
folded tables at the upper point. -/
theorem lastClaim_upper (n : ℕ) (φ : Fin (n + 1) → E) {w t : Col E (n + 1)} (ht : Upper t) :
    lastClaim n (Fin.init φ) (Fin.init (colRounds (n + 1) φ w t)) (colIp w t)
      = colFoldN n (Fin.init φ) w (pt true) * colFoldN n (Fin.init φ) t (pt true) := by
  rw [lastClaim_init, colIp_one]
  have h0 : colFoldN n (Fin.init φ) t (pt false) = 0 := upper_foldN n _ ht _ (pt_last false)
  simp [h0]

/-- **Solvers.** A weight on one half against a table on the other moves no round but the last,
and there only its quadratic coefficient. -/
theorem rounds_lower_upper : ∀ (n : ℕ) (φ : Fin (n + 1) → E) {w t : Col E (n + 1)},
    (Lower w ∧ Upper t) ∨ (Upper w ∧ Lower t) →
      (∀ i : Fin n, colRounds (n + 1) φ w t i.castSucc = 0) ∧
        (colRounds (n + 1) φ w t (Fin.last n)).1 = 0
  | 0, φ, w, t, h => by
    refine ⟨fun i => Fin.elim0 i, ?_⟩
    rw [colRounds_last, msg_one]
    rcases h with ⟨hw, ht⟩ | ⟨hw, ht⟩
    · simp [upper_foldN 0 _ ht _ (pt_last false)]
    · simp [upper_foldN 0 _ hw _ (pt_last false)]
  | n + 1, φ, w, t, h => by
    have hmsg : msg (toT w) (toT t) = 0 := by
      refine msg_lower_upper fun b b' hbb => ?_
      rcases h with ⟨hw, ht⟩ | ⟨hw, ht⟩
      · cases hb : b (Fin.last (n + 1))
        · exact Or.inr (ht b' (hbb ▸ hb))
        · exact Or.inl (hw b hb)
      · cases hb : b (Fin.last (n + 1))
        · exact Or.inl (hw b hb)
        · exact Or.inr (ht b' (hbb ▸ hb))
    have hfold : (Lower (colFold (φ 0) w) ∧ Upper (colFold (φ 0) t)) ∨
        (Upper (colFold (φ 0) w) ∧ Lower (colFold (φ 0) t)) := by
      rcases h with ⟨hw, ht⟩ | ⟨hw, ht⟩
      · exact Or.inl ⟨lower_fold _ hw, upper_fold _ ht⟩
      · exact Or.inr ⟨upper_fold _ hw, lower_fold _ ht⟩
    obtain ⟨ih1, ih2⟩ := rounds_lower_upper n (Fin.tail φ) hfold
    refine ⟨fun i => ?_, ?_⟩
    · rw [colRounds_succ]
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hmsg
      · rw [← Fin.succ_castSucc, Fin.cons_succ]
        exact ih1 j
    · rw [colRounds_succ, ← Fin.succ_last, Fin.cons_succ]
      exact ih2

/-! ### Two weights reach every message -/

/-- The halves of `w` by its first variable, as tables of the other variables. -/
def half0 {n : ℕ} (w : Col E (n + 1)) : Col E n := fun b => w (Fin.cons false b)

/-- The upper half by the first variable. -/
def half1 {n : ℕ} (w : Col E (n + 1)) : Col E n := fun b => w (Fin.cons true b)

/-- `w`'s halves by its first variable have a dual pair of tables on the lower half. -/
def HalvesDual {n : ℕ} (w : Col E (n + 2)) : Prop :=
  ∃ x₀ x₁ : Col E (n + 1), Lower x₀ ∧ Lower x₁ ∧ colIp (half0 w) x₀ = 1 ∧ colIp (half1 w) x₀ = 0 ∧
    colIp (half0 w) x₁ = 0 ∧ colIp (half1 w) x₁ = 1

/-- A table of the first variable and the last (two variables). -/
def mk2 (a b c d : E) : Col E 2 := fun v => if v 1 then (if v 0 then d else c) else (if v 0 then b else a)

/-- Two weights are nondegenerate at `φ` (the challenges of all rounds but the last): independent
halves at every round but the last two, and at the last two non-proportional lines on the lower half
(the first one's value at the origin nonzero). -/
def ND : (n : ℕ) → (Fin n → E) → Col E (n + 1) → Col E (n + 1) → Prop
  | 0, _, _, _ => False
  | 1, _, w, w' => w (Fin.cons false (pt false)) ≠ 0 ∧
      w (Fin.cons false (pt false)) * w' (Fin.cons true (pt false))
        ≠ w (Fin.cons true (pt false)) * w' (Fin.cons false (pt false))
  | n + 2, φ, w, w' => HalvesDual w ∧ HalvesDual w' ∧
      ND (n + 1) (Fin.tail φ) (colFold (φ 0) w) (colFold (φ 0) w')

theorem colIp_cons {n : ℕ} (w t : Col E (n + 1)) :
    colIp w t = colIp (half0 w) (half0 t) + colIp (half1 w) (half1 t) := by
  simp only [colIp, half0, half1]
  rw [sum_cons, sum_add_distrib]

theorem nextClaim_add (r : E) (m m' : E × E) (s s' : E) :
    nextClaim r (m + m') (s + s') = nextClaim r m s + nextClaim r m' s' := by
  simp only [nextClaim, Prod.fst_add, Prod.snd_add]
  ring

theorem nextClaim_sub (r : E) (m m' : E × E) (s s' : E) :
    nextClaim r (m - m') (s - s') = nextClaim r m s - nextClaim r m' s' := by
  simp only [nextClaim, Prod.fst_sub, Prod.snd_sub]
  ring

/-- **A change of round 0 alone.** With a dual pair for `w`'s halves, every claim and first message
whose next running claim is zero is reached by a table on the lower half that folds to zero. -/
theorem kernel_move {n : ℕ} {w : Col E (n + 2)} (hw : HalvesDual w) {r : E} (hr : r ≠ 0)
    (s h c : E) (hrel : nextClaim r (h, c) s = 0) :
    ∃ κ : Col E (n + 2), Lower κ ∧ colFold r κ = 0 ∧ colIp w κ = s ∧
      msg (toT w) (toT κ) = (h, c) := by
  obtain ⟨x₀, x₁, hx₀, hx₁, h00, h10, h01, h11⟩ := hw
  set ρ : E := -(1 - r) / r with hρ
  set A : E := h
  set B : E := h - r * c
  set x : Col E (n + 1) := A • x₀ + B • x₁
  have hx : Lower x := lower_add (lower_smul _ hx₀) (lower_smul _ hx₁)
  set κ : Col E (n + 2) := fun v => if v 0 then ρ * x (Fin.tail v) else x (Fin.tail v)
  have hκ0 : half0 κ = x := by funext b; simp [half0, κ]
  have hκ1 : half1 κ = ρ • x := by funext b; simp [half1, κ]
  have hip0 : colIp (half0 w) x = A := by
    simp only [x, colIp_add, colIp_smul, h00, h01]; ring
  have hip1 : colIp (half1 w) x = B := by
    simp only [x, colIp_add, colIp_smul, h10, h11]; ring
  refine ⟨κ, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have hv' : Fin.tail v (Fin.last n) = true := by rw [Fin.tail, Fin.succ_last]; exact hv
    simp [κ, hx _ hv']
  · funext b
    have e0 : κ (Fin.cons false b) = x b := by simp [κ]
    have e1 : κ (Fin.cons true b) = ρ * x b := by simp [κ]
    simp only [colFold, e0, e1, Pi.zero_apply, hρ]
    field_simp
    ring
  · rw [colIp_cons, hκ0, hκ1, colIp_smul, hip0, hip1]
    simp only [nextClaim] at hrel
    simp only [hρ, A, B]
    field_simp
    linear_combination -hrel
  · rw [msg_toT]
    have e0 : ∀ b, κ (Fin.cons false b) = x b := fun b => by simp [κ]
    have e1 : ∀ b, κ (Fin.cons true b) = ρ * x b := fun b => by simp [κ]
    simp only [e0, e1]
    refine Prod.ext ?_ ?_
    · exact hip0
    · have : ∑ b, (w (Fin.cons true b) - w (Fin.cons false b)) * (ρ * x b - x b)
          = (ρ - 1) * (colIp (half1 w) x - colIp (half0 w) x) := by
        simp only [colIp, half0, half1, mul_sum, ← sum_sub_distrib]
        refine sum_congr rfl fun b _ => ?_
        ring
      rw [this, hip0, hip1]
      simp only [hρ, A, B]
      field_simp
      ring

/-- Lift a table of the other variables to one constant in the first. -/
def liftCol {n : ℕ} (σ : Col E n) : Col E (n + 1) := fun v => σ (Fin.tail v)

theorem colFold_lift {n : ℕ} (r : E) (σ : Col E n) : colFold r (liftCol σ) = σ := by
  funext b
  simp [colFold, liftCol]
  ring

theorem lower_lift {n : ℕ} {σ : Col E (n + 1)} (hσ : Lower σ) : Lower (liftCol σ) := by
  intro v hv
  exact hσ _ hv

theorem colRounds_first (k : ℕ) (Φ : Fin (k + 1) → E) (w t : Col E (k + 1)) :
    colRounds (k + 1) Φ w t 0 = msg (toT w) (toT t) := rfl

theorem colRounds_kernel {n : ℕ} (Φ : Fin (n + 2) → E) (w κ : Col E (n + 2))
    (hκ : colFold (Φ 0) κ = 0) :
    colRounds (n + 2) Φ w κ = Fin.cons (msg (toT w) (toT κ)) 0 := by
  rw [colRounds_succ, hκ, colRounds_zero]

theorem colRounds_lift {n : ℕ} (Φ : Fin (n + 2) → E) (w : Col E (n + 2)) (σ : Col E (n + 1)) :
    colRounds (n + 2) Φ w (liftCol σ)
      = Fin.cons (msg (toT w) (toT (liftCol σ))) (colRounds (n + 1) (Fin.tail Φ) (colFold (Φ 0) w) σ) := by
  rw [colRounds_succ, colFold_lift]

theorem mk2_ff (a b c d : E) : mk2 a b c d (Fin.cons false (pt false)) = a := rfl
theorem mk2_tf (a b c d : E) : mk2 a b c d (Fin.cons true (pt false)) = b := rfl
theorem mk2_ft (a b c d : E) : mk2 a b c d (Fin.cons false (pt true)) = c := rfl
theorem mk2_tt (a b c d : E) : mk2 a b c d (Fin.cons true (pt true)) = d := rfl

theorem lower_mk2 (a b : E) : Lower (mk2 a b 0 0) := by
  intro v hv
  simp only [mk2]
  have : v 1 = true := hv
  simp [this]

theorem colIp_two (w t : Col E 2) :
    colIp w t = w (Fin.cons false (pt false)) * t (Fin.cons false (pt false))
      + w (Fin.cons false (pt true)) * t (Fin.cons false (pt true))
      + (w (Fin.cons true (pt false)) * t (Fin.cons true (pt false))
      + w (Fin.cons true (pt true)) * t (Fin.cons true (pt true))) := by
  rw [colIp_cons, colIp_one, colIp_one]
  rfl

theorem msg_two (w t : Col E 2) :
    msg (toT w) (toT t)
      = (w (Fin.cons false (pt false)) * t (Fin.cons false (pt false))
          + w (Fin.cons false (pt true)) * t (Fin.cons false (pt true)),
        (w (Fin.cons true (pt false)) - w (Fin.cons false (pt false))) *
            (t (Fin.cons true (pt false)) - t (Fin.cons false (pt false)))
          + (w (Fin.cons true (pt true)) - w (Fin.cons false (pt true))) *
            (t (Fin.cons true (pt true)) - t (Fin.cons false (pt true)))) := by
  rw [msg_toT, col1_sum, col1_sum]

/-- **Two weights reach every message** but the last round's: induction on the rounds. -/
theorem two_weights_reach : ∀ (n : ℕ) (Φ : Fin (n + 2) → E), (∀ i, Φ i ≠ 0) →
    ∀ (w w' : Col E (n + 2)), ND (n + 1) (Fin.init Φ) w w' →
    ∀ (s : E) (m : Fin (n + 1) → E × E), ∃ τ τ' : Col E (n + 2), Lower τ ∧ Lower τ' ∧
      colIp w τ + colIp w' τ' = s ∧
      ∀ i : Fin (n + 1), colRounds (n + 2) Φ w τ i.castSucc + colRounds (n + 2) Φ w' τ' i.castSucc = m i
  | 0, Φ, _, w, w', hnd, s, m => by
    obtain ⟨ha0, hdet⟩ := hnd
    set a0 := w (Fin.cons false (pt false))
    set a1 := w (Fin.cons true (pt false))
    set b0 := w' (Fin.cons false (pt false))
    set b1 := w' (Fin.cons true (pt false))
    set h := (m 0).1
    set c := (m 0).2
    set D := a0 * b1 - a1 * b0
    have hD : D ≠ 0 := sub_ne_zero.mpr hdet
    set t0 := h / a0
    set S := s - h
    set C := c + (a1 - a0) * t0
    set t1 := (S * (b1 - b0) - b1 * C) / D
    set u1 := (a1 * C - (a1 - a0) * S) / D
    refine ⟨mk2 t0 t1 0 0, mk2 0 u1 0 0, lower_mk2 _ _, lower_mk2 _ _, ?_, fun i => ?_⟩
    · rw [colIp_two, colIp_two]
      simp only [mk2_ff, mk2_tf, mk2_ft, mk2_tt]
      change a0 * t0 + _ * 0 + (a1 * t1 + _ * 0) + (b0 * 0 + _ * 0 + (b1 * u1 + _ * 0)) = s
      simp only [t0, t1, u1, C, S, D]
      field_simp
      ring
    · obtain rfl : i = 0 := Fin.ext (by have := i.isLt; simp)
      rw [Fin.castSucc_zero, colRounds_first, colRounds_first, msg_two, msg_two]
      simp only [mk2_ff, mk2_tf, mk2_ft, mk2_tt]
      refine Prod.ext ?_ ?_
      · change a0 * t0 + _ * 0 + (b0 * 0 + _ * 0) = h
        simp only [t0]
        field_simp
        ring
      · change (a1 - a0) * (t1 - t0) + (_ - _) * (0 - 0) + ((b1 - b0) * (u1 - 0) + (_ - _) * (0 - 0)) = c
        simp only [t0, t1, u1, C, S, D]
        field_simp
        ring
  | n + 1, Φ, hΦ, w, w', hnd, s, m => by
    obtain ⟨hw, -, hnd'⟩ := hnd
    have hnd'' : ND (n + 1) (Fin.init (Fin.tail Φ)) (colFold (Φ 0) w) (colFold (Φ 0) w') := by
      rw [← Fin.tail_init_eq_init_tail]
      exact hnd'
    set s' := nextClaim (Φ 0) (m 0) s
    obtain ⟨σ, σ', hσ, hσ', hs', hm'⟩ :=
      two_weights_reach n (Fin.tail Φ) (fun i => hΦ i.succ) _ _ hnd'' s' (Fin.tail m)
    set τ₁ := liftCol σ
    set τ₁' := liftCol σ'
    set s₁ := colIp w τ₁ + colIp w' τ₁'
    set m₁ := msg (toT w) (toT τ₁) + msg (toT w') (toT τ₁')
    have hnext : nextClaim (Φ 0) m₁ s₁ = s' := by
      rw [nextClaim_add, ← ip_toT, ← ip_toT, nextClaim_msg, nextClaim_msg, foldFirst_toT,
        foldFirst_toT, foldFirst_toT, foldFirst_toT, ip_toT, ip_toT, colFold_lift, colFold_lift]
      exact hs'
    have hrel : nextClaim (Φ 0) (m 0 - m₁) (s - s₁) = 0 := by
      rw [nextClaim_sub, hnext]
      exact sub_self _
    obtain ⟨κ, hκ, hκf, hκs, hκm⟩ := kernel_move hw (hΦ 0) (s - s₁) (m 0 - m₁).1 (m 0 - m₁).2 hrel
    refine ⟨τ₁ + κ, τ₁', lower_add (lower_lift hσ) hκ, lower_lift hσ', ?_, fun i => ?_⟩
    · rw [colIp_add, hκs]
      ring
    · rw [colRounds_add, colRounds_kernel Φ w κ hκf, colRounds_lift, colRounds_lift]
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.castSucc_zero, Pi.add_apply, Fin.cons_zero, hκm]
        change msg (toT w) (toT τ₁) + (m 0 - m₁) + msg (toT w') (toT τ₁') = m 0
        simp only [m₁]
        abel
      · rw [← Fin.succ_castSucc]
        simp only [Pi.add_apply, Fin.cons_succ, Pi.zero_apply, add_zero]
        rw [hm' j]
        rfl

/-- **With zero claims.** When both weights have independent halves at round 0 too, each table can
weigh zero against its own weight. -/
theorem two_weights_reach_zero (n : ℕ) (Φ : Fin (n + 3) → E) (hΦ : ∀ i, Φ i ≠ 0 ∧ Φ i ≠ 1)
    (w w' : Col E (n + 3)) (hnd : ND (n + 2) (Fin.init Φ) w w') (m : Fin (n + 2) → E × E) :
    ∃ τ τ' : Col E (n + 3), Lower τ ∧ Lower τ' ∧ colIp w τ = 0 ∧ colIp w' τ' = 0 ∧
      ∀ i : Fin (n + 2), colRounds (n + 3) Φ w τ i.castSucc + colRounds (n + 3) Φ w' τ' i.castSucc = m i := by
  obtain ⟨τ, τ', hτ, hτ', hs, hm⟩ := two_weights_reach (n + 1) Φ (fun i => (hΦ i).1) w w' hnd 0 m
  obtain ⟨hw, hw', -⟩ := hnd
  set σ := colIp w τ
  set r := Φ 0
  have hr1 : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm (hΦ 0).2)
  set c := σ / (1 - r)
  obtain ⟨κ, hκ, hκf, hκs, hκm⟩ := kernel_move hw (hΦ 0).1 (-σ) 0 (-c) (by
    simp only [nextClaim, c]; field_simp; ring)
  obtain ⟨κ', hκ', hκf', hκs', hκm'⟩ := kernel_move hw' (hΦ 0).1 σ 0 c (by
    simp only [nextClaim, c]; field_simp; ring)
  refine ⟨τ + κ, τ' + κ', lower_add hτ hκ, lower_add hτ' hκ', ?_, ?_, fun i => ?_⟩
  · rw [colIp_add, hκs]; ring
  · rw [colIp_add, hκs']; linear_combination hs
  · rw [colRounds_add, colRounds_add, colRounds_kernel Φ w κ hκf, colRounds_kernel Φ w' κ' hκf']
    refine Fin.cases ?_ (fun j => ?_) i
    · have h0 : colRounds (n + 3) Φ w τ 0 + colRounds (n + 3) Φ w' τ' 0 = m 0 := hm 0
      simp only [Fin.castSucc_zero, Pi.add_apply, Fin.cons_zero, hκm, hκm']
      rw [← h0]
      ext <;> simp; ring
    · have hj := hm j.succ
      rw [← Fin.succ_castSucc] at hj ⊢
      simp only [Pi.add_apply, Fin.cons_succ, Pi.zero_apply, add_zero]
      exact hj

/-- The running claim after all rounds but the last, from a zero claim. -/
def runClaim {n : ℕ} (φ : Fin n → E) (m : Fin n → E × E) : E := lastClaim n φ m 0

theorem runClaim_add {n : ℕ} (φ : Fin n → E) (m m' : Fin n → E × E) :
    runClaim φ (m + m') = runClaim φ m + runClaim φ m' := by
  have h := lastClaim_add n φ m m' 0 0
  rw [add_zero] at h
  exact h

theorem runClaim_smul {n : ℕ} (φ : Fin n → E) (c : E) (m : Fin n → E × E) :
    runClaim φ (c • m) = c * runClaim φ m := by
  have h := lastClaim_smul n φ c m 0
  rw [smul_zero] at h
  exact h

/-- **Every value of the rounds but the last quadratic coefficient** is reached by two weights on
the lower half (tables there, of zero claims) and one move on the upper half (of zero claim and a
nonzero running claim): `HIDING.md`'s steps 4 and 5 for one entry. -/
theorem reach_all (n : ℕ) (Φ : Fin (n + 3) → E) (hΦ : ∀ i, Φ i ≠ 0 ∧ Φ i ≠ 1)
    (wa wb : Col E (n + 3)) (hnd : ND (n + 2) (Fin.init Φ) wa wb) (wc τc : Col E (n + 3))
    (hτc : Upper τc)
    (hℓ : runClaim (Fin.init Φ) (Fin.init (colRounds (n + 3) Φ wc τc)) ≠ 0)
    (v : Fin (n + 3) → E × E) :
    ∃ (τa τb : Col E (n + 3)) (α : E), Lower τa ∧ Lower τb ∧ colIp wa τa = 0 ∧ colIp wb τb = 0 ∧
      (∀ i : Fin (n + 2), (colRounds (n + 3) Φ wa τa + colRounds (n + 3) Φ wb τb
          + α • colRounds (n + 3) Φ wc τc) i.castSucc = v i.castSucc) ∧
      ((colRounds (n + 3) Φ wa τa + colRounds (n + 3) Φ wb τb
          + α • colRounds (n + 3) Φ wc τc) (Fin.last (n + 2))).1 = (v (Fin.last (n + 2))).1 := by
  set mc := Fin.init (colRounds (n + 3) Φ wc τc)
  set α := (runClaim (Fin.init Φ) (Fin.init v) - (v (Fin.last (n + 2))).1) / runClaim (Fin.init Φ) mc
  set m := Fin.init v + (-α) • mc
  obtain ⟨τa, τb, hτa, hτb, ha, hb, hm⟩ := two_weights_reach_zero n Φ hΦ wa wb hnd m
  refine ⟨τa, τb, α, hτa, hτb, ha, hb, fun i => ?_, ?_⟩
  · have h := hm i
    simp only [Pi.add_apply, Pi.smul_apply] at h ⊢
    rw [h]
    simp only [m, mc, Pi.add_apply, Pi.smul_apply, Fin.init]
    ext <;> simp
  · simp only [Pi.add_apply, Pi.smul_apply, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    rw [last_fst_lower _ _ hτa, last_fst_lower _ _ hτb, last_fst_upper _ _ hτc, ha, hb, mul_zero,
      add_zero]
    have hinit : Fin.init (colRounds (n + 3) Φ wa τa) + Fin.init (colRounds (n + 3) Φ wb τb) = m := by
      funext i
      exact hm i
    have := runClaim_add (Fin.init Φ) (Fin.init (colRounds (n + 3) Φ wa τa))
      (Fin.init (colRounds (n + 3) Φ wb τb))
    simp only [runClaim] at this ⊢
    rw [← this, hinit]
    have hsplit := runClaim_add (Fin.init Φ) (Fin.init v) ((-α) • mc)
    rw [runClaim_smul] at hsplit
    simp only [runClaim] at hsplit
    rw [hsplit]
    simp only [α, runClaim] at hℓ ⊢
    field_simp
    ring

/-! ### From a stack to one entry -/

section Bridge

variable {Y : Type} [Fintype Y] [DecidableEq Y]

theorem msg_column {k : ℕ} (w t : LTable E Y (k + 1)) (y : Y) (ht : ∀ b y', y' ≠ y → t b y' = 0) :
    msg w t = msg (fun b (_ : Unit) => w b y) (fun b _ => t b y) := by
  simp only [msg, Fintype.sum_unique]
  congr 1
  · refine sum_congr rfl fun b _ => ?_
    rw [sum_eq_single y]
    · intro y' _ hy'; simp [ht _ y' hy']
    · simp
  · refine sum_congr rfl fun b _ => ?_
    rw [sum_eq_single y]
    · intro y' _ hy'; simp [ht _ y' hy']
    · simp

/-- **The lane rounds of a change on one entry** are that entry's. -/
theorem laneRounds_column : ∀ (k : ℕ) (φ : Fin k → E) (w t : LTable E Y k) (y : Y),
    (∀ b y', y' ≠ y → t b y' = 0) →
    laneRounds k φ w t = laneRounds k φ (fun b (_ : Unit) => w b y) (fun b _ => t b y)
  | 0, _, _, _, _, _ => funext fun i => Fin.elim0 i
  | k + 1, φ, w, t, y, ht => by
    have hf : ∀ b y', y' ≠ y → foldFirst (φ 0) t b y' = 0 := fun b y' hy' => by
      simp [foldFirst, ht _ y' hy']
    simp only [laneRounds]
    rw [msg_column w t y ht, laneRounds_column k _ _ _ y hf]
    rfl

theorem msg_smul_left {k : ℕ} (c : E) (w t : LTable E Y (k + 1)) :
    msg (c • w) t = c • msg w t := by
  simp only [msg, Pi.smul_apply, smul_eq_mul, Prod.smul_mk, mul_sum]
  congr 1 <;> refine sum_congr rfl fun b _ => sum_congr rfl fun y _ => ?_ <;> ring

theorem foldFirst_smul_left {k : ℕ} (r c : E) (w : LTable E Y (k + 1)) :
    foldFirst r (c • w) = c • foldFirst r w := by
  funext b y
  simp only [foldFirst, Pi.smul_apply, smul_eq_mul]
  ring

/-- The rounds are linear in the weight too. -/
theorem laneRounds_smul_left : ∀ (k : ℕ) (φ : Fin k → E) (c : E) (w t : LTable E Y k),
    laneRounds k φ (c • w) t = c • laneRounds k φ w t
  | 0, _, _, _, _ => funext fun i => Fin.elim0 i
  | k + 1, φ, c, w, t => by
    simp only [laneRounds, foldFirst_smul_left, laneRounds_smul_left k, msg_smul_left]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Pi.smul_apply, Fin.cons_zero, Fin.cons_zero]
    · rw [Pi.smul_apply, Fin.cons_succ, Fin.cons_succ, Pi.smul_apply]

end Bridge

end QuotientSecurity.Hiding
