-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import FlockSound.Cube

/-!
# Sumcheck soundness, round by round, with explicit bad challenges

A sumcheck over `m` variables proves `cubeSum w Φ = c₀`. Round `j` sends a polynomial `q j` of
degree at most `d` whose two halves, weighted by the round's variable (`roundL`: plain, or `eq` at
`τ`, Gruen's split), give the running claim; the verifier then draws `χ j` and the claim becomes
`(q j)(χ j)`. After the last round the claim must equal `Φ χ`.

* `trueAt w Φ χ j`: the true claim before round `j`, the cube sum of `Φ` with its first `j`
  coordinates bound to `χ`; `trueRound w Φ`: the true round polynomial of the first round, as a
  function (`roundL_trueRound`: its halves give the cube sum).
* `roundBad d h q`: the challenges at which a message `q` that differs from the true round function
  `h` agrees with it; empty when `q = h`. At most `d` of them when `h` is a polynomial of degree at
  most `d` (`card_roundBad_le`).
* `sumBad d w Φ q χ j`: round `j`'s bad challenges, a function of the challenges before `j` only
  (`sumBad_congr`), at most `d` (`card_sumBad_le`).
* **`sumcheck_escape`**: if a claim of the run is false and the last one is true, some later round
  `j'` had a false claim and a bad challenge.

The rounds' encoding (the Rust's two scalars a round) is not here: a round is any polynomial of
degree at most `d` whose halves give the claim. Nothing here transcribes a source.
-/

namespace FlockSound

open Polynomial Finset

variable {F : Type*} [Field F]

/-- **The round functional**: the two halves of a round function, weighted by the variable. -/
def roundL (o : Option F) (q : F → F) : F := wt o false * q 0 + wt o true * q 1

/-- The true round function of the first round: the cube sum of the other coordinates. -/
def trueRound {m : ℕ} (w : Fin (m + 1) → Option F) (Φ : (Fin (m + 1) → F) → F) (x : F) : F :=
  cubeSum (Fin.tail w) fun r ↦ Φ (Fin.cons x r)

theorem roundL_trueRound {m : ℕ} (w : Fin (m + 1) → Option F) (Φ : (Fin (m + 1) → F) → F) :
    roundL (w 0) (trueRound w Φ) = cubeSum w Φ := by
  rw [cubeSum_succ, roundL, trueRound, trueRound]

/-- The true round function of a function of individual degree `d` is a polynomial of degree at
most `d`. -/
theorem trueRound_poly {m : ℕ} (w : Fin (m + 1) → Option F) {Φ : (Fin (m + 1) → F) → F} {d : ℕ}
    (hΦ : IndDeg Φ d) : ∃ p : F[X], p.natDegree ≤ d ∧ ∀ x, trueRound w Φ x = p.eval x := by
  classical
  choose p hp hpe using fun b : Cube m ↦ hΦ.zero (cube b)
  refine ⟨∑ b, C (eqW (Fin.tail w) b) * p b, ?_, fun x ↦ ?_⟩
  · exact natDegree_sum_le_of_forall_le _ _ fun b _ ↦ (natDegree_C_mul_le _ _).trans (hp b)
  · simp only [trueRound, cubeSum, eval_finset_sum, eval_mul, eval_C, hpe]

section Bad

variable [Fintype F] [DecidableEq F]

/-- **A round's bad challenges**: where a message `q` of degree at most `d` that differs from the
true round function `h` agrees with it. -/
noncomputable def roundBad (d : ℕ) (h : F → F) (q : F[X]) : Finset F :=
  if q.natDegree ≤ d ∧ ∃ x, q.eval x ≠ h x then univ.filter fun x ↦ q.eval x = h x else ∅

/-- At most `d` bad challenges when the true round function is a polynomial of degree `≤ d`. -/
theorem card_roundBad_le {d : ℕ} {h : F → F} (q : F[X])
    (hh : ∃ p : F[X], p.natDegree ≤ d ∧ ∀ x, h x = p.eval x) : (roundBad d h q).card ≤ d := by
  unfold roundBad
  split_ifs with hc
  · obtain ⟨p, hp, hpe⟩ := hh
    obtain ⟨hq, x₀, hx₀⟩ := hc
    have hne : q - p ≠ 0 := by
      intro h0
      apply hx₀
      rw [hpe, ← sub_eq_zero, ← eval_sub, h0, eval_zero]
    refine (card_le_degree_of_subset_roots fun x hx ↦ ?_).trans
      ((natDegree_sub_le _ _).trans (max_le hq hp))
    rw [Finset.mem_val, Finset.mem_filter] at hx
    rw [mem_roots hne, IsRoot, eval_sub, hx.2, hpe, sub_self]
  · simp

/-- A message whose halves give a claim the true round function's halves do not is bad exactly
where it agrees with the true round function. -/
theorem mem_roundBad {d : ℕ} {h : F → F} {q : F[X]} {o : Option F} (hq : q.natDegree ≤ d)
    (hne : roundL o (fun x ↦ q.eval x) ≠ roundL o h) {x : F} (hx : q.eval x = h x) :
    x ∈ roundBad d h q := by
  have hc : q.natDegree ≤ d ∧ ∃ x, q.eval x ≠ h x := by
    refine ⟨hq, ?_⟩
    by_contra hall
    push Not at hall
    exact hne (by simp only [roundL, hall])
  rw [roundBad, if_pos hc]
  simp [hx]

/-- **Round `j`'s bad challenges** in a run of messages `q` and challenges `χ`: round `0`'s from
`Φ`, round `j + 1`'s those of the run on `Φ` with its first coordinate bound to `χ 0`. -/
noncomputable def sumBad (d : ℕ) : (m : ℕ) → (Fin m → Option F) → ((Fin m → F) → F) →
    (Fin m → F[X]) → (Fin m → F) → Fin m → Finset F
  | 0, _, _, _, _, j => j.elim0
  | m + 1, w, Φ, q, χ, j => Fin.cases (roundBad d (trueRound w Φ) (q 0))
      (fun j ↦ sumBad d m (Fin.tail w) (fun r ↦ Φ (Fin.cons (χ 0) r)) (Fin.tail q) (Fin.tail χ) j) j

theorem card_sumBad_le (d : ℕ) : ∀ (m : ℕ) (w : Fin m → Option F) (Φ : (Fin m → F) → F)
    (q : Fin m → F[X]) (χ : Fin m → F), IndDeg Φ d → ∀ j, (sumBad d m w Φ q χ j).card ≤ d
  | 0, _, _, _, _, _, j => j.elim0
  | m + 1, w, Φ, q, χ, hΦ, j => by
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · simp only [sumBad, Fin.cases_zero]
      obtain ⟨p, hp, hpe⟩ := trueRound_poly w hΦ
      exact card_roundBad_le _ ⟨p, hp, hpe⟩
    · simp only [sumBad, Fin.cases_succ]
      exact card_sumBad_le d m _ _ _ _ (hΦ.cons _) j

/-- Round `j`'s bad challenges depend on the challenges before `j` only. -/
theorem sumBad_congr (d : ℕ) : ∀ (m : ℕ) (w : Fin m → Option F) (Φ : (Fin m → F) → F)
    (q : Fin m → F[X]) (χ χ' : Fin m → F) (j : Fin m), (∀ i : Fin m, i.val < j.val → χ i = χ' i) →
    sumBad d m w Φ q χ j = sumBad d m w Φ q χ' j
  | 0, _, _, _, _, _, j, _ => j.elim0
  | m + 1, w, Φ, q, χ, χ', j, h => by
    refine Fin.cases (fun _ ↦ ?_) (fun j h ↦ ?_) j h
    · simp only [sumBad, Fin.cases_zero]
    · simp only [sumBad, Fin.cases_succ]
      rw [h 0 (Nat.succ_pos _)]
      exact sumBad_congr d m _ _ _ _ _ j fun i hi ↦ h i.succ (by simpa using hi)

end Bad

/-- The run's claims: `c₀`, then each message at its challenge. -/
def claimAt {m : ℕ} (c₀ : F) (q : Fin m → F[X]) (χ : Fin m → F) : Fin (m + 1) → F :=
  Fin.cases c₀ fun j ↦ (q j).eval (χ j)

/-- The true claims: before round `j`, the cube sum with the first `j` coordinates bound. -/
def trueAt : (m : ℕ) → (Fin m → Option F) → ((Fin m → F) → F) → (Fin m → F) → Fin (m + 1) → F
  | 0, w, Φ, _, _ => cubeSum w Φ
  | m + 1, w, Φ, χ, j => Fin.cases (cubeSum w Φ)
      (fun j ↦ trueAt m (Fin.tail w) (fun r ↦ Φ (Fin.cons (χ 0) r)) (Fin.tail χ) j) j

/-- The last true claim is `Φ` at the challenges. -/
theorem trueAt_last : ∀ (m : ℕ) (w : Fin m → Option F) (Φ : (Fin m → F) → F) (χ : Fin m → F),
    trueAt m w Φ χ (Fin.last m) = Φ χ
  | 0, w, Φ, χ => by simp [trueAt, cubeSum_zero w Φ χ]
  | m + 1, w, Φ, χ => by
    rw [show Fin.last (m + 1) = (Fin.last m).succ from rfl]
    simp only [trueAt, Fin.cases_succ]
    rw [trueAt_last m]
    exact congrArg Φ (Fin.cons_self_tail χ)

theorem trueAt_zero (m : ℕ) (w : Fin m → Option F) (Φ : (Fin m → F) → F) (χ : Fin m → F) :
    trueAt m w Φ χ 0 = cubeSum w Φ := by
  cases m <;> rfl

/-- The run is **consistent**: each round's halves give its claim, and its degree is at most `d`. -/
def Consistent {m : ℕ} (d : ℕ) (w : Fin m → Option F) (c₀ : F) (q : Fin m → F[X])
    (χ : Fin m → F) : Prop :=
  ∀ j : Fin m, (q j).natDegree ≤ d ∧ roundL (w j) (fun x ↦ (q j).eval x) = claimAt c₀ q χ j.castSucc

theorem claimAt_succ {m : ℕ} (c₀ : F) (q : Fin (m + 1) → F[X]) (χ : Fin (m + 1) → F)
    (j : Fin (m + 1)) :
    claimAt c₀ q χ j.succ = claimAt ((q 0).eval (χ 0)) (Fin.tail q) (Fin.tail χ) j := by
  refine Fin.cases ?_ (fun i ↦ ?_) j <;> rfl

theorem Consistent.tail {m d : ℕ} {w : Fin (m + 1) → Option F} {c₀ : F} {q : Fin (m + 1) → F[X]}
    {χ : Fin (m + 1) → F} (h : Consistent d w c₀ q χ) :
    Consistent d (Fin.tail w) ((q 0).eval (χ 0)) (Fin.tail q) (Fin.tail χ) := by
  intro j
  refine ⟨(h j.succ).1, ?_⟩
  have := (h j.succ).2
  rw [← Fin.succ_castSucc, claimAt_succ] at this
  exact this

theorem trueAt_succ {m : ℕ} (w : Fin (m + 1) → Option F) (Φ : (Fin (m + 1) → F) → F)
    (χ : Fin (m + 1) → F) (j : Fin (m + 1)) :
    trueAt (m + 1) w Φ χ j.succ = trueAt m (Fin.tail w) (fun r ↦ Φ (Fin.cons (χ 0) r)) (Fin.tail χ) j :=
  rfl

theorem sumBad_succ (d : ℕ) {m : ℕ} (w : Fin (m + 1) → Option F) (Φ : (Fin (m + 1) → F) → F)
    [Fintype F] [DecidableEq F] (q : Fin (m + 1) → F[X]) (χ : Fin (m + 1) → F) (j : Fin m) :
    sumBad d (m + 1) w Φ q χ j.succ =
      sumBad d m (Fin.tail w) (fun r ↦ Φ (Fin.cons (χ 0) r)) (Fin.tail q) (Fin.tail χ) j := rfl

/-- **Sumcheck soundness, round by round.** In a consistent run on a function of individual
degree `d`, if the claim before round `j` is false and the last claim is true, some round
`j' ≥ j` had a false claim and a challenge in its bad set. -/
theorem sumcheck_escape [Fintype F] [DecidableEq F] (d : ℕ) : ∀ (m : ℕ) (w : Fin m → Option F)
    (Φ : (Fin m → F) → F) (c₀ : F) (q : Fin m → F[X]) (χ : Fin m → F),
    IndDeg Φ d → Consistent d w c₀ q χ → ∀ j : Fin (m + 1),
    claimAt c₀ q χ j ≠ trueAt m w Φ χ j → claimAt c₀ q χ (Fin.last m) = Φ χ →
    ∃ j' : Fin m, j.val ≤ j'.val ∧ claimAt c₀ q χ j'.castSucc ≠ trueAt m w Φ χ j'.castSucc ∧
      χ j' ∈ sumBad d m w Φ q χ j'
  | 0, w, Φ, c₀, q, χ, _, _, j, hj, hlast => by
    have : j = Fin.last 0 := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
    subst this
    exact absurd (hlast.trans (trueAt_last 0 w Φ χ).symm) hj
  | m + 1, w, Φ, c₀, q, χ, hΦ, hc, j, hj, hlast => by
    have hlast' : claimAt ((q 0).eval (χ 0)) (Fin.tail q) (Fin.tail χ) (Fin.last m) =
        (fun r ↦ Φ (Fin.cons (χ 0) r)) (Fin.tail χ) := by
      rw [← claimAt_succ]
      simpa [Fin.cons_self_tail] using hlast
    -- From round `i + 1` on, the run is the tail's.
    have tailCase : ∀ i : Fin (m + 1), claimAt c₀ q χ i.succ ≠ trueAt (m + 1) w Φ χ i.succ →
        ∃ j' : Fin (m + 1), i.val + 1 ≤ j'.val ∧
          claimAt c₀ q χ j'.castSucc ≠ trueAt (m + 1) w Φ χ j'.castSucc ∧
          χ j' ∈ sumBad d (m + 1) w Φ q χ j' := by
      intro i hi
      rw [claimAt_succ, trueAt_succ] at hi
      obtain ⟨j'', hle, hne, hbad⟩ :=
        sumcheck_escape d m _ _ _ _ _ (hΦ.cons (χ 0)) hc.tail i hi hlast'
      refine ⟨j''.succ, by simpa using hle, ?_, ?_⟩
      · rw [← Fin.succ_castSucc, claimAt_succ, trueAt_succ]
        exact hne
      · rw [sumBad_succ]
        exact hbad
    refine Fin.cases (fun hj ↦ ?_) (fun i hi ↦ ?_) j hj
    · -- Round 0 has a false claim: its message differs from the true round function.
      have h0 : claimAt c₀ q χ 0 = c₀ := rfl
      rw [h0, trueAt_zero] at hj
      have hround : roundL (w 0) (fun x ↦ (q 0).eval x) ≠ roundL (w 0) (trueRound w Φ) := by
        rw [roundL_trueRound, (hc 0).2]
        exact hj
      by_cases hx : (q 0).eval (χ 0) = trueRound w Φ (χ 0)
      · refine ⟨0, le_refl _, ?_, ?_⟩
        · show claimAt c₀ q χ 0 ≠ trueAt (m + 1) w Φ χ 0
          rw [trueAt_zero]
          exact hj
        · simp only [sumBad, Fin.cases_zero]
          exact mem_roundBad (hc 0).1 hround hx
      · obtain ⟨j', hle, hne, hbad⟩ := tailCase 0 (by
          change (q 0).eval (χ 0) ≠ trueAt m (Fin.tail w) _ (Fin.tail χ) 0
          rw [trueAt_zero]
          exact hx)
        exact ⟨j', Nat.zero_le _, hne, hbad⟩
    · obtain ⟨j', hle, hne, hbad⟩ := tailCase i hi
      exact ⟨j', by simpa using hle, hne, hbad⟩

/-- **Sumcheck soundness**: a consistent run from a false claim whose last claim is true has a
round with a false claim and a bad challenge. -/
theorem sumcheck_sound [Fintype F] [DecidableEq F] {d m : ℕ} {w : Fin m → Option F}
    {Φ : (Fin m → F) → F} {c₀ : F} {q : Fin m → F[X]} {χ : Fin m → F} (hΦ : IndDeg Φ d)
    (hc : Consistent d w c₀ q χ) (h0 : c₀ ≠ cubeSum w Φ) (hlast : claimAt c₀ q χ (Fin.last m) = Φ χ) :
    ∃ j : Fin m, χ j ∈ sumBad d m w Φ q χ j := by
  obtain ⟨j, -, -, hj⟩ := sumcheck_escape d m w Φ c₀ q χ hΦ hc 0
    (by rw [trueAt_zero]; exact h0) hlast
  exact ⟨j, hj⟩

end FlockSound
