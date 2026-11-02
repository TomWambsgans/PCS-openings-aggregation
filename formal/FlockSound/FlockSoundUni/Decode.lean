-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import FlockSoundUni.Loops
import FlockSound.Sumcheck

/-!
# The sumcheck's rounds, decoded

A sumcheck round of `Transcript.sumcheck` (`roundPoly`, three coefficients) reads two scalars and
derives the third from the running claim. Here:

* `decodeMsg c e vals`: the message `roundPoly` builds from the two scalars `vals`;
* `roundPoly_eq`: `roundPoly 3 c e` is two reads, decoded;
* **`sumcheckR_eq`**: the whole sumcheck is its rounds' reads and draws (`readRounds` of two-scalar
  rounds), decoded round by round (`decodeSC`): the code-level link of the zerocheck's and the
  lincheck's rounds;
* **`decode_consistent`** (characteristic two): the decoded message, as a polynomial (`msgPoly`,
  degree at most `2`), has the halves the round's variable weights to the claim, and
  `polyEval` is its evaluation: the runs `decodeSC` reads are `Consistent` (`FlockSound.Sumcheck`).
-/

namespace FlockSound.Uni

open UniStatement UniSound LeanVM.Parameters LeanVM.Semantics Polynomial

/-- The message `roundPoly 3 c e` builds from its two scalars. -/
def decodeMsg (c : E) : Option E → List E → List E
  | none, vals => [vals.headD 0, c + esum (vals.drop 1)] ++ vals.drop 1
  | some r, vals => [c + r * esum vals] ++ vals

section Link

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem roundPoly_eq (c : E) (e : Option E) :
    roundPoly (m := m) 3 c e = (fun vals ↦ decodeMsg c e vals) <$> nextScalars (m := m) 2 := by
  cases e with
  | none =>
    simp only [roundPoly, nextScalars_eq, repeatM, bind_assoc, pure_bind, map_bind, decodeMsg]
    simp
  | some r =>
    simp only [roundPoly, map_eq_bind_pure_comp]
    rfl

/-- The sumcheck's result from its rounds' reads: each round's message decoded from the claim,
its challenge, the next claim. -/
def decodeSC : E → List (Option E) → Done → List E × E
  | c, [], _ => ([], c)
  | c, e :: es, r :: d =>
    let ch := r.2.headD 0
    let rest := decodeSC (polyEval (decodeMsg c e r.1.2) ch) es d
    (ch :: rest.1, rest.2)
  | c, _ :: _, [] => ([], c)

theorem samples_one (F : KeccakState → m KeccakState) :
    samples F 1 = (fun x ↦ [x]) <$> sample F := by
  simp [samples_eq, repeatM, map_eq_bind_pure_comp]

/-- **The sumcheck is its rounds' reads and draws**, decoded. -/
theorem sumcheckR_eq (F : KeccakState → m KeccakState) : ∀ (es : List (Option E)) (c : E),
    sumcheckR F 3 c es =
      (fun d ↦ decodeSC c es d) <$> readRounds F (List.replicate es.length ⟨false, 2, 0⟩)
  | [], c => by simp [sumcheckR, readRounds, decodeSC]
  | e :: es, c => by
    simp only [sumcheckR, List.length_cons, List.replicate_succ, readRounds, readRound,
      roundPoly_eq, samples_one, bind_assoc, map_bind, bind_map_left, pure_bind, zero_add]
    congr 1
    funext vals
    congr 1
    funext ch
    rw [sumcheckR_eq F es]
    simp [decodeSC]

end Link

/-! ## Consistency -/

/-- A message as a polynomial, constant first. -/
noncomputable def msgPoly (l : List E) : E[X] := C (l.getD 0 0) + C (l.getD 1 0) * X + C (l.getD 2 0) * X ^ 2

theorem natDegree_msgPoly_le (l : List E) : (msgPoly l).natDegree ≤ 2 := by
  unfold msgPoly
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le (by simp) ?_)) ?_)
  · exact (natDegree_C_mul_le _ _).trans (natDegree_X_le.trans (by norm_num))
  · exact (natDegree_C_mul_le _ _).trans ((natDegree_pow_le).trans (by
      have := natDegree_X_le (R := E); nlinarith))

theorem polyEval_three (a b c x : E) : polyEval [a, b, c] x = a + x * (b + x * c) := by
  simp only [polyEval, List.foldr_cons, List.foldr_nil, zero_mul, zero_add]
  ring

theorem esum_one (a : E) : esum [a] = a := by simp [esum]

theorem esum_two (a b : E) : esum [a, b] = a + b := by simp [esum]

/-- **A decoded message of two scalars is consistent**: degree at most `2`, its halves weighted by
the round's variable give the claim, and `polyEval` is its evaluation. -/
theorem decode_consistent (c : E) (e : Option E) (a b : E) :
    (msgPoly (decodeMsg c e [a, b])).natDegree ≤ 2 ∧
      FlockSound.roundL e (fun x ↦ (msgPoly (decodeMsg c e [a, b])).eval x) = c ∧
      ∀ x, polyEval (decodeMsg c e [a, b]) x = (msgPoly (decodeMsg c e [a, b])).eval x := by
  refine ⟨natDegree_msgPoly_le _, ?_, fun x ↦ ?_⟩
  · cases e with
    | none =>
      simp only [decodeMsg, List.headD_cons, List.drop_succ_cons, List.drop_zero, esum_one,
        List.cons_append, List.nil_append, FlockSound.roundL, FlockSound.wt, msgPoly, List.getD_cons_succ,
        List.getD_cons_zero, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
      have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
      linear_combination (a + b) * h2
    | some r =>
      simp only [decodeMsg, esum_two, List.cons_append, List.nil_append, FlockSound.roundL,
        FlockSound.wt, FlockSound.eq1, msgPoly, List.getD_cons_succ, List.getD_cons_zero, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Bool.false_eq_true, if_false, if_true]
      have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
      linear_combination (r * (a + b)) * h2
  · cases e with
    | none =>
      simp only [decodeMsg, List.headD_cons, List.drop_succ_cons, List.drop_zero, esum_one,
        List.cons_append, List.nil_append, polyEval_three, msgPoly, List.getD_cons_succ,
        List.getD_cons_zero, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
      ring
    | some r =>
      simp only [decodeMsg, esum_two, List.cons_append, List.nil_append, polyEval_three, msgPoly,
        List.getD_cons_succ, List.getD_cons_zero, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
      ring

end FlockSound.Uni
