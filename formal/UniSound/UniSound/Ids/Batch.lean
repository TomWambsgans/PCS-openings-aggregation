-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.Ids.Bridges

/-!
# The batch's start (`UniIdsRest.batch_start`)

`Σ_u g(u) + target` is the combination by `λ` of each commitment's combination by `ρ` of its relations'
differences, and of the pending matrices' difference (`batch_start_of`): `weightAt` is linear in its
terms (`WeightAtLinear`), `combine` is the `ρ`-combination at the merged points (`CombineEq`), so the
combined claim's weight against the zero-extended stack, plus its value, is `Σ_i ρ^i` of the relations'
differences (`relDiff`, at the same merged points); the pending term's product is its difference's sum.
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset

/-! ## Powers -/

theorem powComb_nil (ρ : E) : powComb [] ρ = 0 := by simp [powComb]

theorem powComb_eq_range (a : List E) (ρ : E) :
    powComb a ρ = ∑ i ∈ range a.length, a.getD i 0 * ρ ^ i := by
  unfold powComb
  rw [← Fin.sum_univ_eq_sum_range (fun i ↦ a.getD i 0 * ρ ^ i)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [List.getD_eq_getElem _ _ i.isLt]
  rfl

theorem powComb_cons (x : E) (l : List E) (ρ : E) : powComb (x :: l) ρ = x + ρ * powComb l ρ := by
  rw [powComb_eq_range, powComb_eq_range, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
  have h1 : ∀ i ∈ range l.length, (x :: l).getD (i + 1) 0 * ρ ^ (i + 1) = ρ * (l.getD i 0 * ρ ^ i) := by
    intro i _
    rw [List.getD_cons_succ, pow_succ]
    ring
  rw [Finset.sum_congr rfl h1, List.getD_cons_zero, pow_zero, mul_one, add_comm]

theorem zipIdx_sum (ρ : E) (f : Relation → E) : ∀ (l : List Relation) (n : ℕ),
    ((l.zipIdx n).map fun ri ↦ ρ ^ ri.2 * f ri.1).sum = ρ ^ n * powComb (l.map f) ρ
  | [], n => by simp [powComb_nil]
  | x :: l, n => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, zipIdx_sum ρ f l (n + 1), List.map_cons,
      powComb_cons, pow_succ]
    ring

/-- `Σ_i ρ^i f(l_i)` is `powComb (l.map f) ρ`. -/
theorem zipIdx_sum_zero (ρ : E) (f : Relation → E) (l : List Relation) :
    ((l.zipIdx).map fun ri ↦ ρ ^ ri.2 * f ri.1).sum = powComb (l.map f) ρ := by
  have := zipIdx_sum ρ f l 0
  rwa [pow_zero, one_mul] at this

/-! ## One commitment -/

theorem sum_list_mul {α : Type} (l : List α) (f : α → E) (c : E) :
    (l.map fun a ↦ f a * c).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, add_mul]

theorem sum_range_list {α : Type} (l : List α) (f : α → ℕ → E) (n : ℕ) :
    ∑ u ∈ range n, (l.map fun a ↦ f a u).sum = (l.map fun a ↦ ∑ u ∈ range n, f a u).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- **One commitment's product and value**: its combined claim's weight against the zero-extended
stack, plus its value, is `Σ_i ρ^i` of its relations' differences. -/
theorem comm_start (hW : WeightAtLinear) (hC : CombineEq) (rels : List Relation) (c : Commitment)
    (ρ : E) (L : StackLayout) (rm : Option (List E)) (V : ℕ) (C : Stk) :
    ∑ u ∈ range (2 ^ V), weightAt ((combine rels c ρ).getD zeroClaim) L (bitsE u V) rm * stE C L.vars u +
        ((combine rels c ρ).getD zeroClaim).value =
      powComb ((mine rels c).map (relDiff L rm V C (mergedPoint (mine rels c)))) ρ := by
  by_cases hm : mine rels c = []
  · have hnone : combine rels c ρ = none := by
      unfold combine
      simp only [mine] at hm
      simp [hm]
    rw [hnone, hm]
    simp [weightAt, powComb_nil, zeroClaim]
  · obtain ⟨cb, hcb, hv, hF⟩ := hC rels c ρ hm
    rw [hcb, Option.getD_some]
    have hw : ∀ u, weightAt cb L (bitsE u V) rm =
        (cb.terms.map fun tm ↦ tm.2.2.2 * termW L rm V tm.1 (cb.points.getD tm.2.1 []) tm.2.2.1 u).sum :=
      fun u ↦ hW cb L (bitsE u V) rm
    simp_rw [hw, ← sum_list_mul]
    rw [sum_range_list]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [hF (fun col pt tw ↦ ∑ u ∈ range (2 ^ V), termW L rm V col pt tw u * stE C L.vars u), hv,
      ← List.sum_map_add, ← zipIdx_sum_zero]
    congr 1
    refine List.map_congr_left fun ri _ ↦ ?_
    simp only [relDiff]
    ring

/-- **The batch's start** (`UniIdsRest.batch_start`): `Σ_u g(u) + target` is the combination by `λ` of
the commitments' combinations by `ρ` of their relations' differences, and of the pending matrices'
difference. -/
theorem batch_start_of (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (hW : WeightAtLinear)
    (hC : CombineEq) (s : USt) (c1 : Stk) (ch : List E) (fd : Done) (c2 : Stk) (t : E)
    (vals : List E) (ρ l : E) :
    (prodOf D Fl s c1 ch fd c2 t vals ρ l).T [] + targetOf D Fl s c1 ch fd c2 t vals ρ l =
      powComb ((diffsOf D Fl s c1 ch fd c2 t vals).map fun d ↦ powComb d ρ) l := by
  unfold prodOf targetOf diffsOf
  split_ifs with hg
  · have h0 := comm_start hW hC (relsAt D Fl s ch fd t vals) .c1 ρ (layoutOf D.shape .c1)
      (ringMapAt Fl fd) (batchVars D.shape) (stackFor D c1 c2 .c1)
    have h1 := comm_start hW hC (relsAt D Fl s ch fd t vals) .c2 ρ (layoutOf D.shape .c2)
      (ringMapAt Fl fd) (batchVars D.shape) (stackFor D c1 c2 .c2)
    have h2 := comm_start hW hC (relsAt D Fl s ch fd t vals) .setup ρ (layoutOf D.shape .setup)
      (ringMapAt Fl fd) (batchVars D.shape) (stackFor D c1 c2 .setup)
    simp only [ProdSum.T, List.length_nil, Nat.sub_zero, foldAll, List.foldl_nil,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add, commitments, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, powComb_cons, powComb_nil, mul_zero, add_zero]
    simp only [cm, combAt, commitments, List.getD_cons_zero, List.getD_cons_succ,
      show (0 : ℕ) < 3 from by norm_num, show (1 : ℕ) < 3 from by norm_num,
      show (2 : ℕ) < 3 from by norm_num, show ¬ (3 : ℕ) < 3 from by norm_num, ite_true, ite_false,
      pendDiff] at h0 h1 h2 ⊢
    rw [← h0, ← h1, ← h2]
    ring
  · simp [ProdSum.T, powComb_cons, powComb_nil]

end UniSound.Ids
