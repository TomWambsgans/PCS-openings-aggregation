-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniSound.FlockInterface
import Heap

/-!
# Uniform challenges over `E`: counting, roots, powers

The rounds' errors are counts of bad challenges over `|E| = 2^192`:

* **`prEvent_draws_card`**: `n` independent uniform challenges (`Compose.draws`) satisfy an event
  with probability its count over `|E|^n`; **`prEvent_draws_append_le`**: an event on the first
  `a` challenges or on the last `b` is at most the sum of the two probabilities.
* **Schwartz–Zippel in one variable** (`card_roots_le`, `prEvent_root_le`): a nonzero polynomial
  of degree `d` vanishes at at most `d` points, so at a uniform point with probability at most
  `d / |E|`; for a list of polynomials, the sum of the degrees.
* **Powers** (`card_powers_le`): a nonzero vector `a` of length `n` has `Σ_i a_i ρ^i = 0` at at
  most `n − 1` points `ρ` (the batching by `γ`, by `ρ`, by `λ`).
-/

namespace UniSound

open LeanVM.Parameters OracleComp Finset
open scoped ENNReal

/-! ## Counting challenges -/

theorem draws_succ (n : ℕ) : Compose.draws E (n + 1) =
    ($ᵗ E : ProbComp E) >>= fun a => Compose.draws E n >>= fun l => pure (a :: l) := rfl

theorem prEvent_uniformE_singleton (a : E) :
    Pr{let x ← ($ᵗ E : ProbComp E)}[x = a] = (Fintype.card E : ℝ≥0∞)⁻¹ :=
  SampleableType.prEvent_uniformSample_eq_singleton a

/-- **`n` uniform challenges by counting.** -/
theorem prEvent_draws_card : ∀ (n : ℕ) (P : List E → Prop) [DecidablePred P],
    Pr{let c ← Compose.draws E n}[P c] =
      ((univ.filter fun v : Fin n → E => P (List.ofFn v)).card : ℝ≥0∞) /
        (Fintype.card E : ℝ≥0∞) ^ n
  | 0, P, _ => by
    simp only [Compose.draws, pow_zero, div_one]
    rw [prEvent_pure]
    by_cases h : P []
    · simp only [h, ite_true]
      have : (univ.filter fun v : Fin 0 → E => P (List.ofFn v)) = univ :=
        filter_true_of_mem fun v _ => by simpa [List.ofFn_zero] using h
      rw [this, card_univ]
      simp
    · simp only [h, ite_false]
      have : (univ.filter fun v : Fin 0 → E => P (List.ofFn v)) = ∅ :=
        filter_false_of_mem fun v _ => by simpa [List.ofFn_zero] using h
      rw [this]
      simp
  | n + 1, P, _ => by
    classical
    rw [draws_succ]
    have e1 : Pr{let c ← (($ᵗ E : ProbComp E) >>= fun a => Compose.draws E n >>= fun l =>
        pure (a :: l))}[P c] =
        ∑ a : E, Pr{let x ← ($ᵗ E : ProbComp E)}[x = a] *
          Pr{let c ← (Compose.draws E n >>= fun l => pure (a :: l))}[P c] :=
      prEvent_bind_eq_sum_fintype _ _ _
    rw [e1]
    have e2 : ∀ a : E, Pr{let c ← (Compose.draws E n >>= fun l => pure (a :: l))}[P c] =
        ((univ.filter fun v : Fin n → E => P (a :: List.ofFn v)).card : ℝ≥0∞) /
          (Fintype.card E : ℝ≥0∞) ^ n := by
      intro a
      rw [← prEvent_draws_card n (fun l => P (a :: l))]
      simp only [bind_pure_comp, prEvent_map]
    simp only [e2, prEvent_uniformE_singleton]
    rw [← Finset.mul_sum, ← ENNReal.sum_div]
    have hc : ∑ a : E, ((univ.filter fun v : Fin n → E => P (a :: List.ofFn v)).card : ℝ≥0∞) =
        ((univ.filter fun v : Fin (n + 1) → E => P (List.ofFn v)).card : ℝ≥0∞) := by
      rw [← Nat.cast_sum]
      congr 1
      rw [← Finset.card_sigma]
      refine Finset.card_bij (fun x _ => Fin.cons x.1 x.2) (fun x hx => ?_) (fun x hx y hy h => ?_)
        (fun v hv => ?_)
      · simp only [mem_sigma, mem_univ, mem_filter, true_and] at hx ⊢
        rw [List.ofFn_succ]
        simpa using hx
      · obtain ⟨a, v⟩ := x
        obtain ⟨b, w⟩ := y
        simp only at h
        have h1 := congrFun h 0
        simp only [Fin.cons_zero] at h1
        subst h1
        have h2 : v = w := funext fun i => by simpa using congrFun h i.succ
        subst h2
        rfl
      · refine ⟨⟨v 0, Fin.tail v⟩, ?_, Fin.cons_self_tail v⟩
        simp only [mem_sigma, mem_univ, mem_filter, true_and] at hv ⊢
        rw [List.ofFn_succ] at hv
        exact hv
    rw [hc, pow_succ, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.mul_inv
      (Or.inl (pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)))
      (Or.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))]
    ring

/-- An event on `n` challenges of at most `c · |E|^(n-1)` tuples, `0 < n`, has probability at most
`c / |E|`. -/
theorem prEvent_draws_le_of_card (n : ℕ) (P : List E → Prop) [DecidablePred P] (c : ℕ)
    (h : (univ.filter fun v : Fin (n + 1) → E => P (List.ofFn v)).card ≤ c * Fintype.card E ^ n) :
    Pr{let x ← Compose.draws E (n + 1)}[P x] ≤ (c : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  rw [prEvent_draws_card]
  have hE : (Fintype.card E : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hEt : (Fintype.card E : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc ((univ.filter fun v : Fin (n + 1) → E => P (List.ofFn v)).card : ℝ≥0∞) /
        (Fintype.card E : ℝ≥0∞) ^ (n + 1)
      ≤ ((c * Fintype.card E ^ n : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) ^ (n + 1) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr h) _
    _ = (c : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
        rw [Nat.cast_mul, Nat.cast_pow, pow_succ, mul_comm (c : ℝ≥0∞),
          ENNReal.mul_div_mul_left _ _ (pow_ne_zero _ hE) (ENNReal.pow_ne_top hEt)]

/-! ## Splitting the challenges of a round -/

open Classical in
/-- Tuples of `a + b` challenges, counted as pairs of the first `a` and the last `b`. -/
theorem card_filter_append (a b : ℕ) (P : List E → List E → Prop) :
    (univ.filter fun v : Fin (a + b) → E => P ((List.ofFn v).take a) ((List.ofFn v).drop a)).card =
      (univ.filter fun x : (Fin a → E) × (Fin b → E) => P (List.ofFn x.1) (List.ofFn x.2)).card := by
  symm
  refine Finset.card_bij (fun x _ => Fin.append x.1 x.2) (fun x hx => ?_) (fun x _ y _ h => ?_)
    (fun v hv => ?_)
  · simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [List.ofFn_fin_append, List.take_left' (List.length_ofFn), List.drop_left' (List.length_ofFn)]
    exact hx
  · obtain ⟨u, w⟩ := x
    obtain ⟨u', w'⟩ := y
    simp only at h
    have h1 : u = u' := funext fun i => by simpa using congrFun h (Fin.castAdd b i)
    have h2 : w = w' := funext fun i => by simpa using congrFun h (Fin.natAdd a i)
    rw [h1, h2]
  · refine ⟨(fun i => v (Fin.castAdd b i), fun i => v (Fin.natAdd a i)), ?_,
      Fin.append_castAdd_natAdd⟩
    simp only [mem_filter, mem_univ, true_and] at hv ⊢
    rw [List.ofFn_add, List.take_left' (List.length_ofFn), List.drop_left' (List.length_ofFn)] at hv
    exact hv

/-- **An event on the first `a` challenges or on the next `b`**: at most the sum. -/
theorem prEvent_draws_append_le (a b : ℕ) (P Q : List E → Prop) :
    Pr{let c ← Compose.draws E (a + b)}[P (c.take a) ∨ Q (c.drop a)] ≤
      Pr{let c ← Compose.draws E a}[P c] + Pr{let c ← Compose.draws E b}[Q c] := by
  classical
  rw [prEvent_draws_card, prEvent_draws_card, prEvent_draws_card]
  have hc0 : (univ.filter fun v : Fin (a + b) → E =>
      P ((List.ofFn v).take a) ∨ Q ((List.ofFn v).drop a)).card =
      (univ.filter fun x : (Fin a → E) × (Fin b → E) =>
        P (List.ofFn x.1) ∨ Q (List.ofFn x.2)).card := by
    convert card_filter_append a b (fun x y => P x ∨ Q y) using 2 <;> ext <;> simp
  rw [hc0]
  have hE : (Fintype.card E : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hEt : (Fintype.card E : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsub : (univ.filter fun x : (Fin a → E) × (Fin b → E) => P (List.ofFn x.1) ∨
      Q (List.ofFn x.2)) ⊆ ((univ.filter fun u : Fin a → E => P (List.ofFn u)) ×ˢ univ) ∪
        (univ ×ˢ (univ.filter fun w : Fin b → E => Q (List.ofFn w))) := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    rcases hx with hx | hx
    · exact mem_union_left _ (mem_product.mpr ⟨by simpa using hx, mem_univ _⟩)
    · exact mem_union_right _ (mem_product.mpr ⟨mem_univ _, by simpa using hx⟩)
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  rw [card_product, card_product, card_univ, card_univ, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin] at hc
  calc _ ≤ ((((univ.filter fun u : Fin a → E => P (List.ofFn u)).card * Fintype.card E ^ b +
        Fintype.card E ^ a * (univ.filter fun w : Fin b → E => Q (List.ofFn w)).card : ℕ)) :
        ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) ^ (a + b) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr hc) _
    _ = _ := by
        rw [Nat.cast_add, ENNReal.add_div]
        congr 1
        · rw [Nat.cast_mul, Nat.cast_pow, pow_add,
            ENNReal.mul_div_mul_right _ _ (pow_ne_zero _ hE) (ENNReal.pow_ne_top hEt)]
        · rw [Nat.cast_mul, Nat.cast_pow, pow_add,
            ENNReal.mul_div_mul_left _ _ (pow_ne_zero _ hE) (ENNReal.pow_ne_top hEt)]

/-! ## Schwartz–Zippel in one variable -/

/-- **A nonzero polynomial of degree `d` vanishes at at most `d` points.** -/
theorem card_roots_le (p : Polynomial E) (hp : p ≠ 0) :
    (univ.filter fun t : E => p.eval t = 0).card ≤ p.natDegree :=
  Polynomial.card_le_degree_of_subset_roots fun t ht => by
    simp only [Finset.mem_val, mem_filter, mem_univ, true_and] at ht
    exact (Polynomial.mem_roots hp).mpr ht

/-- Some nonzero polynomial of a list vanishes at at most the sum of their degrees' points. -/
theorem card_exists_root_le : ∀ ps : List (Polynomial E),
    (univ.filter fun t : E => ∃ p ∈ ps, p ≠ 0 ∧ p.eval t = 0).card ≤ (ps.map Polynomial.natDegree).sum
  | [] => by simp
  | p :: ps => by
    have hsub : (univ.filter fun t : E => ∃ q ∈ p :: ps, q ≠ 0 ∧ q.eval t = 0) ⊆
        (univ.filter fun t : E => p ≠ 0 ∧ p.eval t = 0) ∪
          (univ.filter fun t : E => ∃ q ∈ ps, q ≠ 0 ∧ q.eval t = 0) := by
      intro t ht
      simp only [mem_filter, mem_univ, true_and, List.mem_cons, exists_eq_or_imp] at ht
      rcases ht with ht | ht
      · exact mem_union_left _ (by simpa using ht)
      · exact mem_union_right _ (by simpa using ht)
    refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
    simp only [List.map_cons, List.sum_cons]
    refine add_le_add ?_ (card_exists_root_le ps)
    by_cases hp : p = 0
    · simp [hp]
    · exact (card_le_card fun t ht => by
        simp only [mem_filter, mem_univ, true_and] at ht ⊢
        exact ht.2).trans (card_roots_le p hp)

/-- One challenge: its event counted on `E`. -/
theorem card_filter_fin_one (Q : E → Prop) [DecidablePred Q] :
    (univ.filter fun v : Fin 1 → E => Q ((List.ofFn v).headD 0)).card = (univ.filter Q).card := by
  refine Finset.card_bij (fun v _ => v 0) (fun v hv => ?_) (fun v _ w _ h => ?_) (fun t ht => ?_)
  · simp only [mem_filter, mem_univ, true_and, List.ofFn_succ, List.headD_cons] at hv ⊢
    exact hv
  · funext i
    rw [Fin.fin_one_eq_zero i]
    exact h
  · exact ⟨fun _ => t, by simpa using ht, rfl⟩

/-- **Schwartz–Zippel at a uniform point**: some nonzero polynomial of the list vanishes there with
probability at most the sum of their degrees over `|E|`. -/
theorem prEvent_root_le (ps : List (Polynomial E)) :
    Pr{let c ← Compose.draws E 1}[∃ p ∈ ps, p ≠ 0 ∧ p.eval (c.headD 0) = 0] ≤
      (((ps.map Polynomial.natDegree).sum : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  classical
  refine prEvent_draws_le_of_card 0 _ _ ?_
  rw [pow_zero, mul_one]
  convert card_exists_root_le ps using 1
  convert card_filter_fin_one (fun t => ∃ p ∈ ps, p ≠ 0 ∧ p.eval t = 0) using 2

/-! ## Powers of one challenge -/

/-- **A combination by the powers of `ρ`**: `Σ_i a_i ρ^i` (the batching by `γ`, `ρ` and `λ`: the
first entry at `1`, each next at the next power). -/
def powComb (a : List E) (ρ : E) : E := ∑ i : Fin a.length, a[i] * ρ ^ (i : ℕ)

/-- The polynomial `Σ_i a_i X^i`. -/
noncomputable def powPoly (a : List E) : Polynomial E :=
  ∑ i : Fin a.length, Polynomial.C a[i] * Polynomial.X ^ (i : ℕ)

theorem eval_powPoly (a : List E) (ρ : E) : (powPoly a).eval ρ = powComb a ρ := by
  simp [powPoly, powComb, Polynomial.eval_finsetSum]

theorem coeff_powPoly (a : List E) (j : ℕ) (hj : j < a.length) :
    (powPoly a).coeff j = a[j] := by
  simp only [powPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single ⟨j, hj⟩]
  · simp
  · intro b _ hb
    simp only [ite_eq_right_iff]
    intro h
    exact absurd (Fin.ext h.symm) hb
  · simp

theorem natDegree_powPoly_le (a : List E) : (powPoly a).natDegree ≤ a.length - 1 :=
  Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ =>
    (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

/-- **A nonzero vector of length `n` has `Σ_i a_i ρ^i = 0` at at most `n − 1` points.** -/
theorem card_powComb_le (a : List E) (h : ∃ x ∈ a, x ≠ 0) :
    (univ.filter fun ρ : E => powComb a ρ = 0).card ≤ a.length - 1 := by
  have hne : powPoly a ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    intro h0
    have hc := coeff_powPoly a i hi
    rw [h0, Polynomial.coeff_zero] at hc
    exact hx0 hc.symm
  refine (card_le_card fun ρ hρ => ?_).trans ((card_roots_le _ hne).trans
    (natDegree_powPoly_le a))
  simp only [mem_filter, mem_univ, true_and] at hρ ⊢
  rw [eval_powPoly]
  exact hρ

/-! ## Two challenges, a combination of combinations -/

/-- Pairs of challenges counted along the first: at most `Σ_ρ f ρ` when each `ρ` has at most
`f ρ` partners. -/
theorem card_fin_two_le (Q : E → E → Prop) [∀ a b, Decidable (Q a b)] (f : E → ℕ)
    (h : ∀ ρ, (univ.filter (Q ρ)).card ≤ f ρ) :
    (univ.filter fun v : Fin 2 → E => Q (v 0) (v 1)).card ≤ ∑ ρ : E, f ρ := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun v : Fin 2 → E => v 0) (t := univ)
    (fun _ _ => mem_univ _)]
  refine Finset.sum_le_sum fun ρ _ => (le_of_eq ?_).trans (h ρ)
  refine Finset.card_bij (fun v _ => v 1) (fun v hv => ?_) (fun v hv w hw hvw => ?_)
    (fun l hl => ?_)
  · simp only [mem_filter, mem_univ, true_and] at hv ⊢
    rw [← hv.2]
    exact hv.1
  · simp only [mem_filter, mem_univ, true_and] at hv hw
    funext i
    fin_cases i
    · exact hv.2.trans hw.2.symm
    · exact hvw
  · refine ⟨![ρ, l], ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and] at hl ⊢
    exact ⟨hl, rfl⟩

/-- **A combination by `λ` of combinations by `ρ`** of vectors one of which is nonzero (the
batch's start: `λ` over the commitments, `ρ` over each one's relations) vanishes at at most
`(n − 1 + m − 1) / |E|` of the pairs `(ρ, λ)`, `n` bounding the vectors' lengths and `m` their
number. -/
theorem prEvent_twoLevel_le (ds : List (List E)) (n m : ℕ) (hn : ∀ d ∈ ds, d.length ≤ n)
    (hm : ds.length ≤ m) (hbad : ∃ d ∈ ds, ∃ x ∈ d, x ≠ 0) :
    Pr{let c ← Compose.draws E 2}[
        powComb (ds.map fun d => powComb d (c.headD 0)) (c.getD 1 0) = 0] ≤
      (((n - 1) + (m - 1) : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  classical
  obtain ⟨d₀, hd₀, hbad₀⟩ := hbad
  refine prEvent_draws_le_of_card 1 _ _ ?_
  rw [pow_one]
  have hc := card_fin_two_le (fun ρ l => powComb (ds.map fun d => powComb d ρ) l = 0)
    (fun ρ => if powComb d₀ ρ = 0 then Fintype.card E else m - 1) (fun ρ => by
      split_ifs with h0
      · exact card_le_univ _
      · refine (card_powComb_le _ ⟨powComb d₀ ρ,
          List.mem_map_of_mem (f := fun d => powComb d ρ) hd₀, h0⟩).trans ?_
        simp only [List.length_map]
        omega)
  have hcard : (univ.filter fun v : Fin (1 + 1) → E =>
      powComb (ds.map fun d => powComb d ((List.ofFn v).headD 0)) ((List.ofFn v).getD 1 0) = 0).card
        = (univ.filter fun v : Fin 2 → E =>
          powComb (ds.map fun d => powComb d (v 0)) (v 1) = 0).card := by
    congr 1
  rw [hcard]
  refine hc.trans ?_
  have hsplit : ∑ ρ : E, (if powComb d₀ ρ = 0 then Fintype.card E else m - 1) ≤
      (univ.filter fun ρ : E => powComb d₀ ρ = 0).card * Fintype.card E +
        Fintype.card E * (m - 1) := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
    refine add_le_add le_rfl (Nat.mul_le_mul_right _ (card_le_univ _))
  refine hsplit.trans ?_
  have h0 := card_powComb_le d₀ hbad₀
  have h1 : (univ.filter fun ρ : E => powComb d₀ ρ = 0).card ≤ n - 1 :=
    h0.trans (by have := hn d₀ hd₀; omega)
  calc (univ.filter fun ρ : E => powComb d₀ ρ = 0).card * Fintype.card E +
        Fintype.card E * (m - 1)
      ≤ (n - 1) * Fintype.card E + Fintype.card E * (m - 1) :=
        add_le_add (Nat.mul_le_mul_right _ h1) le_rfl
    _ = ((n - 1) + (m - 1)) * Fintype.card E := by ring

end UniSound
