-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Instance.JointV
import QuotientSecurity.Assembly
import QuotientSecurity.Concrete

/-!
# The claims' degenerate challenges and masks

The verifier's claims are the honest tables' only where they are defined: the witness claim's
point and value divide by `claimScale 2 23 t = Π (1 + w_{k+2}(t))`, the quotient claim's by
`claimScale 0 26 t` and by `claimDen(α, β, t, a, s) · vRows(t)`, `a` the four values the masks give.
`Good` (F1) asks `w_24(t) ≠ 0` only: at `t = β_24` (`w_24(t) = 1`) the witness claim's value is
`x / 0 = 0` while the honest table's claim is the cells' half, and for many good challenges some
masks make `claimDen` vanish. So the honest tables meet the verifier's claims (`hT₁`, `hT₂`) only off
a small set, which this file charges to the bound:

* **`TND t`**: `1 + w_k(t) ≠ 0` for `k < 26`, and the row `t^4 + t` outside `K`; **`goodT`**:
  `good` and `TND`. Uniform challenges fail `TND` with probability at most `(26·2^25 + 4|K|)/|E|`
  (`prob_not_TND_le`, `card_not_TND_le`: the roots of `1 + w_k`, at most `2^k ≤ 2^25` for each `k < 26`,
  and of `X^4 + X − a`, at most `4` for each `a ∈ K`), so
  `goodT` fails with probability at most `2^-165 + 2^-125` at our sizes (`prob_not_goodT_bits`);
* **`ClaimsND c m`**: `TND` and `claimDen · vRows(t) ≠ 0` at the five values of the masks `m`. At a
  `goodT` challenge, masks fail it with probability at most `2/|E|` (`prob_not_claimsND_le`):
  `vRows(t) ≠ 0` (the rows are `vRows`'s roots, `Exact`, and `van` vanishes there but not at `t`),
  and the four values are uniform in `E` (F1, `redMsgs_evalDistEq`, the row outside `K`), the
  first one entering the copy cell `x = a₀ + …` alone, so `claimDen = (x + ·)(x + ·) + ·` is a monic
  quadratic in `a₀`;
* **the hybrid, approximately** (`view_vclose`): with the honest tables' claims the simulator's
  only on the masks of `ClaimsND`, the honest view is within `Pr[¬ ClaimsND]` of the simulator's
  for every continuation (`VClose`): on those masks the openings' views are swapped as in
  `view_evalDistEq`, on the others nothing is claimed;
* **`joint_hzkV_nd`**, **`jointHVZKε_of_linkV`**: `joint_hzkV` and `jointHVZK_of_linkV` with
  `hT₁`, `hT₂` required only under `ClaimsND`, at `goodT`: `JointHVZKε` with `εhv = 2^-165 + 2^-125`
  and `εz = 2/2^192`.
-/

open OracleComp OracleSpec Polynomial Module QuotientSecurity QuotientSecurity.Hiding Common Finset
open QuotientZk.Joint
open scoped ENNReal NNReal

namespace QuotientZk

set_option linter.unusedSectionVars false

/-! ## Any two games are `1`-close -/

theorem close_one (A B : ProbComp Bool) : Close A B 1 := by
  constructor <;> exact le_add_left (prEvent_le_one _)

/-! ## The approximate HVZK hypothesis -/

namespace Deployed

section Named

variable {S I O M K X : Type} [DecidableEq I] [SampleableType O] [Inhabited O]
  [DecidableEq K] [DecidableEq X] [Inhabited I] [SampleableType S]

/-- **The interactive protocol's honest-verifier zero knowledge, within `εz`**: at good
challenges, the view of uniform randomness is within `εz` of the simulator's (`VClose`); bad
challenges have probability at most `εhv`. -/
def JointHVZKε (P : Proto S I O M K X) (simV : List O → ProbComp (View M I K X))
    (good : List O → Prop) (εhv εz : ℝ≥0∞) : Prop :=
  (∀ σ, good σ → VClose ((fun s => P.view s σ) <$> ($ᵗ S)) (simV σ) εz) ∧
    Pr{let σ ← uniformList O P.n}[¬ good σ] ≤ εhv

end Named

end Deployed

/-! ## The hybrid, approximately -/

namespace Joint

variable {Ch Mk R₁ R₂ V₀ W D₁ D₂ V₁ V₂ C₁ C₂ : Type}

/-- **Joint honest-verifier zero knowledge at one challenge, within the masks' degenerate
probability.** As `view_evalDistEq`, the simulator's tables having the honest tables' claims only
on the masks `nd`: the honest view is within `Pr[¬ nd]` of the simulator's. -/
theorem view_vclose [SampleableType Mk] [SampleableType R₁] [SampleableType R₂]
    (M : Model Ch Mk R₁ R₂ V₀ W D₁ D₂ V₁ V₂ C₁ C₂) (simRed : Ch → ProbComp V₀)
    (simT₁ : Ch → V₀ → D₁) (simT₂ : Ch → V₀ → D₂) (c : Ch) (nd : Mk → Prop) (ε : ℝ≥0∞)
    (hnd : Pr{let m ← $ᵗ Mk}[¬ nd m] ≤ ε)
    (hred : M.red c <$> ($ᵗ Mk) =ᵈ simRed c)
    (hide₁ : Hides M.open₁ M.cl₁ c) (hide₂ : Hides M.open₂ M.cl₂ c)
    (hT₁ : ∀ m, nd m → M.cl₁ c (simT₁ c (M.red c m)) = M.cl₁ c (M.tab₁ c m))
    (hT₂ : ∀ m, nd m → M.cl₂ c (simT₂ c (M.red c m)) = M.cl₂ c (M.tab₂ c m)) :
    VClose (M.view c <$> ($ᵗ (Mk × R₁ × R₂)))
      (simulate M.wir M.open₁ M.open₂ simRed simT₁ simT₂ c) ε := by
  classical
  let G : V₀ → D₁ → D₂ → ProbComp (V₀ × W × V₁ × V₂) := fun v d₁ d₂ =>
    (M.open₁ c d₁ <$> ($ᵗ R₁)) >>= fun x₁ => (M.open₂ c d₂ <$> ($ᵗ R₂)) >>= fun x₂ =>
      pure (v, M.wir c, x₁, x₂)
  have hreal : M.view c <$> ($ᵗ (Mk × R₁ × R₂)) =
      ($ᵗ Mk) >>= fun m => G (M.red c m) (M.tab₁ c m) (M.tab₂ c m) := by
    rw [SampleableType.uniformSample_prod_eq_bind, SampleableType.uniformSample_prod_eq_bind]
    simp only [G, map_bind, map_pure, bind_assoc, pure_bind, bind_map_left, Model.view]
  have hsimE : simulate M.wir M.open₁ M.open₂ simRed simT₁ simT₂ c =
      simRed c >>= fun v => G v (simT₁ c v) (simT₂ c v) := by
    simp only [simulate, G, bind_map_left]
  have hsim : (($ᵗ Mk) >>= fun m => G (M.red c m) (simT₁ c (M.red c m)) (simT₂ c (M.red c m))) =ᵈ
      simulate M.wir M.open₁ M.open₂ simRed simT₁ simT₂ c := by
    rw [hsimE]
    have h := hred.bind_left fun v => G v (simT₁ c v) (simT₂ c v)
    rw [bind_map_left] at h
    exact h
  intro g
  rw [hreal]
  have h1 : Close ((($ᵗ Mk) >>= fun m => G (M.red c m) (M.tab₁ c m) (M.tab₂ c m)) >>= g)
      ((($ᵗ Mk) >>= fun m => G (M.red c m) (simT₁ c (M.red c m)) (simT₂ c (M.red c m))) >>= g)
      ε := by
    rw [bind_assoc, bind_assoc]
    refine (Close.bind _ _ _ (fun m => if nd m then 0 else 1) fun m => ?_).mono ?_
    · by_cases hm : nd m
      · simp only [hm, ite_true]
        refine Close.of_evalDistEq (EvalDistEq.bind_left ?_ g)
        exact (hide₁ _ _ (hT₁ m hm).symm).bind fun _ => (hide₂ _ _ (hT₂ m hm).symm).bind fun _ =>
          EvalDistEq.rfl
      · simp only [hm, ite_false]
        exact close_one _ _
    · refine le_trans (le_of_eq ?_) hnd
      rw [prEvent_eq_tsum_ite]
      refine tsum_congr fun m => ?_
      by_cases hm : nd m <;> simp [hm]
  exact (h1.trans (Close.of_evalDistEq (hsim.bind_left g))).mono (le_of_eq (add_zero ε))

/-- `hzk_of_factor` within `ε`: a public function of the joint view. -/
theorem hzk_of_factor_vclose {S I Ob Mm Kt Xt JV Ch : Type} [Inhabited I] [SampleableType S]
    (P : Proto S I Ob Mm Kt Xt) (chOf : List Ob → Ch) (jv : Ch → S → JV)
    (out : List Ob → JV → View Mm I Kt Xt) (hview : ∀ s σ, P.view s σ = out σ (jv (chOf σ) s))
    (simJ : Ch → ProbComp JV) (good : Ch → Prop) (ε : ℝ≥0∞)
    (hj : ∀ c, good c → VClose (jv c <$> ($ᵗ S)) (simJ c) ε) :
    ∀ σ, good (chOf σ) →
      VClose ((fun s => P.view s σ) <$> ($ᵗ S)) (out σ <$> simJ (chOf σ)) ε := by
  intro σ hσ
  have h : (fun s => P.view s σ) = out σ ∘ jv (chOf σ) := funext fun s => hview s σ
  have h' := (hj _ hσ).map (out σ)
  rw [Functor.map_map] at h'
  rw [h]
  exact h'

end Joint

/-! ## The degenerate challenges and masks -/

namespace Instance

section Nondeg

variable {K E Γ₁ Γ₂ Γw : Type} [Field K] [Field E] [Algebra K E] [DecidableEq E] [CharP E 2]
  [Fintype E]

/-- **The claims' scales and the row**: `1 + w_k(t) ≠ 0` for `k < 26` (`w_k = S^k`; the claims'
scales `claimScale 2 23`, `claimScale 0 26`), and the row `t^4 + t` outside `K`. -/
def TND (t : E) : Prop :=
  (∀ k < 26, 1 + QuotientSecurity.sq^[k] t ≠ 0) ∧ rowOf t ∉ Set.range (algebraMap K E)

/-- **The claims at `(c, m)` are not degenerate**: `TND` at `t`, and the quotient claim's
denominator `claimDen · vRows(t)` nonzero at the five values the masks `m` give. -/
def ClaimsND (P : Params E) (gK : Fin 4 → K[X]) (van : K[X]) (c : Chal E Γ₁ Γ₂ Γw)
    (m : Fin 4 → Fin 3 → K) : Prop :=
  TND (K := K) c.1.1.2 ∧
    P.claimDen c.1.1.1.1 c.1.1.1.2.1 c.1.1.2 (redMsgs P gK van c.1.1.2 m).1
      (redMsgs P gK van c.1.1.2 m).2 * P.vRows.eval c.1.1.2 ≠ 0

/-- **Good, the claims' scales and the row not degenerate.** -/
def goodT (P : Params E) (gK : Fin 4 → K[X]) (van : K[X]) (c : Chal E Γ₁ Γ₂ Γw) : Prop :=
  good P gK van c ∧ TND (K := K) c.1.1.2

/-! ### Counting -/

/-- The roots of a nonzero polynomial of degree at most `d`, as a filter. -/
theorem card_filter_eval_le (p : E[X]) (hp : p ≠ 0) {d : ℕ} (hd : p.natDegree ≤ d) :
    (univ.filter fun t : E => p.eval t = 0).card ≤ d := by
  have hsub : (univ.filter fun t : E => p.eval t = 0) ⊆ p.roots.toFinset := by
    intro t ht
    rw [mem_filter] at ht
    rw [Multiset.mem_toFinset, mem_roots hp, IsRoot.def]
    exact ht.2
  calc _ ≤ p.roots.toFinset.card := card_le_card hsub
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := card_roots' p
    _ ≤ d := hd

/-- `1 + w_k(t) = 0` at most `2^k` times. -/
theorem card_one_add_sq_le (k : ℕ) :
    (univ.filter fun t : E => 1 + QuotientSecurity.sq^[k] t = 0).card ≤ 2 ^ k := by
  have hmd := digitPoly_monic_natDegree (F := E) k
  have hdeg : (digitPoly k + C 1 : E[X]).natDegree = 2 ^ k := by
    rw [natDegree_add_C, hmd.2]
  have hne : (digitPoly k + C 1 : E[X]) ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    exact absurd hdeg.symm (by positivity)
  have e : (univ.filter fun t : E => 1 + QuotientSecurity.sq^[k] t = 0) =
      univ.filter fun t : E => (digitPoly k + C 1 : E[X]).eval t = 0 := by
    refine filter_congr fun t _ => ?_
    rw [eval_add, eval_C, digitPoly_eval, add_comm]
  rw [e]
  exact card_filter_eval_le _ hne hdeg.le

/-- `t^4 + t = b` at most `4` times. -/
theorem card_rowOf_eq_le (b : E) : (univ.filter fun t : E => rowOf t = b).card ≤ 4 := by
  have hmon : (X ^ 4 + (X - C b) : E[X]).Monic := by
    refine monic_X_pow_add ?_
    rw [degree_X_sub_C]
    exact_mod_cast (by norm_num : (1 : ℕ) < 4)
  have hdeg : (X ^ 4 + (X - C b) : E[X]).natDegree ≤ 4 := by
    rw [natDegree_add_eq_left_of_natDegree_lt
      (by rw [natDegree_X_sub_C, natDegree_X_pow]; norm_num), natDegree_X_pow]
  have e : (univ.filter fun t : E => rowOf t = b) =
      univ.filter fun t : E => (X ^ 4 + (X - C b) : E[X]).eval t = 0 := by
    refine filter_congr fun t _ => ?_
    simp only [eval_add, eval_pow, eval_X, eval_sub, eval_C, rowOf]
    constructor
    · intro h
      rw [← h]
      ring
    · intro h
      linear_combination h
  rw [e]
  exact card_filter_eval_le _ hmon.ne_zero hdeg

open Classical in
/-- **`TND` fails at most `26 · 2^25 + 4|K|` times.** -/
theorem card_not_TND_le [Fintype K] :
    (univ.filter fun t : E => ¬ TND (K := K) t).card ≤ 26 * 2 ^ 25 + 4 * Fintype.card K := by
  have hsub : (univ.filter fun t : E => ¬ TND (K := K) t) ⊆
      (range 26).biUnion
        (fun k => univ.filter fun t : E => 1 + QuotientSecurity.sq^[k] t = 0) ∪
        (univ : Finset K).biUnion
          (fun a => univ.filter fun t : E => rowOf t = algebraMap K E a) := by
    intro t ht
    rw [mem_filter] at ht
    unfold TND at ht
    rw [not_and_or] at ht
    rcases ht.2 with h | h
    · push Not at h
      obtain ⟨k, hk, hk0⟩ := h
      exact mem_union_left _
        (mem_biUnion.mpr ⟨k, mem_range.mpr hk, mem_filter.mpr ⟨mem_univ _, hk0⟩⟩)
    · rw [not_not] at h
      obtain ⟨a, ha⟩ := h
      exact mem_union_right _
        (mem_biUnion.mpr ⟨a, mem_univ _, mem_filter.mpr ⟨mem_univ _, ha.symm⟩⟩)
  refine (card_le_card hsub).trans ((card_union_le _ _).trans (add_le_add ?_ ?_))
  · refine card_biUnion_le.trans ?_
    calc ∑ k ∈ range 26, (univ.filter fun t : E => 1 + QuotientSecurity.sq^[k] t = 0).card
        ≤ ∑ _k ∈ range 26, 2 ^ 25 := sum_le_sum fun k hk => (card_one_add_sq_le k).trans
          (Nat.pow_le_pow_right (by norm_num) (by have := mem_range.mp hk; omega))
      _ = 26 * 2 ^ 25 := by rw [sum_const, card_range, smul_eq_mul]
  · refine card_biUnion_le.trans ?_
    calc ∑ a : K, (univ.filter fun t : E => rowOf t = algebraMap K E a).card
        ≤ ∑ _a : K, 4 := sum_le_sum fun a _ => card_rowOf_eq_le _
      _ = 4 * Fintype.card K := by rw [sum_const, card_univ, smul_eq_mul, mul_comm]

/-- **Uniform `t` fails `TND` with probability at most `(26 · 2^25 + 4|K|) / |E|`.** -/
theorem prob_not_TND_le [Fintype K] [SampleableType E] :
    Pr{let t ← $ᵗ E}[¬ TND (K := K) t] ≤
      ((26 * 2 ^ 25 + 4 * Fintype.card K : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  gcongr
  exact_mod_cast card_not_TND_le

/-- **`goodT` fails with probability at most `2^-165 + 2^-125`** at our sizes. -/
theorem prob_not_goodT_bits [Fintype K] [DecidableEq K] [FiniteDimensional K E]
    [SampleableType K] [SampleableType E] [SampleableType Γ₁] [Fintype Γ₁] [SampleableType Γ₂]
    [Fintype Γ₂] [SampleableType Γw]
    (P : Params E) (gK : Fin 4 → K[X]) (van : K[X]) (hvan0 : van ≠ 0)
    (hq : Fintype.card E = 2 ^ 192) (hK : Fintype.card K = 2 ^ 64) (hN : P.nCells = 2 ^ 24)
    (hdeg : van.natDegree ≤ 2 ^ 22) :
    Pr{let c ← $ᵗ (Chal E Γ₁ Γ₂ Γw)}[¬ goodT (K := K) P gK van c] ≤
      1 / 2 ^ 165 + 1 / 2 ^ 125 := by
  refine (prEvent_not_and_le _ (fun c => good P gK van c) (fun c => TND (K := K) c.1.1.2)).trans
    (add_le_add (joint_hgood_bits P gK van hvan0 hq hK hN hdeg) ?_)
  refine le_trans (le_of_eq (prEvent_uniform_fst (A := ((E × E × E) × E) × E)
    (fun x => ¬ TND (K := K) x.1.2))) ?_
  refine le_trans (le_of_eq (prEvent_uniform_fst (A := (E × E × E) × E)
    (fun y => ¬ TND (K := K) y.2))) ?_
  refine le_trans (le_of_eq (prEvent_uniform_snd (A := E × E × E)
    (fun t => ¬ TND (K := K) t))) ?_
  refine prob_not_TND_le.trans ?_
  rw [hq, hK]
  have h := HiddenLayout.natCast_div_le_natCast_div (a := 26 * 2 ^ 25 + 4 * 2 ^ 64)
    (b := 2 ^ 192) (c := 1) (d := 2 ^ 125) (by positivity) (by positivity) (by norm_num)
  convert h using 1
  norm_num

/-! ### The masks -/

/-- The copy cell's value at the four values: the first, plus the other three's part. -/
theorem cellAt_zero_eq (P : Params E) (a : Fin 4 → E) (t : E) :
    P.cellAt a t 0 = a 0 + ∑ j : Fin 3, (digit j.succ : E[X]).eval t * Fin.tail a j := by
  unfold Params.cellAt
  rw [Fin.sum_univ_succ]
  have h0 : shift P.θ 0 = 0 := rfl
  have hd : (digit 0 : E[X]) = 1 := rfl
  rw [h0, add_zero, hd, eval_one, one_mul]
  rfl

/-- **A monic quadratic in the first of four uniform values** (its other coefficients functions of
the other three) vanishes with probability at most `2/|E|`. -/
theorem prob_quad_le [SampleableType E] (u v w : (Fin 3 → E) → E) :
    Pr{let a ← $ᵗ (Fin 4 → E)}[(a 0 + u (Fin.tail a)) * (a 0 + v (Fin.tail a)) +
      w (Fin.tail a) = 0] ≤ 2 / (Fintype.card E : ℝ≥0∞) := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  let p : (Fin 3 → E) → E[X] := fun τ =>
    X ^ 2 + (C (u τ + v τ) * X + C (u τ * v τ + w τ))
  have hmon : ∀ τ, (p τ).Monic := fun τ =>
    monic_X_pow_add (degree_linear_le.trans_lt (by exact_mod_cast (by norm_num : (1 : ℕ) < 2)))
  have hdeg : ∀ τ, (p τ).natDegree ≤ 2 := fun τ => by
    show (X ^ 2 + (C (u τ + v τ) * X + C (u τ * v τ + w τ)) : E[X]).natDegree ≤ 2
    compute_degree
  have hev : ∀ τ r, (p τ).eval r = (r + u τ) * (r + v τ) + w τ := fun τ r => by
    simp only [p, eval_add, eval_pow, eval_mul, eval_X, eval_C]
    ring
  have hcard : (univ.filter fun a : Fin 4 → E =>
      (a 0 + u (Fin.tail a)) * (a 0 + v (Fin.tail a)) + w (Fin.tail a) = 0).card ≤
      2 * Fintype.card E ^ 3 := by
    have hsub : (univ.filter fun a : Fin 4 → E =>
        (a 0 + u (Fin.tail a)) * (a 0 + v (Fin.tail a)) + w (Fin.tail a) = 0) ⊆
        (univ : Finset (Fin 3 → E)).biUnion fun τ =>
          (univ.filter fun r : E => (p τ).eval r = 0).image
            fun r => (Fin.cons r τ : Fin 4 → E) := by
      intro a ha
      rw [mem_filter] at ha
      refine mem_biUnion.mpr ⟨Fin.tail a, mem_univ _, mem_image.mpr ⟨a 0,
        mem_filter.mpr ⟨mem_univ _, ?_⟩, Fin.cons_self_tail a⟩⟩
      rw [hev]
      exact ha.2
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    calc ∑ τ : Fin 3 → E, ((univ.filter fun r : E => (p τ).eval r = 0).image
          fun r => (Fin.cons r τ : Fin 4 → E)).card
        ≤ ∑ _τ : Fin 3 → E, 2 := sum_le_sum fun τ _ =>
          card_image_le.trans (card_filter_eval_le _ (hmon τ).ne_zero (hdeg τ))
      _ = 2 * Fintype.card E ^ 3 := by
          rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul, mul_comm]
  have hE : 0 < Fintype.card E := Fintype.card_pos
  rw [Fintype.card_fun, Fintype.card_fin]
  have h := HiddenLayout.natCast_div_le_natCast_div
    (a := (univ.filter fun a : Fin 4 → E =>
      (a 0 + u (Fin.tail a)) * (a 0 + v (Fin.tail a)) + w (Fin.tail a) = 0).card)
    (b := Fintype.card E ^ 4) (c := 2) (d := Fintype.card E) (by positivity) hE (by
      calc _ ≤ 2 * Fintype.card E ^ 3 * Fintype.card E := Nat.mul_le_mul_right _ hcard
        _ = 2 * Fintype.card E ^ 4 := by ring)
  convert h using 2

/-- **At a `goodT` challenge, masks make the claims degenerate with probability at most
`2/|E|`**: `vRows(t) ≠ 0` (`Exact`: the rows are its roots, where `van` vanishes, not at `t`), and
`claimDen` is a monic quadratic in the first of the four values, uniform in `E` (F1, the row
outside `K`). -/
theorem prob_not_claimsND_le [Fintype K] [DecidableEq K] [FiniteDimensional K E]
    [SampleableType K] [SampleableType E]
    (h3 : finrank K E = 3) (P : Params E) (hE : P.Exact) (stmt : Fin P.words → E)
    (gK : Fin 4 → K[X]) (van : K[X]) (hvan : ∀ x : P.T, aeval (rowPoly.eval (x : E)) van = 0)
    (hsat : P.Sat stmt (P.cells (committed gK van 0))) (c : Chal E Γ₁ Γ₂ Γw)
    (hc : goodT (K := K) P gK van c) :
    Pr{let m ← $ᵗ (Fin 4 → Fin 3 → K)}[¬ ClaimsND (K := K) P gK van c m] ≤
      2 / (Fintype.card E : ℝ≥0∞) := by
  classical
  obtain ⟨⟨hg, -, -⟩, hT⟩ := hc
  -- `vRows(t) ≠ 0`
  have hrows : P.vRows.eval c.1.1.2 ≠ 0 := by
    intro h
    rw [hE.rows, eval_prod, prod_eq_zero_iff] at h
    obtain ⟨x, -, hx⟩ := h
    rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hx
    exact hg.2.2 (hx ▸ hvan x)
  -- the event, on the five values
  have hmono : Pr{let m ← $ᵗ (Fin 4 → Fin 3 → K)}[¬ ClaimsND (K := K) P gK van c m] ≤
      Pr{let v ← redMsgs P gK van c.1.1.2 <$> ($ᵗ (Fin 4 → Fin 3 → K))}[
        P.claimDen c.1.1.1.1 c.1.1.1.2.1 c.1.1.2 v.1 v.2 = 0] := by
    rw [prEvent_map]
    refine prEvent_mono _ _ _ fun m hm => ?_
    by_contra h
    exact hm ⟨hT, mul_ne_zero h hrows⟩
  refine hmono.trans ?_
  -- F1: the values are uniform in `E`
  let inK : E → Bool := fun e => decide (e ∈ Set.range (algebraMap K E))
  have hinK : ∀ e, inK e = true ↔ e ∈ Set.range (algebraMap K E) := fun e => by simp [inK]
  have heq := redMsgs_evalDistEq P h3 hE stmt gK van hvan hsat inK hinK
    (fun t => P.sigmaPoly.eval t) (fun _ => rfl) c.1.1.1 c.1.1.2 hg
  rw [heq.prEvent_eq]
  have hnot : inK (rowOf c.1.1.2) = false := by
    simpa [inK] using hT.2
  simp only [simRed, simValuesC, hnot, Bool.false_eq_true, ite_false, prEvent_map]
  refine le_trans (prEvent_mono _ _ _ fun a ha => ?_)
    (prob_quad_le
      (fun τ => c.1.1.1.1 + ∑ j : Fin 3, (digit j.succ : E[X]).eval c.1.1.2 * τ j +
        c.1.1.1.2.1 * c.1.1.2)
      (fun τ => c.1.1.1.1 + ∑ j : Fin 3, (digit j.succ : E[X]).eval c.1.1.2 * τ j +
        c.1.1.1.2.1 * P.sigmaPoly.eval c.1.1.2)
      (fun _ => P.vCells.eval c.1.1.2))
  refine Eq.trans ?_ ha
  unfold Params.claimDen
  rw [cellAt_zero_eq]
  ring

end Nondeg

/-! ## The joint model, the claims required off the degenerate masks -/

section Model

variable {K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂ : Type} [Field K] [Field E] [Algebra K E]
  [DecidableEq E] [CharP E 2] [Fintype E]
  [Fintype ι₁] [DecidableEq ι₁] [Fintype Y₁] [DecidableEq Y₁] [Fintype Q₁] [DecidableEq Q₁]
  [Fintype ι₂] [DecidableEq ι₂] [Fintype Y₂] [DecidableEq Y₂] [Fintype Q₂] [DecidableEq Q₂]
  [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K] [SampleableType E]
  [SampleableType (ι₁ → Y₁ → K)] [SampleableType (ι₂ → Y₂ → K)]

/-- **Joint honest-verifier zero knowledge, the honest tables' claims the verifier's off the
degenerate masks**: at every `goodT` challenge the honest view under uniform masks and paddings is
within `2/|E|` of `jointSimV` (`VClose`). -/
theorem joint_hzkV_nd (h3 : finrank K E = 3) (P : Params E) (hE : P.Exact)
    (stmt : Fin P.words → E)
    (gK : Fin 4 → K[X]) (van : K[X]) (hvan : ∀ x : P.T, aeval (rowPoly.eval (x : E)) van = 0)
    (hsat : P.Sat stmt (P.cells (committed gK van 0)))
    (inK : E → Bool) (hinK : ∀ e, inK e = true ↔ e ∈ Set.range (algebraMap K E))
    (sigmaAt : E → E) (hsig : ∀ t, sigmaAt t = P.sigmaPoly.eval t)
    (wir : Chal E Γ₁ Γ₂ Γw → W)
    (S₁ : SecretOpening K E (ChV E Γ₁ Γ₂ Γw) ι₁ Y₁ Q₁ O₁)
    (S₂ : SecretOpening K E (ChV E Γ₁ Γ₂ Γw) ι₂ Y₂ Q₂ O₂)
    (hS₁ : S₁.Conditions) (hS₂ : S₂.Conditions)
    (T₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₁ → Y₁ → K)
    (T₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₂ → Y₂ → K)
    (cl₁ : Chal E Γ₁ Γ₂ Γw → Vals E → Fin S₁.m → E)
    (cl₂ : Chal E Γ₁ Γ₂ Γw → Vals E → Fin S₂.m → E)
    (hT₁ : ∀ c, good P gK van c → ∀ m, ClaimsND (K := K) P gK van c m →
      S₁.claims (c, redMsgs P gK van c.1.1.2 m) (T₁ c m) = cl₁ c (redMsgs P gK van c.1.1.2 m))
    (hT₂ : ∀ c, good P gK van c → ∀ m, ClaimsND (K := K) P gK van c m →
      S₂.claims (c, redMsgs P gK van c.1.1.2 m) (T₂ c m) = cl₂ c (redMsgs P gK van c.1.1.2 m))
    (simT₁ : Chal E Γ₁ Γ₂ Γw → Vals E → ι₁ → Y₁ → K)
    (simT₂ : Chal E Γ₁ Γ₂ Γw → Vals E → ι₂ → Y₂ → K)
    (hsimT₁ : ∀ c, good P gK van c → ∀ v, S₁.claims (c, v) (simT₁ c v) = cl₁ c v)
    (hsimT₂ : ∀ c, good P gK van c → ∀ v, S₂.claims (c, v) (simT₂ c v) = cl₂ c v) :
    ∀ c, goodT (K := K) P gK van c →
      VClose ((modelV P gK van wir T₁ T₂ S₁ S₂).view c <$>
          ($ᵗ ((Fin 4 → Fin 3 → K) × (ι₁ → Y₁ → K) × (ι₂ → Y₂ → K))))
        (jointSimV inK sigmaAt wir S₁ S₂ simT₁ simT₂ c) (2 / (Fintype.card E : ℝ≥0∞)) := by
  intro c hc
  have hc₀ := hc.1
  exact view_vclose (modelV P gK van wir T₁ T₂ S₁ S₂)
    (fun c => simRed (K := K) inK sigmaAt c.1.1.2) (fun c v => (v, simT₁ c v))
    (fun c v => (v, simT₂ c v)) c (ClaimsND (K := K) P gK van c) _
    (prob_not_claimsND_le h3 P hE stmt gK van hvan hsat c hc)
    (redMsgs_evalDistEq P h3 hE stmt gK van hvan hsat inK hinK sigmaAt hsig c.1.1.1 c.1.1.2
      hc₀.1)
    (hides_pair h3 S₁ hS₁ lamV₁ phiV₁ c fun _ => hc₀.2.1)
    (hides_pair h3 S₂ hS₂ lamV₂ phiV₂ c fun _ => hc₀.2.2)
    (fun m hm => by
      show (redMsgs P gK van c.1.1.2 m, S₁.claims (c, redMsgs P gK van c.1.1.2 m)
          (simT₁ c (redMsgs P gK van c.1.1.2 m))) =
        (redMsgs P gK van c.1.1.2 m, S₁.claims (c, redMsgs P gK van c.1.1.2 m) (T₁ c m))
      rw [hsimT₁ c hc₀, hT₁ c hc₀ m hm])
    (fun m hm => by
      show (redMsgs P gK van c.1.1.2 m, S₂.claims (c, redMsgs P gK van c.1.1.2 m)
          (simT₂ c (redMsgs P gK van c.1.1.2 m))) =
        (redMsgs P gK van c.1.1.2 m, S₂.claims (c, redMsgs P gK van c.1.1.2 m) (T₂ c m))
      rw [hsimT₂ c hc₀, hT₂ c hc₀ m hm])

variable [SampleableType Γ₁] [Fintype Γ₁] [SampleableType Γ₂] [Fintype Γ₂] [SampleableType Γw]

/-- **`JointHVZKε`** for a prover that is the model `modelV`, the honest tables' claims required
off the degenerate masks (`ClaimsND`), at our sizes: the good challenges `goodT`,
`εhv = 2^-165 + 2^-125`, `εz = 2/2^192`. -/
theorem jointHVZKε_of_linkV {I Ob Mm Xt : Type} [DecidableEq I] [Inhabited I]
    [SampleableType Ob] [Inhabited Ob] [DecidableEq Xt]
    (P : Proto (Rand K ι₁ Y₁ ι₂ Y₂) I Ob Mm (Fin 2) Xt)
    (h3 : finrank K E = 3) (P₀ : Params E) (hE : P₀.Exact) (stmt : Fin P₀.words → E)
    (gK : Fin 4 → K[X]) (van : K[X]) (hvan : ∀ x : P₀.T, aeval (rowPoly.eval (x : E)) van = 0)
    (hsat : P₀.Sat stmt (P₀.cells (committed gK van 0))) (hvan0 : van ≠ 0)
    (hq : Fintype.card E = 2 ^ 192) (hK : Fintype.card K = 2 ^ 64) (hN : P₀.nCells = 2 ^ 24)
    (hdeg : van.natDegree ≤ 2 ^ 22)
    (inK : E → Bool) (hinK : ∀ e, inK e = true ↔ e ∈ Set.range (algebraMap K E))
    (sigmaAt : E → E) (hsig : ∀ t, sigmaAt t = P₀.sigmaPoly.eval t)
    (wir : Chal E Γ₁ Γ₂ Γw → W)
    (S₁ : SecretOpening K E (ChV E Γ₁ Γ₂ Γw) ι₁ Y₁ Q₁ O₁)
    (S₂ : SecretOpening K E (ChV E Γ₁ Γ₂ Γw) ι₂ Y₂ Q₂ O₂)
    (hS₁ : S₁.Conditions) (hS₂ : S₂.Conditions)
    (T₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₁ → Y₁ → K)
    (T₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₂ → Y₂ → K)
    (cl₁ : Chal E Γ₁ Γ₂ Γw → Vals E → Fin S₁.m → E)
    (cl₂ : Chal E Γ₁ Γ₂ Γw → Vals E → Fin S₂.m → E)
    (hT₁ : ∀ c, good P₀ gK van c → ∀ m, ClaimsND (K := K) P₀ gK van c m →
      S₁.claims (c, redMsgs P₀ gK van c.1.1.2 m) (T₁ c m) = cl₁ c (redMsgs P₀ gK van c.1.1.2 m))
    (hT₂ : ∀ c, good P₀ gK van c → ∀ m, ClaimsND (K := K) P₀ gK van c m →
      S₂.claims (c, redMsgs P₀ gK van c.1.1.2 m) (T₂ c m) = cl₂ c (redMsgs P₀ gK van c.1.1.2 m))
    (simT₁ : Chal E Γ₁ Γ₂ Γw → Vals E → ι₁ → Y₁ → K)
    (simT₂ : Chal E Γ₁ Γ₂ Γw → Vals E → ι₂ → Y₂ → K)
    (hsimT₁ : ∀ c, good P₀ gK van c → ∀ v, S₁.claims (c, v) (simT₁ c v) = cl₁ c v)
    (hsimT₂ : ∀ c, good P₀ gK van c → ∀ v, S₂.claims (c, v) (simT₂ c v) = cl₂ c v)
    (lk : LinkV P P₀ gK van wir T₁ T₂ S₁ S₂)
    (hch : lk.chOf <$> uniformList Ob P.n =ᵈ ($ᵗ (Chal E Γ₁ Γ₂ Γw))) :
    Deployed.JointHVZKε P
      (fun σ => lk.out σ <$> jointSimV inK sigmaAt wir S₁ S₂ simT₁ simT₂ (lk.chOf σ))
      (fun σ => goodT (K := K) P₀ gK van (lk.chOf σ)) (1 / 2 ^ 165 + 1 / 2 ^ 125)
      (2 / 2 ^ 192) :=
  ⟨hzk_of_factor_vclose P lk.chOf (modelV P₀ gK van wir T₁ T₂ S₁ S₂).view lk.out lk.hview
      (jointSimV inK sigmaAt wir S₁ S₂ simT₁ simT₂) (goodT (K := K) P₀ gK van) _
      (fun c hc => (joint_hzkV_nd h3 P₀ hE stmt gK van hvan hsat inK hinK sigmaAt hsig wir S₁ S₂
        hS₁ hS₂ T₁ T₂ cl₁ cl₂ hT₁ hT₂ simT₁ simT₂ hsimT₁ hsimT₂ c hc).mono
        (le_of_eq (by rw [hq]; norm_num))),
    hgood_of_uniform P.n lk.chOf hch (goodT (K := K) P₀ gK van) _
      (prob_not_goodT_bits P₀ gK van hvan0 hq hK hN hdeg)⟩

end Model

end Instance

end QuotientZk

/-! ## Axioms -/

/-- info: 'QuotientZk.zk_rom_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.zk_rom_approx

/--
info: 'QuotientZk.DRpm.zk_rpm_skel_approx' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms QuotientZk.DRpm.zk_rpm_skel_approx

/--
info: 'QuotientZk.Instance.jointHVZKε_of_linkV' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms QuotientZk.Instance.jointHVZKε_of_linkV
