-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Statement
import QuotientSecurity.CompletenessProb

/-!
# The reduction's completeness, at the deployed rejection

`quotient::protocol::reduce` rejects (`VerifyError::Degenerate`) when the product it inverts is
zero: every `1 + w_k(t)` for `k ≤ m + 1`, the copy identity's denominator `d d' + w_m(t)` and the
rows' polynomial at `t`. The honest prover (`prove_with_randomness`) also needs the sum's
polynomial to exist: no denominator `α + w(x) + β x` may vanish at a cell `x` (`batch_inverse`
of a zero would give garbage). This file proves, on F1's instance (`Instance`, `2^22` rows):

* `honest_accepts`: for a first message `g` whose cells satisfy the relation, at every
  challenge `(α, β, γ, t, ρ)` outside these two sets, the honest second message
  (`Params.honest`, the interpolated sum and the two quotients) with the honest values
  (`opened g t`, the wiring polynomial at `t`) is accepted (`Params.Accepts`, which
  `claims_iff_accepts_ofCantor` turns into the four claims on the tables), and the Rust's own
  check passes (`rustCheck_honest`). `γ` and `ρ` are free.
* `card_bad_le`, `bad_fraction_le`: the bad challenges number at most `(17 · 2^24 + 8) q^2` of
  the `q^3` triples `(α, β, t)`: `2 · 2^24 · q` pairs `(α, β)` (for each cell and each `β`, one
  `α` per denominator), then, for a good pair, at most `11 · 2^24 + 8` values of `t` where the
  product of the copy denominator and the rows' polynomial (`rejectPoly`, of degree at most the
  identities' bound) vanishes and `2^26 − 1` where some `1 + w_k(t)`, `k ≤ 25`, does. Over a
  field of `2^192` elements, a uniform `(α, β, t)` is bad with probability at most
  `(17 · 2^24 + 8) / 2^192 < 2^-163`.

The counting is done for any parameters (`card_badP_le`): on the instance's own parameters the
elaborator would unfold their `2^22`-element sets.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial
open scoped ENNReal

namespace Completeness

open QuotientSecurity

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]

/-! ## For any parameters -/

section General

variable (P : Params F)

/-- **The honest prover's own failure**: a denominator of the sum's values vanishes at a cell. -/
def BadABP (g : Fin 4 → F[X]) (α β : F) : Prop :=
  ∃ i : P.T × Fin 4, α + P.cells g i + β * P.pt i = 0 ∨ α + P.cells g i + β * P.pt (P.σ i) = 0

/-- **The degenerate `t`** of an honest run: some `1 + w_k(t)` (`k < 26`) or the product the
verifier inverts on the honest values vanishes. -/
def DegenerateP (g : Fin 4 → F[X]) (α β t : F) : Prop :=
  (∃ k : Fin (22 + 2 + 1 + 1), 1 + sq^[(k : ℕ)] t = 0) ∨ (rejectPoly P g α β).eval t = 0

open Classical in
/-- The pairs `(α, β)` at which a denominator vanishes at a cell: for each cell and each `β`,
one `α` per denominator. -/
theorem card_badABP_le (g : Fin 4 → F[X]) :
    (univ.filter fun p : F × F => BadABP P g p.1 p.2).card ≤ 2 * P.nCells * Fintype.card F := by
  have hsub : (univ.filter fun p : F × F => BadABP P g p.1 p.2) ⊆
      (univ : Finset (P.T × Fin 4)).biUnion fun i =>
        (univ.image fun β : F => (-(P.cells g i + β * P.pt i), β)) ∪
          (univ.image fun β : F => (-(P.cells g i + β * P.pt (P.σ i)), β)) := by
    intro p hp
    obtain ⟨i, hi⟩ := (mem_filter.mp hp).2
    refine mem_biUnion.mpr ⟨i, mem_univ _, ?_⟩
    rcases hi with h | h
    · refine mem_union_left _ (mem_image.mpr ⟨p.2, mem_univ _, ?_⟩)
      refine Prod.ext ?_ rfl
      show -(P.cells g i + p.2 * P.pt i) = p.1
      linear_combination -h
    · refine mem_union_right _ (mem_image.mpr ⟨p.2, mem_univ _, ?_⟩)
      refine Prod.ext ?_ rfl
      show -(P.cells g i + p.2 * P.pt (P.σ i)) = p.1
      linear_combination -h
  refine (card_le_card hsub).trans ((card_biUnion_le).trans ?_)
  have hterm : ∀ i : P.T × Fin 4,
      ((univ.image fun β : F => (-(P.cells g i + β * P.pt i), β)) ∪
        (univ.image fun β : F => (-(P.cells g i + β * P.pt (P.σ i)), β))).card
        ≤ 2 * Fintype.card F := fun i =>
    (card_union_le _ _).trans (by
      have h1 := card_image_le (s := (univ : Finset F))
        (f := fun β : F => (-(P.cells g i + β * P.pt i), β))
      have h2 := card_image_le (s := (univ : Finset F))
        (f := fun β : F => (-(P.cells g i + β * P.pt (P.σ i)), β))
      rw [card_univ] at h1 h2
      omega)
  refine (sum_le_sum fun i _ => hterm i).trans (le_of_eq ?_)
  rw [sum_const, card_univ, smul_eq_mul, Params.nCells]
  ring

/-- `1 + w_k` as a polynomial: monic of degree `2^k`. -/
theorem one_add_digitPoly (k : ℕ) :
    (1 + digitPoly k : F[X]) ≠ 0 ∧ (1 + digitPoly k : F[X]).natDegree ≤ 2 ^ k := by
  obtain ⟨hmon, hdeg⟩ := digitPoly_monic_natDegree (F := F) k
  have hpos : 0 < (digitPoly k : F[X]).natDegree := by rw [hdeg]; positivity
  have hm : (1 + digitPoly k : F[X]).Monic := by
    rw [add_comm]
    exact hmon.add_of_left (degree_lt_degree (by rw [natDegree_one]; exact hpos))
  refine ⟨hm.ne_zero, ?_⟩
  rw [add_comm, natDegree_add_eq_left_of_natDegree_lt (by rw [natDegree_one]; exact hpos), hdeg]

open Classical in
/-- The roots of a nonzero polynomial of degree at most `d`, as a set of points: at most `d`. -/
theorem card_filter_eval_eq_zero_le (p : F[X]) (hp : p ≠ 0) {d : ℕ} (hd : p.natDegree ≤ d) :
    (univ.filter fun t : F => p.eval t = 0).card ≤ d := by
  have hsub : (univ.filter fun t : F => p.eval t = 0) ⊆ p.roots.toFinset := by
    intro t ht
    rw [mem_filter] at ht
    rw [Multiset.mem_toFinset, mem_roots hp, IsRoot.def]
    exact ht.2
  exact (card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans ((card_roots' _).trans hd))

open Classical in
/-- At a good pair `(α, β)`, at most `D + 2^26` values of `t` are degenerate, `D` a bound on the
identities' degree for a first message within the bounds. -/
theorem card_degenerateP_le (hE : P.Exact) (Bd : P.Bounds) (g : Bd.Msg₁) (α β : F)
    (hab : ¬ BadABP P g.1 α β) {D : ℕ} (hD : Bd.identity ≤ D) (i₀ : P.T × Fin 4) :
    (univ.filter fun t : F => DegenerateP P g.1 α β t).card ≤ D + 2 ^ 26 := by
  have hd : ∀ i, α + P.cells g.1 i + β * P.pt i ≠ 0 := fun i h => hab ⟨i, Or.inl h⟩
  have hd' : ∀ i, α + P.cells g.1 i + β * P.pt (P.σ i) ≠ 0 := fun i h => hab ⟨i, Or.inr h⟩
  have hR0 := rejectPoly_ne_zero hE g.1 α β i₀ (hd i₀) (hd' i₀)
  have hRdeg : (rejectPoly P g.1 α β).natDegree ≤ D := (natDegree_rejectPoly_le Bd g α β).trans hD
  have h1 := card_filter_eval_eq_zero_le (rejectPoly P g.1 α β) hR0 hRdeg
  have hw : ∀ k : Fin (22 + 2 + 1 + 1),
      (univ.filter fun t : F => 1 + sq^[(k : ℕ)] t = 0).card ≤ 2 ^ (k : ℕ) := fun k => by
    have := card_filter_eval_eq_zero_le (1 + digitPoly k : F[X]) (one_add_digitPoly k).1
      (one_add_digitPoly k).2
    simpa [digitPoly_eval] using this
  have hsub : (univ.filter fun t : F => DegenerateP P g.1 α β t) ⊆
      ((univ : Finset (Fin (22 + 2 + 1 + 1))).biUnion fun k =>
        univ.filter fun t : F => 1 + sq^[(k : ℕ)] t = 0) ∪
        univ.filter fun t : F => (rejectPoly P g.1 α β).eval t = 0 := by
    intro t ht
    rcases (mem_filter.mp ht).2 with ⟨k, hk⟩ | h
    · exact mem_union_left _ (mem_biUnion.mpr ⟨k, mem_univ _, mem_filter.mpr ⟨mem_univ _, hk⟩⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, h⟩)
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  have h2 : ((univ : Finset (Fin (22 + 2 + 1 + 1))).biUnion fun k =>
      univ.filter fun t : F => 1 + sq^[(k : ℕ)] t = 0).card ≤ 2 ^ 26 :=
    card_biUnion_le.trans ((sum_le_sum fun k _ => hw k).trans (sum_two_pow_fin _).le)
  omega

open Classical in
/-- **The bad challenges of an honest run**, for any parameters: of the `q^3` triples
`(α, β, t)`, at most `(2 N + D + 2^26) q^2`. -/
theorem card_badP_le (hE : P.Exact) (Bd : P.Bounds) (g : Bd.Msg₁) {D : ℕ}
    (hD : Bd.identity ≤ D) (i₀ : P.T × Fin 4) :
    (univ.filter fun x : F × F × F =>
        BadABP P g.1 x.1 x.2.1 ∨ DegenerateP P g.1 x.1 x.2.1 x.2.2).card
      ≤ (2 * P.nCells + D + 2 ^ 26) * Fintype.card F ^ 2 := by
  set q := Fintype.card F
  have hsplit : (univ.filter fun x : F × F × F =>
      BadABP P g.1 x.1 x.2.1 ∨ DegenerateP P g.1 x.1 x.2.1 x.2.2) ⊆
      (univ.filter fun x : F × F × F => BadABP P g.1 x.1 x.2.1) ∪
        (univ.filter fun x : F × F × F =>
          ¬ BadABP P g.1 x.1 x.2.1 ∧ DegenerateP P g.1 x.1 x.2.1 x.2.2) := by
    intro x hx
    by_cases h : BadABP P g.1 x.1 x.2.1
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, h⟩)
    · rcases (mem_filter.mp hx).2 with h' | h'
      · exact absurd h' h
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, h, h'⟩)
  have hA : (univ.filter fun x : F × F × F => BadABP P g.1 x.1 x.2.1).card
      ≤ 2 * P.nCells * q * q := by
    have he : (univ.filter fun x : F × F × F => BadABP P g.1 x.1 x.2.1) =
        ((univ.filter fun p : F × F => BadABP P g.1 p.1 p.2) ×ˢ (univ : Finset F)).map
          (Equiv.prodAssoc F F F).toEmbedding := by
      ext ⟨a, b, t⟩
      simp
    rw [he, card_map, card_product, card_univ]
    exact Nat.mul_le_mul_right _ (card_badABP_le P g.1)
  have hB : (univ.filter fun x : F × F × F =>
      ¬ BadABP P g.1 x.1 x.2.1 ∧ DegenerateP P g.1 x.1 x.2.1 x.2.2).card
      ≤ q * q * (D + 2 ^ 26) := by
    have he : (univ.filter fun x : F × F × F =>
        ¬ BadABP P g.1 x.1 x.2.1 ∧ DegenerateP P g.1 x.1 x.2.1 x.2.2) =
        (univ : Finset (F × F)).biUnion fun p =>
          if BadABP P g.1 p.1 p.2 then ∅ else
            (univ.filter fun t : F => DegenerateP P g.1 p.1 p.2 t).map
              ⟨fun t => (p.1, p.2, t), fun t t' h => by simpa using h⟩ := by
      ext ⟨a, b, t⟩
      simp only [mem_filter, mem_univ, true_and, mem_biUnion]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨(a, b), ?_⟩
        simp only [h1, ↓reduceIte, mem_map, mem_filter, mem_univ, true_and]
        exact ⟨t, h2, rfl⟩
      · rintro ⟨⟨a', b'⟩, h⟩
        split_ifs at h with hb
        · simp at h
        · simp only [mem_map, mem_filter, mem_univ, true_and] at h
          obtain ⟨t', ht', he⟩ := h
          cases he
          exact ⟨hb, ht'⟩
    rw [he]
    refine card_biUnion_le.trans
      ((sum_le_sum (g := fun _ => D + 2 ^ 26) fun p _ => ?_).trans (le_of_eq ?_))
    · split_ifs with hb
      · simp
      · rw [card_map]
        exact card_degenerateP_le P hE Bd g p.1 p.2 hb hD i₀
    · rw [sum_const, card_univ, Fintype.card_prod, smul_eq_mul]
  refine (card_le_card hsplit).trans ((card_union_le _ _).trans ?_)
  calc _ ≤ 2 * P.nCells * q * q + q * q * (D + 2 ^ 26) := add_le_add hA hB
    _ = (2 * P.nCells + D + 2 ^ 26) * q ^ 2 := by ring

end General

namespace Reduction

variable (I : Instance F)

/-- **The honest prover's own failure** on the instance. -/
abbrev BadAB (g : Fin 4 → F[X]) (α β : F) : Prop := BadABP I.params g α β

/-- **The Rust verifier's check** on the values it received (`reduce`, `prefix[..] != 0`): every
`1 + w_k(t)` for `k ≤ m + 1 = 25`, the copy identity's denominator and the rows' polynomial at
`t` are nonzero. -/
def RustCheck (α β t : F) (a : Fin 4 → F) (s : F) : Prop :=
  (∀ k : Fin (22 + 2 + 1 + 1), 1 + sq^[(k : ℕ)] t ≠ 0) ∧
    I.params.claimDen α β t a s * I.params.vRows.eval t ≠ 0

/-- **The degenerate `t`** of an honest run on the instance. -/
abbrev Degenerate (g : Fin 4 → F[X]) (α β t : F) : Prop := DegenerateP I.params g α β t

theorem claimDen_honest (g : Fin 4 → F[X]) (α β t : F) :
    I.params.claimDen α β t (Params.opened g t) (I.params.sigmaPoly.eval t) *
        I.params.vRows.eval t = (rejectPoly I.params g α β).eval t :=
  (rejectPoly_eval (P := I.params) g α β t).symm

/-- On the honest values, the Rust check is the complement of `Degenerate`. -/
theorem rustCheck_honest (g : Fin 4 → F[X]) (α β t : F) :
    RustCheck I α β t (Params.opened g t) (I.params.sigmaPoly.eval t) ↔ ¬ Degenerate I g α β t := by
  unfold RustCheck Degenerate DegenerateP
  rw [claimDen_honest, not_or, not_exists]

/-- **Completeness of the reduction, pointwise.** For a first message whose cells satisfy the
relation, at every challenge where the honest sum exists and the Rust check passes, the honest
second message with the honest values is accepted, whatever `γ` and `ρ`. -/
theorem honest_accepts (stmt : Fin 8 → F) (g : Fin 4 → F[X])
    (hsat : I.Relation stmt (I.cellsOf g)) (α β γ t ρ : F) (hab : ¬ BadAB I g α β)
    (ht : ¬ Degenerate I g α β t) :
    I.params.Accepts stmt g (Params.honest I.params g α β γ) α β γ t (Params.opened g t)
      (I.params.sigmaPoly.eval t) ρ := by
  have hsat' := I.sat_of_relation stmt g hsat
  have hd : ∀ i, α + I.params.cells g i + β * I.params.pt i ≠ 0 := fun i h => hab ⟨i, Or.inl h⟩
  have hd' : ∀ i, α + I.params.cells g i + β * I.params.pt (I.params.σ i) ≠ 0 :=
    fun i h => hab ⟨i, Or.inr h⟩
  have hcons := Params.honest_consistent I.exact stmt g α β γ hsat' hd hd'
  refine Params.accepts_of_consistent (P := I.params) stmt g _ α β γ t ρ hcons ?_
  have e := rejectPoly_eval (P := I.params) g α β t
  rw [Params.cellAt_opened] at e
  rw [← e]
  exact fun h0 => ht (Or.inr h0)

open Classical in
/-- **The bad challenges of an honest run.** Of the `q^3` triples `(α, β, t)`, at most
`(17 · 2^24 + 8) q^2` make the honest prover fail (`BadAB`) or the Rust verifier reject
(`Degenerate`), for a first message of degree at most `2^23` (a masked witness's is
`2^22 + 2`). -/
theorem card_bad_le (g : Fin 4 → F[X]) (hg : ∀ j, (g j).natDegree ≤ 2 ^ 23) :
    (univ.filter fun x : F × F × F => BadAB I g x.1 x.2.1 ∨ Degenerate I g x.1 x.2.1 x.2.2).card
      ≤ (17 * 2 ^ 24 + 8) * Fintype.card F ^ 2 := by
  have hgm : ∀ j, (g j).natDegree ≤ I.bounds.witness := fun j => (hg j).trans (by
    show 2 ^ 23 ≤ 2 ^ (22 + 1)
    norm_num)
  have hD : I.bounds.identity ≤ 11 * 2 ^ 24 + 8 :=
    le_of_eq (Params.ofCantor_identity_eq I.basis le24 I.wiring _ _ I.pub_hPub
      (natDegree_membershipPub_le _ I.c))
  have h := card_badP_le I.params I.exact I.bounds ⟨g, hgm⟩ hD (I.cellEquiv fun _ => false)
  rw [I.nCells] at h
  exact h.trans (le_of_eq (by ring))

open Classical in
/-- **The probability of a degenerate honest run**, over uniform challenges in a field of
`2^192` elements: at most `(17 · 2^24 + 8) / 2^192`. -/
theorem bad_fraction_le (hq : Fintype.card F = 2 ^ 192) (g : Fin 4 → F[X])
    (hg : ∀ j, (g j).natDegree ≤ 2 ^ 23) :
    ((univ.filter fun x : F × F × F =>
        BadAB I g x.1 x.2.1 ∨ Degenerate I g x.1 x.2.1 x.2.2).card : ℝ≥0∞) /
        (Fintype.card (F × F × F) : ℝ≥0∞)
      ≤ (17 * 2 ^ 24 + 8 : ℝ≥0∞) / 2 ^ 192 := by
  have h := card_bad_le I g hg
  have hc : (Fintype.card (F × F × F) : ℝ≥0∞) = 2 ^ 192 * (2 ^ 192) ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_prod, hq]
    push_cast
    ring
  rw [hc]
  have h' : ((univ.filter fun x : F × F × F =>
      BadAB I g x.1 x.2.1 ∨ Degenerate I g x.1 x.2.1 x.2.2).card : ℝ≥0∞)
      ≤ (17 * 2 ^ 24 + 8) * (2 ^ 192) ^ 2 := by
    rw [hq] at h
    exact_mod_cast h
  calc _ ≤ (17 * 2 ^ 24 + 8) * (2 ^ 192) ^ 2 / (2 ^ 192 * (2 ^ 192) ^ 2) :=
        ENNReal.div_le_div_right h' _
    _ = (17 * 2 ^ 24 + 8 : ℝ≥0∞) / 2 ^ 192 :=
        ENNReal.mul_div_mul_right _ _ (by simp) (by simp)

/-- The number, below `2^-163`. -/
theorem bad_bound_lt : (17 * 2 ^ 24 + 8 : ℝ≥0∞) / 2 ^ 192 < 2⁻¹ ^ 163 := by
  have h1 : (17 * 2 ^ 24 + 8 : ℝ≥0∞) / 2 ^ 192 < 2 ^ 29 / 2 ^ 192 :=
    ENNReal.div_lt_div_right (by simp) (by simp) (by norm_num)
  have h2 : (2 ^ 29 : ℝ≥0∞) / 2 ^ 192 = 2⁻¹ ^ 163 := by
    have e : (2 : ℝ≥0∞) ^ 29 / 2 ^ 192 = (2 ^ 29 * 1) / (2 ^ 29 * 2 ^ 163) := by norm_num
    rw [e, ENNReal.mul_div_mul_left _ _ (by simp) (by simp), one_div, ENNReal.inv_pow]
  exact h2 ▸ h1

end Reduction

end Completeness
