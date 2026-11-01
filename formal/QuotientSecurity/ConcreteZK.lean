-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/ConcreteZK.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Concrete
import QuotientSecurity.CompletenessProb

/-!
# Zero knowledge on the instance

The zero knowledge theorem asks for a field `K` under `E` of degree 3 and a nonzero polynomial
over `K` vanishing on the rows of the row polynomial's values. On the instance of a Cantor basis
that lies in `K`, the digit `w_n` is that polynomial; and every field of `2^192` elements has
such a `K`, of `2^64` elements.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp Polynomial Module NNReal

namespace QuotientSecurity

theorem digitPoly_map {K E : Type*} [Field K] [Field E] (f : K →+* E) (k : ℕ) :
    (digitPoly k : K[X]).map f = digitPoly k := by
  induction k with
  | zero => simp [digitPoly]
  | succ k ih => simp [digitPoly, ih]

section Instance

variable {K E : Type} [Field K] [Field E] [Algebra K E] [DecidableEq E] [CharP E 2] [Fintype E]
variable [CharP K 2] {H : Type} [SampleableType E] [SampleableType H] [Fintype H] [DecidableEq H]
variable [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K]
variable {N : ℕ} (BK : CantorBasis K N) {n : ℕ} (hm : n + 2 ≤ N)
  (σ : Equiv.Perm (Fin (n + 2) → Bool)) (words : ℕ)
  (wordSum : Fin words → ((Fin (n + 2) → Bool) → E) →ₗ[E] E) (pub : E → E[X])
  (hPub : ∀ (γ : E) (w : (Fin (n + 2) → Bool) → E),
    ∑ x, (pub γ).eval ((BK.map (algebraMap K E)).point x) * w x
      = ∑ J : Fin words, γ ^ (J : ℕ) * wordSum J w)

/-- The mask's vanishing polynomial vanishes where the theorem asks. -/
theorem ofCantor_van
    (x : (Params.ofCantor (BK.map (algebraMap K E)) hm σ words wordSum pub hPub).T) :
    aeval (rowPoly.eval (x : E)) (digitPoly n : K[X]) = 0 := by
  obtain ⟨y, -, hy⟩ := Finset.mem_image.mp x.2
  rw [← eval_map_algebraMap, digitPoly_map, digitPoly_eval, rowPoly_eval,
    ← Function.iterate_add_apply, ← hy]
  exact (BK.map (algebraMap K E)).iterate_point hm _

/-- **Zero knowledge on the instance**: `zeroKnowledge` with its hypotheses on the vanishing
polynomials met. What is left is a satisfying witness over `K` and the oracle's state. -/
theorem zeroKnowledge_ofCantor (h3 : finrank K E = 3)
    (c₀ : (ofFn (ZAnswer (Params.ofCantor (BK.map (algebraMap K E)) hm σ words wordSum pub hPub)
      H)).QueryCache) (stmt : Fin words → E)
    (U : Finset H) (hU : ∀ c₁, c₁ ∉ U → Fresh c₀ stmt c₁) (gK : Fin 4 → K[X])
    (hsat : (Params.ofCantor (BK.map (algebraMap K E)) hm σ words wordSum pub hPub).Sat stmt
      ((Params.ofCantor (BK.map (algebraMap K E)) hm σ words wordSum pub hPub).cells
        (committed gK (digitPoly n) 0)))
    (S : Outcome (E := E) H × (ofFn (ZAnswer (Params.ofCantor (BK.map (algebraMap K E)) hm σ
      words wordSum pub hPub) H)).QueryCache → Prop) :
    Pr{let x ← realNI c₀ stmt gK (digitPoly n)}[S x] ≤ Pr{let x ← simNI (K := K) c₀ stmt}[S x]
        + zkBound (Params.ofCantor (BK.map (algebraMap K E)) hm σ words wordSum pub hPub)
          (digitPoly n : K[X]) U ∧
      Pr{let x ← simNI (K := K) c₀ stmt}[S x] ≤ Pr{let x ← realNI c₀ stmt gK (digitPoly n)}[S x]
        + zkBound (Params.ofCantor (BK.map (algebraMap K E)) hm σ words wordSum pub hPub)
          (digitPoly n : K[X]) U :=
  zeroKnowledge h3 (Params.ofCantor_exact _ hm σ words wordSum pub hPub) c₀ stmt U hU gK
    (digitPoly n) (digitPoly_monic_natDegree n).1.ne_zero
    (ofCantor_van BK hm σ words wordSum pub hPub) hsat S

end Instance

/-- At `2^22` rows over a field of `2^192` elements, the challenges' part of the bound is below
`2^-128`. -/
theorem zkError_ofCantor {K E : Type} [Field K] [Field E] [Algebra K E] [DecidableEq E]
    [CharP E 2] [Fintype E] [CharP K 2] [SampleableType E] [Fintype K] [DecidableEq K]
    [FiniteDimensional K E] [SampleableType K] {N : ℕ} (BK : CantorBasis K N) (hm : 22 + 2 ≤ N)
    (σ : Equiv.Perm (Fin (22 + 2) → Bool)) (words : ℕ)
    (wordSum : Fin words → ((Fin (22 + 2) → Bool) → E) →ₗ[E] E) (pub : E → E[X])
    (hPub : ∀ (γ : E) (w : (Fin (22 + 2) → Bool) → E),
      ∑ x, (pub γ).eval ((BK.map (algebraMap K E)).point x) * w x
        = ∑ J : Fin words, γ ^ (J : ℕ) * wordSum J w)
    (hq : Fintype.card E = 2 ^ 192) :
    zkError (Params.ofCantor (BK.map (algebraMap K E)) hm σ words wordSum pub hPub)
      (digitPoly 22 : K[X]) ≤ 1 / 2 ^ 128 :=
  zkError_le hq (Params.ofCantor_nCells _ hm σ words wordSum pub hPub) _
    (digitPoly_monic_natDegree 22).2.le

/-- **Completeness on the instance, in bits.** At `2^22` rows over a field of `2^192` elements,
with row polynomials of degree at most `2^23` and the public weight's at most `2^24 + 9 * 2^10`,
the honest prover's proof gets a false verdict with probability at most `2 / 2^128` plus the
fraction of handles the oracle was asked about. -/
theorem completeness_ofCantor {K E : Type} [Field K] [Field E] [Algebra K E] [DecidableEq E]
    [CharP E 2] [Fintype E] [CharP K 2] [SampleableType E] [Fintype K] [DecidableEq K]
    [FiniteDimensional K E] [SampleableType K] {H : Type} [SampleableType H] [Fintype H]
    [DecidableEq H] {N : ℕ} (BK : CantorBasis K N) (hm : 22 + 2 ≤ N)
    (σ : Equiv.Perm (Fin (22 + 2) → Bool))
    (wordSum : Fin 8 → ((Fin (22 + 2) → Bool) → E) →ₗ[E] E) (pub : E → E[X])
    (hPub : ∀ (γ : E) (w : (Fin (22 + 2) → Bool) → E),
      ∑ x, (pub γ).eval ((BK.map (algebraMap K E)).point x) * w x
        = ∑ J : Fin 8, γ ^ (J : ℕ) * wordSum J w)
    (hd : ∀ γ, (pub γ).natDegree ≤ 2 ^ 24 + 9 * 2 ^ 10)
    (hq : Fintype.card E = 2 ^ 192)
    (c₀ : (ofFn (ZAnswer (Params.ofCantor (BK.map (algebraMap K E)) hm σ 8 wordSum pub hPub)
      H)).QueryCache) (stmt : Fin 8 → E)
    (U : Finset H) (hU : ∀ c₁, c₁ ∉ U → Fresh c₀ stmt c₁) (gK : Fin 4 → K[X])
    (hgK : ∀ j, (gK j).natDegree ≤ 2 ^ 23)
    (hsat : (Params.ofCantor (BK.map (algebraMap K E)) hm σ 8 wordSum pub hPub).Sat stmt
      ((Params.ofCantor (BK.map (algebraMap K E)) hm σ 8 wordSum pub hPub).cells
        (committed gK (digitPoly 22) 0))) :
    Pr{let o ← realNI c₀ stmt gK (digitPoly 22)}[o.1.verdict = false]
      ≤ (U.card : ENNReal) / (Fintype.card H : ENNReal)
        + 2 * (((1 / 2 ^ 128 : ℝ≥0) : ℝ≥0) : ENNReal) := by
  have hdeg : (digitPoly 22 : K[X]).natDegree = 2 ^ 22 := (digitPoly_monic_natDegree 22).2
  have hg : ∀ m j, (committed (E := E) gK (digitPoly 22) m j).natDegree ≤ (Params.ofCantorBounds (BK.map (algebraMap K E)) hm σ 8 wordSum pub hPub _ hd).witness := by
    intro m j
    refine (natDegree_committed_le gK _ m j).trans (max_le (hgK j) ?_)
    rw [hdeg]
    show 2 ^ 22 + 2 ≤ 2 ^ (22 + 1)
    norm_num
  have h := completeness_prob (Params.ofCantor_exact _ hm σ 8 wordSum pub hPub) c₀ stmt U hU gK
    (digitPoly 22) (digitPoly_monic_natDegree 22).1.ne_zero
    (ofCantor_van BK hm σ 8 wordSum pub hPub) hsat
    (cantorCells (BK.map (algebraMap K E)) hm fun _ => false) (Params.ofCantorBounds (BK.map (algebraMap K E)) hm σ 8 wordSum pub hPub _ hd) hg
  have e1 : (zkError (Params.ofCantor (BK.map (algebraMap K E)) hm σ 8 wordSum pub hPub) (digitPoly 22 : K[X]) : ENNReal) ≤ ((1 / 2 ^ 128 : ℝ≥0) : ENNReal) :=
    ENNReal.coe_le_coe.mpr (zkError_ofCantor BK hm σ 8 wordSum pub hPub hq)
  have hpos : 0 < Fintype.card E := Fintype.card_pos
  have e2 : ((Params.ofCantorBounds (BK.map (algebraMap K E)) hm σ 8 wordSum pub hPub _ hd).identity : ENNReal) / (Fintype.card E : ENNReal)
      ≤ ((1 / 2 ^ 128 : ℝ≥0) : ENNReal) := by
    have hid : (Params.ofCantorBounds (BK.map (algebraMap K E)) hm σ 8 wordSum pub hPub _ hd).identity ≤ 2 ^ 29 :=
      Params.ofCantor_identity (BK.map (algebraMap K E)) hm σ wordSum pub hPub hd
    have hle := div_le_two_pow hpos (a := (Params.ofCantorBounds (BK.map (algebraMap K E)) hm σ 8 wordSum pub hPub _ hd).identity) (by
      rw [hq]; exact (Nat.mul_le_mul_right (2 ^ 128) hid).trans (by norm_num))
    have hc : ((Params.ofCantorBounds (BK.map (algebraMap K E)) hm σ 8 wordSum pub hPub _ hd).identity : ENNReal) / (Fintype.card E : ENNReal)
        = ((((Params.ofCantorBounds (BK.map (algebraMap K E)) hm σ 8 wordSum pub hPub _ hd).identity : ℝ≥0) / (Fintype.card E : ℝ≥0) : ℝ≥0) : ENNReal) := by
      rw [ENNReal.coe_div (by exact_mod_cast hpos.ne')]
      simp
    rw [hc]
    exact ENNReal.coe_le_coe.mpr hle
  refine h.trans ?_
  unfold zkBound
  calc (zkError (Params.ofCantor (BK.map (algebraMap K E)) hm σ 8 wordSum pub hPub) (digitPoly 22 : K[X]) : ENNReal)
          + (U.card : ENNReal) / (Fintype.card H : ENNReal)
          + ((Params.ofCantorBounds (BK.map (algebraMap K E)) hm σ 8 wordSum pub hPub _ hd).identity : ENNReal) / (Fintype.card E : ENNReal)
        ≤ ((1 / 2 ^ 128 : ℝ≥0) : ENNReal) + (U.card : ENNReal) / (Fintype.card H : ENNReal)
          + ((1 / 2 ^ 128 : ℝ≥0) : ENNReal) := by gcongr
    _ = _ := by ring

/-- **The fields exist**: a field of `2^192` elements is of degree 3 over one of `2^64`. -/
theorem exists_subfield {E : Type} [Field E] [Fintype E] [CharP E 2]
    (hE : Fintype.card E = 2 ^ 192) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : Algebra K E),
      CharP K 2 ∧ Fintype.card K = 2 ^ 64 ∧ finrank K E = 3 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Algebra (ZMod 2) E := ZMod.algebra E 2
  have : Fintype (GaloisField 2 64) := Fintype.ofFinite _
  have hK : Fintype.card (GaloisField 2 64) = 2 ^ 64 := by
    rw [Fintype.card_eq_nat_card]; exact GaloisField.card 2 64 (by norm_num)
  have hrE : Module.finrank (ZMod 2) E = 192 := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := E)
    rw [hE, ZMod.card] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  have hrK : Module.finrank (ZMod 2) (GaloisField 2 64) = 64 :=
    GaloisField.finrank 2 (by norm_num)
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2)
    (K := GaloisField 2 64) (L := E) (by rw [hrK, hrE]; norm_num)
  refine ⟨GaloisField 2 64, inferInstance, inferInstance, f.toRingHom.toAlgebra,
    inferInstance, hK, ?_⟩
  let _ : Algebra (GaloisField 2 64) E := f.toRingHom.toAlgebra
  have h := Module.card_eq_pow_finrank (K := GaloisField 2 64) (V := E)
  rw [hE, hK, ← pow_mul] at h
  have := Nat.pow_right_injective (le_refl 2) h
  omega

end QuotientSecurity
