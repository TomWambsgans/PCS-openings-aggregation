-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/Statement.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.SetupLemmas

/-!
# The statements

What is proved about the protocol `quotient::protocol` (`2^22` rows of χ gates, a field of `2^192`
elements), with every size discharged. The definitions
these theorems mention are in `Setup.lean`, which is short and has no proof in it.

**What is assumed.**
* The hash is a random oracle, used by this protocol only.
* The commitment is ideal. For soundness: binding, so a proof carries its polynomials, within
  the degrees its tables allow, and the oracle is asked about them. For zero knowledge: a
  commitment is a random handle and its openings reveal only whether the claims are true. These
  are two different idealizations, and no theorem here has both at once.

**What is not said.**
* That the circuit is the one of `quotient::circuit::membership`: the theorems are for every
  wiring and every weights, and with a degenerate circuit the relation holds of every statement.
  The Rust tests check that code's wiring is a permutation with no loop.
* That the Rust `reduce` is this verifier. `claims_iff_accepts_ofCantor` proves that four claims
  on committed tables, at given points with given values, are "accepts" here; that `reduce`
  forms those points and values is by review (the coordinate-by-coordinate comparison is written
  out above `claims_iff_accepts_ofCantor`, `Concrete.lean`). The verifier here accepts more than
  Rust's, which also rejects a challenge `t` with some `1 + w_k(t) = 0`.
* That the honest proof is accepted in the game of `soundness`. `completeness` is in the game of
  zero knowledge, with random handles; `honest_messages_fit` shows the honest messages are
  objects `soundness` speaks of, and no more.
* That a witness over `K` of degree at most `2^22` exists for a given statement: it is a
  hypothesis of zero knowledge and completeness.
* Anything about the commitment the Rust code uses. Its tables are not padded and its roots are
  deterministic, so the zero knowledge theorem does not apply to it as built.
* The adversary of `soundness` has no coins of its own; zero knowledge is for one proof, with a
  simulator that writes in the oracle's table and is not shown efficient.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp Polynomial Module NNReal

namespace QuotientSecurity

namespace Instance

/-! ## The setting is not empty -/

/-- Over every field of `2^192` elements there is a circuit, with any wiring and any weights. -/
theorem exists_instance {F : Type} [Field F] [CharP F 2] [Fintype F]
    (hq : Fintype.card F = 2 ^ 192) (wiring : Equiv.Perm (Fin (22 + 2) → Bool)) (c : ℕ → F) :
    ∃ I : Instance F, I.wiring = wiring ∧ I.c = c := by
  obtain ⟨B⟩ := exists_cantorBasis_big hq (22 + 2) (by norm_num) (by norm_num)
  exact ⟨⟨B, wiring, c⟩, rfl, rfl⟩

/-! ## Knowledge soundness -/

section Soundness

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable (I : Instance F)

/-- **Knowledge soundness.** Over a field of `2^192` elements, for every adversary making at
most `Q` oracle queries: run it, then the verifier on its output `r = (proof, verdict)`. The
probability that the verdict is true while the cells the proof's first message holds do not
satisfy the relation is at most `(Q + 3) / 2^128`. -/
theorem soundness (hq : Fintype.card F = 2 ^ 192) (adv : I.Adversary) (Q : ℕ)
    (hQ : IsTotalQueryBound adv Q) :
    Pr{let r ← (simulateQ randomOracle (experiment adv)).run' ∅}[
        r.2 = true ∧ ¬ I.Relation r.1.stmt (I.cellsOf r.1.g.1)]
      ≤ (Q + 3 : ENNReal) / 2 ^ 128 := by
  have h := knowledgeSoundness_membership I.basis le24 I.wiring _ I.c (invSeq_zero _)
    (fun d hd _ => invSeq_sum I.basis.β I.basis.zero d hd) hq adv Q hQ
  rw [bound_eq] at h
  exact le_trans (prEvent_mono _ _ _ fun r hr =>
    ⟨hr.1, fun hsat => hr.2 (I.relation_of_sat _ _ hsat)⟩) h

end Soundness

/-! ## Zero knowledge and completeness

`K` is the field of the witness and `E` the field of the challenges; zero knowledge asks that
`E` be of degree 3 over `K`. -/

section ZeroKnowledge

variable {K E : Type} [Field K] [Field E] [Algebra K E] [DecidableEq E] [CharP E 2] [Fintype E]
variable [Fintype K] [DecidableEq K] [FiniteDimensional K E]
variable [SampleableType K] [SampleableType E]
variable {H : Type} [SampleableType H] [Fintype H] [DecidableEq H]
variable (I : Instance E)

/-- **Zero knowledge.** Take a statement, a witness over `K` whose cells satisfy the relation,
and any state `c₀` of the oracle, with `U` a set holding every handle the oracle was asked about
with this statement. Then for every event `S` on the view, its probabilities in the real
experiment and in the simulator's differ by at most `1 / 2^128 + |U| / |H|`. -/
theorem zero_knowledge (h3 : finrank K E = 3) (hq : Fintype.card E = 2 ^ 192)
    (c₀ : I.Table H) (stmt : Fin 8 → E) (U : Finset H)
    (hU : ∀ c₁, c₁ ∉ U → Fresh c₀ stmt c₁) (gK : Fin 4 → K[X])
    (hsat : I.Relation stmt (I.witnessCells gK)) (S : I.View H → Prop) :
    Pr{let o ← I.real c₀ stmt gK}[S o]
        ≤ Pr{let o ← I.sim K c₀ stmt}[S o] + (1 / 2 ^ 128 + U.card / Fintype.card H) ∧
      Pr{let o ← I.sim K c₀ stmt}[S o]
        ≤ Pr{let o ← I.real c₀ stmt gK}[S o] + (1 / 2 ^ 128 + U.card / Fintype.card H) := by
  have : CharP K 2 := RingHom.charP (algebraMap K E) (algebraMap K E).injective 2
  have hsat' := I.sat_of_relation stmt _ (I.witnessCells_eq gK ▸ hsat)
  have h := zeroKnowledge h3 I.exact c₀ stmt U hU gK (digitPoly 22)
    (digitPoly_monic_natDegree 22).1.ne_zero I.mask_vanishes hsat' S
  have hle := I.zkBound_le (K := K) hq U
  rw [I.real_event, I.sim_event]
  exact ⟨h.1.trans (add_le_add_right hle _), h.2.trans (add_le_add_right hle _)⟩

/-- **Zero knowledge, from a fresh oracle.** When the oracle has not been asked anything, the
difference is at most `1 / 2^128`. -/
theorem zero_knowledge_fresh (h3 : finrank K E = 3) (hq : Fintype.card E = 2 ^ 192)
    (stmt : Fin 8 → E) (gK : Fin 4 → K[X]) (hsat : I.Relation stmt (I.witnessCells gK))
    (S : I.View H → Prop) :
    Pr{let o ← I.real ∅ stmt gK}[S o] ≤ Pr{let o ← I.sim K ∅ stmt}[S o] + 1 / 2 ^ 128 ∧
      Pr{let o ← I.sim K ∅ stmt}[S o] ≤ Pr{let o ← I.real ∅ stmt gK}[S o] + 1 / 2 ^ 128 := by
  have h := I.zero_knowledge h3 hq (∅ : I.Table H) stmt ∅
    (fun c₁ _ => ⟨rfl, fun _ => rfl, fun _ _ _ => rfl⟩) gK hsat S
  simpa using h

/-- **Completeness.** In the real experiment, for a witness of degree at most `2^22`: the
verdict on the honest proof is false with probability at most `2 / 2^128 + |U| / |H|`. The
verdict is that the four claims are true and the product the verifier inverts is not zero; the
Rust verifier also rejects a challenge `t` with some `1 + w_k(t) = 0` (`k ≤ 25`), about
`2^26 / 2^192` of them, which is not counted. -/
theorem completeness (hq : Fintype.card E = 2 ^ 192)
    (c₀ : I.Table H) (stmt : Fin 8 → E) (U : Finset H)
    (hU : ∀ c₁, c₁ ∉ U → Fresh c₀ stmt c₁) (gK : Fin 4 → K[X])
    (hdeg : ∀ j, (gK j).natDegree ≤ 2 ^ 22)
    (hsat : I.Relation stmt (I.witnessCells gK)) :
    Pr{let o ← I.real c₀ stmt gK}[o.1.verdict = false]
      ≤ 2 / 2 ^ 128 + U.card / Fintype.card H := by
  have : CharP K 2 := RingHom.charP (algebraMap K E) (algebraMap K E).injective 2
  have hsat' := I.sat_of_relation stmt _ (I.witnessCells_eq gK ▸ hsat)
  have hvdeg : (digitPoly 22 : K[X]).natDegree = 2 ^ 22 := (digitPoly_monic_natDegree 22).2
  have hg : ∀ m j, (committed (E := E) gK (digitPoly 22) m j).natDegree ≤ I.bounds.witness := by
    intro m j
    refine (natDegree_committed_le gK _ m j).trans (max_le ((hdeg j).trans ?_) ?_)
    · show 2 ^ 22 ≤ 2 ^ (22 + 1)
      norm_num
    · rw [hvdeg]
      show 2 ^ 22 + 2 ≤ 2 ^ (22 + 1)
      norm_num
  have h := completeness_prob I.exact c₀ stmt U hU gK (digitPoly 22)
    (digitPoly_monic_natDegree 22).1.ne_zero I.mask_vanishes hsat'
    (I.cellEquiv fun _ => false) I.bounds hg
  have hid : I.bounds.identity ≤ 2 ^ 29 :=
    Params.ofCantor_identity I.basis le24 I.wiring _ _ I.pub_hPub
      (natDegree_membershipPub_le _ I.c)
  have hpos : 0 < Fintype.card E := Fintype.card_pos
  have e2 : (I.bounds.identity : ENNReal) / (Fintype.card E : ENNReal) ≤ 1 / 2 ^ 128 := by
    have hle := div_le_two_pow hpos (a := I.bounds.identity) (by
      rw [hq]; exact (Nat.mul_le_mul_right (2 ^ 128) hid).trans (by norm_num))
    have hc : (I.bounds.identity : ENNReal) / (Fintype.card E : ENNReal)
        = (((I.bounds.identity : ℝ≥0) / (Fintype.card E : ℝ≥0) : ℝ≥0) : ENNReal) := by
      rw [ENNReal.coe_div (by exact_mod_cast hpos.ne')]
      simp
    rw [hc, ← coe_bit]
    exact ENNReal.coe_le_coe.mpr hle
  rw [I.real_event]
  refine (h.trans (add_le_add (I.zkBound_le (K := K) hq U) e2)).trans (le_of_eq ?_)
  rw [show (2 : ENNReal) / 2 ^ 128 = 1 / 2 ^ 128 + 1 / 2 ^ 128 by
    rw [ENNReal.div_add_div_same]; norm_num]
  ring

/-- **The honest prover's messages are legal**: for a witness of degree at most `2^22`, whatever
the masks and the challenges, its two messages are within the degrees a proof may have. -/
theorem honest_messages_fit (gK : Fin 4 → K[X]) (hdeg : ∀ j, (gK j).natDegree ≤ 2 ^ 22)
    (m : Fin 4 → Fin 3 → K) (α β γ : E) :
    ∃ (g : I.bounds.Msg₁) (R : I.bounds.Msg₂), g.1 = committed gK (digitPoly 22) m ∧
      R.1 = Params.honest I.params g.1 α β γ := by
  have : CharP K 2 := RingHom.charP (algebraMap K E) (algebraMap K E).injective 2
  have hvdeg : (digitPoly 22 : K[X]).natDegree = 2 ^ 22 := (digitPoly_monic_natDegree 22).2
  have hg : ∀ j, (committed (E := E) gK (digitPoly 22) m j).natDegree ≤ 2 ^ 22 + 2 := by
    intro j
    refine (natDegree_committed_le gK _ m j).trans (max_le ((hdeg j).trans (by norm_num)) ?_)
    rw [hvdeg]
  refine ⟨⟨_, fun j => (hg j).trans ?_⟩, ⟨_, I.honest_legal _ hg α β γ⟩, rfl, rfl⟩
  show 2 ^ 22 + 2 ≤ 2 ^ (22 + 1)
  norm_num

end ZeroKnowledge

end Instance

end QuotientSecurity
