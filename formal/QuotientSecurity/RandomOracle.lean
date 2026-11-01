-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/RandomOracle.lean. MIT OR Apache-2.0; see NOTICE.md.
import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery
import QuotientSecurity.Bits

/-!
# Knowledge soundness of the non-interactive proof, in the random-oracle model

The transcript's hash is a random oracle on what it has absorbed: the statement and the first
message give `(α, β, γ)`, with the second message they give `t`, and with the five values `ρ`.
Commitments are ideal, so a proof is the two messages and the five values. An adversary that
makes at most `Q` queries outputs a statement and a proof; the verifier asks its three
challenges of the same oracle. The cells read off the first message fail the relation while the
verifier accepts with probability at most `(Q + 3)` times the largest round error.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal

namespace QuotientSecurity

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable (P : Params F) (B : P.Bounds)

/-- What the hash has absorbed when it gives a challenge. -/
inductive Key
  | first (stmt : Fin P.words → F) (g : B.Msg₁)
  | second (stmt : Fin P.words → F) (g : B.Msg₁) (R : B.Msg₂)
  | third (stmt : Fin P.words → F) (g : B.Msg₁) (R : B.Msg₂) (v : (Fin 4 → F) × F)

/-- The challenge it gives. -/
def Answer : Key P B → Type
  | .first .. => F × F × F
  | .second .. => F
  | .third .. => F

noncomputable instance : DecidableEq (Key P B) := Classical.decEq _

instance : ∀ k, SampleableType (Answer P B k)
  | .first .. => (inferInstance : SampleableType (F × F × F))
  | .second .. => (inferInstance : SampleableType F)
  | .third .. => (inferInstance : SampleableType F)

/-- A statement and a proof of it. -/
structure Proof where
  stmt : Fin P.words → F
  g : B.Msg₁
  R : B.Msg₂
  v : (Fin 4 → F) × F

variable {P B}

open Classical in
/-- The non-interactive verifier. -/
noncomputable def verify (π : Proof P B) : OracleComp (ofFn (Answer P B)) Bool :=
  liftM ((ofFn (Answer P B)).query (Key.first π.stmt π.g)) >>= fun (c : F × F × F) =>
  liftM ((ofFn (Answer P B)).query (Key.second π.stmt π.g π.R)) >>= fun (t : F) =>
  liftM ((ofFn (Answer P B)).query (Key.third π.stmt π.g π.R π.v)) >>= fun (ρ : F) =>
  pure (decide (P.Accepts π.stmt π.g.1 π.R.1 c.1 c.2.1 c.2.2 t π.v.1 π.v.2 ρ))

open Params

/-- A key is bad in a table when its challenge turns a lost state into one that is not. -/
def bad (k : Key P B) (tbl : ∀ k, Answer P B k) : Prop :=
  match k with
  | .first stmt g => ¬ State₁ stmt g ∧ State₂ stmt g (tbl (.first stmt g))
  | .second stmt g R =>
      ¬ State₃ stmt g (tbl (.first stmt g)) R ∧
        State₄ stmt g (tbl (.first stmt g)) R (tbl (.second stmt g R))
  | .third stmt g R v =>
      ¬ State₄ stmt g (tbl (.first stmt g)) R (tbl (.second stmt g R)) ∧
        State₆ stmt g (tbl (.first stmt g)) R (tbl (.second stmt g R)) v
          (tbl (.third stmt g R v))

variable (P B)

/-- The largest of the three round errors. -/
noncomputable def roundError : ℝ≥0 :=
  max (max (((2 * P.nCells ^ 2 + 4 * P.nCells + P.words : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0))
    (((B.identity : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0)))
    (((3 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0))

variable {P B}

theorem prob_bad_le (k : Key P B) (tbl : ∀ k, Answer P B k) :
    Pr{let u ← $ᵗ (Answer P B k)}[bad k (Function.update tbl k u)] ≤ (roundError P B : ENNReal) := by
  cases k with
  | first stmt g =>
    simp only [bad, Function.update_self]
    refine (prob_first P B stmt g).trans ?_
    exact_mod_cast le_trans (le_max_left _ _) (le_max_left _ _)
  | second stmt g R =>
    have hne : Key.first stmt g ≠ Key.second stmt g R := by intro h; cases h
    simp only [bad, Function.update_self, Function.update_of_ne hne]
    refine (prob_second P B stmt g _ R).trans ?_
    exact_mod_cast le_trans (le_max_right _ _) (le_max_left _ _)
  | third stmt g R v =>
    have hne1 : Key.first stmt g ≠ Key.third stmt g R v := by intro h; cases h
    have hne2 : Key.second stmt g R ≠ Key.third stmt g R v := by intro h; cases h
    simp only [bad, Function.update_self, Function.update_of_ne hne1, Function.update_of_ne hne2]
    refine (prob_third P B stmt g _ R _ v).trans ?_
    exact_mod_cast le_max_right _ _

/-- The experiment: the adversary's statement and proof, and the verifier's decision. -/
noncomputable def experiment (adv : OracleComp (ofFn (Answer P B)) (Proof P B)) :
    OracleComp (ofFn (Answer P B)) (Proof P B × Bool) :=
  adv >>= fun π => verify π >>= fun b => pure (π, b)

theorem verify_queryBound (π : Proof P B) : IsTotalQueryBound (verify π) 3 :=
  isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ =>
    isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ =>
      isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ => trivial⟩⟩⟩

/-- **Knowledge soundness in the random-oracle model.** For every adversary making at most `Q`
queries, the probability that the verifier accepts its proof while the cells read off the proof's
first message do not satisfy the relation is at most `(Q + 3)` times the largest round error. -/
theorem knowledgeSoundness (adv : OracleComp (ofFn (Answer P B)) (Proof P B)) (Q : ℕ)
    (hQ : IsTotalQueryBound adv Q) :
    Pr{let r ← (simulateQ randomOracle (experiment adv)).run' ∅}[
        r.2 = true ∧ ¬ P.Sat r.1.stmt (P.cells r.1.g.1)]
      ≤ ((Q + 3 : ℕ) : ENNReal) * (roundError P B : ENNReal) := by
  classical
  refine prEvent_randomOracle_le_of_bad_queries (experiment adv) (Q + 3)
    (isTotalQueryBound_bind hQ fun π =>
      (isTotalQueryBound_bind (n₂ := 0) (verify_queryBound π) fun b => trivial))
    _ bad _ prob_bad_le ?_
  intro tbl hevent
  set π := evalWithAnswerFn (QueryImpl.ofFn tbl) adv with hπ
  have hlog : tableQueryLog (experiment adv) tbl
      = tableQueryLog adv tbl ++
        [⟨Key.first π.stmt π.g, tbl (Key.first π.stmt π.g)⟩,
          ⟨Key.second π.stmt π.g π.R, tbl (Key.second π.stmt π.g π.R)⟩,
          ⟨Key.third π.stmt π.g π.R π.v, tbl (Key.third π.stmt π.g π.R π.v)⟩] := by
    simp only [experiment, verify, tableQueryLog_bind, bind_assoc, tableQueryLog_query_bind,
      tableQueryLog_pure, List.append_nil, ← hπ, pure_bind]
    rfl
  have heval : evalWithAnswerFn (QueryImpl.ofFn tbl) (experiment adv)
      = (π, decide (P.Accepts π.stmt π.g.1 π.R.1 (tbl (Key.first π.stmt π.g)).1
          (tbl (Key.first π.stmt π.g)).2.1 (tbl (Key.first π.stmt π.g)).2.2
          (tbl (Key.second π.stmt π.g π.R)) π.v.1 π.v.2 (tbl (Key.third π.stmt π.g π.R π.v)))) := by
    simp only [experiment, verify, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
      evalWithAnswerFn_pure, ← hπ]
    rfl
  rw [heval] at hevent
  obtain ⟨hacc, hsat⟩ := hevent
  have hacc' := of_decide_eq_true hacc
  rw [hlog]
  -- The first challenge at which the state stops being lost is a bad key, and the verifier asked it.
  by_cases h2 : State₂ π.stmt π.g (tbl (Key.first π.stmt π.g))
  · exact ⟨⟨Key.first π.stmt π.g, _⟩, List.mem_append_right _ List.mem_cons_self, hsat, h2⟩
  · have h3 : ¬ State₃ π.stmt π.g (tbl (Key.first π.stmt π.g)) π.R := by
      rintro (h | h)
      · exact h2 (Or.inl h)
      · exact h2 (Or.inr ⟨_, h⟩)
    by_cases h4 : State₄ π.stmt π.g (tbl (Key.first π.stmt π.g)) π.R
        (tbl (Key.second π.stmt π.g π.R))
    · exact ⟨⟨Key.second π.stmt π.g π.R, _⟩,
        List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), h3, h4⟩
    · exact ⟨⟨Key.third π.stmt π.g π.R π.v, _⟩,
        List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
        h4, Or.inr hacc'⟩

/-- **128 bits.** At the sizes of `quotient::protocol` (`2^24` cells, eight words, identities of
degree at most `2^29`, a field of `2^192` elements), an adversary making `Q` queries wins with
probability at most `(Q + 3) / 2^128`. -/
theorem knowledgeSoundness_bits (hq : Fintype.card F = 2 ^ 192) (hN : P.nCells = 2 ^ 24)
    (hw : P.words = 8) (hd : B.identity ≤ 2 ^ 29)
    (adv : OracleComp (ofFn (Answer P B)) (Proof P B)) (Q : ℕ) (hQ : IsTotalQueryBound adv Q) :
    Pr{let r ← (simulateQ randomOracle (experiment adv)).run' ∅}[
        r.2 = true ∧ ¬ P.Sat r.1.stmt (P.cells r.1.g.1)]
      ≤ ((Q + 3 : ℕ) : ENNReal) * (((1 / 2 ^ 128 : ℝ≥0) : ℝ≥0) : ENNReal) := by
  refine (knowledgeSoundness adv Q hQ).trans ?_
  gcongr
  have h1 := rbrError_le P B hq hN hw hd ⟨⟨1, by norm_num⟩, rfl⟩
  have h3 := rbrError_le P B hq hN hw hd ⟨⟨3, by norm_num⟩, rfl⟩
  have h5 := rbrError_le P B hq hN hw hd ⟨⟨5, by norm_num⟩, rfl⟩
  exact max_le (max_le h1 h3) h5

end QuotientSecurity
