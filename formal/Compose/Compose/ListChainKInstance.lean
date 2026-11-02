-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The instance of `ListChainK.lean`'s `k`-round chain that is `ListChain.lean`'s (two roots, three
-- challenge groups); the statements re-derived are `AdversaryLog.lean`'s, of this repository.
import Compose.ListChainKComposed

/-!
# `quotient::protocol`'s chain is an instance: two roots, three challenge groups

The reduction's chain (`ListChain.lean`'s `chainWith`) is the `k`-round chain of
`ListChainK.lean` at three rounds (`quotRounds`): the witness root then `α, β, γ`; the quotient
root then `t`; the five values then `ρ`. Its label is `labelOf` (112 bytes, `≢ 0 mod 32`), its
scalars the wire's limbs (`quotK`), and the proof's messages are its two roots and its values
(`quotView`). On a run, the generic chain's challenges are `chainWith`'s (`chain_quot`), so the
generic experiment is `AdversaryLog.lean`'s `advExperiment`, its outcome read as lists
(`expK_quot`).

The protocol's round-by-round soundness is F1's (`quotPiop`): its states `State₁`, `State₃`,
`State₄` before each round's challenges and `State₂`, `State₄`, `Accepts` after, read off the
opened transcript (a candidate of the first root a witness message `Sum.inl g`, of the second a
quotient message `Sum.inr R`); each round's error is F1's `roundError` (`prob_first`,
`prob_second`, `prob_third`). The candidates are `ListChain.lean`'s two list commitments, each
mapped into `B.Msg₁ ⊕ B.Msg₂` (`quotC`). Its factor-weighted error is at most
`listFactor L₁ L₂ · roundError` (`maxErrK_quot_le`): `L₁` for round one, `L₁ L₂` for rounds two
and three.

**Re-derived**: `knowledgeSoundness_list_adv_K` is `AdversaryLog.lean`'s
`knowledgeSoundness_list_adv`, statement for statement, from `knowledgeSoundness_listK_adv`; and
`knowledgeSoundness_composed_adv_K`, `knowledgeSoundness_merkle_adv_K` are
`knowledgeSoundness_composed_adv` and `knowledgeSoundness_merkle_adv`, from the generic composed
theorem `knowledgeSoundness_listChainK` (the witness and quotient openings the two roots', the
wiring opening the setup's, `Openings.lean`'s `accepts_iff` the link).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm QuotientSecurity QuotientSecurity.Params LeanVM LeanVM.Protocol LeanVM.Semantics

/-! ## List commitments into a common type -/

/-- A list commitment's candidates, mapped. -/
def ListCommit.map {M M' : Type} (f : M → M') (C : ListCommit M) : ListCommit M' where
  bound := C.bound
  cands H T r := (C.cands H T r).map f
  length_le H T r := by rw [List.length_map]; exact C.length_le H T r
  congr H T T' r h := by rw [C.congr H T T' r h]
  stable H H' T r h1 h2 h3 := by rw [C.stable H H' T r h1 h2 h3]

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : Params F} {B : P.Bounds} (W : Wire P B)

/-! ## The chain -/

/-- **The reduction's rounds**: the witness root and three challenges, the quotient root and one,
the five values and one. -/
def quotRounds : List RoundSpec := [⟨true, 0, 2⟩, ⟨true, 0, 0⟩, ⟨false, 5, 0⟩]

/-- **The reduction's chain**: the wire's limbs, `labelOf`, three rounds. -/
def quotK : ChainSpec F (Bytes32 × Vector UInt8 64) where
  lim := W.limbs
  label s := labelOf s.1 s.2
  label_injective a b h := by simpa using labelOf_injective h
  label_len s := by rw [length_labelOf]; decide
  rounds := quotRounds

/-- The five values as a list. -/
def valsOf (v : (Fin 4 → F) × F) : List F := [v.1 0, v.1 1, v.1 2, v.1 3, v.2]

/-- The five values read off a list. -/
def fromVals (l : List F) : (Fin 4 → F) × F := (fun i => l.getD i 0, l.getD 4 0)

theorem fromVals_valsOf (v : (Fin 4 → F) × F) : fromVals (valsOf v) = v := by
  obtain ⟨a, b⟩ := v
  refine Prod.ext (funext fun i => ?_) rfl
  fin_cases i <;> rfl

/-- The proof's messages: its two roots, its values. -/
def msgsOf (π : RootProof F) : List (RMsg F) :=
  [(some π.r₁, []), (some π.r₂, []), (none, valsOf π.v)]

/-- What the generic chain reads of a proof. -/
def quotView {O : Type} (p : RootProof F × O) : (Bytes32 × Vector UInt8 64) × List (RMsg F) :=
  ((p.1.ir, p.1.stmt), msgsOf p.1)

/-- The challenges, as one list per round. -/
def toL (ch : Chals F) : List (List F) := [[ch.α, ch.β, ch.γ], [ch.t], [ch.ρ]]

/-- A round's three challenges, read off a list. -/
def c3 (l : List F) : F × F × F := (l.getD 0 0, l.getD 1 0, l.getD 2 0)

/-- A round's challenge, read off a list. -/
def c1 (l : List F) : F := l.getD 0 0

/-- The challenges read off one list per round. -/
def ofL (l : List (List F)) : Chals F :=
  ⟨(c3 (l.headD [])).1, (c3 (l.headD [])).2.1, (c3 (l.headD [])).2.2, c1 (l.tail.headD []),
    c1 (l.tail.tail.headD [])⟩

theorem ofL_toL (ch : Chals F) : ofL (toL ch) = ch := rfl

/-- **On every proof, the generic chain is `chainWith`.** -/
theorem chain_quot (π : RootProof F) :
    (quotK W).chain hash256 (π.ir, π.stmt) (msgsOf π) = toL <$> chainWith W hash256 π := by
  simp only [ChainSpec.chain, quotK, quotRounds, absorbs, msgsOf, List.headD_cons, List.tail_cons,
    List.replicate, List.nil_append, List.cons_append, runM, chainWith, map_bind, map_pure,
    bind_assoc, pure_bind, stepIn_nil]
  simp [stepIn, encM, scalarsOf, valsOf, Wire.afterRoot, Wire.afterValues, Wire.valueWords,
    Wire.word, ChainSpec.chalsOf, groupK, toL, chalL, Wire.chal]

/-- What the generic experiment returns, from `advExperiment`'s outcome. -/
def gK {O β : Type} (z : Run F O β × Transcript) : OutK (RootProof F × O) F β :=
  (((z.1.proof, z.1.rest), (toL z.1.chals, z.1.out)), z.2)

/-- **The generic experiment is `advExperiment`**, its outcome read as lists. -/
theorem expK_quot {O β : Type} (A : OracleComp KeccakCalls (RootProof F × O))
    (post : RootProof F × O → Chals F → OracleComp KeccakCalls β) :
    expK (quotK W) quotView A (fun p l => post p (ofL l)) = gK <$> advExperiment W A post := by
  simp only [expK, verK, advExperiment, map_bind, map_pure, gK]
  refine bind_congr fun pt => ?_
  simp only [quotView]
  rw [chain_quot, bind_map_left]
  simp only [bind_assoc, pure_bind, ofL_toL]

theorem prEvent_run'_map {α γ : Type} (X : OracleComp KeccakCalls α) (f : α → γ) (E : γ → Prop) :
    Pr{let z ← (simulateQ randomOracle (f <$> X)).run' ∅}[E z] =
      Pr{let z ← (simulateQ randomOracle X).run' ∅}[E (f z)] := by
  rw [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map, StateT.run'_eq,
    prEvent_map, prEvent_map]

/-! ## The candidates and the protocol's soundness -/

/-- The candidates' common type: a witness message or a quotient message. -/
abbrev QM (B : P.Bounds) := B.Msg₁ ⊕ B.Msg₂

/-- The two roots' list commitments, round by round. -/
def quotC (C₁ : ListCommit B.Msg₁) (C₂ : ListCommit B.Msg₂) : ℕ → ListCommit (QM B)
  | 1 => C₂.map Sum.inr
  | _ => C₁.map Sum.inl

/-- **F1's states before each round's challenges**, on an opened transcript. -/
def quotPre (W : Wire P B) (s : Bytes32 × Vector UInt8 64) :
    Opened (QM B) F → Option (QM B) × List F → Prop
  | [], m => ∃ g, m.1 = some (.inl g) ∧ State₁ (W.decode s.2) g
  | [a], m => ∃ g R, a.1.1 = some (.inl g) ∧ m.1 = some (.inr R) ∧
      State₃ (W.decode s.2) g (c3 a.2) R
  | [a, b], _ => ∃ g R, a.1.1 = some (.inl g) ∧ b.1.1 = some (.inr R) ∧
      State₄ (W.decode s.2) g (c3 a.2) R (c1 b.2)
  | _, _ => False

/-- **F1's states after each round's challenges**: after the last round, the verifier's
claims; before, the next round's state for some message. -/
def quotPost (W : Wire P B) (s : Bytes32 × Vector UInt8 64) :
    Opened (QM B) F → Option (QM B) × List F → List F → Prop
  | [a, b], m, c => ∃ g R, a.1.1 = some (.inl g) ∧ b.1.1 = some (.inr R) ∧
      P.Accepts (W.decode s.2) g.1 R.1 (c3 a.2).1 (c3 a.2).2.1 (c3 a.2).2.2 (c1 b.2)
        (fromVals m.2).1 (fromVals m.2).2 (c1 c)
  | p, m, c => ∃ m', quotPre W s (p ++ [(m, c)]) m'

theorem draws_three :
    draws F 3 = (($ᵗ F : ProbComp F) >>= fun a => ($ᵗ F : ProbComp F) >>= fun b =>
      ($ᵗ F : ProbComp F) >>= fun d => pure [a, b, d]) := by
  simp [draws]

theorem draws_one : draws F 1 = (fun a => [a]) <$> ($ᵗ F : ProbComp F) := by
  simp [draws]

theorem prEvent_draws_three (Q : F × F × F → Prop) :
    Pr{let c ← draws F 3}[Q (c3 c)] = Pr{let x ← $ᵗ (F × F × F)}[Q x] := by
  rw [draws_three, ← prEvent_three_draws (fun a b d => Q (a, b, d))]
  simp [c3]

theorem prEvent_draws_one (Q : F → Prop) :
    Pr{let c ← draws F 1}[Q (c1 c)] = Pr{let x ← $ᵗ F}[Q x] := by
  rw [draws_one, prEvent_map]
  rfl

theorem state₂_of_state₃ {stmt : Fin P.words → F} {g : B.Msg₁} {c : F × F × F} {R : B.Msg₂}
    (h : State₃ stmt g c R) : State₂ stmt g c := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr ⟨R, h⟩

/-- **F1's round-by-round soundness, as the `k`-round chain's protocol.** -/
noncomputable def quotPiop : Piop (quotK W) (QM B) where
  pre := quotPre W
  post := quotPost W
  pre_post s p m c m' h := by
    rcases p with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
    · exact ⟨m', h⟩
    · exact ⟨m', h⟩
    · simp [quotPre] at h
    · simp [quotPre] at h
  err _ := (roundError P B : ℝ≥0∞)
  sound j s p m hj hp := by
    classical
    simp only [quotK, quotRounds, List.length_cons, List.length_nil] at hj
    interval_cases j
    · -- The first round: `α, β, γ` after the witness root.
      rw [List.length_eq_zero_iff] at hp
      subst hp
      by_cases hm : ∃ g, m.1 = some (.inl g)
      · obtain ⟨g, hg⟩ := hm
        refine (prEvent_mono _ _ (fun c => ¬ State₁ (W.decode s.2) g ∧
          State₂ (W.decode s.2) g (c3 c)) fun c h => ?_).trans ?_
        · obtain ⟨h1, m', g', R, hg', hR, h3⟩ := h
          simp only [List.nil_append] at hg'
          rw [hg] at hg'
          simp only [Option.some.injEq, Sum.inl.injEq] at hg'
          subst hg'
          exact ⟨fun h => h1 ⟨g, hg, h⟩, state₂_of_state₃ h3⟩
        · show Pr{let c ← draws F 3}[(fun x => ¬ State₁ (W.decode s.2) g ∧
            State₂ (W.decode s.2) g x) (c3 c)] ≤ _
          rw [prEvent_draws_three (fun x => ¬ State₁ (W.decode s.2) g ∧ State₂ (W.decode s.2) g x)]
          refine (prob_first P B (W.decode s.2) g).trans ?_
          exact_mod_cast le_trans (le_max_left _ _) (le_max_left _ _)
      · rw [prEvent_eq_zero_of_forall_not _ _ fun c h => ?_]
        · exact bot_le
        obtain ⟨-, m', g', R, hg', -⟩ := h
        exact hm ⟨g', hg'⟩
    · -- The second round: `t` after the quotient root.
      obtain ⟨a, rfl⟩ : ∃ a, p = [a] := List.length_eq_one_iff.mp hp
      by_cases hm : ∃ g R, a.1.1 = some (.inl g) ∧ m.1 = some (.inr R)
      · obtain ⟨g, R, hg, hR⟩ := hm
        refine (prEvent_mono _ _ (fun c => ¬ State₃ (W.decode s.2) g (c3 a.2) R ∧
          State₄ (W.decode s.2) g (c3 a.2) R (c1 c)) fun c h => ?_).trans ?_
        · obtain ⟨h1, m', g', R', hg', hR', h4⟩ := h
          rw [hg] at hg'
          simp only [Option.some.injEq, Sum.inl.injEq] at hg'
          subst hg'
          simp only at hR'
          rw [hR] at hR'
          simp only [Option.some.injEq, Sum.inr.injEq] at hR'
          subst hR'
          exact ⟨fun h => h1 ⟨g, R, hg, hR, h⟩, h4⟩
        · show Pr{let c ← draws F 1}[(fun x => ¬ State₃ (W.decode s.2) g (c3 a.2) R ∧
            State₄ (W.decode s.2) g (c3 a.2) R x) (c1 c)] ≤ _
          rw [prEvent_draws_one (fun x => ¬ State₃ (W.decode s.2) g (c3 a.2) R ∧
            State₄ (W.decode s.2) g (c3 a.2) R x)]
          refine (prob_second P B (W.decode s.2) g (c3 a.2) R).trans ?_
          exact_mod_cast le_trans (le_max_right _ _) (le_max_left _ _)
      · rw [prEvent_eq_zero_of_forall_not _ _ fun c h => ?_]
        · exact bot_le
        obtain ⟨-, m', g', R', hg', hR', -⟩ := h
        exact hm ⟨g', R', hg', hR'⟩
    · -- The third round: `ρ` after the values.
      obtain ⟨a, b, rfl⟩ : ∃ a b, p = [a, b] := by
        match p, hp with
        | [a, b], _ => exact ⟨a, b, rfl⟩
      by_cases hm : ∃ g R, a.1.1 = some (.inl g) ∧ b.1.1 = some (.inr R)
      · obtain ⟨g, R, hg, hR⟩ := hm
        refine (prEvent_mono _ _ (fun c => ¬ State₄ (W.decode s.2) g (c3 a.2) R (c1 b.2) ∧
          State₆ (W.decode s.2) g (c3 a.2) R (c1 b.2) (fromVals m.2) (c1 c)) fun c h => ?_).trans ?_
        · obtain ⟨h1, g', R', hg', hR', hacc⟩ := h
          rw [hg] at hg'
          simp only [Option.some.injEq, Sum.inl.injEq] at hg'
          subst hg'
          rw [hR] at hR'
          simp only [Option.some.injEq, Sum.inr.injEq] at hR'
          subst hR'
          exact ⟨fun h => h1 ⟨g, R, hg, hR, h⟩, Or.inr hacc⟩
        · show Pr{let c ← draws F 1}[(fun x => ¬ State₄ (W.decode s.2) g (c3 a.2) R (c1 b.2) ∧
            State₆ (W.decode s.2) g (c3 a.2) R (c1 b.2) (fromVals m.2) x) (c1 c)] ≤ _
          rw [prEvent_draws_one (fun x => ¬ State₄ (W.decode s.2) g (c3 a.2) R (c1 b.2) ∧
            State₆ (W.decode s.2) g (c3 a.2) R (c1 b.2) (fromVals m.2) x)]
          refine (prob_third P B (W.decode s.2) g (c3 a.2) R (c1 b.2) (fromVals m.2)).trans ?_
          exact_mod_cast le_max_right _ _
      · rw [prEvent_eq_zero_of_forall_not _ _ fun c h => ?_]
        · exact bot_le
        obtain ⟨-, g', R', hg', hR', -⟩ := h
        exact hm ⟨g', R', hg', hR'⟩

/-- **The factor-weighted error is at most `listFactor L₁ L₂ · roundError`.** -/
theorem maxErrK_quot_le (C₁ : ListCommit B.Msg₁) (C₂ : ListCommit B.Msg₂) :
    maxErrK (quotK W) (quotC C₁ C₂) (quotPiop W) ≤
      (listFactor C₁.bound C₂.bound : ℝ≥0∞) * (roundError P B : ℝ≥0∞) := by
  unfold maxErrK
  refine Finset.sup_le fun j hj => ?_
  simp only [quotK, quotRounds, List.length_cons, List.length_nil, Finset.mem_range] at hj
  show (facL (quotC C₁ C₂) 0 (quotRounds.take (j + 1)) : ℝ≥0∞) * (roundError P B : ℝ≥0∞) ≤ _
  gcongr
  have h1 := le_listFactor_left C₁.bound C₂.bound
  have h2 := le_listFactor_right C₁.bound C₂.bound
  interval_cases j <;> simp [facL, quotRounds, quotC, ListCommit.map] <;> omega

/-! ## The list game re-derived -/

variable (C₁ : ListCommit B.Msg₁) (C₂ : ListCommit B.Msg₂)

/-- `ListChain.lean`'s winning event is the generic one, on the outcome read as lists. -/
theorem listWinsK_of_listWins {O β : Type} (z : Run F O β × Transcript)
    (h : ListWins W C₁ C₂ z) :
    ListWinsK (quotK W) (quotC C₁ C₂) (quotPiop W) quotView (gK z) := by
  obtain ⟨g, hg, R, hR, hacc, hsat⟩ := h
  refine ⟨by simp [FitsAll, RMsg.Fits, quotK, quotRounds, quotView, gK, msgsOf, valsOf], ?_⟩
  refine ⟨[some (.inl g), some (.inr R), none], ?_, ?_⟩
  · simp only [gK, quotView, msgsOf, candLists, optC, quotC]
    refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))
    · simpa [ListCommit.map] using hg
    · simpa [ListCommit.map] using hR
    · simp
  · simp only [gK, quotView, msgsOf, toL, opened, List.headD_cons, List.tail_cons]
    refine ⟨fun ⟨g', hg', h1⟩ => ?_, [((some (.inl g), []), [z.1.chals.α, z.1.chals.β,
      z.1.chals.γ]), ((some (.inr R), []), [z.1.chals.t])], (none, valsOf z.1.proof.v),
      [z.1.chals.ρ], rfl, ?_⟩
    · simp only [Option.some.injEq, Sum.inl.injEq] at hg'
      subst hg'
      exact hsat h1
    · refine ⟨g, R, rfl, rfl, ?_⟩
      simp only [c3, c1, List.getD_cons_zero, List.getD_cons_succ, fromVals_valsOf]
      exact hacc

/-- **`AdversaryLog.lean`'s `knowledgeSoundness_list_adv`, re-derived from the generic
theorem.** -/
theorem knowledgeSoundness_list_adv_K {O β : Type} (A : OracleComp KeccakCalls (RootProof F × O))
    (post : RootProof F × O → Chals F → OracleComp KeccakCalls β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (post p ch) QV) :
    Pr{let z ← (simulateQ randomOracle (advExperiment W A post)).run' ∅}[ListWins W C₁ C₂ z] ≤
      ((Q + 6 + QV : ℕ) : ℝ≥0∞) * ((listFactor C₁.bound C₂.bound : ℝ≥0∞) *
        (roundError P B : ℝ≥0∞) + 5 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  have hK := knowledgeSoundness_listK_adv (quotK W) (quotC C₁ C₂) (quotPiop W) quotView A
    (fun p l => post p (ofL l)) Q QV hQ fun p ch => hV p (ofL ch)
  rw [expK_quot, prEvent_run'_map] at hK
  have hnQ : (quotK W).nQ = 6 := rfl
  rw [hnQ] at hK
  refine (prEvent_mono _ _ _ fun z h => listWinsK_of_listWins W C₁ C₂ z h).trans (hK.trans ?_)
  gcongr
  exact maxErrK_quot_le W C₁ C₂

/-! ## The composed statement re-derived -/

/-- **The reduction's openings, as the `k`-round chain's**: the witness opening is round `0`'s
root's, the quotient opening round `1`'s, the wiring opening the setup's; the verifier's own check
is `reductionCheck`. -/
def quotOp {O : Type} : OpeningsK (RootProof F × O) F Verdicts (QM B) where
  check π ch _ := reductionCheck P (ofL ch).α (ofL ch).β (ofL ch).t π.1.v.1 π.1.v.2
  acc i _ _ b := if i = 0 then b.1 = true else b.2.2 = true
  good i π ch c := match i, c with
    | 0, some (.inl g) => witnessClaim g.1 (ofL ch).t (ofL ch).ρ π.1.v.1
    | 1, some (.inr R) => quotientClaims P (W.decode π.1.stmt) R.1 (ofL ch).α (ofL ch).β
        (ofL ch).γ (ofL ch).t π.1.v.1 π.1.v.2 (ofL ch).ρ
    | _, _ => False
  accS _ _ b := b.2.1 = true
  goodS π ch := wiringClaim P (ofL ch).t π.1.v.2

variable {O : Type}

theorem breaksK_of_breaks (z : Run F O Verdicts × Transcript) (h : Breaks W C₁ z) :
    BreaksK (quotK W) (quotC C₁ C₂) (quotPiop W) quotView (quotOp W) (gK z) := by
  obtain ⟨⟨hchk, hout⟩, hsat⟩ := h
  refine ⟨⟨hchk, fun i hi _ => ?_, by simp [quotOp, gK, hout]⟩, fun c hc hpre => ?_⟩
  · simp only [quotK, quotRounds, List.length_cons, List.length_nil] at hi
    by_cases h0 : i = 0 <;> simp [quotOp, gK, hout, h0]
  · simp only [extractorK, msgK, gK, quotView, msgsOf, optC, quotC, ListCommit.map,
      List.getD_cons_zero, List.map_map, List.mem_map, Function.comp_apply] at hc
    obtain ⟨g, hg, rfl⟩ := hc
    obtain ⟨g', hg', h1⟩ := hpre
    simp only [Option.some.injEq, Sum.inl.injEq] at hg'
    subst hg'
    exact hsat g hg h1

theorem doomK0_imp (z : Run F O Verdicts × Transcript)
    (h : DoomK (quotC C₁ C₂) quotView (quotOp W) 0 (gK z)) : WitnessDoomed C₁ z := by
  obtain ⟨hacc, hd⟩ := h
  refine ⟨by simpa [quotOp, gK] using hacc, fun g hg hw => hd (some (.inl g)) ?_ ?_⟩
  · simp only [msgK, gK, quotView, msgsOf, optC, quotC, ListCommit.map, List.getD_cons_zero,
      List.map_map, List.mem_map, Function.comp_apply]
    exact ⟨g, hg, rfl⟩
  · simpa [quotOp, gK, ofL_toL] using hw

theorem doomK1_imp (z : Run F O Verdicts × Transcript)
    (h : DoomK (quotC C₁ C₂) quotView (quotOp W) 1 (gK z)) : QuotientDoomed W C₂ z := by
  obtain ⟨hacc, hd⟩ := h
  refine ⟨by simpa [quotOp, gK] using hacc, fun R hR hq => hd (some (.inr R)) ?_ ?_⟩
  · simp only [msgK, gK, quotView, msgsOf, optC, quotC, ListCommit.map, List.getD_cons_succ,
      List.getD_cons_zero, List.map_map, List.mem_map, Function.comp_apply]
    exact ⟨R, hR, rfl⟩
  · simpa [quotOp, gK, ofL_toL] using hq

theorem doomSK_imp (z : Run F O Verdicts × Transcript)
    (h : DoomSK (quotOp (W := W) (O := O)) (gK z)) : WiringDoomed (P := P) z := by
  obtain ⟨hacc, hd⟩ := h
  exact ⟨by simpa [quotOp, gK] using hacc, by simpa [quotOp, gK, ofL_toL] using hd⟩

/-- **The link**: candidates satisfying the witness and quotient openings' claims, with the
wiring claim and the reduction's check, make the opened transcript won at the end
(`accepts_iff`). -/
theorem quot_link (π : RootProof F × O) (ch : List (List F)) (b : Verdicts)
    (cs : List (Option (QM B))) (hchk : (quotOp W).check π ch b)
    (hl : cs.length = (quotK W).rounds.length)
    (hgood : ∀ i (h : i < cs.length), ((quotK W).spec i).root → (quotOp W).good i π ch cs[i])
    (hS : (quotOp W).goodS π ch) :
    ∃ p m c, opened cs (quotView π).2 ch = p ++ [(m, c)] ∧
      (quotPiop W).post (quotView π).1 p m c := by
  match cs, hl, hgood with
  | [c₀, c₁, c₂], _, hgood =>
    have h0 := hgood 0 (by simp) rfl
    have h1 := hgood 1 (by simp) rfl
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
    match c₀, c₁, h0, h1 with
    | some (.inl g), some (.inr R), h0, h1 =>
      refine ⟨[((some (.inl g), []), ch.headD []), ((some (.inr R), []), ch.tail.headD [])],
        (c₂, valsOf π.1.v), ch.tail.tail.headD [], rfl, g, R, rfl, rfl, ?_⟩
      have e : ∀ l : List (List F), (c3 (l.headD [])).1 = (ofL l).α ∧
          (c3 (l.headD [])).2.1 = (ofL l).β ∧ (c3 (l.headD [])).2.2 = (ofL l).γ ∧
          c1 (l.tail.headD []) = (ofL l).t ∧ c1 (l.tail.tail.headD []) = (ofL l).ρ :=
        fun l => ⟨rfl, rfl, rfl, rfl, rfl⟩
      simp only [quotView, msgsOf, fromVals_valsOf, (e ch).1, (e ch).2.1, (e ch).2.2.1,
        (e ch).2.2.2.1, (e ch).2.2.2.2]
      exact (accepts_iff _ _ _ _ _ _ _ _ _ _).mpr ⟨h0, hS, hchk, h1⟩

/-- **`AdversaryLog.lean`'s `knowledgeSoundness_composed_adv`, re-derived from the generic
composed theorem** (the witness and quotient openings the roots', the wiring opening the
setup's). -/
theorem knowledgeSoundness_composed_adv_K (A : OracleComp KeccakCalls (RootProof F × O))
    (openings : RootProof F × O → Chals F → OracleComp KeccakCalls Verdicts) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (openings p ch) QV)
    (εW εσ εQ : ℝ≥0∞)
    (hW : Pr{let z ← (simulateQ randomOracle (advExperiment W A openings)).run' ∅}[
      WitnessDoomed C₁ z] ≤ εW)
    (hσ : Pr{let z ← (simulateQ randomOracle (advExperiment W A openings)).run' ∅}[
      WiringDoomed (P := P) z] ≤ εσ)
    (hQd : Pr{let z ← (simulateQ randomOracle (advExperiment W A openings)).run' ∅}[
      QuotientDoomed W C₂ z] ≤ εQ) :
    Pr{let z ← (simulateQ randomOracle (advExperiment W A openings)).run' ∅}[Breaks W C₁ z] ≤
      εW + εσ + εQ + ((Q + 6 + QV : ℕ) : ℝ≥0∞) * ((listFactor C₁.bound C₂.bound : ℝ≥0∞) *
        (roundError P B : ℝ≥0∞) + 5 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  have hexp := expK_quot W A openings
  let εD : ℕ → ℝ≥0∞ := fun i => if i = 0 then εW else if i = 1 then εQ else 0
  have hK := knowledgeSoundness_listChainK (quotK W) (quotC C₁ C₂) (quotPiop W) quotView
    (quotOp W) A (fun p l => openings p (ofL l)) Q QV hQ (fun p ch => hV p (ofL ch))
    (fun π _ _ _ => by simp [FitsAll, RMsg.Fits, quotK, quotRounds, quotView, msgsOf, valsOf])
    (fun π ch b cs hchk hl hgood hS => quot_link W π ch b cs hchk hl hgood hS) εD εσ
    (fun i hi hr => by
      rw [hexp, prEvent_run'_map]
      simp only [quotK, quotRounds, List.length_cons, List.length_nil] at hi
      interval_cases i
      · exact (prEvent_mono _ _ _ fun z h => doomK0_imp W C₁ C₂ z h).trans hW
      · exact (prEvent_mono _ _ _ fun z h => doomK1_imp W C₁ C₂ z h).trans hQd
      · simp [ChainSpec.spec, quotK, quotRounds] at hr)
    (by
      rw [hexp, prEvent_run'_map]
      exact (prEvent_mono _ _ _ fun z h => doomSK_imp W z h).trans hσ)
  rw [hexp, prEvent_run'_map] at hK
  have hnQ : (quotK W).nQ = 6 := rfl
  have hsum : (∑ i ∈ Finset.range (quotK W).rounds.length, εD i) = εW + εQ := by
    simp [εD, quotK, quotRounds, Finset.sum_range_succ]
  rw [hnQ, hsum] at hK
  refine (prEvent_mono _ _ _ fun z h => breaksK_of_breaks W C₁ C₂ z h).trans (hK.trans ?_)
  rw [add_comm εW εQ, add_assoc εQ, add_comm εQ (εW + εσ)]
  gcongr
  exact maxErrK_quot_le W C₁ C₂

/-- **`AdversaryLog.lean`'s `knowledgeSoundness_merkle_adv`, re-derived**: the Merkle-path
statement at the sizes of `quotient::protocol`, from the generic composed theorem. -/
theorem knowledgeSoundness_merkle_adv_K (hq : Fintype.card F = 2 ^ 192) (hN : P.nCells = 2 ^ 24)
    (hw : P.words = 8) (hd : B.identity ≤ 2 ^ 28)
    (c₁ : TableCode B.Msg₁) (c₂ : TableCode B.Msg₂) (h₁ : c₁.bound ≤ 2 ^ 18)
    (h₂ : c₂.bound ≤ 2 ^ 18)
    (A : OracleComp KeccakCalls (RootProof F × O))
    (openings : RootProof F × O → Chals F → OracleComp KeccakCalls Verdicts) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (openings p ch) QV)
    (εW εσ εQ : ℝ≥0∞)
    (hW : Pr{let z ← (simulateQ randomOracle (advExperiment W A openings)).run' ∅}[
      WitnessDoomed c₁.commit z] ≤ εW)
    (hσ : Pr{let z ← (simulateQ randomOracle (advExperiment W A openings)).run' ∅}[
      WiringDoomed (P := P) z] ≤ εσ)
    (hQd : Pr{let z ← (simulateQ randomOracle (advExperiment W A openings)).run' ∅}[
      QuotientDoomed W c₂.commit z] ≤ εQ) :
    Pr{let z ← (simulateQ randomOracle (advExperiment W A openings)).run' ∅}[
        Accepted (P := P) z ∧ ∀ g ∈ adversaryExtractor c₁ z.2 z.1.proof,
          ¬ P.Sat (W.decode z.1.proof.stmt) (P.cells g.1)] ≤
      εW + εσ + εQ + ((Q + 6 + QV : ℕ) : ℝ≥0∞) * (((1 / 2 ^ 128 : ℝ≥0) : ℝ≥0∞) +
        5 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  refine (knowledgeSoundness_composed_adv_K W c₁.commit c₂.commit A openings Q QV hQ hV εW εσ εQ
    hW hσ hQd).trans ?_
  gcongr
  exact listError_le_generic hq hN hw hd h₁ h₂

end Compose
