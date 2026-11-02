-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The instance of `ListChainKDoom.lean`'s closed theorem that is `quotient::protocol`'s (the
-- chain of `ListChainKInstance.lean`, the witness, wiring and quotient openings of
-- `DeployedWired.lean`, the wiring stack's setup of `WiringSetup.lean`), of this repository.
import Compose.ListChainKDoom
import Compose.ListChainKInstance

/-!
# `quotient::protocol` as an instance: two proof openings and the setup's

`ListChainKInstance.lean` makes the reduction's chain (`quotK`, `quotPiop`, `quotView`) an
instance of the `k`-round chain. Here its three openings are `ListChainKDoom.lean`'s, in the
deployed order (`quotOps`): the witness opening at round `0`'s root (the witness layout, the
decoder `c₁` read back as the first message), the wiring opening at the setup's root (the proof's
`ir`, the setup the wiring stack's tree, `stackSetup`), the quotient opening at round `1`'s root,
each at its deployed layout (`WhirShape.small`, F2's `ours_sound`).

**`knowledgeSoundness_merkle_closed`**: `knowledgeSoundness_listChainK_closed` at this instance,
with what `DeployedWired.lean`'s `knowledgeSoundness_wired` assumes (`WitnessMatch`,
`QuotientMatch`, the wiring stack's claims `WiringClaims`): its bound is
`knowledgeSoundness_wired`'s, term for term,

`openingBound (QS + Q + 6) + openingBound (QS + Q + 6 + QO) + openingBound (QS + Q + 6 + 2 QO)
  + N (max L₁ (L₁ L₂) · roundError + 5 N / 2^256)`,  `QO = 10122`, `N = QS + Q + 6 + 3 QO`,

`QS = 2^(ht + 1)` the setup's queries: the three doom terms are the generic `doomSum`, the list
term the generic `maxErrK` (`maxErrK_quotTC_le`). The event is the generic one: the verifier's
check and the three openings accept, and no candidate of the first root read off the adversary's
(and the setup's) queries satisfies F1's first state.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm QuotientSecurity QuotientSecurity.Params LeanVM LeanVM.Protocol LeanVM.Semantics
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## Matching an opening -/

section Match

variable {Pf F M M' σ : Type} [SampleableType F]

/-- A table code's messages, mapped. -/
def TableCode.map (f : M → M') (c : TableCode M) : TableCode M' where
  height := c.height
  leafLen := c.leafLen
  bound := c.bound
  dec w := (c.dec w).map f
  length_dec w := by rw [List.length_map]; exact c.length_dec w

/-- **A round's opening matched by a decoder** (`Deployed.lean`'s `WitnessMatch`, mapped into the
protocol's messages). -/
theorem whirOp_ok_round (S : WhirShape) (cl : Pf → List (List F) → Stmt S.L.stacking)
    (prf : Pf → Proof) (i : ℕ) (rd : Column S.L.logN → M) (f : M → M') (c : TableCode M)
    (tc : ℕ → TableCode M') (htc : tc i = c.map f) (hh : c.height = rootHeight S.L.logN S.R)
    (hl : c.leafLen = 8 * 2 ^ laneFold)
    (hc : ∀ w q, q ∈ Candidates S.L.logN S.R (code₀ S.L.logN S.R).thr
      (wordOfMerkle c.height (2 ^ laneFold) w) → rd q ∈ c.dec w)
    (good : ℕ → Pf → List (List F) → Option M' → Prop)
    (hg : ∀ π ch q, (∀ cl' ∈ (cl π ch).claims, S.L.tableEval q cl'.point = cl'.value) →
      good i π ch (some (f (rd q))))
    (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf) :
    WhirOp.OK tc good setup fix (⟨S, cl, prf, .round i (f ∘ rd)⟩ : WhirOp Pf F M') := by
  unfold WhirOp.OK
  dsimp only
  rw [htc]
  exact ⟨hh, hl, fun w q hq => List.mem_map.mpr ⟨rd q, hc w q hq, rfl⟩, hg⟩

end Match

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : Params F} {B : P.Bounds} (W : Wire P B) (D : Deploy F)

/-! ## The instance -/

/-- The two roots' decoders, round by round, into the common message type. -/
def quotTC (c₁ : TableCode B.Msg₁) (c₂ : TableCode B.Msg₂) : ℕ → TableCode (QM B)
  | 1 => c₂.map Sum.inr
  | _ => c₁.map Sum.inl

variable (r : ℕ) (h1 : WhirBridge.minLogRows ≤ r) (h2 : r ≤ WhirBridge.maxLogRows)
  (hLw : D.Lw = witnessLayout r) (hLσ : D.Lσ = wiringLayout r) (hLQ : D.LQ = quotientLayout r)

/-- **The reduction's three openings**, in the deployed order: the witness opening at round `0`'s
root, the wiring opening at the setup's root (the proof's `ir`), the quotient opening at round
`1`'s root. -/
noncomputable def quotOps (rd₁ : Column D.Lw.logN → B.Msg₁) (rd₂ : Column D.LQ.logN → B.Msg₂)
    (q₀ : Column D.Lσ.logN) : List (WhirOp (RootProof F × OpenProofs) F (QM B)) :=
  [⟨WhirShape.small r h1 h2 D.Lw (Or.inl hLw), fun π ch => D.clW π.1 (ofL ch), fun π => π.2.1,
      .round 0 (Sum.inl ∘ rd₁)⟩,
    ⟨WhirShape.small r h1 h2 D.Lσ (Or.inr (Or.inl hLσ)), fun π ch => D.clσ π.1 (ofL ch),
      fun π => π.2.2.1, .setup (fun π => π.1.ir) q₀⟩,
    ⟨WhirShape.small r h1 h2 D.LQ (Or.inr (Or.inr hLQ)), fun π ch => D.clQ π.1 (ofL ch),
      fun π => π.2.2.2, .round 1 (Sum.inr ∘ rd₂)⟩]

/-- The reduction's own check. -/
def quotChk (π : RootProof F × OpenProofs) (ch : List (List F)) : Prop :=
  reductionCheck P (ofL ch).α (ofL ch).β (ofL ch).t π.1.v.1 π.1.v.2

/-- **The factor-weighted error is at most `listFactor L₁ L₂ · roundError`.** -/
theorem maxErrK_quotTC_le (c₁ : TableCode B.Msg₁) (c₂ : TableCode B.Msg₂) :
    maxErrK (quotK W) (fun i => (quotTC c₁ c₂ i).commit) (quotPiop W) ≤
      (listFactor c₁.commit.bound c₂.commit.bound : ℝ≥0∞) * (roundError P B : ℝ≥0∞) := by
  unfold maxErrK
  refine Finset.sup_le fun j hj => ?_
  simp only [quotK, quotRounds, List.length_cons, List.length_nil, Finset.mem_range] at hj
  show (facL (fun i => (quotTC c₁ c₂ i).commit) 0 (quotRounds.take (j + 1)) : ℝ≥0∞) *
    (roundError P B : ℝ≥0∞) ≤ _
  gcongr
  have h1 := le_listFactor_left c₁.commit.bound c₂.commit.bound
  have h2 := le_listFactor_right c₁.commit.bound c₂.commit.bound
  have e0 : (quotTC c₁ c₂ 0).commit.bound = c₁.commit.bound := rfl
  have e1 : (quotTC c₁ c₂ 1).commit.bound = c₂.commit.bound := rfl
  interval_cases j <;> simp [facL, quotRounds, e0, e1] <;> omega

/-- **Knowledge soundness of `quotient::protocol` from the closed generic theorem**: the chain of
`ListChainKInstance.lean`, the witness, wiring and quotient openings at their deployed layouts
(`17 ≤ log_rows ≤ 22`), the setup the wiring stack's tree, every opening's doom F2's
`ours_sound`. The bound is `DeployedWired.lean`'s `knowledgeSoundness_wired`'s at
`QS = setupQueries D`. -/
theorem knowledgeSoundness_merkle_closed (c₁ : TableCode B.Msg₁) (c₂ : TableCode B.Msg₂)
    (mW : WitnessMatch D c₁) (mQ : QuotientMatch W D c₂) (q₀ : Column D.Lσ.logN)
    (hclσ : WiringClaims (P := P) D q₀) (hR : D.R = logInvRate)
    (A₀ : Bytes32 → OracleComp KeccakCalls (RootProof F × OpenProofs)) (Q : ℕ)
    (hQ : ∀ ir, IsTotalQueryBound (A₀ ir) Q) :
    Pr{let z ← (simulateQ randomOracle (expK (quotK W) quotView
        (withSetupG (stackSetup D q₀) withIr A₀)
        (opsRun quotView (quotOps D r h1 h2 hLw hLσ hLQ mW.read mQ.read q₀)))).run' ∅}[
        BreaksOK (quotK W) (fun i => (quotTC c₁ c₂ i).commit) (quotPiop W) quotView
          (quotChk (P := P)) (fun bs => ∀ k < 3, bs.getD k false = true) z] ≤
      openingBound (setupQueries D + Q + 6) + openingBound (setupQueries D + Q + 6 + 10122) +
        openingBound (setupQueries D + Q + 6 + 10122 + 10122) +
        ((setupQueries D + Q + 6 + 10122 + 10122 + 10122 : ℕ) : ℝ≥0∞) *
          ((listFactor c₁.commit.bound c₂.commit.bound : ℝ≥0∞) * (roundError P B : ℝ≥0∞) +
          5 * ((setupQueries D + Q + 6 + 10122 + 10122 + 10122 : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  set ops := quotOps D r h1 h2 hLw hLσ hLQ mW.read mQ.read q₀ with hops
  -- The openings' matches.
  have hhW : c₁.height = rootHeight D.Lw.logN logInvRate := by rw [← hR]; exact mW.height
  have hhQ : c₂.height = rootHeight D.LQ.logN logInvRate := by rw [← hR]; exact mQ.height
  have hcW : ∀ w q, q ∈ Candidates D.Lw.logN logInvRate (code₀ D.Lw.logN logInvRate).thr
      (wordOfMerkle c₁.height (2 ^ laneFold) w) → mW.read q ∈ c₁.dec w := by
    rw [← hR]; exact mW.complete
  have hcQ : ∀ w q, q ∈ Candidates D.LQ.logN logInvRate (code₀ D.LQ.logN logInvRate).thr
      (wordOfMerkle c₂.height (2 ^ laneFold) w) → mQ.read q ∈ c₂.dec w := by
    rw [← hR]; exact mQ.complete
  have hσw : ∀ (T : KTable) (H : Hist), (∀ x, Sum.inl x ∈ (tableQueryLog (stackSetup D q₀) T).map
      Sigma.fst → x ∈ H) → Set.InjOn (viewT T) ↑H → ∀ v < 2 ^ rootHeight D.Lσ.logN logInvRate,
        Rom.extract (ansOf H (viewT T))
          (ofB (evalWithAnswerFn (QueryImpl.ofFn T) (stackSetup D q₀)))
          (rootHeight D.Lσ.logN logInvRate) (2 ^ laneFold) v =
        LeanVM.Protocol.Whir.Complete.stackWord D.Lσ.logN q₀ v := by
    intro T H hsub hinj v hv
    have hht : rootHeight D.Lσ.logN logInvRate = rootHeight D.Lσ.logN D.R := by rw [hR]
    rw [hht] at hv ⊢
    exact extract_wiringSetup (rootHeight D.Lσ.logN D.R) (2 ^ laneFold)
      (LeanVM.Protocol.Whir.Complete.stackWord D.Lσ.logN q₀)
      (LeanVM.Protocol.Whir.Complete.wellShaped_stackWord _ q₀) T H hsub hinj v hv
  have hok : ∀ o ∈ ops, WhirOp.OK (quotTC c₁ c₂) (quotOp W (O := OpenProofs)).good
      (stackSetup D q₀) withIr o := by
    intro o ho
    simp only [hops, quotOps, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · exact whirOp_ok_round (WhirShape.small r h1 h2 D.Lw (Or.inl hLw))
        (fun (π : RootProof F × OpenProofs) ch => D.clW π.1 (ofL ch))
        (fun π : RootProof F × OpenProofs => π.2.1) 0 mW.read Sum.inl c₁ (quotTC c₁ c₂)
        rfl hhW mW.leaf hcW _
        (fun (π : RootProof F × OpenProofs) ch q h => mW.claims π.1 (ofL ch) q h) _ _
    · exact ⟨LeanVM.Protocol.Whir.Complete.stackWord D.Lσ.logN q₀, honest_stackWord _ _ q₀,
        fun T H _ hsub hinj v hv => hσw T H hsub hinj v hv⟩
    · exact whirOp_ok_round (WhirShape.small r h1 h2 D.LQ (Or.inr (Or.inr hLQ)))
        (fun (π : RootProof F × OpenProofs) ch => D.clQ π.1 (ofL ch))
        (fun π : RootProof F × OpenProofs => π.2.2.2) 1 mQ.read Sum.inr c₂ (quotTC c₁ c₂)
        rfl hhQ mQ.leaf hcQ _
        (fun (π : RootProof F × OpenProofs) ch q h => mQ.claims π.1 (ofL ch) q h) _ _
  -- Every root is opened.
  have hcov : ∀ i < (quotK W).rounds.length, ((quotK W).spec i).root →
      ∃ o ∈ ops, ∃ rd, o.tgt = .round i rd := by
    intro i hi hr
    simp only [quotK, quotRounds, List.length_cons, List.length_nil] at hi
    interval_cases i
    · exact ⟨_, List.mem_cons_self, _, rfl⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), _, rfl⟩
    · simp [ChainSpec.spec, quotK, quotRounds] at hr
  -- The wiring stack's claims give F1's wiring claim.
  have hS : ∀ π ch, (∀ o ∈ ops, WhirOp.SetupHolds o π ch) →
      (quotOp W (O := OpenProofs)).goodS π ch := fun π ch h =>
    hclσ π.1 (ofL ch) (h _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have h := knowledgeSoundness_listChainK_closed (quotK W) (quotPiop W) quotView ops
    (quotTC c₁ c₂) (quotChk (P := P)) (quotOp W (O := OpenProofs)).good
    (quotOp W (O := OpenProofs)).goodS (stackSetup D q₀) withIr A₀ (setupQueries D) Q
    (isTotalQueryBound_stackSetup D q₀) hQ hok hcov hS
    (fun π _ _ => by simp [FitsAll, RMsg.Fits, quotK, quotRounds, quotView, msgsOf, valsOf])
    (fun π ch cs hchk hl hgood hS' => quot_link W π ch (false, false, false) cs hchk hl hgood hS')
  have hn : setupQueries D + Q + (quotK W).nQ + (ops.map fun o => o.S.QO).sum =
      setupQueries D + Q + 6 + 10122 + 10122 + 10122 := by
    have e : (quotK W).nQ = 6 := rfl
    simp only [hops, quotOps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      WhirShape.small, e]
    omega
  have hd : doomSum ops (setupQueries D + Q + (quotK W).nQ) =
      openingBound (setupQueries D + Q + 6) + openingBound (setupQueries D + Q + 6 + 10122) +
        openingBound (setupQueries D + Q + 6 + 10122 + 10122) := by
    have e : (quotK W).nQ = 6 := rfl
    simp only [hops, quotOps, doomSum, WhirShape.small, e, add_zero, add_assoc]
  have hlen : ops.length = 3 := rfl
  rw [hn, hd, hlen] at h
  refine h.trans ?_
  gcongr
  exact maxErrK_quotTC_le W c₁ c₂

end Compose
