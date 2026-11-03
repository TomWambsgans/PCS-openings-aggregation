-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The port of `formal/UniSound/UniSound/FsGame128.lean`
-- (`fsLayer128_of_gameV`) and `Fs128.lean` (`le_uniBound128`) to π2's verifier, through
-- `Compose.knowledgeSoundness_listChainU_closed128S` (the setup's stacks and the protocol read off the setup),
-- `Compose.prEvent_doomF_le` (the six openings once) and `Compose.prEvent_pairTr_expL_le` (the seed's pair).
import RecCompose.FsOps
import RecCompose.FsSetup
import RecCompose.FsExtract
import RecCompose.FsWalk
import Compose.FirstDoom
import Compose.SeedPair

/-!
# π2's Fiat–Shamir layer, from its bridges

**`pi2FsLayer_of`**: `Pi2FsLayer D` at the real deployment from the coupling (`Pi2GameLeV`'s inequality, `hG`) and the
composed verifier's facts (its duplex shape and cost, the IV moved into the adversary, the extractor's word unchanged
by the IV's log, the seed's first 32 bytes, the event read through the transcript's answers), as
`UniSound.fsLayer128_of_gameV`:

* `rpm_le_kcS`: the random-permutation game to the two-oracle game (the permutation's term);
* the IV moved into the adversary (`hexpU`), the event to the framework's `BreaksOK` at the protocol of the setup's
  roots (`liftPiop2 (R (rootsOfOut s))`, `hpre`; the extractor's word read before the IV's log, `hext`);
* `knowledgeSoundness_listChainU_closed128S` on π2's chain, six openings (`okp_*`), setup (`p2Setup_noLabel`),
  the last link from `Pi2FsLayer`'s (`hlink_p2`), `maxErrK ≤ e` (`maxErrK_p2`);
* the openings once (`prEvent_doomF_le` at `p2Shapes`, `QV = 9018`) and the seed's pair (`prEvent_pairTr_expL_le`);
* the numbers (`le_pi2BoundE`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open OracleSpec OracleComp
open scoped ENNReal

attribute [local instance high] Completeness.instSampleableTypeE_completeness

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack RecStatement.layoutWords

/-! ## The numbers -/

section Bits

theorem le256' {a b : ℕ} (h : a ≤ b) : (a : ℝ≥0∞) / 2 ^ 256 ≤ (b : ℝ≥0∞) / 2 ^ 256 :=
  ENNReal.div_le_div_right (Nat.cast_le.mpr h) _

/-- **The composed bound is at most `pi2BoundE`**: the openings' term at `N + QV` queries, the seed's pair and the
chain's at `N`, the permutation's at `QS 2^32 + Q + 2^48` calls, `N` the two-oracle game's queries (the setup's four
trees, the adversary and the IV, the chain, the six openings). -/
theorem le_pi2BoundE (e : ℝ≥0∞) (Q QS nQ SQO nRf QV : ℕ) (hQS : QS ≤ 3 * 2 ^ 24 + 2 ^ 21)
    (hnQ : nQ ≤ 2 ^ 10) (hSQO : SQO ≤ 6 * 10122) (hr : nRf ≤ 6) (hQV : QV ≤ 10122) (d p m : ℝ≥0∞)
    (hd : d ≤ ((QS + (QS + Q + 4) + nQ + SQO + QV : ℕ) : ℝ≥0∞) *
      (269 * (2 : ℝ≥0∞)⁻¹ ^ 137 +
        ((5 * (QS + (QS + Q + 4) + nQ + SQO + QV) : ℕ) : ℝ≥0∞) / 2 ^ 256))
    (hp : p ≤ ((2 * (QS + (QS + Q + 4) + nQ + SQO) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256)
    (hm : m ≤ e) :
    d + p + ((QS + (QS + Q + 4) + nQ + SQO : ℕ) : ℝ≥0∞) *
        (m + (((nRf + 2) * (QS + (QS + Q + 4) + nQ + SQO) : ℕ) : ℝ≥0∞) / 2 ^ 256) +
      ((QS * 2 ^ 32 + Q + 2 ^ 48 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 ≤ pi2BoundE e Q := by
  have h33 : (2 : ℕ) ^ 33 = 8589934592 := by norm_num
  have h24 : (2 : ℕ) ^ 24 = 16777216 := by norm_num
  have h21 : (2 : ℕ) ^ 21 = 2097152 := by norm_num
  have h10 : (2 : ℕ) ^ 10 = 1024 := by norm_num
  have hN : QS + (QS + Q + 4) + nQ + SQO ≤ pi2N Q := by unfold pi2N; omega
  have hNV : QS + (QS + Q + 4) + nQ + SQO + QV ≤ pi2N Q := by unfold pi2N; omega
  have b1 : d ≤ (pi2N Q : ℝ≥0∞) * (269 * (2 : ℝ≥0∞)⁻¹ ^ 137 + ((5 * pi2N Q : ℕ) : ℝ≥0∞) / 2 ^ 256) :=
    hd.trans (mul_le_mul' (Nat.cast_le.mpr hNV) (add_le_add le_rfl (le256' (Nat.mul_le_mul_left 5 hNV))))
  have b2 : p ≤ ((2 * pi2N Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
    hp.trans (le256' (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hN 2)))
  have b3 : ((QS + (QS + Q + 4) + nQ + SQO : ℕ) : ℝ≥0∞) *
        (m + (((nRf + 2) * (QS + (QS + Q + 4) + nQ + SQO) : ℕ) : ℝ≥0∞) / 2 ^ 256) ≤
      (pi2N Q : ℝ≥0∞) * (e + ((8 * pi2N Q : ℕ) : ℝ≥0∞) / 2 ^ 256) :=
    mul_le_mul' (Nat.cast_le.mpr hN) (add_le_add hm (le256' (Nat.mul_le_mul (by omega) hN)))
  have b4 : ((QS * 2 ^ 32 + Q + 2 ^ 48 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 ≤
      ((2 ^ 81 + Q : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 := by
    refine ENNReal.div_le_div_right (pow_le_pow_left₀ bot_le (Nat.cast_le.mpr ?_) 2) _
    have h32 : QS * 2 ^ 32 ≤ (3 * 2 ^ 24 + 2 ^ 21) * 2 ^ 32 := Nat.mul_le_mul_right _ hQS
    have h81 : (3 * 2 ^ 24 + 2 ^ 21) * 2 ^ 32 + 2 ^ 48 ≤ (2 : ℕ) ^ 81 := by norm_num
    calc QS * 2 ^ 32 + Q + 2 ^ 48 = (QS * 2 ^ 32 + 2 ^ 48) + Q := by ring
      _ ≤ 2 ^ 81 + Q := Nat.add_le_add_right ((Nat.add_le_add_right h32 _).trans h81) Q
  unfold pi2BoundE
  calc _ ≤ (pi2N Q : ℝ≥0∞) * (269 * (2 : ℝ≥0∞)⁻¹ ^ 137 + ((5 * pi2N Q : ℕ) : ℝ≥0∞) / 2 ^ 256) +
        ((2 * pi2N Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        (pi2N Q : ℝ≥0∞) * (e + ((8 * pi2N Q : ℕ) : ℝ≥0∞) / 2 ^ 256) +
        ((2 ^ 81 + Q : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 :=
      add_le_add (add_le_add (add_le_add b1 b2) b3) b4
    _ = _ := by ring

end Bits

/-! ## The links -/

section Links

variable (D : RecDeployment) (hD : RecDeployment.Real D) (hs : UniSound.UniShapes D.pi1)

include hD in
theorem circuitAt_real (roots : UniStatement.SetupRoots) : (D.circuitAt roots).circuit = cc := hD.1 _

/-- **The six openings' `OKP`.** -/
theorem hok_p2 : ∀ o ∈ p2Ops D, WhirOp.OKP p2Tc p2Good (p2Setup D hs) p2Fix (p2Stk D) o := by
  intro o ho
  simp only [p2Ops, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
  · exact okp_pi1 D hs 0 _ _ _
  · exact okp_pi1 D hs 1 _ _ _
  · exact okp_pi1 D hs 2 _ _ _
  · exact okp_W D hs
  · exact okp_setupOp D hs
  · exact okp_Q D hs

/-- A list of length three. -/
theorem list_three_eq {α : Type} (l : List α) (h : l.length = 3) (d : α) :
    l = [l.getD 0 d, l.getD 1 d, l.getD 2 d] := by
  match l, h with
  | [a, b, c], _ => rfl

/-- A list of length `n + 1` is its first `n` entries and its last. -/
theorem take_getD_eq {α : Type} : ∀ (l : List α) (n : ℕ), l.length = n + 1 → ∀ d : α, l.take n ++ [l.getD n d] = l
  | [a], 0, _, _ => rfl
  | a :: l, n + 1, h, d => by
    simp only [List.take_succ_cons, List.getD_cons_succ, List.cons_append]
    rw [take_getD_eq l n (by simpa using h) d]
  | [], _, h, _ => by simp at h
  | _ :: _ :: _, 0, h, _ => by simp at h

/-- A list of length one. -/
theorem list_one_eq {α : Type} (l : List α) (h : l.length = 1) (d : α) : l = [l.getD 0 d] := by
  match l, h with
  | [a], _ => rfl

include hD in
/-- **The composition's last link from `Pi2FsLayer`'s**: candidates good at `W`'s and `Q`'s rounds and `none` at
`ρ`'s, the setup's table good, and the check, make the opened transcript `pi2Opened` then `ρ`'s round, the claims
true (`Pi2ClaimsHold`), so the protocol's last state holds. -/
theorem hlink_p2 (R : RecSetupRoots → Compose.Piop pi2K Stk)
    (hpost : ∀ roots (s : Pi2St) (cW cQ : Stk) (inp : Inputs E), inp.scalars = s.2 →
      inp.a.length = 2 ^ (Spec.of (D.circuitAt roots.pi1).circuit).core.logRow →
      ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp).all ≠ 0 →
      Pi2ClaimsHold D roots inp cW cQ →
      (R roots).post s (pi2Opened cW cQ inp) (none, inp.a ++ [inp.ξ]) [inp.ρ])
    (π : P2Pf) (ch : List (List E)) (cs : List (Option Stk)) (hc : p2Check π ch)
    (hl : cs.length = pi2Spec.K.rounds.length)
    (hg : ∀ i (h : i < cs.length), (pi2Spec.K.spec i).root → p2Good i π ch cs[i])
    (hn : ∀ i (h : i < cs.length), (pi2Spec.K.spec i).root = false → cs[i] = none)
    (hgS : p2GoodS D π ch) :
    ∃ p m c, opened cs (p2View π).2 ch = p ++ [(m, c)] ∧
      (liftPiop2 (R (rootsOfOut π.roots))).post (p2View π).1 p m c := by
  obtain ⟨hsz, hch, hc0, hc1, hc2, hall⟩ := hc
  have hl3 : cs.length = 3 := hl
  have g0 := hg 0 (by omega) rfl
  have g1 := hg 1 (by omega) rfl
  have n2 := hn 2 (by omega) rfl
  unfold p2Good at g0 g1
  rw [ite_eq_left rfl] at g0
  rw [ite_eq_right (by decide), ite_eq_left rfl] at g1
  obtain ⟨cW, hcW, hW⟩ := g0
  obtain ⟨cQ, hcQ, hQ1, hQ2⟩ := g1
  have hcs : cs = [some cW, some cQ, none] := by
    rw [list_three_eq cs hl3 none]
    simp only [List.getD_eq_getElem _ _ (show 0 < cs.length by omega),
      List.getD_eq_getElem _ _ (show 1 < cs.length by omega), List.getD_eq_getElem _ _ (show 2 < cs.length by omega)]
    rw [hcW, hcQ, n2]
  have hvals : ((p2Msgs π).getD 2 default).2 = (p2Inputs π ch).a ++ [(p2Inputs π ch).ξ] := by
    show ((p2Msgs π).getD 2 default).2 = ((p2Msgs π).getD 2 default).2.take 16 ++
      [((p2Msgs π).getD 2 default).2.getD 16 0]
    refine (take_getD_eq _ 16 ?_ 0).symm
    rw [p2Msgs_eq]
    simp
  have hcirc := circuitAt_real D hD (rootsOfOut π.roots).pi1
  have hpost' := hpost (rootsOfOut π.roots) (stOf (p2View π).1) cW cQ (p2Inputs π ch) rfl (by
      rw [hcirc, spec_core_logRow]
      show (((p2Msgs π).getD 2 default).2.take 16).length = 2 ^ 4
      rw [p2Msgs_eq]
      simp) (by rw [hcirc]; exact hall) (by
      unfold Pi2ClaimsHold
      simp only
      rw [hcirc]
      unfold p2GoodS at hgS
      rw [layoutsOf_cc] at hW hQ1 hQ2 hgS ⊢
      exact ⟨hW, hQ1, hQ2, hgS⟩)
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, ch = [a, b, c] := ⟨_, _, _, list_three_eq ch hch []⟩
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hc0 hc1 hc2
  obtain ⟨a0, a1, a2, rfl⟩ : ∃ x y z, a = [x, y, z] := ⟨_, _, _, list_three_eq a hc0 0⟩
  obtain ⟨b0, rfl⟩ : ∃ x, b = [x] := ⟨_, list_one_eq b hc1 0⟩
  obtain ⟨c0, rfl⟩ : ∃ x, c = [x] := ⟨_, list_one_eq c hc2 0⟩
  refine ⟨_, _, _, ?_, hpost'⟩
  rw [hcs]
  unfold p2View
  rw [p2Msgs_eq]
  rw [p2Msgs_eq] at hvals
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hvals
  simp only [List.map_cons, List.map_nil, opened, List.headD_cons, List.tail_cons, UniSound.toRMsg,
    Option.map_some, Option.map_none, hvals]
  rfl

end Links

/-! ## The Fiat–Shamir layer -/

/-- **π2's Fiat–Shamir layer from its bridges** at the real deployment: the coupling (`hG`), the composed verifier's
duplex shape and cost (`hdup`, `hcost`), the IV in the adversary (`hIvAdv`, `hexpU`), the extractor's word before the
IV's log (`hext`), the seed's first 32 bytes (`hlab`), the event read through the transcript's answers (`hcongr`),
the chain's queries (`hnQ`). -/
theorem pi2FsLayer_of (D : RecDeployment) (hD : RecDeployment.Real D) (hs : UniSound.UniShapes D.pi1)
    (hG : ∀ (P : RecSetupRoots → Pi2St → Stk → Prop) (A : RecAdversary),
      Pr{let z ← recSoundnessExperiment2 D A}[acc z = true ∧
          ¬ ∃ w ∈ outcomeCandidates D z, P (rts z) (pi2StmtOf D z) (stkOf w)] ≤
        Pr{let z ← Common.runWithRandomPermutation (rpmGameS (p2Setup D hs) p2Fix (p2Adv A) (p2Ver D))}[
          P2BreaksRel D P (ivOut2 z.1, z.2.1 ++ evalTr (permutationQueries z.2.2))])
    (hdup : ∀ π, LeanVM.Rpm.DuplexVm (p2Ver D π) [])
    (hcost : ∀ π, Common.QueryCostAtMost (p2Ver D π) LeanVM.Rpm.hashBlocks (2 ^ 48))
    (hIvAdv : ∀ (A₀ : SOut → OracleComp KeccakCalls P2Pf) (n : ℕ), (∀ s, IsTotalQueryBound (A₀ s) n) →
      ∀ s, IsTotalQueryBound (p2IvAdv D A₀ s) (n + 4))
    (hexpU : ∀ A₀ : SOut → OracleComp KeccakCalls P2Pf,
      expU pi2Spec p2View (withSetupG (p2Setup D hs) p2Fix (p2IvAdv D A₀)) (opsRun p2View (p2Ops D)) =
        (fun w => (ivOut2 w.1, w.2 ++ ivLog D w.1.1 w.1.2.1)) <$> kcGameS (p2Setup D hs) p2Fix A₀ (p2Ver D))
    (hext : ∀ (z : P2Pf × (List (List E) × List Bool)) (tr : Transcript) (π : P2Pf)
      (x : Bytes32 × Bytes32 × Bytes32 × Bytes32),
      extractorK (fun i => (p2Tc i).commit) p2View (z, tr ++ ivLog D π x) =
        extractorK (fun i => (p2Tc i).commit) p2View (z, tr))
    (hlab : ∀ (A₀ : SOut → OracleComp KeccakCalls P2Pf) (T : KTable), ∃ w,
      Sum.inl w ∈ (tableQueryLog (withSetupG (p2Setup D hs) p2Fix (p2IvAdv D A₀)) T).map Sigma.fst ∧
      (pi2Spec.label (p2View (evalWithAnswerFn (QueryImpl.ofFn T)
          (withSetupG (p2Setup D hs) p2Fix (p2IvAdv D A₀)))).1).take 32 =
        RecStatement.name ++ (viewT T w).toList.take (32 - RecStatement.name.length))
    (hcongr : ∀ (P : RecSetupRoots → Pi2St → Stk → Prop) (z : P2Pf × (List (List E) × List Bool))
      (tr tr' : Transcript), (∀ x, lookTr tr x = lookTr tr' x) → P2BreaksRel D P (z, tr) →
        P2BreaksRel D P (z, tr'))
    (hnQ : pi2Spec.K.nQ ≤ 2 ^ 10) :
    Pi2FsLayer D := by
  intro R e herr P hpre hpost A Q hQ
  obtain ⟨A₀, hA₀, hle⟩ := rpm_le_kcS (p2Setup D hs) (hOnly_p2Setup D hs) (p2QS D) (p2QS D * 2 ^ 32)
    (isTotalQueryBound_p2Setup D hs) (cost_p2Setup D hs) p2Fix (p2Adv A) Q
    (fun s => Common.isWeightBound_map _ (hQ _)) (p2Ver D) hdup (2 ^ 48) hcost
    (fun z tr => P2BreaksRel D P (ivOut2 z, tr)) (fun z tr tr' h hz => hcongr P _ tr tr' h hz)
  have hmain := knowledgeSoundness_listChainU_closed128S pi2Spec p2View
    (fun s => liftPiop2 (R (rootsOfOut s))) (fun π => π.roots) (p2Ops D) p2Tc p2Check p2Good (p2GoodS D)
    (p2Setup D hs) p2Fix (p2Stk D) (p2IvAdv D A₀) (p2QS D) (p2QS D + Q + 4) (isTotalQueryBound_p2Setup D hs)
    (hIvAdv A₀ _ hA₀) (fun _ _ => rfl) (hok_p2 D hs) (hcov_p2 D) (hS_p2 D) (fun π _ _ => hfit_p2 π)
    (fun π ch cs hc hl hg hn hgS => hlink_p2 D hD R hpost π ch cs hc hl hg hn hgS) (p2Setup_noLabel D hs)
    RecStatement.name (hlab A₀) e (fun s => maxErrK_p2 _ e fun j hj => herr _ j hj)
  have hkc : Pr{let z ← (simulateQ randomOracle (kcGameS (p2Setup D hs) p2Fix A₀ (p2Ver D))).run' ∅}[
        P2BreaksRel D P (ivOut2 z.1, z.2)] ≤
      Pr{let z ← (simulateQ randomOracle (expU pi2Spec p2View (withSetupG (p2Setup D hs) p2Fix (p2IvAdv D A₀))
          (opsRun p2View (p2Ops D)))).run' ∅}[
        BreaksOK pi2Spec.K (fun i => (p2Tc i).commit) (liftPiop2 (R (rootsOfOut z.1.1.roots))) p2View p2Check
          (fun bs => ∀ k < (p2Ops D).length, bs.getD k false = true) z] := by
    rw [hexpU A₀, run'_simulateQ_map, prEvent_map]
    refine prEvent_mono _ _ _ fun w hw => ?_
    obtain ⟨h1, h2, h3⟩ := hw
    refine ⟨h1, h2, fun c hc hpre' => ?_⟩
    rw [hext] at hc
    have hc' := hc
    simp only [extractorK, optC, msgK_p2View_zero, List.mem_map] at hc'
    obtain ⟨q, -, rfl⟩ := hc'
    exact h3 _ hc q rfl (hpre _ _ _ _ hpre')
  -- The run before the openings, and its queries.
  set X := preU pi2Spec p2View (withSetupG (p2Setup D hs) p2Fix (p2IvAdv D A₀)) with hXdef
  have hX : IsTotalQueryBound X (p2QS D + (p2QS D + Q + 4) + pi2Spec.K.nQ) :=
    isTotalQueryBound_preU _ _ _ _ (isTotalQueryBound_withSetupG _ _ _ _ _ (isTotalQueryBound_p2Setup D hs)
      (hIvAdv A₀ _ hA₀))
  -- The openings, once.
  have hdoom := prEvent_doomF_le εExact p2Shapes p2Shapes_nodup p2View (p2Ops D) (hops_p2 D) X _ hX 9018
    p2Shapes_QO
  -- The seed's pair.
  have hpair := prEvent_pairTr_expL_le p2View X (p2Ops D) _ hX RecStatement.name name_length
  refine (hG P A).trans (hle.trans (add_le_add (hkc.trans hmain) le_rfl) |>.trans ?_)
  rw [sumQO_p2 D] at hdoom hpair ⊢
  exact le_pi2BoundE e Q (p2QS D) pi2Spec.K.nQ 47566 pi2Spec.nRf 9018 (p2QS_le D hs) hnQ (by norm_num)
    (show 5 ≤ 6 by decide) (by norm_num) _ _ _ hdoom hpair le_rfl

end RecCompose

/-- info: 'RecCompose.le_pi2BoundE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.le_pi2BoundE

/-- info: 'RecCompose.hlink_p2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.hlink_p2

/-- info: 'RecCompose.pi2FsLayer_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2FsLayer_of
