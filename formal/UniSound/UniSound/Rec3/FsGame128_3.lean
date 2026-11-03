-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The main line's `FsGame128.lean` (`hops_uni`,
-- `fsLayer128_of_gameV`) for π1-rec3, through `Compose`'s `knowledgeSoundness_listChainU_closed128`,
-- `prEvent_doomF_le` and `prEvent_pairTr_expL_le`. Kept apart from `FsFinal3.lean`'s bridges, which bring
-- `Completeness`'s instance of `SampleableType E`.
import UniSound.Rec3.Fs128_3
import UniSound.FsGame128

/-!
# π1-rec3's Fiat–Shamir layer at `≥ 128` bits, from the coupling

* **`hops_uni3`**: π1-rec3's three openings' shapes (`C1`, `C2`, the setup: plain layouts of `2^24 ..= 2^28`
  words) are among `WhirBridge.largeShapes`.
* **`fsLayer128_3_of_gameV`**: `FsLayer128_3` from the coupling `UniGameLeV3` (`FsGame3.lean`; proved in
  `FsFinal3.lean`), the numbers `UniNumbers3` and the IV `UniIv3`, as `fsLayer3_of_gameV`, with the composed
  theorem's three terms bounded as `fsLayer128_of_gameV`'s: the openings once (`prEvent_doomF_le` at `largeShapes`,
  `QV = 10122`), the seed's pair (`prEvent_pairTr_expL_le`, `hlab_uni3`), the chain (`maxErrK_uni3`), then
  `le_uniBound128` (its openings' sum `≤ 5 · 10122` holds with three, `sumQO_le3`).
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack

section Layer

variable (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ) (C : UniCode3 D F3 nV np)
  (hs : UniShapes D)

/-- **π1-rec3's three openings' shapes are among `largeShapes`**: each a plain layout of `2^v` words,
`24 ≤ v ≤ 28`, at rate `1/2`. -/
theorem hops_uni3 : ∀ o ∈ uOps3 D F3 nV np C hs, ∃ s ∈ largeShapes, s.L = o.S.L ∧ s.R = o.S.R := by
  intro o ho
  simp only [uOps3, uniOps3, List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl
  all_goals
    dsimp only [shapeK, plainShape, WhirShape.large]
    exact largeShapes_plain _ (hs.lo _ (by decide)) (hs.hi _ (by decide))

/-- **π1-rec3's Fiat–Shamir layer at `≥ 128` bits from the coupling with the IV in the verifier**:
`fsLayer3_of_gameV` with `knowledgeSoundness_listChainU_closed128` and its three terms bounded. -/
theorem fsLayer128_3_of_gameV (hN : UniNumbers3 D F3 nV np C hs) (hI : UniIv3 D)
    (hG : UniGameLeV3 D F3 nV np C hs) : FsLayer128_3 D F3 nV np C := by
  intro R e herr hpre hFin A Q hQ
  obtain ⟨A₀, hA₀, hle⟩ := rpm_le_kcS (uSetup D hs) (hOnly_setupK3 hs _ _ _) setupQS
    (setupQS * 2 ^ 32) (isTotalQueryBound_setupK3 hs _ _ _) (cost_setupK3 hs _ _ _) uFix (uAdv A) Q
    (cost_uAdv A Q hQ) (uVerIv3 D F3 nV np C hs) (duplexVm_uVerIv3 D F3 nV np C hs) (2 ^ 80 + 8)
    (cost_uVerIv3 D F3 nV np C hs hN hI)
    (fun z tr => UniBreaksRel3 D F3 nV np C hs (ivOut z, tr))
    (fun z tr tr' h hz => uniBreaksRel3_congr D F3 nV np C hs (ivOut z) tr tr' h hz)
  have hmain := knowledgeSoundness_listChainU_closed128 (uSpec3 F3 nV np)
    (liftPiop (uSpec3 F3 nV np).K R rfl) (uView (uRounds3 F3 nV np)) (uOps3 D F3 nV np C hs)
    (fun i => uniTc hs i) (uniCheck3 D F3 nV np C) (uniGood3 D F3 nV np C) (uniGoodS3 D F3 nV np C)
    (uSetup D hs) uFix (ivAdv3 D A₀) setupQS (setupQS + Q + 1) (isTotalQueryBound_setupK3 hs _ _ _)
    (isTotalQueryBound_ivAdv3 D A₀ _ hA₀) (hok_uni3 D F3 nV np C hs) (hcov_uni3 D F3 nV np C hs)
    (hS_uni3 D F3 nV np C hs) (fun π _ _ => fitsAll_uView _ π)
    (fun π ch cs hc hl hg hn hgS => hlink_uni3 D F3 nV np C R hFin π ch cs hc hl hg hn hgS)
    name (hlab_uni3 D F3 nV np hs A₀)
  have hkc : Pr{let z ← (simulateQ randomOracle
        (kcGameS (uSetup D hs) uFix A₀ (uVerIv3 D F3 nV np C hs))).run' ∅}[
        UniBreaksRel3 D F3 nV np C hs (ivOut z.1, z.2)] ≤
      Pr{let z ← (simulateQ randomOracle (expU (uSpec3 F3 nV np) (uView (uRounds3 F3 nV np))
          (withSetupG (uSetup D hs) uFix (ivAdv3 D A₀))
          (opsRun (uView (uRounds3 F3 nV np)) (uOps3 D F3 nV np C hs)))).run' ∅}[
        BreaksOK (uSpec3 F3 nV np).K (fun i => (uniTc hs i).commit) (liftPiop (uSpec3 F3 nV np).K R rfl)
          (uView (uRounds3 F3 nV np)) (uniCheck3 D F3 nV np C)
          (fun bs => ∀ k < (uOps3 D F3 nV np C hs).length, bs.getD k false = true) z] := by
    rw [expU_ivAdv3, run'_simulateQ_map, prEvent_map]
    refine prEvent_mono _ _ _ fun w hw => ?_
    have hb := breaksOK_of_rel3 D F3 nV np C hs R hpre _ hw
    have hlen : (ivInput3 D w.1.1.roots).length = D.programIv.length + 289 := length_ivInput3 _ _
    have h64 : (ivInput3 D w.1.1.roots).length ≠ 64 := by rw [hlen]; omega
    have hl : (ivInput3 D w.1.1.roots).length ≠ (uniTc hs 0).leafLen := by
      rw [hlen, leafLen_uniTc_zero]
      have := hI.ne
      omega
    have he := extractorK_append (uniTc hs) (uView (uRounds3 F3 nV np)) (ivOut w.1) w.2
      (ivInput3 D w.1.1.roots, w.1.2.1) h64 hl
    refine ⟨hb.1, hb.2.1, fun c hc => hb.2.2 c ?_⟩
    rw [← he]
    exact hc
  -- The run before the openings, and its queries.
  set X := preU (uSpec3 F3 nV np) (uView (uRounds3 F3 nV np))
    (withSetupG (uSetup D hs) uFix (ivAdv3 D A₀)) with hXdef
  have hX : IsTotalQueryBound X (setupQS + (setupQS + Q + 1) + (uSpec3 F3 nV np).K.nQ) :=
    isTotalQueryBound_preU _ _ _ _ (isTotalQueryBound_withSetupG _ _ _ _ _
      (isTotalQueryBound_setupK3 hs _ _ _) (isTotalQueryBound_ivAdv3 D A₀ _ hA₀))
  -- The openings, once.
  have hdoom := prEvent_doomF_le εExact largeShapes largeShapes_nodup (uView (uRounds3 F3 nV np))
    (uOps3 D F3 nV np C hs) (hops_uni3 D F3 nV np C hs) X _ hX 10122 largeShapes_QO_le
  -- The seed's pair.
  have hpair := prEvent_pairTr_expL_le (uView (uRounds3 F3 nV np)) X (uOps3 D F3 nV np C hs) _ hX
    name name_length
  refine (hG A).trans (hle.trans (add_le_add (hkc.trans hmain) le_rfl) |>.trans ?_)
  have hS := setupQS_le D hs
  have hn := hN.chain
  have hq : ((uOps3 D F3 nV np C hs).map fun o => o.S.QO).sum ≤ 5 * 10122 :=
    (sumQO_le3 D F3 nV np C hs).trans (by norm_num)
  exact le_uniBound128 e Q setupQS (uSpec3 F3 nV np).K.nQ _ (uSpec3 F3 nV np).nRf 10122 hS hn hq
    (show (5 : ℕ) ≤ 6 by decide) le_rfl _ _ _ hdoom hpair (maxErrK_uni3 D F3 nV np hs R e herr)

/-- `fsLayer128_3_of_gameV` with the numbers from the rounds' sizes (`uniNumbers3_of`). -/
theorem fsLayer128_3_of_gameV' (hnQ : (uSpec3 F3 nV np).K.nQ ≤ 2 ^ 10)
    (hnv : ∀ r ∈ uRounds3 F3 nV np, r.nv ≤ 2 ^ 30) (hI : UniIv3 D) (hG : UniGameLeV3 D F3 nV np C hs) :
    FsLayer128_3 D F3 nV np C :=
  fsLayer128_3_of_gameV D F3 nV np C hs (uniNumbers3_of D F3 nV np C hs hnQ hnv) hI hG

end Layer

end UniSound

/-- info: 'UniSound.hops_uni3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.hops_uni3

/-- info: 'UniSound.fsLayer128_3_of_gameV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.fsLayer128_3_of_gameV
