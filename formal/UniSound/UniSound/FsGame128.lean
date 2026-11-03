-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The route is `FsGame.lean`'s
-- `fsLayer_of_gameV` and `FsFinal.lean`'s `fsLayer_holds`, through `Compose`'s
-- `knowledgeSoundness_listChainU_closed128` (the chain without the seed's tag, doom at the run's end),
-- `prEvent_doomF_le` (the openings once, one union family) and `prEvent_pairTr_le` (the seed's pair).
import UniSound.Fs128
import Compose.ListChainUDoom128
import Compose.FirstDoom
import Compose.SeedPair

/-!
# The Fiat–Shamir layer at `≥ 128` bits, proved

* **`hops_uni`**: the five openings' shapes (`C1`, `C2`, the setup, `A0`, `B0`: plain layouts of
  `2^24 ..= 2^28` words) are among `WhirBridge.largeShapes`, the union family of the plain layouts
  at `2^24 ..= 2^28` at the exact certified per-group bound `εExact`.
* **`fsLayer128_of_gameV`**: `FsLayer128` from the coupling `UniGameLeV` (proved in `FsFinal.lean`),
  the numbers and the IV, as `fsLayer_of_gameV`, with the composed theorem's three terms bounded:
  the openings once (`prEvent_doomF_le` at `largeShapes`, `QV = 10122`), the seed's pair
  (`prEvent_pairTr_le`, the label's first 32 bytes `name ‖ iv[0:16]` with `iv` the IV query's
  answer: `hlab_uni`), the chain (`maxErrK ≤ 9952² e`).
* `FsFinal128.lean`'s **`fsLayer128_holds`**: `FsLayer128` at the main line's code-level link, from
  the deployment's numbers (as `fsLayer_holds`).
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

variable (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (nV V : ℕ) (C : UniCode D Fl nV V)
  (hs : UniShapes D)

/-- **The five openings' shapes are among `largeShapes`**: each a plain layout of `2^v` words,
`24 ≤ v ≤ 28`, at rate `1/2`. -/
theorem hops_uni : ∀ o ∈ uOps D Fl nV V C hs, ∃ s ∈ largeShapes, s.L = o.S.L ∧ s.R = o.S.R := by
  intro o ho
  simp only [uOps, uniOps, List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl
  all_goals
    dsimp only [shapeK, plainShape, WhirShape.large]
    exact largeShapes_plain _ (hs.lo _ (by decide)) (hs.hi _ (by decide))

/-- **The Fiat–Shamir layer at `≥ 128` bits from the coupling with the IV in the verifier**:
`fsLayer_of_gameV` with `knowledgeSoundness_listChainU_closed128` and its three terms bounded. -/
theorem fsLayer128_of_gameV (hN : UniNumbers D Fl nV V C hs) (hI : UniIv D)
    (hG : UniGameLeV D Fl nV V C hs) : FsLayer128 D Fl nV V C := by
  intro R e herr hpre hFin A Q hQ
  obtain ⟨A₀, hA₀, hle⟩ := rpm_le_kcS (uSetup D hs) (hOnly_setupK3 hs _ _ _) setupQS
    (setupQS * 2 ^ 32) (isTotalQueryBound_setupK3 hs _ _ _) (cost_setupK3 hs _ _ _) uFix (uAdv A) Q
    (cost_uAdv A Q hQ) (uVerIv D Fl nV V C hs) (duplexVm_uVerIv D Fl nV V C hs) (2 ^ 80 + 8)
    (cost_uVerIv D Fl nV V C hs hN hI)
    (fun z tr => UniBreaksRel D Fl nV V C hs (ivOut z, tr))
    (fun z tr tr' h hz => uniBreaksRel_congr D Fl nV V C hs (ivOut z) tr tr' h hz)
  have hmain := knowledgeSoundness_listChainU_closed128 (uSpec Fl nV V)
    (liftPiop (uSpec Fl nV V).K R rfl) (uView (uRounds Fl nV V)) (uOps D Fl nV V C hs)
    (fun i => uniTc hs i) (uniCheck D Fl nV V C) (uniGood D Fl nV V C) (uniGoodS D Fl nV V C)
    (uSetup D hs) uFix (ivAdv D A₀) setupQS (setupQS + Q + 1) (isTotalQueryBound_setupK3 hs _ _ _)
    (isTotalQueryBound_ivAdv D A₀ _ hA₀) (hok_uni D Fl nV V C hs) (hcov_uni D Fl nV V C hs)
    (hS_uni D Fl nV V C hs) (fun π _ _ => fitsAll_uView _ π)
    (fun π ch cs hc hl hg hn hgS => hlink_uni D Fl nV V C R hFin π ch cs hc hl hg hn hgS)
    name (hlab_uni D Fl nV V hs A₀)
  have hkc : Pr{let z ← (simulateQ randomOracle
        (kcGameS (uSetup D hs) uFix A₀ (uVerIv D Fl nV V C hs))).run' ∅}[
        UniBreaksRel D Fl nV V C hs (ivOut z.1, z.2)] ≤
      Pr{let z ← (simulateQ randomOracle (expU (uSpec Fl nV V) (uView (uRounds Fl nV V))
          (withSetupG (uSetup D hs) uFix (ivAdv D A₀))
          (opsRun (uView (uRounds Fl nV V)) (uOps D Fl nV V C hs)))).run' ∅}[
        BreaksOK (uSpec Fl nV V).K (fun i => (uniTc hs i).commit) (liftPiop (uSpec Fl nV V).K R rfl)
          (uView (uRounds Fl nV V)) (uniCheck D Fl nV V C)
          (fun bs => ∀ k < (uOps D Fl nV V C hs).length, bs.getD k false = true) z] := by
    rw [expU_ivAdv, run'_simulateQ_map, prEvent_map]
    refine prEvent_mono _ _ _ fun w hw => ?_
    have hb := breaksOK_of_rel D Fl nV V C hs R hpre _ hw
    have hlen : (ivInput D w.1.1.roots).length = D.programIv.length + 280 := length_ivInput _ _
    have h64 : (ivInput D w.1.1.roots).length ≠ 64 := by rw [hlen]; omega
    have hl : (ivInput D w.1.1.roots).length ≠ (uniTc hs 0).leafLen := by
      rw [hlen, leafLen_uniTc_zero]
      have := hI.ne
      omega
    have he := extractorK_append (uniTc hs) (uView (uRounds Fl nV V)) (ivOut w.1) w.2
      (ivInput D w.1.1.roots, w.1.2.1) h64 hl
    refine ⟨hb.1, hb.2.1, fun c hc => hb.2.2 c ?_⟩
    rw [← he]
    exact hc
  -- The run before the openings, and its queries.
  set X := preU (uSpec Fl nV V) (uView (uRounds Fl nV V))
    (withSetupG (uSetup D hs) uFix (ivAdv D A₀)) with hXdef
  have hX : IsTotalQueryBound X (setupQS + (setupQS + Q + 1) + (uSpec Fl nV V).K.nQ) :=
    isTotalQueryBound_preU _ _ _ _ (isTotalQueryBound_withSetupG _ _ _ _ _
      (isTotalQueryBound_setupK3 hs _ _ _) (isTotalQueryBound_ivAdv D A₀ _ hA₀))
  -- The openings, once.
  have hdoom := prEvent_doomF_le εExact largeShapes largeShapes_nodup (uView (uRounds Fl nV V))
    (uOps D Fl nV V C hs) (hops_uni D Fl nV V C hs) X _ hX 10122 largeShapes_QO_le
  -- The seed's pair.
  have hpair := prEvent_pairTr_expL_le (uView (uRounds Fl nV V)) X (uOps D Fl nV V C hs) _ hX
    name name_length
  refine (hG A).trans (hle.trans (add_le_add (hkc.trans hmain) le_rfl) |>.trans ?_)
  have hS := setupQS_le D hs
  have hn := hN.chain
  have hq := sumQO_le D Fl nV V C hs
  exact le_uniBound128 e Q setupQS (uSpec Fl nV V).K.nQ _ (uSpec Fl nV V).nRf 10122 hS hn hq
    (show (5 : ℕ) ≤ 6 by decide) le_rfl _ _ _ hdoom hpair (maxErrK_uni D Fl nV V hs R e herr)

/-- `fsLayer128_of_gameV` with the numbers from the rounds' sizes (`uniNumbers_of`). -/
theorem fsLayer128_of_gameV' (hnQ : (uSpec Fl nV V).K.nQ ≤ 2 ^ 10)
    (hnv : ∀ r ∈ uRounds Fl nV V, r.nv ≤ 2 ^ 30) (hI : UniIv D) (hG : UniGameLeV D Fl nV V C hs) :
    FsLayer128 D Fl nV V C :=
  fsLayer128_of_gameV D Fl nV V C hs (uniNumbers_of D Fl nV V C hs hnQ hnv) hI hG

end Layer

end UniSound

/-- info: 'UniSound.fsLayer128_of_gameV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.fsLayer128_of_gameV
