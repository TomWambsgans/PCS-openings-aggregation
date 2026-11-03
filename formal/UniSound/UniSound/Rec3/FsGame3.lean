-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The main line's `FsGame.lean` (`fsLayer_of_gameV`)
-- for π1-rec3: its IV (`UniStatement.Deployment.ivRec3With`, `contractIvForWith … .rec3 true`) and its three
-- openings.
import UniSound.Rec3.FsProof3
import UniSound.FsGame

/-!
# π1-rec3's Fiat–Shamir layer, the contract's IV computed by the verifier

`FsGame.lean` for π1-rec3:

* **The IV** (`ivInput3`): π1-rec3's contract IV hashes the main line's preimage (`ivInput`) with the variant
  bytes appended (`rec3Extra = variantBytes (.flock flockMain) .rec3 true`: `fs-rec3`, the skip `3`, the slices'
  code `4`, nine bytes), so its input has `D.programIv.length + 289` bytes; **`UniIv3`** asks it neither a leaf's
  `512` (`D.programIv.length ≠ 223`) nor more than eight calls of `π` (`D.programIv.length ≤ 798`). The reference
  program IV has `32` bytes.
* **`uVerIv3`**: the IV (`ivKC3`, one Keccak-256 call), then the composed verifier (the chain on `rec3Rounds`, the
  three openings) on the proof carrying it; **`UniGameLeV3`**, the coupling with π1-rec3's experiment
  (`uniSoundnessExperimentRec3`), the same adversary log on both sides.
* **`fsLayer3_of_gameV`**: `FsLayer3` from `UniGameLeV3`, `UniNumbers3` and `UniIv3`, through `rpm_le_kcS`, the IV
  moved into the two-oracle adversary (`expU_ivAdv3`; its log entry leaves `C1`'s word, `extractorK_append`), the
  two-oracle theorem, and the bound `uniBound3` (`le_uniBoundV3`: three doom terms).
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack

/-! ## π1-rec3's IV -/

/-- **π1-rec3's variant bytes** (`variant_bytes` at `FLOCK_REC3`): `fs-rec3`, the skip, the slices' code. -/
def rec3Extra : List UInt8 := variantBytes (.flock flockMain) .rec3 true

theorem length_rec3Extra : rec3Extra.length = 9 := by decide +kernel

theorem rec3Extra_isEmpty : rec3Extra.isEmpty = false := by decide +kernel

/-- **π1-rec3's IV input** (`contractIvForWith … .rec3 true`): the main line's, then the variant bytes. -/
def ivInput3 (D : Deployment) (roots : SetupRoots) : List UInt8 := ivInput D roots ++ rec3Extra

theorem length_ivInput3 (D : Deployment) (roots : SetupRoots) :
    (ivInput3 D roots).length = D.programIv.length + 289 := by
  rw [ivInput3, List.length_append, length_ivInput, length_rec3Extra]

theorem ivRec3With_eq' {m : Type → Type} [Monad m] [LawfulMonad m]
    (F : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState) (D : Deployment) (roots : SetupRoots) :
    D.ivRec3With F roots = digestBytes <$> keccak256With F (ivInput3 D roots) := by
  unfold Deployment.ivRec3With contractIvForWith
  rw [map_eq_bind_pure_comp]
  show (if rec3Extra.isEmpty then _ else _) = _
  rw [rec3Extra_isEmpty]
  rfl

/-- **The Statement's IV is the composed one**, Keccak-256 over `π`. -/
theorem ivRec3With_eq (D : Deployment) (roots : SetupRoots) :
    D.ivRec3With Common.queryPermutation roots =
      (fun b : Bytes32 => b.toList) <$>
        simulateQ keccakCallsOverQueryPermutation (hash256 (ivInput3 D roots)) := by
  rw [ivRec3With_eq', hash256, callKeccak256, simulateQ_bind, simulateQ_spec_query, map_bind]
  simp only [simulateQ_pure, map_pure, Bridge.toB_toList]
  rw [map_eq_bind_pure_comp]
  rfl

/-- **π1-rec3's deployment IV is short and of no Merkle length**: its input (`D.programIv.length + 289` bytes) not a
leaf's `512`, and at most eight calls of `π` (`≤ 1087` bytes). -/
structure UniIv3 (D : Deployment) : Prop where
  ne : D.programIv.length ≠ 223
  le : D.programIv.length ≤ 798

/-- **The IV as the composed verifier computes it**: one Keccak-256 call of its input. -/
def ivKC3 (D : Deployment) (π : UPf) : OracleComp KeccakCalls Bytes32 := hash256 (ivInput3 D π.roots)

section Verifier

variable (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ) (C : UniCode3 D F3 nV np)
  (hs : UniShapes D)

/-- **The composed verifier with the IV**: π1-rec3's contract IV, then the chain and the three openings on the
proof carrying it. -/
noncomputable def uVerIv3 (π : UPf) :
    OracleComp KeccakCalls (Bytes32 × (List (List E) × List Bool)) :=
  ivKC3 D π >>= fun iv => (fun v => (iv, v)) <$>
    verU (uSpec3 F3 nV np) (uView (uRounds3 F3 nV np))
      (opsRun (uView (uRounds3 F3 nV np)) (uOps3 D F3 nV np C hs)) (setIv iv π)

/-- **The game bridge** (the coupling `fsLayer3_of_gameV` takes): π1-rec3's experiment's break is at most as likely
as the composed random-permutation game's, of the setup's three trees, the adversary (`uAdv`) and the composed
verifier with π1-rec3's IV (`uVerIv3`), the event read on the proof with its IV (`ivOut`), the setup's log and the
Keccak-256 evaluations of the adversary's permutation transcript. -/
def UniGameLeV3 : Prop :=
  ∀ A : UniAdversary,
    Pr{let z ← uniSoundnessExperimentRec3 D A}[UniBreaksKnowledgeSoundness D (uniExtractor D) z] ≤
      Pr{let z ← Common.runWithRandomPermutation
          (rpmGameS (uSetup D hs) uFix (uAdv A) (uVerIv3 D F3 nV np C hs))}[
        UniBreaksRel3 D F3 nV np C hs (ivOut z.1, z.2.1 ++ evalTr (permutationQueries z.2.2))]

theorem duplexVm_uVerIv3 (π : UPf) : LeanVM.Rpm.DuplexVm (uVerIv3 D F3 nV np C hs π) [] := by
  unfold uVerIv3 ivKC3
  refine LeanVM.Rpm.DuplexVm.bind ?_ fun iv => ?_
  · rw [LeanVM.Rpm.duplexVm_iff_duplexP]
    exact ((hOnly_hash256 _).duplexP []).mono fun _ _ _ => trivial
  · rw [map_eq_bind_pure_comp]
    exact LeanVM.Rpm.DuplexVm.bind (duplexVm_verU _ _ _ (fun π ch => duplexVm_opsRun _ _ π ch) _)
      fun _ => trivial

theorem cost_uVerIv3 (hN : UniNumbers3 D F3 nV np C hs) (hI : UniIv3 D) (π : UPf) :
    Common.QueryCostAtMost (uVerIv3 D F3 nV np C hs π) LeanVM.Rpm.hashBlocks (2 ^ 80 + 8) := by
  unfold uVerIv3 ivKC3
  have hb : (ivInput3 D π.roots).length / 136 + 1 ≤ 8 := by
    rw [length_ivInput3]
    have := hI.le
    omega
  refine cost_hash256_bind _ _ _ (hb.trans (by norm_num)) fun u => ?_
  refine (Common.isWeightBound_map _ (hN.verifier _)).mono ?_
  generalize (2 : ℕ) ^ 80 = a
  omega

end Verifier

/-! ## The IV moved into the adversary, in the two-oracle game -/

/-- The two-oracle adversary with π1-rec3's IV: `A₀`, then the IV of the proof the setup fixes. -/
def ivAdv3 (D : Deployment) (A₀ : Bytes32 × Bytes32 × Bytes32 → OracleComp KeccakCalls UPf)
    (s : Bytes32 × Bytes32 × Bytes32) : OracleComp KeccakCalls UPf :=
  A₀ s >>= fun π => (fun iv => setIv iv π) <$> ivKC3 D (uFix s π)

theorem isTotalQueryBound_ivAdv3 (D : Deployment)
    (A₀ : Bytes32 × Bytes32 × Bytes32 → OracleComp KeccakCalls UPf) (n : ℕ)
    (h : ∀ s, IsTotalQueryBound (A₀ s) n) (s : Bytes32 × Bytes32 × Bytes32) :
    IsTotalQueryBound (ivAdv3 D A₀ s) (n + 1) := by
  unfold ivAdv3
  refine isTotalQueryBound_bind (h s) fun π => (isQueryBound_map_iff _ _ _ _ _).mpr ?_
  simp only [ivKC3, hash256, callKeccak256]
  exact isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ => trivial⟩

section Move

variable (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ) (C : UniCode3 D F3 nV np)
  (hs : UniShapes D)

/-- **The IV moved into the adversary**: the two-oracle game with the IV in the verifier is, up to writing the IV
in the proof and appending its entry to the log, the experiment whose adversary computes the IV last. -/
theorem expU_ivAdv3 (A₀ : Bytes32 × Bytes32 × Bytes32 → OracleComp KeccakCalls UPf) :
    expU (uSpec3 F3 nV np) (uView (uRounds3 F3 nV np)) (withSetupG (uSetup D hs) uFix (ivAdv3 D A₀))
        (opsRun (uView (uRounds3 F3 nV np)) (uOps3 D F3 nV np C hs)) =
      (fun w => (ivOut w.1, w.2 ++ [(ivInput3 D w.1.1.roots, w.1.2.1)])) <$>
        kcGameS (uSetup D hs) uFix A₀ (uVerIv3 D F3 nV np C hs) := by
  have hw : withSetupG (uSetup D hs) uFix (ivAdv3 D A₀) =
      withSetupG (uSetup D hs) uFix A₀ >>= fun π => (fun iv => setIv iv π) <$> ivKC3 D π := by
    simp only [withSetupG, ivAdv3, bind_assoc, map_bind, bind_map_left, Functor.map_map]
    rfl
  rw [expU, kcGameS, hw, loggedKC, logImplKC_bind]
  simp only [uVerIv3, ivKC3, hash256, bind_assoc, pure_bind, map_bind, map_pure,
    bind_map_left, ivOut]
  rfl

end Move

/-! ## The bound -/

/-- **The composed bound, the IV in the verifier, is at most `uniBound3`**: `le_uniBound3` with the adversary's
`Q + 8` calls and `2^80` verifier calls traded for `Q + 1` Keccak-256 calls of the two-oracle adversary and
`2^80 + 8` verifier calls. -/
theorem le_uniBoundV3 (e : ℝ≥0∞) (Q QS nQ SQO nRf : ℕ) (hQS : QS ≤ 3 * 2 ^ 24) (hnQ : nQ ≤ 2 ^ 10)
    (hSQO : SQO ≤ 3 * 10122) (hr : nRf ≤ 6) (d m t : ℝ≥0∞)
    (hd : d ≤ 3 * openingBoundAt 10122 (uniN Q)) (hm : m ≤ ((9952 ^ 2 : ℕ) : ℝ≥0∞) * e)
    (ht : t = ((256 ^ 16 : ℕ) : ℝ≥0∞) / 2 ^ 256) :
    d + ((QS + (QS + Q + 1) + nQ + SQO : ℕ) : ℝ≥0∞) *
        (m + t + (((nRf + 2) * (QS + (QS + Q + 1) + nQ + SQO) : ℕ) : ℝ≥0∞) / 2 ^ 256) +
      ((QS * 2 ^ 32 + Q + (2 ^ 80 + 8) : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 ≤ uniBound3 e Q := by
  have hN : QS + (QS + Q + 1) + nQ + SQO ≤ QS + (QS + (Q + 8)) + nQ + SQO := by omega
  have hR : QS * 2 ^ 32 + Q + (2 ^ 80 + 8) = QS * 2 ^ 32 + (Q + 8) + 2 ^ 80 := by ring
  refine le_trans ?_ (le_uniBound3 e Q QS nQ SQO nRf hQS hnQ hSQO hr d m t hd hm ht)
  rw [hR]
  refine add_le_add (add_le_add le_rfl (mul_le_mul' (Nat.cast_le.mpr hN) ?_)) le_rfl
  exact add_le_add le_rfl (ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.mul_le_mul_left _ hN)) _)

/-! ## The Fiat–Shamir layer -/

section Layer

variable (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ) (C : UniCode3 D F3 nV np)
  (hs : UniShapes D)

/-- `UniBreaksRel3` reads the transcript through its answers only. -/
theorem uniBreaksRel3_congr (z : UPf × (List (List E) × List Bool)) (tr tr' : Transcript)
    (h : ∀ x, lookTr tr x = lookTr tr' x) (hz : UniBreaksRel3 D F3 nV np C hs (z, tr)) :
    UniBreaksRel3 D F3 nV np C hs (z, tr') := by
  obtain ⟨hH, hT⟩ := histOfTr_tableOfTr_congr h
  refine ⟨hz.1, hz.2.1, fun c hc => hz.2.2 c ?_⟩
  unfold extractorK at hc ⊢
  simp only at hc ⊢
  rwa [hH, hT]

/-- **π1-rec3's Fiat–Shamir layer from the game bridge with the IV in the verifier**: `FsLayer3` for a deployment
whose layout words name `24 … 28` variables (`hs`), from its numbers (`UniNumbers3`), its program IV's length
(`UniIv3`) and the coupling `UniGameLeV3`. -/
theorem fsLayer3_of_gameV (hN : UniNumbers3 D F3 nV np C hs) (hI : UniIv3 D)
    (hG : UniGameLeV3 D F3 nV np C hs) : FsLayer3 D F3 nV np C := by
  intro R e herr hpre hFin A Q hQ
  obtain ⟨A₀, hA₀, hle⟩ := rpm_le_kcS (uSetup D hs) (hOnly_setupK3 hs _ _ _) setupQS
    (setupQS * 2 ^ 32) (isTotalQueryBound_setupK3 hs _ _ _) (cost_setupK3 hs _ _ _) uFix (uAdv A) Q
    (cost_uAdv A Q hQ) (uVerIv3 D F3 nV np C hs) (duplexVm_uVerIv3 D F3 nV np C hs) (2 ^ 80 + 8)
    (cost_uVerIv3 D F3 nV np C hs hN hI)
    (fun z tr => UniBreaksRel3 D F3 nV np C hs (ivOut z, tr))
    (fun z tr tr' h hz => uniBreaksRel3_congr D F3 nV np C hs (ivOut z) tr tr' h hz)
  have hmain := knowledgeSoundness_listChainU_closed (uSpec3 F3 nV np)
    (liftPiop (uSpec3 F3 nV np).K R rfl) (uView (uRounds3 F3 nV np)) (uOps3 D F3 nV np C hs)
    (fun i => uniTc hs i) (uniCheck3 D F3 nV np C) (uniGood3 D F3 nV np C) (uniGoodS3 D F3 nV np C)
    (uSetup D hs) uFix (ivAdv3 D A₀) setupQS (setupQS + Q + 1) (isTotalQueryBound_setupK3 hs _ _ _)
    (isTotalQueryBound_ivAdv3 D A₀ _ hA₀) (hok_uni3 D F3 nV np C hs) (hcov_uni3 D F3 nV np C hs)
    (hS_uni3 D F3 nV np C hs) (fun π _ _ => fitsAll_uView _ π)
    (fun π ch cs hc hl hg hn hgS => hlink_uni3 D F3 nV np C R hFin π ch cs hc hl hg hn hgS)
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
  refine (hG A).trans (hle.trans (add_le_add (hkc.trans hmain) le_rfl) |>.trans ?_)
  have hS := setupQS_le D hs
  have hn := hN.chain
  have hq := sumQO_le3 D F3 nV np C hs
  exact le_uniBoundV3 e Q setupQS (uSpec3 F3 nV np).K.nQ _ (uSpec3 F3 nV np).nRf hS hn hq
    (show (5 : ℕ) ≤ 6 by decide) _ _ _
    (doom_le3 D F3 nV np C hs Q _ (by
      unfold uniN
      have : (2 : ℕ) ^ 33 = 8589934592 := by norm_num
      have : (2 : ℕ) ^ 24 = 16777216 := by norm_num
      have : (2 : ℕ) ^ 10 = 1024 := by norm_num
      omega)) (maxErrK_uni3 D F3 nV np hs R e herr)
    (uniSpec_tagBound _)

/-- `fsLayer3_of_gameV` with the numbers from the rounds' sizes (`uniNumbers3_of`). -/
theorem fsLayer3_of_gameV' (hnQ : (uSpec3 F3 nV np).K.nQ ≤ 2 ^ 10)
    (hnv : ∀ r ∈ uRounds3 F3 nV np, r.nv ≤ 2 ^ 30) (hI : UniIv3 D) (hG : UniGameLeV3 D F3 nV np C hs) :
    FsLayer3 D F3 nV np C :=
  fsLayer3_of_gameV D F3 nV np C hs (uniNumbers3_of D F3 nV np C hs hnQ hnv) hI hG

end Layer

end UniSound

/-- info: 'UniSound.fsLayer3_of_gameV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.fsLayer3_of_gameV

/-- info: 'UniSound.ivRec3With_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.ivRec3With_eq
