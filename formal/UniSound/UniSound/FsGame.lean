-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The transfer is
-- `formal/Compose/Compose/ListChainKRpmS.lean`'s `rpm_le_kcS`, the two-oracle theorem
-- `ListChainUDoom.lean`'s `knowledgeSoundness_listChainU_closed`; `FsProof.lean`'s
-- `fsLayer_of_game` is the route through their composition.
import UniSound.FsCost
import Soundness.TreeLog
import Bridge.Chain

/-!
# The Fiat–Shamir layer, the contract's IV computed by the verifier

`FsProof.lean`'s `UniGameLe` couples the univariate experiment with the composed random-permutation
game whose adversary computes the contract's IV (`A'`: the adversary, then the IV). That puts the
IV's calls of `π` in the adversary's log, which the composed extractor replays
(`keccakEvaluationsOfTranscript`): a fresh IV answer extends sponge paths the univariate
extractor, reading the adversary's log alone, never sees. Whether that changes `C1`'s Merkle word
depends on the permutation's answers (an IV answer equal to a digest on `C1`'s climb), so the
coupling event by event fails, by a margin near `2^-230`, and `UniGameLe` is not provable without
slack. Here the IV is computed where the univariate experiment computes it, **by the verifier**:

* **`uVerIv`**: the IV (`ivKC`, one Keccak-256 call of `ivInput`, `contractIvWith`'s input), then
  the composed verifier on the proof carrying it (`setIv`); `uAdv` the adversary, given the setup's
  roots; **`UniGameLeV`**, the coupling, now with the same adversary log on both sides;
* the random-permutation transfer `rpm_le_kcS` takes any verifier: the two-oracle game then has
  the IV in the verifier, and **`expU_ivAdv`** moves it into the adversary (`ivAdv`): the same
  queries, the log one entry longer, `(ivInput, IV)`, of `D.programIv.length + 280` bytes, neither
  a Merkle node's `64` nor a leaf's `512` (`UniIv`), so `C1`'s extractor reads the same word
  (**`extractorK_append`**);
* **`fsLayer_of_gameV`**: `FsLayer` from `UniGameLeV`, `UniNumbers` and `UniIv`, through the
  two-oracle theorem, with the bound `uniBound` unchanged (`le_uniBoundV`).
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack

/-! ## The contract's IV -/

/-- **The contract IV's input** (`contractIvWith`): the tag, the program's IV, the setup's three
roots, the shape's bytes and the five layout words. -/
def ivInput (D : Deployment) (roots : SetupRoots) : List UInt8 :=
  ivTag ++ D.programIv ++ digestBytes roots.bytecode ++ digestBytes roots.a0 ++
    digestBytes roots.b0 ++ shapeBytes D.shape ++ (layoutWords D.shape).flatten

theorem contractIvWith_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    (F : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState) (D : Deployment) (roots : SetupRoots) :
    contractIvWith F D.shape D.programIv roots = digestBytes <$> keccak256With F (ivInput D roots) := by
  rw [map_eq_bind_pure_comp]
  rfl

theorem length_digestBytes (d : Digest) : (digestBytes d).length = 32 := by
  rw [← Bridge.toB_toList]
  simp

theorem length_ivTag : ivTag.length = 16 := by decide +kernel

theorem length_shapeBytes (s : UniStatement.Shape) : (shapeBytes s).length = 8 := by
  simp [shapeBytes]

theorem length_layoutWord (s : UniStatement.Shape) (code vars placed : ℕ) :
    (layoutWord s code vars placed).length = 32 := by
  simp [layoutWord, length_shapeBytes]

theorem length_layoutWords_flatten (s : UniStatement.Shape) : (layoutWords s).flatten.length = 160 := by
  unfold layoutWords
  simp only [List.flatten_cons, List.flatten_nil, List.length_append, length_layoutWord,
    List.length_nil]

theorem length_ivInput (D : Deployment) (roots : SetupRoots) :
    (ivInput D roots).length = D.programIv.length + 280 := by
  simp only [ivInput, List.length_append, length_ivTag, length_digestBytes, length_shapeBytes,
    length_layoutWords_flatten]
  omega

/-- **The deployment's IV is short and of no Merkle length**: the program's IV not `232` bytes (the
IV's input then `512`, a leaf's), and at most `807` (the IV at most eight calls of `π`). The
reference program IV (`UniStatement.programIv`) has `32` bytes. -/
structure UniIv (D : Deployment) : Prop where
  ne : D.programIv.length ≠ 232
  le : D.programIv.length ≤ 807

/-- **The IV as the composed verifier computes it**: one Keccak-256 call of its input. -/
def ivKC (D : Deployment) (π : UPf) : OracleComp KeccakCalls Bytes32 := hash256 (ivInput D π.roots)

/-- **The Statement's IV is the composed one**, Keccak-256 over `π`. -/
theorem ivWith_eq (D : Deployment) (roots : SetupRoots) :
    D.ivWith Common.queryPermutation roots =
      (fun b : Bytes32 => b.toList) <$>
        simulateQ keccakCallsOverQueryPermutation (hash256 (ivInput D roots)) := by
  rw [Deployment.ivWith, contractIvWith_eq, hash256, callKeccak256, simulateQ_bind,
    simulateQ_spec_query, map_bind]
  simp only [simulateQ_pure, map_pure, Bridge.toB_toList]
  rw [map_eq_bind_pure_comp]
  rfl

/-- The proof with an IV. -/
def setIv (iv : Vector UInt8 32) (π : UPf) : UPf := { π with iv := iv }

/-- The setup's roots as the proof records them (`uFix`). -/
def rootsOfS (s : Bytes32 × Bytes32 × Bytes32) : SetupRoots := ⟨ofB s.1, ofB s.2.1, ofB s.2.2⟩

theorem uFix_setIv (s : Bytes32 × Bytes32 × Bytes32) (iv : Vector UInt8 32) (π : UPf) :
    uFix s (setIv iv π) = setIv iv (uFix s π) := rfl

/-- **The adversary of the composed game**: the univariate adversary given the setup's roots, its
statement and proof (the IV and the roots the verifier and `uFix` set). -/
def uAdv (A : UniAdversary) (s : Bytes32 × Bytes32 × Bytes32) :
    OracleComp Common.RandomPermutationOracles UPf :=
  (fun z : Vector UInt8 32 × UniProof => (⟨z.1, z.2, Vector.replicate 32 0, rootsOfS s⟩ : UPf)) <$>
    A (rootsOfS s)

theorem cost_uAdv (A : UniAdversary) (Q : ℕ)
    (hQ : ∀ roots, Common.QueryCostAtMost (A roots) Common.permutationCallCost Q)
    (s : Bytes32 × Bytes32 × Bytes32) :
    Common.QueryCostAtMost (uAdv A s) Common.permutationCallCost Q :=
  Common.isWeightBound_map _ (hQ _)

section Verifier

variable (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (nV V : ℕ) (C : UniCode D Fl nV V)
  (hs : UniShapes D)

/-- **The composed verifier with the IV**: the contract's IV, then the chain and the five openings
on the proof carrying it. -/
noncomputable def uVerIv (π : UPf) :
    OracleComp KeccakCalls (Bytes32 × (List (List E) × List Bool)) :=
  ivKC D π >>= fun iv => (fun v => (iv, v)) <$>
    verU (uSpec Fl nV V) (uView (uRounds Fl nV V))
      (opsRun (uView (uRounds Fl nV V)) (uOps D Fl nV V C hs)) (setIv iv π)

/-- The outcome with the IV written in the proof. -/
def ivOut (z : UPf × (Bytes32 × (List (List E) × List Bool))) : UPf × (List (List E) × List Bool) :=
  (setIv z.2.1 z.1, z.2.2)

/-- **The game bridge** (the coupling `fsLayer_of_gameV` takes): the univariate experiment's break is
at most as likely as the composed random-permutation game's, of the setup's three trees, the
univariate adversary (`uAdv`) and the composed verifier with the contract's IV (`uVerIv`), the event
read on the proof with its IV (`ivOut`), the setup's log and the Keccak-256 evaluations of the
adversary's permutation transcript. The two games make the same calls of `π` in the same order. -/
def UniGameLeV : Prop :=
  ∀ A : UniAdversary,
    Pr{let z ← uniSoundnessExperiment D A}[UniBreaksKnowledgeSoundness D (uniExtractor D) z] ≤
      Pr{let z ← Common.runWithRandomPermutation
          (rpmGameS (uSetup D hs) uFix (uAdv A) (uVerIv D Fl nV V C hs))}[
        UniBreaksRel D Fl nV V C hs (ivOut z.1, z.2.1 ++ evalTr (permutationQueries z.2.2))]

theorem duplexVm_uVerIv (π : UPf) : LeanVM.Rpm.DuplexVm (uVerIv D Fl nV V C hs π) [] := by
  unfold uVerIv ivKC
  refine LeanVM.Rpm.DuplexVm.bind ?_ fun iv => ?_
  · rw [LeanVM.Rpm.duplexVm_iff_duplexP]
    exact ((hOnly_hash256 _).duplexP []).mono fun _ _ _ => trivial
  · rw [map_eq_bind_pure_comp]
    exact LeanVM.Rpm.DuplexVm.bind (duplexVm_verU _ _ _ (fun π ch => duplexVm_opsRun _ _ π ch) _)
      fun _ => trivial

theorem cost_uVerIv (hN : UniNumbers D Fl nV V C hs) (hI : UniIv D) (π : UPf) :
    Common.QueryCostAtMost (uVerIv D Fl nV V C hs π) LeanVM.Rpm.hashBlocks (2 ^ 80 + 8) := by
  unfold uVerIv ivKC
  have hb : (ivInput D π.roots).length / 136 + 1 ≤ 8 := by
    rw [length_ivInput]
    have := hI.le
    omega
  refine cost_hash256_bind _ _ _ (hb.trans (by norm_num)) fun u => ?_
  refine (Common.isWeightBound_map _ (hN.verifier _)).mono ?_
  generalize (2 : ℕ) ^ 80 = a
  omega

end Verifier

/-! ## An entry of no Merkle length leaves the extractor's word -/

theorem below_insert (H : Hist) (T T' : QuotientRpm.Table) (x d : List UInt8) (n : ℕ) (hn : x.length ≠ n)
    (hT : ∀ z ∈ H, T' z = T z) : below (insert x H) T' d n = below H T d n := by
  unfold below
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨rfl | hz, h1, h2⟩
    · exact absurd h2 hn
    · exact ⟨hz, by rw [← hT z hz]; exact h1, h2⟩
  · rintro ⟨hz, h1, h2⟩
    exact ⟨Or.inr hz, by rw [hT z hz]; exact h1, h2⟩

theorem leafAt_insert (H : Hist) (T T' : QuotientRpm.Table) (x : List UInt8) (leafLen : ℕ)
    (h64 : x.length ≠ 64) (hl : x.length ≠ leafLen) (hT : ∀ z ∈ H, T' z = T z) :
    ∀ (k : ℕ) (d : List UInt8) (bs : List Bool),
      leafAt (insert x H) T' leafLen k d bs = leafAt H T leafLen k d bs
  | 0, d, _ => below_insert H T T' x d leafLen hl hT
  | _ + 1, _, [] => rfl
  | k + 1, d, b :: bs => by
    simp only [leafAt, below_insert H T T' x d 64 h64 hT]
    congr 1
    funext y
    exact leafAt_insert H T T' x leafLen h64 hl hT k _ bs

theorem histOfTr_append_single (tr : Transcript) (e : List UInt8 × Bytes32) :
    histOfTr (tr ++ [e]) = insert e.1 (histOfTr tr) := by
  ext z
  simp [histOfTr]

theorem tableOfTr_append_single (tr : Transcript) (e : List UInt8 × Bytes32) (z : List UInt8)
    (hz : z ∈ histOfTr tr) : tableOfTr (tr ++ [e]) z = tableOfTr tr z := by
  unfold tableOfTr
  obtain ⟨a, ha, rfl⟩ : ∃ a ∈ tr, a.1 = z := by
    simpa [histOfTr] using hz
  have hs : (tr.find? fun e => decide (e.1 = a.1)).isSome :=
    List.find?_isSome.mpr ⟨a, ha, by simp⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hs
  rw [List.find?_append, hb]
  rfl

/-- **The extractor reads the same word** after a transcript entry of neither a node's nor a leaf's
length. -/
theorem extractorK_append {Pf F M St β : Type} (tc : ℕ → TableCode M)
    (view : Pf → St × List (RMsg F)) (z : Pf × (List (List F) × β)) (tr : Transcript)
    (e : List UInt8 × Bytes32) (h64 : e.1.length ≠ 64) (hl : e.1.length ≠ (tc 0).leafLen) :
    extractorK (fun i => (tc i).commit) view (z, tr ++ [e]) =
      extractorK (fun i => (tc i).commit) view (z, tr) := by
  show optC ((tc 0).commit) (histOfTr (tr ++ [e])) (tableOfTr (tr ++ [e])) (msgK view z.1 0) =
    optC ((tc 0).commit) (histOfTr tr) (tableOfTr tr) (msgK view z.1 0)
  unfold optC
  split
  · next r _ =>
    show ((tc 0).dec (merkleWord _ _ _ _ r)).map some = ((tc 0).dec (merkleWord _ _ _ _ r)).map some
    congr 2
    funext p
    unfold merkleWord
    rw [histOfTr_append_single]
    exact leafAt_insert _ _ _ _ _ h64 hl (fun y hy => tableOfTr_append_single tr e y hy) _ _ _
  · rfl

/-! ## The IV moved into the adversary, in the two-oracle game -/

theorem logImplKC_bind {α β : Type} (oa : OracleComp KeccakCalls α)
    (f : α → OracleComp KeccakCalls β) (l : Transcript) :
    (simulateQ logImplKC (oa >>= f)).run l =
      (simulateQ logImplKC oa).run l >>= fun p => (simulateQ logImplKC (f p.1)).run p.2 := by
  rw [simulateQ_bind, StateT.run_bind]

theorem logImplKC_ivKC (D : Deployment) (π : UPf) (l : Transcript) :
    (simulateQ logImplKC ((fun iv => setIv iv π) <$> ivKC D π)).run l =
      callKeccak256 (ivInput D π.roots) >>= fun u =>
        pure (setIv (toB u) π, l ++ [(ivInput D π.roots, toB u)]) := by
  rw [ivKC, hash256, map_bind]
  simp only [map_pure]
  rw [callKeccak256, loggedKC_run_query_bind]
  simp only [simulateQ_pure, StateT.run_pure]
  rfl

/-- The two-oracle adversary with the IV: `A₀`, then the IV of the proof the setup fixes. -/
def ivAdv (D : Deployment) (A₀ : Bytes32 × Bytes32 × Bytes32 → OracleComp KeccakCalls UPf)
    (s : Bytes32 × Bytes32 × Bytes32) : OracleComp KeccakCalls UPf :=
  A₀ s >>= fun π => (fun iv => setIv iv π) <$> ivKC D (uFix s π)

theorem isTotalQueryBound_ivAdv (D : Deployment)
    (A₀ : Bytes32 × Bytes32 × Bytes32 → OracleComp KeccakCalls UPf) (n : ℕ)
    (h : ∀ s, IsTotalQueryBound (A₀ s) n) (s : Bytes32 × Bytes32 × Bytes32) :
    IsTotalQueryBound (ivAdv D A₀ s) (n + 1) := by
  unfold ivAdv
  refine isTotalQueryBound_bind (h s) fun π => (isQueryBound_map_iff _ _ _ _ _).mpr ?_
  simp only [ivKC, hash256, callKeccak256]
  exact isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ => trivial⟩

section Move

variable (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (nV V : ℕ) (C : UniCode D Fl nV V)
  (hs : UniShapes D)

/-- **The IV moved into the adversary**: the two-oracle game with the IV in the verifier is, up to
writing the IV in the proof and appending its entry to the log, the experiment whose adversary
computes the IV last. -/
theorem expU_ivAdv (A₀ : Bytes32 × Bytes32 × Bytes32 → OracleComp KeccakCalls UPf) :
    expU (uSpec Fl nV V) (uView (uRounds Fl nV V)) (withSetupG (uSetup D hs) uFix (ivAdv D A₀))
        (opsRun (uView (uRounds Fl nV V)) (uOps D Fl nV V C hs)) =
      (fun w => (ivOut w.1, w.2 ++ [(ivInput D w.1.1.roots, w.1.2.1)])) <$>
        kcGameS (uSetup D hs) uFix A₀ (uVerIv D Fl nV V C hs) := by
  have hw : withSetupG (uSetup D hs) uFix (ivAdv D A₀) =
      withSetupG (uSetup D hs) uFix A₀ >>= fun π => (fun iv => setIv iv π) <$> ivKC D π := by
    simp only [withSetupG, ivAdv, bind_assoc, map_bind, bind_map_left, Functor.map_map]
    rfl
  rw [expU, kcGameS, hw, loggedKC, logImplKC_bind]
  simp only [uVerIv, ivKC, hash256, bind_assoc, pure_bind, map_bind, map_pure,
    bind_map_left, ivOut]
  rfl

end Move

/-! ## The bound -/

/-- **The composed bound, the IV in the verifier, is at most `uniBound`**: `le_uniBound` with the
adversary's `Q + 8` calls and `2^80` verifier calls traded for `Q + 1` Keccak-256 calls of the
two-oracle adversary and `2^80 + 8` verifier calls. -/
theorem le_uniBoundV (e : ℝ≥0∞) (Q QS nQ SQO nRf : ℕ) (hQS : QS ≤ 3 * 2 ^ 24) (hnQ : nQ ≤ 2 ^ 10)
    (hSQO : SQO ≤ 5 * 10122) (hr : nRf ≤ 6) (d m t : ℝ≥0∞)
    (hd : d ≤ 5 * openingBoundAt 10122 (uniN Q)) (hm : m ≤ ((9952 ^ 2 : ℕ) : ℝ≥0∞) * e)
    (ht : t = ((256 ^ 16 : ℕ) : ℝ≥0∞) / 2 ^ 256) :
    d + ((QS + (QS + Q + 1) + nQ + SQO : ℕ) : ℝ≥0∞) *
        (m + t + (((nRf + 2) * (QS + (QS + Q + 1) + nQ + SQO) : ℕ) : ℝ≥0∞) / 2 ^ 256) +
      ((QS * 2 ^ 32 + Q + (2 ^ 80 + 8) : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 ≤ uniBound e Q := by
  have hN : QS + (QS + Q + 1) + nQ + SQO ≤ QS + (QS + (Q + 8)) + nQ + SQO := by omega
  have hR : QS * 2 ^ 32 + Q + (2 ^ 80 + 8) = QS * 2 ^ 32 + (Q + 8) + 2 ^ 80 := by ring
  refine le_trans ?_ (le_uniBound e Q QS nQ SQO nRf hQS hnQ hSQO hr d m t hd hm ht)
  rw [hR]
  refine add_le_add (add_le_add le_rfl (mul_le_mul' (Nat.cast_le.mpr hN) ?_)) le_rfl
  exact add_le_add le_rfl (ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.mul_le_mul_left _ hN)) _)

/-! ## The Fiat–Shamir layer -/

section Layer

variable (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (nV V : ℕ) (C : UniCode D Fl nV V)
  (hs : UniShapes D)

/-- `UniBreaksRel` reads the transcript through its answers only. -/
theorem uniBreaksRel_congr (z : UPf × (List (List E) × List Bool)) (tr tr' : Transcript)
    (h : ∀ x, lookTr tr x = lookTr tr' x) (hz : UniBreaksRel D Fl nV V C hs (z, tr)) :
    UniBreaksRel D Fl nV V C hs (z, tr') := by
  obtain ⟨hH, hT⟩ := histOfTr_tableOfTr_congr h
  refine ⟨hz.1, hz.2.1, fun c hc => hz.2.2 c ?_⟩
  unfold extractorK at hc ⊢
  simp only at hc ⊢
  rwa [hH, hT]

theorem leafLen_uniTc_zero : (uniTc hs 0).leafLen = 512 := by
  unfold uniTc
  rw [ite_eq_left rfl]
  rfl

/-- **The Fiat–Shamir layer from the game bridge with the IV in the verifier**: `FsLayer` for a
deployment whose five layout words name `24 … 28` variables (`hs`), from its numbers
(`UniNumbers`), its program IV's length (`UniIv`) and the coupling `UniGameLeV`. -/
theorem fsLayer_of_gameV (hN : UniNumbers D Fl nV V C hs) (hI : UniIv D)
    (hG : UniGameLeV D Fl nV V C hs) : FsLayer D Fl nV V C := by
  intro R e herr hpre hFin A Q hQ
  obtain ⟨A₀, hA₀, hle⟩ := rpm_le_kcS (uSetup D hs) (hOnly_setupK3 hs _ _ _) setupQS
    (setupQS * 2 ^ 32) (isTotalQueryBound_setupK3 hs _ _ _) (cost_setupK3 hs _ _ _) uFix (uAdv A) Q
    (cost_uAdv A Q hQ) (uVerIv D Fl nV V C hs) (duplexVm_uVerIv D Fl nV V C hs) (2 ^ 80 + 8)
    (cost_uVerIv D Fl nV V C hs hN hI)
    (fun z tr => UniBreaksRel D Fl nV V C hs (ivOut z, tr))
    (fun z tr tr' h hz => uniBreaksRel_congr D Fl nV V C hs (ivOut z) tr tr' h hz)
  have hmain := knowledgeSoundness_listChainU_closed (uSpec Fl nV V)
    (liftPiop (uSpec Fl nV V).K R rfl) (uView (uRounds Fl nV V)) (uOps D Fl nV V C hs)
    (fun i => uniTc hs i) (uniCheck D Fl nV V C) (uniGood D Fl nV V C) (uniGoodS D Fl nV V C)
    (uSetup D hs) uFix (ivAdv D A₀) setupQS (setupQS + Q + 1) (isTotalQueryBound_setupK3 hs _ _ _)
    (isTotalQueryBound_ivAdv D A₀ _ hA₀) (hok_uni D Fl nV V C hs) (hcov_uni D Fl nV V C hs)
    (hS_uni D Fl nV V C hs) (fun π _ _ => fitsAll_uView _ π)
    (fun π ch cs hc hl hg hn hgS => hlink_uni D Fl nV V C R hFin π ch cs hc hl hg hn hgS)
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
  refine (hG A).trans (hle.trans (add_le_add (hkc.trans hmain) le_rfl) |>.trans ?_)
  have hS := setupQS_le D hs
  have hn := hN.chain
  have hq := sumQO_le D Fl nV V C hs
  exact le_uniBoundV e Q setupQS (uSpec Fl nV V).K.nQ _ (uSpec Fl nV V).nRf hS hn hq
    (show (5 : ℕ) ≤ 6 by decide) _ _ _
    (doom_le D Fl nV V C hs Q _ (by
      unfold uniN
      have : (2 : ℕ) ^ 33 = 8589934592 := by norm_num
      have : (2 : ℕ) ^ 24 = 16777216 := by norm_num
      have : (2 : ℕ) ^ 10 = 1024 := by norm_num
      omega)) (maxErrK_uni D Fl nV V hs R e herr)
    (uniSpec_tagBound _)

/-- `fsLayer_of_gameV` with the numbers from the rounds' sizes (`uniNumbers_of`). -/
theorem fsLayer_of_gameV' (hnQ : (uSpec Fl nV V).K.nQ ≤ 2 ^ 10)
    (hnv : ∀ r ∈ uRounds Fl nV V, r.nv ≤ 2 ^ 30) (hI : UniIv D) (hG : UniGameLeV D Fl nV V C hs) :
    FsLayer D Fl nV V C :=
  fsLayer_of_gameV D Fl nV V C hs (uniNumbers_of D Fl nV V C hs hnQ hnv) hI hG

end Layer

end UniSound

/-- info: 'UniSound.fsLayer_of_gameV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.fsLayer_of_gameV

/-- info: 'UniSound.extractorK_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.extractorK_append
