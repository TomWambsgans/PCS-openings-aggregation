-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Follows `formal/UniSound/UniSound/FsExtract.lean`
-- (`uniExtractBridge_of_c1`, `c1Word_eq_committed`) for π2's `W`, with `formal/EndToEnd/Soundness/Replay.lean`'s
-- `preimage_merkle`, `leavesUnder_preimage`, `leavesUnder_congr` and `Soundness/MerkleWord.lean`'s
-- `wordOfMerkle_merkleWord_eq`.
import RecCompose.FsSetup
import RecCompose.OpeningsAgree
import UniSound.FsExtract
import UniSound.FsWalkProof

/-!
# The extractor's reading: π2's extractor lists what the composed one lists

**`pi2ExtractBridge_of`**: a candidate of `W`'s root that the composed extractor (`extractorK` at round `0`, `W`'s
decoder `p2Tc 0 = colCode shW…`) reads off the setup's evaluations and a permutation transcript is a stack of π2's
extractor's list (`wCandidates`) on the same evaluations, for a stream that holds `W`'s root (`pLen + 32` bytes):

* **round `0`'s message is `W`'s root** the stream names (`msgK_p2View_zero`: its halves at byte `472`), and the
  Statement's root, `PCS_OPEN`'s root word of the stream's `32` bytes there (`streamRoot`, at `rootsAt cc.reads`'s
  `W` entry), is the same digest (`streamRoot_eq`, for a stream holding those bytes);
* **the composed candidate is a stack of mumbai's decoder** (`decodeColumns` = `Column.mk` of `decodeStacks` at `2^24`
  words, rate `1/2`), and the Statement's word is mumbai's `committedLeaves` (`committedWord_eq`), which agrees with the
  composed Merkle word on every column (`wordOfMerkle_merkleWord_eq`), so the Statement's list decoder lists the same
  stack (`mem_decodeStacks_congr`), last of `candidates`.

**`Pi2ExtractBridge` (`FsDefs.lean`) needs the stream's length**: on a stream shorter than `504` bytes the composed view
reads `W`'s root's missing bytes as zeros in place (`halvesAt`, big-endian words by `getD`), while `PCS_OPEN`'s root
word of the shorter slice (`streamWord`, then each half reversed) shifts them, so the two roots, and the two lists,
can differ. The composed event's check (`p2Check`) has the stream's `944` bytes.
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

/-! ## `W`'s root -/

/-- **Round `0`'s message is `W`'s root** the stream names (bytes `472 … 504`), without scalars. -/
theorem msgK_p2View_zero (π : P2Pf) :
    msgK p2View π 0 = (some (toB (UniStatement.rootOf (UniSound.halvesAt π.proof.stream pLen))), []) :=
  rfl

/-- The public data's reads: `C1`'s root at byte `0`, `C2`'s at `32`; `W`'s at `472`, `Q`'s at `504`. -/
theorem rootsAt_cc : rootsAt cc.reads = [0, 32, 472, 504] := by decide

theorem rootReads_cc : rootReads cc.reads = 2 := by decide

/-- A digest's bytes, each half reversed, are the stream's order of its root's halves (`revRoot`). -/
theorem revRoot_toB (d : Digest) : UniSound.revRoot (toB d) = rootWordOfBytes (digestBytes d) := by
  have hl := Pi1Decode.length_digestBytes d
  unfold UniSound.revRoot rootWordOfBytes
  rw [Bridge.toB_toList, List.take_of_length_le (l := (digestBytes d).drop 16) (by simp [hl])]

/-- **`PCS_OPEN`'s root word of the stream's 32 bytes names the root the stream's halves name**, on a stream that holds
them. -/
theorem streamRoot_eq (b : Array UInt8) (o : ℕ) (h : o + 32 ≤ b.size) :
    streamRoot b o = UniStatement.rootOf (UniSound.halvesAt b o) := by
  have hw : streamWord b o = UniSound.revRoot (toB (UniStatement.rootOf (UniSound.halvesAt b o))) := by
    rw [UniSound.revRoot_halvesAt b o h]
    unfold streamWord
    rw [UniSound.toList_extract_eq, Nat.add_sub_cancel_left]
  unfold streamRoot
  rw [hw, revRoot_toB, rootOfWord_rootWordOfBytes_digestBytes]

/-! ## The Statement's word -/

/-- **The Statement's committed word is mumbai's `committedLeaves`** on the setup's evaluations and the transcript's,
under any root, at any size. -/
theorem committedWord_eq (setupEvals : List (List UInt8 × Digest)) (T : Common.OracleQueryLog) (μ : ℕ)
    (root : Digest) :
    committedWord (preimagesOf setupEvals T) μ root =
      LeanVM.Extraction.leafAt (LeanVM.Extraction.committedLeaves
        (lookupEvaluation (setupEvals ++ keccakEvaluationsOfTranscript (permutationQueries T)))
        ((setupEvals ++ keccakEvaluationsOfTranscript (permutationQueries T)).map (·.1))
        root (μ - 6 + 1) 64) (μ - 6 + 1) 64 := by
  unfold committedWord preimagesOf
  show LeanVM.Extraction.leafAt (PcsQuotient.Replay.leavesUnder _ 64 _ _) _ 64 =
    LeanVM.Extraction.leafAt (LeanVM.Extraction.subtreeLeaves _ 64 _ _) _ 64
  rw [← Soundness.Replay.leavesUnder_preimage]
  congr 1
  refine Soundness.Replay.leavesUnder_congr _ _ 64 (fun d' => ?_) (fun d' => ?_) _ _
  · exact Soundness.Replay.preimage_merkle setupEvals _ d' 64 (by decide)
  · exact Soundness.Replay.preimage_merkle setupEvals _ d' (8 * 64) (by decide)

/-- `W`'s layout has `2^24` words (π2's circuit the real deployment's). -/
theorem wLayout_logN (D : RecDeployment) (hD : RecDeployment.Real D) (roots : RecSetupRoots) :
    (wLayout D roots).logN = 24 := by
  unfold wLayout
  rw [RecDeployment.circuitAt, hD.1]
  decide

/-! ## The bridge -/

/-- **The extractor's reading**: a candidate of `W`'s root that the composed extractor lists, off the setup's
evaluations and a permutation transcript, is a stack of π2's extractor's list on them, for a stream holding `W`'s
root. -/
theorem pi2ExtractBridge_of (D : RecDeployment) (hD : RecDeployment.Real D) (t : RecSetupTrees)
    (T : Common.OracleQueryLog) (z : P2Pf × (List (List E) × List Bool)) (q : Stk)
    (hsz : pLen + 32 ≤ z.1.proof.stream.size)
    (hq : some q ∈ extractorK (fun i => (p2Tc i).commit) p2View (z, setupTr2 t ++ evalTr (permutationQueries T))) :
    ∃ w ∈ wCandidates D t.roots (preimagesOf t.evaluations T) z.1.proof, stkOf w = q := by
  have htr : setupTr2 t ++ evalTr (permutationQueries T) = Soundness.trOf
      (t.evaluations ++ keccakEvaluationsOfTranscript (permutationQueries T)) := by
    simp only [Soundness.trOf, setupTr2, evalTr, List.map_append]
  set R := UniStatement.rootOf (UniSound.halvesAt z.1.proof.stream pLen) with hR
  -- the composed candidate: a stack of `W`'s decoder under the stream's root
  have h0 : extractorK (fun i => (p2Tc i).commit) p2View (z, setupTr2 t ++ evalTr (permutationQueries T)) =
      ((p2Tc 0).commit.cands
        (histOfTr (Soundness.trOf (t.evaluations ++ keccakEvaluationsOfTranscript (permutationQueries T))))
        (tableOfTr (Soundness.trOf (t.evaluations ++ keccakEvaluationsOfTranscript (permutationQueries T))))
        (toB R)).map some := by
    rw [htr]
    show optC _ _ _ (msgK p2View z.1 0) = _
    rw [msgK_p2View_zero]
    rfl
  rw [h0] at hq
  obtain ⟨q', hq', he⟩ := List.mem_map.mp hq
  cases Option.some.inj he
  have e0 : p2Tc 0 = colCode shW.L shW.R shW.adm := by
    unfold p2Tc
    rw [ite_eq_left rfl]
  rw [e0, UniSound.cands_commit] at hq'
  unfold colCode at hq'
  dsimp only at hq'
  rw [List.mem_map] at hq'
  obtain ⟨c, hc, hcq⟩ := hq'
  unfold decodeColumns at hc
  rw [List.mem_map] at hc
  obtain ⟨st, hst, hstc⟩ := hc
  subst hstc hcq
  -- the Statement's word agrees with the composed one on every column
  have hst2 : st ∈ LeanVM.Extraction.decodeStacks 24 1
      (committedWord (preimagesOf t.evaluations T) 24 R) := by
    refine Soundness.mem_decodeStacks_congr shW.adm (fun p hp => ?_) st hst
    rw [committedWord_eq]
    exact Soundness.wordOfMerkle_merkleWord_eq _ _ _ _ hp
  -- the Statement's root and size
  have hroot : streamRoot z.1.proof.stream
      ((rootsAt (D.circuitAt t.roots.pi1).circuit.reads).getD (rootReads (D.circuitAt t.roots.pi1).circuit.reads) 0) =
        R := by
    rw [RecDeployment.circuitAt, hD.1, rootsAt_cc, rootReads_cc]
    exact streamRoot_eq _ _ hsz
  have hμ := wLayout_logN D hD t.roots
  unfold wCandidates
  dsimp only
  rw [hroot]
  generalize (wLayout D t.roots).logN = μ at hμ ⊢
  subst hμ
  exact ⟨st, List.mem_append_right _ hst2, rfl⟩

/-- **EXTRACTOR READING** (`Pi2ExtractBridge`) at the real deployment. -/
theorem pi2ExtractBridge (D : RecDeployment) (hD : RecDeployment.Real D) : Pi2ExtractBridge D :=
  fun t T z q hsz hq => pi2ExtractBridge_of D hD t T z q hsz hq

end RecCompose

/-- info: 'RecCompose.pi2ExtractBridge_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2ExtractBridge_of
