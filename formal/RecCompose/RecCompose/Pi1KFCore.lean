-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The ports of `formal/UniComplete/UniComplete/
-- Rec3CoreRun.lean` (`proveRec3With_eq`, `proveRec3With_eq_some`) and `Rec3Core.lean` (`accepts_of_trace3`,
-- `verifyWithFsH_of_calls3`) to π1-rec3's two-hash prover (`Pi1KF.lean`), against `formal/RecStatement`'s
-- `pi1KeccakVerifierWith` (π1-rec3's verifier with its Fiat–Shamir over Keccak-f[1600]); uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): Keccak-256 over
-- Keccak-f[1600] (`keccak256`).
import RecCompose.Pi1KF
import UniComplete.Rec3Core
import UniComplete.Rec3EndRows
import FlockSoundUni.Walk

/-!
# π1-rec3's two-hash prover against the Keccak-f[1600] verifier: the challenges match, the proof is accepted

At `Id`, the recursion's π1 prover (`Pi1KF.uniProverRec3With2 hKF Hm F (flockProve3H hKF)`: Fiat–Shamir Keccak-256
over the real Keccak-f[1600], trees over a pure `Hm`, WHIR over a pure `F`):

* **`proveRec3With2_eq`**, **`proveRec3With2_eq_some`**: the prover is its stream's run (`streamRunKF`: the seed
  `proverSeedKF` over `Hfs` from the IV over `Hfs` of the setup's roots over `Hm`; the stream's draws over `Hfs`, its
  commitments over `Hm`), then the three openings (`ProverRun.claimProof` over `Hm`, `F`).
* **`pi1Iv_eq`**, **`runFs_eq`**: `RecStatement.pi1Iv` is π1-rec3's prover's IV (`contractIvRec3Of`) at `keccak256`, and
  `UniStatement.runFs` is `runWithFsH` at `keccak256`: the graph's and the verifier's Fiat–Shamir is the prover's.
* **`runFs_kf_syncs`** (**the challenges match**): the verifier's run over Keccak-f[1600] on the prover's stream, from
  π1's IV of the setup's roots at `Hm`, returns the prover's openings and ends at a channel synchronised with the
  prover's final writer, so its challenges (`chan.challenges`) are the prover's (**`runFs_kf_challenges`**) and it
  accepts (**`runFs_kf_accepts`**). Its hypotheses are `runWithFsH_syncs3`'s: the trace valid and fitting, Flock's
  prover synchronising with the walked verifier at a zero walk (`FlockSyncs3`), the paired batch at a zero terminal
  (`BatchSyncsAt3`).
* **`pi1KF_sync_honest`**: at an honest statement of the reference shape those hypotheses hold but for the bad events:
  `¬ BadFp` (a bus challenge making a divided fingerprint vanish) and `¬ BadT` (`t` a bad point) at the prover's own
  front challenges (`frontKF`: `α`, `β`, Flock's point, `t`, which are Keccak-256 over Keccak-f[1600] of the stream);
  Flock's facts from the walk's rows (`FlockSound.Uni.rowValues_spec`, as `uniCompletenessRec3_end_closed`).
* **`pi1KF_accepts`**: off those two bad events, a proof the prover returns (its three proofs of work found) is
  accepted by `RecStatement.pi1KeccakVerifierWith` over `F`, on the setup's roots over `F` (`UniStatement.setupTreesWith`),
  the trees' hash being Keccak-256 over `F` (`hOfF F`, the sponge `pcsOpenWith` and `setupTreesWith` hash with). These
  are exactly π1-rec3's completeness bad events (`UniComplete.Rec3.CoreAccepts3`'s), at the recursion's challenges.
-/

set_option autoImplicit false

open UniStatement LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover

namespace RecCompose.Pi1KF

open UniComplete UniComplete.Rec3 UniComplete.ProverRun
open UniComplete.Core (claims_shape ref_word_c1 ref_word_c2 ref_word_setup commitReal_tree commitReal_halves
  rootRead_digestScalars)

/-! ## The prover at `Id`, two hashes -/

section Pieces

variable (Hfs Hm : List UInt8 → Digest) (F : KeccakState → KeccakState)

/-- **The two-hash prover's seed**: `seedOf` over `Hfs` of π1-rec3's IV over `Hfs` on the setup's roots over `Hm`. -/
def proverSeedKF (programIv : List UInt8) (tr : Trace) : Digest :=
  seedOf (m := Id) Hfs (contractIvRec3Of (m := Id) Hfs tr.shape programIv (setupTreesOf (m := Id) Hm tr).roots)
    tr.publicInput

/-- **The two-hash prover's stream's run** from its seed: draws over `Hfs`, commitments over `Hm`. -/
def streamRunKF (flock : FlockProver Id) (programIv : List UInt8) (tr : Trace) : CoreOut × Wr :=
  (proveStreamRec3With (m := Id) Hfs (commitReal (m := Id) Hm) flock tr).run (Wr.start (proverSeedKF Hfs Hm programIv tr))

/-- **`proveRec3With2` at `Id`**: the three claims' openings over `Hm`, `F`, bound in `Option`. -/
theorem proveRec3With2_eq (fuel : ℕ) (flock : FlockProver Id) (programIv : List UInt8) (tr : Trace) :
    proveRec3With2 (m := Id) Hfs Hm F fuel flock programIv tr =
      (claimProof Hm F fuel (setupTreesOf (m := Id) Hm tr) (streamRunKF Hfs Hm flock programIv tr).1
          (layoutWords tr.shape) .c1).bind fun p1 ↦
      (claimProof Hm F fuel (setupTreesOf (m := Id) Hm tr) (streamRunKF Hfs Hm flock programIv tr).1
          (layoutWords tr.shape) .c2).bind fun p2 ↦
      (claimProof Hm F fuel (setupTreesOf (m := Id) Hm tr) (streamRunKF Hfs Hm flock programIv tr).1
          (layoutWords tr.shape) .setup).bind fun p3 ↦
      some ⟨(streamRunKF Hfs Hm flock programIv tr).1.stream, p1, p2, p3, noProof, noProof⟩ := by
  simp only [proveRec3With2, idBind, idPure, streamRunKF, proverSeedKF]
  generalize (StateT.run (proveStreamRec3With (m := Id) Hfs (commitReal (m := Id) Hm) flock tr)
    (Wr.start (seedOf (m := Id) Hfs (contractIvRec3Of (m := Id) Hfs tr.shape programIv
      (setupTreesOf (m := Id) Hm tr).roots) tr.publicInput))).1 = out
  generalize setupTreesOf (m := Id) Hm tr = trees
  unfold claimProof
  split <;> split <;> split <;> (try simp only [openingFor, *]) <;> rfl

/-- **`proveRec3With2` returns a proof** exactly when the three openings do; the proof is the stream and them. -/
theorem proveRec3With2_eq_some (fuel : ℕ) (flock : FlockProver Id) (programIv : List UInt8) (tr : Trace)
    (π : UniProof) :
    proveRec3With2 (m := Id) Hfs Hm F fuel flock programIv tr = some π ↔
      ∃ p1 p2 p3,
        claimProof Hm F fuel (setupTreesOf (m := Id) Hm tr) (streamRunKF Hfs Hm flock programIv tr).1
          (layoutWords tr.shape) .c1 = some p1 ∧
        claimProof Hm F fuel (setupTreesOf (m := Id) Hm tr) (streamRunKF Hfs Hm flock programIv tr).1
          (layoutWords tr.shape) .c2 = some p2 ∧
        claimProof Hm F fuel (setupTreesOf (m := Id) Hm tr) (streamRunKF Hfs Hm flock programIv tr).1
          (layoutWords tr.shape) .setup = some p3 ∧
        π = ⟨(streamRunKF Hfs Hm flock programIv tr).1.stream, p1, p2, p3, noProof, noProof⟩ := by
  rw [proveRec3With2_eq, Option.bind_eq_some_iff]
  simp only [Option.bind_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨p1, h1, p2, h2, p3, h3, rfl⟩
    exact ⟨p1, p2, p3, h1, h2, h3, rfl⟩
  · rintro ⟨p1, p2, p3, h1, h2, h3, rfl⟩
    exact ⟨p1, h1, p2, h2, p3, h3, rfl⟩

end Pieces

/-! ## The verifier's Fiat–Shamir is the prover's -/

/-- **π1's IV over Keccak-f[1600]** (the graph's and `pi1KeccakVerifierWith`'s) is π1-rec3's prover's IV at
`keccak256`. -/
theorem pi1Iv_eq (s : UniStatement.Shape) (programIv : List UInt8) (roots : SetupRoots) :
    RecStatement.pi1Iv s programIv roots = contractIvRec3Of (m := Id) keccak256 s programIv roots := by
  unfold RecStatement.pi1Iv RecStatement.pi1IvWith contractIvForWith contractIvRec3Of
  simp only [variantBytes_rec3_isEmpty, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- **The verifier's run over Keccak-f[1600]** is `runWithFsH` at `keccak256`. -/
theorem runFs_eq (shape : UniStatement.Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (blake2s : Blake2s)
    (mode : ClaimsMode) (fs : FsShape) (walk : Bool) :
    runFs shape iv publicInput stream blake2s mode fs walk =
      runWithFsH (m := Id) (Pure.pure ∘ keccak256) shape iv publicInput stream blake2s mode fs walk := by
  unfold runFs
  rw [runWithFs_eqH]
  rfl

/-- The two-hash prover's run is `Rec3SyncVerifier`'s `proverRun3` at its IV. -/
theorem streamRunKF_eq (Hm : List UInt8 → Digest) (flock : FlockProver Id) (programIv : List UInt8) (tr : Trace) :
    streamRunKF keccak256 Hm flock programIv tr = proverRun3 keccak256 (commitReal (m := Id) Hm) flock tr
      (RecStatement.pi1Iv tr.shape programIv (setupTreesOf (m := Id) Hm tr).roots) := by
  rw [pi1Iv_eq]
  rfl

/-! ## The challenges match -/

/-- **The challenges match**: π1-rec3's verifier over Keccak-f[1600], from π1's IV of the setup's roots at `Hm`, on the
two-hash prover's stream returns `R` (its openings the prover's point claims, no matrices' claim, its roots the
prover's) and ends at the channel synchronised with the prover's final writer (its challenges the prover's), having
collected the counts' checks, Flock's walk's zero and the batch's terminal. Hypotheses `runWithFsH_syncs3`'s: Flock's
prover synchronising at a zero walk, the paired batch at a zero terminal at the prover's seed. -/
theorem runFs_kf_syncs (Hm : List UInt8 → Digest) (flock : FlockProver Id) (programIv : List UInt8) (tr : Trace)
    (hvalid : tr.shape.Valid) (hfit : tr.shape.RowsFit tr.rows)
    (hflock : FlockSyncs3 keccak256 flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) flockMain
      tr.qflock (fun _ ↦ 0))
    (hbatch : BatchSyncsAt3 keccak256 (commitReal (m := Id) Hm) flock tr (proverSeedKF keccak256 Hm programIv tr)
      (fun _ ↦ 0)) :
    ∃ R : Reduced,
      runFs tr.shape (RecStatement.pi1Iv tr.shape programIv (setupTreesOf (m := Id) Hm tr).roots) tr.publicInput
          (streamRunKF keccak256 Hm flock programIv tr).1.stream (.flock flockMain) .point .rec3 true =
        ⟨.ok R, chanAt (streamRunKF keccak256 Hm flock programIv tr).1.stream
          (streamRunKF keccak256 Hm flock programIv tr).1.stream.size (streamRunKF keccak256 Hm flock programIv tr).2
          (countChecks tr.rows tr.shape.heights ++ [0] ++
            [(0 : E)]).toArray⟩ ∧
      R.openings = (streamRunKF keccak256 Hm flock programIv tr).1.claims.map pointOpening ∧ R.matrices = none ∧
      R.roots = (rootRead (streamRunKF keccak256 Hm flock programIv tr).1.c1.2.halves,
        rootRead (streamRunKF keccak256 Hm flock programIv tr).1.c2.2.halves) := by
  have hseed : proverSeedKF keccak256 Hm programIv tr = seedAt keccak256
      (RecStatement.pi1Iv tr.shape programIv (setupTreesOf (m := Id) Hm tr).roots) tr.publicInput := by
    rw [pi1Iv_eq]
    rfl
  rw [hseed] at hbatch
  rw [streamRunKF_eq, runFs_eq]
  exact runWithFsH_syncs3 keccak256 (commitReal (m := Id) Hm) flock tr _ hvalid hfit hflock (fun _ ↦ 0) hbatch

/-- **The verifier's challenges are the prover's.** -/
theorem runFs_kf_challenges (Hm : List UInt8 → Digest) (flock : FlockProver Id) (programIv : List UInt8)
    (tr : Trace) (hvalid : tr.shape.Valid) (hfit : tr.shape.RowsFit tr.rows)
    (hflock : FlockSyncs3 keccak256 flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) flockMain
      tr.qflock (fun _ ↦ 0))
    (hbatch : BatchSyncsAt3 keccak256 (commitReal (m := Id) Hm) flock tr (proverSeedKF keccak256 Hm programIv tr)
      (fun _ ↦ 0)) :
    (runFs tr.shape (RecStatement.pi1Iv tr.shape programIv (setupTreesOf (m := Id) Hm tr).roots) tr.publicInput
        (streamRunKF keccak256 Hm flock programIv tr).1.stream (.flock flockMain) .point .rec3 true).chan.challenges =
      (streamRunKF keccak256 Hm flock programIv tr).2.challenges := by
  obtain ⟨R, h, -⟩ := runFs_kf_syncs Hm flock programIv tr hvalid hfit hflock hbatch
  rw [h]
  rfl

/-- **The verifier's run accepts** (no error, every collected value zero). -/
theorem runFs_kf_accepts (Hm : List UInt8 → Digest) (flock : FlockProver Id) (programIv : List UInt8)
    (tr : Trace) (hvalid : tr.shape.Valid) (hfit : tr.shape.RowsFit tr.rows)
    (hflock : FlockSyncs3 keccak256 flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) flockMain
      tr.qflock (fun _ ↦ 0))
    (hbatch : BatchSyncsAt3 keccak256 (commitReal (m := Id) Hm) flock tr (proverSeedKF keccak256 Hm programIv tr)
      (fun _ ↦ 0)) :
    (runFs tr.shape (RecStatement.pi1Iv tr.shape programIv (setupTreesOf (m := Id) Hm tr).roots) tr.publicInput
        (streamRunKF keccak256 Hm flock programIv tr).1.stream (.flock flockMain) .point .rec3 true).accepts =
      true := by
  have hseed : proverSeedKF keccak256 Hm programIv tr = seedAt keccak256
      (RecStatement.pi1Iv tr.shape programIv (setupTreesOf (m := Id) Hm tr).roots) tr.publicInput := by
    rw [pi1Iv_eq]
    rfl
  rw [hseed] at hbatch
  rw [streamRunKF_eq, runFs_eq]
  exact runWithFsH_accepts3 keccak256 (commitReal (m := Id) Hm) flock tr _ hvalid hfit hflock (fun _ ↦ 0) hbatch rfl

/-! ## At an honest statement: the bad events are π1-rec3's -/

/-- **The two-hash prover's front state** on an honest statement: its `α`, `β`, Flock's output and point, `t`
(Keccak-256 over Keccak-f[1600] of its stream), at its seed. -/
def frontKF (Hm : List UInt8 → Digest) (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    FrontOut :=
  (frontOf3 keccak256 (commitReal (m := Id) Hm) (flockProve3 (m := Id) (Pure.pure ∘ keccak256))
    (honestTrace D input rows q) (Wr.start (proverSeedKF keccak256 Hm D.programIv (honestTrace D input rows q)))).1

/-- **π1-rec3's completeness bad events at the recursion's challenges**: a bus challenge `β` making a divided
fingerprint vanish, or `t` a bad point for Flock's point (`UniComplete.Rec3.CoreAccepts3`'s, at `frontKF`). -/
def BadKF (Hm : List UInt8 → Digest) (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    Prop :=
  BadFp (honestTrace D input rows q) (frontKF Hm D input rows q).alphas (frontKF Hm D input rows q).beta ∨
    ∃ out, (frontKF Hm D input rows q).flockOut = some out ∧
      Prob.BadT reference out.point (frontKF Hm D input rows q).t

/-- The walk lemma's converse, from the walk's rows (`FlockSound.Uni.rowValues_spec`). -/
theorem walkLemmaConverse_closed : WalkLemmaConverse :=
  walkLemmaConverse_of_rowsSpec fun cw hcw j ↦ FlockSound.Uni.rowValues_spec cw hcw j

/-- **At an honest statement of the reference shape, off `BadKF`**, `runFs_kf_syncs`'s hypotheses hold for π1-rec3's
honest Flock prover at `keccak256`. -/
theorem pi1KF_sync_honest (Hm : List UInt8 → Digest) (D : Deployment) (hD : D.shape = reference)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) (hfit : D.shape.RowsFit rows)
    (hrel : D.HonestRelation rows input q) (hbad : ¬ BadKF Hm D input rows q) :
    TraceHonest (honestTrace D input rows q) ∧
    FlockSyncs3 keccak256 (flockProve3 (m := Id) (Pure.pure ∘ keccak256))
      (blake2sR1csLogSize + (honestTrace D input rows q).shape.heights.getD opBlake2s 0) flockMain
      (honestTrace D input rows q).qflock (fun _ ↦ 0) ∧
    BatchSyncsAt3 keccak256 (commitReal (m := Id) Hm) (flockProve3 (m := Id) (Pure.pure ∘ keccak256))
      (honestTrace D input rows q) (proverSeedKF keccak256 Hm D.programIv (honestTrace D input rows q))
      (fun _ ↦ 0) := by
  have hon : TraceHonest (honestTrace D input rows q) := Mapping.honestTrace_honest D input rows q hfit hrel
  have href : (honestTrace D input rows q).shape = reference := hD
  refine ⟨hon, flockSyncs3_trace walkLemmaConverse_closed keccak256 _ hon, ?_⟩
  refine batchSyncsAt3_front keccak256 _ _ _ hon href _ (flockRing3_flockProve3 keccak256 _ _)
    (flockPointLen3_flockProve3 keccak256 _) ?_ ?_
  · exact fun h ↦ hbad (Or.inl h)
  · exact fun out hout h ↦ hbad (Or.inr ⟨out, hout, h⟩)

/-! ## The honest proof is accepted by the Keccak-f[1600] verifier -/

/-- **Keccak-256 over `F`** (the sponge `UniStatement.pcsOpenWith (pure ∘ F)` and `setupTreesWith (pure ∘ F)` hash with). -/
def hOfF (F : KeccakState → KeccakState) (x : List UInt8) : Digest :=
  Id.run (keccak256With (m := Id) (fun s ↦ pure (F s)) x)

/-- **`pi1KeccakVerifierWith` accepts** when its run over Keccak-f[1600] accepts with the three point claims on `C1`,
`C2`, the setup and the three openings accept (it does not check a matrices' claim). -/
theorem pi1KeccakVerifier_of_calls (F : KeccakState → KeccakState) (D : Deployment) (roots : SetupRoots)
    (input : Vector UInt8 32) (π : UniProof) (o : UniStatement.Outcome) (r : Reduced) (p1 p2 p3 : List E) (v1 v2 v3 : E)
    (hrun : runFs D.shape (RecStatement.pi1Iv D.shape D.programIv roots) input.toList π.stream (.flock flockMain)
      .point .rec3 true = o)
    (hacc : o.accepts = true) (hres : o.result = .ok r)
    (hop : r.openings = [(.c1, .point p1 v1 none), (.c2, .point p2 v2 none), (.setup, .point p3 v3 none)])
    (h1 : pcsOpenWith (m := Id) (fun s ↦ pure (F s)) (layoutWordVars ((layoutWords D.shape).getD 0 []))
      (rootOf r.roots.1) [⟨p1, v1⟩] π.c1 = true)
    (h2 : pcsOpenWith (m := Id) (fun s ↦ pure (F s)) (layoutWordVars ((layoutWords D.shape).getD 1 []))
      (rootOf r.roots.2) [⟨p2, v2⟩] π.c2 = true)
    (h3 : pcsOpenWith (m := Id) (fun s ↦ pure (F s)) (layoutWordVars ((layoutWords D.shape).getD 2 []))
      roots.bytecode [⟨p3, v3⟩] π.setup = true) :
    Id.run (RecStatement.pi1KeccakVerifierWith (m := Id) (fun s ↦ pure (F s)) D roots input π) = true := by
  unfold RecStatement.pi1KeccakVerifierWith
  simp only [hrun]
  simp only [bind, pure, List.getD_eq_getElem?_getD] at h1 h2 h3 ⊢
  simp only [hacc, hres, hop, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp [commitments, h1, h2, h3]
  rfl

set_option maxHeartbeats 1000000 in
/-- **π1-rec3's honest proof, two hashes, is accepted by the Keccak-f[1600] verifier**, for an honest trace at the
reference shape (its setup the deployment's) whose Flock step synchronises at a zero walk and whose paired batch
synchronises at a zero terminal, its trees and openings over `hOfF F`, `F`. -/
theorem accepts_of_traceKF (D : Deployment) (F : KeccakState → KeccakState) (input : Vector UInt8 32) (tr : Trace)
    (π : UniProof) (flock : FlockProver Id) (hon : TraceHonest tr) (href : tr.shape = reference)
    (hshape : tr.shape = D.shape) (hpi : tr.publicInput = input.toList)
    (hsetup : setupStackOf tr = setupStack D.prog D.shape)
    (hflock : FlockSyncs3 keccak256 flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) flockMain
      tr.qflock (fun _ ↦ 0))
    (hbatch : BatchSyncsAt3 keccak256 (commitReal (m := Id) (hOfF F)) flock tr
      (proverSeedKF keccak256 (hOfF F) D.programIv tr) (fun _ ↦ 0))
    (hs1 : (c1Stack tr).size = 2 ^ 27)
    (hs2 : ∀ alphas beta gamma, (c2DataOf tr (eqKernel alphas) beta gamma).stack.size = 2 ^ 27)
    (hs3 : (setupStackOf tr).size = 2 ^ 24)
    (hπ : proveRec3With2 (m := Id) keccak256 (hOfF F) F PcsQuotient.nonceFuel flock D.programIv tr = some π) :
    Id.run (RecStatement.pi1KeccakVerifierWith (m := Id) (fun s ↦ pure (F s)) D
      (Id.run (setupTreesWith (m := Id) (fun s ↦ pure (F s)) D)).roots input π) = true := by
  have htrees : Id.run (setupTreesWith (m := Id) (fun s ↦ pure (F s)) D) = setupTreesOf (m := Id) (hOfF F) tr := by
    rw [setupTreesWith_eqH]
    unfold setupTreesWithH setupTreesOf
    rw [hsetup, hshape]
    all_goals rfl
  have hC2 := c2ColumnsHonest_of_traceHonest hon
  obtain ⟨p1, p2, p3, h1, h2, h3, rfl⟩ := (proveRec3With2_eq_some keccak256 (hOfF F) F _ _ _ _ π).mp hπ
  obtain ⟨R, hrunR, hopR, -, hrootR⟩ := runFs_kf_syncs (hOfF F) flock D.programIv tr hon.valid hon.rowsFit hflock
    hbatch
  have hacc := runFs_kf_accepts (hOfF F) flock D.programIv tr hon.valid hon.rowsFit hflock hbatch
  have hf : StreamFacts3 (commitReal (m := Id) (hOfF F)) tr (streamRunKF keccak256 (hOfF F) flock D.programIv tr).1 :=
    streamRun3_facts keccak256 (commitReal (m := Id) (hOfF F)) flock tr _
  have hv : StreamValues3 tr (streamRunKF keccak256 (hOfF F) flock D.programIv tr).1 :=
    streamValues3 keccak256 (commitReal (m := Id) (hOfF F)) flock tr _
  rw [htrees]
  rw [hshape, hpi] at hacc hrunR
  generalize (streamRunKF keccak256 (hOfF F) flock D.programIv tr).1 = out at hf hv h1 h2 h3 hopR hrootR hrunR hacc ⊢
  -- The claims.
  obtain ⟨pt1, v1, pt2, v2, pt3, v3, hcl⟩ := claims_shape _ hf.claims_fst
  have hmem : ∀ x ∈ [(Commitment.c1, pt1, v1), (.c2, pt2, v2), (.setup, pt3, v3)], x ∈ out.claims := by
    rw [hcl]; exact fun _ h ↦ h
  have hpts := hf.points hC2
  rw [href, ref_rounds] at hpts
  have hl1 : pt1.length = 27 := by simpa [ref_layoutIn_c1] using hpts _ (hmem (.c1, pt1, v1) (by simp))
  have hl2 : pt2.length = 27 := by simpa [ref_layoutIn_c2] using hpts _ (hmem (.c2, pt2, v2) (by simp))
  have hl3 : pt3.length = 24 := by simpa [ref_layoutIn_setup] using hpts _ (hmem (.setup, pt3, v3) (by simp))
  have hv1 : v1 = stackEval (c1Stack tr) pt1 := by
    have := hv.values _ (hmem (.c1, pt1, v1) (by simp)); rw [hf.c1] at this; exact this
  have hv2 : v2 = stackEval out.c2.1 pt2 := hv.values _ (hmem (.c2, pt2, v2) (by simp))
  have hv3 : v3 = stackEval (setupStackOf tr) pt3 := by
    have := hv.values _ (hmem (.setup, pt3, v3) (by simp)); rw [hf.setup] at this; exact this
  obtain ⟨α2, β2, γ2, hc2s⟩ := hv.c2stack
  have hs2' : out.c2.1.size = 2 ^ 27 := by rw [hc2s]; exact hs2 α2 β2 γ2
  -- The openings the prover made.
  have hfind : ∀ c, out.claims.find? (·.1 == c) =
      [(Commitment.c1, pt1, v1), (.c2, pt2, v2), (.setup, pt3, v3)].find? (·.1 == c) := by
    intro c; rw [hcl]
  obtain ⟨c1', q1, w1, hf1, ho1⟩ := (claimProof_eq_some (hOfF F) F _ _ _ _ _ _).mp h1
  obtain ⟨c2', q2, w2, hf2, ho2⟩ := (claimProof_eq_some (hOfF F) F _ _ _ _ _ _).mp h2
  obtain ⟨c3', q3, w3, hf3, ho3⟩ := (claimProof_eq_some (hOfF F) F _ _ _ _ _ _).mp h3
  have e1 : some (Commitment.c1, pt1, v1) = some (c1', q1, w1) := ((hfind .c1).trans rfl).symm.trans hf1
  have e2 : some (Commitment.c2, pt2, v2) = some (c2', q2, w2) := ((hfind .c2).trans rfl).symm.trans hf2
  have e3 : some (Commitment.setup, pt3, v3) = some (c3', q3, w3) := ((hfind .setup).trans rfl).symm.trans hf3
  simp only [Option.some.injEq, Prod.mk.injEq] at e1 e2 e3
  rw [← e1.2.1, ← e1.2.2] at ho1
  rw [← e2.2.1, ← e2.2.2] at ho2
  rw [← e3.2.1, ← e3.2.2] at ho3
  have ho1' : E2ECompleteness.proveOpeningWithH (m := Id) (hOfF F) F PcsQuotient.nonceFuel (plainLayout 27)
      (E2ECompleteness.commitWithH (m := Id) (hOfF F) 27 (c1Stack tr)) (c1Stack tr)
      [⟨pt1, stackEval (c1Stack tr) pt1⟩] = some p1 := by
    have : E2ECompleteness.proveOpeningWithH (m := Id) (hOfF F) F PcsQuotient.nonceFuel
        (plainLayout (layoutWordVars ((layoutWords tr.shape).getD 0 []))) out.c1.2.tree out.c1.1 [⟨pt1, v1⟩] =
        some p1 := ho1
    simp only [hf.c1, commitReal_tree, href, ref_word_c1, ref_c1Layout, hv1] at this
    exact this
  have ho2' : E2ECompleteness.proveOpeningWithH (m := Id) (hOfF F) F PcsQuotient.nonceFuel (plainLayout 27)
      (E2ECompleteness.commitWithH (m := Id) (hOfF F) 27 out.c2.1) out.c2.1 [⟨pt2, stackEval out.c2.1 pt2⟩] =
      some p2 := by
    have : E2ECompleteness.proveOpeningWithH (m := Id) (hOfF F) F PcsQuotient.nonceFuel
        (plainLayout (layoutWordVars ((layoutWords tr.shape).getD 1 []))) out.c2.2.tree out.c2.1 [⟨pt2, v2⟩] =
        some p2 := ho2
    simp only [hf.c2, commitReal_tree, href, ref_word_c2, ref_c2Layout, hv2] at this
    exact this
  have ho3' : E2ECompleteness.proveOpeningWithH (m := Id) (hOfF F) F PcsQuotient.nonceFuel (plainLayout 24)
      (E2ECompleteness.commitWithH (m := Id) (hOfF F) 24 (setupStackOf tr)) (setupStackOf tr)
      [⟨pt3, stackEval (setupStackOf tr) pt3⟩] = some p3 := by
    have : E2ECompleteness.proveOpeningWithH (m := Id) (hOfF F) F PcsQuotient.nonceFuel
        (plainLayout (layoutWordVars ((layoutWords tr.shape).getD 2 [])))
        (E2ECompleteness.commitWithH (m := Id) (hOfF F) (setupLayout tr.shape).vars (setupStackOf tr)) out.setup
        [⟨pt3, v3⟩] = some p3 := ho3
    simp only [hf.setup, href, ref_word_setup, ref_setupLayout, hv3] at this
    exact this
  -- WHIR accepts each.
  have a1 := pcsOpen_honest (hOfF F) F _ (vars := 27) (by norm_num) (by norm_num) _ hs1 pt1 hl1 ho1'
  have a2 := pcsOpen_honest (hOfF F) F _ (vars := 27) (by norm_num) (by norm_num) _ hs2' pt2 hl2 ho2'
  have a3 := pcsOpen_honest (hOfF F) F _ (vars := 24) (by norm_num) (by norm_num) _ hs3 pt3 hl3 ho3'
  -- The verifier.
  have hD : D.shape = reference := hshape.symm.trans href
  refine pi1KeccakVerifier_of_calls F D _ input _ _ R pt1 pt2 pt3 v1 v2 v3 ?_ hacc ?_ ?_ ?_ ?_ ?_
  · rfl
  · rw [hrunR]
  · rw [hopR, hcl]; rfl
  · rw [pcsOpenWith_eqH]
    simp only [hrootR, hf.c1, commitReal_halves, rootRead_digestScalars, rootOf_digestScalars, hD, ref_word_c1,
      href, ref_c1Layout, hv1]
    exact a1
  · rw [pcsOpenWith_eqH]
    simp only [hrootR, hf.c2, commitReal_halves, rootRead_digestScalars, rootOf_digestScalars, hD, ref_word_c2,
      href, ref_c2Layout, hv2]
    exact a2
  · rw [pcsOpenWith_eqH]
    simp only [hD, ref_word_setup, hv3, SetupTrees.roots, setupTrees_bytecode, href, ref_setupLayout]
    exact a3

/-- **The recursion's π1 prover is accepted by π1-rec3's verifier at Keccak-f[1600] off π1-rec3's completeness bad
events**: at an honest statement of the reference shape, a pure permutation `F` (the eager model's `π`), its trees and
openings over `hOfF F`, `F` and its Fiat–Shamir Keccak-256 over the real Keccak-f[1600], if it returns a proof (its
three proofs of work found) and neither bad event holds at its own challenges (`BadKF`), then
`RecStatement.pi1KeccakVerifierWith` over `F` accepts it on the setup's roots over `F`. -/
theorem pi1KF_accepts (D : Deployment) (hD : D.shape = reference) (F : KeccakState → KeccakState)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) (hfit : D.shape.RowsFit rows)
    (hrel : D.HonestRelation rows input q) (π : UniProof)
    (hπ : uniProverRec3With2 (m := Id) hKF (hOfF F) F (flockProve3H hKF) D input rows q = some π)
    (hbad : ¬ BadKF (hOfF F) D input rows q) :
    Id.run (RecStatement.pi1KeccakVerifierWith (m := Id) (fun s ↦ pure (F s)) D
      (Id.run (setupTreesWith (m := Id) (fun s ↦ pure (F s)) D)).roots input π) = true := by
  have hπ' : proveRec3With2 (m := Id) keccak256 (hOfF F) F PcsQuotient.nonceFuel
      (flockProve3 (m := Id) (Pure.pure ∘ keccak256)) D.programIv (honestTrace D input rows q) = some π := hπ
  obtain ⟨hon, hflock, hbatch⟩ := pi1KF_sync_honest (hOfF F) D hD input rows q hfit hrel hbad
  have href : (honestTrace D input rows q).shape = reference := hD
  exact accepts_of_traceKF D F input (honestTrace D input rows q) π (flockProve3 (m := Id) (Pure.pure ∘ keccak256))
    hon href rfl rfl (setupStackOf_honestTrace D input rows q) hflock hbatch (Core.c1Stack_size _ href)
    (fun alphas beta gamma ↦ Core.c2Stack_size _ href (eqKernel alphas) beta gamma) (Core.setupStackOf_size _ href) hπ'

/-- **The challenges match, at an honest statement**: off `BadKF`, the verifier's run over Keccak-f[1600] on the
recursion's π1 prover's stream, from π1's IV of the setup's roots at `Hm`, has the prover's challenges and accepts. -/
theorem pi1KF_challenges (Hm : List UInt8 → Digest) (D : Deployment) (hD : D.shape = reference)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) (hfit : D.shape.RowsFit rows)
    (hrel : D.HonestRelation rows input q) (hbad : ¬ BadKF Hm D input rows q) :
    (runFs D.shape (RecStatement.pi1Iv D.shape D.programIv (setupTreesOf (m := Id) Hm (honestTrace D input rows q)).roots)
        input.toList (streamRunKF keccak256 Hm (flockProve3 (m := Id) (Pure.pure ∘ keccak256)) D.programIv
          (honestTrace D input rows q)).1.stream (.flock flockMain) .point .rec3 true).chan.challenges =
      (streamRunKF keccak256 Hm (flockProve3 (m := Id) (Pure.pure ∘ keccak256)) D.programIv
        (honestTrace D input rows q)).2.challenges ∧
    (runFs D.shape (RecStatement.pi1Iv D.shape D.programIv (setupTreesOf (m := Id) Hm (honestTrace D input rows q)).roots)
        input.toList (streamRunKF keccak256 Hm (flockProve3 (m := Id) (Pure.pure ∘ keccak256)) D.programIv
          (honestTrace D input rows q)).1.stream (.flock flockMain) .point .rec3 true).accepts = true := by
  obtain ⟨hon, hflock, hbatch⟩ := pi1KF_sync_honest Hm D hD input rows q hfit hrel hbad
  exact ⟨runFs_kf_challenges Hm (flockProve3 (m := Id) (Pure.pure ∘ keccak256)) D.programIv
      (honestTrace D input rows q) hon.valid hon.rowsFit hflock hbatch,
    runFs_kf_accepts Hm (flockProve3 (m := Id) (Pure.pure ∘ keccak256)) D.programIv (honestTrace D input rows q)
      hon.valid hon.rowsFit hflock hbatch⟩

/-- The recursion's π1 prover at `Id`, unfolded. -/
theorem uniProverRec3With2_hKF (Hm : List UInt8 → Digest) (F : KeccakState → KeccakState) (D : Deployment)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    uniProverRec3With2 (m := Id) hKF Hm F (flockProve3H hKF) D input rows q =
      proveRec3With2 (m := Id) keccak256 Hm F PcsQuotient.nonceFuel (flockProve3 (m := Id) (Pure.pure ∘ keccak256))
        D.programIv (honestTrace D input rows q) := rfl

/-- **The proof's stream is the stream's run's.** -/
theorem stream_of_kf (Hm : List UInt8 → Digest) (F : KeccakState → KeccakState) (D : Deployment)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) (π : UniProof)
    (hπ : uniProverRec3With2 (m := Id) hKF Hm F (flockProve3H hKF) D input rows q = some π) :
    π.stream = (streamRunKF keccak256 Hm (flockProve3 (m := Id) (Pure.pure ∘ keccak256)) D.programIv
      (honestTrace D input rows q)).1.stream := by
  rw [uniProverRec3With2_hKF] at hπ
  obtain ⟨p1, p2, p3, -, -, -, hπe⟩ := (proveRec3With2_eq_some keccak256 Hm F PcsQuotient.nonceFuel
    (flockProve3 (m := Id) (Pure.pure ∘ keccak256)) D.programIv (honestTrace D input rows q) π).mp hπ
  rw [hπe]

end RecCompose.Pi1KF

/-- info: 'RecCompose.Pi1KF.runFs_kf_challenges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1KF.runFs_kf_challenges

/-- info: 'RecCompose.Pi1KF.pi1KF_challenges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1KF.pi1KF_challenges

/-- info: 'RecCompose.Pi1KF.pi1KF_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1KF.pi1KF_accepts

/-- info: 'RecCompose.Pi1KF.runFs_kf_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1KF.runFs_kf_accepts

/-- info: 'RecCompose.Pi1KF.stream_of_kf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1KF.stream_of_kf
