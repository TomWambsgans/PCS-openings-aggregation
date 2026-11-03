-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π1-rec3's honest proof is accepted: `Core.lean`'s
-- `accepts_of_trace`, `coreAccepts_of` for π1-rec3's verifier (`Rec3VerifierH.lean`'s `verifierRec3WithH`, three
-- `PCS_OPEN` calls) and prover (`Rec3Prover.lean`).
import UniComplete.Rec3CoreBatch
import UniComplete.Rec3CoreRun
import UniComplete.Core

/-!
# π1-rec3's honest proof is accepted

* **`verifyWithFsH_of_calls3`**: π1-rec3's verifier (`verifyWithFsH … .rec3 true`: the run, then three `PCS_OPEN`
  calls) accepts when its run accepts with the three point claims on `C1`, `C2`, the setup, no matrices' claim, and the
  three openings accept.
* **`accepts_of_trace3`**: for an honest trace at the reference shape (its setup the deployment's), Flock's prover
  synchronising with the walked verifier at a zero walk (`FlockSyncs3 … (fun _ ↦ 0)`) and the paired batch at a zero
  terminal (`BatchSyncsAt3 … (fun _ ↦ 0)`), a proof `proveRec3With` returns is accepted: the run on the prover's stream
  accepts (`runWithFsH_syncs3`, `runWithFsH_accepts3`), its claims are the prover's (`streamRun3_facts`,
  `streamValues3`), and WHIR's three honest openings are accepted (`pcsOpen_honest`, at `27, 27, 24` variables).
* **`front_challenges3`**: the staged challenges are the prover's front state's (`α`, `β`, Flock's point, `t`).
* **`coreAccepts3_of`**: `CoreAccepts3 D flock` at the reference shape, from Flock's three facts (`FlockSyncs3` at a
  zero walk, `FlockRing3`, `FlockPointLen3`, for every honest trace and hash), the bad events moved to the prover's
  front state by `front_challenges3`.
-/

open UniStatement LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover

namespace UniComplete.Rec3

open ProverRun
open UniComplete.Core (claims_shape ref_word_c1 ref_word_c2 ref_word_setup commitReal_tree commitReal_halves
  rootRead_digestScalars)

/-! ## When π1-rec3's verifier accepts -/

/-- **π1-rec3's verifier accepts** when its run does with the three point claims and no matrices' claim, and the
three openings accept. -/
theorem verifyWithFsH_of_calls3 (H : List UInt8 → Digest) (F : KeccakState → KeccakState)
    (shape : UniStatement.Shape) (iv : List UInt8) (roots : SetupRoots) (input : Vector UInt8 32) (π : UniProof)
    (o : UniStatement.Outcome) (r : Reduced) (p1 p2 p3 : List E) (v1 v2 v3 : E)
    (hrun : runWithFsH (m := Id) (fun b ↦ pure (H b)) shape iv input.toList π.stream (.flock flockMain) .point .rec3
      true = o)
    (hacc : o.accepts = true) (hres : o.result = .ok r)
    (hop : r.openings = [(.c1, .point p1 v1 none), (.c2, .point p2 v2 none), (.setup, .point p3 v3 none)])
    (hmat : r.matrices = none)
    (h1 : pcsOpenWithH (m := Id) (fun b ↦ pure (H b)) (fun s ↦ pure (F s))
      (layoutWordVars ((layoutWords shape).getD 0 [])) (rootOf r.roots.1) [⟨p1, v1⟩] π.c1 = true)
    (h2 : pcsOpenWithH (m := Id) (fun b ↦ pure (H b)) (fun s ↦ pure (F s))
      (layoutWordVars ((layoutWords shape).getD 1 [])) (rootOf r.roots.2) [⟨p2, v2⟩] π.c2 = true)
    (h3 : pcsOpenWithH (m := Id) (fun b ↦ pure (H b)) (fun s ↦ pure (F s))
      (layoutWordVars ((layoutWords shape).getD 2 [])) roots.bytecode [⟨p3, v3⟩] π.setup = true) :
    verifyWithFsH (m := Id) (fun b ↦ pure (H b)) (fun s ↦ pure (F s)) shape iv roots input π .rec3 true = true := by
  unfold verifyWithFsH
  simp only [hrun]
  simp only [bind, pure, List.getD_eq_getElem?_getD] at h1 h2 h3 ⊢
  simp only [hacc, hres, hop, hmat, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp [commitments, h1, h2, h3]
  rfl

theorem variantBytes_rec3_isEmpty : (variantBytes (.flock flockMain) .rec3 true).isEmpty = false := by
  decide +kernel

/-- **π1-rec3's IV at a pure hash** is the prover's (`contractIvRec3Of`). -/
theorem ivRec3WithH_eq (H : List UInt8 → Digest) (D : Deployment) (roots : SetupRoots) :
    Deployment.ivRec3WithH (m := Id) H D roots = contractIvRec3Of (m := Id) H D.shape D.programIv roots := by
  unfold Deployment.ivRec3WithH contractIvForWithH contractIvRec3Of
  simp only [variantBytes_rec3_isEmpty, Bool.false_eq_true, ↓reduceIte]

/-! ## The honest proof is accepted -/

set_option maxHeartbeats 1000000 in
/-- **π1-rec3's honest proof is accepted**, for an honest trace at the reference shape (its setup the deployment's)
whose Flock step synchronises at a zero walk and whose paired batch synchronises at a zero terminal. -/
theorem accepts_of_trace3 (D : Deployment) (H : List UInt8 → Digest) (F : KeccakState → KeccakState)
    (input : Vector UInt8 32) (tr : Trace) (π : UniProof) (flock : FlockProver Id) (hon : TraceHonest tr)
    (href : tr.shape = reference) (hshape : tr.shape = D.shape) (hpi : tr.publicInput = input.toList)
    (hsetup : setupStackOf tr = setupStack D.prog D.shape)
    (hflock : FlockSyncs3 H flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) flockMain tr.qflock
      (fun _ ↦ 0))
    (hbatch : BatchSyncsAt3 H (commitReal (m := Id) H) flock tr (proverSeed3 H D.programIv tr) (fun _ ↦ 0))
    (hs1 : (c1Stack tr).size = 2 ^ 27)
    (hs2 : ∀ alphas beta gamma, (c2DataOf tr (eqKernel alphas) beta gamma).stack.size = 2 ^ 27)
    (hs3 : (setupStackOf tr).size = 2 ^ 24)
    (hπ : proveRec3With (m := Id) H F PcsQuotient.nonceFuel flock D.programIv tr = some π) :
    Deployment.verifierRec3WithH (m := Id) H F D (setupTreesWithH (m := Id) H F D).roots input π = true := by
  have htrees : setupTreesWithH (m := Id) H F D = setupTreesOf (m := Id) H tr := by
    unfold setupTreesWithH setupTreesOf
    rw [hsetup, hshape]
  have hiv : Deployment.ivRec3WithH (m := Id) H D (setupTreesOf (m := Id) H tr).roots =
      contractIvRec3Of (m := Id) H tr.shape D.programIv (setupTreesOf (m := Id) H tr).roots := by
    rw [hshape]; exact ivRec3WithH_eq H D _
  have hC2 := c2ColumnsHonest_of_traceHonest hon
  -- The prover's proof.
  obtain ⟨p1, p2, p3, h1, h2, h3, rfl⟩ := (proveRec3With_eq_some H F _ _ _ _ π).mp hπ
  -- The verifier's run on the prover's stream.
  obtain ⟨R, hrunR, hopR, hmatR, hrootR⟩ := runWithFsH_syncs3 H (commitReal (m := Id) H) flock tr
    (contractIvRec3Of (m := Id) H tr.shape D.programIv (setupTreesOf (m := Id) H tr).roots) hon.valid hon.rowsFit
    hflock (fun _ ↦ 0) hbatch
  have hacc := runWithFsH_accepts3 H (commitReal (m := Id) H) flock tr
    (contractIvRec3Of (m := Id) H tr.shape D.programIv (setupTreesOf (m := Id) H tr).roots) hon.valid hon.rowsFit
    hflock (fun _ ↦ 0) hbatch rfl
  have hrun_eq : proverRun3 H (commitReal (m := Id) H) flock tr
      (contractIvRec3Of (m := Id) H tr.shape D.programIv (setupTreesOf (m := Id) H tr).roots) =
      streamRun3 H flock D.programIv tr := rfl
  rw [hrun_eq] at hrunR hopR hrootR hacc
  have hf : StreamFacts3 (commitReal (m := Id) H) tr (streamRun3 H flock D.programIv tr).1 :=
    streamRun3_facts H (commitReal (m := Id) H) flock tr _
  have hv : StreamValues3 tr (streamRun3 H flock D.programIv tr).1 :=
    streamValues3 H (commitReal (m := Id) H) flock tr _
  generalize (streamRun3 H flock D.programIv tr).1 = out at hf hv h1 h2 h3 hopR hrootR hrunR hacc ⊢
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
  obtain ⟨c1', q1, w1, hf1, ho1⟩ := (claimProof_eq_some H F _ _ _ _ _ _).mp h1
  obtain ⟨c2', q2, w2, hf2, ho2⟩ := (claimProof_eq_some H F _ _ _ _ _ _).mp h2
  obtain ⟨c3', q3, w3, hf3, ho3⟩ := (claimProof_eq_some H F _ _ _ _ _ _).mp h3
  have e1 : some (Commitment.c1, pt1, v1) = some (c1', q1, w1) := ((hfind .c1).trans rfl).symm.trans hf1
  have e2 : some (Commitment.c2, pt2, v2) = some (c2', q2, w2) := ((hfind .c2).trans rfl).symm.trans hf2
  have e3 : some (Commitment.setup, pt3, v3) = some (c3', q3, w3) := ((hfind .setup).trans rfl).symm.trans hf3
  simp only [Option.some.injEq, Prod.mk.injEq] at e1 e2 e3
  rw [← e1.2.1, ← e1.2.2] at ho1
  rw [← e2.2.1, ← e2.2.2] at ho2
  rw [← e3.2.1, ← e3.2.2] at ho3
  have ho1' : E2ECompleteness.proveOpeningWithH (m := Id) H F PcsQuotient.nonceFuel (plainLayout 27)
      (E2ECompleteness.commitWithH (m := Id) H 27 (c1Stack tr)) (c1Stack tr) [⟨pt1, stackEval (c1Stack tr) pt1⟩] =
      some p1 := by
    have : E2ECompleteness.proveOpeningWithH (m := Id) H F PcsQuotient.nonceFuel
        (plainLayout (layoutWordVars ((layoutWords tr.shape).getD 0 []))) out.c1.2.tree out.c1.1 [⟨pt1, v1⟩] =
        some p1 := ho1
    simp only [hf.c1, commitReal_tree, href, ref_word_c1, ref_c1Layout, hv1] at this
    exact this
  have ho2' : E2ECompleteness.proveOpeningWithH (m := Id) H F PcsQuotient.nonceFuel (plainLayout 27)
      (E2ECompleteness.commitWithH (m := Id) H 27 out.c2.1) out.c2.1 [⟨pt2, stackEval out.c2.1 pt2⟩] =
      some p2 := by
    have : E2ECompleteness.proveOpeningWithH (m := Id) H F PcsQuotient.nonceFuel
        (plainLayout (layoutWordVars ((layoutWords tr.shape).getD 1 []))) out.c2.2.tree out.c2.1 [⟨pt2, v2⟩] =
        some p2 := ho2
    simp only [hf.c2, commitReal_tree, href, ref_word_c2, ref_c2Layout, hv2] at this
    exact this
  have ho3' : E2ECompleteness.proveOpeningWithH (m := Id) H F PcsQuotient.nonceFuel (plainLayout 24)
      (E2ECompleteness.commitWithH (m := Id) H 24 (setupStackOf tr)) (setupStackOf tr)
      [⟨pt3, stackEval (setupStackOf tr) pt3⟩] = some p3 := by
    have : E2ECompleteness.proveOpeningWithH (m := Id) H F PcsQuotient.nonceFuel
        (plainLayout (layoutWordVars ((layoutWords tr.shape).getD 2 [])))
        (E2ECompleteness.commitWithH (m := Id) H (setupLayout tr.shape).vars (setupStackOf tr)) out.setup
        [⟨pt3, v3⟩] = some p3 := ho3
    simp only [hf.setup, href, ref_word_setup, ref_setupLayout, hv3] at this
    exact this
  -- WHIR accepts each.
  have a1 := pcsOpen_honest H F _ (vars := 27) (by norm_num) (by norm_num) _ hs1 pt1 hl1 ho1'
  have a2 := pcsOpen_honest H F _ (vars := 27) (by norm_num) (by norm_num) _ hs2' pt2 hl2 ho2'
  have a3 := pcsOpen_honest H F _ (vars := 24) (by norm_num) (by norm_num) _ hs3 pt3 hl3 ho3'
  -- The verifier.
  show verifyWithFsH (m := Id) H F D.shape
    (Deployment.ivRec3WithH (m := Id) H D (setupTreesWithH (m := Id) H F D).roots)
    (setupTreesWithH (m := Id) H F D).roots input _ .rec3 true = true
  rw [htrees, hiv]
  have hD : D.shape = reference := hshape.symm.trans href
  refine verifyWithFsH_of_calls3 H F D.shape _ _ input _ _ R pt1 pt2 pt3 v1 v2 v3 ?_ hacc ?_ ?_ hmatR ?_ ?_ ?_
  · rw [← hshape, ← hpi]; rfl
  · rw [hrunR]
  · rw [hopR, hcl]; rfl
  · simp only [hrootR, hf.c1, commitReal_halves, rootRead_digestScalars, rootOf_digestScalars, hD, ref_word_c1,
      href, ref_c1Layout, hv1]
    exact a1
  · simp only [hrootR, hf.c2, commitReal_halves, rootRead_digestScalars, rootOf_digestScalars, hD, ref_word_c2,
      href, ref_c2Layout, hv2]
    exact a2
  · simp only [hD, ref_word_setup, hv3, SetupTrees.roots, setupTrees_bytecode, href, ref_setupLayout]
    exact a3

/-! ## The staged challenges are the prover's -/

/-- **The staged challenges are π1-rec3's prover's front state's**: `α`, `β`, Flock's point, `t`. -/
theorem front_challenges3 (H : List UInt8 → Digest) (flock : FlockProver Id) (D : Deployment)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    (frontOf3 H (commitReal (m := Id) H) flock (honestTrace D input rows q)
        (Wr.start (proverSeed3 H D.programIv (honestTrace D input rows q)))).1.alphas =
        (proverChallenges3 H D input rows q).1 ∧
      (frontOf3 H (commitReal (m := Id) H) flock (honestTrace D input rows q)
        (Wr.start (proverSeed3 H D.programIv (honestTrace D input rows q)))).1.beta =
        (proverChallenges3 H D input rows q).2 ∧
      (frontOf3 H (commitReal (m := Id) H) flock (honestTrace D input rows q)
          (Wr.start (proverSeed3 H D.programIv (honestTrace D input rows q)))).1.flockOut.map (·.point) =
        some (proverTChallenge3 H flock D input rows q).1 ∧
      (frontOf3 H (commitReal (m := Id) H) flock (honestTrace D input rows q)
        (Wr.start (proverSeed3 H D.programIv (honestTrace D input rows q)))).1.t =
        (proverTChallenge3 H flock D input rows q).2 := by
  set tr := honestTrace D input rows q
  set c1 := E2ECompleteness.commitWithH (m := Id) H (c1Layout tr.shape).vars (c1Stack tr)
  set seed := proverSeed3 H D.programIv tr
  have hw2 : ((Wr.start seed).append (tr.rows.flatMap fun n ↦ integerWire n 4)).append
      (rootWord (commitReal (m := Id) H .c1 (c1Layout tr.shape).vars (c1Stack tr)).halves) =
      ⟨Prob.prefixStream rows c1, 0, seed, #[]⟩ := rfl
  set s₁ := H (digestBytes seed ++ ((Prob.prefixStream rows c1).extract 0 (Prob.prefixStream rows c1).size).toList)
  have h1 : Wr.sampled H ⟨Prob.prefixStream rows c1, 0, seed, #[]⟩ =
      (Prob.chal s₁, ⟨Prob.prefixStream rows c1, (Prob.prefixStream rows c1).size, s₁, #[Prob.chal s₁]⟩) := rfl
  have h2 : Wr.sampled H ⟨Prob.prefixStream rows c1, (Prob.prefixStream rows c1).size, s₁, #[Prob.chal s₁]⟩ =
      (Prob.chal (H (digestBytes s₁)), writerAfter3 rows c1 s₁ (H (digestBytes s₁))) := by
    simp only [Wr.sampled, Prob.extract_size_toList, List.append_nil]
    rfl
  unfold frontOf3
  simp only []
  rw [hw2, h1, h2]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## The core fact of the probability layer -/

/-- **`CoreAccepts3` at the reference shape**, from Flock's three facts at every hash and honest trace: the walked
verifier synchronises at a zero walk, the ring switch's target is true, the point has `h_B + 8` coordinates. -/
theorem coreAccepts3_of (D : Deployment) (hD : D.shape = reference) (flock : FlockProverH)
    (hflock : ∀ (H : List UInt8 → Digest) (tr : Trace), TraceHonest tr → tr.shape = reference →
      FlockSyncs3 H (flock (m := Id) (Pure.pure ∘ H)) (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0)
        flockMain tr.qflock (fun _ ↦ 0))
    (hring : ∀ (H : List UInt8 → Digest) (tr : Trace), TraceHonest tr → tr.shape = reference →
      FlockRing3 (flock (m := Id) (Pure.pure ∘ H)) (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0)
        tr.qflock)
    (hlen : ∀ (H : List UInt8 → Digest) (tr : Trace), TraceHonest tr → tr.shape = reference →
      FlockPointLen3 (flock (m := Id) (Pure.pure ∘ H)) tr) :
    CoreAccepts3 D flock := by
  intro input rows q hfit hrel H F π hπ hbad hbadT
  have hon : TraceHonest (honestTrace D input rows q) := Mapping.honestTrace_honest D input rows q hfit hrel
  have href : (honestTrace D input rows q).shape = reference := hD
  obtain ⟨hα, hβ, hpt, ht⟩ := front_challenges3 H (flock (m := Id) (Pure.pure ∘ H)) D input rows q
  refine accepts_of_trace3 D H F input (honestTrace D input rows q) π (flock (m := Id) (Pure.pure ∘ H)) hon href
    rfl rfl (setupStackOf_honestTrace D input rows q) (hflock H _ hon href) ?_
    (Core.c1Stack_size _ href) (fun alphas beta gamma ↦ Core.c2Stack_size _ href (eqKernel alphas) beta gamma)
    (Core.setupStackOf_size _ href) hπ
  refine batchSyncsAt3_front H _ _ _ hon href _ (hring H _ hon href) (hlen H _ hon href) ?_ ?_
  · rw [hα, hβ]
    exact hbad
  · intro out hout
    rw [hout, Option.map_some, Option.some.injEq] at hpt
    rw [hpt, ht]
    have h := hbadT
    rw [hD] at h
    exact h

end UniComplete.Rec3

/-- info: 'UniComplete.Rec3.accepts_of_trace3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.accepts_of_trace3

/-- info: 'UniComplete.Rec3.coreAccepts3_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.coreAccepts3_of
