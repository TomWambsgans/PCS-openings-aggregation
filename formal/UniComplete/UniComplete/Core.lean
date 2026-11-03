-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.CoreRun
import UniComplete.FlockCost
import UniComplete.VerifierAccept
import UniComplete.Whir
import UniComplete.Setup
import UniComplete.Mapping

/-!
# The honest prover's proof is accepted

The core of completeness at a pure hash and permutation (`Prob.CoreAccepts`, `Prob.CoreFailsOnlyAtPow`,
`Prob.BadFpCard`), for Flock's honest prover (`flockProveH`) at the reference shape:

* **`accepts_of_trace`**: for an honest trace (`TraceHonest`) at the reference shape whose batching sumcheck
  synchronises with a zero terminal (`BatchSyncsAt … (fun _ ↦ 0)`), a proof `proveWith` returns is accepted by
  `Deployment.verifierWithH`: the verifier's run on the prover's stream accepts (`runWithH_syncs`,
  `runWithH_accepts`: the counts' checks and the terminal are zero) with the prover's three point claims and Flock's
  matrices' claim, and the five `PCS_OPEN` calls accept WHIR's honest openings (`pcsOpen_honest`, at `27, 27, 24, 28,
  28` variables: each claim's value is its stack's extension at its point, `streamValues`; each point has its stack's
  variables, `StreamFacts.points`, `flockProve_matrixPoint`; each root is the committed tree's,
  `rootRead_digestScalars`, `rootOf_digestScalars`, the setup's the deployment's, `setupStackOf_honestTrace`);
* **`coreAccepts_of`**: `CoreAccepts D flockProveH`, given the batch's hypothesis at the prover's state
  (`hbatch`, `CoreBatch.lean`'s `batchSyncsAt_front`) and the stacks' sizes, the bad events moved from the staged
  challenges to the prover's state by `front_challenges`;
* **`coreFailsOnlyAtPow`**: `proveWith` fails only at an opening (`proveWith_eq_none`, every commitment has a
  claim, `claims_complete`);
* **`badFpCard_reference`**: at most `2^24 − 1` bad `β` per `α` (one per divided tuple, `Mapping.fpOf_eq`, at most
  `capBound reference = 10,878,976` of them, `Mapping.capBound_reference`).
-/

open UniStatement LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover

namespace UniComplete.Core

open ProverRun

/-- A root's halves are read back as they are (`digestScalars` leaves the top limbs zero). -/
theorem rootRead_digestScalars (d : Digest) : rootRead (digestScalars d) = digestScalars d := by
  have h := digestOfScalars_digestScalars d
  unfold digestOfScalars at h
  split at h
  · rename_i hc
    exact rootRead_of hc.1 hc.2
  · exact absurd h (by simp)

theorem commitReal_tree (H : List UInt8 → Digest) (c : Commitment) (vars : ℕ) (stack : Array K) :
    (commitReal (m := Id) H c vars stack).tree = E2ECompleteness.commitWithH (m := Id) H vars stack := rfl

theorem commitReal_halves (H : List UInt8 → Digest) (c : Commitment) (vars : ℕ) (stack : Array K) :
    (commitReal (m := Id) H c vars stack).halves =
      digestScalars (E2ECompleteness.commitWithH (m := Id) H vars stack).root := rfl

/-- Three claims on `C1`, `C2`, the setup, in order. -/
theorem claims_shape (l : List (Commitment × List E × E)) (h : l.map (·.1) = [.c1, .c2, .setup]) :
    ∃ pt1 v1 pt2 v2 pt3 v3, l = [(.c1, pt1, v1), (.c2, pt2, v2), (.setup, pt3, v3)] := by
  rcases l with _ | ⟨⟨a, pt1, v1⟩, _ | ⟨⟨b, pt2, v2⟩, _ | ⟨⟨c, pt3, v3⟩, _ | _⟩⟩⟩ <;> simp at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨_, _, _, _, _, _, rfl⟩

theorem ref_word_c1 : layoutWordVars ((layoutWords reference).getD 0 []) = 27 := by rw [ref_word]; rfl
theorem ref_word_c2 : layoutWordVars ((layoutWords reference).getD 1 []) = 27 := by rw [ref_word]; rfl
theorem ref_word_setup : layoutWordVars ((layoutWords reference).getD 2 []) = 24 := by rw [ref_word]; rfl
theorem ref_word_a0 : layoutWordVars ((layoutWords reference).getD 3 []) = 28 := by rw [ref_word]; rfl
theorem ref_word_b0 : layoutWordVars ((layoutWords reference).getD 4 []) = 28 := by rw [ref_word]; rfl

set_option maxHeartbeats 1000000 in
/-- **The honest proof is accepted**, for an honest trace at the reference shape (its setup the deployment's) whose
batching sumcheck synchronises with a zero terminal. -/
theorem accepts_of_trace (D : Deployment) (H : List UInt8 → Digest) (F : KeccakState → KeccakState)
    (input : Vector UInt8 32) (tr : Trace) (π : UniProof) (hon : TraceHonest tr) (href : tr.shape = reference)
    (hshape : tr.shape = D.shape) (hpi : tr.publicInput = input.toList)
    (hsetup : setupStackOf tr = setupStack D.prog D.shape)
    (hbatch : BatchSyncsAt H (commitReal (m := Id) H) (FlockP.flockProve (m := Id) (Pure.pure ∘ H))
      (.flock flockMain) tr (proverSeed H D.programIv tr) (fun _ ↦ 0))
    (hs1 : (c1Stack tr).size = 2 ^ 27)
    (hs2 : ∀ alphas beta gamma, (c2DataOf tr (eqKernel alphas) beta gamma).stack.size = 2 ^ 27)
    (hs3 : (setupStackOf tr).size = 2 ^ 24)
    (hπ : proveWith (m := Id) H F PcsQuotient.nonceFuel (FlockP.flockProve (m := Id) (Pure.pure ∘ H))
      (.flock flockMain) D.programIv tr = some π) :
    Deployment.verifierWithH (m := Id) H F D (setupTreesWithH (m := Id) H F D).roots input π = true := by
  have hflock : FlockSyncs H (FlockP.flockProve (m := Id) (Pure.pure ∘ H))
      (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) flockMain tr.qflock :=
    FlockP.flockSyncs H _ flockMain tr.qflock (by decide)
  have htrees : setupTreesWithH (m := Id) H F D = setupTreesOf (m := Id) H tr := by
    unfold setupTreesWithH setupTreesOf
    rw [hsetup, hshape]
  have hiv : Deployment.ivWithH (m := Id) H D (setupTreesOf (m := Id) H tr).roots =
      contractIvOf (m := Id) H tr.shape D.programIv (setupTreesOf (m := Id) H tr).roots := by
    rw [hshape]; rfl
  have hC2 := c2ColumnsHonest_of_traceHonest hon
  -- The prover's proof.
  obtain ⟨p1, p2, p3, pa, pb, h1, h2, h3, ha, hb, rfl⟩ := (proveWith_eq_some H F _ _ _ _ _ π).mp hπ
  -- The verifier's run on the prover's stream.
  obtain ⟨R, hrunR, hopR, hmatR, hrootR⟩ := runWithH_syncs H (commitReal (m := Id) H)
    (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) tr
    (contractIvOf (m := Id) H tr.shape D.programIv (setupTreesOf (m := Id) H tr).roots) hon.valid hon.rowsFit hflock
    (fun _ ↦ 0) hbatch
  have hacc := runWithH_accepts H (commitReal (m := Id) H) (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) tr
    (contractIvOf (m := Id) H tr.shape D.programIv (setupTreesOf (m := Id) H tr).roots) hon.valid hon.rowsFit hflock
    (fun _ ↦ 0) hbatch rfl
  have hrun_eq : proverRun H (commitReal (m := Id) H) (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) (.flock flockMain)
      tr (contractIvOf (m := Id) H tr.shape D.programIv (setupTreesOf (m := Id) H tr).roots) =
      streamRun H (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) (.flock flockMain) D.programIv tr := rfl
  rw [hrun_eq] at hrunR hopR hmatR hrootR hacc
  have hf : StreamFacts (commitReal (m := Id) H) (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) (.flock flockMain) tr
      (streamRun H (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) (.flock flockMain) D.programIv tr).1 :=
    streamRun_facts H (commitReal (m := Id) H) _ _ tr _
  have hv : StreamValues (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) (.flock flockMain) tr
      (streamRun H (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) (.flock flockMain) D.programIv tr).1 :=
    streamValues H (commitReal (m := Id) H) _ _ tr _
  generalize (streamRun H (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) (.flock flockMain) D.programIv tr).1 = out
    at hf hv h1 h2 h3 ha hb hopR hmatR hrootR hrunR hacc ⊢
  -- The claims and the matrices' claim.
  obtain ⟨pt1, v1, pt2, v2, pt3, v3, hcl⟩ := claims_shape _ hf.claims_fst
  obtain ⟨mc, hmc⟩ := Option.isSome_iff_exists.mp (hf.flock_some flockMain rfl)
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
  obtain ⟨hma, hmb, w, r, hr, hmpt⟩ := hv.matrices hC2 flockMain rfl mc hmc
  rw [href, ref_rounds] at hr
  have hlm : mc.point.length = 28 := by
    rw [hmpt]
    exact flockProve_matrixPoint (Pure.pure ∘ H) _ flockMain tr.qflock w (by decide)
      (Nat.le_add_right blake2sR1csLogSize _) r (by rw [hr]; decide) 0 0
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
  rw [hmc] at ha hb
  have ha' : E2ECompleteness.proveOpeningWithH (m := Id) H F PcsQuotient.nonceFuel (plainLayout 28)
      (E2ECompleteness.commitWithH (m := Id) H 28 (flockMatrixStack true)) (flockMatrixStack true)
      [⟨mc.point, stackEval (flockMatrixStack true) mc.point⟩] = some pa := by
    have : E2ECompleteness.proveOpeningWithH (m := Id) H F PcsQuotient.nonceFuel
        (plainLayout (layoutWordVars ((layoutWords tr.shape).getD 3 [])))
        (E2ECompleteness.commitWithH (m := Id) H 28 (flockMatrixStack true)) (flockMatrixStack true)
        [⟨mc.point, mc.a⟩] = some pa := ha
    simp only [href, ref_word_a0, hma] at this
    exact this
  have hb' : E2ECompleteness.proveOpeningWithH (m := Id) H F PcsQuotient.nonceFuel (plainLayout 28)
      (E2ECompleteness.commitWithH (m := Id) H 28 (flockMatrixStack false)) (flockMatrixStack false)
      [⟨mc.point, stackEval (flockMatrixStack false) mc.point⟩] = some pb := by
    have : E2ECompleteness.proveOpeningWithH (m := Id) H F PcsQuotient.nonceFuel
        (plainLayout (layoutWordVars ((layoutWords tr.shape).getD 4 [])))
        (E2ECompleteness.commitWithH (m := Id) H 28 (flockMatrixStack false)) (flockMatrixStack false)
        [⟨mc.point, mc.b⟩] = some pb := hb
    simp only [href, ref_word_b0, hmb] at this
    exact this
  -- WHIR accepts each.
  have a1 := pcsOpen_honest H F _ (vars := 27) (by norm_num) (by norm_num) _ hs1 pt1 hl1 ho1'
  have a2 := pcsOpen_honest H F _ (vars := 27) (by norm_num) (by norm_num) _ hs2' pt2 hl2 ho2'
  have a3 := pcsOpen_honest H F _ (vars := 24) (by norm_num) (by norm_num) _ hs3 pt3 hl3 ho3'
  have aa := pcsOpen_honest H F _ (vars := 28) (by norm_num) (by norm_num) _ (FlockP.flockMatrixStack_size true)
    mc.point hlm ha'
  have ab := pcsOpen_honest H F _ (vars := 28) (by norm_num) (by norm_num) _ (FlockP.flockMatrixStack_size false)
    mc.point hlm hb'
  -- The verifier.
  show verifyWithH (m := Id) H F D.shape (Deployment.ivWithH (m := Id) H D (setupTreesWithH (m := Id) H F D).roots)
    (setupTreesWithH (m := Id) H F D).roots input _ = true
  rw [htrees, hiv]
  have hD : D.shape = reference := hshape.symm.trans href
  refine verifyWithH_of_calls H F D.shape _ _ input _ _ R pt1 pt2 pt3 v1 v2 v3 mc ?_ hacc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← hshape, ← hpi]; rfl
  · rw [hrunR]
  · rw [hopR, hcl]; rfl
  · rw [hmatR, hmc]
  · simp only [hrootR, hf.c1, commitReal_halves, rootRead_digestScalars, rootOf_digestScalars, hD, ref_word_c1,
      href, ref_c1Layout, hv1]
    exact a1
  · simp only [hrootR, hf.c2, commitReal_halves, rootRead_digestScalars, rootOf_digestScalars, hD, ref_word_c2,
      href, ref_c2Layout, hv2]
    exact a2
  · simp only [hD, ref_word_setup, hv3, SetupTrees.roots, setupTrees_bytecode, href, ref_setupLayout]
    exact a3
  · simp only [hD, ref_word_a0, hma, SetupTrees.roots, setupTrees_a0]
    exact aa
  · simp only [hD, ref_word_b0, hmb, SetupTrees.roots, setupTrees_b0]
    exact ab

end UniComplete.Core

/-- info: 'UniComplete.Core.accepts_of_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Core.accepts_of_trace
