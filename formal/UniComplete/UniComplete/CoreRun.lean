-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.ProverRun
import UniComplete.FlockProverMain
import UniComplete.ProbHyp
import UniComplete.SyncVerifier

/-!
# The honest prover's run, read off for the verifier

What the end composition (`Core.lean`) reads off the honest prover's stream (`proveStreamWith` at `Id`), beyond
`ProverRun.StreamFacts`:

* **`streamValues`** (a `StreamValues`): every point claim's value is its stack's multilinear extension at its point
  (`stackEval`, what WHIR's honest opening `pcsOpen_honest` needs), and the matrices' claim carries `Â0`, `B̂0` at its
  point, the point Flock's pending reduction's at the batch's point;
* **`flockProve_matrixPoint`**: Flock's honest prover (`FlockP.flockProve`) leaves a matrices' claim of `28`
  coordinates (`k + 6` of the batch's point, `6 − k` of `row_low`, `8 + 8` of `chi_in`, `chi_in'`);
* **the prover's challenges are the staged ones** (`front_challenges`): at the prover's seed (`proverSeed`), the
  state when the batching sumcheck starts (`frontOf`, `SyncVerifier.lean`) has the bus challenges
  `Prob.proverChallenges` and Flock's point and `t` of `Prob.proverTChallenge`, the values the bad events
  (`BadFp`, `BadT`) are stated at. Through `frontFrom` (`frontOf` from `γ` on, `frontOf_eq` by `rfl`) and the five
  samples from the stream's prefix (`samples_prefix`).
-/

open UniStatement LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover

namespace UniComplete.Core

open ProverRun

/-! ## The values of the claims -/

/-- **The claims' values** in the stream's output `out`: each point claim's value is its stack's extension at its
point; with Flock, the matrices' claim carries `Â0`, `B̂0` at its point, which is Flock's pending reduction's at a
point of the batch's rounds. -/
structure StreamValues (flock : FlockProver Id) (blake2s : Blake2s) (tr : Trace) (out : CoreOut) : Prop where
  values : ∀ x ∈ out.claims, x.2.2 = stackEval (stacksOf out.c1.1 out.c2.1 out.setup x.1) x.2.1
  c2stack : ∃ alphas beta gamma, out.c2.1 = (c2DataOf tr (eqKernel alphas) beta gamma).stack
  matrices : C2ColumnsHonest tr → ∀ v, blake2s = .flock v → ∀ mc, out.matrices = some mc →
    mc.a = stackEval (flockMatrixStack true) mc.point ∧ mc.b = stackEval (flockMatrixStack false) mc.point ∧
    ∃ (w : Wr) (r : List E), r.length = ((layouts tr.shape tr.shape.c2Columns).map (·.2.vars)).foldl max 0 ∧
      mc.point = (((flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) v tr.qflock).run w).1.pending.matrixClaim
        r 0 0).point

set_option maxHeartbeats 1000000 in
theorem streamValues (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed)
    (flock : FlockProver Id) (blake2s : Blake2s) (tr : Trace) (w0 : Wr) :
    StreamValues flock blake2s tr ((proveStreamWith (m := Id) H commit flock blake2s tr).run w0).1 := by
  unfold proveStreamWith
  refine peel fun _ s0 _ ↦ ?_
  refine peel_lift ?_
  refine peel fun _ s1 _ ↦ ?_
  refine peel fun alphas s2 _ ↦ ?_
  refine peel fun beta s3 _ ↦ ?_
  refine peel fun gamma s4 _ ↦ ?_
  cases blake2s with
  | flock v =>
    refine peel_map fun fo s5 hfo ↦ ?_
    dsimp only
    refine peel_lift ?_
    refine peel fun _ s6 _ ↦ ?_
    refine peel fun t s7 _ ↦ ?_
    refine peel fun _ s8 _ ↦ ?_
    refine peel fun rho s9 _ ↦ ?_
    refine peel fun lambda s10 _ ↦ ?_
    refine peel fun r s11 hr ↦ ?_
    refine peel fun _ s12 _ ↦ ?_
    have hpend := ProverRun.atTOf_pending tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t (some fo)
    split
    · rename_i p snd hp
      refine peel fun _ s13 _ ↦ ?_
      refine peel_pure_bind ?_
      refine peel_get ?_
      refine peel_pure ?_
      have hl := congrArg (fun p ↦ p.1.length) hr
      simp only [batchRounds_point, List.length_nil, Nat.zero_add] at hl
      refine ⟨?_, ⟨alphas, beta, gamma, rfl⟩, ?_⟩
      · intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨⟨c, snd⟩, -, rfl⟩ := hx
        cases c <;> rfl
      · intro hC2 v' hv
        rw [show v' = v from (Blake2s.flock.inj hv).symm]
        intro mc hmc
        unfold C2ColumnsHonest at hC2
        rw [hp] at hpend
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpend hmc
        subst hmc
        refine ⟨rfl, rfl, s4, r, by rw [← hl, hC2], ?_⟩
        have hfo' : fo = ((flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) v tr.qflock).run s4).1 := by
          rw [hfo]
        rw [hpend.1, hfo']
        rfl
    · rename_i hp
      rw [hp] at hpend
      exact absurd hpend (by simp)
  | omitted =>
    refine peel_pure_bind ?_
    dsimp only
    refine peel_lift ?_
    refine peel fun _ s6 _ ↦ ?_
    refine peel fun t s7 _ ↦ ?_
    refine peel fun _ s8 _ ↦ ?_
    refine peel fun rho s9 _ ↦ ?_
    refine peel fun lambda s10 _ ↦ ?_
    refine peel fun r s11 hr ↦ ?_
    refine peel fun _ s12 _ ↦ ?_
    have hpend := ProverRun.atTOf_pending tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t none
    split
    · rename_i p snd hp
      rw [hp] at hpend
      exact absurd hpend (by simp)
    · rename_i hp
      refine peel_pure_bind ?_
      refine peel_get ?_
      refine peel_pure ?_
      refine ⟨?_, ⟨alphas, beta, gamma, rfl⟩, fun _ _ hv ↦ nomatch hv⟩
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨⟨c, snd⟩, -, rfl⟩ := hx
      cases c <;> rfl

/-! ## Flock's matrices' point -/

/-- **Flock's honest prover leaves a matrices' claim of `28` coordinates**, at a batch point of at least `k + 6`
coordinates: `ρ` (`k`), `row_low` (`6 − k`), `chi_in` (`8`), `σ` (`6`), `chi_in'` (`8`). -/
theorem flockProve_matrixPoint (H : List UInt8 → Id Digest) (logN : ℕ) (variant : Flock.Variant) (q : Array K)
    (w : Wr) (hk : variant.skip ≤ 6) (hN : 14 ≤ logN) (r : List E) (hr : variant.skip + 6 ≤ r.length) (a b : E) :
    (((FlockP.flockProve H logN variant q).run w).1.pending.matrixClaim r a b).point.length = 28 := by
  obtain ⟨frs, e, hfrs, hout⟩ := FlockP.flockProve_eq H logN variant q w
  obtain ⟨h1, h2, h3, -⟩ := FlockP.frontW_shape H logN variant q w hk hN
  rw [← hfrs] at h1 h2 h3
  rw [hout]
  simp only [FlockP.assemble, Flock.Pending.matrixClaim, Flock.Pending.rounds, FlockP.pending_k,
    FlockP.pending_rowLow, FlockP.pending_chiIn, FlockP.pending_chiInPrime, List.length_append, List.length_take,
    List.length_drop, h1, h2, h3, Flock.packing]
  omega

/-! ## The prover's challenges -/

section Front

variable (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed) (flock : FlockProver Id)

/-- **`frontOf` from `γ` on**: given `C1`'s commitment, the bus challenges and the writer after them. -/
def frontFrom (blake2s : Blake2s) (tr : Trace) (committed1 : Committed) (alphas : List E) (beta : E) (w4 : Wr) :
    FrontOut × Wr :=
  let shape := tr.shape
  let stack1 := c1Stack tr
  let gamma := (Wr.sampled H w4).1
  let w5 := (Wr.sampled H w4).2
  let logN := blake2sR1csLogSize + shape.heights.getD opBlake2s 0
  let flockOut : Option FlockOut := match blake2s with
    | .flock variant => some ((flock logN variant tr.qflock).run w5).1
    | .omitted => none
  let w6 := match blake2s with
    | .flock variant => ((flock logN variant tr.qflock).run w5).2
    | .omitted => w5
  let c2 := c2DataOf tr (eqKernel alphas) beta gamma
  let committed2 : Committed := commit .c2 (((layoutsOf shape).lookup .c2).getD default).vars c2.stack
  let w7 := w6.append (rootWord committed2.halves)
  let t := (Wr.sampled H w7).1
  let w8 := (Wr.sampled H w7).2
  let a := atTOf tr c2 alphas beta gamma t flockOut
  let w9 := w8.append (a.values.flatMap scalarWire)
  let rho := (Wr.sampled H w9).1
  let w10 := (Wr.sampled H w9).2
  let combined := commitments.filterMap fun c ↦ (combine a.relations c rho).map (c, ·)
  let stackLayouts := layouts shape a.c2Columns
  (⟨stack1, committed1, alphas, beta, gamma, flockOut, c2, committed2, t, a, rho, combined, stackLayouts,
    setupStackOf tr⟩, w10)

/-- **`frontOf` is `frontFrom`** after the stream's prefix and the five bus challenges. -/
theorem frontOf_eq (blake2s : Blake2s) (tr : Trace) (w0 : Wr) :
    frontOf H commit flock blake2s tr w0 =
      frontFrom H commit flock blake2s tr (commit .c1 (c1Layout tr.shape).vars (c1Stack tr))
        ((samplesW (m := Id) (Pure.pure ∘ H) 4).run
          ((w0.append (tr.rows.flatMap fun n ↦ integerWire n 4)).append
            (rootWord (commit .c1 (c1Layout tr.shape).vars (c1Stack tr)).halves))).1
        (Wr.sampled H ((samplesW (m := Id) (Pure.pure ∘ H) 4).run
          ((w0.append (tr.rows.flatMap fun n ↦ integerWire n 4)).append
            (rootWord (commit .c1 (c1Layout tr.shape).vars (c1Stack tr)).halves))).2).1
        (Wr.sampled H ((samplesW (m := Id) (Pure.pure ∘ H) 4).run
          ((w0.append (tr.rows.flatMap fun n ↦ integerWire n 4)).append
            (rootWord (commit .c1 (c1Layout tr.shape).vars (c1Stack tr)).halves))).2).2 := rfl

end Front

/-- A sample at a writer that has absorbed its stream hashes the state alone. -/
theorem sampled_absorbed (H : List UInt8 → Digest) (s : Array UInt8) (st : Digest) (ch : Array E) :
    Wr.sampled H ⟨s, s.size, st, ch⟩ =
      (Prob.chal (H (digestBytes st)), ⟨s, s.size, H (digestBytes st), ch.push (Prob.chal (H (digestBytes st)))⟩) := by
  simp [Wr.sampled, Prob.chal]

/-- The first sample from the stream's prefix. -/
theorem sampled_start (H : List UInt8 → Digest) (s : Array UInt8) (st : Digest) :
    Wr.sampled H ⟨s, 0, st, #[]⟩ =
      (Prob.chal (H (digestBytes st ++ (s.extract 0 s.size).toList)),
        ⟨s, s.size, H (digestBytes st ++ (s.extract 0 s.size).toList),
          #[Prob.chal (H (digestBytes st ++ (s.extract 0 s.size).toList))]⟩) := rfl

/-- **The five bus challenges from the stream's prefix**: `s₁ = H(seed ‖ prefix)`, `s_{k+1} = H(s_k)`; the writer
after them is `Prob.writerAfter`. -/
theorem samples_prefix (H : List UInt8 → Digest) (rows : List ℕ) (c1 : LeanVM.Prover.Tree) (seed : Digest)
    (s₁ s₂ s₃ s₄ s₅ : Digest)
    (h₁ : s₁ = H (digestBytes seed ++
      ((Prob.prefixStream rows c1).extract 0 (Prob.prefixStream rows c1).size).toList))
    (h₂ : s₂ = H (digestBytes s₁)) (h₃ : s₃ = H (digestBytes s₂)) (h₄ : s₄ = H (digestBytes s₃))
    (h₅ : s₅ = H (digestBytes s₄)) :
    ((samplesW (m := Id) (Pure.pure ∘ H) 4).run ⟨Prob.prefixStream rows c1, 0, seed, #[]⟩).1 =
        [Prob.chal s₁, Prob.chal s₂, Prob.chal s₃, Prob.chal s₄] ∧
      Wr.sampled H ((samplesW (m := Id) (Pure.pure ∘ H) 4).run ⟨Prob.prefixStream rows c1, 0, seed, #[]⟩).2 =
        (Prob.chal s₅, Prob.writerAfter rows c1 s₁ s₂ s₃ s₄ s₅) := by
  subst h₁ h₂ h₃ h₄ h₅
  have h4 : (samplesW (m := Id) (Pure.pure ∘ H) 4).run ⟨Prob.prefixStream rows c1, 0, seed, #[]⟩ =
      ([(Wr.sampled H ⟨Prob.prefixStream rows c1, 0, seed, #[]⟩).1,
        (Wr.sampled H (Wr.sampled H ⟨Prob.prefixStream rows c1, 0, seed, #[]⟩).2).1,
        (Wr.sampled H (Wr.sampled H (Wr.sampled H ⟨Prob.prefixStream rows c1, 0, seed, #[]⟩).2).2).1,
        (Wr.sampled H (Wr.sampled H (Wr.sampled H (Wr.sampled H
          ⟨Prob.prefixStream rows c1, 0, seed, #[]⟩).2).2).2).1],
        (Wr.sampled H (Wr.sampled H (Wr.sampled H (Wr.sampled H
          ⟨Prob.prefixStream rows c1, 0, seed, #[]⟩).2).2).2).2) := rfl
  rw [h4]
  refine ⟨?_, ?_⟩ <;> (simp only [sampled_start, sampled_absorbed]; try rfl)

/-- **The prover's challenges are the staged ones**: at the prover's seed, the state when the batching sumcheck
starts has the bus challenges `proverChallenges`, Flock's point and `t` of `proverTChallenge`. -/
theorem front_challenges (H : List UInt8 → Digest) (flock : FlockProver Id) (D : Deployment)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    (frontOf H (commitReal (m := Id) H) flock (.flock flockMain)
        (honestTrace D input rows q) (Wr.start (proverSeed H D.programIv (honestTrace D input rows q)))).1.alphas =
        (Prob.proverChallenges H D input rows q).1 ∧
      (frontOf H (commitReal (m := Id) H) flock (.flock flockMain)
        (honestTrace D input rows q) (Wr.start (proverSeed H D.programIv (honestTrace D input rows q)))).1.beta =
        (Prob.proverChallenges H D input rows q).2 ∧
      (frontOf H (commitReal (m := Id) H) flock (.flock flockMain)
        (honestTrace D input rows q)
          (Wr.start (proverSeed H D.programIv (honestTrace D input rows q)))).1.flockOut.map (·.point) =
        some (Prob.proverTChallenge H flock D input rows q).1 ∧
      (frontOf H (commitReal (m := Id) H) flock (.flock flockMain)
        (honestTrace D input rows q) (Wr.start (proverSeed H D.programIv (honestTrace D input rows q)))).1.t =
        (Prob.proverTChallenge H flock D input rows q).2 := by
  have hw2 : ((Wr.start (proverSeed H D.programIv (honestTrace D input rows q))).append
        ((honestTrace D input rows q).rows.flatMap fun n ↦ integerWire n 4)).append
      (rootWord (commitReal (m := Id) H .c1 (c1Layout (honestTrace D input rows q).shape).vars
        (c1Stack (honestTrace D input rows q))).halves) =
      ⟨Prob.prefixStream rows (E2ECompleteness.commitWithH (m := Id) H
          (c1Layout (honestTrace D input rows q).shape).vars (c1Stack (honestTrace D input rows q))), 0,
        proverSeed H D.programIv (honestTrace D input rows q), #[]⟩ := rfl
  obtain ⟨hα, hβ⟩ := samples_prefix H rows (E2ECompleteness.commitWithH (m := Id) H
      (c1Layout (honestTrace D input rows q).shape).vars (c1Stack (honestTrace D input rows q)))
    (proverSeed H D.programIv (honestTrace D input rows q)) _ _ _ _ _ rfl rfl rfl rfl rfl
  rw [frontOf_eq, hw2, hα, hβ]
  exact ⟨rfl, rfl, rfl, rfl⟩

end UniComplete.Core

/-- info: 'UniComplete.Core.streamValues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Core.streamValues

/-- info: 'UniComplete.Core.flockProve_matrixPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Core.flockProve_matrixPoint

/-- info: 'UniComplete.Core.front_challenges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Core.front_challenges
