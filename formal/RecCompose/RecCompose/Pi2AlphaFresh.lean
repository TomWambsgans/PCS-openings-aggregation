-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. `α`'s freshness at π2's staged run (`Pi2ProbStaged`'s
-- `pi2Staged`, `stageA`) for π1-rec3's honest prover, from `Pi2AlphaLen` (the census before `σ`'s hash),
-- `Pi2AlphaChain` (the chain from `σ` to `α`) and `Pi2AlphaSupport` (the graph's verdict on every outcome); uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two calls,
-- their lazy random oracles, the block cost.
import RecCompose.Pi2AlphaLen
import RecCompose.Pi2AlphaSupport
import RecCompose.Pi2Witness

/-!
# `α`'s input is fresh at π1-rec3's honest prover

**`alphaFresh_p1k`**: in the two-call random-oracle model, after stage A of π2's staged run at π1-rec3's honest prover,
`α`'s input is cached while π1-rec3's graph accepted (`GAcc`) with probability at most

  `alphaBound = 4 · (2 · setupR + 2^47 + 3 · gOpen + 4) / 2^256 ≤ 2^-204` (**`alphaBound_le`**).

The proof: with `GAcc`, `α`'s input is the writer's `536` bytes (`gAcc_length`), so it suffices to bound their being
cached (**`prA_le`**). Stage A is the setup, π1-rec3's prover, its graph, the setup again (every input shorter than
`2^26` bytes: `Pi2AlphaLen`, at most `2 · setupR + 2^47 + 3 · gOpen` hashed inputs), then π2's IV, its seed and `W`'s
tree: `Pi2AlphaChain.chain_le` from `σ`'s `2^26` bytes, not cached.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2Sim

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM
open LeanVM.Protocol.Compile.Rom (implH implF simulateQ_queryH simulateQ_queryF)
open E2ECompleteness (ro runAt Cache HashOK cache_of_hashOK length_digestBytes)
open UniComplete (Wr WrM Morph)
open UniComplete.Prob.TFresh (HC hc_of_qc CacheBound cacheBound_empty cacheBound_run take_digestBytes)
open Pi2S Pi2K Pi2P Pi2E Pi2G Pi2G.Cost2
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## The cache's invariant before `σ` -/

/-- **Every cached hash input is shorter than `σ`'s.** -/
def CacheShort (c : Cache) : Prop := ∀ m, c (.inl m) ≠ none → Pi2A.Short m

theorem cacheShort_empty : CacheShort ∅ := fun _ h ↦ absurd rfl h

/-- A run of a computation hashing short inputs keeps the cache short, and adds at most its hash count. -/
theorem inv_run {α : Type} {X : OracleComp KeccakCalls α} {n : ℕ} (hX : HashOK Pi2A.Short X) (hn : HC X n)
    {c : Cache} {K : ℕ} (hc : CacheShort c) (hK : CacheBound c K) {z : α × Cache}
    (hz : z ∈ support ((simulateQ ro X).run c)) : CacheShort z.2 ∧ CacheBound z.2 (K + n) :=
  ⟨fun m hm ↦ (cache_of_hashOK hX c hz m hm).elim (hc m) id, cacheBound_run hn hK hz⟩

/-! ## `pre2`'s writer on every outcome -/

theorem runAt_pre2 (Ht : List UInt8 → Digest) (Ft : KeccakState → KeccakState) (G : RecPiop.Circuit E)
    (reads : List Read) (values : List PublicValue) (w : ℕ → K) (w0 : Wr) :
    runAt Ht Ft ((pre2 callKeccak256 G reads values w).run w0) =
      Id.run ((pre2 (m := Id) (Pure.pure ∘ Ht) G reads values w).run w0) := by
  have h := wr_pre2 (Morph.sim (LeanVM.Protocol.Compile.totalImpl Ht Ft)) callKeccak256 G reads values w
  rw [Morph.sim_H] at h
  have h2 := congrArg (fun x ↦ StateT.run x w0) h
  simp only [Morph.wr_run] at h2
  exact h2

/-! ## `W`'s tree -/

/-- A Merkle tree of rows of `64` words hashes `512`-byte leaves and `64`-byte nodes: nothing of `536` bytes. -/
theorem hashOK_buildTree536 (height : ℕ) (word : LeanVM.Protocol.Compile.Word) (hw : ∀ p, (word p).length = 64) :
    HashOK (fun m ↦ m.length ≠ 536) (LeanVM.Prover.buildTreeWithHash callKeccak256 height word) := by
  unfold LeanVM.Prover.buildTreeWithHash
  refine E2ECompleteness.HashOK.bind ?_ fun leaves ↦ E2ECompleteness.HashOK.bind ?_ fun _ ↦
    E2ECompleteness.HashOK.pure _ _
  · unfold LeanVM.Prover.leafDigestsWithHash
    refine E2ECompleteness.HashOK.arrayMapM _ (fun i ↦ E2ECompleteness.hashOK_callKeccak256 ?_) _
    show _ ≠ 536
    rw [E2ECompleteness.length_flatMap_kBytes, hw]
    norm_num
  · suffices h : ∀ k (level : Array Digest),
        HashOK (fun m ↦ m.length ≠ 536) (LeanVM.Prover.levelsWithHash callKeccak256 k level) from h _ _
    intro k
    induction k with
    | zero => intro level; exact E2ECompleteness.HashOK.pure _ _
    | succ k ih =>
      intro level
      unfold LeanVM.Prover.levelsWithHash
      refine E2ECompleteness.HashOK.bind ?_ fun up ↦ E2ECompleteness.HashOK.bind (ih up) fun _ ↦
        E2ECompleteness.HashOK.pure _ _
      unfold LeanVM.Prover.parentsWithHash
      refine E2ECompleteness.HashOK.arrayMapM _ (fun j ↦ E2ECompleteness.hashOK_callKeccak256 ?_) _
      show _ ≠ 536
      rw [List.length_append, length_digestBytes, length_digestBytes]
      norm_num

theorem hashOK_commitWithH536 (μ : ℕ) (stack : Array K) :
    HashOK (fun m ↦ m.length ≠ 536) (E2ECompleteness.commitWithH callKeccak256 μ stack) :=
  hashOK_buildTree536 _ _ (E2ECompleteness.length_stackWordFast μ 1 stack)

/-! ## Stage A -/

/-- `α`'s input before `fixLen`. -/
abbrev rawInp (a : StA) : List UInt8 := UniComplete.Prob.tInput a.wr

theorem rawInp_start : (UniComplete.Prob.tInput (Wr.start default)).length = 32 := by
  simp [UniComplete.Prob.tInput, Wr.start, length_digestBytes]

set_option maxHeartbeats 1600000 in
/-- **Stage A caches its writer's `536`-byte input** with probability at most `4 · (K + 4) / 2^256`, `K` the hash count
before `σ`, for a π1 prover hashing short inputs. -/
theorem prA_le {D : RecDeployment} (hD : D.Real) (hg : GraphsAgree) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : OracleComp KeccakCalls (Option UniStatement.UniProof)) (input : Vector UInt8 32) {K₂ : ℕ}
    (hpS : HashOK Pi2A.Short P1k) (hpC : HC P1k K₂) :
    Pr{let p ← (simulateQ ro (stageA callKeccak256 callKeccakF1600 D C Fa P1k input)).run ∅}[
      p.2 (.inl (rawInp p.1)) ≠ none ∧ (rawInp p.1).length = 536] ≤
      4 * (((0 + setupR + K₂ + 3 * gOpen + setupR + 4 : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  classical
  have hsS := Pi2A.hashOK_setupTreesWithH2 D
  have hsC : HC (Pi2H.setupTreesWithH callKeccak256 callKeccakF1600 D) setupR :=
    hc_of_qc ((qc_setupTreesWithH2 hD).mono (setup2_le hD))
  unfold stageA
  rw [simulateQ_bind, StateT.run_bind]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p₀ hp₀ ↦ ?_
  obtain ⟨hs₀, hb₀⟩ := inv_run hsS hsC cacheShort_empty cacheBound_empty hp₀
  rw [simulateQ_bind, StateT.run_bind]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p₁ hp₁ ↦ ?_
  obtain ⟨hs₁, hb₁⟩ := inv_run hpS hpC hs₀ hb₀ hp₁
  obtain ⟨o, c₁⟩ := p₁
  rcases o with _ | p1
  · -- π1's prover returned none: the writer is the start's.
    refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hev ↦ ?_) zero_le
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    have := hev.2
    rw [rawInp, rawInp_start] at this
    exact absurd this (by norm_num)
  · dsimp only
    rw [simulateQ_bind, StateT.run_bind]
    refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p₂ hp₂ ↦ ?_
    obtain ⟨hs₂, hb₂⟩ := inv_run (Pi2A.hashOK_graph hg D _ input p1)
      (hc_of_qc (qc_pi1GraphVerifierWithH hg D _ input p1)) hs₁ hb₁ hp₂
    rw [simulateQ_bind, StateT.run_bind]
    refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p₃ hp₃ ↦ ?_
    obtain ⟨hs₃, hb₃⟩ := inv_run hsS hsC hs₂ hb₂ hp₃
    obtain ⟨tr, c₃⟩ := p₃
    dsimp only at hs₃ hb₃ ⊢
    have hc : (D.circuitAt tr.roots.pi1).circuit = Data.circuit := by rw [RecDeployment.circuitAt, hD.1]
    have hn : (D.circuitAt tr.roots.pi1).n = 2 ^ 24 := by rw [Pi2Circuit.n, hc]; rfl
    rcases hl : layoutWords (D.circuitAt tr.roots.pi1).circuit.logN with ⟨w, q, s⟩
    have hwqs : w.length + q.length + s.length = 96 := by
      have := congrArg (fun x : List UInt8 × List UInt8 × List UInt8 ↦ x.1.length + x.2.1.length + x.2.2.length) hl
      simp only [layoutWords, length_layoutWord] at this
      omega
    simp only [Pi2H.ivOfH, Pi2H.digestWithH, Pi2H.ivWithH, hl, bind_assoc, pure_bind]
    have hσ : ((List.range (D.circuitAt tr.roots.pi1).n).flatMap fun i ↦
        (le64 ((D.circuitAt tr.roots.pi1).sigma i)).take 4).length = 2 ^ 26 := by
      rw [length_flatMap_const _ 4 (fun i ↦ by simp [length_le64]), List.length_range, hn]
      norm_num
    have hκ : ((List.range (D.circuitAt tr.roots.pi1).n).flatMap fun i ↦
        le64 ((D.circuitAt tr.roots.pi1).kappa i).lane.toNat).length = 2 ^ 27 := by
      rw [length_flatMap_const _ 8 (fun i ↦ length_le64 _), List.length_range, hn]
      norm_num
    have h0 : c₃ (.inl ((List.range (D.circuitAt tr.roots.pi1).n).flatMap fun i ↦
        (le64 ((D.circuitAt tr.roots.pi1).sigma i)).take 4)) = none := by
      by_contra h
      have := hs₃ _ h
      unfold Pi2A.Short at this
      omega
    refine (Pi2C.chain_le _ _
      (fun σ κ ↦ (D.circuitAt tr.roots.pi1).circuit.encoding ++ digestBytes σ ++ digestBytes κ)
      (fun d ↦ ivTag ++ D.pi1IvAt tr.roots.pi1 ++ digestBytes tr.roots.pi2 ++ digestBytes d ++ w ++ q ++ s)
      (fun iv ↦ RecStatement.name ++ digestBytes iv ++ input.toList)
      (by rw [hκ]; norm_num) (by rw [hσ]; norm_num) (fun σ κ ↦ ⟨?_, ?_⟩) (fun d ↦ ⟨?_, ?_⟩) (fun iv ↦ ⟨?_, ?_⟩)
      _ rawInp ?_ ?_ c₃ hb₃ h0).trans ?_
    · simp only [List.length_append, hc, encoding_length, length_digestBytes]
    · rw [hc, List.append_assoc, List.drop_left' encoding_length]
      exact take_digestBytes _ _
    · simp only [List.length_append, ivTag_length, RecDeployment.pi1IvAt, length_pi1Iv, length_digestBytes]
      omega
    · have e : ivTag ++ D.pi1IvAt tr.roots.pi1 ++ digestBytes tr.roots.pi2 ++ digestBytes d ++ w ++ q ++ s =
          (ivTag ++ D.pi1IvAt tr.roots.pi1 ++ digestBytes tr.roots.pi2) ++ (digestBytes d ++ (w ++ q ++ s)) := by
        simp only [List.append_assoc]
      rw [e, List.drop_left' (by simp only [List.length_append, ivTag_length, RecDeployment.pi1IvAt, length_pi1Iv,
        length_digestBytes])]
      exact take_digestBytes _ _
    · simp only [List.length_append, name_length, length_digestBytes, Vector.length_toList]
    · rw [List.append_assoc, List.drop_left' name_length]
      exact take_digestBytes _ _
    · -- `W`'s tree hashes nothing of `536` bytes.
      intro seed
      refine E2ECompleteness.HashOK.bind ?_ fun x ↦ ?_
      · obtain ⟨s', h, -, -⟩ := run_sendPublic ((D.circuitAt tr.roots.pi1).circuit.reads.zip
          (pi2Choice D C Fa tr.roots input p1.stream).1) (Wr.start seed)
        unfold pre2
        simp only [StateT.run_bind, h, pure_bind, StateT.run_lift, bind_assoc, run_sendRoot2, StateT.run_pure]
        exact E2ECompleteness.HashOK.bind (hashOK_commitWithH536 _ _) fun _ ↦ E2ECompleteness.HashOK.pure _ _
      · obtain ⟨_, _⟩ := x
        exact E2ECompleteness.HashOK.pure _ _
    · -- the input begins with the seed.
      intro seed c z hz _
      have e := Pi2C.runAt_read hz
      rw [← e]
      generalize Pi2C.readH z.2 = Ht
      generalize Pi2C.readF z.2 = Ft
      unfold runAt
      rw [simulateQ_bind]
      generalize hy : simulateQ (LeanVM.Protocol.Compile.totalImpl Ht Ft)
        ((pre2 callKeccak256 (C.G tr.roots) (D.circuitAt tr.roots.pi1).circuit.reads
          (pi2Choice D C Fa tr.roots input p1.stream).1 (pi2Choice D C Fa tr.roots input p1.stream).2).run
            (Wr.start seed)) = y
      obtain ⟨ws, wr⟩ := y
      have hwr : wr = (Id.run ((pre2 (m := Id) (Pure.pure ∘ Ht) (C.G tr.roots) (D.circuitAt tr.roots.pi1).circuit.reads
          (pi2Choice D C Fa tr.roots input p1.stream).1 (pi2Choice D C Fa tr.roots input p1.stream).2).run
            (Wr.start seed))).2 := by
        rw [← runAt_pre2 Ht Ft]
        unfold runAt
        rw [hy]
      obtain ⟨hh, hw⟩ := pre2_writer (C.G tr.roots) (D.circuitAt tr.roots.pi1).circuit.reads
        (pi2Choice D C Fa tr.roots input p1.stream).1 (pi2Choice D C Fa tr.roots input p1.stream).2 Ht (Wr.start seed)
      show (UniComplete.Prob.tInput wr).take 32 = digestBytes seed
      rw [hwr, hw, tInput_start_append]
      exact take_digestBytes _ _
    · exact le_rfl

/-! ## At π1-rec3's honest prover -/

/-- **`α`'s bound**: four links, each at most the hashed inputs before `σ` (the setup twice, π1-rec3's prover, its graph)
and four, over `2^256`. -/
noncomputable def alphaBound : ℝ≥0∞ := 4 * (((0 + setupR + 2 ^ 47 + 3 * gOpen + setupR + 4 : ℕ) : ℝ≥0∞) / 2 ^ 256)

theorem alphaK_le : 0 + setupR + 2 ^ 47 + 3 * gOpen + setupR + 4 ≤ 2 ^ 50 := by
  unfold setupR gOpen
  norm_num [E2ECompleteness.Cost.treeCost, E2ECompleteness.Cost.vOpen, LeanVM.Protocol.Verifier.whirBound]

/-- **`α`'s bound in bits**: at most `2^-204`. -/
theorem alphaBound_le : alphaBound ≤ (2 : ℝ≥0∞)⁻¹ ^ 204 := by
  unfold alphaBound
  have h1 : ((0 + setupR + 2 ^ 47 + 3 * gOpen + setupR + 4 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ (2 : ℝ≥0∞)⁻¹ ^ 206 := by
    calc ((0 + setupR + 2 ^ 47 + 3 * gOpen + setupR + 4 : ℕ) : ℝ≥0∞) / 2 ^ 256
        ≤ ((2 ^ 50 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (206 + 50) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
          gcongr
          exact_mod_cast alphaK_le
      _ = (2 : ℝ≥0∞)⁻¹ ^ 206 := by
          rw [Nat.cast_pow, Nat.cast_ofNat]
          exact E2ECompleteness.two_pow_mul_inv_pow 50 206
  calc 4 * (((0 + setupR + 2 ^ 47 + 3 * gOpen + setupR + 4 : ℕ) : ℝ≥0∞) / 2 ^ 256)
      ≤ 2 ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ (204 + 2) := by
        rw [show (4 : ℝ≥0∞) = 2 ^ 2 by norm_num]
        gcongr
    _ = (2 : ℝ≥0∞)⁻¹ ^ 204 := E2ECompleteness.two_pow_mul_inv_pow 2 204

theorem alphaBound_le201 : alphaBound ≤ (2 : ℝ≥0∞)⁻¹ ^ 201 :=
  alphaBound_le.trans (E2ECompleteness.inv_pow_le_inv_pow (by norm_num))

/-- **`α`'s input is fresh while the graph accepts** at π1-rec3's honest prover: in the two-call random-oracle model,
after stage A of π2's staged run, `α`'s input is cached and π1-rec3's graph accepted with probability at most
`alphaBound ≤ 2^-204`. -/
theorem alphaFresh_p1k {D : RecDeployment} (hD : D.Real) (hg : GraphsAgree) (C : Pi2Circuits D)
    (hchk : Pi2ViewChecked C) (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows)
    (hfit : D.pi1.shape.RowsFit rows) (hrel : D.pi1.HonestRelation rows input q) :
    Pr{let p ← (simulateQ ro (pi2Staged D C (pi2Facts hD C hchk) (p1k D input rows q) input).A).run ∅}[
      p.2 (.inl ((pi2Staged D C (pi2Facts hD C hchk) (p1k D input rows q) input).inp p.1)) ≠ none ∧ GAcc p.1] ≤
      alphaBound := by
  have hwc := Pi2W.pi2WitnessComplete hD C hchk
  refine (prEvent_mono_of_support _ _ (fun p ↦ p.2 (.inl (rawInp p.1)) ≠ none ∧ (rawInp p.1).length = 536)
    fun p hp hev ↦ ?_).trans ?_
  · have hl := gAcc_length C (pi2Facts hD C hchk) input hD hwc _ hp hev.2
    have e : (pi2Staged D C (pi2Facts hD C hchk) (p1k D input rows q) input).inp p.1 = rawInp p.1 := by
      show fixLen 536 (UniComplete.Prob.tInput p.1.wr) = _
      unfold fixLen
      simp only [hl, ↓reduceIte]
    have h1 := hev.1
    rw [e] at h1
    exact ⟨h1, hl⟩
  · exact prA_le hD hg C _ _ input (Pi2A.hashOK_p1k hD input rows q hfit hrel)
      (hc_of_qc (UniComplete.Rec3.proverCost3_flockProve3H D.pi1 hD.2.2.1
        (by rw [hD.2.2.2.1, programIv_length]; norm_num) input rows q hfit hrel))

end RecCompose.Pi2Sim

/-- info: 'RecCompose.Pi2Sim.prA_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.prA_le

/-- info: 'RecCompose.Pi2Sim.alphaFresh_p1k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.alphaFresh_p1k

/-- info: 'RecCompose.Pi2Sim.alphaBound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.alphaBound_le
