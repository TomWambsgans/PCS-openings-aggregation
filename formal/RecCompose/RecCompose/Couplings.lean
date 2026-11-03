-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCompose.Part1
import RecCompose.Part2
import RecCompose.Rpm

/-!
# The soundness couplings

* `experimentsAgree`: the end-to-end experiment is π2's, the calls dropped (the monad laws).
* `hazardCoupling`: the hazard adversary built from π2's (`hazardAdversary`) makes `A`'s queries, and its transcript,
  logged, is `A`'s (`Rpm.logged_post`); for every fixed permutation (`Rpm.prEvent_le_of_perm`) the two games agree up to
  the contract, which the hazard event does not read.
* `pi1Coupling`: the π1 adversary built from π2's (`pi1Adversary`) likewise; for every fixed permutation and every
  prefix (the setup, `A`'s output and transcript) on which π2's extractor outputs a stream `s` accepted with the
  contract's π1 openings `ops` off the hazard, the contract accepts at most as often as its three π1 openings do
  (`contract_le_openSeq`: the contract's acceptance needs all six; `loop_le`), and those are π1-rec3's verifier at
  Keccak-f[1600] with its openings over `π` (**`Pi1OpeningsAgree`**, named below); `CallsPure` makes the contract's π1
  openings the calldata's `pi1OpsOf`.
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec Common
open scoped ENNReal

/-- **The end-to-end experiment is π2's, the calls dropped.** -/
theorem experimentsAgree (D : RecDeployment) : ExperimentsAgree D := by
  intro A
  unfold recSoundnessExperiment recSoundnessExperiment2
  rw [Rpm.runWithRandomPermutation_map]
  congr 1
  simp only [map_bind, RecDeployment.verifierWith, bind_assoc]
  refine bind_congr fun trees ↦ bind_congr fun p ↦ ?_
  obtain ⟨z, T⟩ := p
  refine bind_congr fun r ↦ ?_
  simp

/-- The derived adversaries' continuation after `A`. -/
theorem hazardAdversary_eq (D : RecDeployment) (A : RecAdversary) (roots : RecSetupRoots)
    (evals : List (List UInt8 × Digest)) :
    hazardAdversary D A roots evals = (simulateQ loggedOracles (A roots)).run [] >>= fun p ↦
      pure (p.1.1, (recExtractor2 D roots p.1.1 evals p.2 p.1.2).getD #[]) := by
  unfold hazardAdversary
  refine bind_congr fun p ↦ ?_
  obtain ⟨z, T⟩ := p
  rfl

/-- **The hazard coupling.** -/
theorem hazardCoupling (D : RecDeployment) : HazardCoupling D := by
  intro A Q hQ
  refine ⟨fun roots evals ↦ ?_, ?_⟩
  · rw [hazardAdversary_eq]
    exact Rpm.queryCost_post _ _ _ (fun _ ↦ rfl) Q (hQ roots)
  unfold recSoundnessExperiment2 pi1HazardExperiment
  refine Rpm.prEvent_le_of_perm _ _ _ _ fun π ↦ ?_
  simp only [simulateQ_bind]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun trees ↦ ?_
  rw [hazardAdversary_eq, Rpm.logged_post _ _ _ (fun _ ↦ rfl), simulateQ_map, bind_map_left]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun p ↦ ?_
  obtain ⟨z, T⟩ := p
  simp only [simulateQ_pure]
  refine prEvent_bind_le_of_forall_le _ _ _ fun r ↦ ?_
  obtain ⟨acc, calls⟩ := r
  simp only
  refine Rpm.prEvent_pure_le _ _ _ _ fun h1 ↦ ?_
  obtain ⟨s, hs, hz⟩ := h1
  simp only at hs ⊢
  rw [hs]
  exact hz

/-! ## π1-rec3's coupling -/

/-- **A π1 opening as the contract's `PCS_OPEN` opens it**: by its layout word's registered opener. -/
def openAt {m : Type → Type} [Monad m] (F : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState)
    (reg : List (List UInt8 × Opener)) (o : Pi1Opening) (p : Compile.Proof) : m Bool :=
  match reg.lookup o.2.1 with
  | none => pure false
  | some (.pi1 vars) => UniStatement.pcsOpenWith F vars o.1 o.2.2 p
  | some (.pi2 L) => PcsQuotient.openingWith F L o.1 o.2.2 p

/-- **The contract's three π1 openings** `ops`, with the recursive proof's three π1 opening proofs. -/
def openSeq {m : Type → Type} [Monad m] (F : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState)
    (reg : List (List UInt8 × Opener)) (ops : List Pi1Opening) (proof : RecProof) : m Bool := do
  let b1 ← openAt F reg (ops.getD 0 default) proof.c1
  let b2 ← openAt F reg (ops.getD 1 default) proof.c2
  let b3 ← openAt F reg (ops.getD 2 default) proof.f
  return b1 && b2 && b3

/-- **Named hypothesis: π1-rec3's verifier at Keccak-f[1600] is the contract's three π1 openings**, on a stream `s`
π1-rec3's graph accepts with the contract's π1 openings `ops` (read off the calldata) off the merge hazard, the graph
being π1-rec3's verifier there: `pi1KeccakVerifierWith` (π1's run over Keccak-f[1600], then `C1`, `C2`, the setup opened
over `π`) on π1's proof of `s` with the recursive proof's three π1 opening proofs is, as a computation, the contract's
three π1 `PCS_OPEN` calls `openSeq` of `ops`.

Why it holds, and what its proof needs (open, `lean-rec-compose`): off the hazard `Pi1GraphIsVerifier` makes the graph's
outputs `UniStatement.verifierOutputsWith`'s at the reference shape (`D.pi1.shape = reference`), so the run accepts and
the graph's calls are `UniStatement.pcsCalls`' words; their decoding (`decodePi1Call`, which `Pi1GraphAccepts` compares
with `ops`) gives back the verifier's openings: `elementOfWord ∘ elementWord`, `countOfWord ∘ numberWord`,
`rootOfWord ∘ rootWord = rootOf` (`C1`, `C2`), and the contract's setup root word `rootWordOfBytes (digestBytes F)`
naming `F` (`digestOfBytes32 ∘ digestBytes`); the verifier's openings at π1-rec3 are three point claims in
`commitments` order, no matrix call; and π1's layout words are registered with π1's opener at their variables (no π2
layout word equals one: their first bytes, `"pi2"` and the shape's). -/
def Pi1OpeningsAgree (D : RecDeployment) : Prop :=
  RecGraph.Pi1.Pi1GraphIsVerifier →
    ∀ (roots : RecSetupRoots) (input : Vector UInt8 32) (proof : RecProof) (s : Array UInt8)
      (ops : List Pi1Opening),
      pi1OpsOf D roots input proof.stream = some ops →
      Pi1GraphAccepts (D.pi1IvAt roots.pi1) input s ops →
      ¬ RecGraph.MergeHazard LeanVM.Semantics.keccakF1600 (D.pi1IvAt roots.pi1) input.toList s →
        pi1KeccakVerifierWith queryPermutation D.pi1 roots.pi1 input (proof.pi1Proof s) =
          openSeq queryPermutation (registryAt D roots) ops proof

theorem lookup_of_decodeWith (reg : List (List UInt8 × Opener)) (w : List (List UInt8))
    (x : Digest × Opener × List PcsQuotient.Claim) (h : decodeWith reg w = some x) :
    reg.lookup (w.getD 1 []) = some x.2.1 := by
  unfold decodeWith at h
  cases hw0 : w.head? with
  | none => simp [hw0] at h
  | some root =>
    cases hw1 : w[1]? with
    | none => simp [hw0, hw1] at h
    | some layout =>
      cases hl : reg.lookup layout with
      | none => simp [hw0, hw1, hl] at h
      | some op =>
        simp only [hw0, hw1, hl, Option.bind_eq_bind, Option.bind_some] at h
        have hg : w.getD 1 [] = layout := by rw [List.getD_eq_getElem?_getD, hw1, Option.getD_some]
        rw [hg, hl]
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨a, -, k, -, h⟩ := h
        split_ifs at h with hc
        · simp at h
        · obtain ⟨cl, -, hx⟩ := Option.bind_eq_some_iff.mp h
          cases hx
          rfl

/-- A call the registry decodes is opened as its decoded opening. -/
theorem pcsOpenAt_eq {m : Type → Type} [Monad m] (F : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState)
    (reg : List (List UInt8 × Opener)) (w : List (List UInt8)) (p : Compile.Proof)
    (x : Digest × Opener × List PcsQuotient.Claim) (h : decodeWith reg w = some x) :
    pcsOpenAt F reg w p = openAt F reg (x.1, w.getD 1 [], x.2.2) p := by
  have hl := lookup_of_decodeWith reg w x h
  unfold pcsOpenAt openAt
  rw [h]
  simp only [hl]
  obtain ⟨root, op, claims⟩ := x
  cases op <;> rfl

/-- **The contract's six openings accept at most as often as its three π1 openings**, over any oracle answers. -/
theorem loop_le (I : QueryImpl RandomPermutationOracles ProbComp) (reg : List (List UInt8 × Opener))
    (calls : List (List (List UInt8))) (hlen : calls.length = 6) (proof : RecProof) (ops : List Pi1Opening)
    (hops : contractPi1Openings reg calls = some ops) :
    Pr{let x ← simulateQ I (do
        let s ← forIn (calls.zip proof.openings) true fun x s ↦ do
          let b ← pcsOpenAt queryPermutation reg x.1 x.2
          pure (ForInStep.yield (s && b))
        pure (s, calls))}[x.1 = true ∧ contractPi1Openings reg x.2 = some ops] ≤
      Pr{let b ← simulateQ I (openSeq queryPermutation reg ops proof)}[b = true] := by
  match calls, hlen with
  | [w0, w1, w2, w3, w4, w5], _ =>
    simp only [contractPi1Openings, List.take, List.mapM_cons, List.mapM_nil, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.pure_def, Option.some.injEq] at hops
    obtain ⟨_, ⟨x0, h0, rfl⟩, _, ⟨_, ⟨x1, h1, rfl⟩, _, ⟨_, ⟨x2, h2, rfl⟩, _, rfl, rfl⟩, rfl⟩, rfl⟩ := hops
    simp only [RecProof.openings, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons, List.forIn_nil,
      bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure, pcsOpenAt_eq _ _ _ _ _ h0, pcsOpenAt_eq _ _ _ _ _ h1,
      pcsOpenAt_eq _ _ _ _ _ h2, openSeq, List.getD_cons_zero, List.getD_cons_succ]
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun b0 ↦ ?_
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun b1 ↦ ?_
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun b2 ↦ ?_
    refine prEvent_bind_le_of_forall_le _ _ _ fun b3 ↦ ?_
    refine prEvent_bind_le_of_forall_le _ _ _ fun b4 ↦ ?_
    refine prEvent_bind_le_of_forall_le _ _ _ fun b5 ↦ ?_
    refine Rpm.prEvent_pure_le _ _ _ _ fun h ↦ ?_
    simp only [Bool.and_eq_true] at h ⊢
    tauto

/-- A pure event that fails has probability at most anything. -/
theorem prEvent_pure_le_of_not {α : Type} (a : α) (p : α → Prop) (h : ¬ p a) (x : ℝ≥0∞) :
    Pr{let y ← (pure a : ProbComp α)}[p y] ≤ x := by
  classical
  rw [prEvent_pure]
  simp [h]

/-- **The contract accepts with π1 openings `ops` at most as often as those openings accept**, over any oracle
answers. -/
theorem contract_le_openSeq (I : QueryImpl RandomPermutationOracles ProbComp) (D : RecDeployment)
    (roots : RecSetupRoots) (input : Vector UInt8 32) (proof : RecProof) (ops : List Pi1Opening) :
    Pr{let x ← simulateQ I (D.contractWith queryPermutation roots input proof)}[
      x.1 = true ∧ contractPi1Openings (registryAt D roots) x.2 = some ops] ≤
    Pr{let b ← simulateQ I (openSeq queryPermutation (registryAt D roots) ops proof)}[b = true] := by
  unfold RecDeployment.contractWith
  simp only [simulateQ_bind]
  refine prEvent_bind_le_of_forall_le _ _ _ fun iv ↦ ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun o ↦ ?_
  split
  · rw [simulateQ_pure]
    exact prEvent_pure_le_of_not _ _ (fun h ↦ Bool.false_ne_true h.1) _
  · rename_i r hr
    split_ifs with h1 h2
    · rw [simulateQ_pure]
      exact prEvent_pure_le_of_not _ _ (fun h ↦ Bool.false_ne_true h.1) _
    · rw [simulateQ_pure]
      exact prEvent_pure_le_of_not _ _ (fun h ↦ Bool.false_ne_true h.1) _
    · rcases Classical.em (contractPi1Openings (registryAt D roots) (pcsCalls (D.circuitAt roots.pi1).circuit
          (pi1CallsWith D.pi1Calls roots.pi1.bytecode) (digestBytes roots.pi2) proof.stream r) = some ops)
        with hops | hops
      · exact loop_le I _ _ (not_not.mp h2) proof ops hops
      · rw [simulateQ_bind]
        refine prEvent_bind_le_of_forall_le _ _ _ fun b ↦ ?_
        rw [simulateQ_pure]
        exact prEvent_pure_le_of_not _ _ (fun h ↦ hops h.2) _

/-- The π1 adversary's continuation after `A`. -/
theorem pi1Adversary_eq (D : RecDeployment) (A : RecAdversary) (roots : RecSetupRoots)
    (evals : List (List UInt8 × Digest)) :
    pi1Adversary D A roots evals = (simulateQ loggedOracles (A roots)).run [] >>= fun p ↦
      pure (p.1.1, p.1.2.pi1Proof ((recExtractor2 D roots p.1.1 evals p.2 p.1.2).getD #[])) := by
  unfold pi1Adversary
  refine bind_congr fun p ↦ ?_
  obtain ⟨z, T⟩ := p
  rfl

/-- The contract's π1 openings are the calldata's, on the outcome. -/
def CallsGood (D : RecDeployment) (z : RecOutcome2) : Prop :=
  acc z = true → ∃ ops, pi1OpsOf D (rts z) (inp z) (prf z).stream = some ops ∧
    contractPi1Openings (registryAt D (rts z)) (cls z) = some ops

/-- **π1-rec3's coupling.** -/
theorem pi1Coupling (D : RecDeployment) (hpure : CallsPure D) (hagree : Pi1OpeningsAgree D) : Pi1Coupling D := by
  intro hgv A Q hQ
  refine ⟨fun roots evals ↦ ?_, ?_⟩
  · rw [pi1Adversary_eq]
    exact Rpm.queryCost_post _ _ _ (fun _ ↦ rfl) Q (hQ roots)
  refine (prEvent_mono_of_support _ _ (fun z ↦ Pi1Event D z ∧ CallsGood D z)
    fun z hz h ↦ ⟨h, fun ha ↦ hpure A z hz ha⟩).trans ?_
  unfold recSoundnessExperiment2 pi1KeccakSoundnessExperiment
  refine Rpm.prEvent_le_of_perm _ _ _ _ fun π ↦ ?_
  simp only [simulateQ_bind]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun trees ↦ ?_
  rw [pi1Adversary_eq, Rpm.logged_post _ _ _ (fun _ ↦ rfl), simulateQ_map, bind_map_left]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun p ↦ ?_
  obtain ⟨z, T⟩ := p
  simp only
  rcases Classical.em (∃ s ops, recExtractor2 D trees.roots z.1 trees.evaluations T z.2 = some s ∧
      pi1OpsOf D trees.roots z.1 z.2.stream = some ops ∧
      Pi1GraphAccepts (D.pi1IvAt trees.roots.pi1) z.1 s ops ∧
      ¬ RecGraph.MergeHazard LeanVM.Semantics.keccakF1600 (D.pi1IvAt trees.roots.pi1) z.1.toList s ∧
      ¬ ∃ q, UniStatement.uniExtractor D.pi1 z.1 trees.evaluations T (z.2.pi1Proof s) = some q ∧
        D.pi1.Relation (z.2.pi1Proof s).rows z.1 q) with hC | hC
  · obtain ⟨s, ops, hs, hops, hga, hz, hno⟩ := hC
    have hV := hagree hgv trees.roots z.1 z.2 s ops hops hga hz
    rw [hs, Option.getD_some]
    simp only [simulateQ_pure, bind_pure_comp, prEvent_map]
    refine (prEvent_mono _ _ _ ?_).trans ((contract_le_openSeq _ D trees.roots z.1 z.2 ops).trans ?_)
    · rintro x ⟨⟨ha, -⟩, hg⟩
      obtain ⟨ops', hops', hcon'⟩ := hg ha
      refine ⟨ha, ?_⟩
      have e : ops' = ops := by
        change pi1OpsOf D trees.roots z.1 z.2.stream = some ops' at hops'
        rw [hops] at hops'
        exact (Option.some.inj hops').symm
      subst e
      exact hcon'
    · rw [← hV]
      exact prEvent_mono _ _ _ fun b hb ↦ ⟨hb, hno⟩
  · refine prEvent_bind_le_of_forall_le _ _ _ fun r ↦ ?_
    obtain ⟨acc, calls⟩ := r
    refine prEvent_pure_le_of_not _ _ ?_ _
    rintro ⟨⟨ha, s, ops, hs, hops, hga, hz, hno⟩, hg⟩
    obtain ⟨ops', hops', hcon'⟩ := hg ha
    have : ops' = ops := by
      simp only at hops hcon'
      rw [hops] at hcon'
      exact (Option.some.inj hcon').symm
    subst this
    exact hC ⟨s, ops', hs, hops', hga, hz, hno⟩

end RecCompose

/-- info: 'RecCompose.experimentsAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.experimentsAgree

/-- info: 'RecCompose.hazardCoupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.hazardCoupling

/-- info: 'RecCompose.pi1Coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi1Coupling
