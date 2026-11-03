-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The contract is `formal/RecStatement`'s
-- (`Security.lean`: `contractWith`, `pcsOpenAt`, `pi1OpsOf`); π2's honest prover `RecCompose.Pi2Prover`'s; the joint
-- run `Pi2CompleteSync`'s, the calls' decodings `Pi2CompleteCalls`', the honest openings `Pi2Whir`'s.
import RecCompose.Pi2CompleteSync
import RecCompose.Pi2CompleteCalls
import RecCompose.Couplings
import RecCompose.CallsPure
import RecCompose.Bridge

/-!
# The contract accepts π2's honest proof off the bad challenges

**`contract_accepts`** (the core of π2's completeness, at one permutation): over a pure permutation `F` (Keccak-256 the
sponge over it, `Hk`), the contract (`RecDeployment.contractWith`) accepts the proof whose stream π2's honest prover
writes (`proverOut`, at the contract's IV) and whose six openings are π1's three and the honest prover's three, when

* π2's arithmetic on the prover's inputs passes (`all ≠ 0`) and its four claims hold on the prover's stacks
  (`Pi2ClaimsHold`): the algebra, off the bad challenges;
* the three WHIR openings exist (no proof of work failed);
* the contract's three π1 openings (`pi1OpsOf`, read off the calldata) are accepted with π1's opening proofs (`openSeq`).

The steps: π2's verifier reads the prover's stream back (`runWith_honest`), so its arithmetic is the prover's and its
check passes; the calls are six; `W`'s, the setup's and `Q`'s calls decode to the roots the prover committed (the
stream's root words, `rootOfWord_rootWord_digestScalars`; the setup's the deployment's), π2's layouts and the prover's
claims (`decodeWith_claims`), and WHIR accepts the honest openings of true claims (`pi2Open_honest`); π1's three are
`openSeq`'s (`pcsOpenAt_eq`, the calls read only the public data: `pcsCalls_take`, `callWord_congr`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2K

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open Pi2S Pi2C

/-! ## The stream's offsets -/

theorem foldl_rootsAt (reads : List Read) : ∀ acc : List ℕ × ℕ,
    (reads.foldl (fun (acc : List ℕ × ℕ) rd ↦ (if rd = .root then acc.1 ++ [acc.2] else acc.1, acc.2 + rd.bytes))
        acc).1.length = acc.1.length + (reads.filter (· = .root)).length ∧
      (reads.foldl (fun (acc : List ℕ × ℕ) rd ↦ (if rd = .root then acc.1 ++ [acc.2] else acc.1, acc.2 + rd.bytes))
        acc).2 = acc.2 + (reads.map Read.bytes).sum := by
  induction reads with
  | nil => intro acc; simp
  | cons rd rs ih =>
    intro acc
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih _
    refine ⟨?_, ?_⟩
    · rw [h1]
      by_cases hr : rd = .root
      · simp [hr]; omega
      · simp [hr]
    · rw [h2]; simp; omega

/-- **`W`'s and `Q`'s roots' offsets**: after the public data. -/
theorem rootsAt_offsets (reads : List Read) :
    (rootsAt reads).getD (rootReads reads) 0 = (reads.map Read.bytes).sum ∧
      (rootsAt reads).getD (rootReads reads + 1) 0 = (reads.map Read.bytes).sum + 32 := by
  obtain ⟨h1, h2⟩ := foldl_rootsAt reads ([], 0)
  unfold rootsAt rootReads
  simp only at h1 h2 ⊢
  rw [List.length_nil, zero_add] at h1
  rw [zero_add] at h2
  constructor
  · rw [← h1, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, h2]; rfl
  · rw [← h1, List.getD_append_right _ _ _ _ (by omega), show _ + 1 - _ = 1 by omega, h2]; rfl

theorem publicWire_length : ∀ (reads : List Read) (values : List PublicValue), List.Forall₂ ReadMatch reads values →
    (publicWire (reads.zip values)).length = (reads.map Read.bytes).sum
  | [], [], .nil => rfl
  | .root :: rs, .root b :: vs, .cons _ h => by
    simp [publicWire, publicWire_length rs vs h, Read.bytes]
  | .scalar :: rs, .scalar x :: vs, .cons _ h => by
    simp [publicWire, publicWire_length rs vs h, Read.bytes]
  | .integer _ :: _, _ :: _, .cons hm _ => by cases hm
  | .root :: _, .integer _ :: _, .cons hm _ => by cases hm
  | .root :: _, .scalar _ :: _, .cons hm _ => by cases hm
  | .scalar :: _, .integer _ :: _, .cons hm _ => by cases hm
  | .scalar :: _, .root _ :: _, .cons hm _ => by cases hm

/-! ## The arithmetic's points -/

theorem run_points_length (S : CoreSpec E) (hN : S.logN = 24) (hR : S.logRow = 4) (inp : Inputs E) :
    (S.run inp).witnessPoint.length = 24 ∧ (S.run inp).setupPoint.length = 25 ∧
      (S.run inp).quotientPoint.length = 29 ∧ (S.run inp).sumPoint.length = 29 := by
  simp [CoreSpec.run, digitsList, hN, hR]

/-! ## Loops -/

theorem forIn_and_true {γ : Type} (f : γ → Bool → Id (ForInStep Bool)) (g : γ → Bool)
    (hf : ∀ x b, f x b = pure (ForInStep.yield (b && g x))) :
    ∀ (l : List γ) (b : Bool), (∀ x ∈ l, g x = true) → Id.run (forIn l b f) = b
  | [], b, _ => rfl
  | x :: l, b, h => by
    rw [List.forIn_cons, hf, pure_bind, h x List.mem_cons_self, Bool.and_true]
    exact forIn_and_true f g hf l b fun y hy ↦ h y (List.mem_cons_of_mem _ hy)

/-- A postcondition of a computation in `Id` from its value. -/
theorem holds_id_of {α : Type} {X : Id α} {P : α → Prop} (h : P X.run) : Holds X P := by
  unfold Holds
  show ((X.run, P X.run) : α × Prop) = (X.run, True)
  rw [eq_true h]

/-! ## The core -/

theorem varsW : (layoutsOf 24).1.vars = 24 := rfl
theorem varsS : (layoutsOf 24).2.2.vars = 25 := rfl
theorem varsQ : (layoutsOf 24).2.1.vars = 29 := rfl

/-- The contract's IV at a pure permutation. -/
abbrev ivOf (D : RecDeployment) (F : KeccakState → Id KeccakState) (roots : RecSetupRoots) : List UInt8 :=
  Id.run (D.ivWith F roots)

/-- **π2's honest prover's output** at the setup's roots, the contract's IV. -/
abbrev outOf (D : RecDeployment) (F : KeccakState → Id KeccakState) (Hk : List UInt8 → Digest) (roots : RecSetupRoots)
    (G : RecPiop.Circuit E) (input : Vector UInt8 32) (values : List PublicValue) (w : ℕ → K) : Pi2Out :=
  proverOut Hk G (D.circuitAt roots.pi1).circuit (D.circuitAt roots.pi1).setupStack (ivOf D F roots) input.toList
    values w

/-- **The contract accepts π2's honest proof**, at a pure permutation, off the bad challenges and proofs of work, π1's
three openings accepted. -/
theorem contract_accepts (D : RecDeployment) (F : KeccakState → Id KeccakState) (Hk : List UInt8 → Digest)
    (hk : keccak256With (m := Id) F = Pure.pure ∘ Hk) (roots : RecSetupRoots) (G : RecPiop.Circuit E)
    (hview : (D.circuitAt roots.pi1).circuit = Data.circuit) (hGN : G.logN = 24) (hrow : Data.circuit.logRow = G.logW)
    (hcalls3 : D.pi1Calls.length = 3)
    (hroot2 : roots.pi2 = (E2ECompleteness.commitWithH (m := Id) (Pure.pure ∘ Hk) (layoutsOf 24).2.2.logN
      (D.circuitAt roots.pi1).setupStack).root)
    (input : Vector UInt8 32) (values : List PublicValue) (w : ℕ → K)
    (hmatch : List.Forall₂ ReadMatch Data.circuit.reads values) (fuel : ℕ) (c1 c2 cf pW pS pQ : Compile.Proof)
    (halg : ((Spec.of (D.circuitAt roots.pi1).circuit).core.run (outOf D F Hk roots G input values w).inputs).all ≠ 0 ∧
      Pi2ClaimsHold D roots (outOf D F Hk roots G input values w).inputs
        (fun j ↦ (outOf D F Hk roots G input values w).wStack.getD j 0)
        (fun j ↦ (outOf D F Hk roots G input values w).qStack.getD j 0))
    (hW : E2ECompleteness.proveOpeningWithH (m := Id) (Pure.pure ∘ Hk) F fuel (layoutsOf 24).1
      (outOf D F Hk roots G input values w).wTree (outOf D F Hk roots G input values w).wStack
      [⟨((Spec.of (D.circuitAt roots.pi1).circuit).core.run (outOf D F Hk roots G input values w).inputs).witnessPoint,
        ((Spec.of (D.circuitAt roots.pi1).circuit).core.run (outOf D F Hk roots G input values w).inputs).fold⟩] =
      some pW)
    (hS : E2ECompleteness.proveOpeningWithH (m := Id) (Pure.pure ∘ Hk) F fuel (layoutsOf 24).2.2
      (E2ECompleteness.commitWithH (m := Id) (Pure.pure ∘ Hk) (layoutsOf 24).2.2.logN (D.circuitAt roots.pi1).setupStack)
      (D.circuitAt roots.pi1).setupStack
      [⟨((Spec.of (D.circuitAt roots.pi1).circuit).core.run (outOf D F Hk roots G input values w).inputs).setupPoint,
        (outOf D F Hk roots G input values w).inputs.ξ⟩] = some pS)
    (hQ : E2ECompleteness.proveOpeningWithH (m := Id) (Pure.pure ∘ Hk) F fuel (layoutsOf 24).2.1
      (outOf D F Hk roots G input values w).qTree (outOf D F Hk roots G input values w).qStack
      [⟨((Spec.of (D.circuitAt roots.pi1).circuit).core.run (outOf D F Hk roots G input values w).inputs).quotientPoint,
        ((Spec.of (D.circuitAt roots.pi1).circuit).core.run (outOf D F Hk roots G input values w).inputs).quotientValue⟩,
       ⟨((Spec.of (D.circuitAt roots.pi1).circuit).core.run (outOf D F Hk roots G input values w).inputs).sumPoint,
        ((Spec.of (D.circuitAt roots.pi1).circuit).core.run (outOf D F Hk roots G input values w).inputs).sumValue⟩] =
      some pQ)
    (hpi1 : ∃ ops, pi1OpsOf D roots input (outOf D F Hk roots G input values w).stream = some ops ∧
      Id.run (openSeq F (registryOf D.pi1.shape 24) ops
        ⟨(outOf D F Hk roots G input values w).stream, c1, c2, cf, pW, pS, pQ⟩) = true) :
    (Id.run (D.contractWith F roots input ⟨(outOf D F Hk roots G input values w).stream, c1, c2, cf, pW, pS, pQ⟩)).1 =
      true := by
  have hlogN : (D.circuitAt roots.pi1).circuit.logN = 24 := by rw [hview]; rfl
  obtain ⟨r, hr, hinp, hout, hstr, hwt, hqt⟩ := runWith_honest F Hk hk G (D.circuitAt roots.pi1).circuit
    (D.circuitAt roots.pi1).setupStack (ivOf D F roots) input.toList values w (by rw [hview]; exact hmatch)
    (by rw [hview]; exact hrow)
  generalize hout_def : outOf D F Hk roots G input values w = out at halg hW hS hQ hpi1 ⊢
  have hr' : (RecStatement.runWith (m := Id) F (Spec.of (D.circuitAt roots.pi1).circuit) (ivOf D F roots) input.toList
      out.stream).result = .ok r := by rw [← hout_def]; exact hr
  have hinp' : r.inputs = out.inputs := by rw [← hout_def]; exact hinp
  have hstr' : out.stream.toList = publicWire ((D.circuitAt roots.pi1).circuit.reads.zip values) ++
      UniStatement.rootWord (digestScalars out.wTree.root) ++ UniStatement.rootWord (digestScalars out.qTree.root) ++
      (out.inputs.a ++ [out.inputs.ξ]).flatMap UniComplete.scalarWire := by rw [← hout_def]; exact hstr
  have hwt' : out.wTree = E2ECompleteness.commitWithH (m := Id) (Pure.pure ∘ Hk) (layoutsOf 24).1.logN out.wStack := by
    rw [← hout_def, ← hGN]; exact hwt
  have hqt' : out.qTree = E2ECompleteness.commitWithH (m := Id) (Pure.pure ∘ Hk) (layoutsOf 24).2.1.logN
      out.qStack := by rw [← hout_def, ← hGN]; exact hqt
  clear hr hinp hstr hwt hqt hout_def
  have hro : r.out = (Spec.of (D.circuitAt roots.pi1).circuit).core.run out.inputs := by rw [hout, hinp']
  -- the contract
  refine holds_id (P := fun x : Bool × List (List (List UInt8)) ↦ x.1 = true) ?_
  unfold RecDeployment.contractWith
  refine holds_bind (Q := fun iv ↦ iv = ivOf D F roots) (holds_id_of rfl) fun iv hiv ↦ ?_
  subst hiv
  refine holds_bind (Q := fun oc ↦ oc.result = .ok r) (holds_id_of hr') fun oc hoc ↦ ?_
  have hacc : oc.accepts = true := by
    unfold Outcome.accepts
    rw [hoc]
    show (r.out.all != 0) = true
    rw [hro]
    simpa using halg.1
  split
  · rename_i e he
    rw [hoc] at he
    cases he
  rename_i r' hr''
  rw [hoc] at hr''
  cases hr''
  simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hpl : (pi1CallsWith D.pi1Calls roots.pi1.bytecode).length = 3 := by
    simp [pi1CallsWith, hcalls3]
  have hlen : (pcsCalls (D.circuitAt roots.pi1).circuit (pi1CallsWith D.pi1Calls roots.pi1.bytecode)
      (digestBytes roots.pi2) out.stream r).length = 6 := by rw [pcsCalls_length, hpl]
  simp only [hlen, ne_eq, not_true_eq_false, ↓reduceIte]
  refine holds_bind (Q := fun ok ↦ ok = true) (holds_id_of ?_) fun ok hok ↦ holds_pure hok
  -- the six calls, each accepted
  rw [hlogN]
  obtain ⟨ops, hops, hseq⟩ := hpi1
  -- π1's three: the contract's first three calls decode to `ops`
  obtain ⟨hsz, hsc, hpp⟩ := (holds_id (runWith_post (m := Id) F (Spec.of (D.circuitAt roots.pi1).circuit)
    (ivOf D F roots) input.toList out.stream)).1 r hr'
  obtain ⟨r₀, hr₀, hsc₀, hpp₀⟩ := run_ok_of_runWith (m := Id) (Spec.of (D.circuitAt roots.pi1).circuit) input.toList
    out.stream [] r hsz hsc hpp
  have hpi1calls : (pi1CallsWith D.pi1Calls roots.pi1.bytecode).map
      (·.map (callWord (D.circuitAt roots.pi1).circuit.reads out.stream r)) =
      [((pi1CallsWith D.pi1Calls roots.pi1.bytecode).map
        (·.map (callWord (D.circuitAt roots.pi1).circuit.reads out.stream r))).getD 0 [],
       ((pi1CallsWith D.pi1Calls roots.pi1.bytecode).map
        (·.map (callWord (D.circuitAt roots.pi1).circuit.reads out.stream r))).getD 1 [],
       ((pi1CallsWith D.pi1Calls roots.pi1.bytecode).map
        (·.map (callWord (D.circuitAt roots.pi1).circuit.reads out.stream r))).getD 2 []] :=
    list3_getD _ (by simp [hpl]) []
  set a₀ := ((pi1CallsWith D.pi1Calls roots.pi1.bytecode).map
    (·.map (callWord (D.circuitAt roots.pi1).circuit.reads out.stream r))).getD 0 [] with ha₀
  set a₁ := ((pi1CallsWith D.pi1Calls roots.pi1.bytecode).map
    (·.map (callWord (D.circuitAt roots.pi1).circuit.reads out.stream r))).getD 1 [] with ha₁
  set a₂ := ((pi1CallsWith D.pi1Calls roots.pi1.bytecode).map
    (·.map (callWord (D.circuitAt roots.pi1).circuit.reads out.stream r))).getD 2 [] with ha₂
  have hops' : [a₀, a₁, a₂].mapM (fun words ↦ (decodeWith (registryOf D.pi1.shape 24) words).map
      fun x ↦ (x.1, words.getD 1 [], x.2.2)) = some ops := by
    rw [← hops, ← hpi1calls]
    unfold pi1OpsOf
    simp only
    rw [hr₀]
    simp only
    unfold contractPi1Openings
    rw [hlogN, pcsCalls_take _ _ _ _ _ hpl, callWord_congr _ _ hsc₀ hpp₀]
  obtain ⟨o0, o1, o2, hops3, h0, h1, h2⟩ := mapM_three _ _ _ _ _ hops'
  obtain ⟨x0, hx0, rfl⟩ := Option.map_eq_some_iff.mp h0
  obtain ⟨x1, hx1, rfl⟩ := Option.map_eq_some_iff.mp h1
  obtain ⟨x2, hx2, rfl⟩ := Option.map_eq_some_iff.mp h2
  subst hops3
  have hb : ((Id.run (openAt F (registryOf D.pi1.shape 24) (x0.1, a₀.getD 1 [], x0.2.2) c1) &&
      Id.run (openAt F (registryOf D.pi1.shape 24) (x1.1, a₁.getD 1 [], x1.2.2) c2)) &&
      Id.run (openAt F (registryOf D.pi1.shape 24) (x2.1, a₂.getD 1 [], x2.2.2) cf)) = true := hseq
  simp only [Bool.and_eq_true] at hb
  -- π2's three
  have hcr : (D.circuitAt roots.pi1).circuit.reads = Data.circuit.reads := by rw [hview]
  have hpw := publicWire_length _ _ hmatch
  obtain ⟨hoffW, hoffQ⟩ := rootsAt_offsets Data.circuit.reads
  have hrootW : streamWord out.stream ((rootsAt (D.circuitAt roots.pi1).circuit.reads).getD
      (rootReads (D.circuitAt roots.pi1).circuit.reads) 0) = UniStatement.rootWord (digestScalars out.wTree.root) := by
    rw [hcr, hoffW, ← hpw]
    refine streamWord_of out.stream _ _ (UniStatement.rootWord (digestScalars out.qTree.root) ++
      (out.inputs.a ++ [out.inputs.ξ]).flatMap UniComplete.scalarWire) ?_ (length_rootWord _)
    rw [hstr', hcr]
    simp only [List.append_assoc]
  have hrootQ : streamWord out.stream ((rootsAt (D.circuitAt roots.pi1).circuit.reads).getD
      (rootReads (D.circuitAt roots.pi1).circuit.reads + 1) 0) =
      UniStatement.rootWord (digestScalars out.qTree.root) := by
    rw [hcr, hoffQ, ← hpw]
    have := streamWord_of out.stream (publicWire (Data.circuit.reads.zip values) ++
      UniStatement.rootWord (digestScalars out.wTree.root)) (UniStatement.rootWord (digestScalars out.qTree.root))
      ((out.inputs.a ++ [out.inputs.ξ]).flatMap UniComplete.scalarWire)
      (by rw [hstr', hcr]; simp only [List.append_assoc]) (length_rootWord _)
    rwa [List.length_append, length_rootWord] at this
  obtain ⟨lW, lS, lQ, lSum⟩ := run_points_length (Spec.of (D.circuitAt roots.pi1).circuit).core
    (by rw [hview]; rfl) (by rw [hview]; rfl) out.inputs
  obtain ⟨hcW, hcQ, hcSum, hcS⟩ := halg.2
  rw [hlogN] at hcW hcQ hcSum hcS
  -- the six calls listed
  unfold pcsCalls
  simp only [hlogN]
  rw [hpi1calls]
  simp only [RecProof.openings, List.cons_append, List.nil_append, List.zip_cons_cons, List.zip_nil_left]
  refine forIn_and_true _ (fun x ↦ Id.run (pcsOpenAt F (registryOf D.pi1.shape 24) x.1 x.2))
    (fun x b ↦ by obtain ⟨_, _⟩ := x; rfl) _ true ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [pcsOpenAt_eq F _ _ _ x0 hx0]; exact hb.1.1
  · rw [pcsOpenAt_eq F _ _ _ x1 hx1]; exact hb.1.2
  · rw [pcsOpenAt_eq F _ _ _ x2 hx2]; exact hb.2
  · -- `W`
    have hd := decodeWith_claims (registryOf D.pi1.shape 24)
      (streamWord out.stream ((rootsAt (D.circuitAt roots.pi1).circuit.reads).getD
        (rootReads (D.circuitAt roots.pi1).circuit.reads) 0)) (layoutWords 24).1 (.pi2 (layoutsOf 24).1)
      (registry_lookup_w D.pi1.shape 24) (by rw [hrootW]; exact length_rootWord _) [r.witness] (by simp)
      Pi1Decode.countOfWord_numberWord_one
      (by intro c' hc'; simp at hc'; subst hc'; simp [Reduced.witness, hro, lW, Opener.vars, varsW])
    simp only [List.length_singleton, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hd
    simp only [List.cons_append, List.nil_append] at hd
    unfold pcsOpenAt
    dsimp only
    rw [hd, hrootW, rootOfWord_rootWord_digestScalars]
    simp only [List.map_cons, List.map_nil]
    rw [E2ECompleteness.openingWith_eqH, hk, hwt']
    refine Pi2W.pi2Open_honest Hk F fuel Pi2W.pi2Layout_w out.wStack _ (by simp) ?_ ?_
    · intro cl hcl
      simp only [List.mem_singleton] at hcl
      subst hcl
      exact ⟨by simp [Reduced.witness, hro, lW, varsW], by simpa [Reduced.witness, hro] using hcW⟩
    · have h := hW
      rw [hwt', ← hro] at h
      exact h
  · -- the setup
    have hd := decodeWith_claims (registryOf D.pi1.shape 24) (rootWordOfBytes (digestBytes roots.pi2))
      (layoutWords 24).2.2 (.pi2 (layoutsOf 24).2.2) (registry_lookup_s D.pi1.shape 24)
      (by simp [rootWordOfBytes, Pi1Decode.length_digestBytes]) [r.setup] (by simp)
      Pi1Decode.countOfWord_numberWord_one
      (by intro c' hc'; simp at hc'; subst hc'; simp [Reduced.setup, hro, lS, Opener.vars, varsS])
    simp only [List.length_singleton, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hd
    simp only [List.cons_append, List.nil_append] at hd
    unfold pcsOpenAt
    dsimp only
    rw [hd, rootOfWord_rootWordOfBytes_digestBytes, hroot2]
    simp only [List.map_cons, List.map_nil]
    rw [E2ECompleteness.openingWith_eqH, hk]
    refine Pi2W.pi2Open_honest Hk F fuel Pi2W.pi2Layout_s (D.circuitAt roots.pi1).setupStack _ (by simp) ?_ ?_
    · intro cl hcl
      simp only [List.mem_singleton] at hcl
      subst hcl
      exact ⟨by simp [Reduced.setup, hro, lS, varsS], by simpa [Reduced.setup, hro, hinp'] using hcS⟩
    · have h := hS
      rw [← hro, ← hinp'] at h
      exact h
  · -- `Q`
    have hd := decodeWith_claims (registryOf D.pi1.shape 24)
      (streamWord out.stream ((rootsAt (D.circuitAt roots.pi1).circuit.reads).getD
        (rootReads (D.circuitAt roots.pi1).circuit.reads + 1) 0)) (layoutWords 24).2.1 (.pi2 (layoutsOf 24).2.1)
      (registry_lookup_q D.pi1.shape 24) (by rw [hrootQ]; exact length_rootWord _) [r.quotient, r.sum] (by simp)
      countOfWord_numberWord_two
      (by
        intro c' hc'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
        rcases hc' with rfl | rfl
        · simp [Reduced.quotient, hro, lQ, Opener.vars, varsQ]
        · simp [Reduced.sum, hro, lSum, Opener.vars, varsQ])
    simp only [List.length_cons, List.length_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hd
    simp only [List.cons_append, List.nil_append] at hd
    unfold pcsOpenAt
    dsimp only
    rw [hd, hrootQ, rootOfWord_rootWord_digestScalars]
    simp only [List.map_cons, List.map_nil]
    rw [E2ECompleteness.openingWith_eqH, hk, hqt']
    refine Pi2W.pi2Open_honest Hk F fuel Pi2W.pi2Layout_q out.qStack _ (by simp) ?_ ?_
    · intro cl hcl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl
      · exact ⟨by simp [Reduced.quotient, hro, lQ, varsQ], by simpa [Reduced.quotient, hro] using hcQ⟩
      · exact ⟨by simp [Reduced.sum, hro, lSum, varsQ], by simpa [Reduced.sum, hro] using hcSum⟩
    · have h := hQ
      rw [hqt', ← hro] at h
      exact h

end RecCompose.Pi2K

/-- info: 'RecCompose.Pi2K.contract_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2K.contract_accepts
