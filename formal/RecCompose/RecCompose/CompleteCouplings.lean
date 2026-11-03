-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCompose.Complete
import RecCompose.RpmC
import RecCompose.Pi1Decode

/-!
# The completeness couplings, proved

Both in the eager form of the random-permutation model (`RpmC.eager_eq`, `RpmC.eager_le_add`: per permutation the
game keeps no state).

* **`completenessAgree`**: `CompletenessAgree D P1 P2`, for every deployment and provers: π2's completeness
  experiment runs π1-rec3's graph's check between π1's prover and π2's; per permutation its result is unused by the
  rest and drops out (`OracleComp.prEvent_true_eq_one`, `prEvent_bind_eq_of_forall_eq`).
* **`completenessPi1Coupling`**: `CompletenessPi1Coupling D P1 P2`, at the reference shape and under one named fact of
  π1-rec3's verifier's code, **`Pi1RunShape`** (a run that returns a result has no matrices' claim and roots with zero top
  limbs). Per permutation, setup and π1 proof: on the merge hazard the honest-hazard experiment's event holds; off it
  (`graph_le_verifier`) the graph is the verifier (`Pi1GraphIsVerifier`), its checks the run's verdict, its calls
  `UniStatement.pcsCalls`, which decode back to the verifier's three openings (`Pi1Decode.decodePi1Call_point`,
  `Pi1Decode.rootOfWord_rootWord`; the setup's root replaced by the setup's), so the graph runs the same three openings
  as π1-rec3's verifier when the run has three point openings of the right sizes, and π1-rec3's verifier rejects
  surely otherwise (`support_forIn_false`, `pcsOpenWith_of_length_ne`).

With them, `recCompleteness_of_part1 h2 (completenessAgree D P1 P2) (completenessPi1Coupling D hD hS P1 P2)` is
`RecCompleteness`.
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec Common
open PcsQuotient.EndToEnd.Eager
open scoped ENNReal

/-- **`CompletenessAgree`**: π2's experiment's second verdict is the end-to-end experiment's (per permutation the graph's
check, its answer unused by the rest, drops out). -/
theorem completenessAgree (D : RecDeployment) (P1 : Pi1Prover D) (P2 : Pi2Prover) : CompletenessAgree D P1 P2 := by
  intro input rows q
  unfold recCompletenessExperiment recCompletenessExperiment2
  refine RpmC.eager_eq _ _ _ _ fun π ↦ ?_
  rw [simulateQ_bind, simulateQ_bind]
  refine prEvent_bind_congr _ _ _ _ _ fun trees ↦ ?_
  unfold composeProver
  rw [bind_assoc, simulateQ_bind, simulateQ_bind]
  refine prEvent_bind_congr _ _ _ _ _ fun o1 ↦ ?_
  cases o1 with
  | none =>
    simp only [pure_bind, simulateQ_pure, prEvent_pure]
  | some p1 =>
    simp only
    conv_rhs => rw [simulateQ_bind]
    symm
    refine prEvent_bind_eq_of_forall_eq _ (OracleComp.prEvent_true_eq_one _) _ _ fun a1 ↦ ?_
    rw [simulateQ_bind, simulateQ_bind]
    refine prEvent_bind_congr _ _ _ _ _ fun o2 ↦ ?_
    cases o2 with
    | none => simp only [simulateQ_pure, prEvent_pure]
    | some p2 =>
      simp only [simulateQ_bind, simulateQ_pure]
      refine (prEvent_bind_congr _ _ (fun x ↦ pure x) _ (fun v ↦ v = false) fun x ↦ ?_).trans (by rw [bind_pure])
      simp only [prEvent_pure]

/-! ## π1-rec3's graph and its verifier, on one proof -/

/-- **π1-rec3's run's shape** (a fact of `UniStatement.reduceWithFs`'s code, named here, not proved): on every stream, a
run of π1-rec3's verifier (the reference shape, its Fiat–Shamir over Keccak-f[1600]) that returns a result has no
matrices' claim (the walked terminal, `Flock.verifyWalkedFs`, leaves no reduction pending, and `batchFs` defers none
without one) and roots whose halves have zero top limbs (`nextRoot` reads each half as two limbs, `eNew _ _ 0`). The
graph's calls (`UniStatement.pcsCalls`) then are exactly its openings' and their root words read back as its roots
(`Pi1Decode.rootOfWord_rootWord`). -/
def Pi1RunShape : Prop :=
  ∀ (iv publicInput : List UInt8) (stream : Array UInt8) (r : UniStatement.Reduced),
    (UniStatement.runFs UniStatement.reference iv publicInput stream (.flock UniStatement.flockMain) .point .rec3
      true).result = .ok r →
      r.matrices = none ∧ r.roots.1.1.limb 2 = 0 ∧ r.roots.1.2.limb 2 = 0 ∧ r.roots.2.1.limb 2 = 0 ∧
        r.roots.2.2.limb 2 = 0

/-- **A loop of verdicts that a `false` keeps `false`** (every step yields; from `false` every step yields `false`)
returns `false` if it starts at `false` or passes a step that always yields `false`. -/
theorem support_forIn_false {ι : Type} {spec : OracleSpec ι} {β : Type}
    (f : β → Bool → OracleComp spec (ForInStep Bool))
    (hstep : ∀ x s, ∀ y ∈ support (f x s), ∃ b, y = ForInStep.yield b)
    (hpres : ∀ x, ∀ y ∈ support (f x false), y = ForInStep.yield false) :
    ∀ (l : List β) (init : Bool), (init = false ∨ ∃ x ∈ l, ∀ s, ∀ y ∈ support (f x s), y = ForInStep.yield false) →
      ∀ y ∈ support (forIn l init f), y = false
  | [], init, h, y, hy => by
    simp only [List.forIn_nil, support_pure, Set.mem_singleton_iff] at hy
    rcases h with h | ⟨x, hx, -⟩
    · rw [hy, h]
    · simp at hx
  | a :: l, init, h, y, hy => by
    rw [List.forIn_cons, support_bind] at hy
    simp only [Set.mem_iUnion, exists_prop] at hy
    obtain ⟨step, hs, hy⟩ := hy
    obtain ⟨b, rfl⟩ := hstep a init step hs
    refine support_forIn_false f hstep hpres l b ?_ y hy
    rcases h with h | ⟨x, hx, hxf⟩
    · subst h
      have := hpres a _ hs
      simp only [ForInStep.yield.injEq] at this
      exact Or.inl this
    · rcases List.mem_cons.mp hx with rfl | hx
      · have := hxf init _ hs
        simp only [ForInStep.yield.injEq] at this
        exact Or.inl this
      · exact Or.inr ⟨x, hx, hxf⟩

/-- `PCS_OPEN` rejects a claim whose point has another number of coordinates than the layout's variables, at once. -/
theorem pcsOpenWith_of_length_ne {m : Type → Type} [Monad m] (F : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState)
    (vars : ℕ) (root : Digest) (pt : List E) (v : E) (p : LeanVM.Protocol.Compile.Proof) (h : pt.length ≠ vars) :
    UniStatement.pcsOpenWith F vars root [⟨pt, v⟩] p = pure false := by
  unfold UniStatement.pcsOpenWith PcsQuotient.openingWith
  rw [ite_eq_right]
  simp [UniStatement.plainLayout, PcsQuotient.Layout.ofChunks, h]

/-- **Off the merge hazard, π1-rec3's graph with its openings rejects at most as often as π1-rec3's verifier** at
Keccak-f[1600] with the same openings, for every permutation. -/
theorem graph_le_verifier (D : RecDeployment) (hD : D.pi1.shape = UniStatement.reference) (hS : Pi1RunShape)
    (hgv : RecGraph.Pi1.Pi1GraphIsVerifier) (π : Equiv.Perm St) (roots : UniStatement.SetupRoots)
    (input : Vector UInt8 32) (p1 : UniStatement.UniProof)
    (hz : ¬ RecGraph.MergeHazard LeanVM.Semantics.keccakF1600 (D.pi1IvAt roots) input.toList p1.stream) :
    Pr{let a ← simulateQ (permImpl π) (pi1GraphVerifierWith queryPermutation D roots input p1)}[a = false] ≤
      Pr{let a ← simulateQ (permImpl π) (pi1KeccakVerifierWith queryPermutation D.pi1 roots input p1)}[a = false] := by
  have hge := hgv LeanVM.Semantics.keccakF1600 (D.pi1IvAt roots) input p1.stream hz
  unfold pi1GraphVerifierWith pi1KeccakVerifierWith
  simp only [RecDeployment.pi1IvAt] at hge ⊢
  rw [hD] at hge ⊢
  set iv := pi1Iv UniStatement.reference D.pi1.programIv roots with hiv
  set o := UniStatement.runFs UniStatement.reference iv input.toList p1.stream (.flock UniStatement.flockMain) .point
    .rec3 true with ho
  have hgo : RecGraph.evalGraphDeployed RecGraph.Pi1.pi1Graph iv input.toList p1.stream =
      match o.result with
      | .ok r => some ⟨UniStatement.pcsCalls UniStatement.reference UniStatement.referenceRoots r,
          o.chan.zeros.toList, []⟩
      | .error _ => none := hge
  rw [hgo]
  cases hres : o.result with
  | error e =>
    have hacc : o.accepts = false := by simp [UniStatement.Outcome.accepts, hres]
    simp only [hacc, Bool.not_false, ite_true]
    exact le_rfl
  | ok r =>
    obtain ⟨hmat, h11, h12, h21, h22⟩ := hS iv input.toList p1.stream r hres
    have hacc : o.accepts = o.chan.zeros.all (· == 0) := by simp [UniStatement.Outcome.accepts, hres]
    simp only [hacc, Array.all_toList, List.all_nil, Bool.and_true]
    by_cases hzs : o.chan.zeros.all (· == 0) = true
    swap
    · simp only [Bool.eq_false_iff.mpr hzs, Bool.not_false, ite_true]
      exact le_rfl
    simp only [hzs, Bool.not_true, Bool.false_eq_true, ite_false]
    by_cases hgood : ∃ pt1 v1 pt2 v2 pt3 v3, r.openings = [(.c1, .point pt1 v1 none), (.c2, .point pt2 v2 none),
        (.setup, .point pt3 v3 none)] ∧
        pt1.length = UniStatement.layoutWordVars ((UniStatement.layoutWords UniStatement.reference).getD 0 []) ∧
        pt2.length = UniStatement.layoutWordVars ((UniStatement.layoutWords UniStatement.reference).getD 1 []) ∧
        pt3.length = UniStatement.layoutWordVars ((UniStatement.layoutWords UniStatement.reference).getD 2 [])
    · obtain ⟨pt1, v1, pt2, v2, pt3, v3, hro, hl1, hl2, hl3⟩ := hgood
      obtain ⟨⟨a0, b0, hw0⟩, ⟨a1, b1, hw1⟩, ⟨a2, b2, hw2⟩⟩ := Pi1Decode.layoutWords_getD UniStatement.reference
      have hc0 : Pi1Decode.codeOf ((UniStatement.layoutWords UniStatement.reference).getD 0 []) = 0x5501 := by
        rw [hw0, Pi1Decode.codeOf_layoutWord]; decide
      have hc1 : Pi1Decode.codeOf ((UniStatement.layoutWords UniStatement.reference).getD 1 []) = 0x5502 := by
        rw [hw1, Pi1Decode.codeOf_layoutWord]; decide
      have hc2 : Pi1Decode.codeOf ((UniStatement.layoutWords UniStatement.reference).getD 2 []) = 0x5503 := by
        rw [hw2, Pi1Decode.codeOf_layoutWord]; decide
      have hn0 : ((UniStatement.layoutWords UniStatement.reference).getD 0 []).length = 32 := by
        rw [hw0]; exact Pi1Decode.length_layoutWord _ _ _ _
      have hn1 : ((UniStatement.layoutWords UniStatement.reference).getD 1 []).length = 32 := by
        rw [hw1]; exact Pi1Decode.length_layoutWord _ _ _ _
      have hn2 : ((UniStatement.layoutWords UniStatement.reference).getD 2 []).length = 32 := by
        rw [hw2]; exact Pi1Decode.length_layoutWord _ _ _ _
      have hcalls : UniStatement.pcsCalls UniStatement.reference UniStatement.referenceRoots r =
          [UniStatement.openingWords (UniStatement.rootWord r.roots.1)
              ((UniStatement.layoutWords UniStatement.reference).getD 0 []) (.point pt1 v1 none),
            UniStatement.openingWords (UniStatement.rootWord r.roots.2)
              ((UniStatement.layoutWords UniStatement.reference).getD 1 []) (.point pt2 v2 none),
            UniStatement.openingWords (digestBytes UniStatement.referenceRoots.bytecode)
              ((UniStatement.layoutWords UniStatement.reference).getD 2 []) (.point pt3 v3 none)] := by
        unfold UniStatement.pcsCalls
        rw [hro, hmat]
        simp only [List.map_cons, List.map_nil, List.append_nil]
      have hdec : (UniStatement.pcsCalls UniStatement.reference UniStatement.referenceRoots r).mapM decodePi1Call =
          some [(UniStatement.rootOf r.roots.1, (UniStatement.layoutWords UniStatement.reference).getD 0 [],
              [⟨pt1, v1⟩]),
            (UniStatement.rootOf r.roots.2, (UniStatement.layoutWords UniStatement.reference).getD 1 [], [⟨pt2, v2⟩]),
            (UniStatement.digestOfBytes32 (digestBytes UniStatement.referenceRoots.bytecode),
              (UniStatement.layoutWords UniStatement.reference).getD 2 [], [⟨pt3, v3⟩])] := by
        rw [hcalls]
        simp only [List.mapM_cons, List.mapM_nil,
          Pi1Decode.decodePi1Call_point _ _ _ _ (UniComplete.length_rootWord _) hn0 hl1,
          Pi1Decode.decodePi1Call_point _ _ _ _ (UniComplete.length_rootWord _) hn1 hl2,
          Pi1Decode.decodePi1Call_point _ _ _ _ (Pi1Decode.length_digestBytes _) hn2 hl3, hc0, hc1, hc2,
          Pi1Decode.rootOfWord_rootWord _ h11 h12, Pi1Decode.rootOfWord_rootWord _ h21 h22]
        simp
      rw [hdec, hro]
      have hmod : ∀ (x y z : Pi1Opening) (f : Pi1Opening → Pi1Opening), [x, y, z].modify 2 f = [x, y, f z] :=
        fun _ _ _ _ ↦ rfl
      have hcm : (List.map (fun x ↦ x.1) [(UniStatement.Commitment.c1, UniStatement.Opening.point pt1 v1 none),
          (UniStatement.Commitment.c2, UniStatement.Opening.point pt2 v2 none),
          (UniStatement.Commitment.setup, UniStatement.Opening.point pt3 v3 none)] == UniStatement.commitments) = true :=
        rfl
      simp only [hmod, hcm, List.length_cons, List.length_nil, List.zip_cons_cons,
        List.zip_nil_right, List.forIn_cons, List.forIn_nil, bind_assoc, pure_bind, ne_eq, not_true_eq_false,
        ite_false, zero_add, Nat.reduceAdd]
      exact le_rfl
    · refine le_of_le_of_eq (prEvent_le_one _) (RpmC.prEvent_perm_eq_one π _ _ ?_).symm
      intro y hy
      simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff, exists_prop] at hy
      obtain ⟨s, hs, hys⟩ := hy
      rw [hys]
      refine support_forIn_false _ ?_ ?_ r.openings _ ?_ s hs
      · rintro ⟨c, op⟩ b y hy
        rcases op with _ | ⟨pt, v, _ | bs⟩
        all_goals simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hy
        · exact ⟨false, hy⟩
        · obtain ⟨i, -, hi⟩ := hy
          exact ⟨_, hi⟩
        · exact ⟨false, hy⟩
      · rintro ⟨c, op⟩ y hy
        rcases op with _ | ⟨pt, v, _ | bs⟩
        all_goals simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hy
        · exact hy
        · obtain ⟨i, -, hi⟩ := hy
          rw [hi, Bool.false_and]
        · exact hy
      · by_cases hm : r.openings.map (·.1) = UniStatement.commitments
        · right
          rcases hro : r.openings with _ | ⟨⟨c1', o1⟩, _ | ⟨⟨c2', o2⟩, _ | ⟨⟨c3', o3⟩, _ | ⟨x4, l⟩⟩⟩⟩
          all_goals rw [hro] at hm
          all_goals simp [UniStatement.commitments] at hm
          obtain ⟨rfl, rfl, rfl⟩ := hm
          by_cases g1 : ∃ pt v, o1 = .point pt v none ∧
              pt.length = UniStatement.layoutWordVars ((UniStatement.layoutWords UniStatement.reference).getD 0 [])
          · by_cases g2 : ∃ pt v, o2 = .point pt v none ∧
                pt.length = UniStatement.layoutWordVars ((UniStatement.layoutWords UniStatement.reference).getD 1 [])
            · by_cases g3 : ∃ pt v, o3 = .point pt v none ∧
                  pt.length = UniStatement.layoutWordVars ((UniStatement.layoutWords UniStatement.reference).getD 2 [])
              · exfalso
                obtain ⟨q1, w1, rfl, l1⟩ := g1
                obtain ⟨q2, w2, rfl, l2⟩ := g2
                obtain ⟨q3, w3, rfl, l3⟩ := g3
                exact hgood ⟨q1, w1, q2, w2, q3, w3, hro, l1, l2, l3⟩
              · refine ⟨(.setup, o3), by simp, fun s y hy ↦ ?_⟩
                rcases o3 with _ | ⟨pt, v, _ | bs⟩
                all_goals simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hy
                · exact hy
                · rw [pcsOpenWith_of_length_ne _ _ _ _ _ _ (fun hl ↦ g3 ⟨pt, v, rfl, hl⟩)] at hy
                  simp only [support_pure, Set.mem_singleton_iff, exists_eq_left, Bool.and_false] at hy
                  exact hy
                · exact hy
            · refine ⟨(.c2, o2), by simp, fun s y hy ↦ ?_⟩
              rcases o2 with _ | ⟨pt, v, _ | bs⟩
              all_goals simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hy
              · exact hy
              · rw [pcsOpenWith_of_length_ne _ _ _ _ _ _ (fun hl ↦ g2 ⟨pt, v, rfl, hl⟩)] at hy
                simp only [support_pure, Set.mem_singleton_iff, exists_eq_left, Bool.and_false] at hy
                exact hy
              · exact hy
          · refine ⟨(.c1, o1), by simp, fun s y hy ↦ ?_⟩
            rcases o1 with _ | ⟨pt, v, _ | bs⟩
            all_goals simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hy
            · exact hy
            · rw [pcsOpenWith_of_length_ne _ _ _ _ _ _ (fun hl ↦ g1 ⟨pt, v, rfl, hl⟩)] at hy
              simp only [support_pure, Set.mem_singleton_iff, exists_eq_left, Bool.and_false] at hy
              exact hy
            · exact hy
        · left
          simp [hm]

/-- **`CompletenessPi1Coupling`**, at the reference shape, π1-rec3's run's shape given: per permutation, setup and π1
proof, on the merge hazard the honest-hazard experiment's event holds, and off it the graph rejects at most as often as
π1-rec3's verifier at Keccak-f[1600] (`graph_le_verifier`); π2's prover and the contract after the graph's check change
nothing of its verdict. -/
theorem completenessPi1Coupling (D : RecDeployment) (hD : D.pi1.shape = UniStatement.reference) (hS : Pi1RunShape)
    (P1 : Pi1Prover D) (P2 : Pi2Prover) : CompletenessPi1Coupling D P1 P2 := by
  intro hgv input rows q
  unfold recCompletenessExperiment2 pi1KeccakCompletenessExperiment pi1HonestHazardExperiment
  refine RpmC.eager_le_add _ _ _ _ _ _ fun π ↦ ?_
  rw [simulateQ_bind, simulateQ_bind, simulateQ_bind]
  refine prEvent_bind_le_add_of_forall_le _ _ _ _ _ _ _ fun trees ↦ ?_
  rw [simulateQ_bind, simulateQ_bind, simulateQ_bind]
  refine prEvent_bind_le_add_of_forall_le _ _ _ _ _ _ _ fun o1 ↦ ?_
  cases o1 with
  | none =>
    simp only [simulateQ_pure, prEvent_pure, ite_true]
    exact le_add_right le_rfl
  | some p1 =>
    simp only
    rw [simulateQ_bind]
    refine (prEvent_bind_congr _ _ (fun a ↦ (pure a : ProbComp Bool)) _ (fun v ↦ v = false) fun a1 ↦ ?_).trans_le ?_
    · rw [simulateQ_bind]
      refine prEvent_bind_eq_of_forall_eq _ (OracleComp.prEvent_true_eq_one _) _ _ fun o2 ↦ ?_
      cases o2 with
      | none => simp only [simulateQ_pure, prEvent_pure]
      | some p2 =>
        simp only [simulateQ_bind, simulateQ_pure]
        exact prEvent_bind_eq_of_forall_eq _ (OracleComp.prEvent_true_eq_one _) _ _ fun v ↦ by
          simp only [prEvent_pure]
    · classical
      rw [bind_pure, simulateQ_pure, prEvent_pure]
      by_cases hz : RecGraph.MergeHazard LeanVM.Semantics.keccakF1600 (D.pi1IvAt trees.roots.pi1) input.toList
        p1.stream
      · rw [ite_eq_left ⟨_, _, rfl, hz⟩]
        exact (prEvent_le_one _).trans le_add_self
      · rw [ite_eq_right fun ⟨iv, s, he, hs⟩ ↦ by
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact hz hs, add_zero]
        exact graph_le_verifier D hD hS hgv π trees.roots.pi1 input p1 hz

end RecCompose

/-- info: 'RecCompose.completenessAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.completenessAgree

/-- info: 'RecCompose.graph_le_verifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.graph_le_verifier

/-- info: 'RecCompose.completenessPi1Coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.completenessPi1Coupling
