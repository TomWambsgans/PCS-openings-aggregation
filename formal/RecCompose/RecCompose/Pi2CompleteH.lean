-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Transcribed from `formal/RecStatement` (`Verifier.lean`:
-- `ivWith`, `reduceWith`, `runWith`; `Security.lean`: `Pi2Circuit.digestWith`, `Pi2Circuit.setupTreeWith`,
-- `RecDeployment.ivWith`, `pcsOpenAt`, `RecDeployment.contractWith`, `RecDeployment.verifierWith`,
-- `RecDeployment.setupTreesWith`, `pi1GraphVerifierWith`) and `RecCompose.Couplings` (`openAt`, `openSeq`), with
-- Keccak-256 an explicit call, as `formal/UniComplete/UniComplete/VerifierH.lean` rewrites `formal/UniStatement`.
import RecCompose.Pi2Run
import RecCompose.Couplings
import UniComplete.VerifierH

/-!
# π2's verifier, contract and setup with Keccak-256 an explicit call

`formal/RecStatement`'s contract and setup are written over a permutation `F`, every Keccak-256 the sponge over it
(`keccak256With F`). Here each function that hashes is rewritten with Keccak-256 a separate function `H` (`…H`), the
code text the Statement's, only the hash changed (UniComplete's `sampleH`, `pcsOpenWithH`, `setupTreesWithH`;
WithHash's `openingWithH`, `commitWithH`). **At `H = keccak256With F`** each is the Statement's (`…_eqH`). And
`runWithH_post`: `Pi2Run.runWith_post` at any `H` (the run's success and public data do not depend on the hashes).
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2H

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open UniStatement (Chan ChanM)

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- `RecStatement.ivWith` with Keccak-256 `H`. -/
def ivWithH (pi1Iv digest setupRoot : List UInt8) (logN : ℕ) : m (List UInt8) := do
  let (w, q, s) := layoutWords logN
  let d ← H (ivTag ++ pi1Iv ++ setupRoot ++ digest ++ w ++ q ++ s)
  return digestBytes d

/-- `RecStatement.reduceWith` with Keccak-256 `H`. -/
def reduceWithH (s : Spec) (statement : List E) : ChanM m Reduced := do
  let mut pubs := statement
  for rd in s.reads do
    match rd with
    | .integer b => pubs := pubs ++ [UniStatement.eK (UInt64.ofNat (← UniStatement.nextInteger (m := m) b))]
    | .root =>
      let (lo, hi) ← UniStatement.nextRoot (m := m)
      pubs := pubs ++ [lo, hi]
    | .scalar => pubs := pubs ++ [← UniStatement.nextScalar (m := m)]
  let wRoot ← UniStatement.nextRoot (m := m)
  let α ← UniComplete.sampleH H
  let β ← UniComplete.sampleH H
  let γ ← UniComplete.sampleH H
  let qRoot ← UniStatement.nextRoot (m := m)
  let t ← UniComplete.sampleH H
  let a ← UniStatement.nextScalars (m := m) (2 ^ s.logRow)
  let ξ ← UniStatement.nextScalar (m := m)
  let ρ ← UniComplete.sampleH H
  let inp : Inputs E := ⟨pubs, α, β, γ, t, a, ξ, ρ⟩
  return ⟨pubs, pubs.map pairPoint, (wRoot, qRoot), inp, s.core.run inp⟩

/-- `RecStatement.runWith` with Keccak-256 `H`. -/
def runWithH (s : Spec) (iv publicInput : List UInt8) (stream : Array UInt8) : m Outcome := do
  let seed ← H (name ++ iv ++ publicInput)
  let walk : ChanM m Reduced := do
    let r ← reduceWithH H s (UniStatement.publicWordsOf publicInput)
    UniStatement.finish (m := m)
    return r
  let (result, chan) ← (walk.run).run (Chan.start seed stream)
  return ⟨result, chan⟩

/-- `Pi2Circuit.digestWith` with Keccak-256 `H`. -/
def digestWithH (c : Pi2Circuit) : m (List UInt8) := do
  let sigma ← H ((List.range c.n).flatMap fun i ↦ (le64 (c.sigma i)).take 4)
  let kappa ← H ((List.range c.n).flatMap fun i ↦ le64 (c.kappa i).lane.toNat)
  let d ← H (c.circuit.encoding ++ digestBytes sigma ++ digestBytes kappa)
  return digestBytes d

/-- `RecDeployment.ivWith` with Keccak-256 `H`. -/
def ivOfH (D : RecDeployment) (roots : RecSetupRoots) : m (List UInt8) := do
  let c := D.circuitAt roots.pi1
  let digest ← digestWithH H c
  ivWithH H (D.pi1IvAt roots.pi1) digest (digestBytes roots.pi2) c.circuit.logN

/-- `pcsOpenAt` with Keccak-256 `H`. -/
def pcsOpenAtH (registry : List (List UInt8 × Opener)) (words : List (List UInt8)) (proof : Compile.Proof) : m Bool :=
  match decodeWith registry words with
  | none => pure false
  | some (root, .pi1 vars, claims) => UniComplete.pcsOpenWithH H F vars root claims proof
  | some (root, .pi2 L, claims) => E2ECompleteness.openingWithH H F L root claims proof

/-- `RecDeployment.contractWith` with Keccak-256 `H`. -/
def contractWithH (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32)
    (proof : RecProof) : m (Bool × List (List (List UInt8))) := do
  let c := D.circuitAt roots.pi1
  let iv ← ivOfH H D roots
  let o ← runWithH H (Spec.of c.circuit) iv input.toList proof.stream
  match o.result with
  | .error _ => return (false, [])
  | .ok r =>
    if !o.accepts then return (false, []) else
    let calls := pcsCalls c.circuit (pi1CallsWith D.pi1Calls roots.pi1.bytecode) (digestBytes roots.pi2)
      proof.stream r
    if calls.length ≠ 6 then return (false, calls) else
    let reg := registryOf D.pi1.shape c.circuit.logN
    let mut ok := true
    for (words, p) in calls.zip proof.openings do
      ok := ok && (← pcsOpenAtH H F reg words p)
    return (ok, calls)

/-- `RecDeployment.verifierWith` with Keccak-256 `H`. -/
def verifierWithH (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32) (proof : RecProof) : m Bool := do
  return (← contractWithH H F D roots input proof).1

/-- `Pi2Circuit.setupTreeWith` with Keccak-256 `H`. -/
def setupTreeWithH (c : Pi2Circuit) : m LeanVM.Prover.Tree :=
  E2ECompleteness.commitWithH H (layoutsOf c.circuit.logN).2.2.logN c.setupStack

/-- `RecDeployment.setupTreesWith` with Keccak-256 `H`. -/
def setupTreesWithH (D : RecDeployment) : m RecSetupTrees := do
  let t1 ← UniComplete.setupTreesWithH H F D.pi1
  let t2 ← setupTreeWithH H (D.circuitAt t1.roots)
  return ⟨t1, t2⟩

/-- `pi1GraphVerifierWith` with Keccak-256 `H`. -/
def pi1GraphVerifierWithH (D : RecDeployment) (roots : UniStatement.SetupRoots) (input : Vector UInt8 32)
    (proof : UniStatement.UniProof) : m Bool := do
  match RecGraph.evalGraphDeployed RecGraph.Pi1.pi1Graph (D.pi1IvAt roots) input.toList proof.stream with
  | none => return false
  | some out =>
    if !(out.zeros.all (· == 0) && out.nonzeros.all (· != 0)) then return false
    match out.calls.mapM decodePi1Call with
    | none => return false
    | some ops =>
      if ops.length ≠ 3 then return false
      let ops := ops.modify 2 fun o ↦ (roots.bytecode, o.2)
      let mut ok := true
      for (o, p) in ops.zip [proof.c1, proof.c2, proof.setup] do
        ok := ok && (← UniComplete.pcsOpenWithH H F (UniStatement.layoutWordVars o.2.1) o.1 o.2.2 p)
      return ok

/-- `Couplings.openAt` with Keccak-256 `H`. -/
def openAtH (reg : List (List UInt8 × Opener)) (o : Pi1Opening) (p : Compile.Proof) : m Bool :=
  match reg.lookup o.2.1 with
  | none => pure false
  | some (.pi1 vars) => UniComplete.pcsOpenWithH H F vars o.1 o.2.2 p
  | some (.pi2 L) => E2ECompleteness.openingWithH H F L o.1 o.2.2 p

/-- `Couplings.openSeq` with Keccak-256 `H`. -/
def openSeqH (reg : List (List UInt8 × Opener)) (ops : List Pi1Opening) (proof : RecProof) : m Bool := do
  let b1 ← openAtH H F reg (ops.getD 0 default) proof.c1
  let b2 ← openAtH H F reg (ops.getD 1 default) proof.c2
  let b3 ← openAtH H F reg (ops.getD 2 default) proof.f
  return b1 && b2 && b3

end With

/-! ## At `H = keccak256With F`: the Statement's -/

section Eq

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

theorem ivWith_eqH (pi1Iv digest setupRoot : List UInt8) (logN : ℕ) :
    RecStatement.ivWith F pi1Iv digest setupRoot logN = ivWithH (keccak256With F) pi1Iv digest setupRoot logN := rfl

theorem reduceWith_eqH (s : Spec) (statement : List E) :
    reduceWith F s statement = reduceWithH (keccak256With F) s statement := rfl

theorem runWith_eqH (s : Spec) (iv publicInput : List UInt8) (stream : Array UInt8) :
    runWith F s iv publicInput stream = runWithH (keccak256With F) s iv publicInput stream := rfl

theorem digestWith_eqH (c : Pi2Circuit) : c.digestWith F = digestWithH (keccak256With F) c := rfl

theorem ivWith_deploy_eqH (D : RecDeployment) (roots : RecSetupRoots) :
    D.ivWith F roots = ivOfH (keccak256With F) D roots := rfl

theorem pcsOpenAt_eqH (registry : List (List UInt8 × Opener)) (words : List (List UInt8)) (proof : Compile.Proof) :
    pcsOpenAt F registry words proof = pcsOpenAtH (keccak256With F) F registry words proof := by
  unfold pcsOpenAt pcsOpenAtH
  generalize decodeWith registry words = d
  rcases d with _ | ⟨root, ⟨vars⟩ | ⟨L⟩, claims⟩
  · rfl
  · exact UniComplete.pcsOpenWith_eqH F _ _ _ _
  · exact E2ECompleteness.openingWith_eqH F _ _ _ _

theorem contractWith_eqH (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32) (proof : RecProof) :
    D.contractWith F roots input proof = contractWithH (keccak256With F) F D roots input proof := by
  have h : pcsOpenAt F = pcsOpenAtH (keccak256With F) F := by
    funext reg words p
    exact pcsOpenAt_eqH F reg words p
  unfold RecDeployment.contractWith contractWithH
  rw [h]
  rfl

theorem verifierWith_eqH (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32) (proof : RecProof) :
    D.verifierWith F roots input proof = verifierWithH (keccak256With F) F D roots input proof := by
  unfold RecDeployment.verifierWith verifierWithH
  rw [contractWith_eqH]

theorem setupTreeWith_eqH (c : Pi2Circuit) : c.setupTreeWith F = setupTreeWithH (keccak256With F) c := by
  unfold Pi2Circuit.setupTreeWith setupTreeWithH
  exact E2ECompleteness.commitWith_eqH F _ _

theorem setupTreesWith_eqH (D : RecDeployment) :
    D.setupTreesWith F = setupTreesWithH (keccak256With F) F D := by
  unfold RecDeployment.setupTreesWith setupTreesWithH
  simp only [UniComplete.setupTreesWith_eqH]
  simp only [setupTreeWith_eqH]

theorem pi1GraphVerifierWith_eqH (D : RecDeployment) (roots : UniStatement.SetupRoots) (input : Vector UInt8 32)
    (proof : UniStatement.UniProof) :
    pi1GraphVerifierWith F D roots input proof = pi1GraphVerifierWithH (keccak256With F) F D roots input proof := by
  have h : UniStatement.pcsOpenWith F = UniComplete.pcsOpenWithH (keccak256With F) F := by
    funext v r c p
    exact UniComplete.pcsOpenWith_eqH F v r c p
  unfold pi1GraphVerifierWith pi1GraphVerifierWithH
  rw [h]
  rfl

theorem openAt_eqH (reg : List (List UInt8 × Opener)) (o : Pi1Opening) (p : Compile.Proof) :
    openAt F reg o p = openAtH (keccak256With F) F reg o p := by
  unfold openAt openAtH
  generalize reg.lookup o.2.1 = d
  rcases d with _ | ⟨vars⟩ | ⟨L⟩
  · rfl
  · exact UniComplete.pcsOpenWith_eqH F _ _ _ _
  · exact E2ECompleteness.openingWith_eqH F _ _ _ _

theorem openSeq_eqH (reg : List (List UInt8 × Opener)) (ops : List Pi1Opening) (proof : RecProof) :
    openSeq F reg ops proof = openSeqH (keccak256With F) F reg ops proof := by
  unfold openSeq openSeqH
  simp only [openAt_eqH]

end Eq

/-- `Couplings.pcsOpenAt_eq` with Keccak-256 `H`. -/
theorem pcsOpenAtH_eq {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)
    (reg : List (List UInt8 × Opener)) (w : List (List UInt8)) (p : Compile.Proof)
    (x : Digest × Opener × List PcsQuotient.Claim) (h : decodeWith reg w = some x) :
    pcsOpenAtH H F reg w p = openAtH H F reg (x.1, w.getD 1 [], x.2.2) p := by
  have hl := lookup_of_decodeWith reg w x h
  unfold pcsOpenAtH openAtH
  rw [h]
  simp only [hl]
  obtain ⟨root, op, claims⟩ := x
  cases op <;> rfl

/-! ## The run's public data, at any `H` -/

section Generic

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem sampleH_run (H : List UInt8 → m Digest) (c : Chan) :
    ((UniComplete.sampleH H).run).run c =
      (fun st ↦ (.ok (PcsQuotient.Transcript.challengeOf st), sampled c st)) <$>
        H (digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList) := by
  unfold UniComplete.sampleH sampled
  simp [Except.map]

theorem reads_sampleH (H : List UInt8 → m Digest) : Reads (UniComplete.sampleH H) 0 fun _ _ _ ↦ True := by
  intro c
  rw [sampleH_run]
  exact holds_map (holds_true _) fun st _ ↦ ⟨rfl, fun a _ ↦ ⟨rfl, trivial⟩, fun _ ↦ ⟨_, rfl⟩⟩

theorem reads_reduceWithH (H : List UInt8 → m Digest) (s : RecStatement.Spec) (stmt : List E) :
    Reads (reduceWithH H s stmt) (pi2Bytes s) fun d cur r ↦
      r.scalars = foldReads RecStatement.Read.bytes pubsStep d cur s.reads stmt ∧
        r.pairPoints = r.scalars.map RecStatement.pairPoint := by
  unfold reduceWithH
  refine reads_mono (reads_bind (reads_forIn RecStatement.Read.bytes pubsStep _ (fun rd b ↦ ?_) s.reads stmt)
    fun pubs _ ↦
      reads_bind reads_nextRoot fun wRoot _ ↦
      reads_bind (reads_sampleH H) fun α _ ↦
      reads_bind (reads_sampleH H) fun β _ ↦
      reads_bind (reads_sampleH H) fun γ _ ↦
      reads_bind reads_nextRoot fun qRoot _ ↦
      reads_bind (reads_sampleH H) fun t _ ↦
      reads_bind (reads_nextScalars _) fun a _ ↦
      reads_bind reads_nextScalar fun ξ _ ↦
      reads_bind (reads_sampleH H) fun ρ _ ↦ reads_pure _) (by unfold pi2Bytes; omega) ?_
  · cases rd with
    | integer bytes =>
      refine reads_mono (reads_bind (reads_nextInteger bytes) fun x _ ↦ reads_pure _) rfl ?_
      rintro d cur st ⟨x, hx, hst⟩
      subst hx hst
      rfl
    | root =>
      refine reads_mono (reads_bind reads_nextRoot fun x _ ↦ reads_pure _) rfl ?_
      rintro d cur st ⟨x, hx, hst⟩
      subst hx hst
      rfl
    | scalar =>
      refine reads_mono (reads_bind reads_nextScalar fun x _ ↦ reads_pure _) rfl ?_
      rintro d cur st ⟨x, hx, hst⟩
      subst hx hst
      rfl
  · rintro d cur r ⟨pubs, hpubs, w, -, α, -, β, -, γ, -, q, -, t, -, a, -, ξ, -, ρ, -, hr⟩
    subst hr
    exact ⟨hpubs, rfl⟩

/-- **`runWith_post` at any `H`.** -/
theorem runWithH_post (H : List UInt8 → m Digest) (s : RecStatement.Spec) (iv input : List UInt8)
    (stream : Array UInt8) :
    Holds (runWithH H s iv input stream) fun o ↦
      (∀ r, o.result = .ok r → stream.size = pi2Bytes s ∧ r.scalars = pi2Pubs s input stream ∧
        r.pairPoints = r.scalars.map RecStatement.pairPoint) ∧
      (stream.size = pi2Bytes s → ∃ r, o.result = .ok r) := by
  unfold runWithH
  refine holds_bind (holds_true _) fun seed _ ↦ holds_bind (Q := fun p ↦
    (∀ r, p.1 = .ok r → stream.size = pi2Bytes s ∧ r.scalars = pi2Pubs s input stream ∧
        r.pairPoints = r.scalars.map RecStatement.pairPoint) ∧
      (stream.size = pi2Bytes s → ∃ r, p.1 = .ok r)) ?_ fun p hp ↦ ?_
  · rw [ExceptT.run_bind, StateT.run_bind]
    refine holds_bind (reads_reduceWithH H s (UniStatement.publicWordsOf input) (Chan.start seed stream)) ?_
    rintro ⟨e, c'⟩ ⟨hd, hok, hfit⟩
    simp only [Chan.start] at hd hok hfit
    cases e with
    | error err =>
      simp only [StateT.run_pure]
      refine holds_pure ⟨fun r hr ↦ absurd hr (by simp), fun hsz ↦ ?_⟩
      obtain ⟨a, ha⟩ := hfit (by omega)
      exact absurd ha (by simp)
    | ok r =>
      simp only
      obtain ⟨hcur, hsc, hpp⟩ := hok r rfl
      rw [ExceptT.run_bind, StateT.run_bind, finish_run]
      simp only [pure_bind]
      split_ifs with hf
      · simp only
        refine holds_pure ⟨fun r' hr' ↦ ?_, fun _ ↦ ⟨r, rfl⟩⟩
        simp only [Except.ok.injEq] at hr'
        subst hr'
        refine ⟨by rw [← hd, ← hf, hcur]; omega, hsc, hpp⟩
      · simp only [StateT.run_pure]
        refine holds_pure ⟨fun r' hr' ↦ absurd hr' (by simp), fun hsz ↦ absurd ?_ hf⟩
        rw [hcur, hd, hsz]; omega
  · obtain ⟨result, chan⟩ := p
    exact holds_pure hp

end Generic

end RecCompose.Pi2H

/-- info: 'RecCompose.Pi2H.contractWith_eqH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2H.contractWith_eqH

/-- info: 'RecCompose.Pi2H.runWithH_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2H.runWithH_post
