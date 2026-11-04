-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π2's honest prover is `crates/leanvm_rec/src/pi2/prover.rs`'s
-- (`RecCompose.Pi2Prover`), its witness the circuit compiler's (`crates/leanvm_rec/src/circuit/compile.rs`, not
-- transcribed: chosen here); the statements are `formal/RecStatement`'s (`RecCompleteness2`, `RecCompleteness`).
import RecCompose.Pi2Complete
import RecCompose.Pi2Prob
import RecCompose.Pi2HonestThm
import RecCompose.Pi2HonestCount
import RecCompose.Real
import RecCompose.End

/-!
# π2's completeness, and the recursive verifier's end to end

* **`pi2Prover D C Fa fuel : Pi2Prover`**, π2's honest prover as the recursion runs it: the setup's trees and π1's and
  π2's IVs recomputed over `π`, the circuit's witness and public values for π1's stream (`pi2Choice`: a choice of one
  satisfying the compiled circuit at the values' public limbs and holding π1's stream, `Pi2Good`), then
  `pi2ProveWith` (`prover.rs`'s `prove_with` and `open`, Keccak-256 the sponge over `π`, `π` for the proofs of work), its
  stream and three openings after π1's three.
* **`Pi2WitnessComplete D C Fa`** (named: the circuit compiler's completeness, which the Rust's witness generation and
  `Circuit::check` establish on the real vector, not proved): on a stream π1-rec3's graph accepts, such a witness exists.
* **`pi2_accepts`** (proved): at a pure permutation, π2's honest prover's proof is accepted by the contract, off the bad
  challenges (π2's arithmetic passes and its claims hold, `contract_accepts`) and the proofs of work, π1's three
  openings accepted.
* **`Pi2StagedFacts`** (named: the code-level bridge of the experiment to the two-call model, `Pi2Staged.Holds` at
  `L = 536` (`α`'s input: the state and π1's two roots and 17 elements and `W`'s root), the copy argument's
  `(2^25 + 36) |E|²` bad triples (`2N + n_P`, `N = 2^24`, `n_P = 36`), `t`'s `2^27` (`8N`), `N` block calls, `εt`,
  `εpow`): its `rejectGood` is `pi2_accepts` with the grinding, its other fields the commutation, duplex shape, cost and
  lengths of the composed code (UniComplete's `ProverSim`, `ProverDuplex`, `ProverCost`, `ProbTFresh`, `ProbGrind` for π1).
* **`recCompleteness2_pi2`**: `RecCompleteness2 D P1 (pi2Prover D C Fa fuel) (delta2 N εt εpow)`;
  **`delta2_le`**: `delta2 N εt εpow ≤ 2^-164` for `N ≤ 2^50`, `εt ≤ 2^-200`, `εpow ≤ 2^-300`;
  **`recCompleteness_pi2_fs`**: the recursive verifier's completeness end to end with `pi2Prover`, error
  `δ1 + δh + delta2`.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2E

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec Common
open Pi2S Pi2K Pi2P
open LeanVM (rpmError)
open scoped ENNReal

/-! ## The witness -/

/-- **An honest witness and public values** for π1's stream `s` at a setup: the values match the reads, the witness
satisfies the compiled circuit at the public limbs of the values' scalars, and it holds `s`. -/
def Pi2Good (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C) (roots : RecSetupRoots)
    (input : Vector UInt8 32) (s : Array UInt8) (vw : List PublicValue × (ℕ → K)) : Prop :=
  List.Forall₂ ReadMatch (D.circuitAt roots.pi1).circuit.reads vw.1 ∧
    (C.G roots).Satisfies (Fa.pubOf roots (publicScalarsOf input.toList vw.1)) (RecCircuit.emb vw.2) ∧
    D.pi1Stream vw.2 = s

/-- **The circuit compiler's completeness**: on a stream whose π1-rec3 graph checks hold, an honest witness exists.
Proved at the real deployment (`Pi2W.pi2WitnessComplete`, from the compiler's completeness checks `completeSlots`,
`completeValues`, `completeGiven`, `completeCover`), which the end theorems use; here it is the input of the
`Pi2Sim` forms that take it as an argument. -/
def Pi2WitnessComplete (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C) : Prop :=
  ∀ (roots : RecSetupRoots) (input : Vector UInt8 32) (s : Array UInt8),
    pi1GraphChecks (D.pi1IvAt roots.pi1) input s = true → ∃ vw, Pi2Good D C Fa roots input s vw

open Classical in
/-- **The witness π2's prover takes**: an honest one if there is one. -/
noncomputable def pi2Choice (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C) (roots : RecSetupRoots)
    (input : Vector UInt8 32) (s : Array UInt8) : List PublicValue × (ℕ → K) :=
  if h : ∃ vw, Pi2Good D C Fa roots input s vw then h.choose else ([], fun _ ↦ 0)

theorem pi2Choice_good {D : RecDeployment} {C : Pi2Circuits D} {Fa : Pi2Facts D C} {roots : RecSetupRoots}
    {input : Vector UInt8 32} {s : Array UInt8} (h : ∃ vw, Pi2Good D C Fa roots input s vw) :
    Pi2Good D C Fa roots input s (pi2Choice D C Fa roots input s) := by
  unfold pi2Choice
  split
  next h' => exact h'.choose_spec
  next h' => exact absurd h h'

/-! ## The prover -/

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- **π2's honest prover** over `H`, `F`: the setup's trees, the IV, the witness, `pi2ProveWith`, π1's openings first. -/
noncomputable def pi2ProverWith (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C) (fuel : ℕ)
    (input : Vector UInt8 32) (p1 : UniStatement.UniProof) : m (Option RecProof) := do
  let trees ← Pi2H.setupTreesWithH H F D
  let iv ← Pi2H.ivOfH H D trees.roots
  let vw := pi2Choice D C Fa trees.roots input p1.stream
  let c := D.circuitAt trees.roots.pi1
  let res ← pi2ProveWith H F fuel (C.G trees.roots) c.circuit c.setupStack trees.pi2 iv input.toList vw.1 vw.2
  return res.map fun x ↦ ⟨x.1, p1.c1, p1.c2, p1.setup, x.2.1, x.2.2.1, x.2.2.2⟩

end With

/-- **π2's honest prover in the random-permutation model**: Keccak-256 the sponge over `π`, `π` itself for WHIR's
proofs of work. -/
noncomputable def pi2Prover (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C) (fuel : ℕ) : Pi2Prover :=
  pi2ProverWith (keccak256With queryPermutation) queryPermutation D C Fa fuel

/-! ## The core: the honest proof is accepted -/

/-- **The prover's run at a pure permutation**: the stream, then the three openings at the arithmetic's claims. -/
theorem pi2ProveWith_run (Hk : List UInt8 → Digest) (F : KeccakState → Id KeccakState) (fuel : ℕ)
    (G : RecPiop.Circuit E) (view : Circuit) (setupStack : Array K) (setupTree : LeanVM.Prover.Tree)
    (iv input : List UInt8) (values : List PublicValue) (w : ℕ → K) :
    Id.run (pi2ProveWith (m := Id) (Pure.pure ∘ Hk) F fuel G view setupStack setupTree iv input values w) =
      (E2ECompleteness.proveOpeningWithH (m := Id) (Pure.pure ∘ Hk) F fuel (layoutsOf G.logN).1
        (proverOut Hk G view setupStack iv input values w).wTree
        (proverOut Hk G view setupStack iv input values w).wStack
        [⟨((Spec.of view).core.run (proverOut Hk G view setupStack iv input values w).inputs).witnessPoint,
          ((Spec.of view).core.run (proverOut Hk G view setupStack iv input values w).inputs).fold⟩]).bind
        fun a ↦
      (E2ECompleteness.proveOpeningWithH (m := Id) (Pure.pure ∘ Hk) F fuel (layoutsOf G.logN).2.2 setupTree setupStack
        [⟨((Spec.of view).core.run (proverOut Hk G view setupStack iv input values w).inputs).setupPoint,
          (proverOut Hk G view setupStack iv input values w).inputs.ξ⟩]).bind fun b ↦
      (E2ECompleteness.proveOpeningWithH (m := Id) (Pure.pure ∘ Hk) F fuel (layoutsOf G.logN).2.1
        (proverOut Hk G view setupStack iv input values w).qTree
        (proverOut Hk G view setupStack iv input values w).qStack
        [⟨((Spec.of view).core.run (proverOut Hk G view setupStack iv input values w).inputs).quotientPoint,
          ((Spec.of view).core.run (proverOut Hk G view setupStack iv input values w).inputs).quotientValue⟩,
         ⟨((Spec.of view).core.run (proverOut Hk G view setupStack iv input values w).inputs).sumPoint,
          ((Spec.of view).core.run (proverOut Hk G view setupStack iv input values w).inputs).sumValue⟩]).bind fun c ↦
      some ((proverOut Hk G view setupStack iv input values w).stream, a, b, c) := rfl

/-- **π2's honest prover at a pure permutation**: `pi2ProveWith` at the setup's trees, the contract's IV and the witness
it takes, π1's openings first. -/
theorem pi2ProverWith_run (Hk : List UInt8 → Digest) (F : KeccakState → Id KeccakState) (D : RecDeployment)
    (C : Pi2Circuits D) (Fa : Pi2Facts D C) (fuel : ℕ) (input : Vector UInt8 32) (p1 : UniStatement.UniProof) :
    Id.run (pi2ProverWith (m := Id) (Pure.pure ∘ Hk) F D C Fa fuel input p1) =
      (Id.run (pi2ProveWith (m := Id) (Pure.pure ∘ Hk) F fuel (C.G (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots)
        (D.circuitAt (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots.pi1).circuit
        (D.circuitAt (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots.pi1).setupStack (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).pi2
        (ivOf D Hk (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots) input.toList
        (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).1
        (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).2)).map
        fun x ↦ ⟨x.1, p1.c1, p1.c2, p1.setup, x.2.1, x.2.2.1, x.2.2.2⟩ := rfl

/-- **π2's honest proof is accepted** at a pure permutation `F` (Keccak-256 `Hk`): for the witness the prover takes
(an honest one, `hgood`), if the prover returns a proof, π2's arithmetic on its inputs passes and its claims hold on its
stacks (off the bad challenges, `halg`), and π1's three openings are accepted (`hpi1`), the contract accepts. -/
theorem pi2_accepts (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (F : KeccakState → Id KeccakState) (Hk : List UInt8 → Digest)
    (fuel : ℕ) (input : Vector UInt8 32) (p1 : UniStatement.UniProof)
    (hgood : Pi2Good D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream
      (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream))
    (hGN : (C.G (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots).logN = 24)
    (hrow : Data.circuit.logRow = (C.G (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots).logW)
    (proof : RecProof)
    (hp : Id.run (pi2ProverWith (m := Id) (Pure.pure ∘ Hk) F D C Fa fuel input p1) = some proof)
    (hroots : C.rootsAt = RecGraph.Emitted.rootsAt)
    (hbad : ¬ BadCopy (C.G (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots)
      (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).2
      (Fa.pubOf (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots
        (publicScalarsOf input.toList (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).1))
      (outOf D Hk (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots (C.G (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots) input
        (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).1
        (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).2).inputs.α
      (outOf D Hk (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots (C.G (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots) input
        (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).1
        (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).2).inputs.β
      (outOf D Hk (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots (C.G (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots) input
        (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).1
        (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).2).inputs.γ)
    (ht : ¬ BadT (C.G (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots)
      (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).2
      (outOf D Hk (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots (C.G (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots) input
        (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).1
        (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).2).inputs.α
      (outOf D Hk (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots (C.G (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots) input
        (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).1
        (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).2).inputs.β
      (outOf D Hk (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots (C.G (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots) input
        (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).1
        (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).2).inputs.γ
      (outOf D Hk (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots (C.G (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots) input
        (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).1
        (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).2).inputs.t)
    (hpi1 : ∃ ops, pi1OpsOf D (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input proof.stream = some ops ∧
      Id.run (Pi2H.openSeqH (m := Id) (Pure.pure ∘ Hk) F (registryOf D.pi1.shape 24) ops proof) = true) :
    (Id.run (Pi2H.contractWithH (m := Id) (Pure.pure ∘ Hk) F D (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input proof)).1 =
      true := by
  have hview : (D.circuitAt (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots.pi1).circuit = Data.circuit := hD.1 _
  obtain ⟨hmatch, hwS, -⟩ := hgood
  have hmatch' := hmatch
  rw [hview] at hmatch
  -- the algebra (`lean-pi2-alg`'s `pi2_honest`), at the prover's inputs and stacks
  obtain ⟨-, -, -, -, -, -, -, -, hi, hwsk, hqsk⟩ := runWith_honest Hk (C.G (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots)
    (D.circuitAt (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots.pi1).circuit
    (D.circuitAt (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots.pi1).setupStack (ivOf D Hk (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots)
    input.toList (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).1
    (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).2 hmatch' (by rw [hview]; exact hrow)
  have halg := pi2_honest Fa (pi2SetupColumns_of_real hD C hroots) (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots
    (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).2
    (publicScalarsOf input.toList (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).1)
    _ _ _ _ (outOf D Hk (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots (C.G (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots) input
        (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).1
        (pi2Choice D C Fa (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input p1.stream).2).inputs.ρ hwS hbad ht

  have htree : (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).pi2 = E2ECompleteness.commitWithH (m := Id) (Pure.pure ∘ Hk)
      (layoutsOf 24).2.2.logN (D.circuitAt (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots.pi1).setupStack := by
    show Pi2H.setupTreeWithH (Pure.pure ∘ Hk)
      (D.circuitAt (Id.run (UniComplete.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D.pi1)).roots) = _
    unfold Pi2H.setupTreeWithH
    have hl : (D.circuitAt (Id.run (UniComplete.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D.pi1)).roots).circuit.logN
        = 24 := by
      unfold RecDeployment.circuitAt
      rw [hD.1]
      rfl
    rw [hl]
    rfl
  -- the prover's run
  have hres := hp
  rw [pi2ProverWith_run, pi2ProveWith_run, hGN] at hres
  generalize hW : E2ECompleteness.proveOpeningWithH (m := Id) (Pure.pure ∘ Hk) F fuel (layoutsOf 24).1 _ _ _ = rW
    at hres
  generalize hS : E2ECompleteness.proveOpeningWithH (m := Id) (Pure.pure ∘ Hk) F fuel (layoutsOf 24).2.2 _ _ _ = rS
    at hres
  generalize hQ : E2ECompleteness.proveOpeningWithH (m := Id) (Pure.pure ∘ Hk) F fuel (layoutsOf 24).2.1 _ _ _ = rQ
    at hres
  cases rW with
  | none => simp at hres
  | some pW =>
    cases rS with
    | none => simp at hres
    | some pS =>
      cases rQ with
      | none => simp at hres
      | some pQ =>
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at hres
        subst hres
        rw [htree] at hS
        exact contract_accepts D F Hk _ (C.G (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots) hview hGN hrow
          (by rw [hD.2.1]; rfl) (by rw [← htree]; rfl) input _ _ hmatch fuel p1.c1 p1.c2 p1.setup pW pS pQ
          (by obtain ⟨h1, h2⟩ := halg; exact ⟨by rw [hi]; exact h1, by rw [hwsk, hqsk, hi]; exact h2⟩)
          hW hS hQ hpi1

/-! ## π2's completeness -/

/-- **π2's completeness error**: the copy argument's `(2^25 + 36) |E|²` bad triples, `t`'s `2^27` bad points, `N` block
calls, `t`'s cache hit `εt`, the proofs of work `εpow`. -/
noncomputable def delta2 (N : ℕ) (εt εpow : ℝ≥0∞) : ℝ≥0∞ := deltaStaged (2 ^ 25 + 36) (2 ^ 27) N εt εpow

/-! ## The algebra's counts at π2's numbers -/

set_option exponentiation.threshold 1024 in
open Classical in
/-- **The copy argument's bad triples at π2's circuit** (`lean-pi2-alg`'s `card_badCopy_le` at `N = 2^24`): at most
`(2^25 + 36) |E|²`, `Holds.badCard`'s `M`. -/
theorem card_badCopy_pi2 {D : RecDeployment} {C : Pi2Circuits D} (Fa : Pi2Facts D C) (roots : RecSetupRoots)
    (w : ℕ → K) (pub : ℕ → List E) :
    (Finset.univ.filter fun v : E × E × E ↦ BadCopy (C.G roots) w pub v.1 v.2.1 v.2.2).card ≤
      (2 ^ 25 + 36) * 2 ^ 384 := by
  refine (card_badCopy_le _ (Fa.valid roots) w pub).trans ?_
  rw [RecPiop.Circuit.N, logN_G Fa roots, LeanVM.Protocol.card_E]
  calc 2 * 2 ^ 24 * (2 ^ 192) ^ 2 = 2 ^ 25 * 2 ^ 384 := by ring
    _ ≤ (2 ^ 25 + 36) * 2 ^ 384 := Nat.mul_le_mul_right _ (by omega)

open Classical in
/-- **`t`'s bad points at π2's circuit** (`lean-pi2-alg`'s `card_badT_le` at `N = 2^24`): off `BadCopy`, at most
`2^27`, `Holds.badTCard`'s `ct`, for `badT` the event `¬ BadCopy ∧ BadT`. -/
theorem card_badT_pi2 {D : RecDeployment} {C : Pi2Circuits D} (Fa : Pi2Facts D C) (roots : RecSetupRoots)
    (w : ℕ → K) (pub : ℕ → List E) (α β γ : E) (hnh : ∃ i < (C.G roots).N, ¬ (C.G roots).IsHole i) :
    ∃ T : Finset E, T.card ≤ 2 ^ 27 ∧
      ∀ t, (¬ BadCopy (C.G roots) w pub α β γ ∧ BadT (C.G roots) w α β γ t) → t ∈ T := by
  by_cases hbad : BadCopy (C.G roots) w pub α β γ
  · exact ⟨∅, by simp, fun t ht ↦ absurd hbad ht.1⟩
  · refine ⟨_, (card_badT_le _ (Fa.valid roots) (by rw [logN_G Fa roots]; omega) w pub α β γ hbad hnh).trans
      (by rw [RecPiop.Circuit.N, logN_G Fa roots]; norm_num), fun t ht ↦ ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht.2⟩

/-- **Named input: π2's completeness experiment in the two-call model** (`Pi2Staged.Holds` at `α`'s input of `536`
bytes, the copy argument's bad triples `(2^25 + 36) |E|²`, `t`'s `2^27` per prior, `N` block calls, `εt`, `εpow`), for
every honest statement: the code-level bridge. Its `rejectGood` is `pi2_accepts` (proved) with the proofs of work's
grinding; its `badCard`, `badTCard` the algebra's counts (`lean-pi2-alg`: `card_badCopy_le`, `card_badT_le`); the rest
(the experiment as the staged two-call run with P1, the graph's check, `pi2Prover` and the contract; its duplex shape;
its cost; nothing of length `32` or `536` hashed before `α`; `t`'s input fresh) the commutation, duplex and cost lemmas
of the composed code, as UniComplete proves them for π1 (`ProverSim`, `ProverDuplex`, `ProverCost`, `ProbTFresh`). -/
def Pi2StagedFacts (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C) (P1 : Pi1Prover D) (fuel N : ℕ)
    (εt εpow : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation rows input q →
      ∃ (S : Pi2Staged) (Bad : S.ρ → Finset (E × E × E)) (badT : S.τ → E → Prop),
        S.Holds D P1 (pi2Prover D C Fa fuel) input rows q 536 Bad badT (2 ^ 25 + 36) (2 ^ 27) N εt εpow

/-- **π2's completeness**: `RecCompleteness2 D P1 (pi2Prover D C Fa fuel) (delta2 N εt εpow)`. -/
theorem recCompleteness2_pi2 {D : RecDeployment} {C : Pi2Circuits D} {Fa : Pi2Facts D C} {P1 : Pi1Prover D}
    {fuel N : ℕ} {εt εpow : ℝ≥0∞} (h : Pi2StagedFacts D C Fa P1 fuel N εt εpow) :
    RecCompleteness2 D P1 (pi2Prover D C Fa fuel) (delta2 N εt εpow) :=
  recCompleteness2_of_staged h

/-- **`δ2` in bits**: below `2^-164` for at most `2^50` block calls, `εt ≤ 2^-200` and `εpow ≤ 2^-300` (the copy
argument's `2^-166`, `t`'s `2^-165`, the rest below `2^-170` each). -/
theorem delta2_le {N : ℕ} {εt εpow : ℝ≥0∞} (hN : N ≤ 2 ^ 50) (ht : εt ≤ (2 : ℝ≥0∞)⁻¹ ^ 200)
    (hp : εpow ≤ (2 : ℝ≥0∞)⁻¹ ^ 300) : delta2 N εt εpow ≤ (2 : ℝ≥0∞)⁻¹ ^ 164 := by
  set x : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ 170 with hx
  have hsmall : ∀ k, 170 ≤ k → (2 : ℝ≥0∞)⁻¹ ^ k ≤ x := fun k hk ↦ E2ECompleteness.inv_pow_le_inv_pow hk
  have ha : (1 : ℝ≥0∞) / 2 ^ 256 ≤ x := by
    rw [ENNReal.div_eq_inv_mul, mul_one, ENNReal.inv_pow]
    exact hsmall 256 (by norm_num)
  have hb : ((2 ^ 25 + 36 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ 2 ^ 4 * x := by
    calc ((2 ^ 25 + 36 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ 2 ^ 26 * (2 : ℝ≥0∞)⁻¹ ^ (166 + 26) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
          gcongr
          norm_num
      _ = (2 : ℝ≥0∞)⁻¹ ^ 166 := E2ECompleteness.two_pow_mul_inv_pow 26 166
      _ = 2 ^ 4 * x := (E2ECompleteness.two_pow_mul_inv_pow 4 166).symm
  have hc : ((2 ^ 27 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ 2 ^ 5 * x := by
    refine le_of_eq ?_
    calc ((2 ^ 27 : ℕ) : ℝ≥0∞) / 2 ^ 192 = 2 ^ 27 * (2 : ℝ≥0∞)⁻¹ ^ (165 + 27) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
          norm_num
      _ = (2 : ℝ≥0∞)⁻¹ ^ 165 := E2ECompleteness.two_pow_mul_inv_pow 27 165
      _ = 2 ^ 5 * x := (E2ECompleteness.two_pow_mul_inv_pow 5 165).symm
  have hd : εt ≤ x := ht.trans (hsmall 200 (by norm_num))
  have he : εpow ≤ x := hp.trans (hsmall 300 (by norm_num))
  have hf : rpmError N ≤ x := by
    calc rpmError N ≤ rpmError (2 ^ 50) := by
          unfold rpmError
          gcongr
      _ = 2 ^ (50 * 2) * (2 : ℝ≥0∞)⁻¹ ^ (408 + 50 * 2) := by
          rw [rpmError, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
      _ = (2 : ℝ≥0∞)⁻¹ ^ 408 := E2ECompleteness.two_pow_mul_inv_pow _ 408
      _ ≤ x := hsmall 408 (by norm_num)
  unfold delta2 deltaStaged
  calc _ ≤ (x + 2 ^ 4 * x) + (x + 2 ^ 5 * x) + x + x :=
        add_le_add (add_le_add (add_le_add (add_le_add ha hb) (add_le_add hd hc)) he) hf
    _ = 52 * x := by ring
    _ ≤ 2 ^ 6 * x := by gcongr; norm_num
    _ = (2 : ℝ≥0∞)⁻¹ ^ 164 := by rw [hx]; exact E2ECompleteness.two_pow_mul_inv_pow 6 164

/-- **The recursive verifier's completeness end to end, with π2's honest prover**: for π1-rec3's prover `P1`, under π2's
staged facts (named), π1-rec3's completeness at Keccak-f[1600] and its honest proofs' hazard (the Fiat–Shamir heuristic,
named), the composed prover's proof is rejected with probability at most `δ1 + δh + delta2 N εt εpow`. -/
theorem recCompleteness_pi2_fs (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1 : Pi1Prover D) (fuel N : ℕ) (εt εpow : ℝ≥0∞) (h2 : Pi2StagedFacts D C Fa P1 fuel N εt εpow) (δ1 δh : ℝ≥0∞)
    (h1 : Pi1CompletenessKeccak D P1 δ1) (hh : Pi1HazardKeccakHonest D P1 δh) :
    RecCompletenessWith D (composeProver D P1 (pi2Prover D C Fa fuel)) (δ1 + δh + delta2 N εt εpow) :=
  recCompleteness_end_fs D hD P1 (pi2Prover D C Fa fuel) _ (recCompleteness2_pi2 h2) δ1 δh h1 hh

end RecCompose.Pi2E

/-- info: 'RecCompose.Pi2E.pi2_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2E.pi2_accepts

/-- info: 'RecCompose.Pi2E.recCompleteness2_pi2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2E.recCompleteness2_pi2

/-- info: 'RecCompose.Pi2E.card_badCopy_pi2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2E.card_badCopy_pi2

/-- info: 'RecCompose.Pi2E.card_badT_pi2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2E.card_badT_pi2

/-- info: 'RecCompose.Pi2E.delta2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2E.delta2_le

/-- info: 'RecCompose.Pi2E.recCompleteness_pi2_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2E.recCompleteness_pi2_fs
