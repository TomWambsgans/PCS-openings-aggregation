-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import E2ECompleteness.Experiment
import E2ECompleteness.Chain

/-!
# The two-call experiment in the chain's shape

`expH stmt w coins` (`Experiment.lean`: the setup, the honest prover, the verifier, with Keccak-256
and Keccak-f[1600] the calls) is the chain's shape `staged challengeOf A B C` (`Chain.lean`), its
verdict the first component (`expH_eq_staged`):

* `stageA`: the setup's tree, the prover's index and witness trees, the label's hash `s₀`; it
  returns the witness root's two scalars;
* `stageB`: from `α, β, γ` (the low bits of `s₁, s₂, s₃`) the quotient table and its tree; it
  returns the quotient root's two scalars;
* `stageC`: from `t` (the low bits of `s₄`) the values, the reduction, the three openings, and the
  verifier on the proof.

Each stage is the corresponding stretch of `proveWithH` copied verbatim.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Prover (Tree)
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript

set_option autoImplicit false

namespace E2ECompleteness

section Stages

variable (stmt : Statement) (w : Secret) (coins : Masks × Padding × Padding)

/-- What the first stage hands on: the setup's root, the index and witness trees, the witness
table's coefficients, the masks' entries and the witness stack. -/
abbrev AuxA : Type := Digest × Tree × Tree × Array K × Array K × Array K

/-- **Stage A**: the setup, the prover's index and witness trees, and the label's hash `s₀`. -/
def stageA : OracleComp KeccakCalls (AuxA × Digest × (E × E)) := do
  let idx ← setupWithH callKeccak256
  let circuit := membership logRows
  let cells := circuit.cells (membershipInputs w)
  let mv := cellVars circuit.logRows
  let sigmaHat := circuit.wiringTable
  let indexTree ← commitWithH callKeccak256 mv sigmaHat
  let wHat := coefficients mv 0 cells
  let mask := maskEntries coins.1
  let wStack := witnessStack circuit.logRows wHat mask coins.2.1
  let witnessTree ← commitWithH callKeccak256 (mv + 1) wStack
  let s₀ ← callKeccak256 (label indexTree.root stmt)
  return ((idx, indexTree, witnessTree, wHat, mask, wStack), s₀, digestScalars witnessTree.root)

/-- The quotient stack from `α, β, γ` (`proveWithH` between `γ` and the quotient tree). -/
def quotientStackOf (wHat mask : Array K) (α β γ : E) : Array K :=
  let circuit := membership logRows
  let cells := circuit.cells (membershipInputs w)
  let mv := cellVars circuit.logRows
  let n := 2 ^ mv
  let big := 4 * n
  let block := 2 ^ region
  let sigmaHat := circuit.wiringTable
  let h : Array E := Array.ofFn (n := n) fun i ↦
    let common := α + ofK (cells.getD i.val 0)
    (common + β * ofK (point i.val))⁻¹ + (common + β * ofK (point (circuit.sigma.getD i.val 0)))⁻¹ +
      if i.val < block then publicCellWeight i.val γ * ofK (cells.getD i.val 0) else 0
  let hHat := coefficients mv 0 h
  let offset := betaAt (mv + 2)
  let offsets := chain offset (mv + 1)
  let wValues : Array K := values (mv + 2) offset (Array.ofFn (n := big) fun i ↦
    if i.val < n then wHat.getD i.val 0 else mask.getD (i.val - n) 0)
  let sigmaValues : Array K := values (mv + 2) offset (Array.ofFn (n := big) fun i ↦
    sigmaHat.getD i.val 0)
  let q₀ : Array E := values (mv + 2) offset (Array.ofFn (n := big) fun i ↦ hHat.getD i.val 0)
  let b := coordinates region
  let tau := rowVanishing mv
  let rowPoly (x : K) : K := ((chain x (mv - 1)).zip tau).foldl (fun acc (w, t) ↦ acc + t * w) 0
  let gammas : List E := [γ, γ * γ, (γ * γ) * (γ * γ)]
  let blocks : Array (Array E × K × Array K) := Array.ofFn (n := big / block) fun hi ↦
    let base := hi.val * block
    let wAt (k : ℕ) : K := offsets.getD k 0 + point (base >>> k)
    let indicator := (List.range' region (mv - region)).foldl (fun acc k ↦ acc * (1 + wAt k)) 1
    let weights : Array E :=
      if indicator = 0 then #[ofK indicator]
      else (List.range region).foldl
        (fun ws k ↦
          let shift := (List.range' k (region - k)).foldl
            (fun acc j ↦ acc + b.getD (j - k) 0 * wAt j) 0
          let slope : E := 1 + (coordinateWeight k).getD (gammas.getD (k - 8) 0)
          let low := 1 + slope * ofK shift
          ws.map (· * low) ++ ws.map (· * (low + slope)))
        #[ofK indicator]
    let rowBase := rowPoly (offset + point base)
    (weights, (wAt mv)⁻¹, Array.ofFn (n := 4) fun r ↦ (rowBase + rowPoly (point r.val))⁻¹)
  let qValues : Array E := Array.ofFn (n := big) fun i ↦
    let (weights, cellVanishing, _) := blocks.getD (i.val / block) (#[], 0, #[])
    let w := wValues.getD i.val 0
    let common := α + ofK w
    let d := common + β * ofK (offset + point i.val)
    let dNext := common + β * ofK (sigmaValues.getD i.val 0)
    let pub := if i.val % block < weights.size then weights.getD (i.val % block) 0 * ofK w else 0
    ((q₀.getD i.val 0 + pub) * d * dNext + d + dNext) * ofK cellVanishing
  let qGateValues : Array K := Array.ofFn (n := big) fun i ↦
    let (_, _, rowInv) := blocks.getD (i.val / block) (#[], 0, #[])
    let at_ (j : ℕ) : K := wValues.getD j 0
    let (x, y, cc, v) := (at_ i.val, at_ (i.val ^^^ 1), at_ (i.val ^^^ 2), at_ (i.val ^^^ 3))
    (v + x + cc + y * cc) * rowInv.getD (i.val % 4) 0
  let qHat := coefficients (mv + 2) offset qValues
  let qGateHat := coefficients (mv + 2) offset qGateValues
  quotientStack circuit.logRows hHat qHat qGateHat coins.2.2

/-- **Stage B**: from `s₁, s₂, s₃` the quotient stack and its tree. -/
def stageB (a : AuxA) (s₁ s₂ s₃ : Digest) : OracleComp KeccakCalls ((Tree × Array K) × (E × E)) := do
  let qStack := quotientStackOf w coins a.2.2.2.1 a.2.2.2.2.1 (challengeOf s₁) (challengeOf s₂)
    (challengeOf s₃)
  let quotientTree ← commitWithH callKeccak256 (cellVars (membership logRows).logRows + 4) qStack
  return ((quotientTree, qStack), digestScalars quotientTree.root)

/-- The prover's last stretch from `t`: the values, the reduction, the three openings. -/
def proverTail (a : AuxA) (bq : Tree × Array K) (t : E) :
    OracleComp KeccakCalls (Option PcsQuotient.Proof) := do
  let circuit := membership logRows
  let mv := cellVars circuit.logRows
  let sigmaHat := circuit.wiringTable
  let indexTree := a.2.1
  let witnessTree := a.2.2.1
  let wHat := a.2.2.2.1
  let mask := a.2.2.2.2.1
  let wStack := a.2.2.2.2.2
  let quotientTree := bq.1
  let qStack := bq.2
  let witnessRoot := digestScalars witnessTree.root
  let quotientRoot := digestScalars quotientTree.root
  let digits := digitsOf t mv
  let av : Vector E 4 := Vector.ofFn fun j ↦
    novelEval wHat j.val 4 ((digits.drop 2).take (mv - 2)) +
      digits.getD mv 0 * novelEval mask j.val 4 ((digits.drop 2).take 2)
  let next := novelEval sigmaHat 0 1 (digits.take mv)
  let proof : ReductionProof := ⟨witnessRoot, quotientRoot, av, next⟩
  match ← reduceWithH callKeccak256 circuit.logRows indexTree.root stmt proof with
  | none => return none
  | some r =>
    let some witness ← proveOpeningWithH callKeccak256 callKeccakF1600 nonceFuel
      (witnessLayout circuit.logRows) witnessTree wStack [r.claims.witness] | return none
    let some wiring ← proveOpeningWithH callKeccak256 callKeccakF1600 nonceFuel
      (wiringLayout circuit.logRows) indexTree sigmaHat [r.claims.wiring] | return none
    let some quotient ← proveOpeningWithH callKeccak256 callKeccakF1600 nonceFuel
      (quotientLayout circuit.logRows) quotientTree qStack [r.claims.quotient, r.claims.sum]
      | return none
    return some ⟨proof, witness, wiring, quotient⟩

/-- **Stage C**: the prover's tail from `t = challengeOf s₄`, then the verifier. -/
def stageC (a : AuxA) (bq : Tree × Array K) (_s₁ _s₂ _s₃ s₄ : Digest) :
    OracleComp KeccakCalls Bool := do
  match ← proverTail stmt w a bq (challengeOf s₄) with
  | none => return false
  | some proof => verifyWithH callKeccak256 callKeccakF1600 logRows a.1 stmt proof

/-- **The staged run** of the two-call experiment. -/
def stagedRun : OracleComp KeccakCalls (Bool × (E × E × E)) :=
  staged challengeOf (stageA stmt w coins) (stageB w coins) (stageC stmt w)

end Stages

/-- **The two-call experiment is the staged run's verdict.** -/
set_option maxHeartbeats 400000 in
theorem expH_eq_staged (stmt : Statement) (w : Secret) (coins : Masks × Padding × Padding) :
    expH stmt w coins = (·.1) <$> stagedRun stmt w coins := by
  simp only [expH, proverWithH, proveWithH, stagedRun, staged, stageA, stageB, stageC, proverTail,
    quotientStackOf, startWithH, squeezeWithH, bind_assoc, pure_bind, map_bind, map_pure]
  rfl

end E2ECompleteness
