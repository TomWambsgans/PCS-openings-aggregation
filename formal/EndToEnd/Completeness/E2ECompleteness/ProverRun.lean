-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): Merkle trees (`Tree`), `digestScalars`, `digestOfScalars_digestScalars`.
import E2ECompleteness.ProverDefs
import E2ECompleteness.Chain

/-!
# The honest prover's run at pure Keccak-256 and Keccak-f[1600]

At a hash function `H` and a permutation `F` (the `Id` monad), the Statement's prover
(`proveWithH`, `proveSpec`) is a function. Here its stages are named:

* `chainH`: the reduction's chain on a reduction proof: `α, β, γ` after the witness root, `t` after
  the quotient root, `ρ` after the values (`transcript.rs`), as `reduceWithH` computes it;
* **`chainChallenges`**: the staged run's `(α, β, t)` (`Chain.lean`'s `staged`:
  `s₁ = H(s₀ ‖ r₁)`, `s₂ = H(s₁)`, `s₄ = H(s₃ ‖ r₂)`), the chain's (`chainChallenges_eq`);
* `reduceWithH_id`: `reduceWithH` on a proof whose roots name digests is `claimsAt` at the chain's
  challenges;
* `Run`, `runOf`: what the prover computes before its openings, and **`proveSpec_id`**: the prover
  is its run, then the reduction on its own proof, then the three openings.
-/

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript

set_option autoImplicit false

namespace E2ECompleteness

section Pure

variable (H : Bytes → Digest)

/-! ## The chain -/

/-- `startWithH` at a function. -/
theorem startWithH_id (label : List UInt8) :
    startWithH (m := Id) H label = (⟨H label, []⟩ : Chain) := rfl

/-- `squeezeWithH` at a function. -/
theorem squeezeWithH_id (c : Chain) :
    squeezeWithH (m := Id) H c =
      (challengeOf (H (digestBytes c.state ++ c.pending.flatMap scalarBytes)),
        (⟨H (digestBytes c.state ++ c.pending.flatMap scalarBytes), []⟩ : Chain)) := rfl

/-- **The reduction's chain** on a reduction proof, from the circuit's commitment `ir`: the challenges
`α, β, γ, t, ρ`. -/
def chainH (ir : Digest) (stmt : Statement) (p : ReductionProof) : E × E × E × E × E :=
  let c₁ := ((⟨H (label ir stmt), []⟩ : Chain).absorb p.witnessRoot.1).absorb p.witnessRoot.2
  let s₁ := squeezeWithH (m := Id) H c₁
  let s₂ := squeezeWithH (m := Id) H s₁.2
  let s₃ := squeezeWithH (m := Id) H s₂.2
  let c₄ := (s₃.2.absorb p.quotientRoot.1).absorb p.quotientRoot.2
  let s₄ := squeezeWithH (m := Id) H c₄
  let c₅ := (p.values.toList.foldl Chain.absorb s₄.2).absorb p.next
  let s₅ := squeezeWithH (m := Id) H c₅
  (s₁.1, s₂.1, s₃.1, s₄.1, s₅.1)

/-- **The staged run's challenges** `(α, β, t)` (`Chain.lean`'s `staged` with `challengeOf`):
`s₀ = H(label)`, `s₁ = H(s₀ ‖ r₁)`, `s₂ = H(s₁)`, `s₃ = H(s₂)`, `s₄ = H(s₃ ‖ r₂)`. -/
def chainChallenges (ir : Digest) (stmt : Statement) (p : ReductionProof) : E × E × E :=
  let s₀ := H (label ir stmt)
  let s₁ := H (chainIn s₀ p.witnessRoot)
  let s₂ := H (digestBytes s₁)
  let s₃ := H (digestBytes s₂)
  let s₄ := H (chainIn s₃ p.quotientRoot)
  (challengeOf s₁, challengeOf s₂, challengeOf s₄)

theorem chainIn_eq (s : Digest) (r : E × E) :
    digestBytes s ++ ([r.1] ++ [r.2]).flatMap scalarBytes = chainIn s r := by
  simp [chainIn, List.append_assoc]

/-- **The staged run's challenges are the chain's** `α, β, t`. -/
theorem chainChallenges_eq (ir : Digest) (stmt : Statement) (p : ReductionProof) :
    chainChallenges H ir stmt p =
      ((chainH H ir stmt p).1, (chainH H ir stmt p).2.1, (chainH H ir stmt p).2.2.2.1) := by
  simp only [chainChallenges, chainH, squeezeWithH_id, Chain.absorb, List.nil_append,
    List.flatMap_nil, List.append_nil, chainIn_eq]

/-- **The reduction at a function**: on a proof whose two roots name digests, `reduceWithH` is
`claimsAt` at the chain's challenges. -/
theorem reduceWithH_id (ir : Digest) (stmt : Statement) (p : ReductionProof) {r₁ r₂ : Digest}
    (h₁ : digestOfScalars p.witnessRoot = some r₁) (h₂ : digestOfScalars p.quotientRoot = some r₂) :
    reduceWithH (m := Id) H 22 ir stmt p =
      (claimsAt 22 stmt (chainH H ir stmt p).1 (chainH H ir stmt p).2.1 (chainH H ir stmt p).2.2.1
        (chainH H ir stmt p).2.2.2.1 (chainH H ir stmt p).2.2.2.2 p.values p.next).map
        fun claims ↦ ⟨r₁, r₂, claims⟩ := by
  have hs : Supported 22 := by decide
  simp only [reduceWithH, hs, not_true_eq_false, if_false, h₁, h₂]
  rfl

/-! ## The prover's run -/

/-- What the prover computes before its openings. -/
structure Run where
  sigmaHat : Array K
  indexTree : Tree
  wHat : Array K
  mask : Array K
  wStack : Array K
  witnessTree : Tree
  α : E
  β : E
  γ : E
  hHat : Array E
  qHat : Array E
  qGateHat : Array K
  qStack : Array K
  quotientTree : Tree
  t : E
  proof : ReductionProof

/-- **The prover's run** (`proveSpec` up to its reduction), at `H`. -/
def runOf (circuit : Circuit) (stmt : Statement) (cells : Array K) (masks : Masks)
    (witnessPad quotientPad : Padding) : Run :=
  let mv := cellVars circuit.logRows
  let sigmaHat := circuit.wiringTable
  let indexTree := commitWithH (m := Id) H mv sigmaHat
  let wHat := coefficients mv 0 cells
  let mask := maskEntries masks
  let wStack := witnessStack circuit.logRows wHat mask witnessPad
  let witnessTree := commitWithH (m := Id) H (mv + 1) wStack
  let c₀ : Chain := ⟨H (label indexTree.root stmt), []⟩
  let witnessRoot := digestScalars witnessTree.root
  let c := (c₀.absorb witnessRoot.1).absorb witnessRoot.2
  let s₁ := squeezeWithH (m := Id) H c
  let s₂ := squeezeWithH (m := Id) H s₁.2
  let s₃ := squeezeWithH (m := Id) H s₂.2
  let α := s₁.1
  let β := s₂.1
  let γ := s₃.1
  let hHat := coefficients mv 0 (hValues circuit.logRows cells circuit.sigma α β γ)
  let wValues := wValuesOf circuit.logRows wHat mask
  let blocks := blocksOf circuit.logRows γ
  let qHat := coefficients (mv + 2) (betaAt (mv + 2))
    (qValuesOf circuit.logRows wValues (sigmaValuesOf circuit.logRows sigmaHat)
      (q0Of circuit.logRows hHat) blocks α β)
  let qGateHat := coefficients (mv + 2) (betaAt (mv + 2)) (qGateValuesOf circuit.logRows wValues blocks)
  let qStack := quotientStack circuit.logRows hHat qHat qGateHat quotientPad
  let quotientTree := commitWithH (m := Id) H (mv + 4) qStack
  let quotientRoot := digestScalars quotientTree.root
  let c₄ := (s₃.2.absorb quotientRoot.1).absorb quotientRoot.2
  let t := (squeezeWithH (m := Id) H c₄).1
  ⟨sigmaHat, indexTree, wHat, mask, wStack, witnessTree, α, β, γ, hHat, qHat, qGateHat, qStack,
    quotientTree, t, ⟨witnessRoot, quotientRoot, rowValuesAt circuit.logRows wHat mask t,
      nextAt circuit.logRows sigmaHat t⟩⟩

variable (F : KeccakState → KeccakState)

/-- Bind in `Id`. -/
theorem id_bind {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl

/-- Return in `Id`. -/
theorem id_pure {α : Type} (a : α) : (pure a : Id α) = a := rfl

section Opaque

attribute [local irreducible] commitWithH finishSpec witnessStack quotientStack Domain.coefficients
  Domain.values hValues qValuesOf qGateValuesOf

/-- **The prover at a function** is its run, then its end (`finishSpec`) on the run. -/
theorem proveSpec_id (fuel : ℕ) (circuit : Circuit) (stmt : Statement) (cells : Array K)
    (masks : Masks) (witnessPad quotientPad : Padding) :
    proveSpec (m := Id) H F fuel circuit stmt cells masks witnessPad quotientPad =
      finishSpec (m := Id) H F fuel circuit.logRows stmt
        (runOf H circuit stmt cells masks witnessPad quotientPad).indexTree
        (runOf H circuit stmt cells masks witnessPad quotientPad).witnessTree
        (runOf H circuit stmt cells masks witnessPad quotientPad).quotientTree
        (runOf H circuit stmt cells masks witnessPad quotientPad).sigmaHat
        (runOf H circuit stmt cells masks witnessPad quotientPad).wStack
        (runOf H circuit stmt cells masks witnessPad quotientPad).qStack
        (runOf H circuit stmt cells masks witnessPad quotientPad).proof := by
  simp only [proveSpec, id_bind, startWithH_id, squeezeWithH_id]
  rfl

end Opaque

/-- **The prover's end at a function, when it returns a proof**: the reduction on its proof returned
claims, each opening a proof, and the proof is the reduction's proof with the three. -/
theorem finishSpec_id_some {fuel logRows : ℕ} {stmt : Statement}
    {indexTree witnessTree quotientTree : Tree} {sigmaHat wStack qStack : Array K}
    {proof : ReductionProof} {π : PcsQuotient.Proof}
    (h : finishSpec (m := Id) H F fuel logRows stmt indexTree witnessTree quotientTree sigmaHat
      wStack qStack proof = some π) :
    ∃ red, reduceWithH (m := Id) H logRows indexTree.root stmt proof = some red ∧
      proveOpeningWithH (m := Id) H F fuel (witnessLayout logRows) witnessTree wStack
        [red.claims.witness] = some π.witness ∧
      proveOpeningWithH (m := Id) H F fuel (wiringLayout logRows) indexTree sigmaHat
        [red.claims.wiring] = some π.wiring ∧
      proveOpeningWithH (m := Id) H F fuel (quotientLayout logRows) quotientTree qStack
        [red.claims.quotient, red.claims.sum] = some π.quotient ∧
      π.reduction = proof := by
  simp only [finishSpec, id_bind, id_pure] at h
  generalize hr : reduceWithH (m := Id) H logRows indexTree.root stmt proof = r at h
  rcases r with _ | red
  · cases h
  simp only at h
  generalize hw : proveOpeningWithH (m := Id) H F fuel (witnessLayout logRows) witnessTree wStack
    [red.claims.witness] = ow at h
  rcases ow with _ | πW
  · cases h
  simp only at h
  generalize hs : proveOpeningWithH (m := Id) H F fuel (wiringLayout logRows) indexTree sigmaHat
    [red.claims.wiring] = os at h
  rcases os with _ | πσ
  · cases h
  simp only at h
  generalize hq : proveOpeningWithH (m := Id) H F fuel (quotientLayout logRows) quotientTree qStack
    [red.claims.quotient, red.claims.sum] = oq at h
  rcases oq with _ | πQ
  · cases h
  obtain rfl := Option.some.inj h
  exact ⟨red, rfl, hw, hs, hq, rfl⟩

/-! ### The run's fields -/

/-- The witness stack is the layout's stack of `witnessEntry`. -/
theorem witnessStack_eq (lr : ℕ) (wHat mask : Array K) (pad : Padding) :
    witnessStack lr wHat mask pad =
      (witnessLayout lr).stackOf (witnessEntry (2 ^ cellVars lr) wHat mask) pad := by
  unfold witnessStack
  rfl

/-- The quotient stack is the layout's stack of `quotientEntry`. -/
theorem quotientStack_eq (lr : ℕ) (hHat qHat : Array E) (qGateHat : Array K) (pad : Padding) :
    quotientStack lr hHat qHat qGateHat pad =
      (quotientLayout lr).stackOf (quotientEntry lr hHat qHat qGateHat) pad := by
  unfold quotientStack
  rfl

section Fields

attribute [local irreducible] commitWithH Layout.stackOf witnessStack quotientStack
  Domain.coefficients Domain.values hValues qValuesOf qGateValuesOf

variable (circuit : Circuit) (stmt : Statement) (cells : Array K) (masks : Masks)
  (wp qp : Padding)

theorem runOf_sigmaHat : (runOf H circuit stmt cells masks wp qp).sigmaHat = circuit.wiringTable :=
  rfl

theorem runOf_indexTree : (runOf H circuit stmt cells masks wp qp).indexTree =
    commitWithH (m := Id) H (cellVars circuit.logRows) circuit.wiringTable := rfl

theorem runOf_wHat : (runOf H circuit stmt cells masks wp qp).wHat =
    coefficients (cellVars circuit.logRows) 0 cells := rfl

theorem runOf_mask : (runOf H circuit stmt cells masks wp qp).mask = maskEntries masks := rfl

theorem runOf_wStack : (runOf H circuit stmt cells masks wp qp).wStack =
    witnessStack circuit.logRows (runOf H circuit stmt cells masks wp qp).wHat
      (runOf H circuit stmt cells masks wp qp).mask wp := rfl

theorem runOf_witnessTree : (runOf H circuit stmt cells masks wp qp).witnessTree =
    commitWithH (m := Id) H (cellVars circuit.logRows + 1)
      (runOf H circuit stmt cells masks wp qp).wStack := rfl

theorem runOf_hHat : (runOf H circuit stmt cells masks wp qp).hHat =
    coefficients (cellVars circuit.logRows) 0 (hValues circuit.logRows cells circuit.sigma
      (runOf H circuit stmt cells masks wp qp).α (runOf H circuit stmt cells masks wp qp).β
      (runOf H circuit stmt cells masks wp qp).γ) := rfl

theorem runOf_qHat : (runOf H circuit stmt cells masks wp qp).qHat =
    coefficients (cellVars circuit.logRows + 2) (betaAt (cellVars circuit.logRows + 2))
      (qValuesOf circuit.logRows
        (wValuesOf circuit.logRows (runOf H circuit stmt cells masks wp qp).wHat
          (runOf H circuit stmt cells masks wp qp).mask)
        (sigmaValuesOf circuit.logRows (runOf H circuit stmt cells masks wp qp).sigmaHat)
        (q0Of circuit.logRows (runOf H circuit stmt cells masks wp qp).hHat)
        (blocksOf circuit.logRows (runOf H circuit stmt cells masks wp qp).γ)
        (runOf H circuit stmt cells masks wp qp).α (runOf H circuit stmt cells masks wp qp).β) :=
  rfl

theorem runOf_qGateHat : (runOf H circuit stmt cells masks wp qp).qGateHat =
    coefficients (cellVars circuit.logRows + 2) (betaAt (cellVars circuit.logRows + 2))
      (qGateValuesOf circuit.logRows
        (wValuesOf circuit.logRows (runOf H circuit stmt cells masks wp qp).wHat
          (runOf H circuit stmt cells masks wp qp).mask)
        (blocksOf circuit.logRows (runOf H circuit stmt cells masks wp qp).γ)) := rfl

theorem runOf_qStack : (runOf H circuit stmt cells masks wp qp).qStack =
    quotientStack circuit.logRows (runOf H circuit stmt cells masks wp qp).hHat
      (runOf H circuit stmt cells masks wp qp).qHat (runOf H circuit stmt cells masks wp qp).qGateHat
      qp := rfl

theorem runOf_quotientTree : (runOf H circuit stmt cells masks wp qp).quotientTree =
    commitWithH (m := Id) H (cellVars circuit.logRows + 4)
      (runOf H circuit stmt cells masks wp qp).qStack := rfl

theorem runOf_values : (runOf H circuit stmt cells masks wp qp).proof.values =
    rowValuesAt circuit.logRows (runOf H circuit stmt cells masks wp qp).wHat
      (runOf H circuit stmt cells masks wp qp).mask (runOf H circuit stmt cells masks wp qp).t := rfl

theorem runOf_next : (runOf H circuit stmt cells masks wp qp).proof.next =
    nextAt circuit.logRows (runOf H circuit stmt cells masks wp qp).sigmaHat
      (runOf H circuit stmt cells masks wp qp).t := rfl

end Fields

/-- The run's roots name its trees' roots. -/
theorem runOf_roots (circuit : Circuit) (stmt : Statement) (cells : Array K) (masks : Masks)
    (witnessPad quotientPad : Padding) :
    digestOfScalars (runOf H circuit stmt cells masks witnessPad quotientPad).proof.witnessRoot =
        some (runOf H circuit stmt cells masks witnessPad quotientPad).witnessTree.root ∧
      digestOfScalars (runOf H circuit stmt cells masks witnessPad quotientPad).proof.quotientRoot =
        some (runOf H circuit stmt cells masks witnessPad quotientPad).quotientTree.root :=
  ⟨digestOfScalars_digestScalars _, digestOfScalars_digestScalars _⟩

/-- **The run's challenges are the chain's** on its own proof. -/
theorem runOf_chain (circuit : Circuit) (stmt : Statement) (cells : Array K) (masks : Masks)
    (witnessPad quotientPad : Padding) :
    let r := runOf H circuit stmt cells masks witnessPad quotientPad
    (chainH H r.indexTree.root stmt r.proof).1 = r.α ∧
      (chainH H r.indexTree.root stmt r.proof).2.1 = r.β ∧
      (chainH H r.indexTree.root stmt r.proof).2.2.1 = r.γ ∧
      (chainH H r.indexTree.root stmt r.proof).2.2.2.1 = r.t :=
  ⟨rfl, rfl, rfl, rfl⟩

end Pure

end E2ECompleteness

/-- info: 'E2ECompleteness.chainChallenges_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.chainChallenges_eq

/-- info: 'E2ECompleteness.proveSpec_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.proveSpec_id
