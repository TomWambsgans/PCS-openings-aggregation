-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Transcribed from `formal/Statement` (`PcsQuotient`: `Transcript.lean`, `Reduction.lean`,
-- `Opening.lean`, `Verifier.lean`, `Circuit.lean`, `Prover.lean`, `Security.lean`), with Keccak-256 an
-- explicit call. Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0): the runners with a hash (`runWithHash`, `runFromWithHash`,
-- `buildTreeWithHash`), their equalities with the runners over a permutation
-- (`run_eq_withHash`, `runFrom_eq_withHash`, `buildTreeM_eq_withHash`) and their simulation
-- lemmas (`simulateQ_run`, `simulateQ_buildTreeM`, `simulateQ_absorb`, `simulateQ_findNonceM`).
import PcsQuotient.Security
import LeanVM.Protocol.WithHashBridge
import LeanVM.Protocol.Compile.Rom.Bridge
import LeanVM.Protocol.Compile.Rom.Prover

/-!
# The Statement's code with Keccak-256 an explicit call

The Statement's setup, honest prover and verifier are written over a permutation `F`, Keccak-256 the
sponge over it (`keccak256With F`). Here each is rewritten with Keccak-256 a separate function `H`
(`…H H F`), as mumbai's runners are (`runWithHash`, `runFromWithHash`, `buildTreeWithHash`):

* **`…_eq`**: at `H = keccak256With F` it is the Statement's (`rfl`, or mumbai's `…_eq_withHash`);
* **`simulateQ_…`**: over the two calls (`callKeccak256`, `callKeccakF1600`) it commutes with any
  simulation (`implH`, `implF`).

So the Statement's code over `π` is the two-call code answered over `π`
(`keccakCallsOverQueryPermutation`), the form the random-permutation model's transfer takes.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript
open LeanVM.Protocol.Compile.Rom (implH implF simulateQ_queryH simulateQ_queryF simulateQ_absorb
  simulateQ_squeeze simulateQ_run)

set_option autoImplicit false

namespace E2ECompleteness

section With

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KeccakState → m KeccakState)

/-- `Chain.startWith` with Keccak-256 `H`. -/
def startWithH (label : List UInt8) : m Chain := do
  return ⟨← H label, []⟩

/-- `Chain.squeezeWith` with Keccak-256 `H`. -/
def squeezeWithH (c : Chain) : m (E × Chain) := do
  let state ← H (digestBytes c.state ++ c.pending.flatMap scalarBytes)
  return (challengeOf state, ⟨state, []⟩)

/-- `reduceWith` with Keccak-256 `H`. -/
def reduceWithH (logRows : ℕ) (indexRoot : Digest) (stmt : Statement) (p : ReductionProof) :
    m (Option Reduced) := do
  if ¬ Supported logRows then return none
  let c ← startWithH H (label indexRoot stmt)
  let c := (c.absorb p.witnessRoot.1).absorb p.witnessRoot.2
  match digestOfScalars p.witnessRoot with
  | none => return none
  | some witnessRoot =>
    let (α, c) ← squeezeWithH H c
    let (β, c) ← squeezeWithH H c
    let (γ, c) ← squeezeWithH H c
    let c := (c.absorb p.quotientRoot.1).absorb p.quotientRoot.2
    match digestOfScalars p.quotientRoot with
    | none => return none
    | some quotientRoot =>
      let (t, c) ← squeezeWithH H c
      let c := (p.values.toList.foldl Chain.absorb c).absorb p.next
      let (ρ, _) ← squeezeWithH H c
      return (claimsAt logRows stmt α β γ t ρ p.values p.next).map
        fun claims ↦ ⟨witnessRoot, quotientRoot, claims⟩

/-- `openingSpongeWith` with Keccak-256 `H`. -/
def openingSpongeWithH (L : PcsQuotient.Layout) (claims : List PcsQuotient.Claim) : m Sponge := do
  let layoutId ← H L.encoding
  let pre := openingLabel ++ u64Bytes openingVersion ++ digestBytes layoutId ++ u64Bytes L.logN ++
    u64Bytes logInvRate
  let iv ← H (pre ++ claimBytes claims)
  return ⟨← F (seedInput iv zeroDigest), []⟩

/-- `openingWith` with Keccak-256 `H`. -/
def openingWithH (L : PcsQuotient.Layout) (root : Digest) (claims : List PcsQuotient.Claim) (proof : Compile.Proof) :
    m Bool := do
  if claims ≠ [] ∧ claims.all (·.point.length = L.vars) then
    match proof.stream with
    | x0 :: x1 :: rest =>
      let sp ← openingSpongeWithH H F L claims
      let sp ← absorb F sp x0 dsObserve
      let sp ← absorb F sp x1 dsObserve
      match digestOfScalars (x0, x1) with
      | some r =>
        if r.toList = root.toList then
          let program := verifyStackedOpening L.logN logInvRate
            (stackClaims L claims)
          let height := L.logN - laneFold + logInvRate
          match ← runWithHash H F program ⟨sp, rest, proof.openings, [(root, height, 2 ^ laneFold)]⟩ with
          | some (_, s) => return s.stream.isEmpty && s.openings.isEmpty
          | none => return false
        else return false
      | none => return false
    | _ => return false
  else return false

/-- `verifyWith` with Keccak-256 `H`. -/
def verifyWithH (logRows : ℕ) (indexRoot : Digest) (stmt : Statement) (proof : PcsQuotient.Proof) :
    m Bool := do
  match ← reduceWithH H logRows indexRoot stmt proof.reduction with
  | none => return false
  | some r =>
    if !(← openingWithH H F (witnessLayout logRows) r.witnessRoot [r.claims.witness] proof.witness)
    then return false
    if !(← openingWithH H F (wiringLayout logRows) indexRoot [r.claims.wiring] proof.wiring)
    then return false
    openingWithH H F (quotientLayout logRows) r.quotientRoot [r.claims.quotient, r.claims.sum]
      proof.quotient

/-- `commitWith` with Keccak-256 `H`. -/
def commitWithH (μ : ℕ) (stack : Array K) : m Tree :=
  buildTreeWithHash H (μ - 6 + 1) (stackWordFast μ 1 stack)

/-- `setupWith` with Keccak-256 `H`. -/
def setupWithH : m Digest := do
  return (← commitWithH H ((membership logRows).logRows + 2) (membership logRows).wiringTable).root

end With

/-! ## At `H = keccak256With F` -/

section Eq

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

theorem startWith_eq (label : List UInt8) :
    Chain.startWith F label = startWithH (keccak256With F) label := rfl

theorem squeezeWith_eq (c : Chain) : c.squeezeWith F = squeezeWithH (keccak256With F) c := rfl

theorem reduceWith_eqH (logRows : ℕ) (indexRoot : Digest) (stmt : Statement) (p : ReductionProof) :
    reduceWith F logRows indexRoot stmt p = reduceWithH (keccak256With F) logRows indexRoot stmt p :=
  rfl

theorem openingSpongeWith_eq (L : PcsQuotient.Layout) (claims : List PcsQuotient.Claim) :
    openingSpongeWith F L claims = openingSpongeWithH (keccak256With F) F L claims := rfl

theorem openingWith_eqH (L : PcsQuotient.Layout) (root : Digest) (claims : List PcsQuotient.Claim) (proof : Compile.Proof) :
    openingWith F L root claims proof = openingWithH (keccak256With F) F L root claims proof := by
  simp only [openingWith, openingWithH, run_eq_withHash]
  rfl

theorem verifyWith_eqH (logRows : ℕ) (indexRoot : Digest) (stmt : Statement)
    (proof : PcsQuotient.Proof) :
    verifyWith F logRows indexRoot stmt proof =
      verifyWithH (keccak256With F) F logRows indexRoot stmt proof := by
  simp only [PcsQuotient.verifyWith, verifyWithH, reduceWith_eqH, openingWith_eqH]
  rfl

theorem commitWith_eqH (μ : ℕ) (stack : Array K) :
    commitWith F μ stack = commitWithH (keccak256With F) μ stack :=
  buildTreeM_eq_withHash F _ _

theorem setupWith_eqH : setupWith F = setupWithH (keccak256With F) := by
  simp only [setupWith, Circuit.indexRootWith, setupWithH, commitWith_eqH]

end Eq

/-! ## Simulation -/

section Commute

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r)

theorem simulateQ_startWithH (label : List UInt8) :
    simulateQ impl (startWithH callKeccak256 label) = startWithH (implH impl) label := by
  simp only [startWithH, simulateQ_bind, simulateQ_queryH, simulateQ_pure]

theorem simulateQ_squeezeWithH (c : Chain) :
    simulateQ impl (squeezeWithH callKeccak256 c) = squeezeWithH (implH impl) c := by
  simp only [squeezeWithH, simulateQ_bind, simulateQ_queryH, simulateQ_pure]

theorem simulateQ_reduceWithH (logRows : ℕ) (indexRoot : Digest) (stmt : Statement)
    (p : ReductionProof) :
    simulateQ impl (reduceWithH callKeccak256 logRows indexRoot stmt p) =
      reduceWithH (implH impl) logRows indexRoot stmt p := by
  unfold reduceWithH
  split
  · simp
  · simp only [simulateQ_bind, simulateQ_startWithH]
    congr 1; funext c
    split
    · simp
    · simp only [simulateQ_bind, simulateQ_squeezeWithH]
      congr 1; funext x₁; congr 1; funext x₂; congr 1; funext x₃
      split
      · simp
      · simp only [simulateQ_bind, simulateQ_squeezeWithH, simulateQ_pure]

theorem simulateQ_openingSpongeWithH (L : PcsQuotient.Layout) (claims : List PcsQuotient.Claim) :
    simulateQ impl (openingSpongeWithH callKeccak256 callKeccakF1600 L claims) =
      openingSpongeWithH (implH impl) (implF impl) L claims := by
  simp only [openingSpongeWithH, simulateQ_bind, simulateQ_queryH, simulateQ_queryF,
    simulateQ_pure]

/-- mumbai's `simulateQ_run`, for a program of any result type. -/
theorem simulateQ_runWithHash {α : Type} :
    ∀ (p : Prog α) (s : ProgState),
      simulateQ impl (runWithHash callKeccak256 callKeccakF1600 p s) =
        runWithHash (implH impl) (implF impl) p s
  | .ret a, s => by simp [runWithHash]
  | .fail, s => by simp [runWithHash]
  | .read k, s => by
    simp only [runWithHash]
    split
    · simp
    · simp only [simulateQ_bind, simulateQ_absorb]
      congr 1; funext sp; exact simulateQ_runWithHash _ _
  | .sample k, s => by
    simp only [runWithHash, simulateQ_bind, simulateQ_squeeze]
    congr 1; funext r; exact simulateQ_runWithHash _ _
  | .grind bits k, s => by
    simp only [runWithHash]
    split
    · simp
    · simp only [simulateQ_bind, simulateQ_absorb, simulateQ_squeeze]
      congr 1; funext sp; congr 1; funext r
      split
      · exact simulateQ_runWithHash _ _
      · simp
  | .commit ht w k, s => by
    simp only [runWithHash]
    split
    · simp only [simulateQ_bind, simulateQ_absorb]
      congr 1; funext sp0; congr 1; funext sp1
      split
      · exact simulateQ_runWithHash _ _
      · simp
    · simp
  | .query i ps k, s => by
    simp only [runWithHash]
    split
    · simp
    · simp only [simulateQ_bind, LeanVM.Protocol.Compile.Rom.simulateQ_openAll]
      congr 1; funext o
      split
      · exact simulateQ_runWithHash _ _
      · simp

theorem simulateQ_openingWithH (L : PcsQuotient.Layout) (root : Digest) (claims : List PcsQuotient.Claim)
    (proof : Compile.Proof) :
    simulateQ impl (openingWithH callKeccak256 callKeccakF1600 L root claims proof) =
      openingWithH (implH impl) (implF impl) L root claims proof := by
  unfold openingWithH
  split
  · split
    · simp only [simulateQ_bind, simulateQ_openingSpongeWithH, simulateQ_absorb]
      congr 1; funext sp; congr 1; funext sp; congr 1; funext sp
      split
      · split
        · simp only [simulateQ_bind]
          congr 1
          · exact simulateQ_runWithHash impl _ _
          · funext z
            split <;> simp
        · simp
      · simp
    · simp
  · simp

theorem simulateQ_verifyWithH (logRows : ℕ) (indexRoot : Digest) (stmt : Statement)
    (proof : PcsQuotient.Proof) :
    simulateQ impl (verifyWithH callKeccak256 callKeccakF1600 logRows indexRoot stmt proof) =
      verifyWithH (implH impl) (implF impl) logRows indexRoot stmt proof := by
  unfold verifyWithH
  simp only [simulateQ_bind, simulateQ_reduceWithH]
  congr 1; funext z
  split
  · simp
  · simp only [simulateQ_bind, simulateQ_openingWithH]
    congr 1; funext b₁
    split
    · simp
    · simp only [simulateQ_bind, simulateQ_openingWithH]
      congr 1; funext b₂
      split
      · simp
      · simp only [simulateQ_openingWithH]

theorem simulateQ_commitWithH (μ : ℕ) (stack : Array K) :
    simulateQ impl (commitWithH callKeccak256 μ stack) = commitWithH (implH impl) μ stack :=
  simulateQ_buildTreeM impl _ _

theorem simulateQ_setupWithH :
    simulateQ impl (setupWithH callKeccak256) = setupWithH (implH impl) := by
  simp only [setupWithH, simulateQ_bind, simulateQ_commitWithH, simulateQ_pure]

end Commute

/-! ## The prover -/

section ProverWith

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KeccakState → m KeccakState)

/-- `proveOpeningWith` with Keccak-256 `H`. -/
def proveOpeningWithH (fuel : ℕ) (L : PcsQuotient.Layout) (tree : Tree) (stack : Array K)
    (claims : List PcsQuotient.Claim) : m (Option Compile.Proof) := do
  let (r0, r1) := digestScalars tree.root
  let sp ← openingSpongeWithH H F L claims
  let sp ← absorb F sp r0 dsObserve
  let sp ← absorb F sp r1 dsObserve
  let program := verifyStackedOpening L.logN logInvRate
    (stackClaims L claims)
  let r ← runFromWithHash H F fuel program (some (openingScript L stack claims)) sp [tree]
  return r.map fun t ↦ ⟨r0 :: r1 :: t.1, t.2⟩

/-- `proveWith` with Keccak-256 `H`. -/
def proveWithH (fuel : ℕ) (circuit : Circuit) (stmt : Statement) (cells : Array K) (masks : Masks)
    (witnessPad quotientPad : Padding) :
    m (Option PcsQuotient.Proof) := do
  let mv := cellVars circuit.logRows
  let n := 2 ^ mv
  let big := 4 * n
  let block := 2 ^ region
  let sigmaHat := circuit.wiringTable
  let indexTree ← commitWithH H mv sigmaHat
  let wHat := coefficients mv 0 cells
  let mask := maskEntries masks
  let wStack := witnessStack circuit.logRows wHat mask witnessPad
  let witnessTree ← commitWithH H (mv + 1) wStack
  let c ← startWithH H (label indexTree.root stmt)
  let witnessRoot := digestScalars witnessTree.root
  let c := (c.absorb witnessRoot.1).absorb witnessRoot.2
  let (α, c) ← squeezeWithH H c
  let (β, c) ← squeezeWithH H c
  let (γ, c) ← squeezeWithH H c
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
  let qStack := quotientStack circuit.logRows hHat qHat qGateHat quotientPad
  let quotientTree ← commitWithH H (mv + 4) qStack
  let quotientRoot := digestScalars quotientTree.root
  let c := (c.absorb quotientRoot.1).absorb quotientRoot.2
  let (t, _) ← squeezeWithH H c
  let digits := digitsOf t mv
  let a : Vector E 4 := Vector.ofFn fun j ↦
    novelEval wHat j.val 4 ((digits.drop 2).take (mv - 2)) +
      digits.getD mv 0 * novelEval mask j.val 4 ((digits.drop 2).take 2)
  let next := novelEval sigmaHat 0 1 (digits.take mv)
  let proof : ReductionProof := ⟨witnessRoot, quotientRoot, a, next⟩
  match ← reduceWithH H circuit.logRows indexTree.root stmt proof with
  | none => return none
  | some r =>
    let some witness ← proveOpeningWithH H F fuel (witnessLayout circuit.logRows) witnessTree wStack
      [r.claims.witness] | return none
    let some wiring ← proveOpeningWithH H F fuel (wiringLayout circuit.logRows) indexTree sigmaHat
      [r.claims.wiring] | return none
    let some quotient ← proveOpeningWithH H F fuel (quotientLayout circuit.logRows) quotientTree
      qStack [r.claims.quotient, r.claims.sum] | return none
    return some ⟨proof, witness, wiring, quotient⟩

/-- `proverWith` with Keccak-256 `H`. -/
def proverWithH (fuel : ℕ) (stmt : Statement) (w : Secret) (masks : Masks)
    (witnessPad quotientPad : Padding) : m (Option PcsQuotient.Proof) :=
  let circuit := membership logRows
  proveWithH H F fuel circuit stmt (circuit.cells (membershipInputs w)) masks witnessPad
    quotientPad

end ProverWith

section ProverEq

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

theorem proveOpeningWith_eqH (fuel : ℕ) (L : PcsQuotient.Layout) (tree : Tree) (stack : Array K)
    (claims : List PcsQuotient.Claim) :
    proveOpeningWith F fuel L tree stack claims =
      proveOpeningWithH (keccak256With F) F fuel L tree stack claims := by
  simp only [proveOpeningWith, proveOpeningWithH, runFrom_eq_withHash]
  rfl

theorem proveWith_eqH (fuel : ℕ) (circuit : Circuit) (stmt : Statement) (cells : Array K)
    (masks : Masks) (witnessPad quotientPad : Padding) :
    proveWith F fuel circuit stmt cells masks witnessPad quotientPad =
      proveWithH (keccak256With F) F fuel circuit stmt cells masks witnessPad quotientPad := by
  simp only [proveWith, proveWithH, commitWith_eqH, proveOpeningWith_eqH]
  rfl

theorem proverWith_eqH (fuel : ℕ) (stmt : Statement) (w : Secret) (masks : Masks)
    (witnessPad quotientPad : Padding) :
    proverWith F fuel stmt w masks witnessPad quotientPad =
      proverWithH (keccak256With F) F fuel stmt w masks witnessPad quotientPad :=
  proveWith_eqH F _ _ _ _ _ _ _

end ProverEq

section ProverCommute

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r)

/-- The script runner commutes with simulation. -/
theorem simulateQ_runFromWithHash (fuel : ℕ) {α β : Type} (P : Prog α) :
    ∀ (S : Option (Script β)) (sp : Sponge) (cs : List Tree),
      simulateQ impl (runFromWithHash callKeccak256 callKeccakF1600 fuel P S sp cs) =
        runFromWithHash (implH impl) (implF impl) fuel P S sp cs := by
  induction P with
  | ret a => intro S sp cs; simp [runFromWithHash]
  | fail => intro S sp cs; simp [runFromWithHash]
  | read k ih =>
    intro S sp cs
    simp only [runFromWithHash, simulateQ_bind, simulateQ_absorb, simulateQ_pure, ih]
  | sample k ih =>
    intro S sp cs
    simp only [runFromWithHash, simulateQ_bind, simulateQ_squeeze, ih]
  | grind bits k ih =>
    intro S sp cs
    simp only [runFromWithHash, simulateQ_bind, simulateQ_findNonceM]
    congr 1; funext o
    cases o with
    | none => simp
    | some n => simp only [simulateQ_bind, simulateQ_powStepM, simulateQ_pure, ih]
  | commit ht w k ih =>
    intro S sp cs
    simp only [runFromWithHash, simulateQ_bind, simulateQ_buildTreeM, simulateQ_absorb,
      simulateQ_pure, ih]
  | query i ps k ih =>
    intro S sp cs
    simp only [runFromWithHash]
    split
    · simp
    · simp only [simulateQ_bind, simulateQ_pure, ih]

theorem simulateQ_proveOpeningWithH (fuel : ℕ) (L : PcsQuotient.Layout) (tree : Tree)
    (stack : Array K) (claims : List PcsQuotient.Claim) :
    simulateQ impl (proveOpeningWithH callKeccak256 callKeccakF1600 fuel L tree stack claims) =
      proveOpeningWithH (implH impl) (implF impl) fuel L tree stack claims := by
  simp only [proveOpeningWithH, simulateQ_bind, simulateQ_openingSpongeWithH, simulateQ_absorb,
    simulateQ_runFromWithHash, simulateQ_pure]

theorem simulateQ_proveWithH (fuel : ℕ) (circuit : Circuit) (stmt : Statement) (cells : Array K)
    (masks : Masks) (witnessPad quotientPad : Padding) :
    simulateQ impl (proveWithH callKeccak256 callKeccakF1600 fuel circuit stmt cells masks
        witnessPad quotientPad) =
      proveWithH (implH impl) (implF impl) fuel circuit stmt cells masks witnessPad quotientPad := by
  unfold proveWithH
  simp only [simulateQ_bind, simulateQ_commitWithH, simulateQ_startWithH, simulateQ_squeezeWithH,
    simulateQ_reduceWithH]
  congr 1; funext indexTree; congr 1; funext witnessTree; congr 1; funext c
  congr 1; funext x₁; congr 1; funext x₂; congr 1; funext x₃
  congr 1; funext quotientTree; congr 1; funext x₄; congr 1; funext red
  split
  · simp
  · simp only [simulateQ_bind, simulateQ_proveOpeningWithH]
    congr 1; funext o₁
    split
    · simp only [simulateQ_bind, simulateQ_proveOpeningWithH]
      congr 1; funext o₂
      split
      · simp only [simulateQ_bind, simulateQ_proveOpeningWithH]
        congr 1; funext o₃
        split <;> simp
      · simp
    · simp

theorem simulateQ_proverWithH (fuel : ℕ) (stmt : Statement) (w : Secret) (masks : Masks)
    (witnessPad quotientPad : Padding) :
    simulateQ impl (proverWithH callKeccak256 callKeccakF1600 fuel stmt w masks witnessPad
        quotientPad) =
      proverWithH (implH impl) (implF impl) fuel stmt w masks witnessPad quotientPad :=
  simulateQ_proveWithH impl _ _ _ _ _ _ _

end ProverCommute

end E2ECompleteness
