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

end E2ECompleteness
