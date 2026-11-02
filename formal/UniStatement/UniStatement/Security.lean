-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The model, the experiments' shape and the form of the
-- statements are this repository's `formal/Statement` (`PcsQuotient.Security`, after leanerVM `mumbai` 6175f1a0's
-- `Statement/LeanVm.lean`, MIT OR Apache-2.0); the extractor's replay, Merkle inversion and decoders are its
-- (`PcsQuotient.Extractor`, `Replay`, `Decoder`) and mumbai's (`Statement/Extractor.lean`); the relation is Lv42's
-- (`formal/Lv42`, leanerVM `mumbai` f0393df4's `M3Holds`).
module

public import UniStatement.Opening
public import UniStatement.Mapping
public import PcsQuotient.Extractor
public import Lv42.Protocol.FlockSpec
public import VCVio.EvalDist.ProbabilityNotation

/-!
# Knowledge soundness and completeness, against leanVM 42422001's relation

Statements only, no proof. The model is `formal/Statement`'s (leanerVM `mumbai`'s): one uniformly random
permutation `π` of the Keccak-f[1600] state, which every party queries forward and inverse; every hash of
the protocol is Keccak-256 over `π` (the transcript, the WHIR commitments and openings), the setup's
commitments computed over `π` before the adversary runs.

**The deployment** (`Deployment`): the program `prog` (leanISA with `BLAKE2S`, `2^logBytecode`
instructions), the shape (one per contract), the transcript's IV. **The relation** is Lv42's, for leanVM
42422001's statement: `M3Holds (leanIsaInstance blake2sFlockSpec prog s) input q` (`= ConstraintsVanish ∧
Balanced ∧ CountsNonzero ∧ PublicLinesHold ∧ aux`, the last `FlockRegion.Holds` of `q_flock`), at the
shape's sizes `s` (`sizesOf`), the public input the calldata's 32 bytes (`publicInputOf`), `q` a stack of
Lv42's layout. Under `Sizes.Admissible`, Lv42 proves it equivalent to `SatisfiedBy prog input (witnessOf …)`
(`satisfiedBy_witnessOf`) and, from a satisfying witness, `M3Honest` of its stack (`m3Honest_stackOf`).

**The setup** (`setupTreesWith`): the WHIR commitments (`PcsQuotient.commitWith`, rate `1/2`) of the
setup stack `F` (the bytecode's tuples and the memory's addresses, `setupStack`) and of Flock's matrices
`A0`, `B0` (`matrixStack` of `blake2sFlockSpec`'s R1CS). Their roots are the verifier's constants; the
extractor reads their trees (public).

**The extractor** (`uniExtractor`) is explicit and computable, as `formal/Statement`'s: from the
adversary's transcript and the setup's trees, the Keccak-256 evaluations replayed (`Replay`); `C1`'s
Merkle tree inverted under the root the stream names (`c1Word`); its candidate stacks, by the fast path,
the unique decoder, then the list decoder (mumbai's and the Statement's, at `C1`'s `2^μ`, rate `1/2`);
each candidate read as Lv42's stack (`lv42Stack`: basis `B` to values, the correspondence of
`Mapping.lean`); the first that satisfies `M3Holds`. It reads only `C1`: `C2` (the heap, the quotients) and
the setup are not part of the witness.

**Completeness** is stated for a prover given as a parameter (`UniProver`): the univariate PIOP's honest
prover is not transcribed (the Rust has none at `cee6363`; milestone 2 builds it). `UniCompletenessWith`
asks that its proof of a statement with an `M3Honest` stack be rejected with probability at most `δ`.
-/

@[expose] public section

namespace UniStatement

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics (KeccakState)
open LeanVM.Extraction
open OracleComp OracleSpec Common
open Lv42.Protocol.LeanIsa (Sizes leanIsaμ)
open Lv42.Semantics (Program PublicInput)
open scoped ENNReal

/-- **The deployment**: the program, the shape (one per contract), the transcript's IV. -/
structure Deployment where
  prog : Program
  shape : Shape
  iv : List UInt8
  logMemory_pos : 0 < shape.logMemory
  logBytecode_eq : shape.logBytecode = prog.logSize

/-- The deployment's announced sizes, as Lv42's. -/
def Deployment.sizes (D : Deployment) : Sizes := sizesOf D.shape D.logMemory_pos

/-- **The instance**: leanVM 42422001's, Lv42's `leanIsaInstance` with the BLAKE2s Flock specification. -/
abbrev Deployment.inst (D : Deployment) : Lv42.Protocol.M3Instance :=
  Lv42.Protocol.leanIsaInstance Lv42.Protocol.Blake2sFlock.blake2sFlockSpec D.prog D.sizes

/-- Lv42's stack at the deployment's sizes. -/
abbrev Deployment.Stack (D : Deployment) : Type := LeanVM.Protocol.Column (leanIsaμ D.prog D.sizes)

/-- **The relation**: `M3Holds` of the instance, the public input the calldata's 32 bytes. -/
def Deployment.Relation (D : Deployment) (input : Vector UInt8 32) (q : D.Stack) : Prop :=
  Lv42.Protocol.M3Holds D.inst (publicInputOf input.toList) q

instance (D : Deployment) (input : Vector UInt8 32) (q : D.Stack) : Decidable (D.Relation input q) :=
  inferInstanceAs (Decidable (Lv42.Protocol.M3Holds _ _ _))

/-- **The relation completeness starts from**: `M3Honest` (`M3Holds`, and every padding row its public
row). -/
def Deployment.HonestRelation (D : Deployment) (input : Vector UInt8 32) (q : D.Stack) : Prop :=
  Lv42.Protocol.M3Honest D.inst (publicInputOf input.toList) q

/-! ### The setup -/

/-- **The setup's trees**: the WHIR commitments of the setup stack and of `A0`, `B0`. -/
structure SetupTrees where
  bytecode : LeanVM.Prover.Tree
  a0 : LeanVM.Prover.Tree
  b0 : LeanVM.Prover.Tree

/-- The verifier's constants: the trees' roots. -/
def SetupTrees.roots (t : SetupTrees) : SetupRoots := ⟨t.bytecode.root, t.a0.root, t.b0.root⟩

/-- The setup's Keccak-256 evaluations (each tree's, `Tree.evaluations`), which the extractor reads. -/
def SetupTrees.evaluations (t : SetupTrees) : List (List UInt8 × Digest) :=
  PcsQuotient.Tree.evaluations t.bytecode ++ PcsQuotient.Tree.evaluations t.a0 ++
    PcsQuotient.Tree.evaluations t.b0

/-- `A0` (`left`) or `B0` of the BLAKE2s R1CS as a stack. -/
def flockMatrixStack (left : Bool) : Array K :=
  let C := Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs
  matrixStack fun k j ↦ if left then C.A k j else C.B k j

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **The setup** over `F`: the commitments of the setup stack (`setupStack`) and of `A0`, `B0`. -/
def setupTreesWith (D : Deployment) : m SetupTrees := do
  let f ← PcsQuotient.commitWith F (setupLayout D.shape).vars (setupStack D.prog D.shape)
  let a ← PcsQuotient.commitWith F matrixVars (flockMatrixStack true)
  let b ← PcsQuotient.commitWith F matrixVars (flockMatrixStack false)
  return ⟨f, a, b⟩

/-- **The deployed verifier** over `F` on the setup's roots (`verifyWith` at the deployment's shape and
IV). -/
def Deployment.verifierWith (D : Deployment) (roots : SetupRoots) (input : Vector UInt8 32)
    (proof : UniProof) : m Bool :=
  verifyWith F D.shape D.iv roots input proof

end With

/-! ### The extractor -/

/-- `C1`'s root as the stream names it: its first 32 bytes, two 16-byte halves (`next_root`). -/
def c1RootOf (proof : UniProof) : Digest :=
  let b := proof.stream
  let half (o : ℕ) : E := eNew (beWordAt b (o + 8)) (beWordAt b o) 0
  rootOf (half 0, half 16)

/-- **`C1`'s committed word**: under the root the stream names, the leaves the unique preimages `pre`
commit to (`Replay.leavesUnder`, mumbai's `committedLeaves`): `2^(μ − 6 + 1)` leaves of `64` words. -/
def c1Word (D : Deployment) (pre : Digest → ℕ → Option (List UInt8)) (proof : UniProof) : ℕ → List K :=
  let height := (c1Layout D.shape).vars - 6 + 1
  leafAt (PcsQuotient.Replay.leavesUnder pre 64 height (c1RootOf proof)) height 64

/-- **The extractor on given preimages**: the first candidate `C1` stack whose Lv42 stack satisfies the
relation, the fast path's first, then the unique decoder's, then the list decoder's. -/
def extractFrom (D : Deployment) (input : Vector UInt8 32) (pre : Digest → ℕ → Option (List UInt8))
    (proof : UniProof) : Option D.Stack :=
  let word := c1Word D pre proof
  let μ := (c1Layout D.shape).vars
  let candidate (stack : Vector K (2 ^ μ)) : Option D.Stack :=
    let q := lv42Stack D.prog D.sizes D.shape fun i ↦ stack.toArray.getD i 0
    if D.Relation input q then some q else none
  (fastStacks μ 1 word).findSome? candidate <|>
    (PcsQuotient.UniqueDecoding.uniqueStacks μ 1 word).findSome? candidate <|>
    (decodeStacks μ 1 word).findSome? candidate

/-- **The extractor** in the random-permutation model: `extractFrom` on the unique preimages of the
setup's evaluations and the transcript's (the lengths a Merkle tree of `64`-word leaves hashes). -/
def uniExtractor (D : Deployment) (input : Vector UInt8 32) (setupEvals : List (List UInt8 × Digest))
    (T : OracleQueryLog) (proof : UniProof) : Option D.Stack :=
  let paths := setupEvals ++
    PcsQuotient.Replay.transcriptEvaluations PcsQuotient.merkleLengths (LeanVM.permutationQueries T)
  extractFrom D input (PcsQuotient.Replay.preimageIn (PcsQuotient.Replay.preimageIndex paths)) proof

/-- An extractor's shape: from the statement, the setup's evaluations, the transcript and the proof, a
stack. -/
abbrev UniExtractor (D : Deployment) : Type :=
  Vector UInt8 32 → List (List UInt8 × Digest) → OracleQueryLog → UniProof → Option D.Stack

/-! ### Knowledge soundness -/

/-- An adversary: given the setup's roots, a public input and a proof, with coins, `π` and `π⁻¹`. -/
abbrev UniAdversary : Type := SetupRoots → OracleComp RandomPermutationOracles (Vector UInt8 32 × UniProof)

/-- An outcome: the statement and the proof, the verdict, the setup's evaluations, the transcript. -/
abbrev UniOutcome : Type :=
  ((Vector UInt8 32 × UniProof) × Bool) × List (List UInt8 × Digest) × OracleQueryLog

/-- **The knowledge-soundness experiment**: the setup over `π`, the adversary given its roots (its queries
logged), then the deployed verifier over `π`. -/
noncomputable def uniSoundnessExperiment (D : Deployment) (A : UniAdversary) : ProbComp UniOutcome :=
  runWithRandomPermutation do
    let trees ← setupTreesWith queryPermutation D
    let (z, transcript) ← (simulateQ loggedOracles (A trees.roots)).run []
    let accepted ← D.verifierWith queryPermutation trees.roots z.1 z.2
    return ((z, accepted), trees.evaluations, transcript)

/-- **The adversary breaks knowledge soundness**: the verifier accepts, and the extractor outputs no stack
satisfying leanVM 42422001's relation for the public input. -/
def UniBreaksKnowledgeSoundness (D : Deployment) (ext : UniExtractor D) (z : UniOutcome) : Prop :=
  z.1.2 = true ∧ ¬ ∃ q, ext z.1.1.1 z.2.1 z.2.2 z.1.1.2 = some q ∧ D.Relation z.1.1.1 q

/-- **Knowledge soundness for the extractor `ext`**, error `ε Q` for `Q` calls of `π` and `π⁻¹`. -/
def UniKnowledgeSoundnessWith (D : Deployment) (ext : UniExtractor D) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : UniAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    Pr{let z ← uniSoundnessExperiment D A}[UniBreaksKnowledgeSoundness D ext z] ≤ ε Q

/-- **Knowledge soundness** of the univariate verifier against leanVM 42422001's relation, for the explicit
extractor `uniExtractor`. -/
def UniKnowledgeSoundness (D : Deployment) (ε : ℕ → ℝ≥0∞) : Prop :=
  UniKnowledgeSoundnessWith D (uniExtractor D) ε

/-! ### Completeness -/

/-- A prover: from the public input and a stack of Lv42's layout, a proof (or none), with coins, `π` and
`π⁻¹` (it recomputes the public setup as it needs). -/
abbrev UniProver (D : Deployment) : Type :=
  Vector UInt8 32 → D.Stack → OracleComp RandomPermutationOracles (Option UniProof)

/-- **The completeness experiment**: the setup, the prover's proof, the verifier's verdict, over `π`. -/
noncomputable def uniCompletenessExperiment (D : Deployment) (P : UniProver D) (input : Vector UInt8 32)
    (q : D.Stack) : ProbComp Bool :=
  runWithRandomPermutation do
    let trees ← setupTreesWith queryPermutation D
    match ← P input q with
    | none => return false
    | some proof => D.verifierWith queryPermutation trees.roots input proof

/-- **Completeness of the prover `P`**: its proof of a public input with an `M3Honest` stack is rejected
with probability at most `δ`. -/
def UniCompletenessWith (D : Deployment) (P : UniProver D) (δ : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (q : D.Stack), D.HonestRelation input q →
    Pr{let v ← uniCompletenessExperiment D P input q}[v = false] ≤ δ

/-- **Completeness**, for a prover given explicitly: the honest prover is not yet transcribed, so the
statement names it (`UniCompletenessWith`). -/
def UniCompleteness (D : Deployment) (P : UniProver D) (δ : ℝ≥0∞) : Prop := UniCompletenessWith D P δ

end UniStatement

end
