-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The model, the experiments' shape and the form of the
-- statements are `formal/UniStatement`'s (`Security.lean`, after `formal/Statement`'s `PcsQuotient.Security` and
-- leanerVM `mumbai` 6175f1a0's `Statement/LeanVm.lean`, MIT OR Apache-2.0); the relation is Lv42's (`formal/Lv42`,
-- leanerVM `mumbai` f0393df4's `M3Holds`). Transcribed from `crates/leanvm_rec/src/pi2/circuit.rs`
-- (`Circuit::digest`), `prover.rs` (`Setup::new`) and `contract.rs` (`registry`, the calls), and
-- `crates/leanvm_flock_gas/src/evm/machine.rs` (`decode`, `root_of_word`), branch `leanvm-rec` @ 2b22581.
import RecStatement.Calls
import RecStatement.Data
import UniStatement.Security

/-!
# The recursive verifier's end statements, against leanVM 42422001's relation

Statements only, no proof (the composition proves them). The model is `formal/Statement`'s and `formal/UniStatement`'s:
one uniformly random permutation `π` of the Keccak-f[1600] state; every hash of the protocol is Keccak-256 over `π`
(π2's transcript, its IV, the circuit's digest, the WHIR commitments and openings of both layers), the setup's
commitments computed over `π` before the adversary runs.

**The recursive verifier** (`RecDeployment.verifierWith`) is the contract (`pi2::contract`): π2's verifier on the
calldata (`runWith`: the public input, then the stream with π1's roots and claims' elements, `W`'s and `Q`'s roots and
the 17 values), then **six `PCS_OPEN` calls**, each decoded under the contract's registry (`machine::decode`: a known
layout word, which fixes the variables, `k ≥ 1` claims, the exact length, every element's top 64 bits zero) and
opened by the Statement's WHIR opening: **π1's three** (`C1`, `C2`, π1's setup `F`; their points the 27 coordinates the
contract derives from π1-rec3's 14 pair challenges) on the plain layout of π1's stacks (`UniStatement.pcsOpenWith`, as
`UniStatement.verifyWithFs`), and **π2's three** (`W`, the setup, `Q` with its two claims in one call) on π2's layouts
(`PcsQuotient.openingWith`, `quotient::opening`). π1's verifier itself never runs: π2 proves it accepted.

**The deployment** (`RecDeployment`): π1's (`UniStatement.Deployment`: the program, the shape, leanVM's program IV),
**π2's circuit** (`Pi2Circuit`: the verifier's view, `Circuit`, and the setup columns `σ`, `κ`), π1's calls as the
circuit names their words, and **where π2's witness holds π1's row counts** (`pi1Rows`: π1's stream is π2's witness,
not calldata; the row counts are its first 24 bytes, the circuit compiler's free bits). `RecDeployment.Real` pins it to
the circuit of π1-rec3's real proof: the emitted tables (`Data`), the reference shape and program IV, π1's calls, and
`σ`, `κ` by the circuit's digest and the setup's root the Rust computed.

**The IV binds the setup** (`RecDeployment.ivWith`, `prover::iv`): π1-rec3's contract IV (which binds π1's three setup
roots, the shape, π1's layout words and the variant), π2's setup root (the commitment of `κ`, `κ + σ`), the circuit's
digest (its tables, `σ`'s and `κ`'s hashes) and π2's three layout words.

**The relation** is leanVM 42422001's, as `UniStatement.Deployment.Relation`: `M3Holds (leanIsaInstance
blake2sFlockSpec prog s) input q` at the sizes `s` of π1's row counts. The row counts are not public in the recursion
(they are π1's stream's, which π2's witness holds): the extractor outputs them with the stack.

**The extractor** (`recExtractor`) is explicit and computable, as UniStatement's: the transcript's and the setup's
Keccak-256 evaluations replayed; **π2's `W`** inverted under the root the stream names and decoded (the fast path, the
unique decoder, the list decoder, at `W`'s `2^m`, rate `1/2`), each candidate's witness values read (`basisValue`, the
`B` basis) and **π1's row counts** read off them (`pi1Rows`); **π1's `C1`** inverted under the root π2's stream names
(its first public root) and decoded likewise; each `C1` candidate read as Lv42's stack at those row counts
(`lv42Stack`), the first satisfying `M3Holds`.

**Completeness** is stated for a prover given as a parameter (`RecProver`), as UniStatement's.
-/

namespace RecStatement

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics (KeccakState)
open LeanVM.Extraction
open OracleComp OracleSpec Common
open scoped ENNReal

/-! ## π2's circuit with its setup columns -/

/-- **π2's circuit**: the verifier's view (`Circuit`) and the setup columns `σ` (each position's push tag, an index) and
`κ` (the constants), `2^logN` positions. -/
structure Pi2Circuit where
  circuit : Circuit
  sigma : ℕ → ℕ
  kappa : ℕ → K

/-- Eight little-endian bytes of `n` (`put`). -/
def le64 (n : ℕ) : List UInt8 := (List.range 8).map fun k ↦ (n >>> (8 * k)).toUInt8

/-- A coefficient's encoding: its limbs, its power of `γ`. -/
def Coeff.encoding (c : Coeff) : List UInt8 :=
  le64 c.c0.toNat ++ le64 c.c1.toNat ++ le64 c.c2.toNat ++ le64 c.gamma

/-- A linear form's encoding: its terms' count, each coefficient and cell, the constant (`0`, or `1` and it). -/
def Lin.encoding (l : Lin) : List UInt8 :=
  le64 l.terms.length ++ l.terms.flatMap (fun t ↦ t.1.encoding ++ le64 t.2) ++
    match l.constant with
    | none => le64 0
    | some c => le64 1 ++ c.encoding

/-- **The circuit's encoding** (`Circuit::digest`'s bytes before the setup columns' hashes). -/
def Circuit.encoding (c : Circuit) : List UInt8 :=
  le64 c.logN ++ le64 c.logRow ++ le64 c.formulas.length ++
    c.formulas.flatMap (fun f ↦ f.lin.encoding ++ le64 f.products.length ++
      f.products.flatMap fun p ↦ p.1.encoding ++ p.2.1.encoding ++ p.2.2.encoding) ++
    le64 c.pairs.length ++
    c.pairs.flatMap (fun p ↦ le64 p.firstRow ++ le64 p.logRows ++ le64 p.role ++ le64 p.formula ++
      le64 (if p.pulls then 1 else 0)) ++
    le64 c.reads.length ++
    c.reads.flatMap (fun rd ↦ match rd with
      | .integer b => le64 0 ++ le64 b
      | .root => le64 1 ++ le64 32
      | .scalar => le64 2 ++ le64 24) ++
    le64 c.publicTerms.length ++ c.publicTerms.flatMap fun t ↦ le64 t.tag ++ t.value.encoding

/-- The positions' count, `N = 2^logN`. -/
def Pi2Circuit.n (c : Pi2Circuit) : ℕ := 2 ^ c.circuit.logN

/-- **The setup's table** (`Setup::new`): the basis-`B` coefficients of `κ` (on `V_m`), then of `κ + σ` (`σ`'s values the
points `ω_{σ_i}`), `2^(m+1)` words (`setup`'s layout: two chunks of `N`, every lane a block, in order). -/
def Pi2Circuit.setupStack (c : Pi2Circuit) : Array K :=
  let m := c.circuit.logN
  let kb := UniStatement.bCoefficients m (Array.ofFn (n := 2 ^ m) fun i ↦ c.kappa i.val)
  let sb := UniStatement.bCoefficients m (Array.ofFn (n := 2 ^ m) fun i ↦ UniStatement.point (c.sigma i.val))
  kb ++ Array.ofFn (n := 2 ^ m) fun i ↦ kb.getD i.val 0 + sb.getD i.val 0

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **The circuit's digest** over `F` (`Circuit::digest`): Keccak-256 of the encoding, `σ`'s hash (its tags, four
little-endian bytes each) and `κ`'s (eight bytes each). -/
def Pi2Circuit.digestWith (c : Pi2Circuit) : m (List UInt8) := do
  let sigma ← keccak256With F ((List.range c.n).flatMap fun i ↦ (le64 (c.sigma i)).take 4)
  let kappa ← keccak256With F ((List.range c.n).flatMap fun i ↦ le64 (c.kappa i).lane.toNat)
  let d ← keccak256With F (c.circuit.encoding ++ digestBytes sigma ++ digestBytes kappa)
  return digestBytes d

/-- **π2's setup tree** over `F`: the WHIR commitment of the setup's table (`opening::commit`). -/
def Pi2Circuit.setupTreeWith (c : Pi2Circuit) : m LeanVM.Prover.Tree :=
  PcsQuotient.commitWith F (layoutsOf c.circuit.logN).2.2.logN c.setupStack

end With

/-! ## The deployment -/

/-- **The recursive verifier's deployment**: π1's (program, shape, program IV), π2's circuit, π1's calls as the circuit
names their words, and π1's row counts as π2's witness holds them (a function of the witness's values at the
positions, `w(ω_i)`). -/
structure RecDeployment where
  pi1 : UniStatement.Deployment
  pi2 : Pi2Circuit
  pi1Calls : List (List CallWord)
  pi1Rows : (ℕ → K) → List ℕ

/-- **The real deployment's data**: π2's circuit for π1-rec3's real proof (the emitted tables, `σ` and `κ` the ones
whose digest and setup root the Rust computed), π1's calls, the reference shape and leanVM's program IV. -/
def RecDeployment.Real (D : RecDeployment) : Prop :=
  D.pi2.circuit = Data.circuit ∧ D.pi1Calls = Data.pi1Calls ∧ D.pi1.shape = UniStatement.reference ∧
    D.pi1.programIv = UniStatement.programIv ∧
    Id.run (D.pi2.digestWith (m := Id) fun x ↦ pure (LeanVM.Semantics.keccakF1600 x)) = Data.digest ∧
    digestBytes (Id.run (D.pi2.setupTreeWith (m := Id) fun x ↦ pure (LeanVM.Semantics.keccakF1600 x))).root =
      Data.setupRoot

/-- π2's verifier's constants (`Spec::of`). -/
def RecDeployment.spec (D : RecDeployment) : Spec := Spec.of D.pi2.circuit

/-- **The setup's roots**: π1's three (`F`, `A0`, `B0`) and π2's (the commitment of `κ`, `κ + σ`). -/
structure RecSetupRoots where
  pi1 : UniStatement.SetupRoots
  pi2 : Digest

/-- **The setup's trees**: π1's (UniStatement's) and π2's. -/
structure RecSetupTrees where
  pi1 : UniStatement.SetupTrees
  pi2 : LeanVM.Prover.Tree

def RecSetupTrees.roots (t : RecSetupTrees) : RecSetupRoots := ⟨t.pi1.roots, t.pi2.root⟩

/-- The setup's Keccak-256 evaluations, which the extractor reads. -/
def RecSetupTrees.evaluations (t : RecSetupTrees) : List (List UInt8 × Digest) :=
  t.pi1.evaluations ++ PcsQuotient.Tree.evaluations t.pi2

/-! ## `PCS_OPEN` -/

/-- How a layout word's opening is checked: π1's (the plain layout of `2^vars` words, `UniStatement.pcsOpenWith`) or
π2's (its layout, `PcsQuotient.openingWith`). -/
inductive Opener where
  | pi1 (vars : ℕ)
  | pi2 (layout : PcsQuotient.Layout)

/-- **The registry** (`contract::registry`) of π1's shape and π2's `m`: π2's three layout words, then π1's (its calls'
layouts, `C1`, `C2`, `F`). -/
def registryOf (shape : UniStatement.Shape) (m : ℕ) : List (List UInt8 × Opener) :=
  let (lw, lq, ls) := layoutWords m
  let (w, q, s) := layoutsOf m
  [(lw, .pi2 w), (lq, .pi2 q), (ls, .pi2 s)] ++
    ((UniStatement.layoutWords shape).take 3).map fun word ↦ (word, .pi1 (UniStatement.layoutWordVars word))

/-- The deployment's registry. -/
def RecDeployment.registry (D : RecDeployment) : List (List UInt8 × Opener) :=
  registryOf D.pi1.shape D.pi2.circuit.logN

/-- The variables of a registered layout's claims. -/
def Opener.vars : Opener → ℕ
  | .pi1 v => v
  | .pi2 L => L.vars

/-- An element word's element, if its top 64 bits are zero (`decode`'s `element`). -/
def elementOfWord (w : List UInt8) : Option E :=
  let be (at' : ℕ) : UInt64 := (List.range 8).foldl (fun acc k ↦ (acc <<< 8) ||| (w.getD (at' + k) 0).toUInt64) 0
  if w.length = 32 ∧ (w.take 8).all (· = 0) then some (UniStatement.eNew (be 24) (be 16) (be 8)) else none

/-- The root a root word names (`root_of_word`: each 16-byte half reversed), as a digest. -/
def rootOfWord (w : List UInt8) : Digest := UniStatement.digestOfBytes32 (rootWordOfBytes w)

/-- **`decode(input, registry)`**: the root word, the layout word, `k ≥ 1` claims of the registered variables; every
element's top 64 bits zero, the exact length. -/
def decodeWith (registry : List (List UInt8 × Opener)) (words : List (List UInt8)) :
    Option (Digest × Opener × List PcsQuotient.Claim) := do
  let root ← words.head?
  let layout ← words[1]?
  let count ← words[2]?
  let opener ← registry.lookup layout
  if !(count.length = 32 ∧ (count.take 24).all (· = 0)) then none
  let k := (count.drop 24).foldl (fun acc b ↦ acc * 256 + b.toNat) 0
  let v := opener.vars
  if !(1 ≤ k ∧ words.length = 3 + k * (v + 1) ∧ root.length = 32) then none
  let claims ← (List.range k).mapM fun c ↦ do
    let point ← (List.range v).mapM fun j ↦ elementOfWord (words.getD (3 + c * (v + 1) + j) [])
    let value ← elementOfWord (words.getD (3 + c * (v + 1) + v) [])
    pure (⟨point, value⟩ : PcsQuotient.Claim)
  pure (rootOfWord root, opener, claims)

/-- `decode` under the deployment's registry. -/
def RecDeployment.decode (D : RecDeployment) (words : List (List UInt8)) :
    Option (Digest × Opener × List PcsQuotient.Claim) :=
  decodeWith D.registry words

/-- π1's calls with the setup's root `F` the deployment's (the constant root word of the call that has one). -/
def pi1CallsWith (calls : List (List CallWord)) (f : Digest) : List (List CallWord) :=
  calls.map fun call ↦ match call with
    | .const _ :: rest => .const (rootWordOfBytes (digestBytes f)) :: rest
    | other => other

/-- **A proof of the recursive verifier**: the stream (calldata after the selector and the public input) and the six
opening proofs the block holds, in call order: π1's `C1`, `C2`, `F`, then π2's `W`, the setup, `Q`. -/
structure RecProof where
  stream : Array UInt8
  c1 : Compile.Proof
  c2 : Compile.Proof
  f : Compile.Proof
  w : Compile.Proof
  setup : Compile.Proof
  q : Compile.Proof

def RecProof.openings (p : RecProof) : List Compile.Proof := [p.c1, p.c2, p.f, p.w, p.setup, p.q]

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **`PCS_OPEN`** over `F` on one call's words: decoded under the registry, then the registered opening. -/
def RecDeployment.pcsOpenWith (D : RecDeployment) (words : List (List UInt8)) (proof : Compile.Proof) : m Bool :=
  match D.decode words with
  | none => pure false
  | some (root, .pi1 vars, claims) => UniStatement.pcsOpenWith F vars root claims proof
  | some (root, .pi2 L, claims) => PcsQuotient.openingWith F L root claims proof

/-- **π2's IV** over `F` (`prover::iv`): π1-rec3's contract IV at π1's setup roots, the circuit's digest, π2's setup
root, π2's layout words. -/
def RecDeployment.ivWith (D : RecDeployment) (roots : RecSetupRoots) : m (List UInt8) := do
  let pi1 ← pi1IvWith F D.pi1.shape D.pi1.programIv roots.pi1
  let digest ← D.pi2.digestWith F
  RecStatement.ivWith F pi1 digest (digestBytes roots.pi2) D.pi2.circuit.logN

/-- **The recursive verifier** over `F` on the setup's roots: π2's verifier on the calldata (its IV `ivWith`), its
verdict, then the six `PCS_OPEN` calls, word for word as the contract makes them (`pcsCalls`, π1's `F` root word and
π2's setup root the deployment's). -/
def RecDeployment.verifierWith (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32)
    (proof : RecProof) : m Bool := do
  let iv ← D.ivWith F roots
  let o ← runWith F D.spec iv input.toList proof.stream
  if !o.accepts then return false
  match o.result with
  | .error _ => return false
  | .ok r =>
    let calls := pcsCalls D.pi2.circuit (pi1CallsWith D.pi1Calls roots.pi1.bytecode) (digestBytes roots.pi2)
      proof.stream r
    if calls.length ≠ 6 then return false
    let mut ok := true
    for (words, p) in calls.zip proof.openings do
      ok := ok && (← D.pcsOpenWith F words p)
    return ok

/-- **The setup** over `F`: π1's (the setup stack `F`, Flock's `A0`, `B0`) and π2's (`κ`, `κ + σ`). -/
def RecDeployment.setupTreesWith (D : RecDeployment) : m RecSetupTrees := do
  let t1 ← UniStatement.setupTreesWith F D.pi1
  let t2 ← D.pi2.setupTreeWith F
  return ⟨t1, t2⟩

end With

/-! ## The extractor -/

/-- The digest a root word of the stream names, at a stream offset. -/
def streamRoot (stream : Array UInt8) (at' : ℕ) : Digest := rootOfWord (streamWord stream at')

/-- **A committed word** under a root: the leaves the unique preimages `pre` commit to, `2^(μ − 6 + 1)` leaves of `64`
words (`Replay.leavesUnder`). -/
def committedWord (pre : Digest → ℕ → Option (List UInt8)) (μ : ℕ) (root : Digest) : ℕ → List K :=
  let height := μ - 6 + 1
  leafAt (PcsQuotient.Replay.leavesUnder pre 64 height root) height 64

/-- A word's candidate stacks: the fast path's, the unique decoder's, the list decoder's. -/
def candidates (μ : ℕ) (word : ℕ → List K) : List (Vector K (2 ^ μ)) :=
  fastStacks μ 1 word ++ PcsQuotient.UniqueDecoding.uniqueStacks μ 1 word ++ decodeStacks μ 1 word

/-- **The extractor on given preimages**: for each candidate of π2's `W` (its root after π1's public data), π1's row
counts read off its witness values; then the first candidate `C1` stack (its root π2's stream's first public root)
whose Lv42 stack at those counts satisfies the relation. -/
def recExtractFrom (D : RecDeployment) (input : Vector UInt8 32) (pre : Digest → ℕ → Option (List UInt8))
    (proof : RecProof) : Option ((rows : List ℕ) × D.pi1.Stack rows) :=
  let c := D.pi2.circuit
  let at' := rootsAt c.reads
  let wL := (layoutsOf c.logN).1
  let wWord := committedWord pre wL.logN (streamRoot proof.stream (at'.getD (rootReads c.reads) 0))
  let μ := (UniStatement.c1Layout D.pi1.shape).vars
  let c1Word := committedWord pre μ (streamRoot proof.stream (at'.getD 0 0))
  (candidates wL.logN wWord).findSome? fun w ↦
    let table := Array.ofFn (n := 2 ^ c.logN) fun i ↦ wL.readEntry (fun j ↦ w.toArray.getD j 0) i.val
    let rows := D.pi1Rows fun i ↦ UniStatement.basisValue table c.logN i
    (candidates μ c1Word).findSome? fun stack ↦
      let q := UniStatement.lv42Stack D.pi1.prog (D.pi1.sizes rows) D.pi1.shape fun i ↦ stack.toArray.getD i 0
      if D.pi1.Relation rows input q then some ⟨rows, q⟩ else none

/-- **The extractor** in the random-permutation model: `recExtractFrom` on the unique preimages of the setup's
evaluations and the transcript's. -/
def recExtractor (D : RecDeployment) (input : Vector UInt8 32) (setupEvals : List (List UInt8 × Digest))
    (T : OracleQueryLog) (proof : RecProof) : Option ((rows : List ℕ) × D.pi1.Stack rows) :=
  let paths := setupEvals ++
    PcsQuotient.Replay.transcriptEvaluations PcsQuotient.merkleLengths (LeanVM.permutationQueries T)
  recExtractFrom D input (PcsQuotient.Replay.preimageIn (PcsQuotient.Replay.preimageIndex paths)) proof

/-- An extractor's shape: from the statement, the setup's evaluations, the transcript and the proof, π1's row counts and
a stack at them. -/
abbrev RecExtractor (D : RecDeployment) : Type :=
  Vector UInt8 32 → List (List UInt8 × Digest) → OracleQueryLog → RecProof →
    Option ((rows : List ℕ) × D.pi1.Stack rows)

/-! ## Knowledge soundness -/

/-- An adversary: given the setup's roots, a public input and a proof, with coins, `π` and `π⁻¹`. -/
abbrev RecAdversary : Type := RecSetupRoots → OracleComp RandomPermutationOracles (Vector UInt8 32 × RecProof)

/-- An outcome: the statement and the proof, the verdict, the setup's evaluations, the transcript. -/
abbrev RecOutcome : Type :=
  ((Vector UInt8 32 × RecProof) × Bool) × List (List UInt8 × Digest) × OracleQueryLog

/-- **The knowledge-soundness experiment**: the setup over `π`, the adversary given its roots (its queries logged),
then the recursive verifier over `π`. -/
noncomputable def recSoundnessExperiment (D : RecDeployment) (A : RecAdversary) : ProbComp RecOutcome :=
  runWithRandomPermutation do
    let trees ← D.setupTreesWith queryPermutation
    let (z, transcript) ← (simulateQ loggedOracles (A trees.roots)).run []
    let accepted ← D.verifierWith queryPermutation trees.roots z.1 z.2
    return ((z, accepted), trees.evaluations, transcript)

/-- **The adversary breaks knowledge soundness**: the recursive verifier accepts, and the extractor outputs no row
counts and stack satisfying leanVM 42422001's relation for the public input. -/
def RecBreaksKnowledgeSoundness (D : RecDeployment) (ext : RecExtractor D) (z : RecOutcome) : Prop :=
  z.1.2 = true ∧ ¬ ∃ w, ext z.1.1.1 z.2.1 z.2.2 z.1.1.2 = some w ∧ D.pi1.Relation w.1 z.1.1.1 w.2

/-- **Knowledge soundness for the extractor `ext`**, error `ε Q` for `Q` calls of `π` and `π⁻¹`. -/
def RecKnowledgeSoundnessWith (D : RecDeployment) (ext : RecExtractor D) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : RecAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    Pr{let z ← recSoundnessExperiment D A}[RecBreaksKnowledgeSoundness D ext z] ≤ ε Q

/-- **Knowledge soundness** of the recursive verifier (π2's verifier and the six openings) against leanVM 42422001's
relation, for the explicit extractor `recExtractor`. -/
def RecKnowledgeSoundness (D : RecDeployment) (ε : ℕ → ℝ≥0∞) : Prop :=
  RecKnowledgeSoundnessWith D (recExtractor D) ε

/-! ## Completeness -/

/-- A prover: from the public input, π1's row counts and a stack of Lv42's layout at them, a proof of the recursive
verifier (or none), with coins, `π` and `π⁻¹` (it recomputes the public setup as it needs). -/
abbrev RecProver (D : RecDeployment) : Type :=
  Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp RandomPermutationOracles (Option RecProof)

/-- **The completeness experiment**: the setup, the prover's proof, the recursive verifier's verdict, over `π`. -/
noncomputable def recCompletenessExperiment (D : RecDeployment) (P : RecProver D) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.pi1.Stack rows) : ProbComp Bool :=
  runWithRandomPermutation do
    let trees ← D.setupTreesWith queryPermutation
    match ← P input rows q with
    | none => return false
    | some proof => D.verifierWith queryPermutation trees.roots input proof

/-- **Completeness of the prover `P`**: its proof of a public input with an `M3Honest` stack, at row counts that fit
π1's shape, is rejected with probability at most `δ`. -/
def RecCompletenessWith (D : RecDeployment) (P : RecProver D) (δ : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation rows input q →
    Pr{let v ← recCompletenessExperiment D P input rows q}[v = false] ≤ δ

/-- **Completeness** of the recursive verifier, for a prover given explicitly (π1's and π2's honest provers composed,
which are not transcribed). -/
def RecCompleteness (D : RecDeployment) (P : RecProver D) (δ : ℝ≥0∞) : Prop := RecCompletenessWith D P δ

end RecStatement
