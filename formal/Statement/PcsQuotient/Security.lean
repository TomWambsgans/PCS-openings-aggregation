-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The model, the experiment's shape and the form of the statements are leanerVM's (branch `mumbai`,
-- commit 6175f1a0, MIT OR Apache-2.0: `Statement/RandomPermutation.lean`, `Statement/LeanVm.lean`'s
-- `soundnessExperiment`, `KnowledgeSoundness`, `Completeness`), adapted to this protocol.
module

public import PcsQuotient.Extractor
public import PcsQuotient.Simulator
public import VCVio.EvalDist.ProbabilityNotation

/-!
# Knowledge soundness, completeness and zero knowledge

The end statements, in the **random-permutation model** of leanerVM's `mumbai`
(`Statement/RandomPermutation.lean` there): one uniformly random permutation `π` of the Keccak-f[1600]
state, lazily sampled, which every party queries forward (`π x`) and inverse (`π⁻¹ y`); Keccak-256 is
the sponge over `π`. Every hash of the protocol is Keccak-256 over `π`: the reduction's chain
(`Transcript.lean`), the WHIR commitments' Merkle trees and the openings' duplex (`Opening.lean`), and
the circuit's commitment, computed over `π` by the **setup** before the adversary runs (`setupWith`).
The relation's hashes are the deployed Keccak-256 (`Relation.lean`): the circuit computes the
deployed Keccak-f[1600], independent of `π`.

* **Knowledge soundness** (`KnowledgeSoundness ε`): for every adversary of at most `Q` calls of `π`
  and `π⁻¹`, given the setup's commitment (the circuit's index root), the verifier accepts its
  statement and proof while **`extractor`**, reading only the
  statement, the proof, the adversary's transcript and the public setup's tree (the circuit
  commitment's Merkle tree, as its Keccak-256 evaluations), outputs no witness, with probability at
  most `ε Q`.
* **Completeness** (`Completeness δ`): for every statement and witness of the relation, the honest
  prover's (`prover`) proof, with uniform coins (masks and padding), is rejected with probability at most `δ`.
* **Zero knowledge** (`ZeroKnowledge ζ`, statistical, the permutation programmable): for every
  statement and witness of the relation and every distinguisher of at most `Q` calls of `π` and
  `π⁻¹`, its verdict on the honest proof in the model and on **`simulator`**'s proof, the simulator
  answering its queries, differ in probability by at most `ζ Q`. `ZeroKnowledgeWith s₀ sim simOracle ζ`
  is the same for any simulator (`sim`, its oracle `simOracle`, its state from `s₀`):
  `ZeroKnowledge ζ` is it at this package's `simulator`, a tested heuristic; the end theorem
  (`formal/EndToEnd/ZK`) proves `ZeroKnowledgeWith` for `formal/QuotientZk`'s simulator in this shape
  (`README.md`, "The simulator").

**The bounds are parameters** (`ε`, `δ`, `ζ`). A bound is part of what is proved: `KnowledgeSoundness ε`
for `ε = 1` says nothing. The end theorems (`formal/EndToEnd`) fix them: `KnowledgeSoundness
Soundness.ksBound` (about `2^-62` at `Q = 2^64`) and `Completeness E2ECompleteness.deltaDeployed` (below
`2^-162`) are proved with no hypothesis; `ZeroKnowledgeWith` for `formal/QuotientZk`'s simulator, at about
`2^-113`, is in progress (`README.md`, "What is proved").

**Zero knowledge rests on the hidden layouts** (`crates/quotient/HIDING.md`): the prover pads its two
secret tables (`Layout.hidden`), and its opening of a table is then distributed as that of any other table
with the same claims, under conditions (S) and (R) on the challenges, which `formal/QuotientSecurity/Hiding`
proves for the deployed layouts outside a small set of challenges (`deployed_prEvent_le`). The statement's
prover takes its padding uniform; the deployed one expands a 32-byte seed by ChaCha12 (a pseudorandom
generator, outside this model).

**One Keccak-256.** Deployed, one Keccak-256 serves the reduction's chain, the WHIR Merkle trees
(`hash_pair` is byte for byte the relation's `pair`), the openings' duplex and the relation. As in mumbai, the
model has one random permutation `π`, which every hash of the protocol queries (there is no private oracle);
the relation is over the deployed Keccak-256, which the circuit computes. Knowledge soundness needs no
collision clause: the extracted secret satisfies the relation exactly. A consumer that reads more from a
statement than the relation says (that `y` names one `x`) gets it up to a collision of the deployed
Keccak-256, `StatementBinds`, as mumbai's `DigestBinds`.
-/

@[expose] public section

namespace PcsQuotient

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec Common
open scoped ENNReal

/-! ### The deployed system -/

/-- **The setup** over `F`: the membership circuit's commitment (`Circuit.indexRootWith`, at
`logRows = 22`). -/
def setupWith {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState) : m Digest :=
  (membership logRows).indexRootWith F

/-- **The setup's tree** over `F`: the Merkle tree of the membership circuit's commitment
(`Circuit.indexTreeWith`), whose root is `setupWith F`'s. The knowledge-soundness experiment computes
it, and its extractor reads its Keccak-256 evaluations (`Tree.evaluations`): the setup is public. -/
def setupTreeWith {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState) :
    m LeanVM.Prover.Tree :=
  (membership logRows).indexTreeWith F

/-- **The verifier** over `F`, on the circuit committed as `indexRoot` (`Verifier.lean`'s `verifyWith`,
at the membership circuit's size). -/
def verifier {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState) (indexRoot : Digest)
    (stmt : Statement) (proof : Proof) : m Bool :=
  verifyWith F logRows indexRoot stmt proof

/-- Proofs of work: the honest prover and the simulator try `2^25` nonces each (as mumbai's prover). -/
def nonceFuel : ℕ := 2 ^ 25

/-- **The deployed circuit commitment**, over Keccak-f[1600]: the root the deployed verifier holds,
`8fd9a050958016776a4e586439f3e9542dfa438a797e2e2260056e7104043ca9` (the differential test checks that the
Lean circuit's commitment is the Rust's, `--index`; computing it takes about five minutes, so it is a
function of `()`: a compiled constant would be computed whenever a program importing it starts). -/
def deployedIndexRoot (_ : Unit) : Digest :=
  Id.run (setupWith (m := Id) fun s ↦ pure (keccakF1600 s))

set_option compiler.extract_closed false in
/-- **The deployed verifier**, over Keccak-f[1600], on the deployed circuit commitment. -/
def deployedVerifier (stmt : Statement) (proof : Proof) : Bool :=
  Id.run (verifier (m := Id) (fun s ↦ pure (keccakF1600 s)) (deployedIndexRoot ()) stmt proof)

/-! ### The model's calls -/

/-- A uniform 64-bit word from the model's coins. -/
def coinWord : OracleComp RandomPermutationOracles UInt64 := do
  let n ← liftM (RandomPermutationOracles.query (.inl (2 ^ 64 - 1)))
  return UInt64.ofNat (n : Fin (2 ^ 64 - 1 + 1)).val

/-- **Uniform masks** from the model's coins: twelve uniform words of `K`. -/
def sampleMasks : OracleComp RandomPermutationOracles Masks := do
  let w ← (List.range 12).mapM fun _ ↦ coinWord
  return fun j i ↦ K.ofLane (w.getD (3 * j.val + i.val) 0)

/-- **Uniform padding** for a table of layout `L` from the model's coins: a uniform word at every position of
every lane's stream (`2^ℓ` words a lane, as many as a stream can be read at). The deployed prover draws it
from ChaCha12 keyed by Keccak-256 of a secret 32-byte seed (`Table::hidden`); the statement's prover takes it
uniform. -/
def samplePadding (L : Layout) : OracleComp RandomPermutationOracles Padding := do
  let lane := 2 ^ L.logLane
  let w ← (List.range (L.lanes.length * lane)).mapM fun _ ↦ coinWord
  let words := w.toArray
  return fun l i ↦ K.ofLane (words.getD (l * lane + i) 0)

/-- The honest prover's coins: the masks and the two secret tables' padding. -/
def sampleCoins : OracleComp RandomPermutationOracles (Masks × Padding × Padding) := do
  return (← sampleMasks, ← samplePadding (witnessLayout logRows),
    ← samplePadding (quotientLayout logRows))

/-! ### The honest prover, the extractor, the simulator -/

/-- **The honest prover** over `F`: `proverWith` (`Prover.lean`), the Rust's `prove` then `open`, on the
membership circuit's cells of the secret, with the coins given (the masks and the two tables' padding),
`2^25` nonces per proof of work. -/
def prover {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState) (stmt : Statement)
    (w : Secret) (coins : Masks × Padding × Padding) : m (Option Proof) :=
  proverWith F nonceFuel stmt w coins.1 coins.2.1 coins.2.2

/-- **The extractor**: `transcriptExtractorFor` (`Extractor.lean`) at the membership circuit. From the
statement, the public setup's tree (its Keccak-256 evaluations `setupEvals`, `Tree.evaluations`), the
adversary's transcript and the proof, a secret: the witness table's tree inverted through the setup's
and the transcript's Keccak-256 evaluations (hash maps), its word decoded (interpolation, then unique
decoding, then list decoding, each only if the stages before give no witness), and the first
candidate's cells' input bits that spell a witness. Straight-line: it reads the setup's tree and the
transcript, it neither queries `π` nor runs the adversary again. Its cost is `Extractor.lean`'s table. -/
def extractor (stmt : Statement) (setupEvals : List (List UInt8 × Digest)) (T : OracleQueryLog)
    (proof : Proof) : Option Secret :=
  transcriptExtractorFor (membership logRows) stmt setupEvals T proof

/-- **The simulator's proof** (`Simulator.simulate`, `2^25` nonces per proof of work), its state the
permutation it answers. -/
def simulator (stmt : Statement) : Simulator.SimM (Option Proof) :=
  Simulator.simulate nonceFuel stmt

/-! ### Knowledge soundness -/

/-- An adversary in the random-permutation model: given the public setup's commitment (the circuit's
index root, which it could also recompute with `π`), a computation with private coins and oracle
access to `π` and `π⁻¹` that outputs a statement and a proof. -/
abbrev Adversary : Type := Digest → OracleComp RandomPermutationOracles (Statement × Proof)

/-- An outcome of the experiment: the statement and the proof, the verdict, the setup's Keccak-256
evaluations (its tree, `Tree.evaluations`), and the adversary's transcript, its queries and their
answers in order. -/
abbrev Outcome : Type :=
  ((Statement × Proof) × Bool) × List (List UInt8 × Digest) × OracleQueryLog

abbrev Outcome.statement (z : Outcome) : Statement := z.1.1.1
abbrev Outcome.proof (z : Outcome) : Proof := z.1.1.2
abbrev Outcome.accepted (z : Outcome) : Prop := z.1.2 = true
abbrev Outcome.setupEvaluations (z : Outcome) : List (List UInt8 × Digest) := z.2.1
abbrev Outcome.transcript (z : Outcome) : OracleQueryLog := z.2.2

/-- **The knowledge-soundness experiment**: the setup (the circuit commitment's tree over `π`), the
adversary given the tree's root, its queries recorded (`Common.loggedOracles`), then the verifier over
`π` on its statement and proof with the tree's root, the whole game run against the lazily sampled
permutation from no edge; the outcome holds the setup tree's Keccak-256 evaluations, public, for the
extractor. -/
noncomputable def soundnessExperiment (A : Adversary) : ProbComp Outcome :=
  runWithRandomPermutation do
    let tree ← setupTreeWith queryPermutation
    let (z, transcript) ← (simulateQ loggedOracles (A tree.root)).run []
    let accepted ← verifier queryPermutation tree.root z.1 z.2
    return ((z, accepted), Tree.evaluations tree, transcript)

/-- **The adversary breaks knowledge soundness**: the verifier accepts, and `extractor`, on the setup's
tree and the adversary's transcript, outputs no witness of the statement. -/
def BreaksKnowledgeSoundness (z : Outcome) : Prop :=
  z.accepted ∧ ¬ ∃ w, extractor z.statement z.setupEvaluations z.transcript z.proof = some w ∧
    Relation z.statement w

/-- **Knowledge soundness in the random-permutation model**, for the extractor `extractor`, with the
error `ε Q` for `Q` calls of `π` and `π⁻¹` by the adversary on any commitment it is given (its coins
free). -/
def KnowledgeSoundness (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : Adversary) (Q : ℕ), (∀ root, QueryCostAtMost (A root) permutationCallCost Q) →
    Pr{let z ← soundnessExperiment A}[BreaksKnowledgeSoundness z] ≤ ε Q

/-! ### Completeness -/

/-- **The completeness experiment**: the setup, the honest prover's proof with uniform coins, then the
verifier's verdict, all over `π`; no proof is a failure. -/
noncomputable def completenessExperiment (stmt : Statement) (w : Secret) : ProbComp Bool :=
  runWithRandomPermutation do
    let indexRoot ← setupWith queryPermutation
    let coins ← sampleCoins
    match ← prover queryPermutation stmt w coins with
    | none => return false
    | some proof => verifier queryPermutation indexRoot stmt proof

/-- **Completeness in the random-permutation model**: the honest prover's proof of a statement it has
a witness for is rejected with probability at most `δ`. -/
def Completeness (δ : ℝ≥0∞) : Prop :=
  ∀ (stmt : Statement) (w : Secret), Relation stmt w →
    Pr{let v ← completenessExperiment stmt w}[v = false] ≤ δ

/-! ### Zero knowledge -/

/-- A distinguisher: from the proof (`none` if the prover made none), a verdict, with private coins
and oracle access to `π` and `π⁻¹`. It may depend on the statement and the witness (it is quantified
after them). -/
abbrev Distinguisher : Type := Option Proof → OracleComp RandomPermutationOracles Bool

/-- **The real experiment**: the honest prover's proof of `stmt` from `w` with uniform coins over `π`,
then the distinguisher, against the lazily sampled permutation. -/
noncomputable def realExperiment (stmt : Statement) (w : Secret) (D : Distinguisher) :
    ProbComp Bool :=
  runWithRandomPermutation do
    let coins ← sampleCoins
    D (← prover queryPermutation stmt w coins)

/-- **The ideal experiment of a simulator**: `sim`'s proof of `stmt`, without the witness, then the
distinguisher, its every query answered by the simulator's oracle `simOracle`, the simulator's state
(of type `S`) starting at `s₀`. -/
def idealExperimentWith {S : Type} (s₀ : S) (sim : Statement → StateT S ProbComp (Option Proof))
    (simOracle : QueryImpl RandomPermutationOracles (StateT S ProbComp)) (stmt : Statement)
    (D : Distinguisher) : ProbComp Bool :=
  (do
    let proof ← sim stmt
    simulateQ simOracle (D proof)).run' s₀

/-- **The ideal experiment** of this package's `simulator` (`Simulator.simOracle`, from no edge). -/
def idealExperiment (stmt : Statement) (D : Distinguisher) : ProbComp Bool :=
  idealExperimentWith (S := Simulator.SimState) {} simulator Simulator.simOracle stmt D

/-- **Statistical zero knowledge in the programmable random-permutation model, for a simulator**
`sim` with its oracle `simOracle` (from the state `s₀`), with the error `ζ Q` for a distinguisher of at
most `Q` calls of `π` and `π⁻¹` (its coins free): its verdicts in the real experiment and in the ideal
experiment of `sim` differ in probability by at most `ζ Q`. The simulator is a parameter so that the end
theorem can name the simulator it proves (`README.md`, "The simulator"). -/
def ZeroKnowledgeWith {S : Type} (s₀ : S) (sim : Statement → StateT S ProbComp (Option Proof))
    (simOracle : QueryImpl RandomPermutationOracles (StateT S ProbComp)) (ζ : ℕ → ℝ≥0∞) : Prop :=
  ∀ (stmt : Statement) (w : Secret), Relation stmt w →
  ∀ (D : Distinguisher) (Q : ℕ), (∀ proof, QueryCostAtMost (D proof) permutationCallCost Q) →
    Pr{let b ← realExperiment stmt w D}[b = true] ≤
        Pr{let b ← idealExperimentWith s₀ sim simOracle stmt D}[b = true] + ζ Q ∧
      Pr{let b ← idealExperimentWith s₀ sim simOracle stmt D}[b = true] ≤
        Pr{let b ← realExperiment stmt w D}[b = true] + ζ Q

/-- **Statistical zero knowledge for this package's `simulator`** (`ZeroKnowledgeWith` at `simulator`,
`Simulator.simOracle`, from no edge). -/
def ZeroKnowledge (ζ : ℕ → ℝ≥0∞) : Prop :=
  ZeroKnowledgeWith (S := Simulator.SimState) {} simulator Simulator.simOracle ζ

/-! ### Collisions of the deployed Keccak-256 -/

/-- **A collision of the deployed Keccak-256** on two 64-byte blocks (`pair`, `Relation.lean`). -/
def PairCollision (a b : Bytes32 × Bytes32) : Prop := a ≠ b ∧ pair a.1 a.2 = pair b.1 b.2

/-- **The statement binds `x`, up to a collision** (mumbai's `DigestBinds` for this relation): two secrets of
one statement have the same `x`, or their hashes of `y`, `(x, 0x11^32)` and `(x', 0x11^32)`, collide. -/
def StatementBinds : Prop :=
  ∀ w w' : Secret, w.statement = w'.statement →
    w.x = w'.x ∨ PairCollision (w.x, Vector.replicate 32 yPad) (w'.x, Vector.replicate 32 yPad)

/-! ### The end theorems -/

/-- **The end theorems**, at the bounds `ε`, `δ`, `ζ`. The first two fields are proved in
`formal/EndToEnd` (`Soundness.knowledgeSoundness` at `ε = Soundness.ksBound`,
`E2ECompleteness.completeness_end` at `δ = E2ECompleteness.deltaDeployed`); `zeroKnowledge` is about this
package's heuristic `simulator`, which no theorem covers (the zero-knowledge end theorem, in progress, is
`ZeroKnowledgeWith` for `formal/QuotientZk`'s simulator); `statementBinds` is immediate and not proved in
Lean (`README.md`, "What is proved"). -/
structure Theorems (ε : ℕ → ℝ≥0∞) (δ : ℝ≥0∞) (ζ : ℕ → ℝ≥0∞) : Prop where
  /-- Knowledge soundness for the straight-line `extractor`. -/
  knowledgeSoundness : KnowledgeSoundness ε
  /-- Completeness of the honest `prover`. -/
  completeness : Completeness δ
  /-- Statistical zero knowledge for `simulator` (the tables hidden as `crates/quotient/HIDING.md` says;
  its conditions (S), (R) on the challenges are part of what `ζ` must cover). `simulator` is a tested
  heuristic: no theorem covers it. -/
  zeroKnowledge : ZeroKnowledge ζ
  /-- The statement binds `x` up to a collision of the deployed Keccak-256 (needed by no other field: an
  extracted secret satisfies the relation exactly). -/
  statementBinds : StatementBinds

end PcsQuotient

end
