-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The model, the experiments' shape and the form of the
-- statements are `formal/UniStatement`'s (`Security.lean`, `RecSecurity.lean`, after `formal/Statement`'s
-- `PcsQuotient.Security` and leanerVM `mumbai` 6175f1a0's `Statement/LeanVm.lean`, MIT OR Apache-2.0); the relation is
-- Lv42's (`formal/Lv42`, leanerVM `mumbai` f0393df4's `M3Holds`); π1-rec3's graph and its merge hazard are
-- `formal/RecGraph`'s. Transcribed from `crates/leanvm_rec/src/pi2/circuit.rs` (`Circuit::digest`), `prover.rs`
-- (`Setup::new`) and `contract.rs` (`registry`, the calls), and `crates/leanvm_flock_gas/src/evm/machine.rs`
-- (`decode`, `root_of_word`), branch `leanvm-rec` @ 2b22581.
import RecStatement.Calls
import RecStatement.Data
import UniStatement.RecSecurity
import RecGraph.Pi1.Main
import RecGraph.Emitted
import RecCircuit.Sound

/-!
# The recursive verifier's end statements, against leanVM 42422001's relation

Statements only, no proof (the composition proves them).

**Two models, which do not compose formally.** π2's circuit computes π1-rec3's Fiat–Shamir challenges with the
**real Keccak-f[1600]**: a circuit is a fixed function (`RecCircuit.compile_sound`, `keccak_out`: its ports carry
`RecGraph.evalNodes` over Keccak-f[1600]). π1-rec3's knowledge soundness is proved in the **random-permutation model**
(`UniSound.Rec3Ref.uniKnowledgeSoundness_closed_rec3`, 128.49 bits). No circuit computes a random permutation, so the
statements come in two parts, as the earlier proofs' caveat says (AGENTS.md: "the theorems are in the
random-permutation model and do not formally compose with the EVM one, which holds at the real Keccak-f[1600]"):

1. **π2's part, in the random-permutation model** (`RecKnowledgeSoundness2`, `RecCompleteness2`): one random
   permutation `π` for π2's own Fiat–Shamir (the contract's transcript and IV), the circuit's digest, the WHIR
   commitments and the six openings. If the contract accepts, π2's explicit extractor (`recExtractor2`) outputs
   π1's stream `s` on which **π1-rec3's recorded graph, run with Keccak-f[1600]**, accepts, its three `PCS_OPEN` calls
   being the contract's (which `PCS_OPEN` attested) (`Pi1GraphAccepts`); but with probability `ε2 Q`.
2. **The end-to-end corollaries, against Lv42's `M3Holds`** (`RecKnowledgeSoundness`, `RecCompleteness`), under named
   hypotheses about π1-rec3 **at Keccak-f[1600]**:
   * `Pi1FsKeccak ε1`: π1-rec3 is knowledge sound with its Fiat–Shamir instantiated by Keccak-f[1600] (its openings
     and commitments over `π`), error `ε1 Q`, for the adversaries of the recursive setup. **Its justification is
     π1-rec3's random-permutation theorem** (`uniKnowledgeSoundness_closed_rec3`): the Fiat–Shamir heuristic for
     Keccak-f[1600]. It is not provable.
   * `Pi1HazardKeccak εh`: π1-rec3's run at Keccak-f[1600] avoids the merge hazard (`RecGraph.MergeHazard`, where the
     recorded graph merges by symbol what the verifier merges by value), but with probability `εh Q`; justified by
     `RecGraph.hazard_prob` (`2^19/|E|` a challenge) for random challenges, the same heuristic.
   * `RecGraph.Pi1.Pi1GraphIsVerifier`: off the hazard, the recorded graph is π1-rec3's verifier (RecGraph's target;
     **proved**, `RecGraph.Pi1.pi1GraphIsVerifier`, for every permutation function, Keccak-f[1600] included).

   The conclusion's error is `ε2 + ε1 + εh`. Completeness likewise: π2's completeness is over its own coins and `π`
   (`RecCompleteness2`); π1-rec3's completeness at Keccak-f[1600] is the named hypothesis `Pi1CompletenessKeccak δ1`,
   justified by `UniComplete.Rec3.uniCompletenessRec3_end_closed` (`δ < 2^-167`), its honest proofs off the hazard
   `Pi1HazardKeccakHonest δh`.

**The recursive verifier** (`RecDeployment.contractWith`) is the contract (`pi2::contract`): π2's verifier on the
calldata (`runWith`: the public input, then the stream with π1's roots and claims' elements, `W`'s and `Q`'s roots and
the 17 values), then **six `PCS_OPEN` calls**, each decoded under the contract's registry (`machine::decode`: a known
layout word, which fixes the variables, `k ≥ 1` claims, the exact length, every element's top 64 bits zero) and
opened by the Statement's WHIR opening: **π1's three** (`C1`, `C2`, π1's setup `F`; their points the 27 coordinates the
contract derives from π1-rec3's 14 pair challenges) on the plain layout of π1's stacks (`UniStatement.pcsOpenWith`, as
`UniStatement.verifyWithFs`), and **π2's three** (`W`, the setup, `Q` with its two claims in one call) on π2's layouts
(`PcsQuotient.openingWith`, `quotient::opening`). π1's verifier itself never runs: π2 proves its graph accepted.
The deployed EVM bytecode is linked to this model **by transcription and test**, not by a Lean proof (unlike the
membership verifier's `Evm.evm_accepts_iff_verifyWith`): `contract.rs`'s parity tests (`parity`, `parity_deployable`)
and `RecStatement`'s differential runner (64 streams). The deployed contract hard-codes π2's IV (`inst.iv`, the Rust's
from its digest and setup root); `RecDeployment.Real` pins those (`Data.digest`, `Data.setupRoot`) to the Lean
compiler's `σ`, `κ` at π1's reference IV, checked by evaluation (`RecCompose.DigestChecked`, `rec-real-check`).

**The deployment** (`RecDeployment`): π1's (`UniStatement.Deployment`: the program, the shape, leanVM's program IV),
**π2's circuit for π1's contract IV** (`Pi2Circuit`: the verifier's view, `Circuit`, and the setup columns `σ`, `κ`;
the IV is among `κ`'s constants, the seed of π1's transcript), π1's calls as the circuit names their words, and **where
π2's witness holds π1's stream** (`pi1Stream`: the circuit compiler's free bits, `RecCircuit.Compiled.decodeStream`).
`RecDeployment.Real` pins it to the circuit of π1-rec3's real proof. **π1's contract IV** is computed with
Keccak-f[1600] at π1's setup roots (`pi1IvAt`: it is π1's Fiat–Shamir's, which the circuit computes); **π2's IV**
(`RecDeployment.ivWith`, `prover::iv`) over `π`: π1's IV, π2's setup root, the circuit's digest, π2's layout words.

**The relation** is leanVM 42422001's, as `UniStatement.Deployment.Relation`: `M3Holds (leanIsaInstance
blake2sFlockSpec prog s) input q` at the sizes `s` of π1's row counts, which are π1's stream's (π2's witness), so the
extractor outputs them with the stack.

**The extractors** are explicit and computable. `recExtractor2`: the transcript's and the setup's Keccak-256
evaluations replayed; **π2's `W`** inverted under the root the stream names and decoded (the fast path, the unique
decoder, the list decoder, at `W`'s `2^m`, rate `1/2`), each candidate's witness values read (`basisValue`, the `B`
basis) and **π1's stream** read off them (`pi1Stream`), the first on which π1-rec3's graph's checks hold at
Keccak-f[1600]. `recExtractor`: then π1-rec3's own extractor (`UniStatement.uniExtractor`) on that stream with the
proof's three π1 openings, its row counts the stream's.
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

/-- **The recursive verifier's deployment**: π1's (program, shape, program IV); π2's circuit **for π1's contract IV**
(the IV is among the circuit's constants: the seed of π1's transcript, which the circuit hashes with Keccak-f[1600]);
π1's calls as the circuit names their words; and π1's stream as π2's witness holds it (the compiler's free bits,
`RecCircuit.Compiled.decodeStream`), a function of the witness's values at the positions. -/
structure RecDeployment where
  pi1 : UniStatement.Deployment
  pi2 : List UInt8 → Pi2Circuit
  pi1Calls : List (List CallWord)
  pi1Stream : (ℕ → K) → Array UInt8

/-- **π1's contract IV** at π1's setup roots, over Keccak-f[1600] (`contract_iv_for` at `FLOCK_REC3`): π1-rec3's
Fiat–Shamir is the circuit's, which computes Keccak-f[1600]. -/
def RecDeployment.pi1IvAt (D : RecDeployment) (roots : UniStatement.SetupRoots) : List UInt8 :=
  pi1Iv D.pi1.shape D.pi1.programIv roots

/-- π2's circuit at π1's setup roots: for their contract IV. -/
def RecDeployment.circuitAt (D : RecDeployment) (roots : UniStatement.SetupRoots) : Pi2Circuit :=
  D.pi2 (D.pi1IvAt roots)

/-- **The real deployment's setup columns are the circuit compiler's** (how the deployment builds them: `Setup::new`
of `adapt` of `compile`, at π1's contract IV): at every 32-byte π1 IV (π1's contract IV is a Keccak-256 digest) at
which the Lean compiler (`RecCircuit.compile`, the Rust's by `RecCircuitTest`) accepts π1-rec3's recorded graph at the
emitted graph's roots, π2's `σ` and `κ` are the compiled circuit's (`sigmaAt`, `kappaAt`). (Composition,
`lean-pi2-complete`: `RecCompose.Pi2SetupColumns` follows. `RecCompose.realDeployment` has it by construction.) -/
def RecDeployment.SetupFromCompiler (D : RecDeployment) : Prop :=
  ∀ (iv : List UInt8), iv.length = 32 → ∀ (c : RecCircuit.Compiled),
    RecCircuit.compile (RecCircuit.ofRG RecGraph.Pi1.pi1Graph RecGraph.Emitted.rootsAt iv) = .ok c →
      (D.pi2 iv).sigma = c.circuit.sigmaAt ∧ (D.pi2 iv).kappa = c.circuit.kappaAt

/-- **The real deployment's data**: π2's circuit for π1-rec3's real proof (the emitted tables at every IV, and at π1's
reference IV the `σ`, `κ` whose digest and setup root the Rust computed), π1's calls, the reference shape and leanVM's
program IV, and the setup columns the compiler's at every 32-byte IV (`SetupFromCompiler`).

**Inhabited**: `RecCompose.realDeployment prog` (σ, κ the Lean compiler's at every IV, π1's stream its `streamW`) has
it, `RecCompose.realDeployment_real`, given the two evaluated checks of the digest and the setup root
(`RecCompose.DigestChecked`, `RecCompose.SetupRootChecked`, `rec-real-check`) and `GraphsAgree`. The digest and setup
root clauses are used by no proof: they pin the model's σ, κ (from which the model's contract computes π2's IV over `π`)
to the deployed contract's constant IV, which the Rust computed from them. **The program is not pinned**
(`D.pi1.prog`): the end theorems hold for every program of the reference shape, the deployment's program; leanVM
42422001's program is not transcribed in Lean. -/
def RecDeployment.Real (D : RecDeployment) : Prop :=
  (∀ iv, (D.pi2 iv).circuit = Data.circuit) ∧ D.pi1Calls = Data.pi1Calls ∧ D.pi1.shape = UniStatement.reference ∧
    D.pi1.programIv = UniStatement.programIv ∧
    Id.run ((D.pi2 Data.pi1Iv).digestWith (m := Id) fun x ↦ pure (LeanVM.Semantics.keccakF1600 x)) = Data.digest ∧
    digestBytes (Id.run ((D.pi2 Data.pi1Iv).setupTreeWith (m := Id)
      fun x ↦ pure (LeanVM.Semantics.keccakF1600 x))).root = Data.setupRoot ∧
    D.SetupFromCompiler

/-- **The setup's roots**: π1's three (`F`, `A0`, `B0`) and π2's (the commitment of `κ`, `κ + σ`). -/
structure RecSetupRoots where
  pi1 : UniStatement.SetupRoots
  pi2 : Digest

/-- **The setup's trees**: π1's (UniStatement's) and π2's. -/
structure RecSetupTrees where
  pi1 : UniStatement.SetupTrees
  pi2 : LeanVM.Prover.Tree

def RecSetupTrees.roots (t : RecSetupTrees) : RecSetupRoots := ⟨t.pi1.roots, t.pi2.root⟩

/-- The setup's Keccak-256 evaluations, which the extractors read. -/
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

/-- The claims of a call's words after its three header words: `k` claims of `v` coordinates and a value. -/
def claimsOfWords (words : List (List UInt8)) (k v : ℕ) : Option (List PcsQuotient.Claim) :=
  (List.range k).mapM fun c ↦ do
    let point ← (List.range v).mapM fun j ↦ elementOfWord (words.getD (3 + c * (v + 1) + j) [])
    let value ← elementOfWord (words.getD (3 + c * (v + 1) + v) [])
    pure (⟨point, value⟩ : PcsQuotient.Claim)

/-- A count word's number (its last eight bytes; the first 24 must be zero). -/
def countOfWord (w : List UInt8) : Option ℕ :=
  if w.length = 32 ∧ (w.take 24).all (· = 0) then some ((w.drop 24).foldl (fun acc b ↦ acc * 256 + b.toNat) 0)
  else none

/-- **`decode(input, registry)`**: the root word, the layout word, `k ≥ 1` claims of the registered variables; every
element's top 64 bits zero, the exact length. -/
def decodeWith (registry : List (List UInt8 × Opener)) (words : List (List UInt8)) :
    Option (Digest × Opener × List PcsQuotient.Claim) := do
  let root ← words.head?
  let layout ← words[1]?
  let opener ← registry.lookup layout
  let k ← countOfWord (← words[2]?)
  let v := opener.vars
  if !(1 ≤ k ∧ words.length = 3 + k * (v + 1) ∧ root.length = 32) then none
  pure (rootOfWord root, opener, ← claimsOfWords words k v)

/-- **`PCS_OPEN`** over `F` on one call's words: decoded under the registry, then the registered opening. -/
def pcsOpenAt {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState) (registry : List (List UInt8 × Opener))
    (words : List (List UInt8)) (proof : Compile.Proof) : m Bool :=
  match decodeWith registry words with
  | none => pure false
  | some (root, .pi1 vars, claims) => UniStatement.pcsOpenWith F vars root claims proof
  | some (root, .pi2 L, claims) => PcsQuotient.openingWith F L root claims proof

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

/-- **π2's IV** over `F` (`prover::iv`): π1-rec3's contract IV (Keccak-f[1600]) at π1's setup roots, the circuit's
digest, π2's setup root, π2's layout words. -/
def RecDeployment.ivWith (D : RecDeployment) (roots : RecSetupRoots) : m (List UInt8) := do
  let c := D.circuitAt roots.pi1
  let digest ← c.digestWith F
  RecStatement.ivWith F (D.pi1IvAt roots.pi1) digest (digestBytes roots.pi2) c.circuit.logN

/-- **The contract** over `F` on the setup's roots: π2's verifier on the calldata (its IV `ivWith`), its verdict, then
the six `PCS_OPEN` calls, word for word as the contract makes them (`pcsCalls`, π1's `F` root word and π2's setup root
the setup's), each decoded and opened (`pcsOpenAt`). Its verdict, and the calls' words (none if the verifier
rejects). -/
def RecDeployment.contractWith (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32)
    (proof : RecProof) : m (Bool × List (List (List UInt8))) := do
  let c := D.circuitAt roots.pi1
  let iv ← D.ivWith F roots
  let o ← runWith F (Spec.of c.circuit) iv input.toList proof.stream
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
      ok := ok && (← pcsOpenAt F reg words p)
    return (ok, calls)

/-- **The recursive verifier** over `F`: the contract's verdict. -/
def RecDeployment.verifierWith (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32)
    (proof : RecProof) : m Bool := do
  return (← D.contractWith F roots input proof).1

/-- **The setup** over `F`: π1's (the setup stack `F`, Flock's `A0`, `B0`) and π2's (`κ`, `κ + σ` of the circuit for
π1's contract IV at those roots). -/
def RecDeployment.setupTreesWith (D : RecDeployment) : m RecSetupTrees := do
  let t1 ← UniStatement.setupTreesWith F D.pi1
  let t2 ← (D.circuitAt t1.roots).setupTreeWith F
  return ⟨t1, t2⟩

end With

/-! ## π1-rec3 at Keccak-f[1600] -/

/-- A π1 opening: the root, the layout word, the claims. -/
abbrev Pi1Opening : Type := Digest × List UInt8 × List PcsQuotient.Claim

/-- **A call of π1's own contract** (the bytes `RecGraph`'s outputs and `UniStatement.pcsCalls` give), decoded: its
root (the setup's as its hash, by the layout word's code `0x5503`; `C1`'s, `C2`'s as π1's stream carries them), layout
word and claims (the layout word's variables, byte 24). -/
def decodePi1Call (call : List UInt8) : Option Pi1Opening := do
  if call.length % 32 ≠ 0 then none
  let words := (List.range (call.length / 32)).map fun j ↦ (call.drop (32 * j)).take 32
  let root ← words.head?
  let layout ← words[1]?
  let k ← countOfWord (← words[2]?)
  let v := UniStatement.layoutWordVars layout
  if !(1 ≤ k ∧ words.length = 3 + k * (v + 1)) then none
  let code := (layout.getD 22 0).toNat * 256 + (layout.getD 23 0).toNat
  let digest := if code = 0x5503 then UniStatement.digestOfBytes32 root else rootOfWord root
  pure (digest, layout, ← claimsOfWords words k v)

/-- **The contract's π1 openings**: its first three calls decoded under the registry. -/
def contractPi1Openings (registry : List (List UInt8 × Opener)) (calls : List (List (List UInt8))) :
    Option (List Pi1Opening) :=
  (calls.take 3).mapM fun words ↦ (decodeWith registry words).map fun x ↦ (x.1, words.getD 1 [], x.2.2)

/-- **π1-rec3's graph accepts at Keccak-f[1600], its calls the contract's** (π2's part's conclusion): π2's circuit
computes π1-rec3's recorded verifier graph (`RecGraph.Pi1.pi1Graph`) with the real Keccak-f[1600]
(`RecCircuit.compile_sound`); on π1's IV, the public input and the stream `s`, the graph's checks hold and its three
`PCS_OPEN` calls are the contract's `ops`: their layouts and claims, and `C1`'s and `C2`'s roots, which `s` carries (`F`'s
root is the setup's, a constant of the contract, which the graph holds as the reference's). -/
def Pi1GraphAccepts (iv1 : List UInt8) (input : Vector UInt8 32) (s : Array UInt8) (ops : List Pi1Opening) : Prop :=
  ∃ out gops, RecGraph.evalGraphDeployed RecGraph.Pi1.pi1Graph iv1 input.toList s = some out ∧
    (∀ z ∈ out.zeros, z = 0) ∧ (∀ z ∈ out.nonzeros, z ≠ 0) ∧ out.calls.mapM decodePi1Call = some gops ∧
    gops.map (·.2) = ops.map (·.2) ∧ (gops.take 2).map (·.1) = (ops.take 2).map (·.1)

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **π1-rec3's verifier with its Fiat–Shamir over Keccak-f[1600]** and its three openings over `F`: π1's IV and run
over Keccak-f[1600] (`pi1Iv`, `UniStatement.runFs … .rec3 true`), then `C1`, `C2`, the setup opened over `F`
(`UniStatement.pcsOpenWith`, as `verifyWithFs`). -/
def pi1KeccakVerifierWith (D : UniStatement.Deployment) (roots : UniStatement.SetupRoots) (input : Vector UInt8 32)
    (proof : UniStatement.UniProof) : m Bool := do
  let iv := pi1Iv D.shape D.programIv roots
  let o := UniStatement.runFs D.shape iv input.toList proof.stream (.flock UniStatement.flockMain) .point .rec3 true
  if !o.accepts then return false
  match o.result with
  | .error _ => return false
  | .ok r =>
    let words := UniStatement.layoutWords D.shape
    let callOf : UniStatement.Commitment → Digest × List UInt8 × Compile.Proof
      | .c1 => (UniStatement.rootOf r.roots.1, words.getD 0 [], proof.c1)
      | .c2 => (UniStatement.rootOf r.roots.2, words.getD 1 [], proof.c2)
      | .setup => (roots.bytecode, words.getD 2 [], proof.setup)
    let mut ok := r.openings.map (·.1) == UniStatement.commitments
    for (c, opening) in r.openings do
      match opening with
      | .point pt value none =>
        let (root, word, p) := callOf c
        ok := ok && (← UniStatement.pcsOpenWith F (UniStatement.layoutWordVars word) root [⟨pt, value⟩] p)
      | _ => ok := false
    return ok

/-- **π1-rec3's graph at Keccak-f[1600], its three openings over `F`**: the graph's checks hold and its calls (`F`'s root
the setup's) are opened as `UniStatement.pcsOpenWith` with the proof's `C1`, `C2`, setup opening proofs. -/
def pi1GraphVerifierWith (D : RecDeployment) (roots : UniStatement.SetupRoots) (input : Vector UInt8 32)
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
        ok := ok && (← UniStatement.pcsOpenWith F (UniStatement.layoutWordVars o.2.1) o.1 o.2.2 p)
      return ok

end With

/-! ## The extractors -/

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

/-- π1-rec3's graph's checks at Keccak-f[1600] on a stream. -/
def pi1GraphChecks (iv1 : List UInt8) (input : Vector UInt8 32) (s : Array UInt8) : Bool :=
  match RecGraph.evalGraphDeployed RecGraph.Pi1.pi1Graph iv1 input.toList s with
  | some out => out.zeros.all (· == 0) && out.nonzeros.all (· != 0)
  | none => false

/-- **`Pi1GraphAccepts`, decided**: the graph's checks hold at Keccak-f[1600] and its three calls, decoded, are the
openings `ops` (their layouts and claims, `C1`'s and `C2`'s roots). -/
def pi1GraphAcceptsB (iv1 : List UInt8) (input : Vector UInt8 32) (s : Array UInt8) (ops : List Pi1Opening) : Bool :=
  match RecGraph.evalGraphDeployed RecGraph.Pi1.pi1Graph iv1 input.toList s with
  | none => false
  | some out =>
    out.zeros.all (· == 0) && out.nonzeros.all (· != 0) &&
      match out.calls.mapM decodePi1Call with
      | none => false
      | some gops => decide (gops.map (·.2) = ops.map (·.2) ∧ (gops.take 2).map (·.1) = (ops.take 2).map (·.1))

/-- **The contract's π1 openings from the calldata alone**: π2's run over Keccak-f[1600] (any IV: π1's three calls read
only the stream's public data, π1's roots and claims' elements, and the setup's root, not the transcript's hashes),
its first three calls decoded under the registry (`contractPi1Openings`). Composition: `RecCompose.pi1OpsOf_eq`. -/
def pi1OpsOf (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32) (stream : Array UInt8) :
    Option (List Pi1Opening) :=
  let c := (D.circuitAt roots.pi1).circuit
  match (run (Spec.of c) [] input.toList stream).result with
  | .error _ => none
  | .ok r => contractPi1Openings (registryOf D.pi1.shape c.logN)
      (pcsCalls c (pi1CallsWith D.pi1Calls roots.pi1.bytecode) (digestBytes roots.pi2) stream r)

/-- **π2's extractor on given preimages**: for each candidate of π2's `W` (its root after π1's public data), π1's stream
its witness values hold (`pi1Stream`); the first on which π1-rec3's graph accepts at Keccak-f[1600] with the contract's
π1 openings (`pi1GraphAcceptsB`: its checks, and its three calls those the contract makes, `pi1OpsOf`).

(Composition, `lean-rec-compose`: the search must test the calls too, not only the graph's checks. `W`'s list may hold
two candidates whose π1 streams both pass the checks, the first one's calls not the contract's: the adversary commits a
word within the list-decoding radius of two codewords, `c'` first in the list, its stream an honest π1 proof of another
transcript, and `c` the one the openings' claims hold of. Searching by the checks alone, the extractor would output
`c'`'s stream, on which `Pi1GraphAccepts` with the contract's openings fails.) -/
def recExtractFrom2 (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32)
    (pre : Digest → ℕ → Option (List UInt8)) (proof : RecProof) : Option (Array UInt8) :=
  let c := (D.circuitAt roots.pi1).circuit
  let at' := rootsAt c.reads
  let wL := (layoutsOf c.logN).1
  let wWord := committedWord pre wL.logN (streamRoot proof.stream (at'.getD (rootReads c.reads) 0))
  match pi1OpsOf D roots input proof.stream with
  | none => none
  | some ops =>
    (candidates wL.logN wWord).findSome? fun w ↦
      let table := Array.ofFn (n := 2 ^ c.logN) fun i ↦ wL.readEntry (fun j ↦ w.toArray.getD j 0) i.val
      let s := D.pi1Stream fun i ↦ UniStatement.basisValue table c.logN i
      if pi1GraphAcceptsB (D.pi1IvAt roots.pi1) input s ops then some s else none

/-- The unique preimages of the setup's evaluations and the transcript's (the lengths a Merkle tree hashes). -/
def preimagesOf (setupEvals : List (List UInt8 × Digest)) (T : OracleQueryLog) :
    Digest → ℕ → Option (List UInt8) :=
  PcsQuotient.Replay.preimageIn (PcsQuotient.Replay.preimageIndex (setupEvals ++
    PcsQuotient.Replay.transcriptEvaluations PcsQuotient.merkleLengths (LeanVM.permutationQueries T)))

/-- **π2's extractor** in the random-permutation model: π1's stream. -/
def recExtractor2 (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32)
    (setupEvals : List (List UInt8 × Digest)) (T : OracleQueryLog) (proof : RecProof) : Option (Array UInt8) :=
  recExtractFrom2 D roots input (preimagesOf setupEvals T) proof

/-- π1's proof from π1's stream and the recursive proof's three π1 opening proofs (`A0`, `B0` unread at π1-rec3). -/
def RecProof.pi1Proof (p : RecProof) (s : Array UInt8) : UniStatement.UniProof := ⟨s, p.c1, p.c2, p.f, ⟨[], []⟩, ⟨[], []⟩⟩

/-- **The end-to-end extractor**: π2's (π1's stream), then π1-rec3's own (`UniStatement.uniExtractor`: `C1`'s word
under the root the stream names, decoded, read as Lv42's stack at the stream's row counts). -/
def recExtractor (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32)
    (setupEvals : List (List UInt8 × Digest)) (T : OracleQueryLog) (proof : RecProof) :
    Option ((rows : List ℕ) × D.pi1.Stack rows) :=
  (recExtractor2 D roots input setupEvals T proof).bind fun s ↦
    (UniStatement.uniExtractor D.pi1 input setupEvals T (proof.pi1Proof s)).map fun q ↦ ⟨_, q⟩

/-- π2's extractor's shape. -/
abbrev RecExtractor2 : Type :=
  RecSetupRoots → Vector UInt8 32 → List (List UInt8 × Digest) → OracleQueryLog → RecProof → Option (Array UInt8)

/-- The end-to-end extractor's shape: π1's row counts and a stack at them. -/
abbrev RecExtractor (D : RecDeployment) : Type :=
  RecSetupRoots → Vector UInt8 32 → List (List UInt8 × Digest) → OracleQueryLog → RecProof →
    Option ((rows : List ℕ) × D.pi1.Stack rows)

/-! ## Knowledge soundness, part 1: π2's, in the random-permutation model -/

/-- An adversary: given the setup's roots, a public input and a proof, with coins, `π` and `π⁻¹`. -/
abbrev RecAdversary : Type := RecSetupRoots → OracleComp RandomPermutationOracles (Vector UInt8 32 × RecProof)

/-- π2's outcome: the statement and the proof, the verdict, the setup's evaluations, the transcript, the setup's roots,
the contract's calls. -/
abbrev RecOutcome2 : Type :=
  ((Vector UInt8 32 × RecProof) × Bool) × List (List UInt8 × Digest) × OracleQueryLog × RecSetupRoots ×
    List (List (List UInt8))

/-- **π2's knowledge-soundness experiment**: the setup over `π`, the adversary given its roots (its queries logged),
then the contract over `π` (its verdict and calls). -/
noncomputable def recSoundnessExperiment2 (D : RecDeployment) (A : RecAdversary) : ProbComp RecOutcome2 :=
  runWithRandomPermutation do
    let trees ← D.setupTreesWith queryPermutation
    let (z, transcript) ← (simulateQ loggedOracles (A trees.roots)).run []
    let (accepted, calls) ← D.contractWith queryPermutation trees.roots z.1 z.2
    return ((z, accepted), trees.evaluations, transcript, trees.roots, calls)

/-- **The adversary breaks π2's knowledge soundness**: the contract accepts, and π2's extractor outputs no stream on
which π1-rec3's graph accepts at Keccak-f[1600] with the contract's π1 openings. -/
def RecBreaksKnowledgeSoundness2 (D : RecDeployment) (ext : RecExtractor2) (z : RecOutcome2) : Prop :=
  z.1.2 = true ∧ ¬ ∃ s ops, ext z.2.2.2.1 z.1.1.1 z.2.1 z.2.2.1 z.1.1.2 = some s ∧
    contractPi1Openings (registryOf D.pi1.shape (D.circuitAt z.2.2.2.1.pi1).circuit.logN) z.2.2.2.2 = some ops ∧
    Pi1GraphAccepts (D.pi1IvAt z.2.2.2.1.pi1) z.1.1.1 s ops

/-- **π2's knowledge soundness for the extractor `ext`**, error `ε2 Q` for `Q` calls of `π` and `π⁻¹`. -/
def RecKnowledgeSoundness2With (D : RecDeployment) (ext : RecExtractor2) (ε2 : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : RecAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    Pr{let z ← recSoundnessExperiment2 D A}[RecBreaksKnowledgeSoundness2 D ext z] ≤ ε2 Q

/-- **π2's knowledge soundness** (provable in the random-permutation model): if the contract accepts, π2's explicit
extractor `recExtractor2` outputs π1's stream, on which π1-rec3's recorded graph run with Keccak-f[1600] accepts, its
three `PCS_OPEN` calls the contract's (which `PCS_OPEN` attested); but with probability `ε2 Q`. -/
def RecKnowledgeSoundness2 (D : RecDeployment) (ε2 : ℕ → ℝ≥0∞) : Prop :=
  RecKnowledgeSoundness2With D (recExtractor2 D) ε2

/-! ## The hypotheses about π1-rec3 at Keccak-f[1600] -/

/-- A π1 adversary of the recursive setup: given its roots and its trees' Keccak-256 evaluations (the setup is public;
the derived adversary runs π2's extractor, which reads them), a public input and π1's proof.

(Composition, `lean-rec-compose`: with the roots alone, the adversary built from π2's must recompute the setup, `2^27`
and more calls of `π` that `ε1` would be charged at, and whose transcript `uniExtractor` would read with π2's
adversary's.) -/
abbrev Pi1Adversary : Type :=
  RecSetupRoots → List (List UInt8 × Digest) →
    OracleComp RandomPermutationOracles (Vector UInt8 32 × UniStatement.UniProof)

/-- **π1-rec3's knowledge-soundness experiment at Keccak-f[1600]**: the recursive setup over `π`, the adversary, then
π1-rec3's verifier with its Fiat–Shamir over Keccak-f[1600] and its openings over `π` (`pi1KeccakVerifierWith`). -/
noncomputable def pi1KeccakSoundnessExperiment (D : RecDeployment) (A : Pi1Adversary) :
    ProbComp UniStatement.UniOutcome :=
  runWithRandomPermutation do
    let trees ← D.setupTreesWith queryPermutation
    let (z, transcript) ← (simulateQ loggedOracles (A trees.roots trees.evaluations)).run []
    let accepted ← pi1KeccakVerifierWith queryPermutation D.pi1 trees.roots.pi1 z.1 z.2
    return ((z, accepted), trees.evaluations, transcript)

/-- **Hypothesis: π1-rec3 is knowledge sound with its Fiat–Shamir instantiated by Keccak-f[1600]**, error `ε1 Q`, for
its own extractor `UniStatement.uniExtractor`, against the adversaries of the recursive setup (those built from π2's:
they run π2's adversary and π2's extractor). Its justification is π1-rec3's random-permutation theorem
(`UniSound.Rec3Ref.uniKnowledgeSoundness_closed_rec3`, 128.49 bits): **the Fiat–Shamir heuristic for Keccak-f[1600]**;
it is not provable, as the earlier proofs' caveat says (AGENTS.md). -/
def Pi1FsKeccak (D : RecDeployment) (ε1 : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : Pi1Adversary) (Q : ℕ), (∀ roots evals, QueryCostAtMost (A roots evals) permutationCallCost Q) →
    Pr{let z ← pi1KeccakSoundnessExperiment D A}[
      UniStatement.UniBreaksKnowledgeSoundness D.pi1 (UniStatement.uniExtractor D.pi1) z] ≤ ε1 Q

/-- An adversary choosing a public input and π1's stream, given the recursive setup's roots and its trees' Keccak-256
evaluations (as `Pi1Adversary`). -/
abbrev Pi1StreamAdversary : Type :=
  RecSetupRoots → List (List UInt8 × Digest) →
    OracleComp RandomPermutationOracles (Vector UInt8 32 × Array UInt8)

/-- The merge hazard's experiment: the recursive setup, the adversary's public input and stream, π1's IV. -/
noncomputable def pi1HazardExperiment (D : RecDeployment) (B : Pi1StreamAdversary) :
    ProbComp (List UInt8 × Vector UInt8 32 × Array UInt8) :=
  runWithRandomPermutation do
    let trees ← D.setupTreesWith queryPermutation
    let (z, _) ← (simulateQ loggedOracles (B trees.roots trees.evaluations)).run []
    return (D.pi1IvAt trees.roots.pi1, z)

/-- **Hypothesis: π1-rec3's run at Keccak-f[1600] avoids the merge hazard** (`RecGraph.MergeHazard`: the challenges at
which the recorded graph, merging by symbol, and the verifier, merging by value, may differ), but with probability
`εh Q`. Justified by `RecGraph.hazard_prob` (`2^19/|E|` a challenge) for random challenges: the same heuristic. -/
def Pi1HazardKeccak (D : RecDeployment) (εh : ℕ → ℝ≥0∞) : Prop :=
  ∀ (B : Pi1StreamAdversary) (Q : ℕ), (∀ roots evals, QueryCostAtMost (B roots evals) permutationCallCost Q) →
    Pr{let z ← pi1HazardExperiment D B}[
      RecGraph.MergeHazard LeanVM.Semantics.keccakF1600 z.1 z.2.1.toList z.2.2] ≤ εh Q

/-! ## Knowledge soundness, part 2: end to end, against Lv42's `M3Holds` -/

/-- An outcome: the statement and the proof, the verdict, the setup's evaluations, the transcript, the setup's roots. -/
abbrev RecOutcome : Type :=
  ((Vector UInt8 32 × RecProof) × Bool) × List (List UInt8 × Digest) × OracleQueryLog × RecSetupRoots

/-- **The knowledge-soundness experiment**: the setup over `π`, the adversary given its roots (its queries logged),
then the recursive verifier over `π`. -/
noncomputable def recSoundnessExperiment (D : RecDeployment) (A : RecAdversary) : ProbComp RecOutcome :=
  runWithRandomPermutation do
    let trees ← D.setupTreesWith queryPermutation
    let (z, transcript) ← (simulateQ loggedOracles (A trees.roots)).run []
    let accepted ← D.verifierWith queryPermutation trees.roots z.1 z.2
    return ((z, accepted), trees.evaluations, transcript, trees.roots)

/-- **The adversary breaks knowledge soundness**: the recursive verifier accepts, and the extractor outputs no row
counts and stack satisfying leanVM 42422001's relation for the public input. -/
def RecBreaksKnowledgeSoundness (D : RecDeployment) (ext : RecExtractor D) (z : RecOutcome) : Prop :=
  z.1.2 = true ∧ ¬ ∃ w, ext z.2.2.2 z.1.1.1 z.2.1 z.2.2.1 z.1.1.2 = some w ∧ D.pi1.Relation w.1 z.1.1.1 w.2

/-- **Knowledge soundness for the extractor `ext`**, error `ε Q` for `Q` calls of `π` and `π⁻¹`. -/
def RecKnowledgeSoundnessWith (D : RecDeployment) (ext : RecExtractor D) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : RecAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    Pr{let z ← recSoundnessExperiment D A}[RecBreaksKnowledgeSoundness D ext z] ≤ ε Q

/-- **Knowledge soundness of the recursive verifier against leanVM 42422001's relation, end to end** (π2's verifier
and the six openings; the explicit extractor `recExtractor`: π2's, then π1-rec3's), error `ε2 + ε1 + εh`, under the
named hypotheses: the recorded graph is π1-rec3's verifier off the merge hazard (`RecGraph.Pi1.Pi1GraphIsVerifier`,
proved: `RecGraph.Pi1.pi1GraphIsVerifier`), π1-rec3 is knowledge sound with its Fiat–Shamir over Keccak-f[1600] (`Pi1FsKeccak ε1`, justified by
`uniKnowledgeSoundness_closed_rec3`: the Fiat–Shamir heuristic), and its run at Keccak-f[1600] avoids the merge
hazard (`Pi1HazardKeccak εh`, justified by `RecGraph.hazard_prob`). `ε2` is π2's part's (`RecKnowledgeSoundness2`). The
random-permutation theorems do not formally compose with the circuit's Keccak-f[1600]: these hypotheses are where they
meet. -/
def RecKnowledgeSoundness (D : RecDeployment) (ε2 ε1 εh : ℕ → ℝ≥0∞) : Prop :=
  RecGraph.Pi1.Pi1GraphIsVerifier → Pi1FsKeccak D ε1 → Pi1HazardKeccak D εh →
    RecKnowledgeSoundnessWith D (recExtractor D) fun Q ↦ ε2 Q + ε1 Q + εh Q

/-! ## Completeness -/

/-- π1-rec3's prover (in the recursion, its Fiat–Shamir over Keccak-f[1600], its openings over `π`). -/
abbrev Pi1Prover (D : RecDeployment) : Type := UniStatement.UniProver D.pi1

/-- π2's prover: from the public input and π1's proof, a proof of the recursive verifier (or none), with coins, `π` and
`π⁻¹` (it recomputes the public setup as it needs). -/
abbrev Pi2Prover : Type :=
  Vector UInt8 32 → UniStatement.UniProof → OracleComp RandomPermutationOracles (Option RecProof)

/-- A prover of the recursive verifier: from the public input, π1's row counts and a stack of Lv42's layout at them. -/
abbrev RecProver (D : RecDeployment) : Type :=
  Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp RandomPermutationOracles (Option RecProof)

/-- The recursive prover: π1-rec3's, then π2's on its proof. -/
def composeProver (D : RecDeployment) (P1 : Pi1Prover D) (P2 : Pi2Prover) : RecProver D :=
  fun input rows q ↦ do
    match ← P1 input rows q with
    | none => return none
    | some p1 => P2 input p1

/-- **π2's completeness experiment**: the setup, π1's proof (from any π1 prover), whether π1-rec3's graph accepts it at
Keccak-f[1600] with its openings over `π` (`pi1GraphVerifierWith`), and whether the contract accepts π2's proof of it. -/
noncomputable def recCompletenessExperiment2 (D : RecDeployment) (P1 : Pi1Prover D) (P2 : Pi2Prover)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows) : ProbComp (Bool × Bool) :=
  runWithRandomPermutation do
    let trees ← D.setupTreesWith queryPermutation
    match ← P1 input rows q with
    | none => return (false, false)
    | some p1 =>
      let a1 ← pi1GraphVerifierWith queryPermutation D trees.roots.pi1 input p1
      match ← P2 input p1 with
      | none => return (a1, false)
      | some p2 => return (a1, ← D.verifierWith queryPermutation trees.roots input p2)

/-- **π2's completeness** (over its own coins and `π`), on π1-rec3's prover `P1`'s proofs of honest statements: a π1
proof on which π1-rec3's graph accepts at Keccak-f[1600], its openings verifying over `π`, is turned by `P2` into a proof
the contract accepts, but with probability `δ2`.

(Composition, `lean-rec-compose`: for π1-rec3's prover, not every `P1`. A `P1` of unbounded queries can grind its
proof, the graph still accepting, until π2's honest run on it hits one of π2's degenerate challenges (the one value the
contract requires nonzero, `all = 0`), which no `δ2` below one bounds.) -/
def RecCompleteness2 (D : RecDeployment) (P1 : Pi1Prover D) (P2 : Pi2Prover) (δ2 : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation rows input q →
    Pr{let v ← recCompletenessExperiment2 D P1 P2 input rows q}[v.1 = true ∧ v.2 = false] ≤ δ2

/-- **π1-rec3's completeness experiment at Keccak-f[1600]**: the recursive setup, the prover's proof, π1-rec3's
verifier with its Fiat–Shamir over Keccak-f[1600] and its openings over `π`. -/
noncomputable def pi1KeccakCompletenessExperiment (D : RecDeployment) (P1 : Pi1Prover D) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.pi1.Stack rows) : ProbComp Bool :=
  runWithRandomPermutation do
    let trees ← D.setupTreesWith queryPermutation
    match ← P1 input rows q with
    | none => return false
    | some p1 => pi1KeccakVerifierWith queryPermutation D.pi1 trees.roots.pi1 input p1

/-- **Hypothesis: π1-rec3 is complete with its Fiat–Shamir instantiated by Keccak-f[1600]**, error `δ1`. Justified by
`UniComplete.Rec3.uniCompletenessRec3_end_closed` (`δ < 2^-167` in the random-permutation model). -/
def Pi1CompletenessKeccak (D : RecDeployment) (P1 : Pi1Prover D) (δ1 : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation rows input q →
    Pr{let v ← pi1KeccakCompletenessExperiment D P1 input rows q}[v = false] ≤ δ1

/-- The honest proofs' merge hazard experiment: the recursive setup, the prover's proof, whether its run at
Keccak-f[1600] hits the merge hazard. -/
noncomputable def pi1HonestHazardExperiment (D : RecDeployment) (P1 : Pi1Prover D) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.pi1.Stack rows) : ProbComp (Option (List UInt8 × Array UInt8)) :=
  runWithRandomPermutation do
    let trees ← D.setupTreesWith queryPermutation
    match ← P1 input rows q with
    | none => return none
    | some p1 => return some (D.pi1IvAt trees.roots.pi1, p1.stream)

/-- **Hypothesis: π1-rec3's honest proofs avoid the merge hazard at Keccak-f[1600]**, but with probability `δh`
(`RecGraph.hazard_prob` for random challenges). -/
def Pi1HazardKeccakHonest (D : RecDeployment) (P1 : Pi1Prover D) (δh : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation rows input q →
    Pr{let z ← pi1HonestHazardExperiment D P1 input rows q}[
      ∃ iv s, z = some (iv, s) ∧ RecGraph.MergeHazard LeanVM.Semantics.keccakF1600 iv input.toList s] ≤ δh

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

/-- **Completeness of the recursive verifier, end to end**: π1-rec3's prover then π2's (`composeProver`), error
`δ1 + δh + δ2`, under the named hypotheses: the recorded graph is π1-rec3's verifier off the merge hazard
(`RecGraph.Pi1.Pi1GraphIsVerifier`), π1-rec3 is complete with its Fiat–Shamir over Keccak-f[1600]
(`Pi1CompletenessKeccak δ1`, justified by `uniCompletenessRec3_end_closed`) and its honest proofs avoid the merge hazard
(`Pi1HazardKeccakHonest δh`). `δ2` is π2's part's (`RecCompleteness2`). -/
def RecCompleteness (D : RecDeployment) (P1 : Pi1Prover D) (P2 : Pi2Prover) (δ1 δh δ2 : ℝ≥0∞) : Prop :=
  RecGraph.Pi1.Pi1GraphIsVerifier → Pi1CompletenessKeccak D P1 δ1 → Pi1HazardKeccakHonest D P1 δh →
    RecCompletenessWith D (composeProver D P1 P2) (δ1 + δh + δ2)

end RecStatement
