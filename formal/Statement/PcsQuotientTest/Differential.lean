-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import PcsQuotient
import VCVio.OracleComp.RunIO
import PcsQuotientTest.ChaCha

/-!
# The differential test

`lake exe differential VECTORS`: the Lean verifier (`PcsQuotient.reduce`, `PcsQuotient.verify`) on
the vectors `crates/quotient/examples/statement_vectors.rs` writes, each with the Rust verifier's
outcome, and a count of the agreements. Exit code `1` on any disagreement or unreadable line.

* `R` lines: the reduction alone; the Rust's two roots and four claims must be the Lean's, or both
  reject.
* `P` lines: a whole proof, its openings in their raw form; both verifiers accept, or both reject.
-/

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile PcsQuotient

namespace PcsQuotientTest

/-- A parser of a line's tokens. -/
abbrev Parse := StateT (List String) (Except String)

def token : Parse String := do
  match ← get with
  | [] => throw "the line ended early"
  | t :: ts => set ts; pure t

def hexDigit (c : Char) : Option ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def hexNat (s : String) : Except String ℕ :=
  s.toList.foldlM (fun acc c ↦ match hexDigit c with
    | some d => pure (16 * acc + d)
    | none => throw s!"not hex: {s}") 0

def nat : Parse ℕ := do
  let t ← token
  match t.toNat? with
  | some n => pure n
  | none => throw s!"not a number: {t}"

def kWord : Parse K := do
  pure (K.ofLane (UInt64.ofNat (← hexNat (← token))))

def eElem : Parse E := do
  match (← token).splitOn ":" with
  | [a, b, c] =>
    let limb (s : String) : Except String K := (fun n ↦ K.ofLane (UInt64.ofNat n)) <$> hexNat s
    pure (E.ofLimbs (← limb a) (← limb b) (← limb c))
  | _ => throw "not an element of E"

def bytes32 : Parse (Vector UInt8 32) := do
  let t ← token
  if t.length ≠ 64 then throw s!"not 32 bytes: {t}"
  let bytes ← (List.range 32).mapM fun i ↦ hexNat ((t.drop (2 * i)).take 2).toString
  pure (Vector.ofFn fun i : Fin 32 ↦ UInt8.ofNat (bytes.getD i.val 0))

/-- A hash's bytes as a digest: four little-endian words. -/
def digest : Parse Digest := do
  let b ← bytes32
  pure (Vector.ofFn fun i : Fin 4 ↦ (List.range 8).foldl
    (fun acc k ↦ acc ||| ((b.toList.getD (8 * i.val + k) 0).toUInt64 <<< (8 * k).toUInt64)) 0)

def many {α : Type} (p : Parse α) : Parse (List α) := do
  let n ← nat
  (List.range n).mapM fun _ ↦ p

def claim : Parse Claim := do
  let point ← many eElem
  let value ← eElem
  pure ⟨point, value⟩

def openingProof : Parse Compile.Proof := do
  let stream ← many eElem
  let openings ← many do
    let leaf ← many kWord
    let path ← many digest
    pure (⟨leaf, path⟩ : Compile.Opening)
  pure ⟨stream, openings⟩

/-- The common head of a line: the size, the circuit's commitment, the statement, the stream. -/
def lineHead : Parse (ℕ × Digest × Statement × List E) := do
  let logRows ← nat
  let indexRoot ← digest
  let y ← bytes32
  let root ← bytes32
  let stream ← many eElem
  pure (logRows, indexRoot, ⟨y, root⟩, stream)

/-- The small circuit of the vectors (`small`, `statement_vectors.rs`): `256` inputs, XORs and χs
folding them, the inputs as both public values; `2^13` rows. -/
def smallBuilder : BuildM (List Src × List Src) := do
  let x ← (List.range 256).mapM fun _ ↦ Build.input
  let mut acc := x.getD 0 .zero
  for i in [1:256] do
    acc ← if i % 3 = 0 then Build.chi acc (x.getD i .zero) (x.getD (i * 7 % 256) .zero)
      else Build.xor acc (x.getD i .zero)
  let _ ← Build.not acc
  return (x, x)

/-- One Keccak-256 of `x ‖ x` (`toy`, `statement_vectors.rs`); `2^17` rows. -/
def toyBuilder : BuildM (List Src × List Src) := do
  let x ← (List.range 256).mapM fun _ ↦ Build.input
  let digest ← Build.keccak256Block (x ++ x)
  return (x, digest)

/-- The circuits the vectors name. -/
def circuitNamed : String → Option Circuit
  | "small" => let ((y, r), b) := smallBuilder.run Builder.new; some (finish 17 (publicWords y r) b)
  | "toy" => let ((y, r), b) := toyBuilder.run Builder.new; some (finish 17 (publicWords y r) b)
  | "membership" => some (membership 22)
  | _ => none

/-- Check one line: whether Lean and Rust agree, and the line's kind. -/
def checkLine (line : String) : Except String (String × Bool) := do
  let tokens := (line.splitOn " ").filter (· ≠ "")
  let (kind, rest) := match tokens with
    | k :: r => (k, r)
    | [] => ("", [])
  match kind with
  | "R" =>
    let ((logRows, indexRoot, stmt, stream), rest) ← lineHead.run rest
    let lean := (ReductionProof.ofStream stream).bind (reduce logRows indexRoot stmt)
    let (rust, _) ← (do
        match ← token with
        | "REJECT" => pure none
        | "ACCEPT" =>
          let w ← digest
          let q ← digest
          let c1 ← claim
          let c2 ← claim
          let c3 ← claim
          let c4 ← claim
          pure (some (w, q, (⟨c1, c2, c3, c4⟩ : Claims)))
        | t => throw s!"unknown verdict {t}" : Parse _).run rest
    let agree := match lean, rust with
      | none, none => true
      | some r, some (w, q, c) =>
        decide (r.witnessRoot.toList = w.toList) && decide (r.quotientRoot.toList = q.toList) &&
          decide (r.claims = c)
      | _, _ => false
    pure ("R", agree)
  | "P" =>
    let ((logRows, indexRoot, stmt, stream), rest) ← lineHead.run rest
    let ((w, i, q, verdict), _) ← (do
        let w ← openingProof
        let i ← openingProof
        let q ← openingProof
        let v ← token
        pure (w, i, q, v) : Parse _).run rest
    let lean := match ReductionProof.ofStream stream with
      | none => false
      | some p => verify logRows indexRoot stmt ⟨p, w, i, q⟩
    pure ("P", lean == (verdict == "ACCEPT"))
  | "I" =>
    let ((name, logRows, used, inputs, root), _) ← (do
        let name ← token
        let logRows ← nat
        let used ← nat
        let inputs ← nat
        let root ← digest
        pure (name, logRows, used, inputs, root) : Parse _).run rest
    match circuitNamed name with
    | none => throw s!"unknown circuit {name}"
    | some c =>
      let lean := Id.run (c.indexRootWith (m := Id) fun s ↦ pure (LeanVM.Semantics.keccakF1600 s))
      pure ("I", c.logRows == logRows && c.usedRows == used && c.inputs.size == inputs &&
        decide (lean.toList = root.toList))
  | "Q" =>
    let ((name, bits, seed, masks, stream), _) ← (do
        let name ← token
        let count ← nat
        let bytes ← (List.range ((count + 7) / 8)).mapM fun _ ↦ do pure (← hexNat (← token))
        let bits := (List.range count).map fun i ↦ (bytes.getD (i / 8) 0).testBit (i % 8)
        let seed ← bytes32
        let words ← (List.range 12).mapM fun _ ↦ kWord
        let masks : Masks := fun j i ↦ words.getD (3 * j.val + i.val) 0
        let stream ← many eElem
        pure (name, bits, seed, masks, stream) : Parse _).run rest
    match circuitNamed name with
    | none => throw s!"unknown circuit {name}"
    | some c =>
      let stmt : Statement :=
        if name = "membership" then (secretOfInputs bits).statement
        else
          let x : Vector UInt8 32 := Vector.ofFn fun j ↦ (List.range 8).foldl
            (fun acc k ↦ if bits.getD (8 * j.val + k) false then acc ||| (1 <<< k.toUInt8) else acc) 0
          ⟨x, x⟩
      let keccak := fun s ↦ (pure (LeanVM.Semantics.keccakF1600 s) : Id _)
      let pad (table : String) (L : Layout) := ChaCha.paddingOfSeed seed.toList table L
      match Id.run (proveWith (m := Id) keccak (2 ^ 25) c stmt (c.cells bits) masks
          (pad "witness" (witnessLayout c.logRows)) (pad "quotient" (quotientLayout c.logRows))) with
      | none => pure ("Q", false)
      | some proof =>
        let indexRoot := Id.run (c.indexRootWith (m := Id) keccak)
        pure ("Q", decide (proof.reduction.stream = stream) && verify c.logRows indexRoot stmt proof)
  | k => throw s!"unknown line kind {k}"

end PcsQuotientTest

namespace PcsQuotientTest


/-! ### Self-tests of the extractor and the simulator (`--self-test`) -/

/-- The small circuit of the vectors. -/
def smallCircuit : Circuit :=
  let ((y, r), b) := smallBuilder.run Builder.new
  finish 17 (publicWords y r) b

/-- Keccak-f[1600], each call recorded as a forward query of the permutation with its answer. -/
abbrev LogM := StateM (Array (Common.PermutationQuery LeanVM.Semantics.KeccakState ×
  LeanVM.Semantics.KeccakState))

def loggedKeccak (s : LeanVM.Semantics.KeccakState) : LogM LeanVM.Semantics.KeccakState := do
  let y := LeanVM.Semantics.keccakF1600 s
  modify (·.push (.forward s, y))
  return y

/-- **The extractor's Merkle inversion through a transcript**: an adversary commits a word of `8` rows of
`64` words (its transcript, the tree's Keccak-f calls, `4` blocks a row); through the transcript's Keccak-256
evaluations (mumbai's `keccakEvaluationsOfTranscript`, quadratic in the transcript, so a small tree), the
extractor's `committedLeaves` reads back every row. -/
def inversionTest : Bool :=
  let word : LeanVM.Protocol.Compile.Word := fun p ↦
    (List.range 64).map fun j ↦ K.ofLane (UInt64.ofNat (1000003 * (64 * p + j) + 7))
  let (tree, log) := (LeanVM.Prover.buildTreeM (m := LogM) loggedKeccak 3 word).run #[]
  let paths := LeanVM.keccakEvaluationsOfTranscript log.toList
  let leaves := LeanVM.Extraction.committedLeaves (LeanVM.lookupEvaluation paths) (paths.map (·.1))
    tree.root 3 64
  (List.range 8).all fun p ↦ decide (leaves.getD p [] = word p)

/-- **The extractor's decoding of an honest witness table**: the hidden stack of the small circuit's
witness table (padding from a seed), its WHIR word, the fast path's candidate, and the input bits read back
through the hidden layout and the cells' values: they are the inputs. -/
def extractionTest (bits : List Bool) (masks : Masks) : Bool :=
  let c := smallCircuit
  let mv := cellVars c.logRows
  let pad := ChaCha.paddingOfSeed ((List.range 32).map (·.toUInt8)) "witness" (witnessLayout c.logRows)
  let stack := witnessStack c.logRows (Domain.coefficients mv 0 (c.cells bits)) (maskEntries masks) pad
  let word := LeanVM.Prover.stackWordFast (mv + 1) logInvRate stack
  match LeanVM.Extraction.fastStacks (mv + 1) logInvRate word with
  | stack :: _ => inputBitsOfStack c stack == bits
  | [] => false

/-- **The simulator on the small circuit**: its proof of a statement it has no witness for (none
exists: random bytes) is accepted by the verifier querying the simulator's permutation, as a
distinguisher running the verifier would. -/
def simulationTest (stmt : Statement) : IO Bool := do
  let c := smallCircuit
  let run : Simulator.SimM Bool := do
    match ← Simulator.simulateFor c (2 ^ 25) stmt with
    | none => return false
    | some proof =>
      let root ← c.indexRootWith Simulator.simPermutation
      verifyWith Simulator.simPermutation c.logRows root stmt proof
  OracleComp.runIO (run.run' {})

/-- A pseudorandom element of `E`. -/
def eFrom (seed : ℕ) : E :=
  let w (k : ℕ) : K := K.ofLane (UInt64.ofNat ((seed * 6364136223846793005 + 1442695040888963407 * k) % 2 ^ 64))
  E.ofLimbs (w 1) (w 2) (w 3)

/-- **The weight's two forms agree** on the small circuit's hidden layouts: the prover's and the simulator's
`Layout.weightAt` at entry `y` of lane `l` is the verifier's `stackWeight` at that stack point (the bits of `y`,
then of `l`), at pseudorandom claim points and positions; and `fakeStack`'s condition is met: the weighted sum of
a stack conditioned on a claim is its value. Returns the number of mismatches. -/
def weightTest : IO ℕ := do
  let mut bad := 0
  for L in [witnessLayout 17, quotientLayout 17] do
    let lane := 2 ^ L.logLane
    for trial in List.range 4 do
      let c : Claim := ⟨(List.range L.vars).map fun k ↦ eFrom (1000 * trial + k + 1), eFrom (7 * trial + 3)⟩
      let w := L.claimWeights c
      for probe in List.range 64 do
        let l := (probe * 37 + trial) % L.lanes.length
        let y := (probe * 2654435761 + trial * 97) % lane
        let x := (List.range L.logLane).map (fun k ↦ if y.testBit k then (1 : E) else 0) ++
          (List.range 6).map (fun k ↦ if l.testBit k then (1 : E) else 0)
        if L.weightAt w l y ≠ stackWeight L c x then bad := bad + 1
      -- The quotient table's claims are a generic one and one at the sum's point.
      let claims := if L.vars = cellVars 17 + 6 then [c, ⟨sumPoint 17, eFrom (trial + 11)⟩] else [c]
      let stack ← OracleComp.runIO (Simulator.fakeStack L claims)
      for d in claims do
        let wd := L.claimWeights d
        let sum := (List.range stack.size).foldl
          (fun acc p ↦ acc + L.weightAt wd (p / lane) (p % lane) * ofK (stack.getD p 0)) 0
        if sum ≠ d.value then bad := bad + 1
  return bad

/-- Pseudorandom bits for the self-tests. -/
def bitsFrom (seed count : ℕ) : List Bool :=
  (List.range count).map fun i ↦ ((seed * 6364136223846793005 + 1442695040888963407 * (i + 1)) >>> 33) % 2 = 1

end PcsQuotientTest

open PcsQuotientTest in
def main (args : List String) : IO UInt32 := do
  if args.contains "--weights" then
    let bad ← weightTest
    IO.println s!"weights (tensor form vs the verifier's, and fakeStack's claims): {bad} mismatches"
    return if bad = 0 then 0 else 1
  if args.contains "--self-test" then
    let inverted := inversionTest
    IO.println s!"extractor (Merkle inversion through a transcript): {inverted}"
    let bits := bitsFrom 7 256
    let masks : Masks := fun j i ↦ K.ofLane (UInt64.ofNat (1000003 * (3 * j.val + i.val) + 17))
    let extracted := extractionTest bits masks
    IO.println s!"extractor (fast path on an honest hidden commitment): {extracted}"
    (← IO.getStdout).flush
    let bytes : Vector UInt8 32 := Vector.ofFn fun j ↦ UInt8.ofNat (37 * j.val + 11)
    let simulated ← simulationTest ⟨bytes, Vector.ofFn fun j ↦ bytes[j] ^^^ 0x5a⟩
    IO.println s!"simulator (accepted proof of a false statement): {simulated}"
    return if inverted && extracted && simulated then 0 else 1
  let path := args.headD "vectors.txt"
  let lines := ((← IO.FS.readFile path).splitOn "\n").filter (· ≠ "")
  let mut agreed : Std.HashMap String ℕ := {}
  let mut failures : ℕ := 0
  for (line, n) in lines.zipIdx do
    match checkLine line with
    | .ok (kind, true) => agreed := agreed.insert kind (agreed.getD kind 0 + 1)
    | .ok (kind, false) =>
      failures := failures + 1
      IO.println s!"line {n + 1} ({kind}): Lean and Rust disagree"
    | .error e =>
      failures := failures + 1
      IO.println s!"line {n + 1}: unreadable: {e}"
  for (kind, count) in agreed.toList do
    IO.println s!"{kind}: {count} vectors, Lean and Rust agree"
  IO.println s!"{lines.length} vectors, {failures} disagreements"
  return if failures = 0 then 0 else 1
