-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import PcsQuotient
import VCVio.OracleComp.RunIO

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
  | "small" => let ((y, r), b) := smallBuilder.run Builder.new; some (finish 13 (publicWords y r) b)
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
    let ((name, bits, masks, stream), _) ← (do
        let name ← token
        let count ← nat
        let bytes ← (List.range ((count + 7) / 8)).mapM fun _ ↦ do pure (← hexNat (← token))
        let bits := (List.range count).map fun i ↦ (bytes.getD (i / 8) 0).testBit (i % 8)
        let words ← (List.range 12).mapM fun _ ↦ kWord
        let masks : Masks := fun j i ↦ words.getD (3 * j.val + i.val) 0
        let stream ← many eElem
        pure (name, bits, masks, stream) : Parse _).run rest
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
      match Id.run (proveWith (m := Id) keccak (2 ^ 25) c stmt (c.cells bits) masks) with
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
  finish 13 (publicWords y r) b

/-- Keccak-f[1600], each call recorded as a forward query of the permutation with its answer. -/
abbrev LogM := StateM (Array (Common.PermutationQuery LeanVM.Semantics.KeccakState ×
  LeanVM.Semantics.KeccakState))

def loggedKeccak (s : LeanVM.Semantics.KeccakState) : LogM LeanVM.Semantics.KeccakState := do
  let y := LeanVM.Semantics.keccakF1600 s
  modify (·.push (.forward s, y))
  return y

/-- **The extractor's path on an honest commitment**: an adversary commits the honest witness table
of the small circuit (its transcript, the tree's Keccak-f calls); through the transcript's Keccak-256
evaluations, the Merkle inversion and the fast path, the extractor reads back the input bits. -/
def extractionTest (bits : List Bool) (masks : Masks) : Bool :=
  let c := smallCircuit
  let mv := cellVars c.logRows
  let stack := witnessStack c.logRows (Domain.coefficients mv 0 (c.cells bits)) (maskEntries masks)
  let (tree, log) := (commitWith (m := LogM) loggedKeccak (mv + 1) stack).run #[]
  let paths := LeanVM.keccakEvaluationsOfTranscript log.toList
  let proof : PcsQuotient.Proof := ⟨⟨LeanVM.Protocol.KeccakHash.digestScalars tree.root, (0, 0), #v[0, 0, 0, 0], 0⟩, ⟨[], []⟩, ⟨[], []⟩, ⟨[], []⟩⟩
  match witnessWord c.logRows (LeanVM.lookupEvaluation paths) (paths.map (·.1)) proof with
  | none => false
  | some word =>
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

/-- Pseudorandom bits for the self-tests. -/
def bitsFrom (seed count : ℕ) : List Bool :=
  (List.range count).map fun i ↦ ((seed * 6364136223846793005 + 1442695040888963407 * (i + 1)) >>> 33) % 2 = 1

end PcsQuotientTest

open PcsQuotientTest in
def main (args : List String) : IO UInt32 := do
  if args.contains "--self-test" then
    let bits := bitsFrom 7 256
    let masks : Masks := fun j i ↦ K.ofLane (UInt64.ofNat (1000003 * (3 * j.val + i.val) + 17))
    let extracted := extractionTest bits masks
    IO.println s!"extractor (fast path on an honest commitment): {extracted}"
    let bytes : Vector UInt8 32 := Vector.ofFn fun j ↦ UInt8.ofNat (37 * j.val + 11)
    let simulated ← simulationTest ⟨bytes, Vector.ofFn fun j ↦ bytes[j] ^^^ 0x5a⟩
    IO.println s!"simulator (accepted proof of a false statement): {simulated}"
    return if extracted && simulated then 0 else 1
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
