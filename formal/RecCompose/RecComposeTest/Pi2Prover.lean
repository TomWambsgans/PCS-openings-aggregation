-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The parsing follows `formal/UniComplete`'s runner
-- (`UniCompleteTest/Runner.lean`).
import RecCompose.Pi2Prover

/-!
# The differential test of π2's honest prover

`PI2_PROVER=<vectors> lake env lean ../RecCompose/RecComposeTest/Pi2Prover.lean` (from `formal/EndToEnd`), on the
vectors of `crates/leanvm_rec/tests/lean_pi2_prover.rs` (`PI2_PROVER_OUT=... cargo test --release -p leanvm_rec --test
lean_pi2_prover -- --ignored --nocapture`): the circuit compiler's example padded to `2^9`, `2^10` positions, through
`pi2::adapt`. For each vector the runner reads the interface's circuit as `RecCircuit.Circuit` (its PIOP form
`toPiop`), the reads, the public values, the witness and π2's IV, computes the setup's stack and tree
(`Pi2Circuit.setupStack`, `setupTreeWith`) and runs the Lean prover (`pi2ProveStreamWith` from the seed
`keccak(NAME ‖ IV ‖ input)`, Keccak-256 over Keccak-f[1600], interpreted); it compares **the setup's, `W`'s and `Q`'s
roots** and **the stream byte for byte** with the Rust prover's (`pi2::prover::prove`). It throws (so `lean` exits with
an error) on any disagreement.

**Result** (h1, `lean-pi2-alg`): 2/2 vectors (`2^9`, `2^10` positions; 3 pairs, one element port): the setup's, `W`'s and
`Q`'s roots the Rust's, the stream the same byte for byte (496 bytes each); about 9 and 19 minutes interpreted (the
field's inverse, about 125 ms interpreted, dominates: one per point per pair on the coset).
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash RecCompose RecStatement
open Primitives

namespace RecComposeTest

def hexDigit (c : Char) : ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else 0

def hexNat (s : String) : ℕ := s.toList.foldl (fun acc c ↦ 16 * acc + hexDigit c) 0

def hexBytes (s : String) : List UInt8 :=
  let cs := s.toList.toArray
  (List.range (cs.size / 2)).map fun i ↦ UInt8.ofNat (16 * hexDigit (cs.getD (2 * i) '0') + hexDigit (cs.getD (2 * i + 1) '0'))

def hexOf (b : List UInt8) : String :=
  String.join (b.map fun x ↦
    let s := String.ofList (Nat.toDigits 16 x.toNat)
    if s.length = 1 then "0" ++ s else s)

def kOf (s : String) : K := K.ofLane (UInt64.ofNat (hexNat s))

def rest (l : String) : List String := ((l.splitOn " ").drop 1).filter (· ≠ "")

def splitOn (c : String) (s : String) : List String := (s.splitOn c).filter (· ≠ "")

/-- A role: `F`, `E<lin>;<quad>` (`cell:coeff`, `a:b:coeff`), `P<limbs>`. -/
def roleOf (s : String) : RecCircuit.Formula :=
  match s.toList with
  | 'F' :: _ => .forward
  | 'P' :: r => .port ((splitOn "," (String.ofList r)).map String.toNat!)
  | 'E' :: r =>
    let parts := (String.ofList r).splitOn ";"
    let lin := (splitOn "," (parts.getD 0 "")).map fun t ↦
      let xs := t.splitOn ":"
      ((xs.getD 0 "0").toNat!, kOf (xs.getD 1 "0"))
    let quad := (splitOn "," (parts.getD 1 "")).map fun t ↦
      let xs := t.splitOn ":"
      ((xs.getD 0 "0").toNat!, (xs.getD 1 "0").toNat!, kOf (xs.getD 2 "0"))
    .expr ⟨lin, quad⟩
  | _ => .forward

def sourceOf (s : String) : RecCircuit.Source :=
  match s.toList with
  | 'S' :: _ => .statement
  | 'R' :: r => .root (String.ofList r).toNat!
  | 'L' :: r => .element (String.ofList r).toNat!
  | 'Z' :: _ => .zero
  | _ => .pad

def readOf (s : String) : Read :=
  match s.toList with
  | 'I' :: r => .integer (String.ofList r).toNat!
  | 'R' :: _ => .root
  | _ => .scalar

def valueOf (s : String) : PublicValue :=
  match s.toList with
  | 'I' :: r => .integer (hexNat (String.ofList r))
  | 'R' :: r => .root (hexBytes (String.ofList r))
  | 'S' :: r =>
    let xs := (String.ofList r).splitOn ":"
    .scalar (UniStatement.eNew (UInt64.ofNat (hexNat (xs.getD 0 "0"))) (UInt64.ofNat (hexNat (xs.getD 1 "0")))
      (UInt64.ofNat (hexNat (xs.getD 2 "0"))))
  | _ => .scalar 0

structure Vec where
  name : String
  lines : List String

def vectors (ls : List String) : List Vec := Id.run do
  let mut out : Array Vec := #[]
  let mut cur : Option Vec := none
  for l in ls do
    if l.startsWith "VECTOR " then
      cur := some ⟨l, []⟩
    else if l == "END" then
      if let some v := cur then out := out.push ⟨v.name, v.lines.reverse⟩
      cur := none
    else
      cur := cur.map fun v ↦ ⟨v.name, l :: v.lines⟩
  return out.toList

def Vec.tagged (v : Vec) (tag : String) : List String :=
  match v.lines.find? (·.startsWith (tag ++ " ")) with
  | some l => rest l
  | none => []

def Vec.all (v : Vec) (tag : String) : List (List String) :=
  (v.lines.filter (·.startsWith (tag ++ " "))).map rest

/-- Keccak-256 over Keccak-f[1600]. -/
def H : List UInt8 → Id Digest := keccak256With (m := Id) fun s ↦ pure (keccakF1600 s)

def run1 (v : Vec) : IO Unit := do
  let shape := v.tagged "SHAPE"
  let logN := (shape.getD 0 "0").toNat!
  let logW := (shape.getD 1 "0").toNat!
  let regions : Array RecCircuit.Region := ((v.all "REGION").map fun rs ↦ ⟨"", (rs.map roleOf).toArray⟩).toArray
  let blocks : Array RecCircuit.Block := ((v.all "BLOCK").map fun bs ↦
    ⟨(bs.getD 0 "0").toNat!, (bs.getD 1 "0").toNat!, (bs.getD 2 "0").toNat!⟩).toArray
  let sigma : Array ℕ := ((v.tagged "SIGMA").map String.toNat!).toArray
  let kappa : Array (ℕ × K) := ((v.all "KAPPA").map fun ks ↦ ((ks.getD 0 "0").toNat!, kOf (ks.getD 1 "0"))).toArray
  let ports : Array RecCircuit.Port := ((v.all "PORT").map fun ps ↦
    ⟨(ps.getD 0 "0").toNat!, sourceOf (ps.getD 1 "D")⟩).toArray
  let c : RecCircuit.Circuit := ⟨logN, logW, regions, blocks, sigma, kappa, ports, []⟩
  let G := c.toPiop
  let reads := (v.tagged "READS").map readOf
  let values := (v.tagged "VALUES").map valueOf
  let iv := hexBytes ((v.tagged "IV").getD 0 "")
  let input := hexBytes ((v.tagged "INPUT").getD 0 "")
  let wit : Array K := ((v.tagged "WITNESS").map kOf).toArray
  let w : ℕ → K := fun i ↦ wit.getD i 0
  let pc : Pi2Circuit := ⟨{ (default : Circuit) with logN := logN }, c.sigmaAt, c.kappaAt⟩
  let setupStack := pc.setupStack
  let start ← IO.monoMsNow
  let setupTree : LeanVM.Prover.Tree := Id.run (pc.setupTreeWith (m := Id) fun s ↦ pure (keccakF1600 s))
  let setupRoot := digestBytes setupTree.root
  IO.println s!"{v.name}: setup root {hexOf setupRoot} ({(← IO.monoMsNow) - start} ms)"
  if setupRoot != hexBytes ((v.tagged "SETUPROOT").getD 0 "") then
    throw (IO.userError s!"{v.name}: the setup's root differs")
  let seed := Id.run (H (RecStatement.name ++ iv ++ input))
  let (out, _) := Id.run ((pi2ProveStreamWith H G reads setupStack input values w).run (UniComplete.Wr.start seed))
  IO.println s!"{v.name}: proved ({(← IO.monoMsNow) - start} ms)"
  let wr := digestBytes out.wTree.root
  let qr := digestBytes out.qTree.root
  IO.println s!"  W root {hexOf wr}"
  IO.println s!"  Q root {hexOf qr}"
  if wr != hexBytes ((v.tagged "WROOT").getD 0 "") then throw (IO.userError s!"{v.name}: W's root differs")
  if qr != hexBytes ((v.tagged "QROOT").getD 0 "") then throw (IO.userError s!"{v.name}: Q's root differs")
  let expected := hexBytes ((v.tagged "STREAM").getD 0 "")
  if out.stream.toList != expected then
    throw (IO.userError s!"{v.name}: the stream differs ({out.stream.size} bytes, the Rust's {expected.length})")
  IO.println s!"{v.name}: the stream the same byte for byte ({expected.length} bytes)"

def main : IO Unit := do
  let path ← IO.getEnv "PI2_PROVER"
  let text ← IO.FS.readFile (path.getD "pi2_prover.txt")
  let vs := vectors (text.splitOn "\n")
  for v in vs do
    run1 v
  IO.println s!"{vs.length}/{vs.length} vectors agree"

end RecComposeTest

#eval RecComposeTest.main
