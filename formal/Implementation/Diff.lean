-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): Keccak-256 (`Common.keccak256`, `common/Common/Sponge.lean`).
import Implementation.Interp
import Common.Sponge

/-!
# The interpreter against the Rust verifier

`lake env lean --run Implementation/Diff.lean VECTORS`: each line of `VECTORS` (written by
`LEAN_VECTORS=VECTORS cargo test -p evm write_lean_vectors -- --ignored`, `crates/evm/src/lean.rs`)
is an index root, calldata of the verifier and what the Rust verifier
(`quotient::protocol::verify`) has `PCS_OPEN` check, the three calls' inputs back to back (or
`reject`), in hex. The interpreter (`run`, with leanerVM's Keccak-256) must give the same bytes on
every line.
-/

namespace Implementation.Diff

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def ofHex : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let x ← hexDigit a
    let y ← hexDigit b
    let tail ← ofHex rest
    pure ((16 * x + y).toUInt8 :: tail)
  | [_] => none

def toHex (l : List UInt8) : String :=
  String.join (l.map fun b =>
    let h := "0123456789abcdef".toList
    String.ofList [h.getD (b.toNat / 16) '0', h.getD (b.toNat % 16) '0'])

/-- One line: whether the interpreter agrees, or why not. -/
def check (line : String) : Except String Unit := do
  let parts := line.splitOn " "
  let [idxHex, cdHex, expected] := parts | throw s!"malformed line: {parts.length} fields"
  let some idx := ofHex idxHex.toList | throw "bad index root"
  let some cd := ofHex cdHex.toList | throw "bad calldata"
  if h : idx.length = 32 then
    let root : Vector UInt8 32 := ⟨idx.toArray, by simpa using h⟩
    let got := (run Common.keccak256 root cd).map fun ws => (calls ws).flatten
    match got, expected with
    | none, "reject" => pure ()
    | some bytes, e =>
      if toHex bytes = e then pure () else throw s!"mismatch on {cdHex}"
    | none, _ => throw s!"the interpreter rejects {cdHex}, the Rust does not"
  else throw "an index root of 32 bytes"

def main (args : List String) : IO UInt32 := do
  let [path] := args | do IO.eprintln "usage: Diff VECTORS"; return 2
  let lines := (← IO.FS.lines path).filter (· ≠ "")
  let mut bad := 0
  let mut rejects := 0
  for line in lines do
    if line.endsWith " reject" then rejects := rejects + 1
    match check line with
    | .ok () => pure ()
    | .error e => do
      bad := bad + 1
      if bad ≤ 5 then IO.eprintln e
  IO.println s!"{lines.size} vectors ({rejects} rejected by the Rust), {bad} disagreements"
  return if bad = 0 then 0 else 1

end Implementation.Diff

def main (args : List String) : IO UInt32 := Implementation.Diff.main args
