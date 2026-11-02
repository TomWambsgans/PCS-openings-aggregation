/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-/
import Circuit.Defs
import Statement.Fast.Keccak

/-!
# The differential test against the Rust circuit

`lake exe dump-circuit OUT` writes `membership` in the format of `crates/quotient/examples/dump_circuit.rs`
(little-endian `u32`s: the number of rows, the rows used, the number of inputs; each row's `X, Y, C`
sources, `0` zero, `1` one, `2 + r` row `r`; the input rows; σ), and prints the public words that
`Circuit.outputs` computes for a fixed secret next to `Secret.words`. The two files must have the same
SHA-256, and the words must agree with each other and with the Rust's. Not part of the proofs.
-/

open PcsCircuit

/-- Append a little-endian `u32`. -/
def pushU32 (b : ByteArray) (x : Nat) : ByteArray :=
  let x := x.toUInt32
  ((b.push x.toUInt8).push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8).push (x >>> 24).toUInt8

/-- A source as the Rust example codes it. -/
def srcCode : Src → Nat
  | .zero => 0
  | .one => 1
  | .row r => r + 2

/-- A number as `32` hexadecimal digits. -/
def hex32 (n : Nat) : String :=
  let digits := Nat.toDigits 16 n
  String.ofList (List.replicate (32 - digits.length) '0' ++ digits)

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: dump-circuit OUT")
  let c := membership
  IO.println s!"rows {c.rows.size} used {c.usedRows} inputs {c.inputs.size} sigma {c.sigma.size}"
  let mut buf := ByteArray.emptyWithCapacity (4 * (3 + 3 * c.rows.size + c.inputs.size + c.sigma.size))
  buf := pushU32 buf c.rows.size
  buf := pushU32 buf c.usedRows
  buf := pushU32 buf c.inputs.size
  for row in c.rows do
    buf := pushU32 (pushU32 (pushU32 buf (srcCode row.x)) (srcCode row.y)) (srcCode row.c)
  for r in c.inputs do
    buf := pushU32 buf r
  for s in c.sigma do
    buf := pushU32 buf s
  IO.FS.writeBinFile path buf
  -- The secret of the Rust example.
  let s : Secret := {
    x := (List.range 32).map fun i => (i * 37 + 11).toUInt8
    siblings := (List.range 32).map fun l => (List.range 32).map fun i => (l * 101 + i * 13 + 5).toUInt8
    directions := 0xA5C31E77 }
  let v := c.outputs s.inputs
  for word in List.range 4 do
    let w := (List.range 128).foldl (fun acc j =>
      let row := c.rows.getD (word * 64 + j / 2) .idle
      if readBit v (if j % 2 = 0 then row.x else row.y) then acc + 2 ^ j else acc) 0
    IO.println s!"word {word}: circuit {hex32 w} statement {hex32 (s.words word)}"
