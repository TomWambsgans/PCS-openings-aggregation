/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
The Keccak constants are leanerVM's (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`,
commit 6175f1a0, `Statement/Keccak.lean`, MIT OR Apache-2.0), imported, not copied.
-/
import Statement.Keccak

/-!
# The membership circuit, as `crates/quotient/src/circuit.rs` builds it

Read first. A transcription of `quotient::circuit`: the rows of one gate `V = X + C + Y·C`
(`X ⊕ (C ∧ ¬Y)` on bits, Keccak's χ), the `Builder` with its constant folding, Keccak-f[1600] and
Keccak-256 of a 64-byte block as rows, the membership statement, and `finish` (the public rows and
the wiring permutation σ). Every function makes the same rows in the same order as its Rust
namesake, with the same constant folding; the loops of the Rust are `mapM` over `List.range` in the
same order. The one rewrite: ρ and π, which are wiring only, are computed by the inverse lane map
(`piInv`, `rho`) instead of the Rust's forward assignment `b[PI[i]][(z + r) % 64] = a[i][z]`; the
sources are the same (`piInv_keccakPi`), and the differential test compares the rows and σ with
the Rust's.

The statement the circuit computes (`statement.rs`): `y = H(x ‖ 0x11^32)`, `h_0 = H(x ‖ 0x22^32)`,
`h_{i+1} = H(sibling_i ‖ h_i)` if bit `i` of the directions is set and `H(h_i ‖ sibling_i)` if not,
`root = h_32`, `H` = Keccak-256 (leanerVM's `keccak256`, Ethereum's).
-/

namespace PcsCircuit

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol

/-! ## Rows -/

/-- What a cell reads: a constant, or row `r`'s `V` cell (`circuit::Src`). -/
inductive Src where
  | zero
  | one
  | row (r : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- One gate, `V = X + C + Y·C`, by what its three input cells read (`circuit::Row`). -/
structure Row where
  x : Src
  y : Src
  c : Src
  deriving DecidableEq, Repr, Inhabited

/-- A row reading zeros (`IDLE`). -/
def Row.idle : Row := ⟨.zero, .zero, .zero⟩

/-- The rows holding the public bits: eight words of 128, two bits a row (`PUBLIC_ROWS`). -/
def publicRows : Nat := 512
/-- `WORD_BITS`. -/
def wordBits : Nat := 128
/-- The membership circuit's rows: `2^logRows` (`LOG_ROWS`). -/
def logRows : Nat := 22
/-- The Merkle path's length (`statement::DEPTH`). -/
def depth : Nat := 32
/-- The domain constants `y` and the leaf are hashed with (`Y_PAD`, `LEAF_PAD`). -/
def yPad : UInt8 := 0x11
def leafPad : UInt8 := 0x22

/-- The gate on bits: `x ⊕ (c ∧ ¬y)` (`gate_bits`). -/
def gateBits (x y c : Bool) : Bool := x ^^ (c && !y)

/-! ## The builder -/

/-- The rows made so far, the `512` public ones first (idle until `finish`), and the rows that are
free input bits, in the order they were made (`circuit::Builder`). -/
structure Builder where
  rows : Array Row
  inputs : Array Nat

/-- `Builder::new`: the public rows, idle. -/
def Builder.new : Builder := { rows := Array.replicate publicRows Row.idle, inputs := #[] }

/-- The builder's monad: a state of rows. -/
abbrev BuildM := StateM Builder

namespace Builder

/-- `Builder::row`: a new row, read as its output. -/
def row (x y c : Src) : BuildM Src :=
  modifyGet fun b => (.row b.rows.size, { b with rows := b.rows.push ⟨x, y, c⟩ })

/-- `Builder::input`: a free bit, a row reading its own output three times. -/
def input : BuildM Src :=
  modifyGet fun b =>
    let here := Src.row b.rows.size
    (here, { rows := b.rows.push ⟨here, here, here⟩, inputs := b.inputs.push b.rows.size })

/-- `Builder::not`: `¬a`, folded on constants; otherwise the row `1 ⊕ (a ∧ ¬0)`. -/
def notG : Src → BuildM Src
  | .zero => pure .one
  | .one => pure .zero
  | a => row .one .zero a

/-- `Builder::xor`: `a ⊕ b`, folded when either is a constant; otherwise the row `a ⊕ (b ∧ ¬0)`.
The match arms are the Rust's, tried in the same order. -/
def xorG : Src → Src → BuildM Src
  | .zero, v => pure v
  | v, .zero => pure v
  | .one, v => notG v
  | v, .one => notG v
  | a, b => row a .zero b

/-- `Builder::chi`: `a ⊕ (¬b ∧ c)`, Keccak's χ, in one row unless a constant makes it cheaper. -/
def chiG (a b c : Src) : BuildM Src :=
  match b, c with
  | .one, _ => pure a
  | _, .zero => pure a
  | .zero, _ => xorG a c
  | _, .one => do
    let notB ← notG b
    xorG a notB
  | _, _ => row a b c

/-! ## Keccak-f[1600] -/

/-- A Keccak state of wires: lane `i = x + 5y`, bit `z` at index `64 i + z` (the Rust's
`[[Src; 64]; 25]`, flattened). -/
abbrev State := Array Src

/-- Bit `z` of lane `i`. -/
def State.get (a : State) (i z : Nat) : Src := a.getD (64 * i + z) .zero

/-- The lane π sends to lane `j` (`PI` inverted: `PI[piInv j] = j`). -/
def piInv : Nat → Nat
  | 0 => 0 | 1 => 6 | 2 => 12 | 3 => 18 | 4 => 24
  | 5 => 3 | 6 => 9 | 7 => 10 | 8 => 16 | 9 => 22
  | 10 => 1 | 11 => 7 | 12 => 13 | 13 => 19 | 14 => 20
  | 15 => 4 | 16 => 5 | 17 => 11 | 18 => 17 | 19 => 23
  | 20 => 2 | 21 => 8 | 22 => 14 | 23 => 15 | 24 => 21
  | _ => 0

/-- `RHO`: the left rotation of lane `i` (leanerVM's `keccakRho`, `rho_eq`). -/
def rho : Nat → Nat
  | 0 => 0 | 1 => 1 | 2 => 62 | 3 => 28 | 4 => 27
  | 5 => 36 | 6 => 44 | 7 => 6 | 8 => 55 | 9 => 20
  | 10 => 3 | 11 => 10 | 12 => 43 | 13 => 25 | 14 => 39
  | 15 => 41 | 16 => 45 | 17 => 15 | 18 => 21 | 19 => 8
  | 20 => 18 | 21 => 2 | 22 => 61 | 23 => 56 | 24 => 14
  | _ => 0

/-- θ: the column parities (`c`, each a chain of four XORs), their mixes (`d`), then each lane
XORed with its column's mix; the loops in the Rust's order (`x`, then `z`, then `y`). -/
def theta (a : State) : BuildM State := do
  let c ← (List.range 320).mapM fun k =>
    [1, 2, 3, 4].foldlM (fun acc y => xorG acc (a.get (k / 64 + 5 * y) (k % 64))) (a.get (k / 64) (k % 64))
  let c := c.toArray
  let d ← (List.range 320).mapM fun k =>
    xorG (State.get c ((k / 64 + 4) % 5) (k % 64)) (State.get c ((k / 64 + 1) % 5) ((k % 64 + 63) % 64))
  let d := d.toArray
  let a ← (List.range 1600).mapM fun k => xorG (a.get (k / 64) (k % 64)) (State.get d (k / 64 % 5) (k % 64))
  pure a.toArray

/-- ρ and π, wiring only: lane `i`, rotated left by `rho i`, goes to `PI[i]`; so lane `j` bit `z`
reads lane `piInv j` bit `z - rho (piInv j)` (mod `64`). -/
def rhoPi (a : State) : State :=
  ((List.range 1600).map fun k =>
    a.get (piInv (k / 64)) ((k % 64 + 64 - rho (piInv (k / 64))) % 64)).toArray

/-- χ: one row a bit, in the Rust's order (`y`, then `x`, then `z`, that is `64 i + z`). -/
def chiStep (b : State) : BuildM State := do
  let a ← (List.range 1600).mapM fun k =>
    chiG (b.get (k / 64) (k % 64)) (b.get ((k / 64 % 5 + 1) % 5 + 5 * (k / 64 / 5)) (k % 64))
      (b.get ((k / 64 % 5 + 2) % 5 + 5 * (k / 64 / 5)) (k % 64))
  pure a.toArray

/-- ι: a NOT where the round constant has a one (`(rc >> z) & 1 == 1`), lane `0` only. -/
def iota (a : State) (rc : UInt64) : BuildM State := do
  let lane ← (List.range 64).mapM fun z =>
    if rc.toNat.testBit z then notG (a.get 0 z) else pure (a.get 0 z)
  let lane := lane.toArray
  pure ((List.range 1600).map fun k => if k < 64 then lane.getD k .zero else a.getD k .zero).toArray

/-- One round: θ, ρ and π, χ, ι. -/
def round (a : State) (rc : UInt64) : BuildM State := do
  let a ← theta a
  let b := rhoPi a
  let a ← chiStep b
  iota a rc

/-- `Builder::keccak_f`: Keccak-f[1600], the `24` rounds of leanerVM's `keccakRC`. -/
def keccakF (a : State) : BuildM State := keccakRC.foldlM round a

/-- `Builder::keccak256_64`: Keccak-256 of a 64-byte block, its `512` bits in byte order and low
bit first; Keccak's padding of a 64-byte message in one 136-byte block, `0x01` at byte `64` (lane
`8`, bit `0`) and `0x80` at byte `135` (lane `16`, bit `63`); the digest's `256` bits likewise. -/
def keccak256Block (message : Array Src) : BuildM (Array Src) := do
  let state : State := ((List.range 1600).map fun k =>
    if k < 512 then message.getD k .zero
    else if k = 64 * 8 then .one
    else if k = 64 * 16 + 63 then .one
    else .zero).toArray
  let out ← keccakF state
  pure ((List.range 256).map fun k => out.getD k .zero).toArray

/-- `n` free bits. -/
def freeBits (n : Nat) : BuildM (Array Src) := do
  let l ← (List.range n).mapM fun _ => input
  pure l.toArray

end Builder

/-! ## The membership statement -/

open Builder

/-- `constant_block`: `32` copies of a byte, as `256` constant wires, low bit first. -/
def constantBlock (byte : UInt8) : Array Src :=
  ((List.range 256).map fun i => if byte.toNat.testBit (i % 8) then Src.one else Src.zero).toArray

/-- One level of the path: the sibling's `256` bits and the direction bit as inputs, the ordered
pair by a swap (`keep = ¬direction`, `left = χ(node, keep, differ) = node ⊕ (direction ∧ differ)`,
`right = left ⊕ differ`, `differ = node ⊕ sibling`), then its hash. -/
def level (node : Array Src) : BuildM (Array Src) := do
  let sibling ← freeBits 256
  let direction ← input
  let keep ← notG direction
  let lr ← (List.range 256).mapM fun i => do
    let differ ← xorG (node.getD i .zero) (sibling.getD i .zero)
    let l ← chiG (node.getD i .zero) keep differ
    let r ← xorG l differ
    pure (l, r)
  keccak256Block ((lr.map Prod.fst).toArray ++ (lr.map Prod.snd).toArray)

/-- The rows of `membership` before `finish`: `x`, `y = H(x ‖ 0x11^32)`, the leaf
`H(x ‖ 0x22^32)`, the `32` levels; the result is `(y, root)`. -/
def membershipBuild : BuildM (Array Src × Array Src) := do
  let x ← freeBits 256
  let y ← keccak256Block (x ++ constantBlock yPad)
  let leaf ← keccak256Block (x ++ constantBlock leafPad)
  let root ← (List.range depth).foldlM (fun node _ => level node) leaf
  pure (y, root)

/-- `public_words`: the `256` wires of `y` and of `root` as the four public words they are read
as, bit `j` of word `J`; a word is sixteen bytes, big-endian. -/
def publicWords (y root : Array Src) (word j : Nat) : Src :=
  (if word < 2 then y else root).getD (8 * (16 * (word % 2) + 15 - j / 8) + j % 8) .zero

/-! ## Closing the circuit -/

/-- The closed circuit (`circuit::Circuit`): `2^logRows` rows, the free inputs in order, and σ,
each cell's successor on its cycle, cell `4 r + role` for the roles `X, Y, C, V`. -/
structure Circuit where
  logRows : Nat
  usedRows : Nat
  rows : Array Row
  inputs : Array Nat
  sigma : Array Nat

/-- Bit `j` of public word `word`: words `0`–`3` from the statement, word `4` a one then zeros,
words `5`–`7` zeros (`finish`'s `bit`). -/
def publicBit (pub : Nat → Nat → Src) (word j : Nat) : Src :=
  if word < 4 then pub word j else if word = 4 ∧ j = 0 then .one else .zero

/-- Public row `r`: two bits of word `r / 64`, `C` reading zero. -/
def publicRow (pub : Nat → Nat → Src) (r : Nat) : Row :=
  ⟨publicBit pub (r / 64) (2 * (r % 64)), publicBit pub (r / 64) (2 * (r % 64) + 1), .zero⟩

/-- Which cycle a source's cells join: `0` for zero, `1` for one, `2 + r` for row `r`. -/
def slot : Src → Nat
  | .zero => 0
  | .one => 1
  | .row r => 2 + r

/-- The state of the wiring's construction: each slot's first and last cell so far (`NONE` as
`none`), and σ. -/
structure Joins where
  first : Array (Option Nat)
  last : Array (Option Nat)
  sigma : Array Nat

/-- `finish`'s `join`: `cell` joins the cycle of slot `slotAt`, after its last cell, before its
first. -/
def join (st : Joins) (slotAt cell : Nat) : Joins :=
  match st with
  | ⟨first, last, sigma⟩ =>
    match first.getD slotAt none with
    | none => ⟨first.set! slotAt (some cell), last.set! slotAt (some cell), sigma.set! cell cell⟩
    | some f =>
      let prev := (last.getD slotAt none).getD 0
      ⟨first, last.set! slotAt (some cell), (sigma.set! prev cell).set! cell f⟩

/-- σ: a cycle for each source, its output cell (for a row) then the cells reading it, in cell
order (`finish`). -/
def wiring (rows : Array Row) : Array Nat :=
  let n := rows.size
  let st : Joins := ⟨Array.replicate (n + 2) none, Array.replicate (n + 2) none, Array.range (4 * n)⟩
  let st := (List.range n).foldl (fun st r => join st (2 + r) (4 * r + 3)) st
  let st := (List.range n).foldl (fun st r =>
    let row := rows.getD r .idle
    join (join (join st (slot row.x) (4 * r)) (slot row.y) (4 * r + 1)) (slot row.c) (4 * r + 2)) st
  st.sigma

/-- `finish`'s rows: the public rows written, the rows padded with idle ones to `2^logRows`. -/
def Builder.finishRows (b : Builder) (logRows : Nat) (pub : Nat → Nat → Src) : Array Row :=
  ((List.range (2 ^ logRows)).map fun r =>
    if r < publicRows then publicRow pub r else b.rows.getD r .idle).toArray

/-- `Builder::finish`: the rows (`finishRows`) and σ. (The Rust asserts that the rows fit;
`buildRows_lt` proves it for `membership`.) -/
def Builder.finish (b : Builder) (logRows : Nat) (pub : Nat → Nat → Src) : Circuit :=
  let rows := b.finishRows logRows pub
  { logRows, usedRows := b.rows.size, rows, inputs := b.inputs, sigma := wiring rows }

/-- Run a builder program from a builder: its result and the grown builder. -/
def runBuild {α : Type} (m : BuildM α) (b : Builder) : α × Builder := (m.run b).run

/-- **The membership circuit** (`circuit::membership`). -/
def membership : Circuit :=
  let r := runBuild membershipBuild Builder.new
  r.2.finish logRows (publicWords r.1.1 r.1.2)

/-! ## The computation -/

/-- The bit a source holds, given every row's output (`circuit::read`). -/
def readBit (v : Array Bool) : Src → Bool
  | .zero => false
  | .one => true
  | .row r => v.getD r false

/-- `Circuit::outputs`: every row's output bit from the free inputs; the rows from `512` on in
order (each reads rows before it, or itself), then the public rows. -/
def Circuit.outputs (c : Circuit) (bits : Array Bool) : Array Bool :=
  let v := (List.range c.inputs.size).foldl
    (fun v k => v.set! (c.inputs.getD k 0) (bits.getD k false)) (Array.replicate c.rows.size false)
  (List.range' publicRows (c.rows.size - publicRows) ++ List.range publicRows).foldl (fun v r =>
    let row := c.rows.getD r .idle
    v.set! r (gateBits (readBit v row.x) (readBit v row.y) (readBit v row.c))) v

/-! ## The statement -/

/-- `H`: Keccak-256 of a byte string, its `32` bytes (leanerVM's `keccak256`). -/
def H (data : List UInt8) : List UInt8 := KeccakHash.digestBytes (KeccakHash.keccak256 data)

/-- What the prover knows (`statement::Secret`): `x`, the `32` siblings (`32` bytes each), and the
directions, bit `i` saying that the sibling is on the left at level `i`. -/
structure Secret where
  x : List UInt8
  siblings : List (List UInt8)
  directions : Nat

/-- The node above `node` at level `i`: the hash of the ordered pair. -/
def Secret.up (s : Secret) (node : List UInt8) (i : Nat) : List UInt8 :=
  if s.directions.testBit i then H (s.siblings.getD i [] ++ node) else H (node ++ s.siblings.getD i [])

/-- `y = H(x ‖ 0x11^32)` (`Secret::statement`). -/
def Secret.y (s : Secret) : List UInt8 := H (s.x ++ List.replicate 32 yPad)

/-- `root`: from the leaf `H(x ‖ 0x22^32)` up the `32` levels (`Secret::statement`). -/
def Secret.root (s : Secret) : List UInt8 :=
  (List.range depth).foldl s.up (H (s.x ++ List.replicate 32 leafPad))

/-- Sixteen bytes from `16 h`, as a big-endian number (`statement::halves`). -/
def half (bytes : List UInt8) (h : Nat) : Nat :=
  (List.range 16).foldl (fun acc k => acc * 256 + (bytes.getD (16 * h + k) 0).toNat) 0

/-- The four public words of the statement: `y`'s halves, then `root`'s (`Statement::halves`). -/
def Secret.words (s : Secret) (word : Nat) : Nat :=
  half (if word < 2 then s.y else s.root) (word % 2)

/-- The `256` bits of `32` bytes, byte order, low bit first. -/
def bytesBits (bytes : List UInt8) : List Bool :=
  (List.range 256).map fun i => (bytes.getD (i / 8) 0).toNat.testBit (i % 8)

/-- `membership_inputs`: the free inputs of `membership` for a secret: `x`, then each level's
sibling and direction. -/
def Secret.inputs (s : Secret) : Array Bool :=
  (bytesBits s.x ++ (List.range depth).flatMap fun i =>
    bytesBits (s.siblings.getD i []) ++ [s.directions.testBit i]).toArray

end PcsCircuit
