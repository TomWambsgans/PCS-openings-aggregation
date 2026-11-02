-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Transcribed from `crates/quotient/src/circuit.rs` (the wiring and the public rows adapted from leanVM,
-- branch PCS-openings-aggregation, commit 651453c6, `crates/flock/src/quotient/circuit.rs`) and
-- `crates/quotient/src/protocol.rs` (`Index`). Keccak's constants and the WHIR commitment's encoder and
-- Merkle tree are leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0: `Statement/Keccak.lean`,
-- `Statement/Prover/Ntt.lean`, `Statement/Prover/Run.lean`).
module

public import PcsQuotient.Relation
public import PcsQuotient.Domain
public import Statement.Prover.Run
public import Statement.Prover.Ntt

/-!
# The circuit and its commitment

**The gate.** A row has four cells `X, Y, C, V` and says `V = X + C + Y·C` (`circuit.rs:7-11`). On
bits that is `X ⊕ (C ∧ ¬Y)`: Keccak's χ, an XOR when `Y = 0`, a NOT when `X = 1, Y = 0`. A free
input bit is a row whose three inputs are wired to its own output (`v = v + v + v²`, so `v² = v`).

**The builder** (`Builder`, `circuit.rs:66-256`) is transcribed step by step, in the Rust's order, since
the order of the rows is the circuit: the `512` public rows first, each later row reading constants
or rows before it (or itself, for an input), constants folded as the Rust folds them (`not`, `xor`,
`chi`), Keccak-f[1600] one row per χ bit and per XOR of θ (`keccakF`), the membership statement
(`membership`). `finish` closes it on `2^logRows` rows: the public rows read the public words two
bits a row, and the **wiring** `σ` sends each cell to the next cell of its cycle, a cycle being a
source (a constant, or a row's `V` cell) and the cells that read it, in cell order.

**The circuit's commitment** (`indexRootWith`, `Index::new`, `protocol.rs`): the wiring
polynomial, `σ` read as the points `B(σ(i))` and taken to the novel basis (`Domain.coefficients`), is
the wiring table, its own stack (`wiringLayout`), committed by leanVM's WHIR commitment at rate `1/2`:
the `64` lanes' codewords (mumbai's `stackWordFast`) under a Merkle tree of Keccak-256 over `F`
(mumbai's `buildTreeM`). The deployed verifier holds its root, computed over Keccak-f[1600]; in the
model the setup computes it over `π` (`Security.lean`).

**Cells.** `cells` is every cell's value from the inputs, as the honest prover computes it
(`Circuit::outputs`, `Circuit::cells`, `circuit.rs:273-300`).
-/

@[expose] public section

namespace PcsQuotient

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- `PUBLIC_ROWS` (`circuit.rs:19`): the rows holding the public bits, eight words of `128`, two bits
a row. -/
def publicRows : ℕ := 512

/-- `WORD_BITS` (`circuit.rs:20`). -/
def wordBits : ℕ := 128

/-- What a cell reads (`Src`, `circuit.rs:26-30`): a constant, or row `r`'s `V` cell. -/
inductive Src where
  | zero
  | one
  | row (r : ℕ)
  deriving DecidableEq, Inhabited

/-- One gate, `V = X + C + Y·C`, by what its three inputs read (`Row`, `circuit.rs:34-38`). -/
structure Row where
  x : Src
  y : Src
  c : Src
  deriving DecidableEq, Inhabited

/-- `IDLE`: a row reading zeros. -/
def idle : Row := ⟨.zero, .zero, .zero⟩

/-- The gate on bits, `x ⊕ (c ∧ ¬y)` (`gate_bits`, `circuit.rs:47-49`). -/
def gateBits (x y c : Bool) : Bool := x ^^ (c && !y)

/-- **A circuit** (`Circuit`, `circuit.rs:55-64`): its rows (the public ones included, then idle
rows up to `2^logRows`), the rows that are free input bits in the order they are read, and the
wiring, cell `4r + role` (roles `X, Y, C, V`) to the next cell of its cycle. -/
structure Circuit where
  logRows : ℕ
  usedRows : ℕ
  rows : Array Row
  inputs : Array ℕ
  sigma : Array ℕ

/-! ### The builder -/

/-- The builder's state: the rows so far and the input rows. -/
structure Builder where
  rows : Array Row
  inputs : Array ℕ

/-- Building a circuit. -/
abbrev BuildM := StateM Builder

namespace Build

/-- A row; what reads its output. -/
def row (x y c : Src) : BuildM Src :=
  modifyGet fun b ↦ (.row b.rows.size, { b with rows := b.rows.push ⟨x, y, c⟩ })

/-- A free bit: a row reading its own output three times (`input`, `circuit.rs:100-104`). -/
def input : BuildM Src := do
  let b ← get
  set { b with inputs := b.inputs.push b.rows.size }
  row (.row b.rows.size) (.row b.rows.size) (.row b.rows.size)

/-- `¬a`, a constant folded (`not`, `circuit.rs:106-112`). -/
def not : Src → BuildM Src
  | .zero => pure .one
  | .one => pure .zero
  | a => row .one .zero a

/-- `a ⊕ b`, constants folded (`xor`, `circuit.rs:114-120`). -/
def xor : Src → Src → BuildM Src
  | .zero, v => pure v
  | v, .zero => pure v
  | .one, v => not v
  | v, .one => not v
  | a, b => row a .zero b

/-- `a ⊕ (¬b ∧ c)`, Keccak's χ, in one row unless a constant makes it cheaper (`chi`,
`circuit.rs:123-133`). -/
def chi (a : Src) : Src → Src → BuildM Src
  | .one, _ => pure a
  | _, .zero => pure a
  | .zero, c => xor a c
  | b, .one => do xor a (← not b)
  | b, c => row a b c

/-- A Keccak state of wires: lane `x + 5y`, bit `z` at index `64·(x + 5y) + z`. -/
abbrev WireState : Type := Array Src

/-- Wire `(lane, z)` of a state. -/
def WireState.at (a : WireState) (lane z : ℕ) : Src := a.getD (64 * lane + z) .zero

/-- One round of Keccak-f[1600] with the round constant `rc` (`keccak_f`, `circuit.rs:136-185`), the
rows in the Rust's order: θ's column parities (lane `x`, bit `z`, folding `y = 1 … 4`), then its
`d`, then each lane XORed with its `d`; ρ and π as wiring (lane `i`, rotated left by `ρ_i`, goes to
`π_i`); χ, one row a bit, `y`, `x`, `z` in that order; ι, a NOT where `rc` has a one. -/
def round (a : WireState) (rc : UInt64) : BuildM WireState := do
  -- θ: the column parities.
  let mut c : Array Src := Array.replicate (5 * 64) .zero
  for x in [0:5] do
    for z in [0:64] do
      let mut acc := a.at x z
      for y in [1:5] do
        acc ← xor acc (a.at (x + 5 * y) z)
      c := c.set! (64 * x + z) acc
  let cAt (x z : ℕ) : Src := c.getD (64 * x + z) .zero
  let mut d : Array Src := Array.replicate (5 * 64) .zero
  for x in [0:5] do
    for z in [0:64] do
      d := d.set! (64 * x + z) (← xor (cAt ((x + 4) % 5) z) (cAt ((x + 1) % 5) ((z + 63) % 64)))
  let mut a := a
  for i in [0:25] do
    for z in [0:64] do
      a := a.set! (64 * i + z) (← xor (a.at i z) (d.getD (64 * (i % 5) + z) .zero))
  -- ρ and π: wiring only.
  let mut b : WireState := Array.replicate 1600 .zero
  for i in [0:25] do
    let r := LeanVM.Parameters.keccakRho.getD i 0
    for z in [0:64] do
      b := b.set! (64 * LeanVM.Parameters.keccakPi i + (z + r) % 64) (a.at i z)
  -- χ: one row a bit.
  for y in [0:5] do
    for x in [0:5] do
      for z in [0:64] do
        a := a.set! (64 * (x + 5 * y) + z)
          (← chi (b.at (x + 5 * y) z) (b.at ((x + 1) % 5 + 5 * y) z) (b.at ((x + 2) % 5 + 5 * y) z))
  -- ι.
  for z in [0:64] do
    if (rc >>> z.toUInt64) &&& 1 = 1 then
      a := a.set! z (← not (a.at 0 z))
  return a

/-- **Keccak-f[1600]** on wires: the `24` rounds (`keccak_f`). -/
def keccakF (a : WireState) : BuildM WireState :=
  LeanVM.Parameters.keccakRC.foldlM round a

/-- **Keccak-256 of a 64-byte block** on wires (`keccak256_64`, `circuit.rs:188-199`): the message's
`512` bits (byte order, low bit first) in the first eight lanes, Keccak's padding of a 64-byte
message in one block (`0x01` at byte `64`, `0x80` at byte `135`), the digest's `256` bits likewise.
-/
def keccak256Block (message : List Src) : BuildM (List Src) := do
  let state : WireState := Array.ofFn (n := 1600) fun i ↦
    if i.val < 512 then message.getD i.val .zero
    else if i.val = 64 * 8 ∨ i.val = 64 * 16 + 63 then .one
    else .zero
  let out ← keccakF state
  return (List.range 256).map fun b ↦ out.getD b .zero

end Build

/-! ### Closing a circuit: the public rows and the wiring -/

/-- The wiring of `2^logRows` rows (`finish`, `circuit.rs:221-247`): every cell starts as its own
successor; each row's `V` cell opens its source's cycle (row order), then each reading cell joins the
cycle of what it reads (row order, roles `X, Y, C`), the last cell of a cycle sending back to its
first. -/
def wiring (logRows : ℕ) (rows : Array Row) : Array ℕ := Id.run do
  let n := 2 ^ logRows
  let none := 4 * n
  let mut first : Array ℕ := Array.replicate (n + 2) none
  let mut last : Array ℕ := Array.replicate (n + 2) none
  let mut sigma : Array ℕ := Array.range (4 * n)
  let slot : Src → ℕ
    | .zero => 0
    | .one => 1
    | .row r => 2 + r
  -- join `cell` to the cycle of source slot `at_`.
  for r in [0:n] do
    let (at_, cell) := (2 + r, 4 * r + 3)
    if first[at_]! = none then first := first.set! at_ cell
    else sigma := sigma.set! last[at_]! cell
    last := last.set! at_ cell
    sigma := sigma.set! cell first[at_]!
  for r in [0:n] do
    let row := rows.getD r idle
    for (role, src) in [(0, row.x), (1, row.y), (2, row.c)] do
      let (at_, cell) := (slot src, 4 * r + role)
      if first[at_]! = none then first := first.set! at_ cell
      else sigma := sigma.set! last[at_]! cell
      last := last.set! at_ cell
      sigma := sigma.set! cell first[at_]!
  return sigma

/-- **Close the circuit** on `2^logRows` rows (`finish`, `circuit.rs:202-255`), `public[J][j]` being
bit `j` of public word `J < 4`; word `4` is a one then zeros, words `5 … 7` zeros. Public row `r` reads
bits `2(r mod 64)` and `2(r mod 64) + 1` of word `⌊r / 64⌋`. -/
def finish (logRows : ℕ) (public_ : List (List Src)) (b : Builder) : Circuit :=
  let bit (word j : ℕ) : Src :=
    if word < 4 then (public_.getD word []).getD j .zero
    else if word = 4 ∧ j = 0 then .one
    else .zero
  let rows := Array.ofFn (n := 2 ^ logRows) fun r ↦
    if r.val < publicRows then
      let (word, pair_) := (r.val / (wordBits / 2), r.val % (wordBits / 2))
      ⟨bit word (2 * pair_), bit word (2 * pair_ + 1), .zero⟩
    else b.rows.getD r.val idle
  ⟨logRows, b.rows.size, rows, b.inputs, wiring logRows rows⟩

/-- `public_words` (`circuit.rs:304-311`): the `256` wires of `y` and of `root` as the four public
words, a word being sixteen bytes read big-endian. -/
def publicWords (y root : List Src) : List (List Src) :=
  (List.range 4).map fun word ↦
    (List.range wordBits).map fun j ↦
      (if word < 2 then y else root).getD (8 * (16 * (word % 2) + 15 - j / 8) + j % 8) .zero

/-- `constant_block` (`circuit.rs:313-323`): the `256` constant wires of 32 copies of `byte`. -/
def constantBlock (byte : UInt8) : List Src :=
  (List.range 256).map fun i ↦ if (byte >>> (i % 8).toUInt8) &&& 1 = 1 then .one else .zero

/-- The builder of the membership statement (`membership`, `circuit.rs:326-346`): the `256` input
bits of `x`; `y = H(x ‖ 0x11^32)` and the leaf `H(x ‖ 0x22^32)`; then each level: the sibling's `256`
input bits, the direction's, and `left = node ⊕ (direction ∧ (node ⊕ sibling))` (one χ, which negates
its middle input, reading `¬direction`), `right = left ⊕ node ⊕ sibling`, the node `H(left ‖ right)`.
Returns the wires of `y` and of the root. -/
def membershipBuilder : BuildM (List Src × List Src) := do
  let x ← (List.range 256).mapM fun _ ↦ Build.input
  let y ← Build.keccak256Block (x ++ constantBlock yPad)
  let mut node ← Build.keccak256Block (x ++ constantBlock leafPad)
  for _ in [0:depth] do
    let sibling ← (List.range 256).mapM fun _ ↦ Build.input
    let direction ← Build.input
    let keep ← Build.not direction
    let mut left : Array Src := #[]
    let mut right : Array Src := #[]
    for i in [0:256] do
      let differ ← Build.xor (node.getD i .zero) (sibling.getD i .zero)
      let l ← Build.chi (node.getD i .zero) keep differ
      right := right.push (← Build.xor l differ)
      left := left.push l
    node ← Build.keccak256Block (left.toList ++ right.toList)
  return (y, node)

/-- An empty builder: the public rows, idle until `finish`. -/
def Builder.new : Builder := ⟨Array.replicate publicRows idle, #[]⟩

/-- **The membership circuit** on `2^logRows` rows (`membership`, `circuit.rs:326-346`; deployed at
`logRows = 22`, `3 878 612` rows used). -/
def membership (logRows : ℕ) : Circuit :=
  let ((y, root), b) := membershipBuilder.run Builder.new
  finish logRows (publicWords y root) b

/-- `membership_inputs` (`circuit.rs:349-357`): the free inputs of `membership` for a secret, `x`'s
bits, then each level's sibling's bits and its direction, a byte's bits low first. -/
def membershipInputs (w : Secret) : List Bool :=
  let bits (b : Bytes32) : List Bool := (List.range 256).map fun i ↦ (b.toList.getD (i / 8) 0 >>> (i % 8).toUInt8) &&& 1 = 1
  bits w.x ++ (List.finRange depth).flatMap fun i ↦ bits w.siblings[i] ++ [w.directions[i]]

/-- The secret the membership circuit's input bits spell (the inverse of `membershipInputs`): `x`
from the first `256`, then each level's sibling and direction from the next `257`. -/
def secretOfInputs (bits : List Bool) : Secret :=
  let bytes (from_ : ℕ) : Bytes32 := Vector.ofFn fun j : Fin 32 ↦
    (List.range 8).foldl (fun acc k ↦ if bits.getD (from_ + 8 * j.val + k) false then acc ||| (1 <<< k.toUInt8) else acc) 0
  ⟨bytes 0, Vector.ofFn fun i ↦ bytes (256 + 257 * i.val),
    Vector.ofFn fun i ↦ bits.getD (256 + 257 * i.val + 256) false⟩

/-! ### Cells -/

/-- The bit a source holds, given every row's output (`read`, `circuit.rs:259-265`). -/
def readSrc (v : Array Bool) : Src → Bool
  | .zero => false
  | .one => true
  | .row r => v.getD r false

/-- Every row's output bit from the free inputs (`Circuit::outputs`, `circuit.rs:273-285`): the
inputs set, then each row from `512` on and the public rows last, each from rows before it. -/
def Circuit.outputs (c : Circuit) (inputs : List Bool) : Array Bool := Id.run do
  let mut v : Array Bool := Array.replicate c.rows.size false
  for (r, bit) in c.inputs.toList.zip inputs do
    v := v.set! r bit
  for r in List.range' publicRows (c.rows.size - publicRows) ++ List.range publicRows do
    let row := c.rows.getD r idle
    v := v.set! r (gateBits (readSrc v row.x) (readSrc v row.y) (readSrc v row.c))
  return v

/-- **Every cell's value from the free inputs** (`Circuit::cells`, `circuit.rs:288-300`): cell
`4r + role` holds what role `X`, `Y`, `C` of row `r` reads, or the row's output for `V`. -/
def Circuit.cells (c : Circuit) (inputs : List Bool) : Array K :=
  let v := c.outputs inputs
  Array.ofFn (n := 4 * c.rows.size) fun i ↦
    let row := c.rows.getD (i.val / 4) idle
    let bit := match i.val % 4 with
      | 0 => readSrc v row.x
      | 1 => readSrc v row.y
      | 2 => readSrc v row.c
      | _ => v.getD (i.val / 4) false
    if bit then 1 else 0

/-! ### The circuit's commitment -/

/-- **The wiring table** (`Index::new`, `protocol.rs`): `B(σ(i))` for every cell, in the novel
basis; the wiring layout stacks it whole. -/
def Circuit.wiringTable (c : Circuit) : Array K :=
  Domain.coefficients (c.logRows + 2) 0 (c.sigma.map Domain.point)

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **The WHIR commitment of a stack** of `2^μ` words of `K` over `F`, at rate `1/2` (`pcs::whir::commit`
as `opening::commit` calls it): the Merkle tree of Keccak-256 over `F` of the `64` lanes' codewords,
leaf `p` the lanes' entries at `x_p` in reverse lane order (mumbai's `stackWordFast`, `buildTreeM`),
`2^(μ − 6 + 1)` leaves. -/
def commitWith (μ : ℕ) (stack : Array K) : m LeanVM.Prover.Tree :=
  LeanVM.Prover.buildTreeM F (μ - 6 + 1) (LeanVM.Prover.stackWordFast μ 1 stack)

/-- **The circuit's commitment** over `F`: the root of the WHIR commitment of its wiring table. -/
def Circuit.indexRootWith (c : Circuit) : m Digest := do
  return (← commitWith F (c.logRows + 2) c.wiringTable).root

/-- **The circuit's commitment's tree** over `F`: the Merkle tree of the WHIR commitment of its wiring
table, whose root is `indexRootWith` (the setup computes it, `Security.lean`; the extractor reads its
Keccak-256 evaluations, `Tree.evaluations`). -/
def Circuit.indexTreeWith (c : Circuit) : m LeanVM.Prover.Tree :=
  commitWith F (c.logRows + 2) c.wiringTable

end With

/-- **The Keccak-256 evaluations a Merkle tree holds** (mumbai's `Tree`, as `buildTreeM` builds it),
in the order `buildTreeM` computes them: each of the `2^height` leaves' bytes (`kBytes` of its row's
words) with its digest, then, level by level from the leaves up, each node's `64` bytes (its two
children's digests) with its digest. A pure function of the tree. For the circuit's commitment
(`Circuit.indexTreeWith`) these are the setup's Keccak-256 evaluations, which the extractor reads
(`Security.lean`, `Extractor.lean`). -/
def Tree.evaluations (t : LeanVM.Prover.Tree) : List (List UInt8 × Digest) :=
  let level (l : ℕ) : Array Digest := t.levels.getD l #[]
  (List.range (2 ^ t.height)).map (fun i ↦ ((t.word i).flatMap kBytes, (level 0).getD i default)) ++
    (List.range t.height).flatMap fun l ↦ (List.range (2 ^ (t.height - (l + 1)))).map fun j ↦
      (digestBytes ((level l).getD (2 * j) default) ++ digestBytes ((level l).getD (2 * j + 1) default),
        (level (l + 1)).getD j default)

end PcsQuotient

end
