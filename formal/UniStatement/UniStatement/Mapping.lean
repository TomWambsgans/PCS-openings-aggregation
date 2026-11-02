-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The basis-B encoding is `crates/leanvm_univariate`'s
-- (SPEC.md §2); the novel-basis transform is this repository's `formal/Statement` (`PcsQuotient.Domain`); the
-- relation and its stack are `formal/Lv42`'s (leanerVM `mumbai` f0393df4's, MIT OR Apache-2.0).
module

public import UniStatement.Run
public import PcsQuotient.Domain
public import Lv42.Protocol.LeanIsa

/-!
# The univariate commitments against Lv42's stack

The verifier's `C1` and setup commitments hold the tables' columns as **coefficients** in the basis `B`
(SPEC.md §2) on their own stack (`layouts`); Lv42's relation `M3Holds (leanIsaInstance F prog s) input q`
is about one stack `q` of **values** on the Boolean cube, in leanVM's layout (`LeanIsa.layout`). This file
is the map between them, as definitions:

* `basisValue c r x`: the value at `ω_x` of the column whose `2^r` basis-`B` coefficients are `c`, the
  `K`-multilinear extension of `c` at the digits `w_l(ω_x) = ω_{x >> l}` (SPEC.md §2:
  `f(t) = ĉ(w_0(t), …, w_{r−1}(t))`);
* `bCoefficients r v`: the inverse, the basis-`B` coefficients of the column of values `v`: the novel-basis
  coefficients (`PcsQuotient.Domain.coefficients`), then `c_k = Σ_{S ⊆ k} d_S`, since
  `B_k = Σ_{S ⊇ k} X_S` (the runner checks `basisValue ∘ bCoefficients = id` at small sizes);
* **`lv42Stack`**, the Lv42 stack a `C1` stack carries: Lv42's columns in its stacking order
  (`LeanIsa.stackOrder`), each read off `C1` as the correspondence table says, the committed ones by
  `basisValue`, `QFLOCK` as it is (it is committed as values in both);
* the setup's tables (`setupStack`, `matrixStack`): the bytecode's 16 tuple slots and the memory's
  addresses (in basis `B`), and Flock's matrices `A0`, `B0` (`0`/`1` entries, row low).

**The correspondence** (column of `C1` ↦ column of Lv42's `leanIsaInstance`; `t` an opcode, `i` a column):

| `C1` (`UniStatement.Column`) | Lv42 (`LeanIsa.Col`) | encoding |
|---|---|---|
| `memory k`, `k < 3` (limbs), `memory 3` (final counts) | `memCol k` (`MEM_LO, MEM_HI, MEM_TOP, MFCNT`) | basis `B`, `2^logMem` |
| `bytecodeFinal` | `bfcntCol` (`BFCNT`) | basis `B`, `2^logBytecode` |
| `qflock` | `flockCol` (`QFLOCK`, the Flock region) | values, `2^(8 + τ_B)` |
| `table t i`, `i` not a `BLAKE2S` limb | `⟨opIdx t, i⟩` | basis `B`, `2^τ_t` |
| `table 5 i`, `9 ≤ i < 27` (the limbs' copies) | none: Lv42 reads limb `i − 9` off `QFLOCK`'s slot | the copies equal the slots on every row (`Q_W`) |
| `inverse t` (`z_T`) | none | proves `CountsNonzero` (`Q_W`) |
| `qflockSlot j` (a view of `qflock`) | `QFLOCK`'s strided slot | — |

The column index `i` of a table is the same on both sides: both are leanVM's `layout.rs` order (Lv42's
`Verifier.tables` names them, and its `padRow` reads them by position).
-/

@[expose] public section

namespace UniStatement

open LeanVM.Parameters
open Lv42.Protocol.LeanIsa (Col Sizes blocks stackOrder kappa leanIsaμ)
open Lv42.Semantics (Program PublicInput)

/-- The `K`-multilinear extension of a table at a point of `K`, low coordinate first. -/
def mleK (table : Array K) (pt : List K) : K :=
  (pt.foldl (fun (cur : Array K) r ↦ Array.ofFn (n := cur.size / 2) fun i ↦
    let a := cur.getD (2 * i.val) 0
    let b := cur.getD (2 * i.val + 1) 0
    a + r * (a + b)) table).getD 0 0

/-- **The value at `ω_x`** of the column of `2^r` basis-`B` coefficients `c`: `ĉ(ω_x, ω_{x>>1}, …)`. -/
def basisValue (c : Array K) (r x : ℕ) : K := mleK c ((List.range r).map fun l ↦ point (x >>> l))

/-- `c_k = Σ_{S ⊆ k} d_S` (the subset-sum transform, its own inverse in characteristic two). -/
def subsetSums (r : ℕ) (d : Array K) : Array K :=
  (List.range r).foldl (fun a l ↦ Array.ofFn (n := a.size) fun k ↦
    if k.val.testBit l then a.getD k.val 0 + a.getD (k.val - 2 ^ l) 0 else a.getD k.val 0) d

/-- **The basis-`B` coefficients** of the column of values `v` on `V_r`. -/
def bCoefficients (r : ℕ) (v : Array K) : Array K := subsetSums r (PcsQuotient.Domain.coefficients r 0 v)

/-- `C1`'s layout at a shape (`layouts`; it does not depend on `C2`'s columns). -/
def c1Layout (shape : UniStatement.Shape) : StackLayout := ((layouts shape []).lookup .c1).getD default

/-- The setup's layout at a shape. -/
def setupLayout (shape : UniStatement.Shape) : StackLayout := ((layouts shape []).lookup .setup).getD default

/-- Column `column`'s block of a stack (its limb `0`): `2^vars` words from its offset. -/
def c1Block (layout : StackLayout) (stack : ℕ → K) (column : UniStatement.Column) : Array K :=
  match layout.limbs column with
  | (_, vars, offset) :: _ => Array.ofFn (n := 2 ^ vars) fun i ↦ stack (offset + i.val)
  | [] => #[]

/-- **Lv42's column `c`, read off a `C1` stack** (the correspondence above), as Lv42's stacking reads it
(`Vector K (2 ^ kappa prog s c)`). -/
def lv42Column (prog : Program) (s : Sizes) (shape : UniStatement.Shape) (stack : ℕ → K) :
    (c : Col) → Vector K (2 ^ kappa prog s c)
  | ⟨⟨0, _⟩, i⟩ =>
    let coeffs := c1Block (c1Layout shape) stack (.memory i.val)
    Vector.ofFn fun x ↦ basisValue coeffs s.logMem x.val
  | ⟨⟨1, _⟩, _⟩ =>
    let coeffs := c1Block (c1Layout shape) stack .bytecodeFinal
    Vector.ofFn fun x ↦ basisValue coeffs prog.logSize x.val
  | ⟨⟨2, _⟩, _⟩ =>
    let values := c1Block (c1Layout shape) stack .qflock
    Vector.ofFn fun x ↦ values.getD x.val 0
  | ⟨⟨j + 3, h⟩, i⟩ =>
    let coeffs := c1Block (c1Layout shape) stack (.table j i.val)
    Vector.ofFn fun x ↦ basisValue coeffs (s.τ ⟨j, by omega⟩) x.val

/-- **The Lv42 stack a `C1` stack carries**: Lv42's committed columns (`stackOrder`: every column but the
`BLAKE2S` limbs, largest first), each read off `C1` (`lv42Column`), stacked as Lv42 stacks a witness
(`Blocks.stackColumn`, as `LeanIsa.stackOf`). -/
def lv42Stack (prog : Program) (s : Sizes) (shape : UniStatement.Shape) (stack : ℕ → K) :
    LeanVM.Protocol.Column (leanIsaμ prog s) :=
  (blocks prog s).stackColumn (fun b ↦ lv42Column prog s shape stack (stackOrder prog s)[b])
    (leanIsaμ prog s)

/-- **The public input** the calldata's 32 bytes are: four 64-bit big-endian words, `lanes k` the word `k`
(as `publicWordsOf`, the verifier's own reading). -/
def publicInputOf (bytes : List UInt8) : PublicInput :=
  ⟨fun k ↦ K.ofLane (beWordAt bytes.toArray (8 * k.val))⟩

/-- The sizes of a proof, as Lv42's `Sizes`: the shape's memory (its log-size must be positive) and the proof's
row counts. -/
def sizesOf (shape : UniStatement.Shape) (h : 0 < shape.logMemory) (rows : List ℕ) : Sizes :=
  ⟨shape.logMemory, h, fun j ↦ rows.getD j.val 0⟩

/-! ### The setup's tables -/

/-- Slot `s` of instruction `i`'s bytecode tuple (SPEC.md §3): `SEP_BYTECODE`, the pc `g^i`, a zero (the
count is the prover's), then the instruction's entry (`Lv42.Arithmetization.entry`, slots 3 to 10). -/
def tupleSlot (prog : Program) (i : Fin (2 ^ prog.logSize)) (s : ℕ) : K :=
  if s = 0 then K.ofBits 4
  else if s = 1 then LeanVM.Parameters.gpow i.val
  else if s = 2 then 0
  else if h : s - 3 < 8 then (Lv42.Arithmetization.entry (prog.code i))[s - 3]
  else 0

/-- **The setup stack** (`F`): the bytecode's 16 slots, slot `s` of coefficient `k` at word `s + 16 k`
(the slot is the low four coordinates: the claim's point is `(α, w(t))`), and the memory's addresses
`g^i`, both in basis `B`, at the setup layout's offsets; zero elsewhere. -/
def setupStack (prog : Program) (shape : UniStatement.Shape) : Array K :=
  let layout := setupLayout shape
  let slots : Array (Array K) := Array.ofFn (n := 16) fun s ↦
    bCoefficients prog.logSize (Array.ofFn (n := 2 ^ prog.logSize) fun i ↦ tupleSlot prog i s.val)
  let addresses := bCoefficients shape.logMemory (Array.ofFn (n := 2 ^ shape.logMemory) fun i ↦ LeanVM.Parameters.gpow i.val)
  let (_, _, tupleOffset) := (layout.limbs .bytecodeTuple).headD (0, 0, 0)
  let (_, _, addressOffset) := (layout.limbs .address).headD (0, 0, 0)
  Array.ofFn (n := 2 ^ layout.vars) fun w ↦
    let w := w.val
    if tupleOffset ≤ w ∧ w < tupleOffset + 2 ^ (shape.logBytecode + 4) then
      let j := w - tupleOffset
      (slots.getD (j % 16) #[]).getD (j / 16) 0
    else if addressOffset ≤ w ∧ w < addressOffset + 2 ^ shape.logMemory then
      addresses.getD (w - addressOffset) 0
    else 0

/-- **A matrix of Flock's R1CS as a stack** of `2^28` words: entry `(k, j)` (row `k`, column `j`) at word
`k + 2^14 j`, `1` or `0` (`matrix_values`: the row's 14 coordinates, then the column's). -/
def matrixStack (A : Fin (2 ^ 14) → Fin (2 ^ 14) → Bool) : Array K :=
  Array.ofFn (n := 2 ^ 28) fun w ↦
    if A ⟨w.val % 2 ^ 14, Nat.mod_lt _ (by decide)⟩ ⟨w.val / 2 ^ 14 % 2 ^ 14, Nat.mod_lt _ (by decide)⟩
    then 1 else 0

end UniStatement

end
