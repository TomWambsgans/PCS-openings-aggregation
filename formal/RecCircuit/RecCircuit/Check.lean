-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCircuit.Compile
import RecCircuit.KeccakMath

/-!
# The checker

What the theorems need of a compiled circuit, checked on the circuit, its final view and the compiler's traces, in
compiled code (`compile` runs it after the transcription; it is about as fast as the compiler). A failing check makes
`compile` reject the graph: the checks add no constraint and change no circuit, and the Lean compiler accepts
π1-rec3's graph (`RecCircuitTest`). The theorems never evaluate them: they assume `compile r = .ok c` and use each check
through its lemma (`Sat.lean`, `Sound.lean`).

* **The view** (`viewOk`): each value's chain is linked by `σ` (`σ(ch i) = ch (i + 1)`, both positions, no port), its
  forwards are forwards with `κ = 0`, a produced value's chain starts at its producer; each placed position is in its
  value's chain (past the producer). Then on a satisfied witness every placement of a value carries one word, its
  producer's push (`val`).
* **Gates** (`gate v p k cells`): the value `v` is pushed by a slot whose formula is `p`, whose `κ` is `k`, and whose
  row holds the values `cells` at the cells `p` reads. Then `val v = p(val ∘ cells) + k`.
* **Templates**: every free bit's `b = b²` and copy, every Keccak-f instance's gates by round (`keccakOk`), every
  sponge's blocks (`spongeOk`), every packing's windows (`packOk`), every node's limbs (`nodeOk`), every port's limbs
  (`portsOk`).
-/

namespace RecCircuit

open Primitives PcsCircuit.Builder

/-- `∀ i < n, f i`, as a loop. -/
def allBelow (n : ℕ) (f : ℕ → Bool) : Bool := go 0
where
  go (i : ℕ) : Bool := if i < n then f i && go (i + 1) else true
  termination_by n - i

/-- The dense `κ` column (`kappa_column`). -/
def denseKappa (C : Circuit) : Array K := C.kappa.foldl (fun a e => a.set! e.1 e.2) (Array.replicate C.n 0)

/-- What the checks read: the circuit, its view, its dense `κ`. -/
structure Ctx where
  C : Circuit
  V : View
  kd : Array K

namespace Ctx

variable (X : Ctx)

def n : ℕ := X.C.n
def W : ℕ := X.C.width
def prod (v : ℕ) : ℕ := X.V.producerF.getD v NONE
def cellAt (q : ℕ) : ℕ := X.V.cellF.getD q NONE
def chain (v : ℕ) : Array ℕ := X.V.chains.getD v #[]
def idx (q : ℕ) : ℕ := X.V.idxF.getD q 0
def kap (q : ℕ) : K := X.kd.getD q 0
def rowStart (q : ℕ) : ℕ := X.W * (q / X.W)
def role (v : ℕ) : ℕ := X.prod v % X.W

/-- `σ` takes `a` to `b`, both positions, `a` no port. -/
def link (a b : ℕ) : Bool := a < X.n && b < X.n && X.C.sigmaAt a == b && !(X.C.formulaAt a).isPort

/-- `a` is a forward with no `κ`. -/
def fwd (a : ℕ) : Bool := X.C.formulaAt a == .forward && X.kap a == 0

def chainOk (v : ℕ) : Bool :=
  let ch := X.chain v
  allBelow (ch.size - 1) (fun i => X.link (ch.getD i 0) (ch.getD (i + 1) 0)) &&
    (if X.prod v == NONE then allBelow (ch.size - 1) (fun i => X.fwd (ch.getD i 0))
     else 1 ≤ ch.size && ch.getD 0 0 == X.prod v && allBelow (ch.size - 1) (fun i => i == 0 || X.fwd (ch.getD i 0)))

def placedOk (q : ℕ) : Bool :=
  let v := X.cellAt q
  v == NONE || (X.idx q < (X.chain v).size && (X.chain v).getD (X.idx q) 0 == q && (X.prod v == NONE || 1 ≤ X.idx q))

/-- **The view is the circuit's**: chains linked by `σ`, placements in their chains. -/
def viewOk : Bool :=
  X.kd.size == X.n && X.V.cellF.size == X.n && X.V.chains.size == X.V.producerF.size &&
    allBelow X.V.producerF.size X.chainOk && allBelow X.n X.placedOk

/-- **A gate**: `v` is pushed by a slot of formula `p` and `κ = k`, whose row holds `cells` (cell, value) at the cells
`p` reads. -/
def gate (v : ℕ) (p : Poly) (k : K) (cells : List (ℕ × ℕ)) : Bool :=
  let q := X.prod v
  q != NONE && q < X.n && X.C.formulaAt q == .expr p && X.kap q == k &&
    p.reads.all (fun c => (cells.lookup c).isSome) &&
    cells.all (fun t => t.2 != NONE && X.cellAt (X.rowStart q + t.1) == t.2)

/-! ## The formulas the templates' gates have -/

/-- `1`, as `K(1)`. -/
def one : K := F64.ofU64 1

/-- A spare slot (a constant): `0`. -/
def sparePoly : Poly := ⟨[], []⟩

/-- A free bit's self-loop at role `r`: `c_r²`. -/
def sqPoly (r : ℕ) : Poly := ⟨[], [(r, r, one)]⟩

/-- A copy at role `r`: `c_(r−1)`. -/
def copyPoly (r : ℕ) : Poly := ⟨[(r - 1, one)], []⟩

/-- An XOR or a D unit at role `r`: `c_r + c_(r+1)`. -/
def xorPolyL (r : ℕ) : Poly := ⟨[(r, one), (r + 1, one)], []⟩

/-- `kprep`'s column sum at `base + 5`. -/
def sumPolyL (base : ℕ) : Poly := ⟨(List.range 5).map fun i => (base + i, one), []⟩

/-- `pack-top4` at `base + 4`: `Σ_(i<4) c_(base+i) x^i`. -/
def topPolyL (base : ℕ) : Poly := ⟨(List.range 4).map fun i => (base + i, F64.ofU64 (1 <<< i.toUInt64)), []⟩

/-- `pack` at `base + 15`: `Σ_(i<15) c_(base+i) x^i + c_(base+15) x^15`. -/
def packPolyL (base : ℕ) : Poly := ⟨(List.range 16).map fun i => (base + i, F64.ofU64 (1 <<< i.toUInt64)), []⟩

/-- An `E` unit's limb `l` (`op_polys` with `a` at `base..`, `b` at `base + 3..`). -/
def unitPolyL (op : Op) (base l : ℕ) : Poly :=
  match op with
  | .add => ⟨[(base + l, one), (base + 3 + l, one)], []⟩
  | _ =>
    match l with
    | 0 => ⟨[], [(base, base + 3, one), (base + 1, base + 5, one), (base + 2, base + 4, one)]⟩
    | 1 => ⟨[], [(base, base + 4, one), (base + 1, base + 3, one), (base + 1, base + 5, one), (base + 2, base + 4, one),
        (base + 2, base + 5, one)]⟩
    | _ => ⟨[], [(base, base + 5, one), (base + 1, base + 4, one), (base + 2, base + 3, one), (base + 2, base + 5, one)]⟩

/-! ## Unit checks -/

def constOk (v : ℕ) (k : K) : Bool := X.gate v sparePoly k []

/-- A free bit: its self-loop `b = b²`. -/
def bitOk (v : ℕ) : Bool := X.gate v (sqPoly (X.role v)) 0 [(X.role v, v)]

/-- A copy `c` of a free bit `v`. -/
def copyOk (v c : ℕ) : Bool := 1 ≤ X.role c && X.gate c (copyPoly (X.role c)) 0 [(X.role c - 1, v)]

def xorOk (x a b : ℕ) : Bool := X.gate x (xorPolyL (X.role x)) 0 [(X.role x, a), (X.role x + 1, b)]

/-! ## D16v's Keccak-f -/

/-- The χ row of plane `y`, slice `z`: cells `x'`, `5 + x'` hold θ's inputs at the lane ρ and π bring there. -/
def chiCells (a d : Array Val) (y z : ℕ) : List (ℕ × ℕ) :=
  (List.range 5).flatMap fun x =>
    let l := piInv (x + 5 * y)
    let z0 := (z + 64 - rho l) % 64
    [(x, a.getD (64 * l + z0) NONE), (5 + x, d.getD (64 * (l % 5) + z0) NONE)]

/-- **A Keccak-f instance's gates, round by round.** -/
def keccakOk (t : KeccakT) : Bool :=
  let A := fun j i => (t.a.getD j #[]).getD i NONE
  let Cv := fun j i => (t.c.getD j #[]).getD i NONE
  let D := fun j i => (t.d.getD j #[]).getD i NONE
  let P := fun j y i => ((t.p.getD j #[]).getD y #[]).getD i NONE
  -- C_0: kprep's column sums.
  allBelow 320 (fun u =>
    let (x, z) := (u / 64, u % 64)
    let v := Cv 0 u
    5 ≤ X.role v && X.gate v (sumPolyL (X.role v - 5)) 0
      ((List.range 5).map fun y => (X.role v - 5 + y, A 0 (64 * (x + 5 * y) + z)))) &&
  -- D_j: the D units.
  allBelow 24 (fun j => allBelow 320 (fun u =>
    let (x, z) := (u / 64, u % 64)
    let v := D j u
    X.gate v (xorPolyL (X.role v)) 0
      [(X.role v, Cv j (64 * ((x + 4) % 5) + z)), (X.role v + 1, Cv j (64 * ((x + 1) % 5) + (z + 63) % 64))])) &&
  -- The χ rows: A_(j+1) and the partial sums P_(j, y).
  allBelow 24 (fun j => allBelow 5 (fun y => allBelow 320 (fun u =>
    let (x, z) := (u / 64, u % 64)
    let cells := chiCells (t.a.getD j #[]) (t.d.getD j #[]) y z
    let k := if x == 0 then (if y == 0 then rcBit j z else 0) else 0
    X.gate (A (j + 1) (64 * (x + 5 * y) + z)) (Builder.chiB x).build k cells &&
      (if y == 0 then X.gate (P j 0 u) (Builder.chiB x).build k cells
       else X.gate (P j y u) ((Builder.chiB x).addLinear (10 + x) 1).build 0 (cells ++ [(10 + x, P j (y - 1) u)]))))) &&
  -- C_(j+1) = P_(j, 4).
  allBelow 23 (fun j => allBelow 320 (fun u => Cv (j + 1) u == P j 4 u))

/-! ## Keccak-256's sponge -/

/-- A permutation input bit as made: the value itself, or a constant. -/
def inOk (b : Bit) (x : ℕ) : Bool :=
  match b with
  | .v v => x == v
  | .zero => X.constOk x 0
  | .one => X.constOk x 1

/-- The padded message's bit `i` (`Sponge::keccak256`'s `bit_of`). -/
def padBitOf (msg : Array Bit) (i : ℕ) : Bit :=
  let paddedLen := (msg.size / 1088 + 1) * 1088
  if i < msg.size then msg.getD i .zero else if i == msg.size || i == paddedLen - 1 then .one else .zero

/-- **A sponge's blocks**: block 0's input is the padded message's bits and zeros, a later block's the state before XOR
its bits (passed through for a zero bit, through a fresh one for a one); the digest is the last state's 256 bits. -/
def spongeOk (keccaks : Array KeccakT) (s : SpongeT) : Bool :=
  let blocks := s.message.size / 1088 + 1
  let inst := fun (b : ℕ) => keccaks.getD (s.perms.getD b 0) default
  let inp := fun (b i : ℕ) => ((inst b).a.getD 0 #[]).getD i NONE
  let out := fun (b i : ℕ) => ((inst b).a.getD 24 #[]).getD i NONE
  s.perms.size == blocks && s.perms.all (· < keccaks.size) &&
  allBelow 1600 (fun i => X.inOk (if i < 1088 then padBitOf s.message i else .zero) (inp 0 i)) &&
  allBelow blocks (fun b => b == 0 || allBelow 1600 (fun i =>
    let x := inp b i
    let prev := out (b - 1) i
    if 1088 ≤ i then x == prev
    else match padBitOf s.message (b * 1088 + i) with
      | .zero => x == prev
      | .v u => X.xorOk x prev u
      | .one =>
        let o := X.cellAt (X.rowStart (X.prod x) + X.role x + 1)
        X.xorOk x prev o && X.constOk o 1)) &&
  s.digest.size == 256 && allBelow 256 (fun k => s.digest.getD k NONE == out (blocks - 1) k)

/-! ## Packings -/

/-- The packing's top exponent, its window, and how many bits it reads there. -/
def packTopE (pk : PackT) : ℕ := pk.bits.foldl (fun m t => max m t.1) 0

/-- A window's width: the top window is `pack-top4`'s 4 bits when they hold its exponents, else 15. -/
def packKOf (topE t : ℕ) : ℕ := if t == topE / 15 && topE - 15 * (topE / 15) + 1 ≤ 4 then 4 else 15

/-- A window's cells, as its slot's gate reads them. -/
def windowCells (base : ℕ) (cells : Array ℕ) (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).map fun i => (base + i, cells.getD i NONE)

/-- **A packing's window `t'` from the top** (`t = tTop − t'`): its cells the bits at its exponents or a zero constant;
a `pack-top4` slot (no accumulator) or a `pack` slot of the accumulator before (a fresh zero for a wide top window). -/
def windowOk (pk : PackT) (t' : ℕ) : Bool :=
  let topE := packTopE pk
  let t := topE / 15 - t'
  let wd := pk.windows.getD t' default
  let k := packKOf topE t
  wd.1.size == k &&
    allBelow k (fun i => match pk.bits.lookup (15 * t + i) with
      | some u => wd.1.getD i NONE == u
      | none => X.constOk (wd.1.getD i NONE) 0) &&
    (if t' == 0 && k == 4 then
      wd.2.1.isNone && 4 ≤ X.role wd.2.2 && X.gate wd.2.2 (topPolyL (X.role wd.2.2 - 4)) 0 (windowCells (X.role wd.2.2 - 4) wd.1 4)
     else match wd.2.1 with
      | none => false
      | some a =>
        (if t' == 0 then X.constOk a 0 else a == (pk.windows.getD (t' - 1) default).2.2) && 15 ≤ X.role wd.2.2 &&
          X.gate wd.2.2 (packPolyL (X.role wd.2.2 - 15)) 0 (windowCells (X.role wd.2.2 - 15) wd.1 15 ++ [(X.role wd.2.2, a)]))

/-- **A packing's windows**, from the top (`windowOk`), and its output the last window's. -/
def packOk (pk : PackT) : Bool :=
  !pk.bits.isEmpty && pk.bits.all (fun t => t.1 < 64 && t.2 != NONE) && (pk.bits.map (·.1)).Nodup &&
  pk.windows.size == packTopE pk / 15 + 1 &&
  allBelow (packTopE pk / 15 + 1) (X.windowOk pk) &&
  pk.out == (pk.windows.getD (packTopE pk / 15) default).2.2

end Ctx

/-! ## Nodes, ports, and the checked compiler -/

namespace Compiled

variable (c : Compiled)

def ctx : Ctx := ⟨c.circuit, c.view, denseKappa c.circuit⟩

/-- Each value's packing trace, by its output. -/
def packOf : Array (Option ℕ) := Id.run do
  let mut a : Array (Option ℕ) := Array.replicate c.view.producerF.size none
  for t in [0:c.st.packs.size] do
    a := a.set! (c.st.packs.getD t default).out (some t)
  return a

/-- `u` is the output of a packing of `bits`. -/
def packIs (packOf : Array (Option ℕ)) (u : ℕ) (bits : List (ℕ × ℕ)) : Bool :=
  match packOf.getD u none with
  | some t => (c.st.packs.getD t default).out == u && (c.st.packs.getD t default).bits == bits
  | none => false

def streamBit (i : ℕ) : ℕ := (c.bitSelf.getD i none).getD NONE

def limbsOf (id : ℕ) : Array ℕ := (c.limbs.getD id none).getD #[]

/-- The message a hash node's sponge absorbs: the state's digest values, then the stream's bits `f..t` (a first
block's through their copies). -/
def hashMessage (s f t : ℕ) : Array Bit := Id.run do
  let mut m : Array Bit := ((c.digests.getD s none).getD #[]).map Bit.v
  for i in [f:t] do
    for j in [0:8] do
      let k := 8 * i + j
      m := m.push (.v ((c.bitCopy.getD k none).getD (c.streamBit k)))
  return m

def seedMessage (iv : List UInt8) : Array Bit :=
  Builder.constantBits NAME ++ Builder.constantBits iv ++ c.publicCopy.map Bit.v

/-- A digest is a sponge's of this message. -/
def spongeIs (d : Array ℕ) (m : Array Bit) : Bool := c.st.sponges.any fun s => s.digest == d && s.message == m

/-- An `E` unit computes `out = op(lx, ly)`: its slots are `unitPolyL`'s at a base (ended: slots at the base,
forwarded: at base + 6), its cells `a`, `b` the operands (either order). -/
def arithOk (X : Ctx) (op : Op) (out lx ly : Array ℕ) : Bool :=
  let r := X.role (out.getD 0 NONE)
  let q := X.prod (out.getD 0 NONE)
  let try_ := fun (slots : ℕ) =>
    slots ≤ r &&
      (let base := r - slots
       let A := (List.range 3).map fun i => X.cellAt (X.rowStart q + base + i)
       let B := (List.range 3).map fun i => X.cellAt (X.rowStart q + base + 3 + i)
       let cells := (List.range 3).map (fun i => (base + i, A.getD i NONE)) ++
         (List.range 3).map (fun i => (base + 3 + i, B.getD i NONE))
       let opP := if op == .add then Op.add else Op.mul
       (List.range 3).all (fun l => X.gate (out.getD l NONE) (Ctx.unitPolyL opP base l) 0 cells &&
         X.rowStart (X.prod (out.getD l NONE)) == X.rowStart q) &&
       (if op == .square then A == lx.toList && B == lx.toList
        else (A == lx.toList && B == ly.toList) || (A == ly.toList && B == lx.toList)))
  out.size == 3 && lx.size == 3 && ly.size == 3 && (try_ 0 || try_ 6)

/-- **A live node's limbs or digest.** -/
def nodeOk (X : Ctx) (iv : List UInt8) (packOf : Array (Option ℕ)) (id : ℕ) : Bool :=
  let l := c.limbsOf id
  let L := fun (i : ℕ) => l.getD i NONE
  let pk := fun (u : ℕ) (bits : List (ℕ × ℕ)) => c.packIs packOf u bits
  let sb := c.streamBit
  match c.nodes.getD id default with
  | .const c0 c1 c2 =>
    l.size == 3 && X.constOk (L 0) (F64.ofU64 c0) && X.constOk (L 1) (F64.ofU64 c1) && X.constOk (L 2) (F64.ofU64 c2)
  | .statement k =>
    k < 4 && l.size == 3 && L 0 == c.statementLimb.getD k NONE && X.constOk (L 1) 0 && X.constOk (L 2) 0
  | .input off len =>
    l.size == 3 &&
    (if c.freeReads.any (fun e => e.1 == off && e.2 == l) then len == 24
     else (List.range (8 * len)).all (fun k => (c.bitSelf.getD (8 * off + k) none).isSome) &&
      (if len == 24 then pk (L 0) (beBits sb (off + 16) 8) && pk (L 1) (beBits sb (off + 8) 8) && pk (L 2) (beBits sb off 8)
       else if len == 16 then pk (L 0) (beBits sb (off + 8) 8) && pk (L 1) (beBits sb off 8) && X.constOk (L 2) 0
       else len ≤ 8 && pk (L 0) (beBits sb off len) && X.constOk (L 1) 0 && X.constOk (L 2) 0))
  | .low h =>
    let d := (c.digests.getD h none).getD #[]
    let db := fun i => d.getD i NONE
    d.size == 256 && l.size == 3 && pk (L 0) (beBits db 24 8) && pk (L 1) (beBits db 16 8) && pk (L 2) (beBits db 8 8)
  | .narrow h =>
    let d := (c.digests.getD h none).getD #[]
    let db := fun i => d.getD i NONE
    d.size == 256 && l.size == 3 && pk (L 0) (beBits db 24 8) && pk (L 1) (beBits db 16 8) && pk (L 2) (beBits db 12 4)
  | .bits v shift width =>
    match c.nodes.getD v default with
    | .input off len =>
      let field := (beBits sb off len).filterMap fun (e, x) =>
        if shift ≤ e && e < shift + width then some (e - shift, x) else none
      len ≤ 8 && l.size == 3 && X.constOk (L 1) 0 && X.constOk (L 2) 0 &&
      (List.range (8 * len)).all (fun k => (c.bitSelf.getD (8 * off + k) none).isSome) &&
      (match field with
       | [] => X.constOk (L 0) 0
       | [(0, x)] => L 0 == x
       | _ => pk (L 0) field)
    | _ => false
  | .add x y => arithOk X .add l (c.limbsOf x) (c.limbsOf y)
  | .mul x y => arithOk X (if x == y then .square else .mul) l (c.limbsOf x) (c.limbsOf y)
  | .seed =>
    match c.digests.getD id none with
    | some d => d.size == 256 && c.spongeIs d (c.seedMessage iv)
    | none => false
  | .hash s f t =>
    match c.digests.getD id none with
    | some d => d.size == 256 && (c.digests.getD s none).isSome && f ≤ t &&
      (List.range (8 * (t - f))).all (fun k => (c.bitSelf.getD (8 * f + k) none).isSome) &&
      c.spongeIs d (c.hashMessage s f t)
    | none => false
  | .ringWeight .. => false

/-- The zero checks that are not constants, in order: the zero ports'. -/
def zeroNodes : List ℕ := c.zero.filter fun id => match c.nodes.getD id default with
  | .const .. => false
  | _ => true

/-- A port's limb values, by its source (the `m`-th zero port the `m`-th non-constant zero check's). -/
def portValues (X : Ctx) (J : ℕ) : Array ℕ :=
  let p := c.circuit.ports.getD J default
  match p.source with
  | .statement => c.statementLimb
  | .root i => c.rootLimbs.getD i #[]
  | .element e => c.limbsOf (c.elementNodes.getD e 0)
  | .zero =>
    let m := ((c.circuit.ports.toList.take J).filter fun p => p.source == .zero).length
    c.limbsOf (c.zeroNodes.getD m 0)
  | .pad =>
    (List.range 3).toArray.map fun l => X.cellAt (X.rowStart p.position + l)

/-- **Every port's limbs**: its row's cells `0..L` hold its source's values. -/
def portsOk (X : Ctx) : Bool :=
  (c.circuit.ports.toList.filter fun p => p.source == .zero).length == c.zeroNodes.length &&
  allBelow c.circuit.ports.size fun J =>
    let p := c.circuit.ports.getD J default
    let vs := c.portValues X J
    let L := p.source.limbs
    p.position < X.n && X.C.formulaAt p.position == .port (List.range L) && vs.size == L &&
      allBelow L (fun l => vs.getD l NONE != NONE && X.cellAt (X.rowStart p.position + l) == vs.getD l NONE) &&
      (p.source != .pad || allBelow 3 (fun l => X.constOk (vs.getD l NONE) 0))

/-- The roots' packings: limb `l` the little-endian word of the stream's bytes `at + [16, 24, 0, 8][l]`. -/
def rootsOk (rootsAt : List ℕ) (packOf : Array (Option ℕ)) : Bool :=
  c.rootLimbs.size == rootsAt.length &&
  allBelow rootsAt.length fun i =>
    let at_ := rootsAt.getD i 0
    let rl := c.rootLimbs.getD i #[]
    rl.size == 4 && (List.range 256).all (fun k => (c.bitSelf.getD (8 * at_ + k) none).isSome) &&
      allBelow 4 fun l => c.packIs packOf (rl.getD l NONE) (leBits c.streamBit (at_ + [16, 24, 0, 8].getD l 0) 8)

/-- The free bits: every stream and public-input bit a self-loop, every copy a copy. -/
def bitsOk (X : Ctx) : Bool :=
  allBelow c.bitSelf.size (fun k => match c.bitSelf.getD k none with
    | some v => X.bitOk v && (match c.bitCopy.getD k none with
      | some cp => X.copyOk v cp
      | none => true)
    | none => (c.bitCopy.getD k none).isNone) &&
  c.bitCopy.size == c.bitSelf.size &&
  c.publicSelf.size == 256 && c.publicCopy.size == 256 &&
  allBelow 256 (fun k => X.bitOk (c.publicSelf.getD k NONE) && X.copyOk (c.publicSelf.getD k NONE) (c.publicCopy.getD k NONE))

/-- The statement's limbs: limb `k` the big-endian word of the public input's bytes `8k..8k+8`. -/
def statementOk (packOf : Array (Option ℕ)) : Bool :=
  c.statementLimb.size == 4 &&
  allBelow 4 fun k => c.packIs packOf (c.statementLimb.getD k NONE) (beBits (fun i => c.publicSelf.getD i NONE) (8 * k) 8)

/-- The never-hashed reads are disjoint 24-byte reads. -/
def freeReadsOk : Bool :=
  c.freeReads.all (fun e => e.2.size == 3) &&
  allBelow c.freeReads.size fun a => allBelow c.freeReads.size fun b =>
    a == b || (c.freeReads.getD a default).1 + 24 ≤ (c.freeReads.getD b default).1 ||
      (c.freeReads.getD b default).1 + 24 ≤ (c.freeReads.getD a default).1

/-- **Everything the theorems need**, checked. -/
def checks (r : Recorded) : List (String × Bool) :=
  let X := c.ctx
  let packOf := c.packOf
  [("view", X.viewOk),
   ("keccak", c.st.keccaks.all X.keccakOk),
   ("sponge", c.st.sponges.all (X.spongeOk c.st.keccaks)),
   ("pack", c.st.packs.all X.packOk),
   ("bits", c.bitsOk X),
   ("statement", c.statementOk packOf),
   ("roots", c.rootsOk r.rootsAt packOf),
   ("free reads", c.freeReadsOk),
   ("nodes", allBelow c.nodes.size fun id => !c.live.getD id false || c.nodeOk X r.iv packOf id),
   ("ports", c.portsOk X),
   ("sizes", c.live.size == c.nodes.size && c.limbs.size == c.nodes.size && c.digests.size == c.nodes.size &&
      c.bitSelf.size == 8 * r.graph.streamLen && c.circuit.logWidth == 4 && c.circuit.logWidth ≤ c.circuit.logN)]

end Compiled

/-- **The compiler** (`compile.rs`, D16v), with the checker: π1's recorded verifier to π2's circuit, or why it is
rejected. -/
def compile (r : Recorded) : Except String Compiled := do
  let c ← compileRaw r
  match (c.checks r).find? (fun t => !t.2) with
  | some (name, _) => throw s!"the checker rejects the circuit: {name}"
  | none => return c

/-! ## The stream and the public input the witness encodes -/

namespace Compiled

variable (c : Compiled)

/-- A free bit's word as a bit. -/
def bitOfWord (x : K) : ℕ := if x = 1 then 1 else 0

/-- **The public input the witness's free bits encode.** -/
def decodePublic (val : ℕ → K) : List UInt8 :=
  (List.range 32).map fun i =>
    ((List.range 8).foldl (fun acc j => acc + 2 ^ j * bitOfWord (val (c.publicSelf.getD (8 * i + j) NONE))) 0).toUInt8

/-- **The stream the witness encodes**: a hashed byte from its free bits, a byte of a never-hashed read from its free
limbs (big-endian `c2 ‖ c1 ‖ c0`), any other byte 0. -/
def decodeStream (streamLen : ℕ) (val : ℕ → K) : List UInt8 :=
  (List.range streamLen).map fun i =>
    if (c.bitSelf.getD (8 * i) none).isSome then
      ((List.range 8).foldl (fun acc j => acc + 2 ^ j * bitOfWord (val (c.streamBit (8 * i + j)))) 0).toUInt8
    else match c.freeReads.find? (fun e => e.1 ≤ i && i < e.1 + 24) with
      | some (off, ls) =>
        let k := i - off
        let limb := F64.toU64 (val (ls.getD (2 - k / 8) NONE))
        (limb.toNat / 2 ^ (8 * (7 - k % 8)) % 256).toUInt8
      | none => 0

end Compiled

end RecCircuit
