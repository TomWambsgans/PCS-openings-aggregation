-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Transcribed from `crates/leanvm_rec/src/circuit/keccak.rs`
-- (`Constants`, `Xors`, `Sponge`), `keccak16.rs` (`D16`) and `units.rs` (`Bools`, `Packer`, `Arith`, `Ports`). The round
-- constants, rotations and lane permutation are Keccak's (FIPS 202): leanerVM's `keccakRC`, `formal/Circuit`'s
-- `rho` and `PI` = leanerVM's `keccakPi`.
import RecCircuit.Layout
import Circuit.Defs

/-!
# The units (`keccak.rs`, `keccak16.rs`, `units.rs`)

Every unit kind of D16v's circuit, as the Rust lays it out, in the builder's monad: constants in spare slots,
Keccak-256's sponge over D16v's Keccak-f (`k0`, `k1`, `kd`, `kprep` and the pool of D units), free bits, packings
(Horner by 15-bit windows), `E` units on `K`-limbs, ports. The traces the checker reads are recorded on the way: each
Keccak-f instance's values by round (`KeccakT`), each sponge call (`SpongeT`), each packing (`PackT`).
-/

namespace RecCircuit

open Primitives PcsCircuit.Builder LeanVM.Parameters

namespace Builder

/-! ## Constants (`keccak::Constants`) -/

/-- A spare role: an expression slot pushing 0, which a constant may take (`κ`) or which stays dead. -/
def spare : Formula := .expr ⟨[], []⟩

/-- Offer a spare role. -/
def offer (row role : ℕ) : BM Unit := modify fun s => { s with spare := s.spare.push (row, role) }

/-- A new value of word `k` (`Constants::fresh`): a spare slot, else a role of the `const` region's rows. -/
def fresh (k : K) : BM Val := do
  modify fun s => { s with constMade := s.constMade + 1 }
  let s ← get
  let (row, role) ← match s.spare.back? with
    | some slot =>
      modify fun s => { s with spare := s.spare.pop }
      pure slot
    | none => do
      let u ← match s.constUnits with
        | some u => pure u
        | none => do
          let w ← width
          let r ← region "const" (Array.replicate w spare)
          pure (Units.new r 1 w)
      let (u, row, role) ← u.next
      modify fun s => { s with constUnits := some u }
      if role == 0 then modify fun s => { s with constOwnRows := s.constOwnRows + 1 }
      pure (row, role)
  setKappa row role k
  produce row role

/-! ## XOR units (`keccak::Xors`) -/

/-- The `xor` region's formula at role `2u`: `c_(2u) + c_(2u+1)`. -/
def xorPoly (r : ℕ) : Poly := ((PolyBuilder.mk []).linear r 1 |>.linear (r + 1) 1).build

def xorRoles (w : ℕ) : Array Formula :=
  (List.range w).toArray.map fun c => if c % 2 == 0 then .expr (xorPoly c) else .forward

def initXors : BM Unit := do
  let w ← width
  let r ← region "xor" (xorRoles w)
  modify fun s => { s with xorUnits := Units.new r 2 (w / 2) }

/-- `a ⊕ b`: `a` ends here, `b` is forwarded (`Xors::xor`). -/
def xor (a b : Val) : BM Val := do
  let (u, row, base) ← (← get).xorUnits.next
  modify fun s => { s with xorUnits := u }
  place row base a
  place row (base + 1) b
  produce row base

/-! ## D16v's Keccak-f (`keccak16::D16`) -/

/-- `PI`: where π sends lane `x + 5y`. -/
def PI (i : ℕ) : ℕ := keccakPi i

/-- `χ_(x')` on a χ row's cells, `b_i = c_i + c_(5+i)` (`keccak16::chi`). -/
def chiB (x : ℕ) : PolyBuilder := Id.run do
  let (x1, x2) := ((x + 1) % 5, (x + 2) % 5)
  let mut p := (PolyBuilder.mk []).linear x 1 |>.linear (5 + x) 1 |>.linear x2 1 |>.linear (5 + x2) 1
  for a in [x1, 5 + x1] do
    for c in [x2, 5 + x2] do
      p := p.addQuadratic a c 1
  return p

/-- A D unit's slot at `s`: `c_s + c_(s+1)`. -/
def dUnit (s : ℕ) : Formula := .expr ((PolyBuilder.mk []).linear s 1 |>.linear (s + 1) 1).build

def k0Roles : Array Formula := Id.run do
  let mut r := forwards 16
  for x in [0:5] do
    r := r.set! x (.expr (chiB x).build)
    r := r.set! (5 + x) (.expr (chiB x).build)
  for u in [0:3] do
    r := r.set! (10 + 2 * u) (dUnit (10 + 2 * u))
  return r

def k1Roles : Array Formula := Id.run do
  let mut r := forwards 16
  for x in [0:5] do
    r := r.set! x (.expr (chiB x).build)
    r := r.set! (10 + x) (.expr ((chiB x).addLinear (10 + x) 1).build)
  r := r.set! 15 spare
  return r

def kdRoles : Array Formula := Id.run do
  let mut r := forwards 16
  for u in [0:8] do
    r := r.set! (2 * u) (dUnit (2 * u))
  return r

/-- `kprep`'s column-sum slot at `base + 5`: `Σ_(i<5) c_(base+i)`. -/
def sumPoly (base : ℕ) : Poly := Id.run do
  let mut p := PolyBuilder.mk []
  for i in [0:5] do
    p := p.addLinear (base + i) 1
  return p.build

def kprepRoles : Array Formula := Id.run do
  let mut r := forwards 16
  for u in [0:2] do
    r := r.set! (6 * u + 5) (.expr (sumPoly (6 * u)))
  r := r.set! 12 (dUnit 12)
  r := r.set! 14 (dUnit 14)
  return r

def initD16 : BM Unit := do
  need ((← width) == 16) "D16v's rows are 16 positions"
  let k0 ← region "keccak16/k0" k0Roles
  let k1 ← region "keccak16/k1" k1Roles
  let kd ← region "keccak16/kd" kdRoles
  let kprep ← region "keccak16/kprep" kprepRoles
  modify fun s => { s with k0, k1, kd, kprep }

def poolPush (unit : ℕ × ℕ) : BM Unit := modify fun s => { s with pool := s.pool.push unit }

def poolPop : BM (Option (ℕ × ℕ)) := do
  let s ← get
  if s.poolHead < s.pool.size then
    modify fun s => { s with poolHead := s.poolHead + 1 }
    return some (s.pool.getD s.poolHead (0, 0))
  else return none

/-- A round's rows (`D16::round_rows`): 64 `k0` (their D units to the pool), 4 × 64 `k1` (their spare role to the
constants). -/
def roundRows : BM (Array ℕ × Array (Array ℕ)) := do
  let s ← get
  let mut k0 : Array ℕ := #[]
  for _ in [0:64] do k0 := k0.push (← row s.k0)
  let mut k1 : Array (Array ℕ) := #[]
  for _ in [1:5] do
    let mut plane : Array ℕ := #[]
    for _ in [0:64] do plane := plane.push (← row s.k1)
    k1 := k1.push plane
  for r in k0 do
    for u in [0:3] do poolPush (r, 10 + 2 * u)
  for plane in k1 do
    for r in plane do offer r 15
  return (k0, k1)

/-- `D[x][z] = C[x−1][z] + C[x+1][z−1]` for every `(x, z)`, in units from the pool (`D16::d`). -/
def dMix (c : Array Val) : BM (Array Val) := do
  let mut d : Array Val := Array.replicate 320 0
  for x in [0:5] do
    for z in [0:64] do
      let (r, slot) ← match ← poolPop with
        | some unit => pure unit
        | none => do
          let r ← row (← get).kd
          for u in [1:8] do poolPush (r, 2 * u)
          pure (r, 0)
      place r slot (c.getD (64 * ((x + 4) % 5) + z) 0)
      place r (slot + 1) (c.getD (64 * ((x + 1) % 5) + (z + 63) % 64) 0)
      d := d.set! (64 * x + z) (← produce r slot)
  return d

/-- **D16v's Keccak-f of `input`** (`D16::permute`): its output's 1600 values; its trace is pushed to `keccaks`. -/
def permute (input : Array Bit) : BM (Array Val) := do
  need (input.size == 1600) "a permutation's input is 1600 bits"
  let mut rounds : Array (Array ℕ × Array (Array ℕ)) := #[]
  for _ in [0:24] do rounds := rounds.push (← roundRows)
  let mut a : Array Val := #[]
  for x in input do
    a := a.push (← match x with
      | .v v => pure v
      | .zero => fresh 0
      | .one => fresh 1)
  let mut trA : Array (Array Val) := #[a]
  -- C_0: two column sums a kprep row, and its two D units into the pool.
  let mut c : Array Val := Array.replicate 320 0
  let mut r := 0
  for u in [0:320] do
    let (x, z) := (u % 5, u / 5)
    if u % 2 == 0 then
      r ← row (← get).kprep
      poolPush (r, 12)
      poolPush (r, 14)
    let base := 6 * (u % 2)
    for y in [0:5] do
      place r (base + y) (a.getD (64 * (x + 5 * y) + z) 0)
    c := c.set! (64 * x + z) (← produce r (base + 5))
  let mut trC : Array (Array Val) := #[c]
  let mut d ← dMix c
  let mut trD : Array (Array Val) := #[d]
  let mut trP : Array (Array (Array Val)) := #[]
  for j in [0:24] do
    let rc := keccakRC.getD j 0
    let (k0, k1) := rounds.getD j default
    let rowOf := fun (plane z : ℕ) => if plane == 0 then k0.getD z 0 else (k1.getD (plane - 1) #[]).getD z 0
    for l in [0:25] do
      let (xp, yp) := (PI l % 5, PI l / 5)
      for z in [0:64] do
        let rw := rowOf yp ((z + rho l) % 64)
        place rw xp (a.getD (64 * l + z) 0)
        place rw (5 + xp) (d.getD (64 * (l % 5) + z) 0)
    let mut out : Array Val := Array.replicate 1600 0
    let mut p : Array Val := Array.replicate 320 0
    for z in [0:64] do
      let rw := k0.getD z 0
      if rc >>> z.toUInt64 &&& 1 == 1 then
        setKappa rw 0 1
        setKappa rw 5 1
      for x in [0:5] do
        out := out.set! (64 * x + z) (← produce rw x)
        p := p.set! (64 * x + z) (← produce rw (5 + x))
    let mut planes : Array (Array Val) := #[p]
    for yp in [1:5] do
      for z in [0:64] do
        let rw := (k1.getD (yp - 1) #[]).getD z 0
        for x in [0:5] do
          place rw (10 + x) (p.getD (64 * x + z) 0)
        for x in [0:5] do
          out := out.set! (64 * (x + 5 * yp) + z) (← produce rw x)
          p := p.set! (64 * x + z) (← produce rw (10 + x))
      planes := planes.push p
    trP := trP.push planes
    a := out
    trA := trA.push a
    if j < 23 then
      c := p
      trC := trC.push c
      d ← dMix c
      trD := trD.push d
  modify fun s => { s with keccaks := s.keccaks.push ⟨trA, trC, trD, trP⟩ }
  return a

/-! ## Keccak-256's sponge (`keccak::Sponge`) -/

def RATE_BITS : ℕ := 1088

/-- Keccak-256 of `message` (bits in byte order, low bit first): the digest's 256 values (`Sponge::keccak256`). -/
def keccak256 (message : Array Bit) : BM (Array Val) := do
  need (message.size % 8 == 0) "whole bytes"
  let blocks := message.size / RATE_BITS + 1
  let paddedLen := blocks * RATE_BITS
  let bitOf := fun (i : ℕ) => if i < message.size then message.getD i .zero
    else if i == message.size || i == paddedLen - 1 then Bit.one else Bit.zero
  let mut state : Array Val := #[]
  let mut perms : Array ℕ := #[]
  let mut inputs : Array (Array Bit) := #[]
  for block in [0:blocks] do
    let mut input : Array Bit := Array.replicate 1600 .zero
    for i in [0:RATE_BITS] do
      let bit := bitOf (block * RATE_BITS + i)
      if block == 0 then
        input := input.set! i bit
      else
        let x ← match bit with
          | .v v => xor (state.getD i 0) v
          | .zero => pure (state.getD i 0)
          | .one => do
            let one ← fresh 1
            xor (state.getD i 0) one
        input := input.set! i (.v x)
    if block > 0 then
      for i in [RATE_BITS:1600] do
        input := input.set! i (.v (state.getD i 0))
    inputs := inputs.push input
    perms := perms.push (← get).keccaks.size
    state ← permute input
    modify fun s => { s with permutations := s.permutations + 1 }
  let digest := state.extract 0 256
  modify fun s => { s with sponges := s.sponges.push ⟨message, perms, inputs, digest⟩ }
  return digest

/-! ## Free bits (`units::Bools`) -/

def bitRoles (w : ℕ) : Array Formula := (List.range w).toArray.map fun c =>
  if c % 2 == 0 then .expr ((PolyBuilder.mk []).quadratic c c 1).build
  else .expr ((PolyBuilder.mk []).linear (c - 1) 1).build

def initBools : BM Unit := do
  let w ← width
  let r ← region "bit+copy" (bitRoles w)
  modify fun s => { s with bitUnits := Units.new r 2 (w / 2) }

/-- A free bit and a copy of it: `(b, b')` (`Bools::bit_and_copy`). -/
def bitAndCopy : BM (Val × Val) := do
  let (u, r, role) ← (← get).bitUnits.next
  modify fun s => { s with bitUnits := u }
  let v ← produce r role
  place r role v
  let c ← produce r (role + 1)
  return (v, c)

/-! ## Packings (`units::Packer`) -/

def TOP : ℕ := 4
def WINDOW : ℕ := 15

/-- `pack`'s accumulator slot at `base + 15`: `acc·x^15 + Σ_(i<15) c_(base+i) x^i`. -/
def packPoly (base : ℕ) : Poly := Id.run do
  let mut p := (PolyBuilder.mk []).linear (base + 15) ((1 : UInt64) <<< 15)
  for i in [0:15] do
    p := p.addLinear (base + i) (1 <<< i.toUInt64)
  return p.build

/-- `pack-top4`'s slot at `base + 4`: `Σ_(i<4) c_(base+i) x^i`. -/
def topPoly (base : ℕ) : Poly := Id.run do
  let mut p := PolyBuilder.mk []
  for i in [0:4] do
    p := p.addLinear (base + i) (1 <<< i.toUInt64)
  return p.build

def packRoles (w : ℕ) : Array Formula := Id.run do
  let mut r := forwards w
  for u in [0:w / 16] do
    r := r.set! (16 * u + 15) (.expr (packPoly (16 * u)))
  return r

def topRoles (w : ℕ) : Array Formula := Id.run do
  let mut r := forwards w
  for u in [0:w / 5] do
    r := r.set! (5 * u + 4) (.expr (topPoly (5 * u)))
  return r

def initPacker : BM Unit := do
  let w ← width
  let next ← region "pack" (packRoles w)
  let top ← region "pack-top4" (topRoles w)
  modify fun s => { s with packTop := Units.new top 5 (w / 5), packNext := Units.new next 16 (w / 16) }

/-- `Σ b x^e` over `(e, b)`, exponents distinct and below 64 (`Packer::pack`); its trace is pushed to `packs`. -/
def pack (bits : List (ℕ × Val)) : BM Val := do
  need (!bits.isEmpty) "a packing of no bit"
  let mut at_ : Array (Option Val) := Array.replicate 64 none
  for (e, v) in bits do
    need (e < 64 && (at_.getD e none).isNone) "distinct exponents below 64"
    at_ := at_.set! e (some v)
  let topE := bits.foldl (fun m t => max m t.1) 0
  let tTop := topE / WINDOW
  let topK := topE - WINDOW * tTop + 1
  let kOf := fun (t : ℕ) => if t == tTop && topK ≤ TOP then TOP else WINDOW
  let absent := (List.range (tTop + 1)).any fun t => (List.range (kOf t)).any fun i => (at_.getD (WINDOW * t + i) none).isNone
  if absent && (← get).packZero.isNone then
    let z ← fresh 0
    modify fun s => { s with packZero := some z }
  let mut acc : Option Val := none
  let mut windows : Array (Array Val × Option Val × Val) := #[]
  for t' in [0:tTop + 1] do
    let t := tTop - t'
    let lo := WINDOW * t
    let k := kOf t
    let zero := (← get).packZero
    let mut cells : Array Val := #[]
    for i in [0:k] do
      match (at_.getD (lo + i) none).orElse fun _ => zero with
      | some v => cells := cells.push v
      | none => throw "a zero when a bit is absent"
    let (r, base, accRole, accIn) ← match acc with
      | none =>
        if k == TOP then do
          let (u, r, base) ← (← get).packTop.next
          modify fun s => { s with packTop := u }
          pure (r, base, base + TOP, none)
        else do
          let (u, r, base) ← (← get).packNext.next
          modify fun s => { s with packNext := u }
          let z ← fresh 0
          place r (base + 15) z
          pure (r, base, base + 15, some z)
      | some prev => do
        let (u, r, base) ← (← get).packNext.next
        modify fun s => { s with packNext := u }
        place r (base + 15) prev
        pure (r, base, base + 15, some prev)
    for i in [0:cells.size] do
      place r (base + i) (cells.getD i 0)
    let out ← produce r accRole
    windows := windows.push (cells, accIn, out)
    acc := some out
  match acc with
  | some out =>
    modify fun s => { s with packs := s.packs.push ⟨bits, windows, out⟩ }
    return out
  | none => throw "a window"

/-! ## `E` units (`units::Arith`) -/

/-- The limbs of `a·b`, `a + b`, `a²` as polynomials of the cells `a` at `ra`, `b` at `rb` (`op_polys`). -/
def opPolys (op : Op) (ra rb : Array ℕ) : Array PolyBuilder := Id.run do
  let q := fun (p : PolyBuilder) (i j : ℕ) => p.addQuadratic (ra.getD i 0) (rb.getD j 0) 1
  let mut c : Array PolyBuilder := #[default, default, default]
  match op with
  | .add =>
    for l in [0:3] do
      c := c.modify l fun p => (p.addLinear (ra.getD l 0) 1).addLinear (rb.getD l 0) 1
  | .mul =>
    for (i, j) in [(0, 0), (1, 2), (2, 1)] do c := c.modify 0 (q · i j)
    for (i, j) in [(0, 1), (1, 0), (1, 2), (2, 1), (2, 2)] do c := c.modify 1 (q · i j)
    for (i, j) in [(0, 2), (1, 1), (2, 0), (2, 2)] do c := c.modify 2 (q · i j)
  | .square =>
    c := c.modify 0 fun p => p.addQuadratic (ra.getD 0 0) (ra.getD 0 0) 1
    c := c.modify 1 fun p => p.addQuadratic (ra.getD 2 0) (ra.getD 2 0) 1
    c := c.modify 2 fun p => (p.addQuadratic (ra.getD 1 0) (ra.getD 1 0) 1).addQuadratic (ra.getD 2 0) (ra.getD 2 0) 1
  return c

/-- An `E` unit's three slots at `base + slots + l`, reading `a` at `base..base+3` and `b` at `base+3..base+6`. -/
def unitPolys (op : Op) (base : ℕ) : Array Poly :=
  (opPolys op #[base, base + 1, base + 2] #[base + 3, base + 4, base + 5]).map PolyBuilder.build

def endedRoles (op : Op) (w : ℕ) : Array Formula := Id.run do
  let mut r := forwards w
  for u in [0:w / 6] do
    let ps := unitPolys op (6 * u)
    for l in [0:3] do
      r := r.set! (6 * u + l) (.expr (ps.getD l default))
  return r

def forwardedRoles (op : Op) (w : ℕ) : Array Formula := Id.run do
  let mut r := forwards w
  for u in [0:w / 9] do
    let ps := unitPolys op (9 * u)
    for l in [0:3] do
      r := r.set! (9 * u + 6 + l) (.expr (ps.getD l default))
  return r

def initArith : BM Unit := do
  let w ← width
  let em ← region "e-mul" (endedRoles .mul w)
  let ea ← region "e-add" (endedRoles .add w)
  let fm ← region "e-mul-fwd" (forwardedRoles .mul w)
  let fa ← region "e-add-fwd" (forwardedRoles .add w)
  modify fun s => { s with
    ended := #[Units.new em 6 (w / 6), Units.new ea 6 (w / 6)]
    forwarded := #[Units.new fm 9 (w / 9), Units.new fa 9 (w / 9)] }

def opIndex : Op → ℕ
  | .mul => 0
  | .add => 1
  | .square => 2

/-- `op(a, b)` (`b` ignored for a square, which is `a·a`); with `endA`, `a`'s limbs end here (`Arith::op`). -/
def arith (op : Op) (a b : Array Val) (endA : Bool) : BM (Array Val) := do
  modify fun s => { s with arithCounts := s.arithCounts.modify (opIndex op) fun c => c.modify (if endA then 0 else 1) (· + 1) }
  let (k, b) := match op with
    | .mul => (0, b)
    | .square => (0, a)
    | .add => (1, b)
  let s ← get
  let (u, slots) := if endA then (s.ended.getD k default, 0) else (s.forwarded.getD k default, 6)
  let (u, r, base) ← u.next
  modify fun s => if endA then { s with ended := s.ended.set! k u } else { s with forwarded := s.forwarded.set! k u }
  for l in [0:3] do
    place r (base + l) (a.getD l 0)
    place r (base + 3 + l) (b.getD l 0)
  let mut out : Array Val := #[]
  for l in [0:3] do out := out.push (← produce r (base + slots + l))
  return out

/-! ## Ports (`units::Ports`) -/

def portRoles (w limbs : ℕ) : Array Formula := (forwards w).set! (w - 1) (.port (List.range limbs))

def initPorts : BM Unit := do
  let w ← width
  let p3 ← region "port3" (portRoles w 3)
  let p4 ← region "port4" (portRoles w 4)
  modify fun s => { s with portUnits := #[Units.new p3 w 1, Units.new p4 w 1] }

/-- A port row: its roles `0..L` forward the limbs, its last role pushes their fingerprint outside (`Ports::port`). -/
def portOf (limbs : Array Val) (source : Source) : BM Unit := do
  need (limbs.size == source.limbs) "a port's limbs are its source's"
  let w ← width
  let k := limbs.size - 3
  let (u, r, _) ← ((← get).portUnits.getD k default).next
  modify fun s => { s with portUnits := s.portUnits.set! k u }
  for l in [0:limbs.size] do place r l (limbs.getD l 0)
  port r (w - 1) source

end Builder

end RecCircuit
