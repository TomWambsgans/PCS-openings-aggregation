-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Transcribed, in the Rust's operation order, from
-- `crates/leanvm_flock_gas/src/flock_min.rs` (`zerocheck`, `front`, `row_low_weights`, `known_weights`,
-- `verify_walked`, `walked_terminal`, `ring_end`), `flock.rs` (`lagrange_weights`, `lagrange_interpolate`,
-- `blake2s_row_values`, `RowValues`, adapted there from leanVM (https://github.com/leanEthereum/leanVM), commit
-- 42422001) and `ring_tower.rs` (`target`, `xor_network`).
import RecGraph.Pi1.Ops

/-!
# π1-rec3's verifier as a program: Flock with the walked terminal

The constants (`fixedChallenges`, `phi`, `windowDenominator`, the tower's `θ_j` and leaves) are `UniStatement`'s;
the leaves' `XOR` network (`xorNetwork`, Paar's greedy common subexpressions) is `ring_tower::xor_network`'s.
-/

namespace RecGraph.Pi1

open LeanVM.Parameters UniStatement UniStatement.Flock

/-- **`lagrange_weights(count, point)`**: the differences, the prefix and suffix products, the denominator. -/
def lagrangeWeights (count : Nat) (pt : Sym) : Prog (List Sym) := do
  let mut differences : Array Sym := #[]
  for node in [0:count] do
    let c ← const (phi node)
    differences := differences.push (← add pt c)
  let o1 ← one
  let mut prefix_ : Array Sym := Array.replicate (count + 1) o1
  let o2 ← one
  let mut suffix : Array Sym := Array.replicate (count + 1) o2
  for i in [0:count] do
    prefix_ := prefix_.set! (i + 1) (← mul (prefix_.getD i 0) (differences.getD i 0))
    suffix := suffix.set! (count - 1 - i) (← mul (suffix.getD (count - i) 0) (differences.getD (count - 1 - i) 0))
  let denominator ← const (windowDenominator count)
  let mut out : Array Sym := #[]
  for i in [0:count] do
    let p ← mul (prefix_.getD i 0) (suffix.getD (i + 1) 0)
    out := out.push (← mul p denominator)
  return out.toList

/-- `lagrange_interpolate(count, values, point)`. -/
def lagrangeInterpolate (count : Nat) (values : List Sym) (pt : Sym) : Prog Sym := do
  let weights ← lagrangeWeights count pt
  dot weights values

/-- **`zerocheck(log_n, k, fs)`**: the seven fixed coordinates, the others drawn as `fs` has it; the skip's coset
values and `z`; the rounds; `v_a`, `v_b`, `v_c = running + v_a v_b`. -/
def zerocheck (logN k : Nat) (fs : FsShape) : Prog (Option Sym × List Sym × Sym × Sym × Sym) := do
  let mut r : Array (Option Sym) := #[]
  for c in fixedChallenges do
    r := r.push (some (← const c))
  let drawn ← drawRun fs (logN - k - nFixed)
  r := r ++ (drawn.map some).toArray
  let (zSkip, claim) ← if k > 0 then do
      let coset ← nextScalars (2 ^ k)
      let z ← sample
      let zz ← zero
      let values := List.replicate (2 ^ k) zz ++ coset
      pure (some z, ← lagrangeInterpolate (2 ^ (k + 1)) values z)
    else do
      pure (none, ← zero)
  let (chi, running) ← sumcheckDrawn claim 3 r.toList false
  let vA ← nextScalar
  let vB ← nextScalar
  let ab ← mul vA vB
  let vC ← add running ab
  return (zSkip, chi, vA, vB, vC)

/-- What the zerocheck and the lincheck leave (`Front`). -/
structure FrontS where
  zSkip : Option Sym
  rowLow : List Sym
  chiIn : List Sym
  chiInPrime : List Sym
  chi : List Sym
  alpha : Sym
  rLc : Sym
  slices : List Sym
  point : List Sym

/-- **`front(log_n, variant)`** (the slices sent). -/
def front (logN : Nat) (variant : Variant) (fs : FsShape) : Prog FrontS := do
  let k := variant.skip
  let (zSkip, chi, vA, vB, vC) ← zerocheck logN k fs
  let rowLow := chi.take (packing - k)
  let rest := chi.drop (packing - k)
  let chiIn := rest.take lincheckRounds
  let chiRest := rest.drop lincheckRounds
  let alpha ← sample
  let t1 ← mul alpha vB
  let s1 ← add vA t1
  let a2 ← pow alpha 2
  let t2 ← mul a2 vC
  let s2 ← add s1 t2
  let a3 ← pow alpha 3
  let claim ← add s2 a3
  let (roundChallenges, rLc) ← sumcheckDrawn claim 3 (List.replicate lincheckRounds none) false
  let chiInPrime := roundChallenges.reverse
  let slices ← nextScalars kBits
  return ⟨zSkip, rowLow, chiIn, chiInPrime, chi, alpha, rLc, slices, chiInPrime ++ chiRest⟩

/-- **`row_low_weights(z_skip, low)`**: the skip's Lagrange weights, and their products with `eq(low, ·)`. -/
def rowLowWeights (zSkip : Option Sym) (low : List Sym) : Prog (List Sym × List Sym) := do
  let skip ← match zSkip with
    | some z => lagrangeWeights (2 ^ (packing - low.length)) z
    | none => do pure [← one]
  let mle ← eqKernel low
  let mut weights : Array Sym := #[]
  for m in mle.toList do
    for l in skip do
      weights := weights.push (← mul l m)
  return (skip, weights.toList)

/-- **`known_weights(α, chi_in, chi_in')`**: the pin's weight first, then the `C = I` claim's. -/
def knownWeights (alpha : Sym) (chiIn chiInPrime : List Sym) : Prog (Sym × Sym) := do
  let mut constantBits : Array Sym := #[]
  for bit in [0:lincheckRounds] do
    constantBits := constantBits.push (← const (eK (UInt64.ofNat ((constantColumn / kBits) >>> bit % 2))))
  let a3 ← pow alpha 3
  let e3 ← eqEval constantBits.toList chiInPrime
  let pinWeight ← mul a3 e3
  let a2 ← pow alpha 2
  let e2 ← eqEval chiIn chiInPrime
  let cWeight ← mul a2 e2
  return (cWeight, pinWeight)

/-! ### The BLAKE2s circuit's walk (`RowValues`) -/

/-- The walk's state: the column weights, `A0 w` and `B0 w` so far. -/
structure Walk where
  cw : Array Sym
  left : Array Sym
  right : Array Sym

/-- `slots(base)`. -/
def Walk.slots (s : Walk) (base : Nat) : Array Sym := Array.ofFn (n := 32) fun b ↦ s.cw.getD (base + b.val) 0

/-- `literal(value)`: the constant column's weight at each set bit, `S::zero()` at the others. -/
def Walk.literal (s : Walk) (value : Nat) : Prog (Array Sym) := do
  let constant := s.cw.getD constantColumn 0
  let mut out : Array Sym := #[]
  for b in [0:32] do
    out := out.push (← if value.testBit b then pure constant else zero)
  return out

/-- `xor(x, y)`. -/
def walkXor (x y : Array Sym) : Prog (Array Sym) := do
  let mut out : Array Sym := #[]
  for b in [0:32] do
    out := out.push (← add (x.getD b 0) (y.getD b 0))
  return out

/-- `rotate_right(word, amount)`. -/
def walkRotr (w : Array Sym) (amount : Nat) : Array Sym :=
  Array.ofFn (n := 32) fun b ↦ w.getD ((b.val + amount) % 32) 0

/-- **`RowValues::add(x, y, carry_base)`**. -/
def Walk.add (s : Walk) (x y : Array Sym) (carryBase : Nat) : Prog (Walk × Array Sym) := do
  let mut s := s
  let mut carry ← zero
  let z ← zero
  let mut output : Array Sym := Array.replicate 32 z
  for bit in [0:32] do
    if bit < 31 then
      s := { s with left := s.left.set! (carryBase + bit) (← RecGraph.Pi1.add (x.getD bit 0) carry) }
      s := { s with right := s.right.set! (carryBase + bit) (← RecGraph.Pi1.add (y.getD bit 0) carry) }
    let xy ← RecGraph.Pi1.add (x.getD bit 0) (y.getD bit 0)
    output := output.set! bit (← RecGraph.Pi1.add xy carry)
    if bit < 31 then
      carry ← RecGraph.Pi1.add carry (s.cw.getD (carryBase + bit) 0)
  return (s, output)

/-- **`RowValues::add3(x, y, z, base)`**: 31 majority rows, then 30 ripple rows. -/
def Walk.add3 (s : Walk) (x y z : Array Sym) (base : Nat) : Prog (Walk × Array Sym) := do
  let mut s := s
  let z0 ← zero
  let mut majority : Array Sym := Array.replicate 31 z0
  for bit in [0:31] do
    s := { s with left := s.left.set! (base + bit) (← RecGraph.Pi1.add (x.getD bit 0) (z.getD bit 0)) }
    s := { s with right := s.right.set! (base + bit) (← RecGraph.Pi1.add (y.getD bit 0) (z.getD bit 0)) }
    majority := majority.set! bit (← RecGraph.Pi1.add (s.cw.getD (base + bit) 0) (z.getD bit 0))
  let rippleBase := base + 31
  let mut carry ← zero
  let z1 ← zero
  let mut output : Array Sym := Array.replicate 32 z1
  for bit in [0:32] do
    let q ← if bit = 0 then zero else pure (majority.getD (bit - 1) 0)
    let xy ← RecGraph.Pi1.add (x.getD bit 0) (y.getD bit 0)
    let xyz ← RecGraph.Pi1.add xy (z.getD bit 0)
    let l ← RecGraph.Pi1.add xyz carry
    output := output.set! bit (← RecGraph.Pi1.add l q)
    if 1 ≤ bit ∧ bit ≤ 30 then
      s := { s with left := s.left.set! (rippleBase + bit - 1) l }
      s := { s with right := s.right.set! (rippleBase + bit - 1) (← RecGraph.Pi1.add q carry) }
      carry ← RecGraph.Pi1.add carry (s.cw.getD (rippleBase + bit - 1) 0)
  return (s, output)

/-- **`blake2s_row_values(column_weights)`**: `A0 w` and `B0 w` by one forward walk of the circuit. -/
def blake2sRowValues (cw : Array Sym) : Prog (Array Sym × Array Sym) := do
  let size := 2 ^ blake2sR1csLogSize
  let constant := constantColumn
  let messageBase := 640
  let counterLow := 1152
  let counterHigh := 1184
  let finalFlag := 1216
  let lastNodeFlag := 1248
  let gatesBase := 1280
  let gateStride := 184
  let z1 ← zero
  let left := Array.replicate size z1
  let z2 ← zero
  let right := Array.replicate size z2
  let mut s : Walk := ⟨cw, left, right⟩
  for (base, length) in [(0, 256), (messageBase, 512), (counterLow, 128)] do
    for row in [base:base + length] do
      s := { s with left := s.left.set! row (cw.getD row 0), right := s.right.set! row (cw.getD constant 0) }
  let z3 ← zero
  let mut state : Array (Array Sym) := Array.replicate 16 (Array.replicate 32 z3)
  for word in [0:8] do
    state := state.set! word (s.slots (32 * word))
  for word in [0:4] do
    state := state.set! (8 + word) (← s.literal (blake2sIv.getD word 0))
  for (base, word) in [counterLow, counterHigh, finalFlag, lastNodeFlag].zip (List.range 4) do
    let lit ← s.literal (blake2sIv.getD (4 + word) 0)
    state := state.set! (12 + word) (← walkXor lit (s.slots base))
  for (sigma, roundIndex) in blake2sSigma.zip (List.range blake2sSigma.length) do
    for (lanes, gateIndex) in blake2sGLanes.zip (List.range blake2sGLanes.length) do
      let gate := roundIndex * 8 + gateIndex
      let gateBase := gatesBase + gateStride * gate
      let la := lanes.getD 0 0
      let lb := lanes.getD 1 0
      let lc := lanes.getD 2 0
      let ld := lanes.getD 3 0
      let a := state.getD la #[]
      let b := state.getD lb #[]
      let c := state.getD lc #[]
      let d := state.getD ld #[]
      let mx := s.slots (messageBase + 32 * sigma.getD (2 * gateIndex) 0)
      let my := s.slots (messageBase + 32 * sigma.getD (2 * gateIndex + 1) 0)
      let (s1, a1) ← s.add3 a b mx gateBase
      let d1 := walkRotr (← walkXor d a1) 16
      let (s2, c1) ← s1.add c d1 (gateBase + 61)
      let b1 := walkRotr (← walkXor b c1) 12
      let (s3, a2) ← s2.add3 a1 b1 my (gateBase + 92)
      let d2 := walkRotr (← walkXor d1 a2) 8
      let (s4, c2) ← s3.add c1 d2 (gateBase + 153)
      let b2 := walkRotr (← walkXor b1 c2) 7
      s := s4
      state := (((state.set! la a2).set! lb b2).set! lc c2).set! ld d2
  for word in [0:8] do
    let x1 ← walkXor (state.getD word #[]) (state.getD (word + 8) #[])
    let out ← walkXor x1 (s.slots (32 * word))
    for bit in [0:32] do
      s := { s with left := s.left.set! (256 + 32 * word + bit) (out.getD bit 0),
                    right := s.right.set! (256 + 32 * word + bit) (cw.getD constant 0) }
  s := { s with left := s.left.set! constant (cw.getD constant 0), right := s.right.set! constant (cw.getD constant 0) }
  return (s.left, s.right)

/-- **`walked_terminal(z_skip, row_low, chi_in, chi_in', s, α)`**. -/
def walkedTerminal (zSkip : Option Sym) (rowLow chiIn chiInPrime s : List Sym) (alpha : Sym) : Prog Sym := do
  let (_, lowWeights) ← rowLowWeights zSkip rowLow
  let high ← eqKernel chiInPrime
  let z ← zero
  let mut w : Array Sym := Array.replicate (2 ^ blake2sR1csLogSize) z
  for (weight, h) in high.toList.zip (List.range high.size) do
    for (slice, l) in s.zip (List.range s.length) do
      w := w.set! (h * kBits + l) (← mul slice weight)
  let (left, right) ← blake2sRowValues w
  let rows ← eqKernel chiIn
  let mut matrix ← zero
  for (rowWeight, h) in rows.toList.zip (List.range rows.size) do
    let mut lSum ← zero
    let mut rSum ← zero
    for (weight, low) in lowWeights.zip (List.range lowWeights.length) do
      let pl ← mul weight (left.getD (h * kBits + low) 0)
      lSum ← add lSum pl
      let pr ← mul weight (right.getD (h * kBits + low) 0)
      rSum ← add rSum pr
    let ar ← mul alpha rSum
    let lr ← add lSum ar
    let rw ← mul rowWeight lr
    matrix ← add matrix rw
  let (cWeight, pinWeight) ← knownWeights alpha chiIn chiInPrime
  let d ← dot lowWeights s
  let cd ← mul cWeight d
  let m1 ← add matrix cd
  let ps ← mul pinWeight (s.getD (constantColumn % kBits) 0)
  add m1 ps

/-! ### The ring switch's end in tower order -/

/-- **`xor_network(leaves)`** (Paar's greedy common subexpressions): while some pair of variables occurs in two sums
or more, the most frequent pair (the first such) becomes a new variable. -/
def xorNetwork (leaves : Array Nat) : List (Nat × Nat) × List (List Nat) := Id.run do
  let mut rows : Array (List Nat) := leaves.map fun mask ↦ (List.range kBits).filter fun i ↦ mask.testBit i
  let mut xors : Array (Nat × Nat) := #[]
  for _ in [0:4096] do
    let vars := kBits + xors.size
    let mut count : Array Nat := Array.replicate (vars * vars) 0
    for row in rows do
      let ra := row.toArray
      for x in [0:ra.size] do
        for y in [x + 1:ra.size] do
          let idx := ra.getD x 0 * vars + ra.getD y 0
          count := count.modify idx (· + 1)
    -- the largest count, the first index among equals
    let mut best := 0
    let mut most := 0
    for at_ in [0:count.size] do
      if count.getD at_ 0 > most then
        best := at_
        most := count.getD at_ 0
    if most < 2 then break
    let a := best / vars
    let b := best % vars
    rows := rows.map fun row ↦ if row.contains a && row.contains b then (row.erase a).erase b ++ [vars] else row
    xors := xors.push (a, b)
  return (xors.toList, rows.toList)

/-- The tower's network, computed once. -/
def towerNetwork : List (Nat × Nat) × List (List Nat) := xorNetwork towerLeaves

/-- **`ring_tower::target(slices, map)`**: the leaves by the `XOR` network, then six levels. -/
def towerTarget (slices map : List Sym) : Prog Sym := do
  let (xors, sums) := towerNetwork
  let mut vars : Array Sym := slices.toArray
  for (a, b) in xors do
    vars := vars.push (← add (vars.getD a 0) (vars.getD b 0))
  let mut nodes : Array Sym := #[]
  for leaf in sums do
    let mut acc ← zero
    for v in leaf do
      acc ← add acc (vars.getD v 0)
    nodes := nodes.push acc
  for (f, j) in map.zip (List.range map.length) do
    let theta ← const (towerTheta.getD j 0)
    let mut next : Array Sym := #[]
    for q in [0:nodes.size / 2] do
      let a := nodes.getD (2 * q) 0
      let b := nodes.getD (2 * q + 1) 0
      let tb ← mul theta b
      let first ← add a tb
      let mut fa := a
      for _ in [0:2 ^ j] do
        fa ← square fa
      let mut fb := b
      for _ in [0:2 ^ j] do
        fb ← square fb
      let tfb ← mul theta fb
      let inner ← add fa tfb
      let second ← mul f inner
      next := next.push (← add first second)
    nodes := next
  return nodes.getD 0 0

/-- **`ring_end`** (tower order): the map's six challenges, then the target. -/
def ringEnd (s : List Sym) : Prog (List Sym × Sym) := do
  let map ← samples 6
  let target ← towerTarget s map
  return (map, target)

/-- **`verify_walked(log_n, variant)`**: the front, the terminal against the walk (required zero), the ring switch's
end. -/
def verifyWalked (logN : Nat) (variant : Variant) (fs : FsShape) : Prog (List Sym × List Sym × Sym) := do
  let fr ← front logN variant fs
  let terminal ← walkedTerminal fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime fr.slices fr.alpha
  requireZero (← add terminal fr.rLc)
  let (map, target) ← ringEnd fr.slices
  return (fr.point, map, target)

end RecGraph.Pi1
