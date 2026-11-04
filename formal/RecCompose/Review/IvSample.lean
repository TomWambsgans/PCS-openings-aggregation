-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCompose.RealDeployment

/-!
# `IvChecked` at more IVs, and the compiled circuit's IV dependence (`STATEMENT_REVIEW_2.md`, finding 2)

Built as the executable `rec-iv-sample` (`formal/EndToEnd/lakefile.toml`). `rec-iv-sample K i` evaluates, for
the IVs `ivAt i, …, ivAt (i + K − 1)` (pseudo-random 32-byte IVs of a fixed xorshift stream; at indices `1000`,
`1001`, `1002` three structured ones):

* `ivCheck iv` (`RecCompose.IvChecked`'s Boolean at that IV);
* **the IV dependence of the compiled circuit**, against the reference IV's (`refCompiled`): whether `logN`,
  `logWidth`, the regions, the blocks, `σ`, the ports and the calls are equal, and the symmetric difference of the
  sparse `κ` (positions and values). Every entry of the difference must be a `1`, `κ`'s size must move by the IVs'
  popcount difference, and the positions are printed, so that their union over all runs can be compared with the
  seed's 256 IV constants.
-/

set_option compiler.extract_closed false

open RecCompose RecStatement

/-- A xorshift64 step. -/
def xs (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

/-- 32 pseudo-random bytes of seed `i`. -/
def rnd (i : Nat) : List UInt8 := Id.run do
  let mut x : UInt64 := 0x9E3779B97F4A7C15 + (UInt64.ofNat i) * 0xBF58476D1CE4E5B9
  for _ in [0:8] do x := xs x
  let mut out : List UInt8 := []
  for _ in [0:32] do
    x := xs x
    out := out ++ [(x >>> 32).toUInt8]
  return out

/-- The IVs: pseudo-random, then three structured ones (the reference IV with its first bit flipped, a single low
bit, a single high bit). -/
def ivAt (i : Nat) : List UInt8 :=
  if i == 1000 then (Data.pi1Iv.headD 0 ^^^ 1) :: Data.pi1Iv.tail
  else if i == 1001 then 1 :: List.replicate 31 0
  else if i == 1002 then List.replicate 31 0 ++ [0x80]
  else rnd i

def hexOf (b : List UInt8) : String :=
  String.join (b.map fun x ↦
    let s := String.ofList (Nat.toDigits 16 x.toNat)
    if s.length = 1 then "0" ++ s else s)

def popcount (b : List UInt8) : Nat := (b.map fun x ↦ (List.range 8).countP fun j ↦ x.toNat.testBit j).sum

def flush : IO Unit := do (← IO.getStdout).flush

def main (args : List String) : IO UInt32 := do
  let k := (args.getD 0 "1").toNat!
  let i0 := (args.getD 1 "0").toNat!
  let r := refCompiled
  IO.println s!"reference IV {hexOf Data.pi1Iv}: {r.circuit.kappa.size} kappa entries, popcount {popcount Data.pi1Iv}"
  flush
  let mut ok := true
  for i in [i0:i0 + k] do
    let iv := ivAt i
    let c := compiledAt iv
    let v := ivCheck iv
    let same := decide (c.circuit.logN = r.circuit.logN) && decide (c.circuit.logWidth = r.circuit.logWidth) &&
      decide (c.circuit.regions = r.circuit.regions) && decide (c.circuit.blocks = r.circuit.blocks) &&
      decide (c.circuit.sigma = r.circuit.sigma) && decide (c.circuit.ports = r.circuit.ports) &&
      decide (c.circuit.calls = r.circuit.calls)
    let a := c.circuit.kappa.toList
    let b := r.circuit.kappa.toList
    let onlyC := a.filter fun e ↦ !(b.contains e)
    let onlyR := b.filter fun e ↦ !(a.contains e)
    let ones := (onlyC ++ onlyR).all fun e ↦ e.2 == 1
    let sizeOk := (c.circuit.kappa.size + popcount Data.pi1Iv) == (r.circuit.kappa.size + popcount iv)
    IO.println s!"iv[{i}] {hexOf iv} (popcount {popcount iv}): ivCheck {v}; structure equal {same}; \
      kappa {c.circuit.kappa.size} entries, +{onlyC.length} -{onlyR.length}, all ones {ones}, \
      size = ref + popcount diff {sizeOk}"
    IO.println s!"  kappa diff positions: {(onlyC ++ onlyR).map (·.1)}"
    flush
    ok := ok && v && same && ones && sizeOk
  IO.println s!"rec-iv-sample: {if ok then "all hold" else "SOMETHING FAILS"}"
  return if ok then 0 else 1
