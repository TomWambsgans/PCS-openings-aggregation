-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCompose.ViewDefs
import RecCircuit.Sound
import RecGraph.Emitted

/-!
# The view check, evaluated

`rec-view-check`: runs `RecCircuit.compile (ofRG RecGraph.Emitted.graph RecGraph.Emitted.rootsAt iv)` (compiled code)
at π1's reference IV (`RecStatement.Data.pi1Iv`) and at the all-zero IV, and evaluates `RecCompose.viewCheck` on the
circuit: its view (`viewOf`, `adapt` transcribed) is `Data.circuit`, its calls (`callsOf`) are `Data.pi1Calls`, and it is
valid (`validB`), part by part.
-/

open RecCompose

def checkAt (label : String) (iv : List UInt8) : IO Bool := do
  let t0 ← IO.monoMsNow
  match RecCircuit.compile (RecCircuit.ofRG RecGraph.Emitted.graph RecGraph.Emitted.rootsAt iv) with
  | .error m => IO.println s!"{label}: the compiler rejects the graph: {m}"; return false
  | .ok c =>
    let t1 ← IO.monoMsNow
    IO.println s!"{label}: compiled in {t1 - t0} ms"
    let C := c.circuit
    let v := viewOf C
    let d := RecStatement.Data.circuit
    IO.println s!"{label}: logN {v.logN == d.logN}, logRow {v.logRow == d.logRow}, formulas \
      {decide (v.formulas = d.formulas)} ({v.formulas.length}/{d.formulas.length}), pairs \
      {decide (v.pairs = d.pairs)} ({v.pairs.length}/{d.pairs.length}), reads {decide (v.reads = d.reads)} \
      ({v.reads.length}/{d.reads.length}), public terms {decide (v.publicTerms = d.publicTerms)} \
      ({v.publicTerms.length}/{d.publicTerms.length})"
    IO.println s!"{label}: calls {decide (callsOf C = RecStatement.Data.pi1Calls)}"
    let part (name : String) (b : Unit → Bool) : IO Unit := do
      let t ← IO.monoMsNow
      let v := b ()
      let t' ← IO.monoMsNow
      IO.println s!"{label}: validB {name}: {v} ({t' - t} ms)"
      (← IO.getStdout).flush
    IO.println s!"{label}: {C.blocks.size} blocks, {C.regions.size} regions, {C.ports.size} ports, \
      {C.kappa.size} kappa entries"
    part "logW < logN" fun _ ↦ decide (C.logWidth < C.logN)
    part "widths" fun _ ↦ C.regions.all fun r ↦ r.roles.size == C.width
    part "reads" fun _ ↦ readsB C
    part "blocks" fun _ ↦ blocksB C
    part "ports" fun _ ↦ portsB C
    part "no hole read" fun _ ↦ noHoleReadB C
    part "kappa" fun _ ↦ kappaExprB C
    part "sigma" fun _ ↦ sigmaOkB C
    let ok := viewCheck c
    IO.println s!"{label}: viewCheck {ok}"
    (← IO.getStdout).flush
    return ok

def main : IO UInt32 := do
  let a ← checkAt "pi1 reference IV" RecStatement.Data.pi1Iv
  let b ← checkAt "zero IV" (List.replicate 32 0)
  return if a && b then 0 else 1
