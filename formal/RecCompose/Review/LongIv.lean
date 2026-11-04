-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Review evidence (STATEMENT_REVIEW.md, finding 1): built as
-- a `lean_exe` `rec-long-iv` (srcDir "../RecCompose", root `RecComposeTest.LongIv`, after copying this file there).
-- `rec-long-iv 49152` printed: "iv of 49152 bytes: the compiler rejects the graph: the checker rejects the circuit: graph".
import RecCompose.ViewDefs
import RecCircuit.Sound
import RecGraph.Emitted

/-! Review: the compiler on π1-rec3's graph at a long IV (`Pi2Circuits`, `Pi2ViewChecked` quantify over every
`List UInt8`). -/

open RecCompose

def main (args : List String) : IO UInt32 := do
  let len := (args.headD "49152").toNat!
  let iv := List.replicate len (0xff : UInt8)
  let t0 ← IO.monoMsNow
  match RecCircuit.compile (RecCircuit.ofRG RecGraph.Emitted.graph RecGraph.Emitted.rootsAt iv) with
  | .error m => IO.println s!"iv of {len} bytes: the compiler rejects the graph: {m}"; return 0
  | .ok c =>
    let t1 ← IO.monoMsNow
    let v := viewOf c.circuit
    IO.println s!"iv of {len} bytes: compiled in {t1 - t0} ms; logN {v.logN} (Data {RecStatement.Data.circuit.logN}), logRow {v.logRow}"
    (← IO.getStdout).flush
    IO.println s!"viewCheck {viewCheck c}"
    return 0
