-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The executable of the differential test of `QuotientZk.Deployed.skel` (`SkelTrace.lean`); the Rust
-- half is `crates/quotient/tests/skel_trace.rs`.
import QuotientZk.Test.SkelTrace

/-!
`skeltrace INPUT TRACE PROOF`: read the Rust half's input, print the deployed shapes' numbers (for the
Rust half to check against its configuration at `2^22`), run `skel` on the input's shape and messages
and write its operations to `TRACE` and its proof to `PROOF`.

Its stack: `skel`'s trees are built by `levelUp`, whose recursion nests one bind a pair of leaves, so a
step of the run reaches through as many binds as pairs done; run it with a large stack
(`ulimit -s unlimited`). At `2^17` rows it takes 6 minutes (quadratic in the largest tree's `2^18` leaves).
The first `lake build skeltrace` compiles every imported module to an object file (a quarter of an hour on 16
cores).
-/

open QuotientZk.Deployed QuotientZk.Test.SkelTrace

def main (args : List String) : IO UInt32 := do
  let [inPath, tracePath, proofPath] := args
    | IO.eprintln "usage: skeltrace INPUT TRACE PROOF"; return 2
  let buf ← IO.FS.readBinFile inPath
  let inp ← match inputAt buf with
    | .ok i => pure i
    | .error e => IO.eprintln e; return 2
  -- The deployed shapes (`2^22` rows), with the ids of the `2^22` layouts.
  let id := fun i => inp.ids22.getD i default
  IO.println s!"deployed witness {shapeLine (witnessShape (id 0))}"
  IO.println s!"deployed wiring {shapeLine (wiringShape (id 1) [])}"
  IO.println s!"deployed quotient {shapeLine (quotientShape (id 2))}"
  let shapes := inp.shapes.map InShape.toOpen
  for (name, s) in ["witness", "wiring", "quotient"].zip shapes do
    IO.println s!"run {name} {shapeLine s}"
  let [sW, sσ, sQ] := shapes | IO.eprintln "three shapes expected"; return 2
  let sh : Shape := ⟨inp.st, sW, sσ, sQ⟩
  let h ← IO.FS.Handle.mk tracePath .write
  let st : DState := ⟨buf, inp.msgPos, inp.msgCount, 0, inp.leaves, none, none, h, Array.replicate 7 0, #[]⟩
  let t0 ← IO.monoMsNow
  let (proof, st) ← runLoop (skel sh) st
  let ((), st) ← flushRuns.run st
  h.flush
  let t1 ← IO.monoMsNow
  let hp ← IO.FS.Handle.mk proofPath .write
  writeProof hp proof
  hp.flush
  IO.println s!"operations H={st.counts[0]!} C={st.counts[1]!} F={st.counts[2]!} X={st.counts[3]!} tries={st.counts[4]!} L={st.counts[5]!} M={st.counts[6]!}"
  IO.println s!"messages left {st.msgsLeft}, time {t1 - t0} ms"
  for e in st.errors do IO.println s!"error {e}"
  return 0
