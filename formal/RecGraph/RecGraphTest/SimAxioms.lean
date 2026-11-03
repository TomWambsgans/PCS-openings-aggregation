-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.Transcript

/-!
# The simulation's lemmas use Lean's three standard axioms only

`Sim/Chan.lean`, `Sim/Pure.lean`, `Sim/Transcript.lean`: run from `formal/EndToEnd` with
`lake env lean ../RecGraph/RecGraphTest/SimAxioms.lean`; it prints nothing when every guard holds.
-/

/-- info: 'RecGraph.Sim.Sim.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.Sim.bind

/-- info: 'RecGraph.Sim.Sim.pure_of_pstep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.Sim.pure_of_pstep

/-- info: 'RecGraph.Sim.Sim.of_psim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.Sim.of_psim

/-- info: 'RecGraph.Sim.Sim.map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.Sim.map

/-- info: 'RecGraph.Sim.Sim.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.Sim.mono

/-- info: 'RecGraph.Sim.Sim.congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.Sim.congr

/-- info: 'RecGraph.Sim.Sim.cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.Sim.cast

/-- info: 'RecGraph.Sim.Sim.of_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.Sim.of_good

/-- info: 'RecGraph.Sim.Sim.forIn_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.Sim.forIn_list

/-- info: 'RecGraph.Sim.Sim.pbind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.Sim.pbind

/-- info: 'RecGraph.Sim.Sim.forIn_range_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.Sim.forIn_range_congr

/-- info: 'RecGraph.Sim.PSim.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.PSim.bind

/-- info: 'RecGraph.Sim.PSim.forIn_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.PSim.forIn_list

/-- info: 'RecGraph.Sim.PSim.forIn_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.PSim.forIn_inv

/-- info: 'RecGraph.Sim.takeBytes_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.takeBytes_run

/-- info: 'RecGraph.Sim.takeBytes_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.takeBytes_fail

/-- info: 'RecGraph.Sim.sim_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.sim_input

/-- info: 'RecGraph.Sim.sim_nextScalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.sim_nextScalar

/-- info: 'RecGraph.Sim.sim_nextInteger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.sim_nextInteger

/-- info: 'RecGraph.Sim.sim_nextRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.sim_nextRoot

/-- info: 'RecGraph.Sim.sim_sampleOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.sim_sampleOp

/-- info: 'RecGraph.Sim.sim_sample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.sim_sample

/-- info: 'RecGraph.Sim.sim_sampleNarrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.sim_sampleNarrow

/-- info: 'RecGraph.Sim.sim_sampleDrawn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.sim_sampleDrawn

/-- info: 'RecGraph.Sim.sim_requireZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.sim_requireZero

/-- info: 'RecGraph.Sim.sim_nextScalars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.sim_nextScalars

/-- info: 'RecGraph.Sim.sim_samples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.sim_samples

/-- info: 'RecGraph.Sim.start_couple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.start_couple

/-- info: 'RecGraph.Sim.statementWords_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.statementWords_bind

/-- info: 'RecGraph.Sim.statementWords_psim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.statementWords_psim

/-- info: 'RecGraph.Sim.start_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.start_sim

/-- info: 'RecGraph.Sim.sum_psim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.sum_psim

/-- info: 'RecGraph.Sim.dot_psim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.dot_psim

/-- info: 'RecGraph.Sim.eqEval_psim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.eqEval_psim

/-- info: 'RecGraph.Sim.polyEval_psim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.polyEval_psim

/-- info: 'RecGraph.Sim.pairPoint_psim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.pairPoint_psim

/-- info: 'RecGraph.Sim.pow_psim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.pow_psim

/-- info: 'RecGraph.Sim.eqKernel_psim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.eqKernel_psim

/-- info: 'RecGraph.Sim.squares_psim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.squares_psim

/-- info: 'RecGraph.Sim.digits_psim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.digits_psim

/-- info: 'RecGraph.Sim.coordinatesAt_psim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.coordinatesAt_psim

/-- info: 'RecGraph.Sim.vanishingRatio_psim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.vanishingRatio_psim

/-- info: 'RecGraph.Sim.activeVanishingFromBits_psim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.activeVanishingFromBits_psim

/-- info: 'RecGraph.Sim.sim_roundPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.sim_roundPoly

/-- info: 'RecGraph.Sim.sim_sumcheckDrawn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.sim_sumcheckDrawn

/-- info: 'RecGraph.Sim.sim_pairRoundPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.sim_pairRoundPoly

/-- info: 'RecGraph.Sim.sim_sumcheckPairsDrawn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.sim_sumcheckPairsDrawn

/-- info: 'RecGraph.Sim.sim_drawRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.sim_drawRun

/-- info: 'RecGraph.Sim.sim_countBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.sim_countBits

/-- info: 'RecGraph.Sim.finish_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.finish_run
