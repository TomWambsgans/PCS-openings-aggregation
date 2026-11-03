-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCompose.Bridge
import RecCompose.Tables

/-!
# The end theorems, from the named inputs left

The end statements at the real deployment with every proved layer in place, their hypotheses the inputs left:

* π2's Fiat–Shamir layer `Pi2FsLayer D` (open, `lean-rec-compose`);
* the setup's columns `Pi2SetupColumns D C`: the deployment's σ, κ at every π1 IV are the compiled circuit's (the tables'
  layer is `pi2Tables`, proved from it; `RecDeployment.Real` pins σ, κ at `Data.pi1Iv` only);
* the compiled circuit `C : Pi2Circuits D` (the Lean compiler accepts π1-rec3's graph at every π1 IV, **checked by
  evaluation**: `rec-circuit-emitted`), at the emitted graph's roots (`hroots`), the Lean recording being the emitted
  graph (`GraphsAgree`, **checked by evaluation**: `RecGraphTest/Pi1Check.lean`);
* the circuit's facts `Fa : Pi2Facts D C` (`SpecOf` and the shape: `RecStatement.Lemmas.SpecLink`, the compiler's checks,
  the runners) and the ports' and calls' meaning in the contract's terms (`StatementPortMeaning`, `ZeroPortsMeaning`,
  `CallWordsAgree`, `Pi1CallsLayouts`: the runners, RecStatementTest and RecCircuitTest, `tests/pi2.rs`);
* for part 2, the Fiat–Shamir heuristic for Keccak-f[1600] (`Pi1FsKeccak`, `Pi1HazardKeccak`), `Pi1GraphIsVerifier`
  being proved (`RecGraph.Pi1.pi1GraphIsVerifier`).
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol
open scoped ENNReal

/-- **π2's part, at the real deployment**: `RecKnowledgeSoundness2 D pi2Bound`, `pi2Bound Q ≤ 2^-64` for `Q ≤ 2^64`. -/
theorem recKnowledgeSoundness2_final (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hcol : Pi2SetupColumns D C) (hfs : Pi2FsLayer D) (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree)
    (hstmt : StatementPortMeaning D C Fa) (hzero : ZeroPortsMeaning D C Fa) (hcalls : CallWordsAgree D C Fa)
    (hlay : Pi1CallsLayouts D) :
    RecKnowledgeSoundness2 D pi2Bound ∧ ∀ Q ≤ 2 ^ 64, pi2Bound Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  recKnowledgeSoundness2_real_bridge D hD C Fa (pi2Tables D C Fa hcol) hfs hroots hg hstmt hzero hcalls hlay

/-- π2's layers from the named inputs. -/
noncomputable def pi2LayersFinal (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hcol : Pi2SetupColumns D C) (hfs : Pi2FsLayer D) (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree)
    (hstmt : StatementPortMeaning D C Fa) (hzero : ZeroPortsMeaning D C Fa) (hcalls : CallWordsAgree D C Fa)
    (hlay : Pi1CallsLayouts D) : Pi2Layers D pi2Bound :=
  pi2Layers_of C Fa (pi2Tables D C Fa hcol) hfs
    (pi2CircuitAccepts_of_bridge C Fa hroots hg (circuitBridge D hD C Fa hroots hg hstmt hzero hcalls hlay))

/-- **End to end, against Lv42's `M3Holds`**: `RecKnowledgeSoundness D pi2Bound ε1 εh` for every `ε1`, `εh`. -/
theorem recKnowledgeSoundness_final (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hcol : Pi2SetupColumns D C) (hfs : Pi2FsLayer D) (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree)
    (hstmt : StatementPortMeaning D C Fa) (hzero : ZeroPortsMeaning D C Fa) (hcalls : CallWordsAgree D C Fa)
    (hlay : Pi1CallsLayouts D) (ε1 εh : ℕ → ℝ≥0∞) : RecKnowledgeSoundness D pi2Bound ε1 εh :=
  recKnowledgeSoundness_end D hD (pi2LayersFinal D hD C Fa hcol hfs hroots hg hstmt hzero hcalls hlay) ε1 εh

/-- **End to end, under the Fiat–Shamir heuristic for Keccak-f[1600] alone**: the explicit extractor `recExtractor`
fails while the contract accepts with probability at most `pi2Bound Q + ε1 Q + εh Q`. -/
theorem recKnowledgeSoundness_final_fs (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hcol : Pi2SetupColumns D C) (hfs : Pi2FsLayer D) (hroots : C.rootsAt = RecGraph.Emitted.rootsAt) (hg : GraphsAgree)
    (hstmt : StatementPortMeaning D C Fa) (hzero : ZeroPortsMeaning D C Fa) (hcalls : CallWordsAgree D C Fa)
    (hlay : Pi1CallsLayouts D) (ε1 εh : ℕ → ℝ≥0∞) (h1 : Pi1FsKeccak D ε1) (hh : Pi1HazardKeccak D εh) :
    RecKnowledgeSoundnessWith D (recExtractor D) fun Q ↦ pi2Bound Q + ε1 Q + εh Q :=
  recKnowledgeSoundness_end_fs D hD (pi2LayersFinal D hD C Fa hcol hfs hroots hg hstmt hzero hcalls hlay) ε1 εh h1 hh

end RecCompose

/-- info: 'RecCompose.recKnowledgeSoundness2_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness2_final

/-- info: 'RecCompose.recKnowledgeSoundness_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness_final

/-- info: 'RecCompose.recKnowledgeSoundness_final_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness_final_fs
