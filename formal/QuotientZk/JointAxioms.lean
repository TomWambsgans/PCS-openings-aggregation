-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.JointDeployed
import VCVio.OracleComp.RunIO

/-!
# ZK-joint: axiom guards, and the simulators run

Every theorem of `Joint*.lean` depends on `propext`, `Classical.choice`, `Quot.sound` only.

**The simulator's computability.** `#print axioms` does not tell a computable definition from a
noncomputable one here: VCVio's `SampleableType` class (a sampler with a proof that its output
measure is uniform) itself depends on `Classical.choice`, so every definition that samples lists it
(even `fun R [SampleableType R] => $ᵗ R`), as does `Fin.fintype`. The check is the compiler's:
`simulate`, `simRed` and the assembled `jointSim` are plain `def`s, which Lean compiles only when
nothing they compute from is `noncomputable` (it rejected `jointSim` while the gadget's
coefficients were a `Module.Basis`, whose coercion goes through `Finsupp`; they are now a plain
`Fin 3 → E`, the basis a hypothesis). F1's `simView`, `simValues`, `realView` are `noncomputable`.
Below, `simRed` (over `ZMod 2`) and `simulate` (on toy components) are run with
`OracleComp.runIO`.
-/

/-- info: 'QuotientZk.Joint.view_evalDistEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Joint.view_evalDistEq

/-- info: 'QuotientZk.Joint.redMsgs_evalDistEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Joint.redMsgs_evalDistEq

/-- info: 'QuotientZk.Joint.prob_not_good_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Joint.prob_not_good_le

/-- info: 'QuotientZk.Joint.Gadget.view_evalDistEq_of_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Joint.Gadget.view_evalDistEq_of_good

/-- info: 'QuotientZk.Joint.Gadget.prob_not_goodCh_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Joint.Gadget.prob_not_goodCh_le

/-- info: 'QuotientZk.Joint.SecretOpening.hides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Joint.SecretOpening.hides

/-- info: 'QuotientZk.Joint.joint_hzk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Joint.joint_hzk

/-- info: 'QuotientZk.Joint.joint_hgood' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Joint.joint_hgood

/-- info: 'QuotientZk.Joint.joint_hgood_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Joint.joint_hgood_bits

/-- info: 'QuotientZk.Joint.zk_rom_of_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Joint.zk_rom_of_joint

/-- info: 'QuotientZk.Joint.factors_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Joint.factors_single

/-- info: 'QuotientZk.Joint.factors_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Joint.factors_pair

/-- info: 'QuotientZk.Joint.jointHVZK_of_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Joint.jointHVZK_of_link

/-- info: 'QuotientZk.Joint.zk_deployed_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Joint.zk_deployed_joint

/-! The simulators (see above: `Classical.choice` enters through `SampleableType` itself). -/

/-- info: 'QuotientZk.Joint.simulate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Joint.simulate

/-- info: 'QuotientZk.Joint.simRed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Joint.simRed

/-- info: 'QuotientZk.Joint.jointSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Joint.jointSim

/-! ## The simulators run -/

namespace QuotientZk.Joint.Run

instance : SampleableType (ZMod 2) := inferInstanceAs (SampleableType (Fin 2))

/-- `simRed` over `ZMod 2` (the row in `K`), at `t = 1`, with the wiring's value `σ(t) = t`. -/
def demoRed : ProbComp ((Fin 4 → ZMod 2) × ZMod 2) :=
  simRed (K := ZMod 2) (E := ZMod 2) (fun _ => true) id 1

/-- `simulate` on toy components: paddings in `Fin 3` and `Fin 5`, the wiring opening `7`. -/
def demoSim : ProbComp (ℕ × ℕ × ℕ × ℕ) :=
  simulate (Ch := Unit) (R₁ := Fin 3) (R₂ := Fin 5) (fun _ => 7) (fun _ d r => d + r.val)
    (fun _ d r => d * r.val) (fun _ => pure 2) (fun _ v => v) (fun _ v => v + 1) ()

/-- info: (1, 7, true, true) -/
#guard_msgs in
#eval show IO _ from do
  let x ← demoRed.runIO
  let y ← demoSim.runIO
  return (x.2, y.2.1, decide (2 ≤ y.2.2.1 ∧ y.2.2.1 < 5), decide (y.2.2.2 % 3 = 0 ∧ y.2.2.2 ≤ 12))

end QuotientZk.Joint.Run
