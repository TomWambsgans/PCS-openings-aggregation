-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Rom.Defs
import QuotientZk.Rom.FS
import QuotientZk.Rom.Tape
import QuotientZk.Rom.Split
import QuotientZk.Rom.Merkle
import QuotientZk.Rom.Entropy
import QuotientZk.Rom.MerkleBound
import QuotientZk.Rom.Main
import QuotientZk.Deployed.RowEntropy
import QuotientZk.Deployed.Skeleton
import QuotientZk.Deployed.Bound
import QuotientZk.Deployed.Main
import QuotientZk.Check
import QuotientZk.JointCore
import QuotientZk.JointReduction
import QuotientZk.JointGadget
import QuotientZk.Joint
import QuotientZk.JointDeployed
import QuotientZk.JointAxioms
import QuotientZk.RpmTape
import QuotientZk.RpmProver
import QuotientZk.RpmMain
import QuotientZk.RpmDuplex
import QuotientZk.RpmDuplexProver
import QuotientZk.RpmDeployed
import QuotientZk.RpmJoint
import QuotientZk.RpmAxioms
import QuotientZk.RpmDiscipline
import QuotientZk.Deployed.Fresh
import QuotientZk.Deployed.Fresh.Setup
import QuotientZk.FreshJoint
import QuotientZk.Instance.Builder
import QuotientZk.Instance.Main
import QuotientZk.Instance.Nondeg

/-!
# Zero knowledge of the non-interactive proof (layer F3b)

* `Rom/`: the generic theorem. The prover is a public skeleton of operations (`Rom/Defs.lean`); the
  simulator `sim` draws the challenges, then the simulated view, and runs the skeleton with the
  challenges programmed and fresh private digests at the unopened leaves. **`zk_rom`**: real and
  simulated games within `εFS + εhv + N (|c₀| + QP + QD) δ + N² δ₂`.
* `Deployed/`: the deployed prover's skeleton (`skel`, the reduction's Keccak-256 chain, leanVM's
  Merkle trees and multiproofs, the overwrite duplex with grinding, the three openings), its
  operation count (`skel_queryBound`, `≤ 2^70` at `2^22` rows), the unopened rows' entropy for the
  redesigned (gadget) layout (`row_entropy`, `gadget_stackR_of_onFirst`) carried to the joint view
  (`Factors.bound`). **`zk_deployed`**, **`zk_deployed_bits`**: `εFS + εhv + 2^-2200`.
* `Deployed/Fresh/`, `Deployed/Fresh.lean`: `FSFresh` proved for the deployed skeleton
  (`fsFresh_deployed`: `εFS = Q · 6 (|c₀| + Q) / 2^256 + 2 (|c₀| + Q) · 3 εc + |c₀| δ₀`,
  `fsFresh_deployed_bits`: `≤ 2^-54`), for a prover whose rows are long, whose witness table's first
  row has min-entropy, and whose openings' claims read a challenge; **`zk_deployed_fs`**,
  **`zk_deployed_fs_bits`**: `2^-54 + εhv + 2^-2200`.
* `Rpm*`: the random-permutation model (leanerVM `mumbai`'s `common`). The real game hashes with
  Keccak-256 over `π` and calls `π` in the duplex; the simulator runs `sim` on the skeleton with
  the duplex's bookkeeping and answers the distinguisher's `π`, `π⁻¹` with `common`'s two-oracle
  indifferentiability simulator over the programmed cache. **`zk_rpm_deployed`**,
  **`zk_rpm_deployed_bits`**, **`zk_rpm_deployed_joint`** (`RpmJoint.lean`): the ROM bounds plus
  `Q² / 2^508` for `Q` permutation calls (`zk_rpm`, `RpmMain.lean`: a prover hashing with
  Keccak-256 only, plus `Q² / 2^509`). `RpmDiscipline.lean` discharges two of their hypotheses:
  the deployed prover follows the duplex discipline for every shape (`duplexDiscipline_skel`), and
  its rows are byte strings (`ofBytes`); **`zk_rpm_deployed_bits'`**, **`zk_rpm_deployed_joint'`**
  are the statements without `hrow` and `hduplex`.
* `Joint*`, `FreshJoint.lean`, `Instance/`: the joint honest-verifier model (the reduction's masks with
  the two hidden openings) and its instance for the deployed prover. The theorems that ask the honest
  tables' claims at every mask (`joint_hzk`, `jointHVZK_of_link`, `zk_deployed_joint(_fs)`,
  `zk_rpm_deployed_joint(_fs)(')`, `joint_hzkV`, `jointHVZK_of_linkV`, `zk_rpm_deployed_jointV_fs'`,
  `zk_rpm_deployed_instance`) are **superseded**: the honest tables do not meet those hypotheses at
  degenerate challenges and masks. The chain the end theorem (`PcsQuotient.EndToEnd.zeroKnowledge_closed`)
  uses is `Instance/Nondeg.lean`'s `jointHVZKε_of_linkV` (the claims under `ClaimsND` only) with
  `zk_rpm_skel_approx` (`RpmDeployed.lean`).
-/

/-- info: 'QuotientZk.zk_rom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.zk_rom

/-- info: 'QuotientZk.tape_evalDistEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.tape_evalDistEq

/-- info: 'QuotientZk.implUp_evalDistEq_implSplit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.implUp_evalDistEq_implSplit

/-- info: 'QuotientZk.prEvent_mBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.prEvent_mBad_le

/-- info: 'QuotientZk.prEvent_hit_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.prEvent_hit_le

/-- info: 'QuotientZk.Deployed.row_entropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Deployed.row_entropy

/-- info: 'QuotientZk.Deployed.gadget_stackR_of_onFirst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Deployed.gadget_stackR_of_onFirst

/-- info: 'QuotientZk.Deployed.prEvent_factor_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Deployed.prEvent_factor_le

/-- info: 'QuotientZk.Deployed.skel_queryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Deployed.skel_queryBound

/-- info: 'QuotientZk.Deployed.skelBound_deployed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Deployed.skelBound_deployed

/-- info: 'QuotientZk.Deployed.zk_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Deployed.zk_deployed

/-- info: 'QuotientZk.Deployed.zk_deployed_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Deployed.zk_deployed_bits

/-- info: 'QuotientZk.Deployed.hidden_hδ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Deployed.hidden_hδ

/-- info: 'QuotientZk.Deployed.Fresh.fsFresh_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Deployed.Fresh.fsFresh_deployed

/-- info: 'QuotientZk.Deployed.Fresh.fsFresh_deployed_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Deployed.Fresh.fsFresh_deployed_bits

/-- info: 'QuotientZk.Deployed.Fresh.zk_deployed_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Deployed.Fresh.zk_deployed_fs

/-- info: 'QuotientZk.Deployed.Fresh.zk_deployed_fs_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Deployed.Fresh.zk_deployed_fs_bits

/-- info: 'QuotientZk.Deployed.Fresh.trip_skel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Deployed.Fresh.trip_skel

/-- info: 'QuotientZk.Deployed.Fresh.prEvent_bad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Deployed.Fresh.prEvent_bad_le

/-- info: 'QuotientZk.Deployed.Fresh.epsFS_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Deployed.Fresh.epsFS_le

/-- info: 'QuotientZk.Joint.zk_deployed_joint_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.Joint.zk_deployed_joint_fs

/-- info: 'QuotientZk.DRpm.zk_rpm_deployed_joint_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.DRpm.zk_rpm_deployed_joint_fs

/-- info: 'QuotientZk.DRpm.zk_rpm_deployed_joint_fs'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuotientZk.DRpm.zk_rpm_deployed_joint_fs'
