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
