-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.Coins
import ZK.Assembly
import ZK.Simulator
import ZK.Real
import ZK.Setup
import ZK.Main
import ZK.Axioms

/-!
# Zero knowledge, end to end (Bridge-ZK)

`PcsQuotient.ZeroKnowledge` (`formal/Statement`, `Security.lean`) from `formal/QuotientZk`.

* `ZK/Coins.lean`: the statement's distinguishers have coins, `QuotientZk`'s do not.
  **`zeroKnowledge_of_coinFree`**: `ZeroKnowledge ζ` follows from the same bound for coin-free
  distinguishers (a tape drawn first answers the coins; the proofs either experiment can hand the
  distinguisher are finitely many, so one tape serves all). Whatever the simulator.
* `ZK/Assembly.lean`: **`zeroKnowledge_deployed`**: `ZeroKnowledge (zkBoundDeployed Qp Qfmt εR εI)` from
  `QuotientZk.DRpm.zk_rpm_skel` on the deployed skeleton, the joint model's honest-verifier zero
  knowledge and factorizations, `fsFresh_deployed` (no query before the proof: `epsFSDeployed ≤ 2^-113`)
  and `duplexDiscipline_skel`. `ζ Q = εR Q + epsFSDeployed + 2^-165 + 2^24 (2^70 + Qfmt + Q) 2^-2368 +
  2^48 2^-2368 + (Qp + Qfmt + Q)² / 2^508 + εI Q` (`zkBound`), at most
  `εR Q + 2^-113 + 2^-165 + 2^-2200 + (Qp + Qfmt + Q)² / 2^508 + εI Q` for `Qfmt + Q ≤ 2^127`
  (`zkBoundDeployed_le`). Named: the joint model of the deployed prover (`JointData`, `JointData.Valid`:
  `zk_rpm_deployed_joint_fs'`'s hypotheses), the prover's permutation budget `Qp`, the bridges
  `RealBridge` (`εR`) and `IdealBridge` (`εI`).
* `ZK/Simulator.lean`: `QuotientZk`'s simulator in the statement's shape, compiled (`rpmSimulator`,
  `rpmSimOracle`; `common`'s `simulator2` and `foldRO` transcribed, equal by definition): its ideal
  experiment is `simGameRpmD` (`rpmIdeal_eq`), so with it as the statement's simulator the ideal bridge
  is exact (`εI = 0`).
* `ZK/Real.lean`: the real bridge split: the prover's coins drawn outside the model
  (`realExperiment_coins`), then `CoinsMatch` (the coins are the skeleton model's uniform randomness read
  by `coinsOf`) and `ProverBridge` (the statement's prover at fixed coins against the skeleton's)
  give `RealBridge` (`realBridge_of`).
* `ZK/Setup.lean`: the skeleton of the statement's prover, `skelSetup`: the circuit's commitment (the
  wiring table's tree) computed over `π` first, its root the chain's index root, then `Deployed.skel`
  (the statement's prover computes it so; `Deployed.skel` reads it as a constant). At most
  `2^24 + 2^70` operations; its duplex discipline proved.
* `ZK/Main.lean`: **`zeroKnowledge_end`**: `ZeroKnowledge (zkBoundEnd Qp Qfmt εFS εR)` on `skelSetup`,
  `ζ Q = εR Q + εFS + 2^-165 + 2^24 (2^24 + 2^70 + Qfmt + Q) 2^-2368 + 2^48 2^-2368 +
  (Qp + Qfmt + Q)² / 2^508`, at most `εR Q + εFS + 2^-165 + 2^-2200 + (Qp + Qfmt + Q)² / 2^508` for
  `Qfmt + Q ≤ 2^127` (`zkBoundEnd_le`). Named: the joint model (`JointData.Valid`), `skelSetup`'s
  `FSFresh` (`εFS`), the budgets `Qp`, `Qfmt`, `CoinsMatch`, `ProverBridge` (`εR`), and the statement's
  ideal experiment being `rpmSimulator`'s (`hI`).
* `ZK/Axioms.lean`: the axioms of these theorems.
-/
