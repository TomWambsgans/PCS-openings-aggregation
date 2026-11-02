-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.Coins
import ZK.Assembly
import ZK.Joint
import ZK.Simulator
import ZK.Real
import ZK.Setup
import ZK.With
import ZK.Main
import ZK.Axioms

/-!
# Zero knowledge, end to end (Bridge-ZK)

`PcsQuotient.ZeroKnowledgeWith` (`formal/Statement`, `Security.lean`: zero knowledge for a simulator
given as a parameter) for `QuotientZk`'s simulator, from `formal/QuotientZk`.

* `ZK/Coins.lean`: the statement's distinguishers have coins, `QuotientZk`'s do not.
  **`zeroKnowledgeWith_of_coinFree`**: `ZeroKnowledgeWith s₀ sim simOracle ζ` follows from the same bound
  for coin-free distinguishers, for any simulator whose oracle forwards coins (a tape drawn first answers
  the coins; the proofs either experiment can hand the distinguisher are finitely many, so one tape
  serves all).
* `ZK/Simulator.lean`: `QuotientZk`'s simulator in the statement's shape, compiled (`rpmSimulator`,
  `rpmSimOracle`; `common`'s `simulator2` and `foldRO` transcribed, equal by definition): its ideal
  experiment is `simGameRpmD` (`rpmIdeal_eq`).
* `ZK/With.lean`: **`zkSimulator`**, the simulator the end theorem names: `rpmSimulator` at the public
  part of the prover (`PubProto`: what `sim` reads) and the view simulator of each statement;
  **`zeroKnowledgeWith_of_core`**: `ZeroKnowledgeWith` for it from the real bridge and `QuotientZk`'s
  closeness of the real and simulated games (`CoreClose`).
* `ZK/Real.lean`: the real bridge split: the prover's coins drawn outside the model
  (`realExperiment_coins`), then `CoinsMatch` (the coins are the skeleton model's uniform randomness read
  by `coinsOf`) and `ProverBridge` (the statement's prover at fixed coins against the skeleton's)
  give `RealBridge` (`realBridge_of`).
* `ZK/Setup.lean`: the skeleton of the statement's prover, `skelSetup`: the circuit's commitment (the
  wiring table's tree) computed over `π` first, its root the chain's index root, then `Deployed.skel`
  (the statement's prover computes it so; `Deployed.skel` reads it as a constant). At most
  `2^24 + 2^70` operations; its duplex discipline proved.
* `ZK/Main.lean`: **`zeroKnowledge_end`**: `ZeroKnowledgeWith s₀ (zkSimulator pp simV skelSetup fmt)
  rpmSimOracle (zkBoundEnd Qp Qfmt εR)`, `ζ Q = εR Q + 2^-113 + 2^-165 + 2^24 (2^24 + 2^70 + Qfmt + Q)
  2^-2368 + 2^48 2^-2368 + (Qp + Qfmt + Q)² / 2^508`, at most
  `εR Q + 2^-113 + 2^-165 + 2^-2200 + (Qp + Qfmt + Q)² / 2^508` for `Qfmt + Q ≤ 2^127` (`zkBoundEnd_le`);
  `QuotientZk`'s closeness from the joint model (`coreClose_of_joint`). Named: the joint model
  (`JointData.Valid`, its public part `pp`, its view simulator `simV`; `skelSetup`'s `FSFresh` is
  `fsFresh_setup_deployed_bits` from its conditions),
  the budgets `Qp`, `Qfmt`, `CoinsMatch`, `ProverBridge` (`εR`).
* `ZK/Assembly.lean`: the same assembly for the package's own `simulator` given an ideal bridge
  (`zeroKnowledge_of_bridges`, `zeroKnowledge_deployed` on the constant-root skeleton); the joint
  model's data (`JointData`) and the bounds (`zkBound`).
* `ZK/Axioms.lean`: the axioms of these theorems.
-/
