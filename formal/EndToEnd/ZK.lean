-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.Coins
import ZK.Assembly
import ZK.Joint
import ZK.Simulator
import ZK.Real
import ZK.Setup
import ZK.With
import ZK.Main
import ZK.Format
import ZK.CoinsMatch
import ZK.End
import ZK.ProverBridge
import ZK.ProverBridgeDuplex
import ZK.ProverBridgeMerkle
import ZK.Final
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
  rpmSimOracle (zkBoundEnd Qp Qfmt εR)`, `ζ Q = εR Q + 2^-113 + epsHV + 2^24 (2^24 + 2^70 + Qfmt + Q)
  2^-2368 + 2^48 2^-2368 + (Qp + Qfmt + Q)² / 2^508`, at most
  `εR Q + 2^-113 + epsHV + 2^-2200 + (Qp + Qfmt + Q)² / 2^508` for `Qfmt + Q ≤ 2^127` (`zkBoundEnd_le`),
  `epsHV = 2^-165 + 2^-125 + 2/2^192` (the joint model's bad challenges and degenerate masks);
  `QuotientZk`'s closeness from the joint model (`coreClose_of_joint`). Named: the joint model
  (`JointData.Valid`, its public part `pp`, its view simulator `simV`; `skelSetup`'s `FSFresh` is
  `fsFresh_setup_deployed_bits` from its conditions),
  the budgets `Qp`, `Qfmt`, `CoinsMatch`, `ProverBridge` (`εR`).
* `ZK/Format.lean`: **`fmt`**, the statement's proof from the skeleton's (the verifier's program replayed,
  the full Merkle paths produced from the pruned multiproofs), within `2^23` calls of `π`
  (`fmt_queryBound`).
* `ZK/CoinsMatch.lean`: the statement's coins are `decodeCoins` of uniform words (`sampleCoinsP_eq`);
  `coinsMatch_of_bijective`.
* `ZK/End.lean`: **`zeroKnowledge_deployed_end`**: `zeroKnowledge_end` with the joint model of the deployed
  prover instantiated (`deployedJointData_valid`, `ZK/Joint.lean`), `fmt` and `coinsMatch_of_bijective`:
  the simulator `zkSimulator (fun _ ↦ deployedPub rep) (deployedSimV …) skelSetup fmt`. Named: the field,
  F1's facts, the simulator's public functions, the honest tables' claims (off the degenerate challenges
  and masks, `ClaimsND`), the prover's budget `Qp`, the bijection `e` of the randomness onto the coins'
  words, `ProverBridge`.
* `ZK/Final.lean`: **`zeroKnowledge_deployed_final`**: `zeroKnowledge_deployed_end` at the deployed
  fields, instance, tables and coins, the field, F1's facts, the simulator's public functions, the honest
  tables' claims and the coins' bijection discharged (`ZK/FactsField.lean`, `ZK/FactsF1.lean`,
  `ZK/FactsLayout.lean`: the layouts' claims on a placed table, `ZK/FactsClaims.lean`: `hTWD`, `hTQD`).
  Named: the renderer `R`, the prover's budget `Qp`, `ProverBridge` at `decodeCoins ∘ eD`.
* `ZK/Joint.lean`: the joint model of the deployed prover (`deployedJointData`, `deployedJointData_valid`).
* `ZK/ProverBridge*.lean`: the prover bridge. The lazily sampled permutation is a uniform one drawn
  first (`ProverBridgeEager.lean`, `prEvent_runWithRandomPermutation`, `close_of_perm`); the
  statement's prover through monad morphisms (`ProverBridgeParam.lean`, `prover_hom`); the skeleton
  against a fixed oracle (`ProverBridgeSkel.lean`, `mem_support_proverJ`); so **`proverBridge_of_det`**
  (`ProverBridgeReduce.lean`): `ProverBridge` at `εR = δ` from a statement about programs at a fixed
  permutation (`hcore`) and `δ` bounding the statement's prover making no proof. The renderer
  **`whirRenderer`** (`ProverBridgeRender.lean`: WHIR's honest prover on the available view, driven
  in the skeleton's order); **`proverBridge_whir`**, **`zeroKnowledge_deployed_whir`**
  (`ProverBridge.lean`): the end theorem with that renderer, from `CoreWhir` and `noneProb ≤ δ`.
  Toward `CoreWhir`: the skeleton's duplex is the statement's sponge, grinding is the proof-of-work
  search (`ProverBridgeDuplex.lean`: `draw_rel`, `grind_rel`); the skeleton's trees are mumbai's and
  `fmt`'s expansion of the pruned multiproofs gives mumbai's full openings (`ProverBridgeMerkle.lean`:
  `tree_levels`, `tree_root`, `expandMulti_eq`).
* `ZK/Assembly.lean`: the same assembly for the package's own `simulator` given an ideal bridge
  (`zeroKnowledge_of_bridges`, `zeroKnowledge_deployed` on the constant-root skeleton); the joint
  model's data (`JointData`) and the bounds (`zkBound`).
* `ZK/Axioms.lean`: the axioms of these theorems.
-/
