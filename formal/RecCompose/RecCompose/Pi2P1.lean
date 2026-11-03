-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π1-rec3's honest prover is `formal/UniComplete`'s
-- (`UniComplete.Rec3.uniProverRec3With`, `uniProverRec3RP`, `Rec3Prover.lean`, `crates/leanvm_univariate`'s
-- `FLOCK_REC3`).
import RecCompose.Pi2ProbStaged
import UniComplete.Rec3End

/-!
# π1-rec3's honest prover, as π2's completeness takes it

* **`p1k D input rows q`**: π1-rec3's honest prover (`uniProverRec3With` with Flock's `flockProve3H`) over the two
  calls (Keccak-256 and Keccak-f[1600]): the program `pi2Staged` runs first. It replaces the parameter `P1k` of
  `Pi2ProbStaged`'s named facts.
* **`pi1Rec3Prover D`**: the same over the random permutation (`uniProverRec3RP flockProve3H D.pi1`), the `P1` of
  `RecCompleteness2` (the statement's fix 3: π2's completeness is for π1-rec3's prover).
-/

namespace RecCompose.Pi2G

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM

/-- **π1-rec3's honest prover over the two calls.** -/
def p1k (D : RecDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows) :
    OracleComp KeccakCalls (Option UniStatement.UniProof) :=
  UniComplete.Rec3.uniProverRec3With callKeccak256 callKeccakF1600
    (UniComplete.Rec3.flockProve3H callKeccak256) D.pi1 input rows q

/-- **π1-rec3's honest prover over the random permutation.** -/
abbrev pi1Rec3Prover (D : RecDeployment) : Pi1Prover D :=
  UniComplete.Rec3.uniProverRec3RP UniComplete.Rec3.flockProve3H D.pi1

end RecCompose.Pi2G
