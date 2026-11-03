-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π1-rec3's analogues of `ProbHyp.lean`'s named
-- hypotheses; uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR
-- Apache-2.0): the two calls `KeccakCalls`, `implH`, `implF`, the block cost `hashBlocks`; and
-- `formal/EndToEnd/Completeness/E2ECompleteness/Duplex.lean`'s discipline `Disc`.
import UniComplete.Rec3Split
import UniComplete.Rec3VerifierH
import UniComplete.ProbHyp

/-!
# π1-rec3's named hypotheses

The facts π1-rec3's probability layer uses, each a `Prop` named here and proved in its own module (or left a
hypothesis of the end theorem, `Rec3End.lean` says which), as `ProbHyp.lean` names the main line's:

**The prover over the two calls** (`m := OracleComp KeccakCalls`, `H := callKeccak256`, `F := callKeccakF1600`):
`ProverCommutes3`, `ProverDuplex3`, `ProverCost3`, `ProverStreamSize3` (the main line's, for `uniProverRec3With`);
Flock's prover's commutation is the main line's `Prob.FlockSimCommutes` / `FlockCommutes` (generic in the prover).

**The verifier over the two calls**: `VerifierCommutes3` (it commutes with every simulation), `VerifierDisc3` (the
duplex discipline), `VerifierCost3 D S N` (at most `N` block calls on streams of at most `S` bytes): for the main line
`VerifierHSim.lean`, `VerifierHDuplex.lean`, `VerifierHCost.lean` prove them.

**The deterministic core** (at every pure `H`, `F`): `CoreAccepts3` (at good bus challenges, `proverChallenges3`, and a
good `t`, `proverTChallenge3`, the honest proof is accepted by π1-rec3's verifier), `CoreFailsOnlyAtPow3` (the prover
fails only at an opening). **The bad sets' counts** are the main line's (`Prob.BadFpCard`, `Prob.BadTCard`: they do
not depend on how `α` was drawn).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile.Rom (implH implF)
open UniStatement

set_option autoImplicit false

namespace UniComplete.Rec3

open UniComplete.Prob (BadT)

/-! ## The prover over the two calls -/

/-- **π1-rec3's prover commutes with simulation.** -/
def ProverCommutes3 (flock : FlockProverH) (D : Deployment) : Prop :=
  ∀ {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows),
    simulateQ impl (uniProverRec3With callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q) =
      uniProverRec3With (implH impl) (implF impl) (flock (implH impl)) D input rows q

/-- **π1-rec3's prover follows the duplex discipline**, from any earlier answers. -/
def ProverDuplex3 (flock : FlockProverH) (D : Deployment) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
    D.HonestRelation rows input q →
    E2ECompleteness.Disc (uniProverRec3With callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q)

/-- **π1-rec3's prover makes at most `N` block calls.** -/
def ProverCost3 (flock : FlockProverH) (D : Deployment) (N : ℕ) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
    D.HonestRelation rows input q →
    Common.QueryCostAtMost (uniProverRec3With callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q)
      hashBlocks N

/-- **π1-rec3's prover's streams have at most `S` bytes**, on every path. -/
def ProverStreamSize3 (flock : FlockProverH) (D : Deployment) (S : ℕ) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
    D.HonestRelation rows input q → ∀ π : UniProof,
    some π ∈ support (uniProverRec3With callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q) →
      π.stream.size ≤ S

/-! ## The verifier over the two calls -/

/-- **π1-rec3's deployed verifier commutes with simulation** (Keccak-256 becoming `implH impl`, the permutation
`implF impl`). -/
def VerifierCommutes3 : Prop :=
  ∀ {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r) (D : Deployment)
    (roots : SetupRoots) (input : Vector UInt8 32) (proof : UniProof),
    simulateQ impl (Deployment.verifierRec3WithH callKeccak256 callKeccakF1600 D roots input proof) =
      Deployment.verifierRec3WithH (implH impl) (implF impl) D roots input proof

/-- **π1-rec3's deployed verifier is disciplined**, from any earlier answers. -/
def VerifierDisc3 : Prop :=
  ∀ (D : Deployment) (roots : SetupRoots) (input : Vector UInt8 32) (proof : UniProof),
    E2ECompleteness.Disc (Deployment.verifierRec3WithH callKeccak256 callKeccakF1600 D roots input proof)

/-- **π1-rec3's deployed verifier makes at most `N` block calls** on a proof whose stream has at most `S` bytes. -/
def VerifierCost3 (D : Deployment) (S N : ℕ) : Prop :=
  ∀ (roots : SetupRoots) (input : Vector UInt8 32) (proof : UniProof), proof.stream.size ≤ S →
    Common.QueryCostAtMost (Deployment.verifierRec3WithH callKeccak256 callKeccakF1600 D roots input proof)
      hashBlocks N

/-! ## The deterministic core -/

/-- **π1-rec3's PIOP's completeness at a pure hash and permutation**: at good bus challenges and a good `t`, the
honest proof is accepted by π1-rec3's deployed verifier. -/
def CoreAccepts3 (D : Deployment) (flock : FlockProverH) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
    D.HonestRelation rows input q →
    ∀ (H : List UInt8 → Digest) (F : KeccakState → KeccakState) (π : UniProof),
      uniProverRec3With (m := Id) H F (flock H) D input rows q = some π →
      ¬ BadFp (honestTrace D input rows q) (proverChallenges3 H D input rows q).1
        (proverChallenges3 H D input rows q).2 →
      ¬ BadT D.shape (proverTChallenge3 H (flock H) D input rows q).1
        (proverTChallenge3 H (flock H) D input rows q).2 →
      Deployment.verifierRec3WithH (m := Id) H F D (setupTreesWithH (m := Id) H F D).roots input π = true

/-- **π1-rec3's prover fails only at an opening**, at a pure hash and permutation and good challenges. -/
def CoreFailsOnlyAtPow3 (D : Deployment) (flock : FlockProverH) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
    D.HonestRelation rows input q →
    ∀ (H : List UInt8 → Digest) (F : KeccakState → KeccakState),
      ¬ BadFp (honestTrace D input rows q) (proverChallenges3 H D input rows q).1
        (proverChallenges3 H D input rows q).2 →
      ¬ BadT D.shape (proverTChallenge3 H (flock H) D input rows q).1
        (proverTChallenge3 H (flock H) D input rows q).2 →
      uniProverRec3With (m := Id) H F (flock H) D input rows q = none →
      ∃ (L : PcsQuotient.Layout) (tree : LeanVM.Prover.Tree) (stack : Array K) (claims : List PcsQuotient.Claim),
        E2ECompleteness.proveOpeningWithH (m := Id) H F PcsQuotient.nonceFuel L tree stack claims = none

end UniComplete.Rec3
