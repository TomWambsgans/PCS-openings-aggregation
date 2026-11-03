-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the
-- two calls `KeccakCalls`, their implementations' Keccak-256 and permutation (`implH`, `implF`), the block cost
-- `hashBlocks`; and `formal/EndToEnd/Completeness/E2ECompleteness/Duplex.lean`'s discipline `Disc`.
import UniComplete.ProbSplit
import UniComplete.Honest
import UniComplete.VerifierH
import E2ECompleteness.Duplex

/-!
# The named hypotheses of univariate completeness

The probability layer (`Prob*.lean`) proves `UniCompleteness D (uniProverRP flock D) δ` from these propositions, which
are about the honest prover and the PIOP at **pure** functions or about the prover's code over the two calls, and
are proved elsewhere (the prover's staging, branch `lean-uni-pstagec`; the PIOP's completeness; the bad set's count).
`flock : PolyFlock` is Flock's prover, polymorphic in the monad and in Keccak-256.

**The prover over the two calls** (`m := OracleComp KeccakCalls`, `H := callKeccak256`, `F := callKeccakF1600`):

* `ProverCommutes flock D`: it commutes with every simulation (`simulateQ impl`), Keccak-256 becoming `implH impl`
  and the permutation `implF impl` (Flock's prover too);
* `ProverDuplex flock D`: it follows the duplex discipline from any earlier answers (`E2ECompleteness.Disc`);
* `ProverCost flock D N`: at most `N` block calls (`hashBlocks`) on every path;
* `ProverStreamSize flock D S`: every proof it can output has a stream of at most `S` bytes.

**The deterministic core** (at every pure `H : List UInt8 → Digest`, `F : KeccakState → KeccakState`, the prover at
`m := Id`, i.e. `pure ∘ H`, `pure ∘ F`):

* `CoreAccepts D flock`: when the prover's bus challenges (`proverChallenges H`, its writer's first five) avoid the
  bad set `BadFp` of the honest trace and the prover returns a proof, the deployed verifier at the same `H`, `F`,
  on the setup's roots at `H`, accepts it;
* `CoreFailsOnlyAtPow D flock`: when they avoid it and the prover returns no proof, one of its WHIR opening provers
  (`E2ECompleteness.proveOpeningWithH` at `H`, `F`, `nonceFuel` nonces) returns none. (`UniComplete.pcsOpen_fails_only_at_pow`
  turns that into a failed `17`-bit search; the probability layer does it itself, `ProbGrind.lean`, tracking the
  sponge's shape, which the potential needs.)

**The bad set's count**: `BadFpCard D Nbad`: for every `α`, at most `Nbad` values of `β` are bad.

Each hypothesis is asked only for an honest witness at row counts that fit (`RowsFit`, `HonestRelation`), but for
`ProverCommutes`, an identity of programs.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile.Rom (implH implF)
open UniStatement

set_option autoImplicit false

namespace UniComplete.Prob

/-- **Flock's prover**, for every monad and every Keccak-256. -/
abbrev PolyFlock : Type 1 := ∀ {m : Type → Type} [Monad m], (List UInt8 → m Digest) → FlockProver m

/-- **The honest prover in the random-permutation model**: `uniProverWith` over `π`, Keccak-256 the sponge over `π`
(`keccak256With queryPermutation`), Flock's prover at the same Keccak-256. -/
def uniProverRP (flock : PolyFlock) (D : Deployment) : UniProver D :=
  uniProverWith (keccak256With Common.queryPermutation) Common.queryPermutation
    (flock (keccak256With Common.queryPermutation)) D

/-! ## The prover over the two calls -/

/-- **The prover commutes with simulation.** -/
def ProverCommutes (flock : PolyFlock) (D : Deployment) : Prop :=
  ∀ {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows),
    simulateQ impl (uniProverWith callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q) =
      uniProverWith (implH impl) (implF impl) (flock (implH impl)) D input rows q

/-- **The prover follows the duplex discipline**, from any earlier answers. -/
def ProverDuplex (flock : PolyFlock) (D : Deployment) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
    D.HonestRelation rows input q →
    E2ECompleteness.Disc (uniProverWith callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q)

/-- **The prover makes at most `N` block calls.** -/
def ProverCost (flock : PolyFlock) (D : Deployment) (N : ℕ) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
    D.HonestRelation rows input q →
    Common.QueryCostAtMost (uniProverWith callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q)
      hashBlocks N

/-- **The prover's streams have at most `S` bytes**, on every path. -/
def ProverStreamSize (flock : PolyFlock) (D : Deployment) (S : ℕ) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
    D.HonestRelation rows input q → ∀ π : UniProof,
    some π ∈ support (uniProverWith callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q) →
      π.stream.size ≤ S

/-! ## The deterministic core -/

/-- **The PIOP's completeness at a pure hash and permutation**: at good bus challenges, the honest proof is accepted. -/
def CoreAccepts (D : Deployment) (flock : PolyFlock) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
    D.HonestRelation rows input q →
    ∀ (H : List UInt8 → Digest) (F : KeccakState → KeccakState) (π : UniProof),
      uniProverWith (m := Id) H F (flock H) D input rows q = some π →
      ¬ BadFp (honestTrace D input rows q) (proverChallenges H D input rows q).1
        (proverChallenges H D input rows q).2 →
      Deployment.verifierWithH (m := Id) H F D (setupTreesWithH (m := Id) H F D).roots input π = true

/-- **The prover fails only at an opening**, at a pure hash and permutation and good bus challenges. -/
def CoreFailsOnlyAtPow (D : Deployment) (flock : PolyFlock) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
    D.HonestRelation rows input q →
    ∀ (H : List UInt8 → Digest) (F : KeccakState → KeccakState),
      ¬ BadFp (honestTrace D input rows q) (proverChallenges H D input rows q).1
        (proverChallenges H D input rows q).2 →
      uniProverWith (m := Id) H F (flock H) D input rows q = none →
      ∃ (L : PcsQuotient.Layout) (tree : LeanVM.Prover.Tree) (stack : Array K) (claims : List PcsQuotient.Claim),
        E2ECompleteness.proveOpeningWithH (m := Id) H F PcsQuotient.nonceFuel L tree stack claims = none

/-- **At most `Nbad` bad values of `β` for each `α`.** -/
def BadFpCard (D : Deployment) (Nbad : ℕ) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
    D.HonestRelation rows input q → ∀ alphas : List E,
    ∃ T : Finset E, T.card ≤ Nbad ∧ ∀ b, BadFp (honestTrace D input rows q) alphas b → b ∈ T

end UniComplete.Prob
