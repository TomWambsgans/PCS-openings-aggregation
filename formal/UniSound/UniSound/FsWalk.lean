-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The walk is `UniStatement.runWith`
-- (`formal/UniStatement/UniStatement/Run.lean`), the chain `Compose.ChainSpecU.chain`
-- (`formal/Compose/Compose/ListChainU.lean`).
import UniSound.FsCouple
import UniSound.FinalLink

/-!
# The verifier bridge's two halves: the walk is the chain, then the openings

`UniVerifierBridge` (`FsCouple.lean`) compares the Statement's `verifyWith` (the walk on the stream,
`runWith`, then the five `PCS_OPEN` calls) with the composed verifier (the chain `verU`, then the
five openings `opsRun`). It splits at the walk:

* **`UniWalk`** (the walk is the chain): on a stream of the main line's length (`uLen`: the row
  counts' `24` bytes, the rounds' messages, the tail's five scalars), in every lawful monad and over
  every permutation `F`, the walk's verdict and result are a function of the chain's challenges
  over Keccak-256 `= keccak256With F`: the verdict `uAccB` (the row counts' range checks and every
  value the chain program requires zero vanish), the result the chain program's (`uOut`);
* **`UniWalkReject`** (a stream of another length is rejected): every outcome of the walk over `π`
  rejects (the stream runs out, `StreamExhausted`, or is left unread, `StreamNotConsumed`);
* the openings (`uniVerifierBridge_of_walk`, the remaining half): the Statement's five `PCS_OPEN`
  calls are F2's `ourVerifierEarly` at the plain layouts (`Bridge.openingWith_eq_ourVerifier'`),
  which accept at most as often as the composed openings (`Soundness.early_le`), and acceptance
  makes the result well formed (`uniCheck`).
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack

section Walk

variable (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (nV V : ℕ) (C : UniCode D Fl nV V)

/-- **The stream's length the main line reads**: the row counts' `24` bytes, the rounds' messages
(`roundsBytes`), the tail's five scalars. -/
def uLen : ℕ := 24 + roundsBytes (uRounds Fl nV V) + 24 * 5

/-- **The row counts' range checks** (`readCounts`), in order: each count below `2^(r + 1)`, and at
most `2^r`, for its height `r`. -/
def countZeros (heights rows : List ℕ) : List E :=
  (heights.zip rows).flatMap fun x =>
    [intBits x.2 (x.1 + 1) 32, intBits x.2 x.1 1 * intBits x.2 0 x.1]

/-- **The walk accepts**: the row counts' range checks vanish, and every value the chain program
requires zero does, on the transcript the stream and the challenges make. -/
def UAcc (π : UPf) (ch : List (List E)) : Prop :=
  (∀ z ∈ countZeros D.shape.heights (uSt Fl nV V π).2, z = 0) ∧
    (C.prog (uSt Fl nV V π).1 (uSt Fl nV V π).2).ZerosVanish (uDone (uRounds Fl nV V) π ch)
      (uTail (uRounds Fl nV V) π)

open Classical in
/-- `UAcc` as a verdict. -/
noncomputable def uAccB (π : UPf) (ch : List (List E)) : Bool := decide (UAcc D Fl nV V C π ch)

/-- **WALK**: on a stream of the main line's length, in every lawful monad and over every
permutation, the walk's verdict and result are the chain's challenges read by `uAccB` and the chain
program's result `uOut`, the chain over Keccak-256 the sponge over the permutation. -/
def UniWalk : Prop :=
  ∀ {m : Type → Type} [Monad m] [LawfulMonad m] (F : KeccakState → m KeccakState) (π : UPf),
    π.proof.stream.size = uLen Fl nV V →
      (fun o : UniStatement.Outcome => (o.accepts, o.result)) <$>
          runWith F D.shape π.iv.toList π.input.toList π.proof.stream (.flock flockMain) .point =
        (fun ch => (uAccB D Fl nV V C π ch, (Except.ok (uOut D Fl nV V C π ch) : Except UniError Reduced))) <$>
          (uSpec Fl nV V).chain (fun x => toB <$> keccak256With F x) (uView (uRounds Fl nV V) π).1
            (uView (uRounds Fl nV V) π).2

/-- **WALK REJECTS**: on a stream of any other length, every outcome of the walk over `π` rejects. -/
def UniWalkReject : Prop :=
  ∀ π : UPf, π.proof.stream.size ≠ uLen Fl nV V →
    ∀ o ∈ support (runWith Common.queryPermutation D.shape π.iv.toList π.input.toList
      π.proof.stream (.flock flockMain) .point), o.accepts = false

/-- **The chain program's result names the roots the stream carries** at rounds `0` (`C1`) and
`nF + 1` (`C2`). -/
def UniOutRoots : Prop :=
  ∀ (π : UPf) (ch : List (List E)),
    (uOut D Fl nV V C π ch).roots =
      (((uDone (uRounds Fl nV V) π ch).getD 0 default).1.1.getD default,
        ((uDone (uRounds Fl nV V) π ch).getD (Fl.prog.rounds.length + 1) default).1.1.getD default)

end Walk

/-- The main line's chain program names them (`mainOut`). -/
theorem uniOutRoots_uniCodeAt (D : Deployment) {κ : ℕ} (Fl : FlockSound κ)
    (hκ : D.shape.heights.getD opBlake2s 0 = κ) (nV V : ℕ) (hnV : nV = valsCount)
    (hV : V = varsOf (layoutsOf D.shape)) :
    UniOutRoots D Fl nV V (uniCodeAt D Fl hκ nV V hnV hV) := fun _ _ => rfl

end UniSound

/-- info: 'UniSound.uniOutRoots_uniCodeAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniOutRoots_uniCodeAt
