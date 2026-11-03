-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The main line's `FsWalk.lean` for π1-rec3's walk
-- (`UniStatement.runWithFs … .rec3 true`, `formal/UniStatement/UniStatement/Rec.lean`).
import UniSound.Rec3.FsCouple3
import UniSound.FsWalk

/-!
# π1-rec3's verifier bridge: the walk is the chain, then the openings

`FsWalk.lean`'s split of the verifier bridge at the walk, for π1-rec3 (`runWithFs … .rec3 true`):

* **`UniWalk3`**: on a stream of π1-rec3's length (`uLen3`: the row counts' `24` bytes, the rounds' messages on
  `rec3Rounds`, the tail's three scalars), in every lawful monad and over every permutation, the walk's verdict
  and result are the chain's challenges read by `uAccB3` and the chain program's result `uOut3`;
* **`UniWalkReject3`**: on a stream of any other length, every outcome of the walk over `π` rejects;
* **`UniOutRoots3`**: the code-level link's result names the stream's two roots (rounds `0` and `nF + 1`).
  It is a hypothesis about the code-level link `C` (another module proves it for the concrete link); it follows
  from the link's `out` naming them on every transcript (`uniOutRoots3_of`).

**The narrow challenges** change nothing here: the chain's challenges are the hash's full outputs
(`challengeOf state`), the chain program `C.prog` applies `narrowE` itself where the code does, and the walk reads
`reduceWithFs`'s run only through `obsOf3` (verdict, result, stream, cursor, absorbed bytes, state, the zeros'
verdict), never the channel's `challenges` (where `sampleNarrow` records the narrow value).
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement
open OracleSpec OracleComp
open scoped ENNReal

section Walk

variable (D : Deployment) {κ : ℕ} (F3 : FlockSound3 κ) (nV np : ℕ) (C : UniCode3 D F3 nV np)

/-- **The stream's length π1-rec3 reads**: the row counts' `24` bytes, the rounds' messages (`roundsBytes`), the
tail's three scalars. -/
def uLen3 : ℕ := 24 + roundsBytes (uRounds3 F3 nV np) + 24 * 3

/-- **The walk accepts**: the row counts' range checks vanish, and every value the chain program requires zero
does, on the transcript the stream and the challenges make. -/
def UAcc3 (π : UPf) (ch : List (List E)) : Prop :=
  (∀ z ∈ countZeros D.shape.heights (uSt3 F3 nV np π).2, z = 0) ∧
    (C.prog (uSt3 F3 nV np π).1 (uSt3 F3 nV np π).2).ZerosVanish (uDone (uRounds3 F3 nV np) π ch)
      (uTail3 (uRounds3 F3 nV np) π)

open Classical in
/-- `UAcc3` as a verdict. -/
noncomputable def uAccB3 (π : UPf) (ch : List (List E)) : Bool := decide (UAcc3 D F3 nV np C π ch)

/-- **WALK** (π1-rec3): on a stream of π1-rec3's length, in every lawful monad and over every permutation, the
walk's verdict and result are the chain's challenges read by `uAccB3` and the chain program's result `uOut3`, the
chain over Keccak-256 the sponge over the permutation. -/
def UniWalk3 : Prop :=
  ∀ {m : Type → Type} [Monad m] [LawfulMonad m] (F : KeccakState → m KeccakState) (π : UPf),
    π.proof.stream.size = uLen3 F3 nV np →
      (fun o : UniStatement.Outcome => (o.accepts, o.result)) <$>
          runWithFs F D.shape π.iv.toList π.input.toList π.proof.stream (.flock flockMain) .point .rec3 true =
        (fun ch => (uAccB3 D F3 nV np C π ch,
            (Except.ok (uOut3 D F3 nV np C π ch) : Except UniError Reduced))) <$>
          (uSpec3 F3 nV np).chain (fun x => toB <$> keccak256With F x) (uView (uRounds3 F3 nV np) π).1
            (uView (uRounds3 F3 nV np) π).2

/-- **WALK REJECTS** (π1-rec3): on a stream of any other length, every outcome of the walk over `π` rejects. -/
def UniWalkReject3 : Prop :=
  ∀ π : UPf, π.proof.stream.size ≠ uLen3 F3 nV np →
    ∀ o ∈ support (runWithFs Common.queryPermutation D.shape π.iv.toList π.input.toList
      π.proof.stream (.flock flockMain) .point .rec3 true), o.accepts = false

/-- **The chain program's result names the roots the stream carries** at rounds `0` (`C1`) and `nF + 1` (`C2`):
`UniOutRoots`' analog, a hypothesis about the code-level link. -/
def UniOutRoots3 : Prop :=
  ∀ (π : UPf) (ch : List (List E)),
    (uOut3 D F3 nV np C π ch).roots =
      (((uDone (uRounds3 F3 nV np) π ch).getD 0 default).1.1.getD default,
        ((uDone (uRounds3 F3 nV np) π ch).getD (F3.prog.rounds.length + 1) default).1.1.getD default)

/-- **`UniOutRoots3` from the link's result on every transcript** (the form the code-level link's module proves:
its `out` names the transcript's roots at rounds `0` and `nF + 1`). -/
theorem uniOutRoots3_of (h : ∀ input rows (done : Done) (tl : List E), ((C.prog input rows).out done tl).roots =
    (((done.getD 0 default).1.1).getD default,
      ((done.getD (F3.prog.rounds.length + 1) default).1.1).getD default)) :
    UniOutRoots3 D F3 nV np C :=
  fun _ _ => h _ _ _ _

end Walk

end UniSound
