-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The bound's form is
-- `formal/Compose/Compose/ListChainKDoom.lean`'s `knowledgeSoundness_listChainK_closed_rpm`.
import UniSound.PiopSound

/-!
# The code-level link, the final link and the Fiat–Shamir layer

Three hypotheses of the end theorem, each a statement about `UniStatement`'s verifier, none
about the PIOP's mathematics:

* **`UniCode`** (the code-level link): after the row counts, `reduceWith` on the main line (Flock
  `flockMain`, point claims) is a chain program (`UniSound.Prog`) on `uniRounds`, its Flock
  rounds Flock's chain program, its tail the three stacks' values and `a`, `b` at the batch's point.
* **`UniFinal`** (the last link): the verifier's last check (the batch's terminal) with the
  claims true makes the sumcheck's last claim the identity model's
  `Σ_{k<3} λ^k W_k(r) C_k(r) + λ³ G(r) L(r)` at its point (`I.prod`, `I.target`: `weightAt` is
  the multilinear extension of the cube's weights, the stacks zero-extended, the pending matrices'
  term `(a + α b) L̂(ρ) ŝ(σ)`).
* **`FsLayer`** (the Fiat–Shamir layer): for **every** round-by-round sound protocol on the main
  line's rounds whose first state is leanVM 42422001's relation (`hpre`) and whose last state
  follows from the verifier's checks with true claims on the candidates (`hlink`), the univariate
  verifier is knowledge sound for `uniExtractor` with the bound `uniBound e` (`e` bounding the
  rounds' errors). It is `Compose.knowledgeSoundness_listChainK_closed_rpm` for the univariate
  verifier: its proof is the port of `ListChainK` to the univariate transcript (24-byte scalars,
  roots as two reversed 16-byte halves, the seed `name ‖ iv ‖ input`; see `FsLayer`'s
  docstring), the five `PCS_OPEN` calls as `WhirOp`s (`WhirShape.large`: `C1`, `C2`, the setup
  and `A0`, `B0` at `2^24 … 2^28` words), the setup's three trees and its IV, and the extractor's
  reading (`uniExtractor`'s replay, Merkle inversion and decoders list the chain's candidates).

**`uniBound e Q`**, for an adversary of `Q` calls of `π` and `π⁻¹`: the five openings' doom terms,
the chain's list term with both roots' lists at most `9952` (`largeList` at `2^24`, the largest
of `2^24 … 2^28`), and the random-permutation term, with `N = 2^33 + Q` bounding every count (the
setup's `< 2^26` Keccak-256 calls, twice, the chain's `< 2^10`, the openings' `5 · 10122`):

`5 · openingBoundAt 10122 N + N · (9952² e + (2^128 + 8 N) / 2^256) + (2^81 + Q)² / 2^508`.

The port (`FsProof.lean`'s `fsLayer_of_game`, through `Compose.ListChainU`) separates the seed
`name ‖ iv ‖ input` from a step's input by its 16-byte tag `name`: a fresh answer starting with it is
a bad event, `2^-128` a query (the `2^128 / 2^256` term, `≈ 2^-64` at `Q = 2^64`); an input refers
to at most five digests (`Refers`' three, and a root after a state or after the row counts), so
`ListChainK`'s `5 N` becomes `(5 + 2) N ≤ 8 N`; `QVπ ≤ 2^80` the verifier's calls of `π`.
-/

namespace UniSound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement Finset WhirBridge
open scoped ENNReal

/-! ## Claims on candidates -/

/-- The multilinear extension of a stack (a function of the word) on its first `n` coordinates. -/
noncomputable def mleStk (c : Stk) (n : ℕ) (pt : List E) : E :=
  ∑ x : Fin (2 ^ n), cubeEq pt n x.val * ofK (c x.val)

/-- **The stack a commitment's claim is on**: `C1`'s and `C2`'s candidates, the setup's honest
stack. -/
def stackFor (D : Deployment) (c1 c2 : Stk) : Commitment → Stk
  | .c1 => c1
  | .c2 => c2
  | .setup => fun i => (setupStack D.prog D.shape).getD i 0

/-- The layout word of a commitment's `PCS_OPEN` call (`layoutWords`: `C1`, `C2`, the setup). -/
def wordIndex : Commitment → ℕ
  | .c1 => 0
  | .c2 => 1
  | .setup => 2

/-- **The claims the verifier hands `PCS_OPEN` hold** of the candidates `c1`, `c2`, the setup's
stack, and Flock's matrices `A0`, `B0`: each commitment's point claim on its stack's multilinear
extension at its layout word's variables (`verifyWith`'s `layoutWordVars`), and `Â0(p) = a`,
`B̂0(p) = b` at theirs. -/
def ClaimsHold (D : Deployment) (r : Reduced) (c1 c2 : Stk) : Prop :=
  (∀ o ∈ r.openings, ∀ pt v bs, o.2 = .point pt v bs →
    mleStk (stackFor D c1 c2 o.1)
      (layoutWordVars ((layoutWords D.shape).getD (wordIndex o.1) [])) pt = v) ∧
  ∀ mc, r.matrices = some mc →
    mleArr (flockMatrixStack true) (layoutWordVars ((layoutWords D.shape).getD 3 [])) mc.point =
        mc.a ∧
      mleArr (flockMatrixStack false) (layoutWordVars ((layoutWords D.shape).getD 4 [])) mc.point =
        mc.b

/-- **The opened transcript of a completed one**, round `0`'s root read as `c1`, round
`nF + 1`'s as `c2`. -/
def openedOf (nF : ℕ) (c1 c2 : Stk) (done : Done) : Op Stk :=
  (done.zipIdx).map fun x =>
    ((if x.2 = 0 then some c1 else if x.2 = nF + 1 then some c2 else none, x.1.1.2), x.1.2)

/-! ## The code-level link -/

section With

variable {m : Type → Type} [Monad m]

/-- **The row counts** (iteration 2, F1): six 4-byte big-endian integers, each range-checked for its
height `r` (`countBits`'s checks: below `2^(r+1)`, and at most `2^r`). -/
def readCounts (heights : List ℕ) : ChanM m (List ℕ) :=
  heights.mapM fun r => do
    let count ← nextInteger (m := m) 4
    requireZero (m := m) (intBits count (r + 1) 32)
    requireZero (m := m) (intBits count r 1 * intBits count 0 r)
    pure count

end With

/-- **What the verdict and the chain read of a run**: its result, and on success the stream, the
cursor, the absorbed bytes, the state, the challenges, and whether every value required zero is. -/
def obsOf {α : Type} (x : Except UniError α × Chan) :
    Except UniError α × Option (Array UInt8 × ℕ × ℕ × Digest × Array E × Bool) :=
  (x.1, match x.1 with
    | .ok _ => some (x.2.data, x.2.cursor, x.2.absorbed, x.2.state, x.2.challenges,
        x.2.zeros.all (· == 0))
    | .error _ => none)

/-- **The main line as a chain program** (code-level link), for the Flock phase `Fl`, with `nV`
values at `t` and `V` batch rounds: after the row counts (`readCounts`, read with `C1`'s root in
round `0`'s absorbed bytes), for each public input and counts the chain program `prog input rows`
on `uniRounds Fl.prog.rounds nV V`, with a tail of five (the three stacks' values, `a`, `b`), runs
as `reduceWith` at the deployment's shape, main line, point claims, up to what the verdict and the
chain read (`obsOf`: the zeros' order aside) (`link`). Its Flock rounds are Flock's (`Fl.link`, by
the composition). -/
structure UniCode (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (nV V : ℕ) where
  prog : Vector UInt8 32 → List ℕ → ChainProg Reduced
  rounds_eq : ∀ input rows, (prog input rows).rounds = uniRounds Fl.prog.rounds nV V
  tail_eq : ∀ input rows, (prog input rows).tail = 5
  link : ∀ (input : Vector UInt8 32) {m : Type → Type} [Monad m] [LawfulMonad m]
    (F : KeccakState → m KeccakState) (c₀ : Chan),
    obsOf <$> ((reduceWith F D.shape (publicWordsOf input.toList) (.flock flockMain) .point).run.run
        c₀) =
      obsOf <$> ((readCounts D.shape.heights >>= fun rows => (prog input rows).run F).run.run c₀)

/-! ## The last link -/

/-- **The last link**: on a completed transcript and its tail, the verifier's checks
(`ZerosVanish`: the batch's terminal `sum + λ³ value · extension + last = 0`) with true claims
(`ClaimsHold`: the stacks' point claims, `A0`'s and `B0`'s at the pending reduction's terminal) make
the batching sumcheck's last claim the identity model's partial sum at its point (`SumState` after
the `V` rounds: `weightAt` the multilinear extension of the cube's weights, the stacks zero-extended,
the pending term `(a + α b) L̂(ρ) ŝ(σ)` its product's value). -/
def UniFinal (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (I : UniIds D Fl)
    (C : UniCode D Fl I.nV I.V) : Prop :=
  ∀ (s : USt) done tl c1 c2, DoneFits (uniRounds Fl.prog.rounds I.nV I.V) done → tl.length = 5 →
    (C.prog s.1 s.2).ZerosVanish done tl → ClaimsHold D ((C.prog s.1 s.2).out done tl) c1 c2 →
      SumState (I.prod s c1 (rd (openedOf Fl.prog.rounds.length c1 c2 done) 0).2
          (fdOf Fl.prog.rounds.length (openedOf Fl.prog.rounds.length c1 c2 done)) c2
          ((rd (openedOf Fl.prog.rounds.length c1 c2 done) (Fl.prog.rounds.length + 1)).2.headD 0)
          (rd (openedOf Fl.prog.rounds.length c1 c2 done) (Fl.prog.rounds.length + 2)).1.2
          ((rd (openedOf Fl.prog.rounds.length c1 c2 done) (Fl.prog.rounds.length + 2)).2.headD 0)
          ((rd (openedOf Fl.prog.rounds.length c1 c2 done)
            (Fl.prog.rounds.length + 2)).2.getD 1 0)).oracle
        (I.target s c1 (rd (openedOf Fl.prog.rounds.length c1 c2 done) 0).2
          (fdOf Fl.prog.rounds.length (openedOf Fl.prog.rounds.length c1 c2 done)) c2
          ((rd (openedOf Fl.prog.rounds.length c1 c2 done) (Fl.prog.rounds.length + 1)).2.headD 0)
          (rd (openedOf Fl.prog.rounds.length c1 c2 done) (Fl.prog.rounds.length + 2)).1.2
          ((rd (openedOf Fl.prog.rounds.length c1 c2 done) (Fl.prog.rounds.length + 2)).2.headD 0)
          ((rd (openedOf Fl.prog.rounds.length c1 c2 done)
            (Fl.prog.rounds.length + 2)).2.getD 1 0))
        (brOf Fl.prog.rounds.length (openedOf Fl.prog.rounds.length c1 c2 done))

/-! ## The Fiat–Shamir layer -/

/-- `N`: every count of the bound at `Q` adversary calls. -/
def uniN (Q : ℕ) : ℕ := 2 ^ 33 + Q

/-- **The univariate verifier's bound** at `Q` adversary calls, rounds' errors at most `e`. -/
noncomputable def uniBound (e : ℝ≥0∞) (Q : ℕ) : ℝ≥0∞ :=
  5 * openingBoundAt 10122 (uniN Q) +
    (uniN Q : ℝ≥0∞) * (((9952 ^ 2 : ℕ) : ℝ≥0∞) * e + ((2 ^ 128 + 8 * uniN Q : ℕ) : ℝ≥0∞) / 2 ^ 256) +
      ((2 ^ 81 + Q : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508

/-- **The Fiat–Shamir layer** (the port of `knowledgeSoundness_listChainK_closed_rpm` to the
univariate verifier): every round-by-round sound protocol on the main line's rounds, its errors at
most `e`, whose state before round `0` is the relation of `C1`'s candidate and whose last state
follows from the verifier's checks with true claims, makes the deployed verifier knowledge sound
for `uniExtractor` with the bound `uniBound e`.

What the port changes in `ListChain`/`ListChainK` (found by this proof; the framework's chain is
`crates/quotient`'s transcript, not the univariate one):
* a scalar is 24 bytes (`nextScalar`), not a 32-byte word with eight zero bytes (`scalarWord`);
  a step's bytes are not whole words, so `chain_unique`'s `32 ∣` separation does not apply;
* a root is its digest's two 16-byte halves each reversed (`nextRoot`, `rootOf`), not
  `rootWords`: `Refers` needs a fourth reading (a fresh answer referred to by `4|H|` digests);
* the seed `name ‖ iv ‖ input` has `80 = 32 + 2 · 24` bytes, the length of every sumcheck round's
  step input (the state and `c0, c2`): the walk back must separate the seed by its fixed prefix
  (`name` and the IV's first half) instead, one more bad answer per query;
* the setup is three trees and the IV hashing their roots and the layout words (`setupTreesWith`,
  `contractIvWith`), not one `Bytes32`; the adversary is given three roots (`rpm_le_kcG` for a
  setup of any type);
* the row counts are read with `C1`'s root (round `0`'s absorbed bytes), the statement's rows:
  the chain's label is not the statement, the first step absorbs part of it.

Its proof also needs, of the deployment: the five stacks at `2^24 … 2^28` words (`C1`, `C2`, the
setup, `A0`, `B0`: `WhirShape.large`, lists at most `largeList ≤ 9952`, `QO ≤ 10122`), the setup's
Keccak-256 calls below `2^26`, the verifier's calls of `π` below `2^80` (`hVπ`), and `uniExtractor`'s
decoders listing the chain's candidates (`fastStacks`, `uniqueStacks`, `decodeStacks` at `C1`'s
`2^μ`, against `Compose`'s `tableCode`). -/
def FsLayer (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (nV V : ℕ) (C : UniCode D Fl nV V) :
    Prop :=
  ∀ (R : RbrPiop (uniRounds Fl.prog.rounds nV V) USt Stk) (e : ℝ≥0∞), (∀ j, R.err j ≤ e) →
    (∀ s c m, R.pre s [] (some c, m) → Rel D s c) →
    (∀ (s : USt) done tl c1 c2, DoneFits (uniRounds Fl.prog.rounds nV V) done → tl.length = 5 →
      (C.prog s.1 s.2).ZerosVanish done tl → ClaimsHold D ((C.prog s.1 s.2).out done tl) c1 c2 →
        ∃ p m ch, openedOf Fl.prog.rounds.length c1 c2 done = p ++ [(m, ch)] ∧ R.post s p m ch) →
    UniKnowledgeSoundness D (uniBound e)

end UniSound
