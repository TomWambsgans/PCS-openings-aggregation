-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The Flock region and its predicate are
-- `formal/Lv42`'s (leanerVM `mumbai` f0393df4's `FlockRegion.Holds`, MIT OR Apache-2.0); the verifier's
-- Flock phase is `formal/UniStatement`'s `Flock.verify` (`crates/leanvm_flock_gas/src/flock_min.rs`).
import UniSound.Prog

/-!
# Flock's interface: the one hypothesis the end-to-end proof takes about BLAKE2s by Flock

**The Flock argument is a separate proof.** The univariate verifier runs Flock (`Flock.verify`,
main line `flockMain`: skip 3, the slices sent, the ring switch) between `γ` and `C2`'s root, on
`C1`'s column `q_flock`; Flock emits three claims: on `q_flock` (the ring switch's
`Σ_k c_k q̂_flock(φ^k(p)) = target`, one of `C1`'s relations), and on the setup's matrices `A0`,
`B0` (one point claim each). The end theorem (`UniSound.Final`) takes **one** hypothesis about it,
`FlockSound κ` below (`κ` the `BLAKE2S` table's log-height, `q_flock` of `2^(8 + κ)` cells), whose
fields are what the Flock proof must provide:

* **`prog`, `link`**: the code-level link. `Flock.verify F (14 + κ) flockMain` is a chain program
  (`UniSound.Prog`): its rounds (`prog.rounds`, no root, the first the zerocheck's sampled
  coordinates with no message), the values it requires zero, and its result, each a pure function
  of its transcript; `link` is the equation of channel programs, for every lawful monad and
  permutation (an unfolding of `flock_min.rs`'s transcription).
* **`S`, `err`, `S_nil`, `step`, `finish`**: Flock's **round-by-round** soundness, on its own
  transcript (`Done`: the messages and challenges of its completed rounds), for every column
  `qf` of `2^(8 + κ)` cells: a state `S qf done`, true at the start only if `qf` satisfies
  `FlockRegion.Holds` (`S_nil`: the BLAKE2s R1CS on every block of `2^14` bits, the constant
  position `1`); round `j` turns it from false to true with probability at most `err j` over its
  `ns + 1` uniform challenges, for every transcript before it and every message (`step`); and it
  is true at the end when Flock's checks pass (the values it requires zero are zero) and the
  claims it emits are true of `qf`, `A0` and `B0` (`finish`).

**Why round by round.** The verifier is non-interactive: Flock's challenges are Keccak-256 of the
transcript, so a prover may re-draw them by re-hashing. A bound "except with probability `ε` over
Flock's challenges" for an interactive prover does not survive Fiat–Shamir; a round-by-round bound
does, and the chain (`Compose.ListChainK`, `Piop`) takes exactly that: each of Flock's rounds is a
round of the chain, its error `err j` multiplied by `C1`'s list bound (the candidates of the one
root before it) and union-bounded over the adversary's queries. Over an interactive run the same
fields give the statement asked for, with `εFlock = Σ_j err j` per candidate (`flockError`).

In the end theorem this structure is a hypothesis **named for Flock** (`hFlock : FlockSound κ`),
and its errors enter `ε` as `flockError`.
-/

namespace UniSound

open LeanVM.Parameters LeanVM.Semantics UniStatement
open scoped ENNReal

/-! ## Flock's predicate and the claims it emits -/

/-- **What the Flock phase establishes** of a column of `2^(8 + κ)` cells (Lv42's
`FlockRegion.Holds` at `kBatch = κ`): every block of `2^14` bits, packed 64 to a cell, satisfies
the BLAKE2s R1CS (`blake2sFlockSpec`) and holds `1` at the constant position. -/
def FlockHolds (κ : ℕ) (qf : LeanVM.Protocol.Column (8 + κ)) : Prop :=
  Lv42.Protocol.BlockR1CS.BatchHolds Lv42.Protocol.Blake2sFlock.blake2sFlockSpec.r1cs
    Lv42.Parameters.Flock.constPos (Lv42.Protocol.bitTable qf)

/-- `eq(p, x)` on the first `n` coordinates, `x` a cube point by its bits (low first):
`Π_k (1 + p_k + x_k)`. -/
def cubeEq (p : List E) (n x : ℕ) : E :=
  ∏ k ∈ Finset.range n, (1 + p.getD k 0 + if x.testBit k then 1 else 0)

/-- **The multilinear extension over `E`** of a column of `K` at a point (low coordinate first):
`Σ_x eq(p, x) q(x)`. -/
noncomputable def mleE {n : ℕ} (q : LeanVM.Protocol.Column n) (p : List E) : E :=
  ∑ x : Fin (2 ^ n), cubeEq p n x.val * ofK (q.values.get x)

/-- The multilinear extension of a table of `2^n` words given as an array (words past its end read
`0`). -/
noncomputable def mleArr (a : Array K) (n : ℕ) (p : List E) : E :=
  ∑ x : Fin (2 ^ n), cubeEq p n x.val * ofK (a.getD x.val 0)

/-- A point's coordinates squared `k` times (`twistedPoints`' `k`-th twist): `φ^k(p)`. -/
def twist (p : List E) (k : ℕ) : List E := p.map fun x ↦ sqn x k

/-- **Flock's claim on `q_flock` holds**: the ring switch's `Σ_{k<64} c_k q̂(φ^k(p)) = target`, `c_k`
the coefficients of the map (`ringSwitchCoefficients`, the relation the verifier pushes on `C1`).
The bit-slice end (extension B) is not the main line's; it holds of nothing here. -/
noncomputable def FlockEndHolds {κ : ℕ} (qf : LeanVM.Protocol.Column (8 + κ)) (r : Flock.Reduced) :
    Prop :=
  match r.end_ with
  | .ring map target =>
    ∑ k ∈ Finset.range 64, (Flock.ringSwitchCoefficients map).getD k 0 * mleE qf (twist r.point k) =
      target
  | .combination _ _ => False

/-- **Flock's claims on the setup's matrices hold**: `Â0(p) = a`, `B̂0(p) = b` on the `2^28`-word
stacks (`flockMatrixStack`). -/
noncomputable def FlockMatricesHold (r : Flock.Reduced) : Prop :=
  mleArr (flockMatrixStack true) matrixVars r.matrices.point = r.matrices.a ∧
    mleArr (flockMatrixStack false) matrixVars r.matrices.point = r.matrices.b

/-! ## The interface -/

/-- **The Flock hypothesis** (the one assumption about BLAKE2s by Flock), for `q_flock` of
`2^(8 + κ)` cells: the main-line Flock phase is a chain program (`link`), round-by-round sound
from `FlockHolds` to its emitted claims (`S`, `err`, `S_nil`, `step`, `finish`). -/
structure FlockSound (κ : ℕ) where
  /-- Flock's phase as a chain program: its rounds, its checks and its result. -/
  prog : ChainProg Flock.Reduced
  /-- No round has a root; nothing is read after the last challenge. -/
  rounds_root : ∀ s ∈ prog.rounds, s.root = false
  tail_eq : prog.tail = 0
  /-- **The code-level link**: `Flock.verify` at `14 + κ` variables, main line, is `prog`'s
  canonical channel program, for every lawful monad and permutation. -/
  link : ∀ {m : Type → Type} [Monad m] [LawfulMonad m] (F : KeccakState → m KeccakState),
    Flock.verify F (blake2sR1csLogSize + κ) flockMain = prog.run F
  /-- Flock's state after its completed rounds `done`, for the column `qf`. -/
  S : LeanVM.Protocol.Column (8 + κ) → Done → Prop
  /-- Round `j`'s error. -/
  err : ℕ → ℝ≥0∞
  /-- At the start the state holds only if the column satisfies Flock's predicate. -/
  S_nil : ∀ qf, S qf [] → FlockHolds κ qf
  /-- **Round by round**: round `j`'s challenges turn the state from false to true with
  probability at most `err j`, for every transcript before it and every message fitting it. -/
  step : ∀ (j : ℕ) (hj : j < prog.rounds.length) (qf : LeanVM.Protocol.Column (8 + κ))
    (done : Done) (msg : UMsg), DoneFits (prog.rounds.take j) done →
      msg.Fits (prog.rounds[j]'hj) →
        Pr{let c ← Compose.draws E ((prog.rounds[j]'hj).ns + 1)}[
          ¬ S qf done ∧ S qf (done ++ [(msg, c)])] ≤ err j
  /-- **At the end**: Flock's checks pass and its claims on `qf`, `A0`, `B0` hold, so the state
  holds. -/
  finish : ∀ (qf : LeanVM.Protocol.Column (8 + κ)) (done : Done), DoneFits prog.rounds done →
    prog.ZerosVanish done [] → FlockEndHolds qf (prog.out done []) →
      FlockMatricesHold (prog.out done []) → S qf done

/-- **Flock's error per candidate**: the sum of its rounds' errors (the bound over an interactive
run; in the chain each round enters on its own, `err j` times the list bound of `C1`). -/
noncomputable def FlockSound.flockError {κ : ℕ} (h : FlockSound κ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range h.prog.rounds.length, h.err j

end UniSound
