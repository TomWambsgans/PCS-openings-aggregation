-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The Flock region and its predicate are
-- `formal/Lv42`'s (leanerVM `mumbai` f0393df4's `FlockRegion.Holds`, MIT OR Apache-2.0); the verifier's
-- Flock phase is `formal/UniStatement`'s `Flock.verify` (`crates/leanvm_flock_gas/src/flock_min.rs`).
import UniSound.Prog

/-!
# Flock's interface: the one hypothesis the end-to-end proof takes about BLAKE2s by Flock

**The Flock argument is a separate proof.** The univariate verifier (iteration 2, main line
`flockMain = ⟨3, .tower⟩`, point claims) runs Flock's front (`Flock.verifyDeferred`: the
zerocheck with a skip of 3, the lincheck, the 64 slices, the ring map in tower order) between `γ`
and `C2`'s root, on `C1`'s column `q_flock`; it leaves

* the **ring switch's claim** on `q_flock` (`End.ring map target`: `Σ_k d_k q̂(φ^k(p)) = target`,
  `d = towerCoefficients map`, one of `C1`'s relations: the term of twist `ringTwist`), and
* the **matrices' reduction, pending** (`Pending`, lever 4a): the claim
  `Σ_(x, y) G(x, y) L̂(x) ŝ(y) = claim`, `G = Â0 + α B̂0` at the row and column points, whose
  `k + 6` rounds the batching sumcheck runs as its `λ³` term; its terminal hands `PCS_OPEN` the
  claims on `A0`, `B0`.

The end theorem (`UniSound.Final`) takes **one** hypothesis about Flock, `FlockSound κ` below (`κ`
the `BLAKE2S` table's log-height, `q_flock` of `2^(8 + κ)` cells), whose fields the Flock proof must
provide:

* **`prog`, `link`**: the code-level link. `Flock.verifyDeferred F (14 + κ) flockMain` is a chain
  program (`UniSound.Prog`): its rounds (no root; the first the zerocheck's sampled coordinates with
  no message), and its result (the slices' point, the end, the pending reduction), each a pure
  function of its transcript; `link` is the equation of channel programs, for every lawful monad
  and permutation (an unfolding of `flock_min.rs`'s transcription).
* **`S`, `err`, `S_nil`, `step`, `finish`**: Flock's **round-by-round** soundness, on its own
  transcript (`Done`: the messages and challenges of its completed rounds), for every column `qf`
  of `2^(8 + κ)` cells: a state `S qf done`, true at the start only if `qf` satisfies
  `FlockRegion.Holds` (`S_nil`: the BLAKE2s R1CS on every block of `2^14` bits, the constant
  position `1`); round `j` turns it from false to true with probability at most `err j` over its
  `ns + 1` uniform challenges, for every transcript before it and every message (`step`); and it
  is true at the end when the ring switch's claim holds of `qf` and the pending reduction's claim
  is its sum (`finish`; `FlockEndHolds`, `PendingHolds`). The pending sum's own rounds are the
  batching sumcheck's (`UniSound.Sumcheck`, generic), not Flock's.

**Why round by round.** The verifier is non-interactive: Flock's challenges are Keccak-256 of the
transcript, so a prover may re-draw them by re-hashing. A bound "except with probability `ε` over
Flock's challenges" for an interactive prover does not survive Fiat–Shamir; a round-by-round bound
does, and the chain (`Compose.ListChainK`, `Piop`) takes exactly that: each of Flock's rounds is a
round of the chain, its error `err j` multiplied by `C1`'s list bound (the candidates of the one
root before it) and union-bounded over the adversary's queries. Over an interactive run the same
fields give the statement asked for, with `εFlock = Σ_j err j` per candidate (`flockError`).

In the end theorem this structure is a hypothesis **named for Flock** (`hFlock : FlockSound κ`),
and its errors enter `ε` through the rounds' bound.
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

/-- **Flock's claim on `q_flock` holds**: the ring switch's `Σ_{k<64} d_k q̂(φ^k(p)) = target`, `d_k`
the tower-order coefficients of the map (`towerCoefficients`, the weight of the relation the verifier
pushes on `C1`, twist `ringTwist`). Without an end, or with the bit-slice end (extension B), it holds
of nothing here. -/
noncomputable def FlockEndHolds {κ : ℕ} (qf : LeanVM.Protocol.Column (8 + κ))
    (r : List E × Option Flock.End × Flock.Pending) : Prop :=
  match r.2.1 with
  | some (.ring map target) =>
    ∑ k ∈ Finset.range 64, (Flock.towerCoefficients map).getD k 0 * mleE qf (twist r.1 k) = target
  | _ => False

/-- Bit `i` of `u`, the cube point's coordinate, in `E`. -/
def bitsE (u n : ℕ) : List E := (List.range n).map fun i => if u.testBit i then 1 else 0

/-- **A claim on Flock's matrices holds**: `Â0(p) = a`, `B̂0(p) = b` on the `2^28`-word stacks
(`flockMatrixStack`). -/
noncomputable def MatrixHolds (mc : Flock.MatrixClaim) : Prop :=
  mleArr (flockMatrixStack true) matrixVars mc.point = mc.a ∧
    mleArr (flockMatrixStack false) matrixVars mc.point = mc.b

/-- **The pending reduction's summand** at the cube point `u` of its `k + 6` variables (`x` the low
`k` bits, `y` the next six): `G(x, y) = Â0 + α B̂0` at `(x, row_low, chi_in, y, chi_in')`. -/
noncomputable def Pending.G (p : Flock.Pending) (u : ℕ) : E :=
  let pt := bitsE (u % 2 ^ p.k) p.k ++ p.rowLow ++ p.chiIn ++ bitsE (u / 2 ^ p.k) Flock.packing ++
    p.chiInPrime
  mleArr (flockMatrixStack true) matrixVars pt + p.alpha * mleArr (flockMatrixStack false) matrixVars pt

/-- `L(x) s(y)` at the cube point `u`: the skip's Lagrange weight (`1` without a skip) and the
slice. -/
def Pending.L (p : Flock.Pending) (u : ℕ) : E :=
  (if p.k > 0 then p.skipWeights.getD (u % 2 ^ p.k) 0 else 1) * (p.slices.getD []).getD (u / 2 ^ p.k) 0

/-- **The pending reduction's claim is its sum**: `claim = Σ_(x, y) G(x, y) L̂(x) ŝ(y)` over the
`2^(k + 6)` cube points. -/
def PendingHolds (p : Flock.Pending) : Prop :=
  p.claim = ∑ u ∈ Finset.range (2 ^ p.rounds), Pending.G p u * Pending.L p u

/-! ## The interface -/

/-- **The Flock hypothesis** (the one assumption about BLAKE2s by Flock), for `q_flock` of
`2^(8 + κ)` cells: the main line's Flock front is a chain program (`link`), round-by-round sound
from `FlockHolds` to its claims (`S`, `err`, `S_nil`, `step`, `finish`). -/
structure FlockSound (κ : ℕ) where
  /-- Flock's front as a chain program: its rounds and its result. -/
  prog : ChainProg (List E × Option Flock.End × Flock.Pending)
  /-- No round has a root; nothing is read after the last challenge. -/
  rounds_root : ∀ s ∈ prog.rounds, s.root = false
  tail_eq : prog.tail = 0
  /-- **The code-level link**: `Flock.verifyDeferred` at `14 + κ` variables, main line, is `prog`'s
  canonical channel program, for every lawful monad and permutation. -/
  link : ∀ {m : Type → Type} [Monad m] [LawfulMonad m] (F : KeccakState → m KeccakState),
    Flock.verifyDeferred F (blake2sR1csLogSize + κ) flockMain = prog.run F
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
  /-- **At the end**: the ring switch's claim on `qf` holds and the pending reduction's claim is its
  sum, so the state holds. -/
  finish : ∀ (qf : LeanVM.Protocol.Column (8 + κ)) (done : Done), DoneFits prog.rounds done →
    FlockEndHolds qf (prog.out done []) → PendingHolds (prog.out done []).2.2 → S qf done

/-- **Flock's error per candidate**: the sum of its rounds' errors (the bound over an interactive
run; in the chain each round enters on its own, `err j` times the list bound of `C1`). -/
noncomputable def FlockSound.flockError {κ : ℕ} (h : FlockSound κ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range h.prog.rounds.length, h.err j

end UniSound
