-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.SimSemantics.QueryImpl.Compose
import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# The non-interactive proof and its simulator, in the random-oracle model

The prover of `crates/quotient` is a Fiat–Shamir transform: the reduction's Keccak-256 chain
(`transcript.rs`) and the three WHIR openings' duplex sponge (`fiat_shamir`), with Merkle trees
(`pcs::merkle`) over the committed tables. In the random-oracle model every hash is one oracle
`I →ₒ O` (lazily sampled, VCVio's `randomOracle`); `Instance.lean` takes `I` the Keccak-256 inputs
and the duplex states, `O` a Keccak-256 digest and a duplex state.

**The prover as a public program.** A prover is described by a fixed program `skel` (its
*skeleton*) that never sees the secret: it asks for what it needs through four operations
(`Op`), and an *implementation* answers them.

* `pub t`: a random-oracle query (a Merkle node, a proof-of-work attempt, a public table's leaf,
  the seeds, everything that is not a challenge);
* `chal t`: a Fiat–Shamir query: a random-oracle query whose answer is the next challenge (a
  chain state of `transcript.rs`, a duplex output of `fiat_shamir`). The `c`-th one is step `c`;
  past `n` of them a `chal` is a plain query;
* `msg`: the prover's next message of the interactive protocol (the values it absorbs, the lane
  rounds, the folded tables and their rows, the opened rows of the secret tables), given the
  challenges so far;
* `leaf k x`: the digest of leaf `x` of the secret table `k` (the hash of its row), once the
  challenges the table depends on are drawn (`cK k` of them).

The **real prover** (`implReal`) answers `pub` and `chal` from the random oracle, `msg` with the
honest message (`Proto.msgFn`) of the secret and the challenges so far, and `leaf k x` with the
oracle's answer at the leaf's row (`Proto.rowFn`). Everything secret is in the implementation.

**The simulator** (`sim`) draws the `n` challenges first (`uniformList`), then the interactive
view from them (`simV`, the honest-verifier simulator of `Proto.view`), and runs the same skeleton
with `implView`: `pub` from the oracle, `chal` *programmed* with the drawn challenges (written into
the oracle's cache), `msg` from the simulated view, `leaf k x` from the oracle at the simulated row
if the position is opened, and a fresh uniform digest (kept private, never written into the
oracle) if it is not: the siblings and the roots then hash fresh values. It outputs the proof and
the oracle's cache, which the distinguisher then queries.

The state (`St`) carries the oracle's cache, the challenges so far (`hist`), the private digests
(`priv`), the inputs written into the cache (`log`, for counting) and a flag (`fs`) that records a
Fiat–Shamir query whose input was already answered; none of these but the cache and `hist`
changes any answer.
-/

open OracleComp OracleSpec

namespace QuotientZk

/-! ## Operations and state -/

/-- The prover's operations. -/
inductive Op (I K X : Type) where
  /-- A random-oracle query. -/
  | pub (t : I)
  /-- The prover's next message. -/
  | msg
  /-- The digest of leaf `x` of the secret table `k`. -/
  | leaf (k : K) (x : X)
  /-- A Fiat–Shamir query: its answer is the next challenge. -/
  | chal (t : I)

/-- What each operation returns. -/
@[reducible] def opRange (O M : Type) {I K X : Type} : Op I K X → Type
  | .pub _ => O
  | .msg => M
  | .leaf _ _ => O
  | .chal _ => O

/-- The operations as an oracle specification. -/
@[reducible] def OpSpec (I O M K X : Type) : OracleSpec (Op I K X) := opRange O M

/-- The state of every implementation. -/
structure St (I O K X : Type) where
  /-- The random oracle's cache. -/
  cache : (I →ₒ O).QueryCache
  /-- The Fiat–Shamir answers so far, in order. -/
  hist : List O
  /-- The private digests of unopened leaves (the simulator's; the real prover keeps none). -/
  priv : List ((K × X) × O)
  /-- The inputs written into the cache, newest first. -/
  log : List I
  /-- Whether a Fiat–Shamir query found its input already answered. -/
  fs : Bool

variable {S I O M K X Pf : Type}

/-- The initial state: the oracle holds the entries `c₀` (whatever was asked of it before). -/
def St.init (c₀ : List (I × O)) [DecidableEq I] : St I O K X where
  cache := c₀.foldr (fun e c => c.cacheQuery e.1 e.2) ∅
  hist := []
  priv := []
  log := []
  fs := false

/-! ## The protocol -/

/-- **The interactive protocol, as the prover sees it.** For a fixed statement and witness, the
prover's randomness is `S` (the masks and the padding, uniform). `n` Fiat–Shamir steps; after `c`
challenges (the oracle's answers `h`, a list of length `c`) the prover's next message is
`msgFn s h`; the secret table `k` is committed after `cK k` challenges, and its leaf `x` hashes the
row `rowFn s h k x` (`h` its `cK k` challenges); with all the challenges `σ`, the positions opened
are `opened σ`. -/
structure Proto (S I O M K X : Type) where
  n : ℕ
  msgFn : S → List O → M
  cK : K → ℕ
  rowFn : S → List O → K → X → I
  opened : List O → K → X → Bool

/-- The interactive view: every message (`msg c` after `c` challenges) and the rows of the opened
positions (`row k x`; a default value at the other positions). -/
structure View (M I K X : Type) where
  msg : ℕ → M
  row : K → X → I

namespace Proto

variable (P : Proto S I O M K X)

/-- The rows of the secret tables, given all the challenges. -/
def rows (s : S) (σ : List O) (k : K) (x : X) : I := P.rowFn s (σ.take (P.cK k)) k x

/-- **The honest-verifier view** of the interactive protocol at the challenges `σ`: the prover's
messages and its opened rows. -/
def view [Inhabited I] (s : S) (σ : List O) : View M I K X where
  msg c := P.msgFn s (σ.take c)
  row k x := if P.opened σ k x then P.rows s σ k x else default

end Proto

/-! ## Uniform challenges -/

/-- `m` uniform values. -/
def uniformList (O : Type) [SampleableType O] : ℕ → ProbComp (List O)
  | 0 => pure []
  | m + 1 => do
    let u ← $ᵗ O
    let l ← uniformList O m
    return u :: l

/-! ## The implementations -/

section Impl

variable [DecidableEq I] [SampleableType O] [Inhabited O]

/-- One random-oracle query against the state's cache (a new input is logged). -/
def roStep (t : I) : StateT (St I O K X) ProbComp O := fun st =>
  match st.cache t with
  | some u => pure (u, st)
  | none => do
    let u ← $ᵗ O
    return (u, { st with cache := st.cache.cacheQuery t u, log := t :: st.log })

/-- A programmed Fiat–Shamir answer `u` at `t`: written into the cache, appended to the
challenges; the flag records an input already answered. -/
def progStep (t : I) (u : O) : StateT (St I O K X) ProbComp O := fun st =>
  pure (u, { st with
    cache := st.cache.cacheQuery t u
    hist := st.hist ++ [u]
    log := t :: st.log
    fs := st.fs || (st.cache t).isSome })

variable (P : Proto S I O M K X)

/-- **The real prover**: everything from the random oracle and the secret `s`. -/
def implReal (s : S) : QueryImpl (OpSpec I O M K X) (StateT (St I O K X) ProbComp)
  | .pub t => roStep t
  | .msg => fun st => pure (P.msgFn s st.hist, st)
  | .leaf k x => fun st =>
    if st.hist.length < P.cK k then pure (default, st)
    else roStep (P.rowFn s (st.hist.take (P.cK k)) k x) st
  | .chal t => fun st =>
    if st.hist.length < P.n then
      match st.cache t with
      | some u => pure (u, { st with hist := st.hist ++ [u], fs := true })
      | none => do
        let u ← $ᵗ O
        return (u, { st with
          cache := st.cache.cacheQuery t u
          hist := st.hist ++ [u]
          log := t :: st.log })
    else roStep t st

/-- The real prover with fresh Fiat–Shamir answers: a `chal` draws a new answer even when its
input was answered before (and then raises the flag). -/
def implFresh (s : S) : QueryImpl (OpSpec I O M K X) (StateT (St I O K X) ProbComp)
  | .pub t => roStep t
  | .msg => fun st => pure (P.msgFn s st.hist, st)
  | .leaf k x => fun st =>
    if st.hist.length < P.cK k then pure (default, st)
    else roStep (P.rowFn s (st.hist.take (P.cK k)) k x) st
  | .chal t => fun st =>
    if st.hist.length < P.n then do
      let u ← $ᵗ O
      progStep t u st
    else roStep t st

/-- The real prover with the challenges `σ` drawn in advance: the `c`-th `chal` is programmed
with `σ[c]`, and the messages and rows read `σ`. -/
def implUp (σ : List O) (s : S) : QueryImpl (OpSpec I O M K X) (StateT (St I O K X) ProbComp)
  | .pub t => roStep t
  | .msg => fun st => pure (P.msgFn s (σ.take st.hist.length), st)
  | .leaf k x => fun st =>
    if st.hist.length < P.cK k then pure (default, st)
    else roStep (P.rows s σ k x) st
  | .chal t => fun st =>
    if st.hist.length < P.n then progStep t (σ.getD st.hist.length default) st
    else roStep t st

/-- The leaf digests of the unopened positions kept apart: the oracle's answer at a row is the
cache's, or else the digest of an unopened position with that row (`unionLook`). Its run is the
`implUp` run read through the union of the two (`Split.lean`). -/
def unionLook (rows : K → X → I) (st : St I O K X) (r : I) : Option O :=
  match st.cache r with
  | some u => some u
  | none => (st.priv.find? fun e => decide (rows e.1.1 e.1.2 = r)).map Prod.snd

/-- A random-oracle query through `unionLook`; an answer from a private digest is written into
the cache. -/
def roSplit (rows : K → X → I) (r : I) : StateT (St I O K X) ProbComp O := fun st =>
  match st.cache r with
  | some u => pure (u, st)
  | none =>
    match (st.priv.find? fun e => decide (rows e.1.1 e.1.2 = r)).map Prod.snd with
    | some u => pure (u, { st with cache := st.cache.cacheQuery r u, log := r :: st.log })
    | none => do
      let u ← $ᵗ O
      return (u, { st with cache := st.cache.cacheQuery r u, log := r :: st.log })

variable [DecidableEq K] [DecidableEq X]

/-- Whether a position has a private digest. -/
def hasPriv (st : St I O K X) (p : K × X) : Bool := (st.priv.lookup p).isSome

/-- `implUp` with the unopened leaves' digests kept apart (`Split.lean`). -/
def implSplit (σ : List O) (s : S) : QueryImpl (OpSpec I O M K X) (StateT (St I O K X) ProbComp)
  | .pub t => roSplit (P.rows s σ) t
  | .msg => fun st => pure (P.msgFn s (σ.take st.hist.length), st)
  | .leaf k x => fun st =>
    if st.hist.length < P.cK k then pure (default, st)
    else if P.opened σ k x then roSplit (P.rows s σ) (P.rows s σ k x) st
    else
      match unionLook (P.rows s σ) st (P.rows s σ k x) with
      | some u => pure (u, if hasPriv st (k, x) then st else { st with priv := st.priv ++ [((k, x), u)] })
      | none => do
        let u ← $ᵗ O
        return (u, { st with priv := st.priv ++ [((k, x), u)] })
  | .chal t => fun st =>
    if st.hist.length < P.n then progStep t (σ.getD st.hist.length default) st
    else roSplit (P.rows s σ) t st

/-- **The simulator's implementation**, from the challenges `σ` and a view `v`: `chal` programmed
with `σ`, `msg` from `v`, an opened leaf from the oracle at `v`'s row, an unopened leaf a fresh
private digest. -/
def implView (σ : List O) (v : View M I K X) :
    QueryImpl (OpSpec I O M K X) (StateT (St I O K X) ProbComp)
  | .pub t => roStep t
  | .msg => fun st => pure (v.msg st.hist.length, st)
  | .leaf k x => fun st =>
    if st.hist.length < P.cK k then pure (default, st)
    else if P.opened σ k x then roStep (v.row k x) st
    else
      match st.priv.lookup (k, x) with
      | some u => pure (u, st)
      | none => do
        let u ← $ᵗ O
        return (u, { st with priv := st.priv ++ [((k, x), u)] })
  | .chal t => fun st =>
    if st.hist.length < P.n then progStep t (σ.getD st.hist.length default) st
    else roStep t st

end Impl

/-! ## The games -/

section Games

variable [DecidableEq I] [SampleableType O] [Inhabited O] [DecidableEq K] [DecidableEq X]
variable (P : Proto S I O M K X)

/-- The distinguisher's oracle queries, as `pub` operations. -/
def pubImpl : QueryImpl (I →ₒ O) (OracleComp (OpSpec I O M K X)) :=
  fun t => liftM ((OpSpec I O M K X).query (.pub t))

/-- **The real prover**: the proof, and the oracle's cache after it, for the secret `s`, from an
oracle that holds `c₀`. -/
def prove (s : S) (skel : OracleComp (OpSpec I O M K X) Pf) (c₀ : List (I × O)) :
    ProbComp (Pf × (I →ₒ O).QueryCache) :=
  (fun z => (z.1, z.2.cache)) <$> (simulateQ (implReal P s) skel).run (St.init c₀)

/-- **The simulator.** No secret: the challenges first, then the simulated view `simV σ`, then the
skeleton with the challenges programmed, the view's messages and opened rows, and fresh private
digests at the unopened leaves. It outputs the proof and the oracle's cache. -/
def sim (simV : List O → ProbComp (View M I K X)) (skel : OracleComp (OpSpec I O M K X) Pf)
    (c₀ : List (I × O)) : ProbComp (Pf × (I →ₒ O).QueryCache) := do
  let σ ← uniformList O P.n
  let v ← simV σ
  let z ← (simulateQ (implView P σ v) skel).run (St.init c₀)
  return (z.1, z.2.cache)

/-- **The real game**: uniform randomness `s`, the honest proof, then the distinguisher `D` with
the random oracle from where the prover left it. -/
def realGame [SampleableType S] (skel : OracleComp (OpSpec I O M K X) Pf) (c₀ : List (I × O))
    (D : Pf → OracleComp (I →ₒ O) Bool) : ProbComp Bool := do
  let s ← $ᵗ S
  let z ← prove P s skel c₀
  (simulateQ randomOracle (D z.1)).run' z.2

/-- **The simulated game**: the simulator's proof, then `D` with the random oracle from the
simulator's cache. -/
def simGame (simV : List O → ProbComp (View M I K X)) (skel : OracleComp (OpSpec I O M K X) Pf)
    (c₀ : List (I × O)) (D : Pf → OracleComp (I →ₒ O) Bool) : ProbComp Bool := do
  let z ← sim P simV skel c₀
  (simulateQ randomOracle (D z.1)).run' z.2

end Games

end QuotientZk
