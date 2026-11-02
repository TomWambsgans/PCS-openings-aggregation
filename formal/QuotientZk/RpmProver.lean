-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): `common`'s folding of a random oracle into a state (`Common.foldRO`) and its
-- state projection (`Common.map_run_simulateQ_evalDistEq_of_inv`).
import QuotientZk.RpmTape

/-!
# The prover with any hash

`implReal` (`Rom/Defs.lean`) answers the prover's operations from a random oracle kept in its
state. Here the same prover asks an external hash `h : I → OracleComp spec O` (`implHash`): a
random-oracle or Fiat–Shamir query is one hash query, a leaf's digest the hash of its row, and the
state is the list of challenges so far. With `h` the random oracle's query, run in the
random-oracle model, it is `implReal` (`romImpl_proverWith`: the proof and the oracle's cache
after it are `prove`'s); with `h` Keccak-256 over a permutation, it is the prover of the
random-permutation model (`Rpm.lean`). Simulating the hash's oracle commutes with the prover
(`simulateQ_proverWith`).
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace QuotientZk

set_option linter.unusedSectionVars false

variable {S I O M K X Pf : Type}

section Hash

variable [Inhabited O] (P : Proto S I O M K X)

/-- **The prover asking a hash `h`**: `pub` and `chal` are hash queries (the first `n` answers of
`chal` the challenges, kept in the state), `msg` the honest message from the challenges so far,
`leaf k x` the hash of the row once its challenges are drawn. -/
def implHash {ι : Type} {spec : OracleSpec.{0, 0} ι} (h : I → OracleComp spec O) (s : S) :
    QueryImpl (OpSpec I O M K X) (StateT (List O) (OracleComp spec))
  | .pub t => fun hist ↦ (fun u ↦ (u, hist)) <$> h t
  | .msg => fun hist ↦ pure (P.msgFn s hist, hist)
  | .leaf k x => fun hist ↦
    if hist.length < P.cK k then pure (default, hist)
    else (fun u ↦ (u, hist)) <$> h (P.rowFn s (hist.take (P.cK k)) k x)
  | .chal t => fun hist ↦
    (fun u ↦ (u, if hist.length < P.n then hist ++ [u] else hist)) <$> h t

/-- **The prover** of the secret `s` with the hash `h`: the skeleton's proof. -/
def proverWith {ι : Type} {spec : OracleSpec.{0, 0} ι} (h : I → OracleComp spec O) (s : S)
    (skel : OracleComp (OpSpec I O M K X) Pf) : OracleComp spec Pf :=
  (simulateQ (implHash P h s) skel).run' []

/-- Simulating the hash's oracle, step by step. -/
theorem mapStateTBase_implHash {ι ι' : Type} {spec : OracleSpec.{0, 0} ι}
    {spec' : OracleSpec.{0, 0} ι'} (impl : QueryImpl spec (OracleComp spec'))
    (h : I → OracleComp spec O) (s : S) :
    impl.mapStateTBase (implHash P h s) = implHash P (fun t ↦ simulateQ impl (h t)) s := by
  funext op
  cases op with
  | pub t => funext hist; simp [QueryImpl.mapStateTBase, implHash, StateT.mk, StateT.run]
  | msg => funext hist; simp [QueryImpl.mapStateTBase, implHash, StateT.mk, StateT.run]
  | leaf k x =>
    funext hist
    by_cases hk : hist.length < P.cK k <;>
      simp [QueryImpl.mapStateTBase, implHash, StateT.mk, StateT.run, hk]
  | chal t => funext hist; simp [QueryImpl.mapStateTBase, implHash, StateT.mk, StateT.run]

/-- **Simulating the hash's oracle commutes with the prover.** -/
theorem simulateQ_proverWith {ι ι' : Type} {spec : OracleSpec.{0, 0} ι}
    {spec' : OracleSpec.{0, 0} ι'} (impl : QueryImpl spec (OracleComp spec'))
    (h : I → OracleComp spec O) (s : S) (skel : OracleComp (OpSpec I O M K X) Pf) :
    simulateQ impl (proverWith P h s skel) =
      proverWith P (fun t ↦ simulateQ impl (h t)) s skel := by
  unfold proverWith
  rw [StateT.run'_eq, StateT.run'_eq, simulateQ_map, QueryImpl.simulateQ_mapStateTBase_run,
    mapStateTBase_implHash]

end Hash

/-! ## With the random oracle, the prover is `implReal` -/

section Rom

variable [DecidableEq I] [SampleableType O] [Inhabited O] (P : Proto S I O M K X)

/-- The random oracle's query, as a hash. -/
abbrev roHash (t : I) : OracleComp (unifSpec + (I →ₒ O)) O := Common.hq (hs := I →ₒ O) t

/-- The challenges and the cache of a state. -/
def histCache (st : St I O K X) : List O × (I →ₒ O).QueryCache := (st.hist, st.cache)

theorem roStep_run (t : I) (st : St I O K X) :
    (QuotientZk.roStep t).run st =
      (match st.cache t with
        | some u => pure (u, st)
        | none => do
          let u ← $ᵗ O
          return (u, { st with cache := st.cache.cacheQuery t u, log := t :: st.log })) := rfl

/-- A random-oracle step of `implReal`, read on the challenges and the cache. -/
theorem roStep_histCache (t : I) (st : St I O K X) :
    Prod.map id histCache <$> (QuotientZk.roStep t).run st =
      (fun z ↦ (z.1, (st.hist, z.2))) <$> Common.roStep (hs := I →ₒ O) t st.cache := by
  rw [roStep_run]
  rcases h : st.cache t with _ | u
  · simp [Common.roStep, h, histCache]
  · simp [Common.roStep, h, histCache]

theorem implHash_pub_run {ι : Type} {spec : OracleSpec.{0, 0} ι} (h : I → OracleComp spec O)
    (s : S) (t : I) (hist : List O) :
    (implHash P h s (.pub t)).run hist = (fun u ↦ (u, hist)) <$> h t := rfl

theorem implHash_msg_run {ι : Type} {spec : OracleSpec.{0, 0} ι} (h : I → OracleComp spec O)
    (s : S) (hist : List O) :
    (implHash P h s .msg).run hist = pure (P.msgFn s hist, hist) := rfl

theorem implHash_leaf_run {ι : Type} {spec : OracleSpec.{0, 0} ι} (h : I → OracleComp spec O)
    (s : S) (k : K) (x : X) (hist : List O) :
    (implHash P h s (.leaf k x)).run hist =
      if hist.length < P.cK k then pure (default, hist)
      else (fun u ↦ (u, hist)) <$> h (P.rowFn s (hist.take (P.cK k)) k x) := rfl

theorem implHash_chal_run {ι : Type} {spec : OracleSpec.{0, 0} ι} (h : I → OracleComp spec O)
    (s : S) (t : I) (hist : List O) :
    (implHash P h s (.chal t)).run hist =
      (fun u ↦ (u, if hist.length < P.n then hist ++ [u] else hist)) <$> h t := rfl

/-- **One step of `implReal`**, read on the challenges and the cache, is one step of the prover
asking the random oracle, the oracle folded into the state. -/
theorem implReal_histCache (s : S) (op : Op I K X) (st : St I O K X) :
    Prod.map id histCache <$> (implReal P s op).run st =ᵈ
      ((Common.foldRO (implHash P roHash s)) op).run (histCache st) := by
  rw [Common.foldRO_run]
  cases op with
  | pub t =>
    rw [implHash_pub_run, simulateQ_map, StateT.run_map, Common.run_hq]
    change Prod.map id histCache <$> (QuotientZk.roStep t).run st =ᵈ _
    rw [roStep_histCache]
    simp only [Functor.map_map]
    exact EvalDistEq.rfl
  | msg =>
    rw [implHash_msg_run]
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    exact EvalDistEq.rfl
  | leaf k x =>
    rw [implHash_leaf_run]
    by_cases hk : st.hist.length < P.cK k
    · simp only [histCache, hk, ↓reduceIte, simulateQ_pure, StateT.run_pure, map_pure]
      change Prod.map id histCache <$>
        (if st.hist.length < P.cK k then pure (default, st)
          else (QuotientZk.roStep (P.rowFn s (st.hist.take (P.cK k)) k x)).run st) =ᵈ _
      simp only [hk, ↓reduceIte, map_pure]
      exact EvalDistEq.rfl
    · simp only [histCache, hk, ↓reduceIte, simulateQ_map, StateT.run_map, Common.run_hq]
      change Prod.map id histCache <$>
        (if st.hist.length < P.cK k then pure (default, st)
          else (QuotientZk.roStep (P.rowFn s (st.hist.take (P.cK k)) k x)).run st) =ᵈ _
      simp only [hk, ↓reduceIte]
      rw [roStep_histCache]
      simp only [Functor.map_map]
      exact EvalDistEq.rfl
  | chal t =>
    rw [implHash_chal_run, simulateQ_map, StateT.run_map, Common.run_hq]
    by_cases hn : st.hist.length < P.n
    · change Prod.map id histCache <$>
        (if st.hist.length < P.n then
          (match st.cache t with
            | some u => pure (u, { st with hist := st.hist ++ [u], fs := true })
            | none => do
              let u ← $ᵗ O
              return (u, { st with
                cache := st.cache.cacheQuery t u
                hist := st.hist ++ [u]
                log := t :: st.log }))
          else (QuotientZk.roStep t).run st) =ᵈ _
      rcases h : st.cache t with _ | u
      · simp [hn, h, Common.roStep, histCache]
      · simp [hn, h, Common.roStep, histCache]
    · change Prod.map id histCache <$>
        (if st.hist.length < P.n then
          (match st.cache t with
            | some u => pure (u, { st with hist := st.hist ++ [u], fs := true })
            | none => do
              let u ← $ᵗ O
              return (u, { st with
                cache := st.cache.cacheQuery t u
                hist := st.hist ++ [u]
                log := t :: st.log }))
          else (QuotientZk.roStep t).run st) =ᵈ _
      simp only [hn, ↓reduceIte]
      rw [roStep_histCache]
      simp only [Functor.map_map, histCache, hn, ↓reduceIte]
      exact EvalDistEq.rfl

/-- **The prover asking the random oracle is `implReal`**: run in the random-oracle model from
the empty cache, its proof and the oracle's cache after it are `prove`'s. -/
theorem romImpl_proverWith (s : S) (skel : OracleComp (OpSpec I O M K X) Pf) :
    (simulateQ (I →ₒ O).romImpl (proverWith P roHash s skel)).run ∅ =ᵈ prove P s skel [] := by
  have h := Common.map_run_simulateQ_evalDistEq_of_inv (implReal P s)
    (Common.foldRO (implHash P roHash s)) (fun _ ↦ True) histCache (fun _ _ _ _ _ ↦ trivial)
    (fun op st _ ↦ implReal_histCache P s op st) skel (St.init []) trivial
  have h0 : histCache (St.init [] : St I O K X) = ([], ∅) := by simp [histCache, St.init]
  rw [h0] at h
  have h1 := h.map fun z ↦ (z.1, z.2.2)
  simp only [Functor.map_map] at h1
  unfold proverWith prove
  rw [StateT.run'_eq, simulateQ_map, StateT.run_map, Common.run_simulateQ_foldRO,
    Functor.map_map]
  exact h1.symm

end Rom

end QuotientZk
