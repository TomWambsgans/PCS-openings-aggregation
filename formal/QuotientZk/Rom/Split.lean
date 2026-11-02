-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): `common`'s state projection (`Common.run'_simulateQ_evalDistEq_of_inv`).
import QuotientZk.Rom.Tape

/-!
# The unopened leaves kept apart, without changing anything

`implSplit` keeps the digests of the unopened leaves in `priv` instead of the cache, and answers
every query through the union of the two (`unionLook`). Read through that union (`unionCache`),
each of its steps is a step of `implSmall`, the up-front prover on the cache and the number of
challenges alone; so is each step of `implUp` read through its cache. Hence the two runs have
the same output distribution (`implUp_evalDistEq_implSplit`).
-/

open OracleComp OracleSpec

namespace QuotientZk

set_option linter.unusedSectionVars false

variable {S I O M K X Pf : Type} [DecidableEq I] [SampleableType O] [Inhabited O]
  [DecidableEq K] [DecidableEq X]
variable (P : Proto S I O M K X)

/-- A random-oracle query on the small state. -/
def roSmall (t : I) : StateT ((I →ₒ O).QueryCache × ℕ) ProbComp O := fun c =>
  match c.1 t with
  | some u => pure (u, c)
  | none => do
    let u ← $ᵗ O
    return (u, (c.1.cacheQuery t u, c.2))

/-- The up-front prover on the cache and the number of challenges. -/
def implSmall (σ : List O) (s : S) :
    QueryImpl (OpSpec I O M K X) (StateT ((I →ₒ O).QueryCache × ℕ) ProbComp)
  | .pub t => roSmall t
  | .msg => fun c => pure (P.msgFn s (σ.take c.2), c)
  | .leaf k x => fun c =>
    if c.2 < P.cK k then pure (default, c) else roSmall (P.rows s σ k x) c
  | .chal t => fun c =>
    if c.2 < P.n then pure (σ.getD c.2 default, (c.1.cacheQuery t (σ.getD c.2 default), c.2 + 1))
    else roSmall t c

/-- A cache and private digests, as one cache. -/
def unionOf (rows : K → X → I) (c : (I →ₒ O).QueryCache) (priv : List ((K × X) × O)) :
    (I →ₒ O).QueryCache :=
  QueryCache.ofFn fun r =>
    match c r with
    | some u => some u
    | none => (priv.find? fun e => decide (rows e.1.1 e.1.2 = r)).map Prod.snd

/-- The state's cache and private digests, as one cache. -/
def unionCache (rows : K → X → I) (st : St I O K X) : (I →ₒ O).QueryCache :=
  unionOf rows st.cache st.priv

theorem unionOf_apply (rows : K → X → I) (st : St I O K X) (r : I) :
    unionOf rows st.cache st.priv r = unionLook rows st r := rfl

/-! ## `implUp` read through its cache -/

theorem roStep_proj (t : I) (st : St I O K X) :
    Prod.map id (fun st : St I O K X => (st.cache, st.hist.length)) <$> roStep t st =
      roSmall t (st.cache, st.hist.length) := by
  unfold roStep roSmall
  cases st.cache t <;> simp

theorem implUp_proj (σ : List O) (s : S) (t : Op I K X) (st : St I O K X) :
    Prod.map id (fun st : St I O K X => (st.cache, st.hist.length)) <$> (implUp P σ s t).run st =
      (implSmall P σ s t).run (st.cache, st.hist.length) := by
  cases t with
  | pub t => exact roStep_proj t st
  | msg => simp [implUp, implSmall, StateT.run]
  | leaf k x =>
    simp only [implUp, implSmall, StateT.run]
    split_ifs
    · simp
    · exact roStep_proj _ st
  | chal t =>
    simp only [implUp, implSmall, StateT.run]
    split_ifs
    · simp [progStep]
    · exact roStep_proj t st

/-- **`implUp` is `implSmall`** read through its cache. -/
theorem implUp_evalDistEq_small {α : Type} (σ : List O) (s : S)
    (oa : OracleComp (OpSpec I O M K X) α) (st : St I O K X) :
    (simulateQ (implUp P σ s) oa).run' st =ᵈ
      (simulateQ (implSmall P σ s) oa).run' (st.cache, st.hist.length) :=
  Common.run'_simulateQ_evalDistEq_of_inv (implUp P σ s) (implSmall P σ s) (fun _ => True)
    (fun st => (st.cache, st.hist.length)) (fun _ _ _ _ _ => trivial)
    (fun t st _ => by rw [implUp_proj]) oa st trivial

/-! ## `implSplit` read through the union -/

theorem unionOf_cacheQuery (rows : K → X → I) (c : (I →ₒ O).QueryCache)
    (priv : List ((K × X) × O)) (t : I) (u : O) :
    unionOf rows (c.cacheQuery t u) priv = (unionOf rows c priv).cacheQuery t u := by
  refine QueryCache.ext fun r => ?_
  by_cases h : r = t
  · subst h
    simp [unionOf, QueryCache.ofFn_apply]
  · simp [unionOf, QueryCache.ofFn_apply, QueryCache.cacheQuery, h]

theorem unionOf_of_find (rows : K → X → I) (c : (I →ₒ O).QueryCache)
    (priv : List ((K × X) × O)) (t : I) (u : O) (hc : c t = none)
    (hf : (priv.find? fun e => decide (rows e.1.1 e.1.2 = t)).map Prod.snd = some u) :
    unionOf rows (c.cacheQuery t u) priv = unionOf rows c priv := by
  rw [unionOf_cacheQuery]
  refine QueryCache.ext fun r => ?_
  by_cases h : r = t
  · subst h
    simp [unionOf, QueryCache.ofFn_apply, hc, hf]
  · simp [QueryCache.cacheQuery, h]

theorem unionOf_append (rows : K → X → I) (c : (I →ₒ O).QueryCache)
    (priv : List ((K × X) × O)) (p : K × X) (u : O) (r : I) :
    unionOf rows c (priv ++ [(p, u)]) r =
      match unionOf rows c priv r with
      | some w => some w
      | none => if rows p.1 p.2 = r then some u else none := by
  simp only [unionOf, QueryCache.ofFn_apply]
  cases c r with
  | some w => rfl
  | none =>
    simp only [List.find?_append]
    cases hf : priv.find? (fun e => decide (rows e.1.1 e.1.2 = r)) with
    | some e => simp
    | none => by_cases h : rows p.1 p.2 = r <;> simp [h]

theorem unionOf_append_of_some (rows : K → X → I) (c : (I →ₒ O).QueryCache)
    (priv : List ((K × X) × O)) (p : K × X) (u : O)
    (h : unionOf rows c priv (rows p.1 p.2) = some u) :
    unionOf rows c (priv ++ [(p, u)]) = unionOf rows c priv := by
  refine QueryCache.ext fun r => ?_
  rw [unionOf_append]
  cases hr : unionOf rows c priv r with
  | some w => rfl
  | none =>
    by_cases hpr : rows p.1 p.2 = r
    · subst hpr; rw [h] at hr; cases hr
    · simp [hpr]

theorem unionOf_append_of_none (rows : K → X → I) (c : (I →ₒ O).QueryCache)
    (priv : List ((K × X) × O)) (p : K × X) (u : O)
    (h : unionOf rows c priv (rows p.1 p.2) = none) :
    unionOf rows c (priv ++ [(p, u)]) = (unionOf rows c priv).cacheQuery (rows p.1 p.2) u := by
  refine QueryCache.ext fun r => ?_
  rw [unionOf_append]
  by_cases hpr : r = rows p.1 p.2
  · subst hpr; simp [h]
  · cases hr : unionOf rows c priv r with
    | some w => simp [QueryCache.cacheQuery, hpr, hr]
    | none => simp [QueryCache.cacheQuery, hpr, hr, Ne.symm hpr]

theorem roSplit_proj (rows : K → X → I) (t : I) (st : St I O K X) :
    Prod.map id (fun st : St I O K X => (unionCache rows st, st.hist.length)) <$> roSplit rows t st =
      roSmall t (unionCache rows st, st.hist.length) := by
  unfold roSplit roSmall unionCache
  cases hc : st.cache t with
  | some u =>
    have : (unionOf rows st.cache st.priv) t = some u := by
      simp [unionOf, QueryCache.ofFn_apply, hc]
    simp [this]
  | none =>
    cases hf : (st.priv.find? fun e => decide (rows e.1.1 e.1.2 = t)).map Prod.snd with
    | some u =>
      have : (unionOf rows st.cache st.priv) t = some u := by
        simp [unionOf, QueryCache.ofFn_apply, hc, hf]
      simp [this, unionOf_of_find rows st.cache st.priv t u hc hf]
    | none =>
      have : (unionOf rows st.cache st.priv) t = none := by
        simp [unionOf, QueryCache.ofFn_apply, hc, hf]
      simp [this, unionOf_cacheQuery]

theorem implSplit_proj (σ : List O) (s : S) (t : Op I K X) (st : St I O K X) :
    Prod.map id (fun st : St I O K X => (unionCache (P.rows s σ) st, st.hist.length)) <$>
        (implSplit P σ s t).run st =
      (implSmall P σ s t).run (unionCache (P.rows s σ) st, st.hist.length) := by
  cases t with
  | pub t => exact roSplit_proj _ t st
  | msg => simp [implSplit, implSmall, StateT.run]
  | leaf k x =>
    simp only [implSplit, implSmall, StateT.run]
    by_cases h1 : st.hist.length < P.cK k
    · simp [h1]
    · simp only [h1, ite_false]
      by_cases h2 : P.opened σ k x = true
      · simp only [h2, ite_true]
        exact roSplit_proj _ _ st
      · simp only [h2, Bool.false_eq_true, ite_false]
        unfold roSmall
        rw [← unionOf_apply]
        unfold unionCache
        cases hl : unionOf (P.rows s σ) st.cache st.priv (P.rows s σ k x) with
        | some u =>
          by_cases hp : hasPriv st (k, x) = true
          · simp [hp]
          · simp [hp, unionOf_append_of_some (P.rows s σ) st.cache st.priv (k, x) u hl]
        | none =>
          simp [unionOf_append_of_none (P.rows s σ) st.cache st.priv (k, x) _ hl]
  | chal t =>
    simp only [implSplit, implSmall, StateT.run]
    by_cases h : st.hist.length < P.n
    · simp [h, progStep, unionCache, unionOf_cacheQuery]
    · simp only [h, ite_false]
      exact roSplit_proj _ t st

/-- **`implSplit` is `implSmall`** read through the union. -/
theorem implSplit_evalDistEq_small {α : Type} (σ : List O) (s : S)
    (oa : OracleComp (OpSpec I O M K X) α) (st : St I O K X) :
    (simulateQ (implSplit P σ s) oa).run' st =ᵈ
      (simulateQ (implSmall P σ s) oa).run' (unionCache (P.rows s σ) st, st.hist.length) :=
  Common.run'_simulateQ_evalDistEq_of_inv (implSplit P σ s) (implSmall P σ s) (fun _ => True)
    (fun st => (unionCache (P.rows s σ) st, st.hist.length)) (fun _ _ _ _ _ => trivial)
    (fun t st _ => by rw [implSplit_proj]) oa st trivial

/-- **The split changes nothing**: from a state with no private digest, `implUp` and
`implSplit` have the same output distribution. -/
theorem implUp_evalDistEq_implSplit {α : Type} (σ : List O) (s : S)
    (oa : OracleComp (OpSpec I O M K X) α) (st : St I O K X) (hst : st.priv = []) :
    (simulateQ (implUp P σ s) oa).run' st =ᵈ (simulateQ (implSplit P σ s) oa).run' st := by
  have h : unionCache (P.rows s σ) st = st.cache := by
    refine QueryCache.ext fun r => ?_
    simp only [unionCache, unionOf, QueryCache.ofFn_apply, hst, List.find?_nil, Option.map_none]
    cases st.cache r <;> rfl
  refine (implUp_evalDistEq_small P σ s oa st).trans ?_
  rw [← h]
  exact (implSplit_evalDistEq_small P σ s oa st).symm

end QuotientZk
