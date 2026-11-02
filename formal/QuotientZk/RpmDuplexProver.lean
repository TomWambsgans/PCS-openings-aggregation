-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): `common`'s two-oracle model (`Common.shadowImpl`, `Common.replayStep`,
-- `Common.foldRO`), its lanes-to-bytes bijection (`LeanVM.Rpm.stateEquiv`) and its state projection
-- (`Common.map_run_simulateQ_evalDistEq_of_inv`).
import QuotientZk.RpmDuplex
import QuotientZk.RpmProver
import QuotientZk.Deployed.Main
import Common.Rerun
import Common.Lanes

/-!
# The deployed prover with Keccak-256 and the duplex over a permutation

`zk_deployed`'s oracle is one random oracle `G : Inp → Out`, `Inp = bytes ⊕ state` (lanes),
`Out = digest × state`: Keccak-256 of `m` is `(G (inl m)).1`, the permutation of a duplex state
`x` is `(G (inr x)).2`. In `common`'s two-oracle model `H` is Keccak-256 (a digest) and `F` the
permutation on byte states. A Keccak-256 answer is completed by a state, a permutation's answer
by a digest, each uniform and the same for the same input: a private table of the prover (in the
random-permutation model it draws them with its own coins). The skeleton never reads them (it
reads `.1` of a Keccak-256 answer, `.2` of a permutation's).

* `implJ`: the prover's operations with a hash `hH`, a permutation `hF` and coins `coinH`,
  `coinF` for the completions (the two tables in the state, beside the challenges);
* `skelRec`: the skeleton keeping, besides its proof, the indifferentiability simulator's
  bookkeeping replayed from its permutation calls (the duplex's edges, on bytes): the simulator
  needs them to answer the distinguisher's queries of `π` on the duplex states consistently with
  the proof; `run_recOps`: the skeleton with the bookkeeping runs as the skeleton;
* `recImpl_implHF`: in `common`'s shadow world the prover's permutation calls are recorded in the
  simulator's state: that is `skelRec`'s bookkeeping;
* `romImpl_proverHF`: with `H` and `F` lazily sampled, the prover is `implReal` for the one oracle
  `G`, read through `hfOf` (the digests of its `inl` entries; the states of its `inr` entries, on
  bytes);
* `ro_enc`: a distinguisher of `H` and `F` is a distinguisher of `G` (`enc`).
-/

open OracleComp OracleSpec Common LeanVM.Rpm
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec)
open scoped ENNReal

namespace QuotientZk.DRpm

set_option linter.unusedSectionVars false

/-! ## The skeleton with the duplex's bookkeeping -/

/-- The simulator's state on byte states. -/
abbrev SimSt := SimState DigestBytes KRest KCap

/-- The bookkeeping after an answer `u` at the input `t`: a permutation call `inr x` records the
edge `(x, u.2)` on bytes as the simulator does (`Common.replayStep`). -/
def recStep (σ : SimSt) : Inp → Out → SimSt
  | .inl _, _ => σ
  | .inr x, u => replayStep σ (.forward (stateEquiv x), stateEquiv u.2)

/-- Each operation, asked as it is, the bookkeeping updated by its permutation call. -/
def recOps : QueryImpl DSpec (StateT SimSt (OracleComp DSpec))
  | .pub t => fun σ ↦ (fun u ↦ (u, recStep σ t u)) <$> liftM (DSpec.query (.pub t))
  | .msg => fun σ ↦ (fun u ↦ (u, σ)) <$> liftM (DSpec.query .msg)
  | .leaf k x => fun σ ↦ (fun u ↦ (u, σ)) <$> liftM (DSpec.query (.leaf k x))
  | .chal t => fun σ ↦ (fun u ↦ (u, recStep σ t u)) <$> liftM (DSpec.query (.chal t))

/-- **The skeleton with the duplex's bookkeeping**: its output, and the simulator's state replayed
from its permutation calls with their answers, in order. -/
def skelRec {Pf : Type} (skel : OracleComp DSpec Pf) : OracleComp DSpec (Pf × SimSt) :=
  (simulateQ recOps skel).run (SimState.init KState.zero)

/-- The bookkeeping of an operation, from its answer. -/
def opRec (σ : SimSt) : (op : Op Inp Tbl Pos) → opRange Out Msg op → SimSt
  | .pub t, u => recStep σ t u
  | .msg, _ => σ
  | .leaf _ _, _ => σ
  | .chal t, u => recStep σ t u

theorem recOps_run (op : Op Inp Tbl Pos) (σ : SimSt) :
    (recOps op).run σ = (fun u ↦ (u, opRec σ op u)) <$> liftM (DSpec.query op) := by
  cases op <;> rfl

/-- **The skeleton with its bookkeeping runs as the skeleton**, under any implementation. -/
theorem run_recOps {ι : Type} {spec : OracleSpec.{0, 0} ι} {τ α : Type}
    (impl : QueryImpl DSpec (StateT τ (OracleComp spec))) (oa : OracleComp DSpec α) (σ : SimSt)
    (st : τ) :
    (fun z ↦ (z.1.1, z.2)) <$> (simulateQ impl ((simulateQ recOps oa).run σ)).run st =
      (simulateQ impl oa).run st := by
  induction oa using OracleComp.inductionOn generalizing σ st with
  | pure a => simp
  | query_bind op k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, recOps_run, bind_map_left, map_bind]
    apply bind_congr; intro z; exact ih z.1 _ z.2

theorem isTotalQueryBound_skelRec {Pf : Type} (skel : OracleComp DSpec Pf) (n : ℕ)
    (h : IsTotalQueryBound skel n) : IsTotalQueryBound (skelRec skel) n :=
  IsTotalQueryBound.simulateQ_run_of_step h (fun op σ ↦ by
    rw [recOps_run, map_eq_bind_pure_comp]
    exact isTotalQueryBound_query_bind_iff.mpr ⟨by omega, fun _ ↦ trivial⟩) _

/-! ## The prover with a hash, a permutation and the completions -/

/-- The completions' tables: a state for each Keccak-256 input, a digest for each permutation
input. -/
abbrev JTab := (List UInt8 →ₒ KSt).QueryCache × (KSt →ₒ DigestBytes).QueryCache

/-- **The oracle `G` with completions**: `inl m` is `(hH m, the table's state at m)`, `inr x` is
`(the table's digest at x, hF x)`, a table's value drawn (`coinH`, `coinF`) the first time. -/
def hashJ {ι : Type} {spec : OracleSpec.{0, 0} ι} (hH : List UInt8 → OracleComp spec DigestBytes)
    (hF : KSt → OracleComp spec KSt) (coinH : OracleComp spec KSt)
    (coinF : OracleComp spec DigestBytes) : Inp → StateT JTab (OracleComp spec) Out
  | .inl m => fun J ↦ hH m >>= fun d ↦
      match J.1 m with
      | some j => pure ((d, j), J)
      | none => coinH >>= fun j ↦ pure ((d, j), (J.1.cacheQuery m j, J.2))
  | .inr x => fun J ↦ hF x >>= fun y ↦
      match J.2 x with
      | some j => pure ((j, y), J)
      | none => coinF >>= fun j ↦ pure ((j, y), (J.1, J.2.cacheQuery x j))

variable {S : Type} (P : Proto S Inp Out Msg Tbl Pos)

/-- **The prover with a hash, a permutation and coins**: `implHash` with `hashJ`, the tables in
the state beside the challenges. -/
def implJ {ι : Type} {spec : OracleSpec.{0, 0} ι} (hH : List UInt8 → OracleComp spec DigestBytes)
    (hF : KSt → OracleComp spec KSt) (coinH : OracleComp spec KSt)
    (coinF : OracleComp spec DigestBytes) (s : S) :
    QueryImpl DSpec (StateT (List Out × JTab) (OracleComp spec))
  | .pub t => fun st ↦ (fun z ↦ (z.1, (st.1, z.2))) <$> (hashJ hH hF coinH coinF t).run st.2
  | .msg => fun st ↦ pure (P.msgFn s st.1, st)
  | .leaf k x => fun st ↦
    if st.1.length < P.cK k then pure (default, st)
    else (fun z ↦ (z.1, (st.1, z.2))) <$>
      (hashJ hH hF coinH coinF (P.rowFn s (st.1.take (P.cK k)) k x)).run st.2
  | .chal t => fun st ↦
    (fun z ↦ (z.1, (if st.1.length < P.n then st.1 ++ [z.1] else st.1, z.2))) <$>
      (hashJ hH hF coinH coinF t).run st.2

/-- The prover of the secret `s`: the skeleton's output. -/
def proverJ {ι : Type} {spec : OracleSpec.{0, 0} ι} {β : Type}
    (hH : List UInt8 → OracleComp spec DigestBytes) (hF : KSt → OracleComp spec KSt)
    (coinH : OracleComp spec KSt) (coinF : OracleComp spec DigestBytes) (s : S)
    (skel : OracleComp DSpec β) : OracleComp spec β :=
  (simulateQ (implJ P hH hF coinH coinF s) skel).run' ([], (∅, ∅))

theorem simulateQ_hashJ {ι ι' : Type} {spec : OracleSpec.{0, 0} ι} {spec' : OracleSpec.{0, 0} ι'}
    (impl : QueryImpl spec (OracleComp spec')) (hH : List UInt8 → OracleComp spec DigestBytes)
    (hF : KSt → OracleComp spec KSt) (coinH : OracleComp spec KSt)
    (coinF : OracleComp spec DigestBytes) (t : Inp) (J : JTab) :
    simulateQ impl ((hashJ hH hF coinH coinF t).run J) =
      (hashJ (fun m ↦ simulateQ impl (hH m)) (fun x ↦ simulateQ impl (hF x))
        (simulateQ impl coinH) (simulateQ impl coinF) t).run J := by
  rcases t with m | x
  · change simulateQ impl (hH m >>= _) = simulateQ impl (hH m) >>= _
    rw [simulateQ_bind]
    refine bind_congr fun d ↦ ?_
    rcases J.1 m with _ | j <;> simp
  · change simulateQ impl (hF x >>= _) = simulateQ impl (hF x) >>= _
    rw [simulateQ_bind]
    refine bind_congr fun d ↦ ?_
    rcases J.2 x with _ | j <;> simp

theorem mapStateTBase_implJ {ι ι' : Type} {spec : OracleSpec.{0, 0} ι}
    {spec' : OracleSpec.{0, 0} ι'} (impl : QueryImpl spec (OracleComp spec'))
    (hH : List UInt8 → OracleComp spec DigestBytes) (hF : KSt → OracleComp spec KSt)
    (coinH : OracleComp spec KSt) (coinF : OracleComp spec DigestBytes) (s : S) :
    impl.mapStateTBase (implJ P hH hF coinH coinF s) =
      implJ P (fun m ↦ simulateQ impl (hH m)) (fun x ↦ simulateQ impl (hF x))
        (simulateQ impl coinH) (simulateQ impl coinF) s := by
  funext op
  cases op with
  | pub t =>
    funext st
    simp [QueryImpl.mapStateTBase, implJ, StateT.mk, StateT.run]
    exact simulateQ_hashJ impl hH hF coinH coinF t st.2
  | msg => funext st; simp [QueryImpl.mapStateTBase, implJ, StateT.mk, StateT.run]
  | leaf k x =>
    funext st
    by_cases hk : st.1.length < P.cK k
    · simp [QueryImpl.mapStateTBase, implJ, StateT.mk, StateT.run, hk]
    · simp [QueryImpl.mapStateTBase, implJ, StateT.mk, StateT.run, hk]
      exact simulateQ_hashJ impl hH hF coinH coinF _ st.2
  | chal t =>
    funext st
    simp [QueryImpl.mapStateTBase, implJ, StateT.mk, StateT.run]
    exact simulateQ_hashJ impl hH hF coinH coinF t st.2

/-- **Simulating the oracles commutes with the prover.** -/
theorem simulateQ_proverJ {ι ι' : Type} {spec : OracleSpec.{0, 0} ι}
    {spec' : OracleSpec.{0, 0} ι'} {β : Type} (impl : QueryImpl spec (OracleComp spec'))
    (hH : List UInt8 → OracleComp spec DigestBytes) (hF : KSt → OracleComp spec KSt)
    (coinH : OracleComp spec KSt) (coinF : OracleComp spec DigestBytes) (s : S)
    (skel : OracleComp DSpec β) :
    simulateQ impl (proverJ P hH hF coinH coinF s skel) =
      proverJ P (fun m ↦ simulateQ impl (hH m)) (fun x ↦ simulateQ impl (hF x))
        (simulateQ impl coinH) (simulateQ impl coinF) s skel := by
  unfold proverJ
  rw [StateT.run'_eq, StateT.run'_eq, simulateQ_map, QueryImpl.simulateQ_mapStateTBase_run,
    mapStateTBase_implJ]

/-! ## The two-oracle random-oracle model and its shadow world -/

/-- `common`'s two oracles for Keccak: `H` (a digest) and `F` (a byte state). -/
abbrev HF := hfSpec (List UInt8) DigestBytes KState

/-- A query of an oracle of a sum with coins, simulated. -/
theorem simulateQ_hq {ι : Type} [DecidableEq ι] {hs : OracleSpec.{0, 0} ι}
    [∀ t : hs.Domain, SampleableType (hs.Range t)] {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (unifSpec + hs) m) (t : ι) :
    simulateQ impl (hq (hs := hs) t) = impl (.inr t) := by
  change simulateQ impl (liftM ((unifSpec + hs).query (.inr t))) = _
  rw [simulateQ_spec_query]

/-- Keccak-256 in the two-oracle model. -/
noncomputable abbrev hH2 (m : List UInt8) : OracleComp (unifSpec + HF) DigestBytes :=
  hQuery (E := KRest) (C := KCap) m

/-- The permutation on lanes in the two-oracle model: `F` on the bytes. -/
noncomputable abbrev hF2 (x : KSt) : OracleComp (unifSpec + HF) KSt :=
  stateEquiv.symm <$> fQuery (Msg := List UInt8) (Dg := DigestBytes) (stateEquiv x)

/-- Coins in the two-oracle model. -/
noncomputable abbrev coin2 (α : Type) [SampleableType α] : OracleComp (unifSpec + HF) α :=
  liftM ($ᵗ α)

/-- **The prover of the two-oracle model**: `H`, `F`, and coins for the completions. -/
noncomputable abbrev implHF (s : S) :=
  implJ P hH2 hF2 (coin2 KSt) (coin2 DigestBytes) s

/-- The two oracles and coins, a permutation call's edge recorded in the simulator's state, as in
`common`'s shadow world (`Common.shadowImpl` through `Common.hfEmbed`). -/
noncomputable abbrev recImpl :
    QueryImpl (unifSpec + HF) (StateT SimSt (OracleComp (unifSpec + HF))) :=
  shadowImpl keccakPadding ∘ₛ hfEmbed (Msg := List UInt8)

theorem recImpl_coin {α : Type} [SampleableType α] (σ : SimSt) :
    (simulateQ recImpl (coin2 α)).run σ = (·, σ) <$> coin2 α :=
  run_simulateQ_liftM_of_coins recImpl (fun n s ↦ by
    simp [recImpl, hfEmbed, shadowImpl, QueryImpl.apply_compose]; rfl) _ σ

theorem recImpl_hH2 (m : List UInt8) (σ : SimSt) :
    (simulateQ recImpl (hH2 m)).run σ = (·, σ) <$> hH2 m := by
  rw [hH2, hQuery, simulateQ_hq]
  simp [recImpl, hfEmbed, shadowImpl, QueryImpl.apply_compose, hQuery]

theorem recImpl_fQuery (x : KState) (σ : SimSt) :
    (simulateQ recImpl (fQuery (Msg := List UInt8) (Dg := DigestBytes) x)).run σ =
      (fun y ↦ (y, replayStep σ (.forward x, y))) <$>
        fQuery (Msg := List UInt8) (Dg := DigestBytes) x := by
  rw [fQuery, simulateQ_hq]
  simp [recImpl, hfEmbed, shadowImpl, QueryImpl.apply_compose, fQuery]

theorem recImpl_hashJ (t : Inp) (J : JTab) (σ : SimSt) :
    (simulateQ recImpl ((hashJ hH2 hF2 (coin2 KSt) (coin2 DigestBytes) t).run J)).run σ =
      (fun z ↦ (z, recStep σ t z.1)) <$>
        (hashJ hH2 hF2 (coin2 KSt) (coin2 DigestBytes) t).run J := by
  rcases t with m | x
  · change (simulateQ recImpl (hH2 m >>= _)).run σ = _ <$> (hH2 m >>= _)
    rw [simulateQ_bind, StateT.run_bind, recImpl_hH2, bind_map_left, map_bind]
    refine bind_congr fun d ↦ ?_
    rcases J.1 m with _ | j
    · simp only [simulateQ_bind, StateT.run_bind, recImpl_coin, bind_map_left, map_bind,
        simulateQ_pure, StateT.run_pure, map_pure]
      rfl
    · simp [recStep]
  · change (simulateQ recImpl (hF2 x >>= _)).run σ = _ <$> (hF2 x >>= _)
    rw [simulateQ_bind, StateT.run_bind, hF2, simulateQ_map, StateT.run_map, recImpl_fQuery,
      Functor.map_map, bind_map_left, map_bind, bind_map_left]
    refine bind_congr fun y ↦ ?_
    rcases J.2 x with _ | j
    · simp only [simulateQ_bind, StateT.run_bind, recImpl_coin, bind_map_left, map_bind,
        simulateQ_pure, StateT.run_pure, map_pure, recStep, stateEquiv_apply,
        stateEquiv_symm_apply, toRpm_ofRpm]
    · simp [recStep, toRpm_ofRpm]

theorem recImpl_implHF_step (hrow : ∀ s h k x, ∃ m, P.rowFn s h k x = .inl m) (s : S)
    (op : Op Inp Tbl Pos) (st : List Out × JTab) (σ : SimSt) :
    (simulateQ recImpl ((implHF P s op).run st)).run σ =
      (fun z ↦ (z, opRec σ op z.1)) <$> (implHF P s op).run st := by
  cases op with
  | pub t =>
    change (simulateQ recImpl ((fun z ↦ (z.1, (st.1, z.2))) <$>
      (hashJ hH2 hF2 (coin2 KSt) (coin2 DigestBytes) t).run st.2)).run σ =
      _ <$> ((fun z ↦ (z.1, (st.1, z.2))) <$>
        (hashJ hH2 hF2 (coin2 KSt) (coin2 DigestBytes) t).run st.2)
    rw [simulateQ_map, StateT.run_map, recImpl_hashJ, Functor.map_map, Functor.map_map]
    rfl
  | msg => rfl
  | leaf k x =>
    by_cases hk : st.1.length < P.cK k
    · change (simulateQ recImpl (if st.1.length < P.cK k then pure (default, st) else _)).run σ =
        _ <$> (if st.1.length < P.cK k then pure (default, st) else _)
      simp only [hk, ↓reduceIte, simulateQ_pure, StateT.run_pure, map_pure]
      rfl
    · obtain ⟨m, hm⟩ := hrow s (st.1.take (P.cK k)) k x
      change (simulateQ recImpl (if st.1.length < P.cK k then pure (default, st) else
        (fun z ↦ (z.1, (st.1, z.2))) <$> (hashJ hH2 hF2 (coin2 KSt) (coin2 DigestBytes)
          (P.rowFn s (st.1.take (P.cK k)) k x)).run st.2)).run σ =
        _ <$> (if st.1.length < P.cK k then pure (default, st) else
        (fun z ↦ (z.1, (st.1, z.2))) <$> (hashJ hH2 hF2 (coin2 KSt) (coin2 DigestBytes)
          (P.rowFn s (st.1.take (P.cK k)) k x)).run st.2)
      simp only [hk, ↓reduceIte, hm]
      rw [simulateQ_map, StateT.run_map, recImpl_hashJ, Functor.map_map, Functor.map_map]
      rfl
  | chal t =>
    change (simulateQ recImpl ((fun z ↦ (z.1, (if st.1.length < P.n then st.1 ++ [z.1]
      else st.1, z.2))) <$> (hashJ hH2 hF2 (coin2 KSt) (coin2 DigestBytes) t).run st.2)).run σ =
      _ <$> ((fun z ↦ (z.1, (if st.1.length < P.n then st.1 ++ [z.1]
      else st.1, z.2))) <$> (hashJ hH2 hF2 (coin2 KSt) (coin2 DigestBytes) t).run st.2)
    rw [simulateQ_map, StateT.run_map, recImpl_hashJ, Functor.map_map, Functor.map_map]
    rfl

/-- **In the shadow world, the prover's permutation calls are recorded as the skeleton's
bookkeeping**: the prover run with its permutation calls recorded from `σ` is the skeleton with
its bookkeeping from `σ`, run by the prover. -/
theorem recImpl_implHF (hrow : ∀ s h k x, ∃ m, P.rowFn s h k x = .inl m) (s : S) {α : Type}
    (oa : OracleComp DSpec α) (σ : SimSt) (st : List Out × JTab) :
    (simulateQ recImpl ((simulateQ (implHF P s) oa).run st)).run σ =
      (fun z ↦ ((z.1.1, z.2), z.1.2)) <$>
        (simulateQ (implHF P s) ((simulateQ recOps oa).run σ)).run st := by
  induction oa using OracleComp.inductionOn generalizing σ st with
  | pure a => simp
  | query_bind op k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, recOps_run]
    rw [recImpl_implHF_step P hrow s op st σ, bind_map_left]
    simp only [simulateQ_map, StateT.run_map, bind_map_left, map_bind, simulateQ_spec_query]
    apply bind_congr; intro z; exact ih z.1 _ z.2

/-! ## With `H` and `F` lazily sampled, the prover is `implReal` for `G` -/

/-- **`G`'s cache read as `H` and `F`**: the digests of its `inl` entries, the states (on bytes) of
its `inr` entries. -/
def hfOf (c : (Inp →ₒ Out).QueryCache) : HF.QueryCache :=
  QueryCache.ofFn fun t ↦ match t with
    | .inl m => (c (.inl m)).map (·.1)
    | .inr xb => (c (.inr (stateEquiv.symm xb))).map fun o ↦ stateEquiv o.2

/-- **`G`'s cache read as the completions' tables.** -/
def jOf (c : (Inp →ₒ Out).QueryCache) : JTab :=
  (QueryCache.ofFn fun m ↦ (c (.inl m)).map (·.2), QueryCache.ofFn fun x ↦ (c (.inr x)).map (·.1))

theorem hfOf_inl (c : (Inp →ₒ Out).QueryCache) (m : List UInt8) :
    hfOf c (.inl m) = (c (.inl m)).map (·.1) := rfl

theorem hfOf_inr (c : (Inp →ₒ Out).QueryCache) (x : KSt) :
    hfOf c (.inr (stateEquiv x)) = (c (.inr x)).map fun o ↦ stateEquiv o.2 := by
  change Option.map _ (c (.inr (stateEquiv.symm (stateEquiv x)))) = _
  rw [Equiv.symm_apply_apply]

theorem hfOf_empty : hfOf (∅ : (Inp →ₒ Out).QueryCache) = ∅ := by
  refine QueryCache.ext fun t ↦ ?_
  rcases t with m | xb <;> rfl

theorem jOf_empty : jOf (∅ : (Inp →ₒ Out).QueryCache) = (∅, ∅) := rfl

theorem hfOf_cacheQuery_inl (c : (Inp →ₒ Out).QueryCache) (m : List UInt8) (o : Out) :
    hfOf (c.cacheQuery (.inl m) o) = (hfOf c).cacheQuery (.inl m) o.1 := by
  refine QueryCache.ext fun t ↦ ?_
  rcases t with m' | xb
  · by_cases h : m' = m
    · subst h; simp [hfOf, QueryCache.cacheQuery_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using h)]
      simp [hfOf, QueryCache.cacheQuery_of_ne _ _ (show (Sum.inl m' : Inp) ≠ .inl m by simpa using h)]
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]
    simp [hfOf, QueryCache.cacheQuery_of_ne _ _ (show (Sum.inr (stateEquiv.symm xb) : Inp) ≠ .inl m by simp)]

theorem hfOf_cacheQuery_inr (c : (Inp →ₒ Out).QueryCache) (x : KSt) (o : Out) :
    hfOf (c.cacheQuery (.inr x) o) = (hfOf c).cacheQuery (.inr (stateEquiv x)) (stateEquiv o.2) := by
  refine QueryCache.ext fun t ↦ ?_
  rcases t with m | xb
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]
    simp [hfOf, QueryCache.cacheQuery_of_ne _ _ (show (Sum.inl m : Inp) ≠ .inr x by simp)]
  · by_cases h : xb = stateEquiv x
    · subst h
      rw [QueryCache.cacheQuery_self, hfOf_inr, QueryCache.cacheQuery_self]
      rfl
    · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using h)]
      have h' : (Sum.inr (LeanVM.Rpm.KState.ofRpm xb) : Inp) ≠ .inr x := by
        intro hx
        apply h
        simp only [Sum.inr.injEq] at hx
        rw [← hx, stateEquiv_apply, LeanVM.Rpm.toRpm_ofRpm]
      simp [hfOf, QueryCache.cacheQuery_of_ne _ _ h']

theorem jOf_cacheQuery_inl (c : (Inp →ₒ Out).QueryCache) (m : List UInt8) (o : Out) :
    jOf (c.cacheQuery (.inl m) o) = ((jOf c).1.cacheQuery m o.2, (jOf c).2) := by
  refine Prod.ext (QueryCache.ext fun m' ↦ ?_) (QueryCache.ext fun x ↦ ?_)
  · by_cases h : m' = m
    · subst h; simp [jOf, QueryCache.cacheQuery_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ h]
      simp [jOf, QueryCache.cacheQuery_of_ne _ _ (show (Sum.inl m' : Inp) ≠ .inl m by simpa using h)]
  · simp [jOf, QueryCache.cacheQuery_of_ne _ _ (show (Sum.inr x : Inp) ≠ .inl m by simp)]

theorem jOf_cacheQuery_inr (c : (Inp →ₒ Out).QueryCache) (x : KSt) (o : Out) :
    jOf (c.cacheQuery (.inr x) o) = ((jOf c).1, (jOf c).2.cacheQuery x o.1) := by
  refine Prod.ext (QueryCache.ext fun m ↦ ?_) (QueryCache.ext fun x' ↦ ?_)
  · simp [jOf, QueryCache.cacheQuery_of_ne _ _ (show (Sum.inl m : Inp) ≠ .inr x by simp)]
  · by_cases h : x' = x
    · subst h; simp [jOf, QueryCache.cacheQuery_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ h]
      simp [jOf, QueryCache.cacheQuery_of_ne _ _ (show (Sum.inr x' : Inp) ≠ .inr x by simpa using h)]

theorem jOf_fst (c : (Inp →ₒ Out).QueryCache) (m : List UInt8) :
    (jOf c).1 m = (c (.inl m)).map (·.2) := rfl

theorem jOf_snd (c : (Inp →ₒ Out).QueryCache) (x : KSt) :
    (jOf c).2 x = (c (.inr x)).map (·.1) := rfl

/-- A uniform answer of `G` is a uniform digest and a uniform state. -/
theorem uniform_out : ($ᵗ Out) = (do let d ← $ᵗ DigestBytes; let y ← $ᵗ KSt; pure (d, y)) :=
  SampleableType.uniformSample_prod_eq_bind _ _

/-- A uniform state on bytes, read on lanes, is uniform. -/
theorem uniform_lanes : (stateEquiv.symm <$> ($ᵗ KState)) =ᵈ ($ᵗ KSt) :=
  SampleableType.map_uniformSample_evalDistEq_of_bijective stateEquiv.symm.bijective

/-- A uniform state on bytes is a uniform state on lanes, read on bytes. -/
theorem lanes_bind {β : Type} (H : KState → ProbComp β) :
    (($ᵗ KState) >>= H) =ᵈ (($ᵗ KSt) >>= fun y ↦ H (stateEquiv y)) := by
  calc (($ᵗ KState) >>= H)
      = (($ᵗ KState) >>= fun y' ↦ (fun y ↦ H (stateEquiv y)) (stateEquiv.symm y')) := by
        refine congrArg (fun f ↦ ($ᵗ KState) >>= f) (funext fun y' ↦ ?_)
        beta_reduce
        rw [Equiv.apply_symm_apply]
    _ = ((stateEquiv.symm <$> ($ᵗ KState)) >>= fun y ↦ H (stateEquiv y)) :=
        (bind_map_left stateEquiv.symm ($ᵗ KState) (fun y ↦ H (stateEquiv y))).symm
    _ =ᵈ _ := EvalDistEq.bind_left uniform_lanes _

/-- **One query of `G`, read as `H`, `F` and the tables**: in the two-oracle model with the
tables of `G`'s cache. -/
theorem romImpl_hashJ (t : Inp) (c : (Inp →ₒ Out).QueryCache) :
    (simulateQ HF.romImpl ((hashJ hH2 hF2 (coin2 KSt) (coin2 DigestBytes) t).run (jOf c))).run
        (hfOf c) =ᵈ
      (fun z ↦ ((z.1, jOf z.2), hfOf z.2)) <$> Common.roStep (hs := Inp →ₒ Out) t c := by
  rcases t with m | x
  · change (simulateQ HF.romImpl (hH2 m >>= _)).run (hfOf c) =ᵈ _
    rw [simulateQ_bind, StateT.run_bind, hH2, hQuery, Common.run_hq]
    rcases h : c (.inl m) with _ | o
    · have h1 : hfOf c (.inl m) = none := by rw [hfOf_inl, h]; rfl
      have h2 : (jOf c).1 m = none := by rw [jOf_fst, h]; rfl
      rw [Common.roStep_of_none h1, Common.roStep_of_none h, uniform_out]
      simp only [bind_assoc, pure_bind, map_bind, map_pure, h2]
      refine EvalDistEq.bind_congr_of_support _ fun d _ ↦ ?_
      simp only [simulateQ_bind, StateT.run_bind, OracleSpec.simulateQ_romImpl_liftM_run,
        bind_map_left, simulateQ_pure, StateT.run_pure, hfOf_cacheQuery_inl, jOf_cacheQuery_inl]
      exact EvalDistEq.rfl
    · have h1 : hfOf c (.inl m) = some o.1 := by rw [hfOf_inl, h]; rfl
      have h2 : (jOf c).1 m = some o.2 := by rw [jOf_fst, h]; rfl
      rw [Common.roStep_of_some h1, Common.roStep_of_some h]
      simp only [pure_bind, map_pure, h2, simulateQ_pure, StateT.run_pure]
      exact EvalDistEq.rfl
  · change (simulateQ HF.romImpl (hF2 x >>= _)).run (hfOf c) =ᵈ _
    rw [simulateQ_bind, StateT.run_bind, hF2, simulateQ_map, StateT.run_map, fQuery,
      Common.run_hq]
    rcases h : c (.inr x) with _ | o
    · have h1 : hfOf c (.inr (stateEquiv x)) = none := by rw [hfOf_inr, h]; rfl
      have h2 : (jOf c).2 x = none := by rw [jOf_snd, h]; rfl
      rw [Common.roStep_of_none h1, Common.roStep_of_none h, uniform_out]
      simp only [map_bind, bind_assoc, map_pure, pure_bind, h2, simulateQ_bind, StateT.run_bind,
        OracleSpec.simulateQ_romImpl_liftM_run, bind_map_left, simulateQ_pure, StateT.run_pure,
        hfOf_cacheQuery_inr, jOf_cacheQuery_inr]
      refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
      refine EvalDistEq.bind_congr_of_support _ fun j _ ↦ ?_
      refine (lanes_bind _).trans ?_
      simp only [Equiv.symm_apply_apply]
      exact EvalDistEq.rfl
    · have h1 : hfOf c (.inr (stateEquiv x)) = some (stateEquiv o.2) := by rw [hfOf_inr, h]; rfl
      have h2 : (jOf c).2 x = some o.1 := by rw [jOf_snd, h]; rfl
      rw [Common.roStep_of_some h1, Common.roStep_of_some h]
      simp only [pure_bind, map_pure, h2, simulateQ_pure, StateT.run_pure, Equiv.symm_apply_apply]
      exact EvalDistEq.rfl

/-- `implReal`'s state read as the two-oracle prover's: the challenges, the tables, `H` and `F`. -/
def projHF (st : St Inp Out Tbl Pos) : (List Out × JTab) × HF.QueryCache :=
  ((st.hist, jOf st.cache), hfOf st.cache)

/-- A query `t` of `G` from the prover's state, read as the two-oracle prover's. -/
theorem foldRO_hashJ (t : Inp) (hist : List Out) (c : (Inp →ₒ Out).QueryCache) (f : List Out → Out → List Out) :
    (fun y ↦ (y.1.1, (y.1.2, y.2))) <$> (simulateQ HF.romImpl
      ((fun z ↦ (z.1, (f hist z.1, z.2))) <$>
        (hashJ hH2 hF2 (coin2 KSt) (coin2 DigestBytes) t).run (jOf c))).run (hfOf c) =ᵈ
      (fun z ↦ (z.1, ((f hist z.1, jOf z.2), hfOf z.2))) <$> Common.roStep (hs := Inp →ₒ Out) t c := by
  rw [simulateQ_map, StateT.run_map, Functor.map_map]
  refine EvalDistEq.trans ((romImpl_hashJ t c).map _) ?_
  rw [Functor.map_map]

/-- **One step of `implReal`**, read as the two-oracle prover's state, is one step of the
two-oracle prover with `H` and `F` lazily sampled. -/
theorem implReal_projHF (s : S) (op : Op Inp Tbl Pos) (st : St Inp Out Tbl Pos) :
    Prod.map id projHF <$> (implReal P s op).run st =ᵈ
      ((foldRO (implHF P s)) op).run (projHF st) := by
  rw [Common.foldRO_run]
  cases op with
  | pub t =>
    have e : Prod.map id projHF <$> (implReal P s (.pub t)).run st =
        (fun z ↦ (z.1, ((st.hist, jOf z.2), hfOf z.2))) <$>
          Common.roStep (hs := Inp →ₒ Out) t st.cache := by
      have h := congrArg (fun x ↦ (fun z : Out × (List Out × (Inp →ₒ Out).QueryCache) ↦
        (z.1, ((z.2.1, jOf z.2.2), hfOf z.2.2))) <$> x) (roStep_histCache t st)
      simp only [Functor.map_map] at h
      exact h
    rw [e]
    exact (foldRO_hashJ t st.hist st.cache fun h _ ↦ h).symm
  | msg => exact EvalDistEq.rfl
  | leaf k x =>
    by_cases hk : st.hist.length < P.cK k
    · change Prod.map id projHF <$> (if st.hist.length < P.cK k then pure (default, st) else _) =ᵈ
        _ <$> (simulateQ HF.romImpl (if st.hist.length < P.cK k then pure (default, (st.hist,
          jOf st.cache)) else _)).run (hfOf st.cache)
      simp only [hk, ↓reduceIte, map_pure, simulateQ_pure, StateT.run_pure]
      exact EvalDistEq.rfl
    · have e : Prod.map id projHF <$> (implReal P s (.leaf k x)).run st =
          (fun z ↦ (z.1, ((st.hist, jOf z.2), hfOf z.2))) <$> Common.roStep (hs := Inp →ₒ Out)
            (P.rowFn s (st.hist.take (P.cK k)) k x) st.cache := by
        change Prod.map id projHF <$> (if st.hist.length < P.cK k then pure (default, st) else
          (QuotientZk.roStep (P.rowFn s (st.hist.take (P.cK k)) k x)).run st) = _
        simp only [hk, ↓reduceIte]
        have h := congrArg (fun x ↦ (fun z : Out × (List Out × (Inp →ₒ Out).QueryCache) ↦
          (z.1, ((z.2.1, jOf z.2.2), hfOf z.2.2))) <$> x)
          (roStep_histCache (P.rowFn s (st.hist.take (P.cK k)) k x) st)
        simp only [Functor.map_map] at h
        exact h
      rw [e]
      change _ =ᵈ _ <$> (simulateQ HF.romImpl (if st.hist.length < P.cK k then pure (default,
        (st.hist, jOf st.cache)) else (fun z ↦ (z.1, (st.hist, z.2))) <$>
          (hashJ hH2 hF2 (coin2 KSt) (coin2 DigestBytes)
            (P.rowFn s (st.hist.take (P.cK k)) k x)).run (jOf st.cache))).run (hfOf st.cache)
      simp only [hk, ↓reduceIte]
      exact (foldRO_hashJ _ st.hist st.cache fun h _ ↦ h).symm
  | chal t =>
    have e : Prod.map id projHF <$> (implReal P s (.chal t)).run st =
        (fun z ↦ (z.1, (((fun h u ↦ if h.length < P.n then h ++ [u] else h) st.hist z.1,
          jOf z.2), hfOf z.2))) <$> Common.roStep (hs := Inp →ₒ Out) t st.cache := by
      by_cases hn : st.hist.length < P.n
      · rcases h : st.cache t with _ | u
        · simp [implReal, StateT.run, hn, h, Common.roStep, projHF]
        · simp [implReal, StateT.run, hn, h, Common.roStep, projHF]
      · simp only [implReal, StateT.run]
        simp only [hn, ↓reduceIte]
        change Prod.map id projHF <$> (QuotientZk.roStep t).run st = _
        have h := congrArg (fun x ↦ (fun z : Out × (List Out × (Inp →ₒ Out).QueryCache) ↦
          (z.1, ((z.2.1, jOf z.2.2), hfOf z.2.2))) <$> x) (roStep_histCache t st)
        simp only [Functor.map_map] at h
        exact h
    rw [e]
    exact (foldRO_hashJ t st.hist st.cache fun h u ↦ if h.length < P.n then h ++ [u] else h).symm

/-- **The two-oracle prover is `implReal`**: run with `H` and `F` lazily sampled from empty
caches, its output and `H`, `F` after it are `prove`'s output and `G`'s cache read through
`hfOf`. -/
theorem romImpl_proverHF (s : S) {β : Type} (skel : OracleComp DSpec β) :
    (simulateQ HF.romImpl (proverJ P hH2 hF2 (coin2 KSt) (coin2 DigestBytes) s skel)).run ∅ =ᵈ
      (fun z ↦ (z.1, hfOf z.2)) <$> prove P s skel [] := by
  have h := Common.map_run_simulateQ_evalDistEq_of_inv (implReal P s)
    (Common.foldRO (implHF P s)) (fun _ ↦ True) projHF (fun _ _ _ _ _ ↦ trivial)
    (fun op st _ ↦ implReal_projHF P s op st) skel (St.init []) trivial
  have h0 : projHF (St.init [] : St Inp Out Tbl Pos) = (([], (∅, ∅)), ∅) := by
    have hc : (St.init [] : St Inp Out Tbl Pos).cache = ∅ := rfl
    simp only [projHF, hc, hfOf_empty, jOf_empty]
    rfl
  rw [h0] at h
  have h1 := h.map fun z ↦ (z.1, z.2.2)
  simp only [Functor.map_map] at h1
  unfold proverJ prove
  rw [StateT.run'_eq, simulateQ_map, StateT.run_map, Common.run_simulateQ_foldRO,
    Functor.map_map, Functor.map_map]
  exact h1.symm

/-! ## A distinguisher of `H` and `F` is a distinguisher of `G` -/

/-- `H` and `F` as queries of `G`: `H m` the digest of `G (inl m)`, `F` on bytes the state of `G`
at the lanes. -/
def enc : QueryImpl HF (OracleComp (Inp →ₒ Out))
  | .inl m => (·.1) <$> liftM ((Inp →ₒ Out).query (.inl m))
  | .inr xb => (fun o ↦ stateEquiv o.2) <$> liftM ((Inp →ₒ Out).query (.inr (stateEquiv.symm xb)))

theorem randomOracle_run {ι : Type} [DecidableEq ι] {hs : OracleSpec.{0, 0} ι}
    [∀ t : hs.Domain, SampleableType (hs.Range t)] (t : ι) (c : hs.QueryCache) :
    (randomOracle t).run c = Common.roStep (hs := hs) t c := by
  rw [randomOracle.run_eq]
  rfl

theorem enc_step (t : HF.Domain) (c : (Inp →ₒ Out).QueryCache) :
    Prod.map id hfOf <$> ((randomOracle ∘ₛ enc) t).run c =ᵈ (randomOracle t).run (hfOf c) := by
  rcases t with m | xb
  · simp only [QueryImpl.apply_compose, enc]
    rw [simulateQ_map, StateT.run_map, ro_query_run', Functor.map_map, randomOracle_run]
    rcases h : c (.inl m) with _ | o
    · have h1 : hfOf c (.inl m) = none := by rw [hfOf_inl, h]; rfl
      rw [Common.roStep_of_none h1, Common.roStep_of_none h, uniform_out]
      simp only [map_bind, bind_assoc, map_pure, pure_bind, Prod.map_apply, id_eq,
        hfOf_cacheQuery_inl]
      refine EvalDistEq.bind_congr_of_support _ fun d _ ↦ ?_
      exact evalDistEq_bind_const _ _
    · have h1 : hfOf c (.inl m) = some o.1 := by rw [hfOf_inl, h]; rfl
      rw [Common.roStep_of_some h1, Common.roStep_of_some h]
      simp only [map_pure, Prod.map_apply, id_eq]
      exact EvalDistEq.rfl
  · simp only [QueryImpl.apply_compose, enc]
    rw [simulateQ_map, StateT.run_map, ro_query_run', Functor.map_map, randomOracle_run]
    obtain ⟨x, rfl⟩ : ∃ x, xb = stateEquiv x := ⟨stateEquiv.symm xb, (Equiv.apply_symm_apply _ _).symm⟩
    rw [Equiv.symm_apply_apply]
    rcases h : c (.inr x) with _ | o
    · have h1 : hfOf c (.inr (stateEquiv x)) = none := by rw [hfOf_inr, h]; rfl
      rw [Common.roStep_of_none h1, Common.roStep_of_none h, uniform_out]
      simp only [map_bind, bind_assoc, map_pure, pure_bind, Prod.map_apply, id_eq,
        hfOf_cacheQuery_inr]
      refine (evalDistEq_bind_const _ _).trans ?_
      exact (lanes_bind (fun y' ↦ pure (y', (hfOf c).cacheQuery (.inr (stateEquiv x)) y'))).symm
    · have h1 : hfOf c (.inr (stateEquiv x)) = some (stateEquiv o.2) := by rw [hfOf_inr, h]; rfl
      rw [Common.roStep_of_some h1, Common.roStep_of_some h]
      simp only [map_pure, Prod.map_apply, id_eq]
      exact EvalDistEq.rfl

/-- **A distinguisher of `H` and `F`, read on `G`** (`enc`): from `G`'s cache `c`, it runs as
from `H` and `F` read through `hfOf`. -/
theorem ro_enc {α : Type} (Y : OracleComp HF α) (c : (Inp →ₒ Out).QueryCache) :
    (simulateQ randomOracle Y).run' (hfOf c) =ᵈ
      (simulateQ randomOracle (simulateQ enc Y)).run' c := by
  rw [← QueryImpl.simulateQ_compose]
  exact (Common.run'_simulateQ_evalDistEq_of_inv (randomOracle ∘ₛ enc) randomOracle
    (fun _ ↦ True) hfOf (fun _ _ _ _ _ ↦ trivial) (fun t c _ ↦ enc_step t c) Y c trivial).symm

theorem isTotalQueryBound_enc {α : Type} (Y : OracleComp HF α) (q : ℕ)
    (hY : IsTotalQueryBound Y q) : IsTotalQueryBound (simulateQ enc Y) q :=
  IsTotalQueryBound.simulateQ_of_step hY fun t ↦ by
    rcases t with m | xb <;>
    · simp only [enc, map_eq_bind_pure_comp]
      exact isTotalQueryBound_query_bind_iff.mpr ⟨by omega, fun _ ↦ trivial⟩

end QuotientZk.DRpm
