-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): `common`'s two-oracle model (`Common.shadowImpl`, `Common.replayStep`,
-- `Common.foldRO`) and its state projection (`Common.map_run_simulateQ_evalDistEq_of_inv`).
import QuotientZk.RpmDuplex
import QuotientZk.RpmProver

/-!
# The prover with Keccak-256 and the duplex

`zk_rom`'s random oracle is one oracle `I →ₒ O`. With both of the prover's hashes, the inputs are
`I = Msg ⊕ St` (a Keccak-256 input, or a state the duplex calls `π` at) and the answers are states
`O = St`: a direct call's answer is `π`'s, and a Keccak-256 answer is its digest **completed** by
a uniform rest of the rate and capacity, the same for the same input (a private table of the
prover: in the random-permutation model the prover draws it with its own coins). The deployed
prover reads only the digest, so the completion changes nothing for it.

* `implJ`: the prover's operations with a hash `H`, direct calls `F` and coins (the completions'
  table in the state);
* `skelRec`: the skeleton keeping, besides its proof, the simulator's bookkeeping replayed from its
  direct calls (the duplex's edges) — the simulator needs them to answer the distinguisher's
  queries of `π` on the duplex states consistently with the proof; `run_recOps`: for any
  implementation, the skeleton with the bookkeeping runs as the skeleton;
* `recImpl_implJ`: in `common`'s shadow world the prover's direct calls are recorded in the
  simulator's state; that is `skelRec`'s bookkeeping;
* `implReal_projJ`: with `H` and `F` lazily sampled, the prover is `zk_rom`'s `implReal` for the
  one random oracle `I →ₒ O` read through `hfOf` (the digests of its `inl` entries, its `inr`
  entries) and the table (the completions of its `inl` entries);
* `ro_enc`: a distinguisher of `H` and `F` is a distinguisher of the one oracle (`enc`).
-/

open OracleComp OracleSpec Common
open scoped ENNReal

namespace QuotientZk

set_option linter.unusedSectionVars false

section Setting

variable {Dg E C Msg : Type} [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C] [SampleableType Dg] [SampleableType E] [SampleableType C]
  [Inhabited Dg] [Inhabited E] [Inhabited C]
  (Pd : Padding Msg (Dg × E)) [Pd.Lawful] (iv : SpState Dg E C)

variable {S M K X Pf : Type}

/-! ## The skeleton with the duplex's bookkeeping -/

/-- The bookkeeping after an answer `u` at the hash input `t`: a direct call `inr x` records the
edge `(x, u)` as the simulator does (`Common.replayStep`). -/
def recStep (σ : SimState Dg E C) : Msg ⊕ SpState Dg E C → SpState Dg E C → SimState Dg E C
  | .inl _, _ => σ
  | .inr x, u => replayStep σ (.forward x, u)

/-- Each operation, asked as it is, the bookkeeping updated by its direct call. -/
def recOps : QueryImpl (OpSpec (Msg ⊕ SpState Dg E C) (SpState Dg E C) M K X)
    (StateT (SimState Dg E C) (OracleComp (OpSpec (Msg ⊕ SpState Dg E C) (SpState Dg E C) M K X)))
  | .pub t => fun σ ↦ (fun u ↦ (u, recStep σ t u)) <$>
      liftM ((OpSpec (Msg ⊕ SpState Dg E C) (SpState Dg E C) M K X).query (.pub t))
  | .msg => fun σ ↦ (fun u ↦ (u, σ)) <$>
      liftM ((OpSpec (Msg ⊕ SpState Dg E C) (SpState Dg E C) M K X).query .msg)
  | .leaf k x => fun σ ↦ (fun u ↦ (u, σ)) <$>
      liftM ((OpSpec (Msg ⊕ SpState Dg E C) (SpState Dg E C) M K X).query (.leaf k x))
  | .chal t => fun σ ↦ (fun u ↦ (u, recStep σ t u)) <$>
      liftM ((OpSpec (Msg ⊕ SpState Dg E C) (SpState Dg E C) M K X).query (.chal t))

/-- **The skeleton with the duplex's bookkeeping**: its proof, and the simulator's state replayed
from its direct calls with their answers, in order. -/
def skelRec (skel : OracleComp (OpSpec (Msg ⊕ SpState Dg E C) (SpState Dg E C) M K X) Pf) :
    OracleComp (OpSpec (Msg ⊕ SpState Dg E C) (SpState Dg E C) M K X) (Pf × SimState Dg E C) :=
  (simulateQ recOps skel).run (SimState.init iv)

/-- The bookkeeping of an operation, from its answer. -/
def opRec (σ : SimState Dg E C) : (op : Op (Msg ⊕ SpState Dg E C) K X) →
    opRange (SpState Dg E C) M op → SimState Dg E C
  | .pub t, u => recStep σ t u
  | .msg, _ => σ
  | .leaf _ _, _ => σ
  | .chal t, u => recStep σ t u

theorem recOps_run (op : Op (Msg ⊕ SpState Dg E C) K X) (σ : SimState Dg E C) :
    (recOps (Dg := Dg) (E := E) (C := C) (M := M) op).run σ =
      (fun u ↦ (u, opRec σ op u)) <$>
        liftM ((OpSpec (Msg ⊕ SpState Dg E C) (SpState Dg E C) M K X).query op) := by
  cases op <;> rfl

/-- **The skeleton with its bookkeeping runs as the skeleton**, under any implementation. -/
theorem run_recOps {ι : Type} {spec : OracleSpec.{0, 0} ι} {τ α : Type}
    (impl : QueryImpl (OpSpec (Msg ⊕ SpState Dg E C) (SpState Dg E C) M K X)
      (StateT τ (OracleComp spec)))
    (oa : OracleComp (OpSpec (Msg ⊕ SpState Dg E C) (SpState Dg E C) M K X) α)
    (σ : SimState Dg E C) (st : τ) :
    (fun z ↦ (z.1.1, z.2)) <$> (simulateQ impl ((simulateQ recOps oa).run σ)).run st =
      (simulateQ impl oa).run st := by
  induction oa using OracleComp.inductionOn generalizing σ st with
  | pure a => simp
  | query_bind op k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, recOps_run, bind_map_left, map_bind]
    exact bind_congr fun z ↦ ih z.1 _ z.2

theorem isTotalQueryBound_skelRec
    (skel : OracleComp (OpSpec (Msg ⊕ SpState Dg E C) (SpState Dg E C) M K X) Pf) (n : ℕ)
    (h : IsTotalQueryBound skel n) : IsTotalQueryBound (skelRec iv skel) n :=
  IsTotalQueryBound.simulateQ_run_of_step h (fun op σ ↦ by
    rw [recOps_run, map_eq_bind_pure_comp]
    exact isTotalQueryBound_query_bind_iff.mpr ⟨by omega, fun _ ↦ trivial⟩) _

/-! ## The prover with `H`, `F` and the completions -/

/-- The completions' table: a rest of the rate and capacity for each Keccak-256 input. -/
abbrev JCache (Msg E C : Type) := (Msg →ₒ (E × C)).QueryCache

/-- **The hash with completions**: a Keccak-256 input `inl m` is answered `H m` completed by the
table's value at `m` (`coin` the first time); a direct call `inr x` by `F x`. -/
def hashJ {ι : Type} {spec : OracleSpec.{0, 0} ι} (hH : Msg → OracleComp spec Dg)
    (hF : SpState Dg E C → OracleComp spec (SpState Dg E C)) (coin : OracleComp spec (E × C)) :
    Msg ⊕ SpState Dg E C → StateT (JCache Msg E C) (OracleComp spec) (SpState Dg E C)
  | .inl m => fun J ↦ hH m >>= fun d ↦
      match J m with
      | some j => pure (((d, j.1), j.2), J)
      | none => coin >>= fun j ↦ pure (((d, j.1), j.2), J.cacheQuery m j)
  | .inr x => fun J ↦ (fun y ↦ (y, J)) <$> hF x

variable (P : Proto S (Msg ⊕ SpState Dg E C) (SpState Dg E C) M K X)

/-- **The prover with `H`, `F` and coins**: `implHash` with `hashJ`, the completions' table in the
state beside the challenges. -/
def implJ {ι : Type} {spec : OracleSpec.{0, 0} ι} (hH : Msg → OracleComp spec Dg)
    (hF : SpState Dg E C → OracleComp spec (SpState Dg E C)) (coin : OracleComp spec (E × C))
    (s : S) : QueryImpl (OpSpec (Msg ⊕ SpState Dg E C) (SpState Dg E C) M K X)
      (StateT (List (SpState Dg E C) × JCache Msg E C) (OracleComp spec))
  | .pub t => fun st ↦ (fun z ↦ (z.1, (st.1, z.2))) <$> (hashJ hH hF coin t).run st.2
  | .msg => fun st ↦ pure (P.msgFn s st.1, st)
  | .leaf k x => fun st ↦
    if st.1.length < P.cK k then pure (default, st)
    else (fun z ↦ (z.1, (st.1, z.2))) <$>
      (hashJ hH hF coin (P.rowFn s (st.1.take (P.cK k)) k x)).run st.2
  | .chal t => fun st ↦
    (fun z ↦ (z.1, (if st.1.length < P.n then st.1 ++ [z.1] else st.1, z.2))) <$>
      (hashJ hH hF coin t).run st.2

/-- The prover of the secret `s`: the skeleton's output. -/
def proverJ {ι : Type} {spec : OracleSpec.{0, 0} ι} {β : Type} (hH : Msg → OracleComp spec Dg)
    (hF : SpState Dg E C → OracleComp spec (SpState Dg E C)) (coin : OracleComp spec (E × C))
    (s : S) (skel : OracleComp (OpSpec (Msg ⊕ SpState Dg E C) (SpState Dg E C) M K X) β) :
    OracleComp spec β :=
  (simulateQ (implJ P hH hF coin s) skel).run' ([], ∅)

theorem simulateQ_hashJ {ι ι' : Type} {spec : OracleSpec.{0, 0} ι} {spec' : OracleSpec.{0, 0} ι'}
    (impl : QueryImpl spec (OracleComp spec')) (hH : Msg → OracleComp spec Dg)
    (hF : SpState Dg E C → OracleComp spec (SpState Dg E C)) (coin : OracleComp spec (E × C))
    (t : Msg ⊕ SpState Dg E C) (J : JCache Msg E C) :
    simulateQ impl ((hashJ hH hF coin t).run J) =
      (hashJ (fun m ↦ simulateQ impl (hH m)) (fun x ↦ simulateQ impl (hF x))
        (simulateQ impl coin) t).run J := by
  rcases t with m | x
  · change simulateQ impl (hH m >>= _) = simulateQ impl (hH m) >>= _
    rw [simulateQ_bind]
    refine bind_congr fun d ↦ ?_
    rcases J m with _ | j <;> simp
  · change simulateQ impl ((fun y ↦ (y, J)) <$> hF x) = (fun y ↦ (y, J)) <$> simulateQ impl (hF x)
    rw [simulateQ_map]

theorem mapStateTBase_implJ {ι ι' : Type} {spec : OracleSpec.{0, 0} ι}
    {spec' : OracleSpec.{0, 0} ι'} (impl : QueryImpl spec (OracleComp spec'))
    (hH : Msg → OracleComp spec Dg) (hF : SpState Dg E C → OracleComp spec (SpState Dg E C))
    (coin : OracleComp spec (E × C)) (s : S) :
    impl.mapStateTBase (implJ P hH hF coin s) =
      implJ P (fun m ↦ simulateQ impl (hH m)) (fun x ↦ simulateQ impl (hF x))
        (simulateQ impl coin) s := by
  funext op
  cases op with
  | pub t =>
    funext st
    simp [QueryImpl.mapStateTBase, implJ, StateT.mk, StateT.run]
    exact simulateQ_hashJ impl hH hF coin t st.2
  | msg => funext st; simp [QueryImpl.mapStateTBase, implJ, StateT.mk, StateT.run]
  | leaf k x =>
    funext st
    by_cases hk : st.1.length < P.cK k
    · simp [QueryImpl.mapStateTBase, implJ, StateT.mk, StateT.run, hk]
    · simp [QueryImpl.mapStateTBase, implJ, StateT.mk, StateT.run, hk]
      exact simulateQ_hashJ impl hH hF coin _ st.2
  | chal t =>
    funext st
    simp [QueryImpl.mapStateTBase, implJ, StateT.mk, StateT.run]
    exact simulateQ_hashJ impl hH hF coin t st.2

/-- **Simulating the oracles commutes with the prover.** -/
theorem simulateQ_proverJ {ι ι' : Type} {spec : OracleSpec.{0, 0} ι}
    {spec' : OracleSpec.{0, 0} ι'} {β : Type} (impl : QueryImpl spec (OracleComp spec'))
    (hH : Msg → OracleComp spec Dg) (hF : SpState Dg E C → OracleComp spec (SpState Dg E C))
    (coin : OracleComp spec (E × C)) (s : S)
    (skel : OracleComp (OpSpec (Msg ⊕ SpState Dg E C) (SpState Dg E C) M K X) β) :
    simulateQ impl (proverJ P hH hF coin s skel) =
      proverJ P (fun m ↦ simulateQ impl (hH m)) (fun x ↦ simulateQ impl (hF x))
        (simulateQ impl coin) s skel := by
  unfold proverJ
  rw [StateT.run'_eq, StateT.run'_eq, simulateQ_map, QueryImpl.simulateQ_mapStateTBase_run,
    mapStateTBase_implJ]

/-! ## In the shadow world, the prover's direct calls are the skeleton's bookkeeping -/

/-- The oracles `H`, `F` and coins of the two-oracle random-oracle model, with a direct call's
edge recorded in the simulator's state as in `common`'s shadow world. -/
noncomputable abbrev recImpl : QueryImpl (unifSpec + hfSpec Msg Dg (SpState Dg E C))
    (StateT (SimState Dg E C) (OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)))) :=
  shadowImpl Pd ∘ₛ hfEmbed (Msg := Msg)

/-- The coins of the two-oracle model, as the prover's completions draw them. -/
noncomputable abbrev coinHF : OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) (E × C) :=
  liftM ($ᵗ (E × C))

theorem recImpl_coin (σ : SimState Dg E C) :
    (simulateQ (recImpl Pd) (coinHF (Msg := Msg) (Dg := Dg) (E := E) (C := C))).run σ =
      (·, σ) <$> coinHF (Msg := Msg) (Dg := Dg) (E := E) (C := C) :=
  run_simulateQ_liftM_of_coins (recImpl Pd) (fun n s ↦ by
    simp [recImpl, hfEmbed, shadowImpl, QueryImpl.apply_compose]) _ σ

theorem recImpl_hQuery (m : Msg) (σ : SimState Dg E C) :
    (simulateQ (recImpl Pd) (hQuery (E := E) (C := C) m)).run σ =
      (·, σ) <$> hQuery (Msg := Msg) (Dg := Dg) (E := E) (C := C) m := by
  simp [recImpl, hfEmbed, shadowImpl, QueryImpl.apply_compose, hQuery]

theorem recImpl_fQuery (x : SpState Dg E C) (σ : SimState Dg E C) :
    (simulateQ (recImpl Pd) (fQuery (Msg := Msg) (Dg := Dg) x)).run σ =
      (fun y ↦ (y, replayStep σ (.forward x, y))) <$> fQuery (Msg := Msg) (Dg := Dg) x := by
  simp [recImpl, hfEmbed, shadowImpl, QueryImpl.apply_compose, fQuery]

theorem recImpl_hashJ (t : Msg ⊕ SpState Dg E C) (J : JCache Msg E C) (σ : SimState Dg E C) :
    (simulateQ (recImpl Pd) ((hashJ (fun m ↦ hQuery (E := E) (C := C) m)
      (fun x ↦ fQuery (Msg := Msg) (Dg := Dg) x) coinHF t).run J)).run σ =
      (fun z ↦ (z, recStep σ t z.1)) <$> (hashJ (fun m ↦ hQuery (E := E) (C := C) m)
        (fun x ↦ fQuery (Msg := Msg) (Dg := Dg) x) coinHF t).run J := by
  rcases t with m | x
  · change (simulateQ (recImpl Pd) (hQuery m >>= _)).run σ = _ <$> (hQuery m >>= _)
    rw [simulateQ_bind, StateT.run_bind, recImpl_hQuery, bind_map_left, map_bind]
    refine bind_congr fun d ↦ ?_
    rcases J m with _ | j
    · simp only [simulateQ_bind, StateT.run_bind, recImpl_coin, bind_map_left, map_bind,
        simulateQ_pure, StateT.run_pure, map_pure]
      rfl
    · simp [recStep]
  · change (simulateQ (recImpl Pd) ((fun y ↦ (y, J)) <$> fQuery x)).run σ =
      _ <$> ((fun y ↦ (y, J)) <$> fQuery x)
    rw [simulateQ_map, StateT.run_map, recImpl_fQuery, Functor.map_map, Functor.map_map]
    rfl

variable (P : Proto S (Msg ⊕ SpState Dg E C) (SpState Dg E C) M K X)

/-- The prover of the two-oracle model: `H`, `F`, and coins for the completions. -/
noncomputable abbrev implHF (s : S) := implJ P (fun m ↦ hQuery (E := E) (C := C) m)
  (fun x ↦ fQuery (Msg := Msg) (Dg := Dg) x) coinHF s

theorem recImpl_implHF_step (hrow : ∀ s h k x, ∃ m, P.rowFn s h k x = .inl m) (s : S)
    (op : Op (Msg ⊕ SpState Dg E C) K X) (st : List (SpState Dg E C) × JCache Msg E C)
    (σ : SimState Dg E C) :
    (simulateQ (recImpl Pd) ((implHF P s op).run st)).run σ =
      (fun z ↦ (z, opRec σ op z.1)) <$> (implHF P s op).run st := by
  cases op with
  | pub t =>
    change (simulateQ (recImpl Pd) ((fun z ↦ (z.1, (st.1, z.2))) <$> _)).run σ = _
    rw [simulateQ_map, StateT.run_map, recImpl_hashJ, Functor.map_map, Functor.map_map]
    rfl
  | msg => simp [implJ, opRec, StateT.run]
  | leaf k x =>
    by_cases hk : st.1.length < P.cK k
    · simp [implJ, opRec, StateT.run, hk]
    · obtain ⟨m, hm⟩ := hrow s (st.1.take (P.cK k)) k x
      change (simulateQ (recImpl Pd) (if st.1.length < P.cK k then _ else _)).run σ =
        _ <$> (if st.1.length < P.cK k then _ else _)
      simp only [hk, ↓reduceIte, hm]
      rw [simulateQ_map, StateT.run_map, recImpl_hashJ, Functor.map_map, Functor.map_map]
      rfl
  | chal t =>
    change (simulateQ (recImpl Pd) ((fun z ↦ (z.1, (if st.1.length < P.n then st.1 ++ [z.1]
      else st.1, z.2))) <$> _)).run σ = _
    rw [simulateQ_map, StateT.run_map, recImpl_hashJ, Functor.map_map, Functor.map_map]
    rfl

/-- **In the shadow world, the prover's direct calls are recorded as the skeleton's
bookkeeping**: the prover run with the direct calls recorded from `σ` is the skeleton with its
bookkeeping from `σ`, run by the prover. -/
theorem recImpl_implHF (hrow : ∀ s h k x, ∃ m, P.rowFn s h k x = .inl m) (s : S) {α : Type}
    (oa : OracleComp (OpSpec (Msg ⊕ SpState Dg E C) (SpState Dg E C) M K X) α)
    (σ : SimState Dg E C) (st : List (SpState Dg E C) × JCache Msg E C) :
    (simulateQ (recImpl Pd) ((simulateQ (implHF P s) oa).run st)).run σ =
      (fun z ↦ ((z.1.1, z.2), z.1.2)) <$>
        (simulateQ (implHF P s) ((simulateQ recOps oa).run σ)).run st := by
  induction oa using OracleComp.inductionOn generalizing σ st with
  | pure a => simp
  | query_bind op k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, recOps_run, bind_map_left, map_bind]
    rw [recImpl_implHF_step Pd P hrow s op st σ, bind_map_left]
    simp only [simulateQ_map, StateT.run_map, bind_map_left]
    sorry

end Setting

end QuotientZk
