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
    exact bind_congr fun z ↦ ih z.1 _ z.2

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

end QuotientZk.DRpm
