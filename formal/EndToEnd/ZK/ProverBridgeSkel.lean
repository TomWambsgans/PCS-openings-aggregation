-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.ProverBridgeHom

/-!
# The skeleton's prover with a fixed oracle

`QuotientZk`'s real game runs the skeleton by `proverJ` (`QuotientZk/RpmDuplexProver.lean`): every
operation's answer is the oracle `G : Inp → Out`, Keccak-256 of `m` the digest `(G (inl m)).1` and
the permutation of `x` the state `(G (inr x)).2`; the other halves (a state for a Keccak-256 input, a
digest for a permutation input) are **completions**, drawn by the prover's coins the first time and
kept in a table.

With Keccak-256 and the permutation fixed (answered purely: `h`, `f`), every output of `proverJ` is the
skeleton run in `Id` against **one** oracle `Gof h f gH gF` whose completions are some functions `gH`,
`gF` (**`mem_support_proverJ`**): the tables only grow, and the functions are the final tables
completed arbitrarily. So a statement about the skeleton for every completion (`skelDet`) is a
statement about every output of the real game's prover.
-/

open OracleComp OracleSpec Common
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec)
open QuotientZk.DRpm (implJ proverJ hashJ JTab)

namespace PcsQuotient.EndToEnd

open QuotientZk (Proto)

set_option linter.unusedSectionVars false

/-- **The oracle** of Keccak-256 `h`, the permutation `f`, and the completions `gH`, `gF`. -/
def Gof (h : List UInt8 → DigestBytes) (f : KSt → KSt) (gH : List UInt8 → KSt)
    (gF : KSt → DigestBytes) : Inp → Out
  | .inl m => (h m, gH m)
  | .inr x => (gF x, f x)

section Skel

variable {S : Type} (P : Proto S Inp Out Msg Tbl Pos)

/-- **The prover's operations against a fixed oracle `G`**, in `Id`: `implJ` with every answer
`G`'s. -/
def implDet (G : Inp → Out) (s : S) : QueryImpl DSpec (StateT (List Out) Id)
  | .pub t => fun hist ↦ pure (G t, hist)
  | .msg => fun hist ↦ pure (P.msgFn s hist, hist)
  | .leaf k x => fun hist ↦
    if hist.length < P.cK k then pure (default, hist)
    else pure (G (P.rowFn s (hist.take (P.cK k)) k x), hist)
  | .chal t => fun hist ↦ pure (G t, if hist.length < P.n then hist ++ [G t] else hist)

/-- A run against `G` from the challenges `hist`. -/
def runDet (G : Inp → Out) (s : S) {β : Type} (X : OracleComp DSpec β) (hist : List Out) :
    β × List Out :=
  ((simulateQ (implDet P G s) X).run hist).run

/-- **The skeleton's output against the oracle `G`**, for the secret `s`. -/
def skelDet (G : Inp → Out) (s : S) {β : Type} (X : OracleComp DSpec β) : β :=
  (runDet P G s X []).1

theorem runDet_query_bind (G : Inp → Out) (s : S) {β : Type} (op : DSpec.Domain)
    (k : DSpec.Range op → OracleComp DSpec β) (hist : List Out) :
    runDet P G s (liftM (DSpec.query op) >>= k) hist =
      runDet P G s (k ((implDet P G s op).run hist).run.1) ((implDet P G s op).run hist).run.2 := by
  unfold runDet
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, StateT.run_bind]
  rfl

/-! ## The completions' tables -/

/-- The completions `gH`, `gF` extend the tables `J`. -/
def Ext (J : JTab) (gH : List UInt8 → KSt) (gF : KSt → DigestBytes) : Prop :=
  (∀ m j, J.1 m = some j → gH m = j) ∧ (∀ x j, J.2 x = some j → gF x = j)

theorem ext_tables (J : JTab) :
    Ext J (fun m ↦ (J.1 m).getD default) (fun x ↦ (J.2 x).getD default) :=
  ⟨fun _ _ h ↦ by simp [h], fun _ _ h ↦ by simp [h]⟩

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} [∀ t, SampleableType (spec.Range t)]

/-- **One oracle step**: its answer is `G`'s for every completion extending the table after it, and
those extend the table before it. -/
theorem hashJ_step (h : List UInt8 → DigestBytes) (f : KSt → KSt) (cH : OracleComp spec KSt)
    (cF : OracleComp spec DigestBytes) (t : Inp) (J : JTab) {z : Out × JTab}
    (hz : z ∈ support ((hashJ (fun m ↦ pure (h m)) (fun x ↦ pure (f x)) cH cF t).run J))
    (gH : List UInt8 → KSt) (gF : KSt → DigestBytes) (hext : Ext z.2 gH gF) :
    Ext J gH gF ∧ z.1 = Gof h f gH gF t := by
  rcases t with m | x
  · change z ∈ support ((pure (h m) : OracleComp spec _) >>= fun d ↦
      match J.1 m with
      | some j => pure ((d, j), J)
      | none => cH >>= fun j ↦ pure ((d, j), (J.1.cacheQuery m j, J.2))) at hz
    rw [pure_bind] at hz
    rcases hJ : J.1 m with _ | j
    · rw [hJ] at hz
      obtain ⟨j, -, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
      rw [mem_support_pure_iff] at hz
      subst hz
      refine ⟨⟨fun m' j' hm' ↦ hext.1 m' j' ?_, hext.2⟩, ?_⟩
      · have hne : m' ≠ m := fun e ↦ by rw [e, hJ] at hm'; cases hm'
        show (J.1.cacheQuery m j) m' = some j'
        rw [QueryCache.cacheQuery_of_ne _ _ hne, hm']
      · show ((h m, j) : Out) = (h m, gH m)
        rw [hext.1 m j (QueryCache.cacheQuery_self _ _ _)]
    · rw [hJ] at hz
      rw [mem_support_pure_iff] at hz
      subst hz
      exact ⟨hext, by show ((h m, j) : Out) = (h m, gH m); rw [hext.1 m j hJ]⟩
  · change z ∈ support ((pure (f x) : OracleComp spec _) >>= fun y ↦
      match J.2 x with
      | some j => pure ((j, y), J)
      | none => cF >>= fun j ↦ pure ((j, y), (J.1, J.2.cacheQuery x j))) at hz
    rw [pure_bind] at hz
    rcases hJ : J.2 x with _ | j
    · rw [hJ] at hz
      obtain ⟨j, -, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
      rw [mem_support_pure_iff] at hz
      subst hz
      refine ⟨⟨hext.1, fun x' j' hx' ↦ hext.2 x' j' ?_⟩, ?_⟩
      · have hne : x' ≠ x := fun e ↦ by rw [e, hJ] at hx'; cases hx'
        show (J.2.cacheQuery x j) x' = some j'
        rw [QueryCache.cacheQuery_of_ne _ _ hne, hx']
      · show ((j, f x) : Out) = (gF x, f x)
        rw [hext.2 x j (QueryCache.cacheQuery_self _ _ _)]
    · rw [hJ] at hz
      rw [mem_support_pure_iff] at hz
      subst hz
      exact ⟨hext, by show ((j, f x) : Out) = (gF x, f x); rw [hext.2 x j hJ]⟩

/-- **One operation**: its answer and the challenges after it are the fixed oracle's for every
completion extending the table after it. -/
theorem implJ_step (h : List UInt8 → DigestBytes) (f : KSt → KSt) (cH : OracleComp spec KSt)
    (cF : OracleComp spec DigestBytes) (s : S) (op : DSpec.Domain) (hist : List Out) (J : JTab)
    {z : DSpec.Range op × (List Out × JTab)}
    (hz : z ∈ support ((implJ P (fun m ↦ pure (h m)) (fun x ↦ pure (f x)) cH cF s op).run (hist, J)))
    (gH : List UInt8 → KSt) (gF : KSt → DigestBytes) (hext : Ext z.2.2 gH gF) :
    Ext J gH gF ∧ (z.1, z.2.1) = ((implDet P (Gof h f gH gF) s op).run hist).run := by
  cases op with
  | pub t =>
    change z ∈ support ((fun y ↦ (y.1, (hist, y.2))) <$>
      (hashJ (fun m ↦ pure (h m)) (fun x ↦ pure (f x)) cH cF t).run J) at hz
    rw [support_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨hJ, hy1⟩ := hashJ_step h f cH cF t J hy gH gF hext
    refine ⟨hJ, ?_⟩
    simp only [implDet, StateT.run]
    rw [← hy1]
    rfl
  | msg =>
    change z ∈ support (pure (P.msgFn s hist, (hist, J)) : OracleComp spec _) at hz
    rw [mem_support_pure_iff] at hz
    subst hz
    exact ⟨hext, rfl⟩
  | leaf k x =>
    by_cases hk : hist.length < P.cK k
    · change z ∈ support (if hist.length < P.cK k then pure (default, (hist, J)) else
        (fun y ↦ (y.1, (hist, y.2))) <$> (hashJ (fun m ↦ pure (h m)) (fun x ↦ pure (f x)) cH cF
          (P.rowFn s (hist.take (P.cK k)) k x)).run J) at hz
      simp only [hk, ↓reduceIte, mem_support_pure_iff] at hz
      subst hz
      refine ⟨hext, ?_⟩
      simp only [implDet, StateT.run, hk, ↓reduceIte]
      rfl
    · change z ∈ support (if hist.length < P.cK k then pure (default, (hist, J)) else
        (fun y ↦ (y.1, (hist, y.2))) <$> (hashJ (fun m ↦ pure (h m)) (fun x ↦ pure (f x)) cH cF
          (P.rowFn s (hist.take (P.cK k)) k x)).run J) at hz
      simp only [hk, ↓reduceIte, support_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨hJ, hy1⟩ := hashJ_step h f cH cF _ J hy gH gF hext
      refine ⟨hJ, ?_⟩
      simp only [implDet, StateT.run, hk, ↓reduceIte]
      rw [← hy1]
      rfl
  | chal t =>
    change z ∈ support ((fun y ↦ (y.1, (if hist.length < P.n then hist ++ [y.1] else hist, y.2))) <$>
      (hashJ (fun m ↦ pure (h m)) (fun x ↦ pure (f x)) cH cF t).run J) at hz
    rw [support_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨hJ, hy1⟩ := hashJ_step h f cH cF t J hy gH gF hext
    refine ⟨hJ, ?_⟩
    simp only [implDet, StateT.run]
    rw [← hy1]
    rfl

/-- **Every output of the prover with Keccak-256 and the permutation fixed is the skeleton's against
one oracle**: some completions `gH`, `gF` extending the tables it started from. -/
theorem mem_support_implJ_run (h : List UInt8 → DigestBytes) (f : KSt → KSt)
    (cH : OracleComp spec KSt) (cF : OracleComp spec DigestBytes) (s : S) {β : Type}
    (X : OracleComp DSpec β) :
    ∀ (hist : List Out) (J : JTab) (z : β × (List Out × JTab)),
      z ∈ support ((simulateQ (implJ P (fun m ↦ pure (h m)) (fun x ↦ pure (f x)) cH cF s) X).run
        (hist, J)) →
      ∃ gH gF, Ext J gH gF ∧ (z.1, z.2.1) = runDet P (Gof h f gH gF) s X hist := by
  induction X using OracleComp.inductionOn with
  | pure a =>
    intro hist J z hz
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst hz
    exact ⟨_, _, ext_tables J, rfl⟩
  | query_bind op k ih =>
    intro hist J z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind] at hz
    obtain ⟨z₀, hz₀, hz⟩ := (mem_support_bind_iff _ _ _).mp hz
    obtain ⟨gH, gF, hext, hrun⟩ := ih z₀.1 z₀.2.1 z₀.2.2 z hz
    obtain ⟨hJ, hstep⟩ := implJ_step P h f cH cF s op hist J hz₀ gH gF hext
    refine ⟨gH, gF, hJ, ?_⟩
    rw [runDet_query_bind, ← hstep]
    exact hrun

/-- **Every proof of `proverJ` with Keccak-256 `h` and the permutation `f` is `skelDet`'s** against
`Gof h f gH gF` for some completions. -/
theorem mem_support_proverJ (h : List UInt8 → DigestBytes) (f : KSt → KSt)
    (cH : OracleComp spec KSt) (cF : OracleComp spec DigestBytes) (s : S) {β : Type}
    (X : OracleComp DSpec β) (pf : β)
    (hpf : pf ∈ support (proverJ P (fun m ↦ pure (h m)) (fun x ↦ pure (f x)) cH cF s X)) :
    ∃ gH gF, pf = skelDet P (Gof h f gH gF) s X := by
  unfold proverJ at hpf
  rw [StateT.run'_eq, support_map] at hpf
  obtain ⟨z, hz, rfl⟩ := hpf
  obtain ⟨gH, gF, -, hrun⟩ := mem_support_implJ_run P h f cH cF s X [] (∅, ∅) z hz
  exact ⟨gH, gF, by unfold skelDet; rw [← hrun]⟩

end Skel

end PcsQuotient.EndToEnd
