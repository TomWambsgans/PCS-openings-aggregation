-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/Joint.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.RandomOracle
import QuotientSecurity.NonInteractive

/-!
# Soundness and simulated proofs in one game

One random oracle, keyed as in the zero knowledge theorem: by the statement and the handles of
the commitments. A commitment is binding: the handle of a message determines it. The adversary
is any computation over this oracle, so it may ask about handles that commit to nothing, as the
simulator's do. `knowledgeSoundness_handles` is the soundness bound in this model, and
`simulationSoundness` the same after any computation over the oracle with its own coins, the
simulator of the zero knowledge theorem run without programming being one.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal Function Polynomial

namespace QuotientSecurity

open Params

variable {E : Type} [Field E] [DecidableEq E] [CharP E 2] [Fintype E] [SampleableType E]
variable {P : Params E} {B : P.Bounds} {H : Type}

/-- An accepted proof of cells that do not satisfy the relation makes one of its three keys
bad. -/
theorem bad_of_accepts (π : Proof P B) (tbl : ∀ k, Answer P B k)
    (hacc : P.Accepts π.stmt π.g.1 π.R.1 (tbl (Key.first π.stmt π.g)).1
      (tbl (Key.first π.stmt π.g)).2.1 (tbl (Key.first π.stmt π.g)).2.2
      (tbl (Key.second π.stmt π.g π.R)) π.v.1 π.v.2 (tbl (Key.third π.stmt π.g π.R π.v)))
    (hsat : ¬ P.Sat π.stmt (P.cells π.g.1)) :
    bad (Key.first π.stmt π.g) tbl ∨ bad (Key.second π.stmt π.g π.R) tbl ∨
      bad (Key.third π.stmt π.g π.R π.v) tbl := by
  by_cases h2 : State₂ π.stmt π.g (tbl (Key.first π.stmt π.g))
  · exact Or.inl ⟨hsat, h2⟩
  · have h3 : ¬ State₃ π.stmt π.g (tbl (Key.first π.stmt π.g)) π.R := by
      rintro (h | h)
      · exact h2 (Or.inl h)
      · exact h2 (Or.inr ⟨_, h⟩)
    by_cases h4 : State₄ π.stmt π.g (tbl (Key.first π.stmt π.g)) π.R
        (tbl (Key.second π.stmt π.g π.R))
    · exact Or.inr (Or.inl ⟨h3, h4⟩)
    · exact Or.inr (Or.inr ⟨h4, Or.inr hacc⟩)

variable (com₁ : B.Msg₁ → H) (com₂ : B.Msg₂ → H)

/-- What the hash absorbs for a proof: its commitments' handles in place of its messages. -/
def keyOf : Key P B → ZKey P H
  | .first stmt g => .first stmt (com₁ g)
  | .second stmt g R => .second stmt (com₁ g) (com₂ R)
  | .third stmt g R v => .third stmt (com₁ g) (com₂ R) v.1 v.2

theorem keyOf_injective (h₁ : Injective com₁) (h₂ : Injective com₂) :
    Injective (keyOf (P := P) com₁ com₂) := by
  intro a b h
  cases a <;> cases b <;> simp only [keyOf, ZKey.first.injEq, ZKey.second.injEq,
    ZKey.third.injEq, reduceCtorEq] at h
  · obtain ⟨rfl, hg⟩ := h
    rw [h₁ hg]
  · obtain ⟨rfl, hg, hR⟩ := h
    rw [h₁ hg, h₂ hR]
  · obtain ⟨rfl, hg, hR, hv1, hv2⟩ := h
    rw [h₁ hg, h₂ hR, Prod.ext hv1 hv2]

/-- The oracle's table, read on proofs. -/
def pull (tbl : ∀ k, ZAnswer P H k) : ∀ k, Answer P B k
  | .first stmt g => tbl (.first stmt (com₁ g))
  | .second stmt g R => tbl (.second stmt (com₁ g) (com₂ R))
  | .third stmt g R v => tbl (.third stmt (com₁ g) (com₂ R) v.1 v.2)

theorem pull_update_of_ne (tbl : ∀ k, ZAnswer P H k) (k : ZKey P H) (u : ZAnswer P H k)
    (key : Key P B) (h : keyOf com₁ com₂ key ≠ k) :
    pull com₁ com₂ (update tbl k u) key = pull com₁ com₂ tbl key := by
  cases key <;> exact update_of_ne h _ _

variable {com₁ com₂}

theorem pull_update_first (h₁ : Injective com₁) (h₂ : Injective com₂) (tbl : ∀ k, ZAnswer P H k)
    (stmt : Fin P.words → E) (g : B.Msg₁) (u : E × E × E) :
    pull com₁ com₂ (update tbl (ZKey.first stmt (com₁ g)) u)
      = update (pull com₁ com₂ tbl) (Key.first stmt g) u := by
  funext k'
  by_cases hk : k' = Key.first stmt g
  · subst hk
    exact (update_self (β := ZAnswer P H) _ _ _).trans
      (update_self (β := Answer P B) (Key.first stmt g) u (pull com₁ com₂ tbl)).symm
  · exact (pull_update_of_ne com₁ com₂ tbl (ZKey.first stmt (com₁ g)) u k'
      fun h => hk (keyOf_injective com₁ com₂ h₁ h₂ h)).trans
      (update_of_ne (β := Answer P B) hk u (pull com₁ com₂ tbl)).symm

theorem pull_update_second (h₁ : Injective com₁) (h₂ : Injective com₂)
    (tbl : ∀ k, ZAnswer P H k) (stmt : Fin P.words → E) (g : B.Msg₁) (R : B.Msg₂) (u : E) :
    pull com₁ com₂ (update tbl (ZKey.second stmt (com₁ g) (com₂ R)) u)
      = update (pull com₁ com₂ tbl) (Key.second stmt g R) u := by
  funext k'
  by_cases hk : k' = Key.second stmt g R
  · subst hk
    exact (update_self (β := ZAnswer P H) _ _ _).trans
      (update_self (β := Answer P B) (Key.second stmt g R) u (pull com₁ com₂ tbl)).symm
  · exact (pull_update_of_ne com₁ com₂ tbl (ZKey.second stmt (com₁ g) (com₂ R)) u k'
      fun h => hk (keyOf_injective com₁ com₂ h₁ h₂ h)).trans
      (update_of_ne (β := Answer P B) hk u (pull com₁ com₂ tbl)).symm

theorem pull_update_third (h₁ : Injective com₁) (h₂ : Injective com₂)
    (tbl : ∀ k, ZAnswer P H k) (stmt : Fin P.words → E) (g : B.Msg₁) (R : B.Msg₂)
    (v : (Fin 4 → E) × E) (u : E) :
    pull com₁ com₂ (update tbl (ZKey.third stmt (com₁ g) (com₂ R) v.1 v.2) u)
      = update (pull com₁ com₂ tbl) (Key.third stmt g R v) u := by
  funext k'
  by_cases hk : k' = Key.third stmt g R v
  · subst hk
    exact (update_self (β := ZAnswer P H) _ _ _).trans
      (update_self (β := Answer P B) (Key.third stmt g R v) u (pull com₁ com₂ tbl)).symm
  · exact (pull_update_of_ne com₁ com₂ tbl (ZKey.third stmt (com₁ g) (com₂ R) v.1 v.2) u k'
      fun h => hk (keyOf_injective com₁ com₂ h₁ h₂ h)).trans
      (update_of_ne (β := Answer P B) hk u (pull com₁ com₂ tbl)).symm

variable (com₁ com₂)

/-- A hash input is bad in a table when it is a proof's key and that key is bad. -/
def badH (k : ZKey P H) (tbl : ∀ k, ZAnswer P H k) : Prop :=
  ∃ key : Key P B, keyOf com₁ com₂ key = k ∧ bad key (pull com₁ com₂ tbl)

variable {com₁ com₂}

theorem prob_badH_le (h₁ : Injective com₁) (h₂ : Injective com₂) (k : ZKey P H)
    (tbl : ∀ k, ZAnswer P H k) :
    Pr{let u ← $ᵗ (ZAnswer P H k)}[badH com₁ com₂ k (update tbl k u)]
      ≤ (roundError P B : ENNReal) := by
  have hinj := keyOf_injective (P := P) com₁ com₂ h₁ h₂
  by_cases hk : ∃ key : Key P B, keyOf com₁ com₂ key = k
  · obtain ⟨key, rfl⟩ := hk
    cases key with
    | first stmt g =>
      refine (prEvent_mono _ _ _ fun u hu => ?_).trans
        (prob_bad_le (Key.first stmt g) (pull com₁ com₂ tbl))
      obtain ⟨key', hkey', hb⟩ := hu
      have := hinj hkey'
      subst this
      have e := pull_update_first h₁ h₂ tbl stmt g u
      exact e ▸ hb
    | second stmt g R =>
      refine (prEvent_mono _ _ _ fun u hu => ?_).trans
        (prob_bad_le (Key.second stmt g R) (pull com₁ com₂ tbl))
      obtain ⟨key', hkey', hb⟩ := hu
      have := hinj hkey'
      subst this
      have e := pull_update_second h₁ h₂ tbl stmt g R u
      exact e ▸ hb
    | third stmt g R v =>
      refine (prEvent_mono _ _ _ fun u hu => ?_).trans
        (prob_bad_le (Key.third stmt g R v) (pull com₁ com₂ tbl))
      obtain ⟨key', hkey', hb⟩ := hu
      have := hinj hkey'
      subst this
      have e := pull_update_third h₁ h₂ tbl stmt g R v u
      exact e ▸ hb
  · have hfalse : ∀ u, ¬ badH com₁ com₂ k (update tbl k u) := fun u ⟨key, hkey, _⟩ =>
      hk ⟨key, hkey⟩
    simp [hfalse]

variable (com₁ com₂)

open Classical in
/-- The verifier, asking the oracle about the handles of the proof's messages. -/
noncomputable def verifyH (π : Proof P B) : OracleComp (ofFn (ZAnswer P H)) Bool :=
  liftM ((ofFn (ZAnswer P H)).query (ZKey.first π.stmt (com₁ π.g))) >>= fun (c : E × E × E) =>
  liftM ((ofFn (ZAnswer P H)).query (ZKey.second π.stmt (com₁ π.g) (com₂ π.R))) >>= fun (t : E) =>
  liftM ((ofFn (ZAnswer P H)).query (ZKey.third π.stmt (com₁ π.g) (com₂ π.R) π.v.1 π.v.2))
    >>= fun (ρ : E) =>
  pure (decide (P.Accepts π.stmt π.g.1 π.R.1 c.1 c.2.1 c.2.2 t π.v.1 π.v.2 ρ))

/-- The experiment: the adversary's statement and proof, and the verifier's decision. -/
noncomputable def experimentH (adv : OracleComp (ofFn (ZAnswer P H)) (Proof P B)) :
    OracleComp (ofFn (ZAnswer P H)) (Proof P B × Bool) :=
  adv >>= fun π => verifyH com₁ com₂ π >>= fun b => pure (π, b)

theorem verifyH_queryBound (π : Proof P B) : IsTotalQueryBound (verifyH com₁ com₂ π) 3 :=
  isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ =>
    isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ =>
      isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ => trivial⟩⟩⟩

variable {com₁ com₂}

/-- **Knowledge soundness with the oracle keyed by handles.** The adversary is any computation
over the oracle of the zero knowledge theorem; with binding commitments, the verifier accepts its
proof while the committed cells do not satisfy the relation with probability at most `(Q + 3)`
times the largest round error. -/
theorem knowledgeSoundness_handles (h₁ : Injective com₁) (h₂ : Injective com₂)
    (adv : OracleComp (ofFn (ZAnswer P H)) (Proof P B)) (Q : ℕ)
    (hQ : IsTotalQueryBound adv Q) :
    Pr{let r ← (simulateQ randomOracle (experimentH com₁ com₂ adv)).run' ∅}[
        r.2 = true ∧ ¬ P.Sat r.1.stmt (P.cells r.1.g.1)]
      ≤ ((Q + 3 : ℕ) : ENNReal) * (roundError P B : ENNReal) := by
  classical
  refine prEvent_randomOracle_le_of_bad_queries (experimentH com₁ com₂ adv) (Q + 3)
    (isTotalQueryBound_bind hQ fun π =>
      (isTotalQueryBound_bind (n₂ := 0) (verifyH_queryBound com₁ com₂ π) fun b => trivial))
    _ (badH com₁ com₂) _ (prob_badH_le h₁ h₂) ?_
  intro tbl hevent
  set π := evalWithAnswerFn (QueryImpl.ofFn tbl) adv with hπ
  have hlog : tableQueryLog (experimentH com₁ com₂ adv) tbl
      = tableQueryLog adv tbl ++
        [⟨ZKey.first π.stmt (com₁ π.g), tbl (ZKey.first π.stmt (com₁ π.g))⟩,
          ⟨ZKey.second π.stmt (com₁ π.g) (com₂ π.R),
            tbl (ZKey.second π.stmt (com₁ π.g) (com₂ π.R))⟩,
          ⟨ZKey.third π.stmt (com₁ π.g) (com₂ π.R) π.v.1 π.v.2,
            tbl (ZKey.third π.stmt (com₁ π.g) (com₂ π.R) π.v.1 π.v.2)⟩] := by
    simp only [experimentH, verifyH, tableQueryLog_bind, bind_assoc, tableQueryLog_query_bind,
      tableQueryLog_pure, List.append_nil, ← hπ, pure_bind]
    rfl
  have heval : evalWithAnswerFn (QueryImpl.ofFn tbl) (experimentH com₁ com₂ adv)
      = (π, decide (P.Accepts π.stmt π.g.1 π.R.1 (tbl (ZKey.first π.stmt (com₁ π.g))).1
          (tbl (ZKey.first π.stmt (com₁ π.g))).2.1 (tbl (ZKey.first π.stmt (com₁ π.g))).2.2
          (tbl (ZKey.second π.stmt (com₁ π.g) (com₂ π.R))) π.v.1 π.v.2
          (tbl (ZKey.third π.stmt (com₁ π.g) (com₂ π.R) π.v.1 π.v.2)))) := by
    simp only [experimentH, verifyH, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
      evalWithAnswerFn_pure, ← hπ]
    rfl
  rw [heval] at hevent
  obtain ⟨hacc, hsat⟩ := hevent
  have hacc' := of_decide_eq_true hacc
  rw [hlog]
  rcases bad_of_accepts π (pull com₁ com₂ tbl) hacc' hsat with hb | hb | hb
  · exact ⟨⟨_, _⟩, List.mem_append_right _ List.mem_cons_self, Key.first π.stmt π.g, rfl, hb⟩
  · exact ⟨⟨_, _⟩, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self),
      Key.second π.stmt π.g π.R, rfl, hb⟩
  · exact ⟨⟨_, _⟩, List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
      Key.third π.stmt π.g π.R π.v, rfl, hb⟩

/-- **Soundness after any computation with coins.** A computation over the oracle with its own
coins runs first, and the adversary gets its output and the coins: the bound is the same, with
that computation's queries counted. -/
theorem soundness_after {Ω α : Type} (h₁ : Injective com₁) (h₂ : Injective com₂)
    (coins : ProbComp Ω) (pre : Ω → OracleComp (ofFn (ZAnswer P H)) α) (q₀ : ℕ)
    (hpre : ∀ ω, IsTotalQueryBound (pre ω) q₀)
    (adv : Ω → α → OracleComp (ofFn (ZAnswer P H)) (Proof P B)) (Q : ℕ)
    (hadv : ∀ ω a, IsTotalQueryBound (adv ω a) Q) :
    Pr{let r ← coins >>= fun ω =>
        (simulateQ randomOracle (experimentH com₁ com₂ (pre ω >>= adv ω))).run' ∅}[
        r.2 = true ∧ ¬ P.Sat r.1.stmt (P.cells r.1.g.1)]
      ≤ ((q₀ + Q + 3 : ℕ) : ENNReal) * (roundError P B : ENNReal) :=
  prEvent_bind_le_of_forall_le coins _ _ fun ω =>
    knowledgeSoundness_handles h₁ h₂ (pre ω >>= adv ω) (q₀ + Q)
      (isTotalQueryBound_bind (hpre ω) (hadv ω))

/-! ## The simulator, without programming

The simulator of the zero knowledge theorem draws its challenges and writes them in the oracle's
table. Its handles being its own, it can as well ask the oracle: the same outcome and table, at
every outcome whose first handle is fresh. -/

theorem probOutput_bind_swap {α β γ : Type} (X : ProbComp α) (Y : ProbComp β)
    (f : α → β → ProbComp γ) (o : γ) :
    Pr{let z ← X >>= fun x => Y >>= fun y => f x y}[z = o]
      = Pr{let z ← Y >>= fun y => X >>= fun x => f x y}[z = o] :=
  (OracleComp.EvalDistEq.bind_bind_swap X Y f).prEvent_eq (· = o)

section Simulator

variable {K : Type} [Field K] [Algebra K E] [Fintype K] [DecidableEq K] [FiniteDimensional K E]
  [SampleableType K] [SampleableType H]

open Classical in
/-- The four values the simulator sends, from its coins: in `K` when the row is. -/
noncomputable def simPick (r : E) (aK : Fin 4 → K) (aE : Fin 4 → E) : Fin 4 → E :=
  if r ∈ Set.range (algebraMap K E) then fun j => algebraMap K E (aK j) else aE

open Classical in
/-- The simulator against the oracle, its handles and coins chosen: it asks for its three
challenges and programs nothing. -/
noncomputable def simRO (stmt : Fin P.words → E) (c₁ c₂ : H) (aK : Fin 4 → K) (aE : Fin 4 → E) :
    OracleComp (ofFn (ZAnswer P H)) (Outcome (E := E) H) :=
  liftM ((ofFn (ZAnswer P H)).query (ZKey.first stmt c₁)) >>= fun (ch : E × E × E) =>
  liftM ((ofFn (ZAnswer P H)).query (ZKey.second stmt c₁ c₂)) >>= fun (t : E) =>
  liftM ((ofFn (ZAnswer P H)).query (ZKey.third stmt c₁ c₂
    (simPick (rowPoly.eval t) aK aE) (P.sigmaPoly.eval t))) >>= fun (ρ : E) =>
  pure ⟨c₁, c₂, simPick (rowPoly.eval t) aK aE, P.sigmaPoly.eval t,
    decide (NotRejected P ch.1 ch.2.1 t (simPick (rowPoly.eval t) aK aE)), ch, t, ρ⟩

theorem simRO_queryBound (stmt : Fin P.words → E) (c₁ c₂ : H) (aK : Fin 4 → K)
    (aE : Fin 4 → E) : IsTotalQueryBound (simRO (P := P) stmt c₁ c₂ aK aE) 3 :=
  isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ =>
    isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ =>
      isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ => trivial⟩⟩⟩

/-- The simulator's experiment without programming, from the oracle state `c₀`. -/
noncomputable def simRun (c₀ : (ofFn (ZAnswer P H)).QueryCache) (stmt : Fin P.words → E) :
    ProbComp (Outcome (E := E) H × (ofFn (ZAnswer P H)).QueryCache) :=
  ($ᵗ H) >>= fun c₁ => ($ᵗ H) >>= fun c₂ => ($ᵗ (Fin 4 → K)) >>= fun aK =>
    ($ᵗ (Fin 4 → E)) >>= fun aE => (simulateQ randomOracle (simRO stmt c₁ c₂ aK aE)).run c₀

open Classical in
theorem run_simRO_fresh (c₀ : (ofFn (ZAnswer P H)).QueryCache) (stmt : Fin P.words → E)
    (c₁ c₂ : H) (aK : Fin 4 → K) (aE : Fin 4 → E) (hf : Fresh c₀ stmt c₁) :
    (simulateQ randomOracle (simRO stmt c₁ c₂ aK aE)).run c₀
      = ($ᵗ (E × E × E)) >>= fun ch => ($ᵗ E) >>= fun t => ($ᵗ E) >>= fun ρ =>
          pure (assemble c₀ stmt (c₁, c₂, ch, t, ρ)
            (simPick (rowPoly.eval t) aK aE, P.sigmaPoly.eval t,
              decide (NotRejected P ch.1 ch.2.1 t (simPick (rowPoly.eval t) aK aE)))) := by
  obtain ⟨h1, h2, h3⟩ := hf
  unfold simRO
  refine (run_query_bind_fresh (ZKey.first stmt c₁) _ c₀ h1).trans ?_
  refine bind_congr fun ch => ?_
  refine (run_query_bind_fresh (ZKey.second stmt c₁ c₂) _ _ (by
    rw [QueryCache.cacheQuery_of_ne _ _ (by intro h; cases h)]; exact h2 c₂)).trans ?_
  refine bind_congr fun t => ?_
  refine (run_query_bind_fresh (ZKey.third stmt c₁ c₂ _ _) _ _ (by
    rw [QueryCache.cacheQuery_of_ne _ _ (by intro h; cases h),
      QueryCache.cacheQuery_of_ne _ _ (by intro h; cases h)]; exact h3 c₂ _ _)).trans ?_
  refine bind_congr fun ρ => ?_
  rfl

theorem run_simRO_handle (c : (ofFn (ZAnswer P H)).QueryCache) (stmt : Fin P.words → E)
    (c₁ c₂ : H) (aK : Fin 4 → K) (aE : Fin 4 → E)
    (y : Outcome (E := E) H × (ofFn (ZAnswer P H)).QueryCache)
    (hy : y ∈ support ((simulateQ randomOracle (simRO stmt c₁ c₂ aK aE)).run c)) :
    y.1.c₁ = c₁ := by
  unfold simRO at hy
  obtain ⟨ch, ca, hy⟩ := support_run_query_bind _ _ _ _ hy
  obtain ⟨t, cb, hy⟩ := support_run_query_bind _ _ _ _ hy
  obtain ⟨ρ, cc, hy⟩ := support_run_query_bind _ _ _ _ hy
  rw [simulateQ_pure] at hy
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
  rw [hy]

/-- **The simulator need not program.** At every outcome whose first handle is fresh, asking the
oracle gives the outcome and table the programming simulator gives, with the same probability. -/
theorem simRun_eq_simNI (c₀ : (ofFn (ZAnswer P H)).QueryCache) (stmt : Fin P.words → E)
    (o : Outcome (E := E) H × (ofFn (ZAnswer P H)).QueryCache) (hf : Fresh c₀ stmt o.1.c₁) :
    Pr{let x ← simRun (K := K) c₀ stmt}[x = o]
      = Pr{let x ← simNI (K := K) c₀ stmt}[x = o] := by
  classical
  unfold simRun simNI challenges
  simp only [bind_assoc, pure_bind]
  refine prEvent_bind_congr _ _ _ _ _ fun c₁ => ?_
  by_cases hc : o.1.c₁ = c₁
  · rw [hc] at hf
    refine prEvent_bind_congr _ _ _ _ _ fun c₂ => ?_
    simp only [run_simRO_fresh c₀ stmt c₁ c₂ _ _ hf]
    refine (prEvent_bind_congr _ _ _ _ _ fun aK => probOutput_bind_swap _ _ _ o).trans ?_
    refine (prEvent_bind_congr _ _ _ _ _ fun aK => prEvent_bind_congr _ _ _ _ _ fun ch =>
      probOutput_bind_swap _ _ _ o).trans ?_
    refine (prEvent_bind_congr _ _ _ _ _ fun aK => prEvent_bind_congr _ _ _ _ _ fun ch =>
      prEvent_bind_congr _ _ _ _ _ fun t => probOutput_bind_swap _ _ _ o).trans ?_
    refine (probOutput_bind_swap _ _ _ o).trans ?_
    refine (prEvent_bind_congr _ _ _ _ _ fun ch => probOutput_bind_swap _ _ _ o).trans ?_
    refine (prEvent_bind_congr _ _ _ _ _ fun ch => prEvent_bind_congr _ _ _ _ _ fun t =>
      probOutput_bind_swap _ _ _ o).trans ?_
    refine prEvent_bind_congr _ _ _ _ _ fun ch => prEvent_bind_congr _ _ _ _ _ fun t =>
      prEvent_bind_congr _ _ _ _ _ fun ρ => ?_
    unfold simValues simPick
    split_ifs with hr
    · refine EvalDistEq.prEvent_eq ?_ (· = o)
      simp only [bind_map_left]
      exact EvalDistEq.bind_right _ fun aK => OracleComp.EvalDistEq.bind_const _ _
    · exact (OracleComp.EvalDistEq.bind_const _ _).prEvent_eq (· = o)
  · have hl : Pr{let x ← (($ᵗ H) >>= fun c₂ => ($ᵗ (Fin 4 → K)) >>= fun aK =>
        ($ᵗ (Fin 4 → E)) >>= fun aE =>
          (simulateQ randomOracle (simRO stmt c₁ c₂ aK aE)).run c₀)}[x = o] = 0 := by
      refine (prEvent_eq_zero_of_not_mem_support _) fun hmem => hc ?_
      simp only [mem_support_bind_iff] at hmem
      obtain ⟨c₂, -, aK, -, aE, -, hy⟩ := hmem
      exact run_simRO_handle c₀ stmt c₁ c₂ aK aE o hy
    have hr : Pr{let x ← (($ᵗ H) >>= fun c₂ => ($ᵗ (E × E × E)) >>= fun ch =>
        ($ᵗ E) >>= fun t => ($ᵗ E) >>= fun ρ => simValues (K := K) (rowPoly.eval t) >>= fun a =>
          (pure (assemble c₀ stmt (c₁, c₂, ch, t, ρ) (a, P.sigmaPoly.eval t,
            decide (NotRejected P ch.1 ch.2.1 t a))) : ProbComp _))}[x = o] = 0 := by
      refine (prEvent_eq_zero_of_not_mem_support _) fun hmem => hc ?_
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hmem
      obtain ⟨c₂, -, ch, -, t, -, ρ, -, a, -, rfl⟩ := hmem
      rfl
    rw [hl, hr]

/-- The simulator's coins: two handles and its values. -/
noncomputable def simCoins (K E H : Type) [SampleableType H] [SampleableType (Fin 4 → K)]
    [SampleableType (Fin 4 → E)] : ProbComp (H × H × (Fin 4 → K) × (Fin 4 → E)) :=
  ($ᵗ H) >>= fun c₁ => ($ᵗ H) >>= fun c₂ => ($ᵗ (Fin 4 → K)) >>= fun aK =>
    ($ᵗ (Fin 4 → E)) >>= fun aE => pure (c₁, c₂, aK, aE)

/-- **Soundness after a simulated proof**, in one oracle game. The simulator makes a proof of a
statement fixed in advance by asking the oracle; the adversary, given it, then outputs a
statement and a proof. With binding commitments, the verifier accepts while the committed cells
do not satisfy the relation with probability at most `(Q + 6)` times the largest round error. -/
theorem simulationSoundness (h₁ : Injective com₁) (h₂ : Injective com₂)
    (stmt₀ : Fin P.words → E)
    (adv : Outcome (E := E) H → OracleComp (ofFn (ZAnswer P H)) (Proof P B)) (Q : ℕ)
    (hadv : ∀ o, IsTotalQueryBound (adv o) Q) :
    Pr{let r ← simCoins K E H >>= fun ω =>
        (simulateQ randomOracle (experimentH com₁ com₂
          (simRO stmt₀ ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 >>= adv))).run' ∅}[
        r.2 = true ∧ ¬ P.Sat r.1.stmt (P.cells r.1.g.1)]
      ≤ ((3 + Q + 3 : ℕ) : ENNReal) * (roundError P B : ENNReal) :=
  soundness_after h₁ h₂ (simCoins K E H) (fun ω => simRO stmt₀ ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) 3
    (fun ω => simRO_queryBound stmt₀ _ _ _ _) (fun _ => adv) Q fun _ => hadv

end Simulator

end QuotientSecurity
