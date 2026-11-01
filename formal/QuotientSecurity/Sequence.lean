-- Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
-- file formal/quotient/QuotientSecurity/Sequence.lean. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Distance

/-!
# Zero knowledge for several proofs

Proofs made one after the other against one oracle, each from the state the last one left: the
real experiment and the simulator's give every event on the whole sequence (every proof, every
verdict, the oracle's table after each) probabilities that differ by at most the sum of the
single bounds, the `i`-th with three more hash inputs in the oracle's table than the one before.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

open OracleSpec OracleComp Polynomial Module NNReal

namespace QuotientSecurity

/-- Two experiments that agree on every good outcome, the bad ones being rare in the first,
followed by continuations that are close after every good outcome, are close. -/
theorem probEvent_bind_le_of_eq_on {α β : Type} (X Y : ProbComp α) (good : α → Prop)
    (ε δ : ENNReal) (heq : ∀ a, good a → Pr{let x ← X}[x = a] = Pr{let x ← Y}[x = a])
    (hbad : Pr{let a ← X}[¬ good a] ≤ ε) (f g : α → ProbComp β) (S : β → Prop)
    (hfg : ∀ a, good a → a ∈ support X → Pr{let x ← f a}[S x] ≤ Pr{let x ← g a}[S x] + δ) :
    Pr{let x ← X >>= f}[S x] ≤ Pr{let x ← Y >>= g}[S x] + (ε + δ) := by
  classical
  rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
  have hterm : ∀ a, Pr{let x ← X}[x = a] * Pr{let x ← f a}[S x]
      ≤ Pr{let x ← Y}[x = a] * Pr{let x ← g a}[S x]
        + (Pr{let x ← X}[x = a] * δ + if ¬ good a then Pr{let x ← X}[x = a] else 0) := by
    intro a
    by_cases hg : good a
    · rw [if_neg (not_not.mpr hg), add_zero]
      by_cases hs : a ∈ support X
      · calc Pr{let x ← X}[x = a] * Pr{let x ← f a}[S x]
              ≤ Pr{let x ← X}[x = a] * (Pr{let x ← g a}[S x] + δ) :=
            by gcongr; exact hfg a hg hs
          _ = Pr{let x ← Y}[x = a] * Pr{let x ← g a}[S x] + Pr{let x ← X}[x = a] * δ := by
            rw [mul_add, heq a hg]
      · rw [prEvent_eq_zero_of_not_mem_support X hs]
        simp
    · rw [if_pos hg]
      calc Pr{let x ← X}[x = a] * Pr{let x ← f a}[S x] ≤ Pr{let x ← X}[x = a] * 1 := by
            gcongr; exact (prEvent_le_one _)
        _ = Pr{let x ← X}[x = a] := mul_one _
        _ ≤ _ := le_add_self.trans le_add_self
  refine (ENNReal.tsum_le_tsum hterm).trans ?_
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
    ← OracleComp.prEvent_eq_tsum_ite]
  refine add_le_add_right ?_ _
  rw [add_comm ε δ]
  exact add_le_add (mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)) hbad

variable {K E : Type} [Field K] [Field E] [Algebra K E] [DecidableEq E] [CharP E 2] [Fintype E]
variable {P : Params E} {H : Type} [SampleableType E] [SampleableType H]
variable [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K]

/-- The oracle's table after a proof holds three more hash inputs. -/
theorem table_none (c₀ : (ofFn (ZAnswer P H)).QueryCache) (keys : Finset (ZKey P H))
    (hkeys : ∀ k, k ∉ keys → c₀ k = none) (stmt : Fin P.words → E)
    (c : H × H × (E × E × E) × E × E) (v : (Fin 4 → E) × E × Bool) :
    ∀ k, k ∉ insert (ZKey.first stmt c.1) (insert (ZKey.second stmt c.1 c.2.1)
        (insert (ZKey.third stmt c.1 c.2.1 v.1 v.2.1) keys)) →
      (assemble c₀ stmt c v).2 k = none := by
  intro k hk
  simp only [Finset.mem_insert, not_or] at hk
  obtain ⟨h1, h2, h3, h4⟩ := hk
  show table c₀ stmt c.1 c.2.1 v.1 v.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 k = none
  unfold table
  exact (QueryCache.cacheQuery_of_ne _ _ h3).trans ((QueryCache.cacheQuery_of_ne _ _ h2).trans
    ((QueryCache.cacheQuery_of_ne _ _ h1).trans (hkeys k h4)))

theorem support_openNI (c₀ : (ofFn (ZAnswer P H)).QueryCache) (stmt : Fin P.words → E)
    (gK : Fin 4 → K[X]) (van : K[X]) (o : Outcome (E := E) H × (ofFn (ZAnswer P H)).QueryCache)
    (ho : o ∈ support (openNI c₀ stmt gK van)) : ∃ c v, o = assemble c₀ stmt c v := by
  unfold openNI at ho
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at ho
  obtain ⟨m, -, c, -, rfl⟩ := ho
  exact ⟨c, _, rfl⟩

theorem support_simNI (c₀ : (ofFn (ZAnswer P H)).QueryCache) (stmt : Fin P.words → E)
    (o : Outcome (E := E) H × (ofFn (ZAnswer P H)).QueryCache)
    (ho : o ∈ support (simNI (K := K) c₀ stmt)) : ∃ c v, o = assemble c₀ stmt c v := by
  unfold simNI at ho
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at ho
  obtain ⟨c, -, a, -, rfl⟩ := ho
  exact ⟨c, _, rfl⟩

variable [Fintype H] [DecidableEq H]

/-- **The real experiment for several proofs**: each statement proved with its witness, against
the oracle in the state the last proof left. It outputs every outcome with the table after it. -/
noncomputable def realSeq (van : K[X]) : List ((Fin P.words → E) × (Fin 4 → K[X])) →
    (ofFn (ZAnswer P H)).QueryCache →
    ProbComp (List (Outcome (E := E) H × (ofFn (ZAnswer P H)).QueryCache))
  | [], _ => pure []
  | p :: L, c => realNI c p.1 p.2 van >>= fun o => (fun os => o :: os) <$> realSeq van L o.2

/-- **The simulator for several proofs**: it reads the statements only. -/
noncomputable def simSeq (K : Type) [Field K] [Algebra K E] [Fintype K] [DecidableEq K]
    [FiniteDimensional K E] [SampleableType K] : List ((Fin P.words → E) × (Fin 4 → K[X])) →
    (ofFn (ZAnswer P H)).QueryCache →
    ProbComp (List (Outcome (E := E) H × (ofFn (ZAnswer P H)).QueryCache))
  | [], _ => pure []
  | p :: L, c => simNI (K := K) c p.1 >>= fun o => (fun os => o :: os) <$> simSeq K L o.2

/-- The bound for `k` proofs from an oracle that was asked `q` things. -/
noncomputable def seqBound (P : Params E) (van : K[X]) (H : Type) [Fintype H] : ℕ → ℕ → ENNReal
  | _, 0 => 0
  | q, k + 1 => (zkError P van : ENNReal) + (q : ENNReal) / (Fintype.card H : ENNReal)
      + seqBound P van H (q + 3) k

/-- **Zero knowledge for several proofs.** From an oracle state that holds at most `q` hash
inputs, for every event on the sequence of outcomes and tables, the real experiment and the
simulator's are within `seqBound q k`: the sum over the proofs of the challenges' error and of
`(q + 3 i) / |H|`. -/
theorem zeroKnowledge_seq (h3 : finrank K E = 3) (hE : P.Exact) (van : K[X]) (hvan0 : van ≠ 0)
    (hvan : ∀ x : P.T, aeval (rowPoly.eval (x : E)) van = 0) :
    ∀ (L : List ((Fin P.words → E) × (Fin 4 → K[X])))
      (_hL : ∀ p ∈ L, P.Sat p.1 (P.cells (committed p.2 van 0))) (q : ℕ)
      (c₀ : (ofFn (ZAnswer P H)).QueryCache) (keys : Finset (ZKey P H))
      (_hkeys : ∀ k, k ∉ keys → c₀ k = none) (_hq : keys.card ≤ q)
      (S : List (Outcome (E := E) H × (ofFn (ZAnswer P H)).QueryCache) → Prop),
      Pr{let x ← realSeq van L c₀}[S x]
          ≤ Pr{let x ← simSeq K L c₀}[S x] + seqBound P van H q L.length ∧
        Pr{let x ← simSeq K L c₀}[S x]
          ≤ Pr{let x ← realSeq van L c₀}[S x] + seqBound P van H q L.length
  | [], _, _, _, _, _, _, S => by simp [realSeq, simSeq, seqBound]
  | p :: L, hL, q, c₀, keys, hkeys, hq, S => by
    classical
    obtain ⟨U, hUcard, hU⟩ := exists_handles c₀ p.1 keys hkeys
    obtain ⟨hbadR, hbadS⟩ := prob_not_good c₀ p.1 U hU p.2 van hvan0
    have hsat := hL p List.mem_cons_self
    have hUb : zkBound P van U
        ≤ (zkError P van : ENNReal) + (q : ENNReal) / (Fintype.card H : ENNReal) := by
      unfold zkBound
      refine add_le_add_right (ENNReal.div_le_div_right ?_ _) _
      exact_mod_cast hUcard.trans hq
    have heq : ∀ o, Fresh c₀ p.1 o.1.c₁ ∧ Good (P := P) p.2 van o.1.ch o.1.t →
        Pr{let x ← realNI c₀ p.1 p.2 van}[x = o] = Pr{let x ← simNI (K := K) c₀ p.1}[x = o] :=
      fun o h => realNI_eq_simNI h3 hE c₀ p.1 p.2 van hvan hsat o h.1 h.2
    have hnext : ∀ o : Outcome (E := E) H × (ofFn (ZAnswer P H)).QueryCache,
        (∃ c v, o = assemble c₀ p.1 c v) →
        ∀ S' : List (Outcome (E := E) H × (ofFn (ZAnswer P H)).QueryCache) → Prop,
          Pr{let x ← realSeq van L o.2}[S' x] ≤ Pr{let x ← simSeq K L o.2}[S' x]
              + seqBound P van H (q + 3) L.length ∧
            Pr{let x ← simSeq K L o.2}[S' x] ≤ Pr{let x ← realSeq van L o.2}[S' x]
              + seqBound P van H (q + 3) L.length := by
      rintro o ⟨c, v, rfl⟩ S'
      refine zeroKnowledge_seq h3 hE van hvan0 hvan L
        (fun p' hp' => hL p' (List.mem_cons_of_mem _ hp')) (q + 3) _ _
        (table_none c₀ keys hkeys p.1 c v) ?_ S'
      refine (Finset.card_insert_le _ _).trans ?_
      have := (Finset.card_insert_le (ZKey.second p.1 c.1 c.2.1)
        (insert (ZKey.third p.1 c.1 c.2.1 v.1 v.2.1) keys)).trans
        (Nat.succ_le_succ (Finset.card_insert_le _ _))
      omega
    have hfin : ∀ x : ENNReal, x + (zkBound P van U + seqBound P van H (q + 3) L.length)
        ≤ x + seqBound P van H q (p :: L).length := fun x =>
      add_le_add_right (add_le_add_left hUb _) _
    constructor
    · refine (probEvent_bind_le_of_eq_on (realNI c₀ p.1 p.2 van) (simNI (K := K) c₀ p.1)
        (fun o => Fresh c₀ p.1 o.1.c₁ ∧ Good (P := P) p.2 van o.1.ch o.1.t) _ _ heq hbadR _ _ S
        fun o hg hs => ?_).trans (hfin _)
      rw [prEvent_map, prEvent_map]
      refine (hnext o (support_openNI c₀ p.1 p.2 van o ?_) _).1
      rw [OracleComp.mem_support_iff_prEvent_ne_zero] at hs ⊢
      rwa [← realNI_eq_openNI c₀ p.1 p.2 van o hg.1]
    · refine (probEvent_bind_le_of_eq_on (simNI (K := K) c₀ p.1) (realNI c₀ p.1 p.2 van)
        (fun o => Fresh c₀ p.1 o.1.c₁ ∧ Good (P := P) p.2 van o.1.ch o.1.t) _ _
        (fun o h => (heq o h).symm) hbadS _ _ S fun o hg hs => ?_).trans (hfin _)
      rw [prEvent_map, prEvent_map]
      exact (hnext o (support_simNI c₀ p.1 o hs) _).2

end QuotientSecurity
