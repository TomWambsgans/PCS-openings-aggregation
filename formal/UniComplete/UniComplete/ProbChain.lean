-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Generalises `formal/EndToEnd/Completeness/E2ECompleteness/Chain.lean` (`prEvent_staged_le`) to the univariate
-- verifier's bus challenges; uses its hash discipline (`HashOK`, `cache_of_hashOK`), its fresh query (`prEvent_fresh`,
-- `prEvent_final_le`) and its regular challenge map (`Regular`, `Regular.lean`'s `challengeOf_regular`), and leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two calls
-- `KeccakCalls` and their lazy random oracles.
import E2ECompleteness.Regular

/-!
# The bus challenges in the random-oracle model

Right after `C1`'s root the univariate prover (and the verifier, `reduceWithH`) draws the bus challenges
`α₁, …, α₄, β` as five chained Keccak-256 answers (`sampleW`, `sampleH`): `s₁ = H(x)` with `x` the state, the six
row counts and `C1`'s root word (`88` bytes), then `s_{k+1} = H(s_k)` (`32` bytes each); `α_k = challengeOf s_k`,
`β = challengeOf s₅`. In the two-call random-oracle model these answers are uniform as long as the queries are
fresh, and they are fresh **by their lengths** (`GoodL 88`: everything hashed before them has another length than
`32` and `88`), but for repetitions inside the chain (`s_k = s_j`, `j < k`, each `2^-256`).

**`prEvent_staged5_le`**: for a computation of this shape (`staged5 chal inp A C`: `A` up to the first input
`inp a` of length `L ≠ 32`, the five answers, `C` anything) whose `A` hashes only inputs of other lengths than `32`
and `L`, from a cache with no such input, and a bad set with at most `Nbad` values of `β` for each `α`, the bad event
has probability at most

  `6 / 2^256 + Nbad / 2^192`,

for any challenge map whose fibres have at most `2^64` digests (`Regular`). The `6` are the repetitions
`s₂ = s₁` (`1`), `s₃ ∈ {s₁, s₂}` (`2`), `s₄ ∈ {s₁, s₂, s₃}` (`3`), which would make the `β` query cached;
`s₅` itself is uniform when its query is fresh, and lands in a bad `β`'s fibre with probability at most
`Nbad · 2^64 / 2^256`.

Decisions: the bad event is any `bad : List E → E → Prop` with the count as a hypothesis (`∃ T, |T| ≤ Nbad`, no
decidability asked); only `β`'s query is bounded against it, the `α`'s are arbitrary (the univariate bad set,
`BadFp`, has at most one `β` per divided tuple for every `α`). The cache's invariant (`Inv`): every hashed input is of
another length, the first input, or a digest of an earlier answer.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open E2ECompleteness (ro Cache HashOK hashOK cache_of_hashOK prEvent_fresh prEvent_final_le Regular
  card_digest_ennreal two_pow_256_ne_zero two_pow_256_ne_top length_digestBytes simulateQ_callKeccak256)
open scoped ENNReal

set_option autoImplicit false

namespace UniComplete.Prob

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## Lengths -/

/-- **Another length than the chain's**: not `32` (a state) and not `L` (the first input). -/
def GoodL (L : ℕ) (m : Bytes) : Prop := m.length ≠ 32 ∧ m.length ≠ L

/-- A weaker predicate on the hashed inputs. -/
theorem HashOK.mono {P Q : Bytes → Prop} (hPQ : ∀ m, P m → Q m) {α : Type} {oa : OracleComp KeccakCalls α}
    (h : HashOK P oa) : HashOK Q oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    obtain ⟨ht, hk⟩ := (isQueryBound_query_bind_iff _ _ _ _ _).1 h
    refine (isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨?_, fun u ↦ ih u (hk u)⟩
    rcases t with x | s
    · exact hPQ x ht
    · trivial

/-! ## The chain's shape -/

section Shape

variable {α γ : Type}

/-- **The bus challenges' shape**: `A` up to the first input `inp a`; `s₁ = H(inp a)`, `s_{k+1} = H(s_k)` for
`k < 5`; `C` the rest. Its output carries `([chal s₁, …, chal s₄], chal s₅)`, the `(α, β)` of `sampleW`/`sampleH`
when `chal` is `challengeOf`. -/
def staged5 (chal : Digest → E) (inp : α → Bytes) (A : OracleComp KeccakCalls α)
    (C : α → Digest → Digest → Digest → Digest → Digest → OracleComp KeccakCalls γ) :
    OracleComp KeccakCalls (γ × (List E × E)) := do
  let a ← A
  let s₁ ← callKeccak256 (inp a)
  let s₂ ← callKeccak256 (digestBytes s₁)
  let s₃ ← callKeccak256 (digestBytes s₂)
  let s₄ ← callKeccak256 (digestBytes s₃)
  let s₅ ← callKeccak256 (digestBytes s₄)
  let z ← C a s₁ s₂ s₃ s₄ s₅
  return (z, ([chal s₁, chal s₂, chal s₃, chal s₄], chal s₅))

theorem run_staged5 (chal : Digest → E) (inp : α → Bytes) (A : OracleComp KeccakCalls α)
    (C : α → Digest → Digest → Digest → Digest → Digest → OracleComp KeccakCalls γ) (c₀ : Cache) :
    (simulateQ ro (staged5 chal inp A C)).run c₀ =
      (simulateQ ro A).run c₀ >>= fun p ↦
      (ro (.inl (inp p.1))).run p.2 >>= fun q₁ ↦
      (ro (.inl (digestBytes q₁.1))).run q₁.2 >>= fun q₂ ↦
      (ro (.inl (digestBytes q₂.1))).run q₂.2 >>= fun q₃ ↦
      (ro (.inl (digestBytes q₃.1))).run q₃.2 >>= fun q₄ ↦
      (ro (.inl (digestBytes q₄.1))).run q₄.2 >>= fun q₅ ↦
      (simulateQ ro (C p.1 q₁.1 q₂.1 q₃.1 q₄.1 q₅.1)).run q₅.2 >>= fun z ↦
      pure ((z.1, ([chal q₁.1, chal q₂.1, chal q₃.1, chal q₄.1], chal q₅.1)), z.2) := by
  simp only [staged5, simulateQ_bind, simulateQ_pure, simulateQ_callKeccak256, StateT.run_bind,
    StateT.run_pure]
  rfl

end Shape

/-! ## One query -/

/-- **One query, fresh unless `P`**: if `P` the event is bounded by `1`, otherwise by the average over the uniform
answer. -/
theorem prEvent_query_le {δ : Type} (x : Bytes) (c : Cache) (P : Prop) [Decidable P]
    (hfresh : ¬ P → c (.inl x) = none) (K : Digest × Cache → ProbComp δ) (q : δ → Prop)
    (b : Digest → ℝ≥0∞) (hK : ∀ u, Pr{let z ← K (u, c.cacheQuery (.inl x) u)}[q z] ≤ b u) :
    Pr{let z ← ((ro (.inl x)).run c >>= K)}[q z] ≤ (if P then 1 else 0) + (∑ u, b u) / 2 ^ 256 := by
  by_cases h : P
  · simp only [h, ↓reduceIte]
    exact (prEvent_le_one _).trans le_self_add
  · simp only [h, ↓reduceIte, zero_add]
    rw [prEvent_fresh _ _ (hfresh h)]
    exact ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ hK u) _

/-- The average of a constant. -/
theorem sum_const_div (r : ℝ≥0∞) : (∑ _u : Digest, r) / 2 ^ 256 = r := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_digest_ennreal, mul_comm,
    ENNReal.mul_div_cancel_right two_pow_256_ne_zero two_pow_256_ne_top]

/-- At most `|l|` digests lie in `l`. -/
theorem sum_mem_le (l : List Digest) : (∑ u : Digest, (if u ∈ l then 1 else 0 : ℝ≥0∞)) ≤ l.length := by
  classical
  rw [Finset.sum_boole]
  have hs : (Finset.univ.filter fun u : Digest ↦ u ∈ l) ⊆ l.toFinset := fun u hu ↦
    List.mem_toFinset.mpr (Finset.mem_filter.mp hu).2
  exact_mod_cast (Finset.card_le_card hs).trans (List.toFinset_card_le l)

/-- **The average of a step's bound**: `|l| / 2^256` for the repetitions, then the rest. -/
theorem sum_step_le (l : List Digest) (k : ℕ) (B : ℝ≥0∞) :
    (∑ u : Digest, ((if u ∈ l then 1 else 0) + ((k : ℝ≥0∞) / 2 ^ 256 + B))) / 2 ^ 256 ≤
      ((l.length + k : ℕ) : ℝ≥0∞) / 2 ^ 256 + B := by
  rw [Finset.sum_add_distrib, ENNReal.add_div, sum_const_div, Nat.cast_add, ENNReal.add_div, add_assoc]
  exact add_le_add (ENNReal.div_le_div_right (sum_mem_le l) _) le_rfl

/-- **The last query**: at most `Nbad · 2^64` digests have a challenge in a bad set of at most `Nbad` values. -/
theorem sum_bad_le (chal : Digest → E) (hreg : Regular chal) (badβ : E → Prop) (Nbad : ℕ)
    (hbad : ∃ T : Finset E, T.card ≤ Nbad ∧ ∀ b, badβ b → b ∈ T) [DecidablePred badβ] :
    (∑ u : Digest, (if badβ (chal u) then 1 else 0 : ℝ≥0∞)) / 2 ^ 256 ≤ (Nbad : ℝ≥0∞) / 2 ^ 192 := by
  classical
  obtain ⟨T, hT, hmem⟩ := hbad
  rw [Finset.sum_boole]
  have hsub : (Finset.univ.filter fun u : Digest ↦ badβ (chal u)) ⊆
      T.biUnion fun e ↦ Finset.univ.filter fun d : Digest ↦ chal d = e := by
    intro u hu
    exact Finset.mem_biUnion.mpr ⟨chal u, hmem _ (Finset.mem_filter.mp hu).2, by simp⟩
  have hcard : (Finset.univ.filter fun u : Digest ↦ badβ (chal u)).card ≤ 2 ^ 64 * Nbad := by
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    calc ∑ e ∈ T, (Finset.univ.filter fun d : Digest ↦ chal d = e).card
        ≤ ∑ _e ∈ T, 2 ^ 64 := Finset.sum_le_sum fun e _ ↦ hreg e
      _ = T.card * 2 ^ 64 := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 2 ^ 64 * Nbad := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hT
  have e : (2 : ℝ≥0∞) ^ 256 = 2 ^ 64 * 2 ^ 192 := by rw [← pow_add]
  calc ((Finset.univ.filter fun u : Digest ↦ badβ (chal u)).card : ℝ≥0∞) / 2 ^ 256
      ≤ ((2 ^ 64 * Nbad : ℕ) : ℝ≥0∞) / 2 ^ 256 := ENNReal.div_le_div_right (by exact_mod_cast hcard) _
    _ = (Nbad : ℝ≥0∞) / 2 ^ 192 := by
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, e,
          ENNReal.mul_div_mul_left _ _ (by simp) (by simp)]

/-! ## The cache along the chain -/

/-- **The cache's invariant** after `j` chain queries: every hashed input is of another length (`GoodL L`), of the
first input's length `L`, or the digest of an earlier answer (in `S`). -/
def Inv (L : ℕ) (c : Cache) (S : List Digest) : Prop :=
  ∀ m, c (.inl m) ≠ none → GoodL L m ∨ m.length = L ∨ ∃ s ∈ S, m = digestBytes s

/-- The first query is fresh. -/
theorem fresh_first {L : ℕ} {c : Cache} (hc : ∀ m, c (.inl m) ≠ none → GoodL L m) {x : Bytes}
    (hx : x.length = L) : c (.inl x) = none := by
  by_contra h
  exact (hc x h).2 hx

/-- After the first query. -/
theorem inv_first {L : ℕ} {c : Cache} (hc : ∀ m, c (.inl m) ≠ none → GoodL L m) (x : Bytes)
    (hx : x.length = L) (u : Digest) : Inv L (c.cacheQuery (.inl x) u) [] := by
  intro m hm
  by_cases hmx : (Sum.inl m : Bytes ⊕ KeccakState) = .inl x
  · cases hmx
    exact Or.inr (Or.inl hx)
  · rw [QueryCache.cacheQuery_of_ne _ _ hmx] at hm
    exact Or.inl (hc m hm)

/-- A state's query is fresh unless the state was answered before. -/
theorem fresh_inv {L : ℕ} (hL : L ≠ 32) {c : Cache} {S : List Digest} (h : Inv L c S) {s : Digest}
    (hs : s ∉ S) : c (.inl (digestBytes s)) = none := by
  by_contra hne
  rcases h _ hne with h1 | h1 | ⟨s', hs', he⟩
  · exact h1.1 (length_digestBytes s)
  · exact hL (h1.symm.trans (length_digestBytes s))
  · exact hs (E2ECompleteness.digestBytes_injective he ▸ hs')

/-- After a state's query. -/
theorem inv_cons {L : ℕ} {c : Cache} {S : List Digest} (h : Inv L c S) (s u : Digest) :
    Inv L (c.cacheQuery (.inl (digestBytes s)) u) (s :: S) := by
  intro m hm
  by_cases hms : (Sum.inl m : Bytes ⊕ KeccakState) = .inl (digestBytes s)
  · cases hms
    exact Or.inr (Or.inr ⟨s, List.mem_cons_self, rfl⟩)
  · rw [QueryCache.cacheQuery_of_ne _ _ hms] at hm
    rcases h m hm with h1 | h1 | ⟨s', hs', he⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨s', List.mem_cons_of_mem _ hs', he⟩)

/-! ## The bound -/

/-- **The bus challenges in the random-oracle model.** For a computation of the chain's shape (`staged5`) whose
stage before the first input hashes only inputs of other lengths than `32` and `L` (`HashOK (GoodL L)`), the first
input of length `L ≠ 32`, run from a cache holding no such input, with a regular challenge map and a bad set of at
most `Nbad` values of `β` for each `α`: the bad event has probability at most `6 / 2^256 + Nbad / 2^192`. -/
theorem prEvent_staged5_le {α γ : Type} (chal : Digest → E) (hreg : Regular chal) {L : ℕ} (hL : L ≠ 32)
    (bad : List E → E → Prop) (Nbad : ℕ) (hbad : ∀ as, ∃ T : Finset E, T.card ≤ Nbad ∧ ∀ b, bad as b → b ∈ T)
    (inp : α → Bytes) (hinp : ∀ a, (inp a).length = L) (A : OracleComp KeccakCalls α)
    (C : α → Digest → Digest → Digest → Digest → Digest → OracleComp KeccakCalls γ)
    (hA : HashOK (GoodL L) A) (c₀ : Cache) (hc₀ : ∀ m, c₀ (.inl m) ≠ none → GoodL L m) :
    Pr{let z ← (simulateQ ro (staged5 chal inp A C)).run c₀}[bad z.1.2.1 z.1.2.2] ≤
      6 / 2 ^ 256 + (Nbad : ℝ≥0∞) / 2 ^ 192 := by
  classical
  set B : ℝ≥0∞ := (Nbad : ℝ≥0∞) / 2 ^ 192
  rw [run_staged5]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p hp ↦ ?_
  have hc₁ : ∀ m, p.2 (.inl m) ≠ none → GoodL L m := fun m hm ↦
    (cache_of_hashOK hA c₀ hp m hm).elim (hc₀ m) id
  -- `s₁`: fresh.
  refine (prEvent_query_le _ _ False (fun _ ↦ fresh_first hc₁ (hinp p.1)) _ _
    (fun s₁ ↦ (if s₁ ∈ ([] : List Digest) then 1 else 0) + (((6 : ℕ) : ℝ≥0∞) / 2 ^ 256 + B))
    fun s₁ ↦ ?_).trans ?_
  rotate_left
  · simp only [↓reduceIte, zero_add]
    exact (sum_step_le [] 6 B).trans (le_of_eq (by norm_num))
  have i₁ := inv_first hc₁ (inp p.1) (hinp p.1) s₁
  -- `s₂`: fresh.
  refine (prEvent_query_le _ _ (s₁ ∈ ([] : List Digest)) (fun hs ↦ fresh_inv hL i₁ hs) _ _
    (fun s₂ ↦ (if s₂ ∈ [s₁] then 1 else 0) + (((5 : ℕ) : ℝ≥0∞) / 2 ^ 256 + B)) fun s₂ ↦ ?_).trans ?_
  rotate_left
  · exact add_le_add le_rfl ((sum_step_le [s₁] 5 B).trans (le_of_eq (by norm_num)))
  have i₂ := inv_cons i₁ s₁ s₂
  -- `s₃`: fresh unless `s₂ = s₁`.
  refine (prEvent_query_le _ _ (s₂ ∈ [s₁]) (fun hs ↦ fresh_inv hL i₂ hs) _ _
    (fun s₃ ↦ (if s₃ ∈ [s₂, s₁] then 1 else 0) + (((3 : ℕ) : ℝ≥0∞) / 2 ^ 256 + B)) fun s₃ ↦ ?_).trans ?_
  rotate_left
  · refine add_le_add le_rfl ((sum_step_le [s₂, s₁] 3 B).trans (le_of_eq (by norm_num)))
  have i₃ := inv_cons i₂ s₂ s₃
  -- `s₄`: fresh unless `s₃ ∈ {s₁, s₂}`.
  refine (prEvent_query_le _ _ (s₃ ∈ [s₂, s₁]) (fun hs ↦ fresh_inv hL i₃ hs) _ _
    (fun s₄ ↦ (if s₄ ∈ [s₃, s₂, s₁] then 1 else 0) + (((0 : ℕ) : ℝ≥0∞) / 2 ^ 256 + B)) fun s₄ ↦ ?_).trans ?_
  rotate_left
  · refine add_le_add le_rfl ((sum_step_le [s₃, s₂, s₁] 0 B).trans (le_of_eq (by norm_num)))
  have i₄ := inv_cons i₃ s₃ s₄
  -- `s₅`: fresh unless `s₄ ∈ {s₁, s₂, s₃}`; then uniform, its challenge bad with probability `≤ Nbad / 2^192`.
  refine (prEvent_query_le _ _ (s₄ ∈ [s₃, s₂, s₁]) (fun hs ↦ fresh_inv hL i₄ hs) _ _
    (fun s₅ ↦ if bad [chal s₁, chal s₂, chal s₃, chal s₄] (chal s₅) then 1 else 0) fun s₅ ↦ ?_).trans ?_
  rotate_left
  · refine add_le_add le_rfl ?_
    rw [Nat.cast_zero, ENNReal.zero_div, zero_add]
    exact sum_bad_le chal hreg _ Nbad (hbad _)
  exact prEvent_final_le _ ([chal s₁, chal s₂, chal s₃, chal s₄], chal s₅) (fun v ↦ bad v.1 v.2)

/-! ## The `t` query -/

/-- **The point challenge `t` in the random-oracle model.** For a computation that, after a prefix `X`, queries
`tin x` and then continues, an event that forces `t = chal(answer)` into a bad set (at most `ct` values for every prior
`pr x`) has probability at most the probability that `tin x` is already cached after `X`, plus `ct / 2^192`. (The
cache-hit probability is the only place `t`'s input enters: unlike the bus challenges, it is not fresh by its length,
`64` bytes being a Merkle node's.) -/
theorem prEvent_tquery_le {β γ ω : Type} (chal : Digest → E) (hreg : Regular chal) (badT : List E → E → Prop)
    (ct : ℕ) (hct : ∀ fp, ∃ T : Finset E, T.card ≤ ct ∧ ∀ b, badT fp b → b ∈ T)
    (X : OracleComp KeccakCalls β) (tin : β → Bytes) (pr : β → List E)
    (K : β → Digest → OracleComp KeccakCalls γ) (h : β → Digest → γ → ω) (ev : ω → Prop)
    (hev : ∀ x st z, ev (h x st z) → badT (pr x) (chal st)) (c₀ : Cache) :
    Pr{let z ← (simulateQ ro (X >>= fun x ↦ callKeccak256 (tin x) >>= fun st ↦ K x st >>= fun z ↦
        pure (h x st z))).run c₀}[ev z.1] ≤
      Pr{let p ← (simulateQ ro X).run c₀}[p.2 (.inl (tin p.1)) ≠ none] + (ct : ℝ≥0∞) / 2 ^ 192 := by
  classical
  simp only [simulateQ_bind, simulateQ_callKeccak256, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  refine prEvent_bind_le_prEvent_add_of_support _ _ _ _ fun p _ hp ↦ ?_
  have hfresh : p.2 (.inl (tin p.1)) = none := not_not.mp hp
  rw [prEvent_fresh _ _ hfresh]
  refine le_trans (ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ ?_) _)
    (sum_bad_le chal hreg (badT (pr p.1)) ct (hct _))
  by_cases hb : badT (pr p.1) (chal u)
  · simp only [hb, ↓reduceIte]
    exact prEvent_le_one _
  · simp only [hb, ↓reduceIte]
    refine le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ↦ ?_)
    rw [mem_support_bind_iff] at hz
    obtain ⟨w, -, hz⟩ := hz
    rw [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact fun he ↦ hb (hev _ _ _ he)

end UniComplete.Prob

/-- info: 'UniComplete.Prob.prEvent_staged5_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Prob.prEvent_staged5_le

/-- info: 'UniComplete.Prob.prEvent_tquery_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Prob.prEvent_tquery_le
