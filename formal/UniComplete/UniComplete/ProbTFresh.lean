-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Follows `formal/EndToEnd/Completeness/E2ECompleteness/Chain.lean` (`HashOK`, `cache_of_hashOK`, the lazy random
-- oracle's fresh answer `prEvent_fresh`) for the point challenge's query; uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two calls
-- `KeccakCalls`, their lazy random oracles, the weight calculus `Common.QueryCostAtMost`; and VCVio's swap of two
-- independent computations (`prEvent_bind_bind_swap_of_uniform`).
import UniComplete.ProbExp
import UniComplete.ProverCost
import UniComplete.FlockProver
import E2ECompleteness.End

/-!
# `t`'s query is fresh (`TQueryFresh`), for Flock's honest prover

`TQueryFresh flock D εt` (`ProbExp.lean`): in the two-call random-oracle model, the input of the query that draws the
point challenge `t`, `tInput` of the writer after `C2`'s root (the state's `32` bytes, then the bytes since the last
challenge), is already cached when it is asked with probability at most `εt`. Proved here for Flock's honest prover
`FlockP.flockProve` (as the parameter, `fun H ↦ FlockP.flockProve H`: definitionally `flockProveH` of branch
`lean-uni-fcostc`'s `FlockCost.lean`, so the theorems apply to it by `exact`):

* **`tQueryFresh_flockProve`**: for every deployment, `εt = tFreshBound D = (n + 1) · M / 2^256`, `n = tSteps D`
  the challenges after the first bus challenge (`α₂ … α₄`, `β`, `γ`, Flock's), `M = tCache D` a bound on the hashed
  inputs (stage A's `stageACost`, the chain's, `C2`'s tree's `c2Cost`, one);
* **`tQueryFresh_reference`**: at the reference shape, `εt = 2^-200` (`n = 72`, `M < 2^28`: `(72 + 1) · 2^28 / 2^256
  < 2^-221`), the hypothesis `uniCompleteness_reference` takes.

**The argument (a chain of challenges).** After the first bus challenge (`88` bytes, fresh by its length,
`hashA_stagedU`), every challenge until `t` hashes the previous challenge's answer first (`sampleW`: the state, then
the bytes since): the bus chain's `s₂ … s₅`, `γ`, Flock's (its sampled coordinates, the skip's `z`, the rounds', `α`,
the lincheck's, the ring map's six). Call the current answer `s`. *Invariant*: no cached input begins with `s`'s 32
bytes (`¬ Hit c s`). Then the next challenge's input is fresh, its answer `u` uniform, and `Hit c' u` only if a cached
input begins with `u`'s bytes (at most `|c|` of the `2^256` answers, `sum_hit_le`) or the input just asked does
(`u = s`, one more). **`C2`'s tree** comes between Flock's last challenge (a `32`-byte query, the ring map's last,
`wend_samplesW2`) and `t`, and it hashes `512`- and `64`-byte inputs whose leaves do not depend on that last answer:
it never asks the last query (by its length), so its run from the cache with the last answer is its run without it,
the answer added (**`run_frame`**); the uniform answer and the tree's run are independent and swap
(**`prEvent_swap_unif`**), and the invariant at the tree's cache costs `|tree| / 2^256` more. `t`'s input begins with
the last answer's 32 bytes, so a cached `t` input is a hit. Each of the `n` steps costs at most `M / 2^256`, the
first (from the first bus challenge) too: **`prHit_le`**, by strong induction on the steps, on chains described by
**`ChainF`** (`ret`: the final state; `step`: a challenge on the current state; `stepT`: the last `32`-byte challenge
followed by an independent tail `T`).

**Decisions.**

* The chains are an inductive predicate on the computation (`ChainF Q n N s X`: at most `n` challenges and `N`
  hashed inputs from state `s`, the final output and state in `Q`), with inequalities in the constructors so that
  `ChainF.mono` and `cases` are immediate; the writer's programs are lifted to it by `WCh` (a chain from every
  writer, its state the chain's) and `WEnd`/`EndsT` (a chain that ends with a `32`-byte challenge, stated by
  continuation: any independent tail and any chain after it).
* Hashed inputs are counted by `HC` (one per Keccak-256 query, none per permutation call), from the block counts of
  `ProverCost.lean`/`E2ECompleteness.Cost` (`hc_of_qc`: a query costs at least one block), so no bound on the program
  IV's length is needed (its one query counts one).
* Flock's prover is used at `flockMain` only through its code (`FlockP.frontW`, `endW`, `ringEndW`): its chain
  (`wend_flockProve`, any variant whose slices are sent) needs no hypothesis (`FlockCommutes` is not used).
* The event is weakened to `Hit` at the final state (any cached input beginning with it), which `t`'s input implies
  (`take_digestBytes`).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open UniStatement
open E2ECompleteness (ro Cache HashOK hashOK cache_of_hashOK prEvent_fresh ro_run_fresh mem_support_ro_run
  simulateQ_callKeccak256 length_digestBytes)
open scoped ENNReal

set_option autoImplicit false

namespace UniComplete.Prob

namespace TFresh

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## Counting hashed inputs -/

/-- A Keccak-256 query counts one, a permutation call nothing. -/
def hq : KeccakCalls.Domain → ℕ
  | .inl _ => 1
  | .inr _ => 0

/-- **At most `n` Keccak-256 queries** on every path. -/
abbrev HC {α : Type} (X : OracleComp KeccakCalls α) (n : ℕ) : Prop := Common.QueryCostAtMost X hq n

/-- A block count bounds the hash count (a query costs at least one block). -/
theorem hc_of_qc {α : Type} {X : OracleComp KeccakCalls α} {n : ℕ}
    (h : Common.QueryCostAtMost X hashBlocks n) : HC X n := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [Common.isWeightBound_query_bind_iff] at h
    show Common.QueryCostAtMost _ hq n
    rw [Common.isWeightBound_query_bind_iff]
    have hle : hq t ≤ hashBlocks t := by
      rcases t with x | s
      · show 1 ≤ x.length / 136 + 1
        omega
      · exact Nat.zero_le _
    exact ⟨hle.trans h.1, fun u ↦ Common.QueryCostAtMost.mono (ih u (h.2 u)) (by omega)⟩

theorem hc_H (x : Bytes) : HC (callKeccak256 x) 1 := Common.isWeightBound_query hq (Sum.inl x)

/-- **The cache's hashed inputs** lie in a finite set of at most `K`. -/
def CacheBound (c : Cache) (K : ℕ) : Prop :=
  ∃ L : Finset Bytes, L.card ≤ K ∧ ∀ m, c (.inl m) ≠ none → m ∈ L

theorem cacheBound_empty : CacheBound ∅ 0 := ⟨∅, le_rfl, fun _ h ↦ absurd rfl h⟩

theorem CacheBound.mono {c : Cache} {K K' : ℕ} (h : CacheBound c K) (hK : K ≤ K') : CacheBound c K' :=
  let ⟨L, hL, hm⟩ := h
  ⟨L, hL.trans hK, hm⟩

theorem CacheBound.cacheQuery_inl {c : Cache} {K : ℕ} (h : CacheBound c K) (x : Bytes) (u : Digest) :
    CacheBound (c.cacheQuery (.inl x) u) (K + 1) := by
  obtain ⟨L, hL, hm⟩ := h
  refine ⟨insert x L, (Finset.card_insert_le _ _).trans (by omega), fun m hc ↦ ?_⟩
  by_cases hmx : m = x
  · rw [hmx]
    exact Finset.mem_insert_self _ _
  · rw [QueryCache.cacheQuery_of_ne _ _ (fun h ↦ hmx (Sum.inl_injective h))] at hc
    exact Finset.mem_insert_of_mem (hm m hc)

theorem CacheBound.cacheQuery_inr {c : Cache} {K : ℕ} (h : CacheBound c K) (s v : KeccakState) :
    CacheBound (c.cacheQuery (.inr s) v) K := by
  obtain ⟨L, hL, hm⟩ := h
  exact ⟨L, hL, fun m hc ↦ hm m (by rwa [QueryCache.cacheQuery_of_ne _ _ Sum.inl_ne_inr] at hc)⟩

/-- **A run adds at most its hash count** to the cache's hashed inputs. -/
theorem cacheBound_run {α : Type} {X : OracleComp KeccakCalls α} {n : ℕ} (hX : HC X n) :
    ∀ {c : Cache} {K : ℕ}, CacheBound c K → ∀ {z : α × Cache}, z ∈ support ((simulateQ ro X).run c) →
      CacheBound z.2 (K + n) := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure a =>
    intro c K hc z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hc.mono (Nat.le_add_right _ _)
  | query_bind t k ih =>
    intro c K hc z hz
    have hX' := (Common.isWeightBound_query_bind_iff _ _ _ _).1 hX
    simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self, OracleQuery.cont_query,
      StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨u, c₁⟩, hu, hz⟩ := hz
    have hc₁ : CacheBound c₁ (K + hq t) := by
      rcases mem_support_ro_run hu with e | ⟨v, e⟩
      · simp only at e
        subst e
        exact hc.mono (Nat.le_add_right _ _)
      · simp only at e
        subst e
        rcases t with x | s
        · exact hc.cacheQuery_inl x v
        · exact hc.cacheQuery_inr s v
    exact (ih u (hX'.2 u) hc₁ hz).mono (by have := hX'.1; omega)

/-! ## Hits -/

/-- **A hit at `s`**: a hashed input begins with `s`'s `32` bytes. -/
def Hit (c : Cache) (s : Digest) : Prop := ∃ m, c (.inl m) ≠ none ∧ m.take 32 = digestBytes s

theorem take_digestBytes (s : Digest) (e : Bytes) : (digestBytes s ++ e).take 32 = digestBytes s :=
  List.take_left' (length_digestBytes s)

theorem take_digestBytes' (s : Digest) : (digestBytes s).take 32 = digestBytes s :=
  List.take_of_length_le (le_of_eq (length_digestBytes s))

/-- **At most `|L|` digests are hit by a set `L` of inputs** (a digest's bytes determine it). -/
theorem sum_hit_le (L : Finset Bytes) (P : Digest → Prop) [DecidablePred P]
    (hP : ∀ u, P u → ∃ m ∈ L, m.take 32 = digestBytes u) :
    (∑ u : Digest, if P u then (1 : ℝ≥0∞) else 0) ≤ L.card := by
  rw [Finset.sum_boole]
  have hsub : (Finset.univ.filter P) ⊆
      L.biUnion fun m ↦ Finset.univ.filter fun u : Digest ↦ m.take 32 = digestBytes u := by
    intro u hu
    obtain ⟨m, hm, hmu⟩ := hP u (Finset.mem_filter.mp hu).2
    exact Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmu⟩⟩
  have hone : ∀ m ∈ L, (Finset.univ.filter fun u : Digest ↦ m.take 32 = digestBytes u).card ≤ 1 := by
    intro m _
    refine Finset.card_le_one.mpr fun u hu v hv ↦ E2ECompleteness.digestBytes_injective ?_
    rw [← (Finset.mem_filter.mp hu).2, ← (Finset.mem_filter.mp hv).2]
  have hcard : (Finset.univ.filter P).card ≤ L.card := by
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    calc ∑ m ∈ L, (Finset.univ.filter fun u : Digest ↦ m.take 32 = digestBytes u).card
        ≤ ∑ _m ∈ L, 1 := Finset.sum_le_sum hone
      _ = L.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
  exact_mod_cast hcard

/-! ## The frame and the swap -/

/-- **A computation that never asks `x`**, run from a cache with `x` answered `v`, is its run without it, `x`'s
answer added. -/
theorem run_frame (x : Bytes) (v : Digest) {α : Type} (T : OracleComp KeccakCalls α)
    (hT : HashOK (fun m ↦ m ≠ x) T) (c : Cache) :
    (simulateQ ro T).run (c.cacheQuery (.inl x) v) =
      (fun p ↦ (p.1, p.2.cacheQuery (.inl x) v)) <$> (simulateQ ro T).run c := by
  induction T using OracleComp.inductionOn generalizing c with
  | pure a => simp
  | query_bind t k ih =>
    obtain ⟨ht, hk⟩ := (isQueryBound_query_bind_iff _ _ _ _ _).1 hT
    have hne : t ≠ .inl x := by
      rcases t with y | s
      · exact fun h ↦ ht (Sum.inl_injective h)
      · exact Sum.inr_ne_inl
    simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self, OracleQuery.cont_query,
      StateT.run_bind, map_bind]
    rw [randomOracle.run_eq, randomOracle.run_eq, QueryCache.cacheQuery_of_ne _ _ hne]
    rcases h : c t with _ | u
    · simp only [bind_assoc, pure_bind]
      refine bind_congr fun u ↦ ?_
      rw [QueryCache.cacheQuery_comm _ (Ne.symm hne)]
      exact ih u (hk u) _
    · simp only [pure_bind]
      exact ih u (hk u) c

/-- **A uniform digest and an independent computation swap.** -/
theorem prEvent_swap_unif {β δ : Type} (Y : ProbComp β) (K : Digest → β → ProbComp δ) (E : δ → Prop) :
    Pr{let z ← ($ᵗ Digest) >>= fun v ↦ Y >>= fun y ↦ K v y}[E z] =
      Pr{let z ← Y >>= fun y ↦ ($ᵗ Digest) >>= fun v ↦ K v y}[E z] := by
  simp only [map_bind]
  exact prEvent_bind_bind_swap_of_uniform _ _ _

/-! ## Chains of challenges -/

/-- **A chain of challenges from state `s`** (at most `n` challenges, at most `N` hashed inputs): either its output
`b`, with `Q b s`; or a challenge `x` on the state (`x` begins with `s`'s 32 bytes), the chain going on from its
answer; or the last challenge, the state alone (`32` bytes), followed by a tail `T` that does not depend on its answer,
hashes no `32`-byte input and at most `NT` inputs, the chain going on from the answer after it. -/
inductive ChainF {γ : Type} (Q : γ → Digest → Prop) : ℕ → ℕ → Digest → OracleComp KeccakCalls γ → Prop
  | ret {n N : ℕ} {s : Digest} (b : γ) : Q b s → ChainF Q n N s (pure b)
  | step {n N n' N' : ℕ} {s : Digest} (x : Bytes) (k : Digest → OracleComp KeccakCalls γ) :
      x.take 32 = digestBytes s → n + 1 ≤ n' → N + 1 ≤ N' → (∀ u, ChainF Q n N u (k u)) →
      ChainF Q n' N' s (callKeccak256 x >>= k)
  | stepT {n N NT n' N' : ℕ} {s : Digest} {δ : Type} (T : OracleComp KeccakCalls δ)
      (F : Digest → δ → OracleComp KeccakCalls γ) :
      HashOK (fun m ↦ m.length ≠ 32) T → HC T NT → n + 1 ≤ n' → N + 1 + NT ≤ N' →
      (∀ u d, ChainF Q n N u (F u d)) →
      ChainF Q n' N' s (callKeccak256 (digestBytes s) >>= fun u ↦ T >>= F u)

theorem ChainF.mono {γ : Type} {Q : γ → Digest → Prop} {n N n' N' : ℕ} {s : Digest}
    {X : OracleComp KeccakCalls γ} (h : ChainF Q n N s X) (hn : n ≤ n') (hN : N ≤ N') : ChainF Q n' N' s X := by
  cases h with
  | ret b hb => exact .ret b hb
  | step x k hx h1 h2 hk => exact .step x k hx (by omega) (by omega) hk
  | stepT T F hT hTc h1 h2 hF => exact .stepT T F hT hTc (by omega) (by omega) hF

theorem ChainF.weakenQ {γ : Type} {Q Q' : γ → Digest → Prop} (hQ : ∀ b s, Q b s → Q' b s) {n N : ℕ}
    {s : Digest} {X : OracleComp KeccakCalls γ} (h : ChainF Q n N s X) : ChainF Q' n N s X := by
  induction h with
  | ret b hb => exact .ret b (hQ _ _ hb)
  | step x k hx h1 h2 _ ih => exact .step x k hx h1 h2 ih
  | stepT T F hT hTc h1 h2 _ ih => exact .stepT T F hT hTc h1 h2 ih

/-- **Chains compose**: a chain, then from its final state a chain. -/
theorem ChainF.bind {β γ : Type} {Q₁ : β → Digest → Prop} {Q₂ : γ → Digest → Prop} {n₂ N₂ : ℕ}
    {F : β → OracleComp KeccakCalls γ} (hF : ∀ b s, Q₁ b s → ChainF Q₂ n₂ N₂ s (F b)) {n₁ N₁ : ℕ}
    {s : Digest} {X : OracleComp KeccakCalls β} (h : ChainF Q₁ n₁ N₁ s X) :
    ChainF Q₂ (n₁ + n₂) (N₁ + N₂) s (X >>= F) := by
  induction h with
  | ret b hb =>
    rw [pure_bind]
    exact (hF b _ hb).mono (Nat.le_add_left _ _) (Nat.le_add_left _ _)
  | step x k hx h1 h2 _ ih =>
    rw [bind_assoc]
    exact .step x _ hx (by omega) (by omega) ih
  | stepT T F' hT hTc h1 h2 _ ih =>
    simp only [bind_assoc]
    exact .stepT T (fun u d ↦ F' u d >>= F) hT hTc (by omega) (by omega) ih

/-! ## The bound on a chain -/

/-- **A chain hits its final state with probability at most `(n + 1) · M / 2^256`**: from a cache of at most `K`
hashed inputs, a fresh query `x` (its answer the chain's first state), then a chain of at most `n` challenges and `N`
hashed inputs from every answer, `K + N + 1 ≤ M`; the event, a hashed input beginning with the final state's bytes
(`Q` gives the final state, `pf`). -/
theorem prHit_le {γ : Type} (Q : γ → Digest → Prop) (pf : γ → Digest) (hQ : ∀ z s, Q z s → pf z = s) (Mb : ℕ)
    (n : ℕ) : ∀ (N K : ℕ) (x : Bytes) (Y : Digest → OracleComp KeccakCalls γ) (c : Cache),
      (∀ u, ChainF Q n N u (Y u)) → CacheBound c K → K + N + 1 ≤ Mb → c (.inl x) = none →
      Pr{let z ← (ro (.inl x)).run c >>= fun p ↦ (simulateQ ro (Y p.1)).run p.2}[Hit z.2 (pf z.1)] ≤
        ((n + 1 : ℕ) : ℝ≥0∞) * ((Mb : ℝ≥0∞) / 2 ^ 256) := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N K x Y c hY hc hM hx
  -- One continuation, from a cache with no hit at its state.
  have one : ∀ (u : Digest) (c₁ : Cache) (Y₀ : OracleComp KeccakCalls γ), ChainF Q n N u Y₀ →
      CacheBound c₁ (K + 1) → ¬ Hit c₁ u →
      Pr{let z ← (simulateQ ro Y₀).run c₁}[Hit z.2 (pf z.1)] ≤ (n : ℝ≥0∞) * ((Mb : ℝ≥0∞) / 2 ^ 256) := by
    intro u c₁ Y₀ h hc₁ hit
    cases h with
    | ret b hb =>
      rw [simulateQ_pure, StateT.run_pure]
      refine (le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ↦ ?_)).trans (by simp)
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      rw [hQ _ _ hb]
      exact hit
    | step x' k hx' h1 h2 hk =>
      have hfresh : c₁ (.inl x') = none := by
        by_contra hne
        exact hit ⟨x', hne, hx'⟩
      rw [simulateQ_bind, simulateQ_callKeccak256, StateT.run_bind]
      refine (ih _ (by omega) _ (K + 1) x' k c₁ hk hc₁ (by omega) hfresh).trans ?_
      exact mul_le_mul' (by exact_mod_cast h1) le_rfl
    | stepT T F hT hTc h1 h2 hF =>
      have hfresh : c₁ (.inl (digestBytes u)) = none := by
        by_contra hne
        exact hit ⟨_, hne, take_digestBytes' u⟩
      have hTx : HashOK (fun m ↦ m ≠ digestBytes u) T :=
        HashOK.mono (P := fun m ↦ m.length ≠ 32) (Q := fun m ↦ m ≠ digestBytes u)
          (fun m hm he ↦ hm (by rw [he]; exact length_digestBytes u)) hT
      have hframe : ∀ v, (simulateQ ro T).run (c₁.cacheQuery (.inl (digestBytes u)) v) =
          (fun p ↦ (p.1, p.2.cacheQuery (.inl (digestBytes u)) v)) <$> (simulateQ ro T).run c₁ :=
        fun v ↦ run_frame _ v T hTx c₁
      rw [simulateQ_bind, simulateQ_callKeccak256, StateT.run_bind, ro_run_fresh _ _ hfresh]
      simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind, hframe, bind_map_left]
      rw [prEvent_swap_unif]
      refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun q hq ↦ ?_
      have hq' : q.2 (.inl (digestBytes u)) = none := by
        by_contra hne
        rcases cache_of_hashOK hT c₁ hq _ hne with h' | h'
        · exact h' hfresh
        · exact h' (length_digestBytes u)
      have e := ih _ (by omega) _ _ (digestBytes u) (fun v ↦ F v q.1) q.2 (fun v ↦ hF v q.1)
        (cacheBound_run hTc hc₁ hq) (by omega) hq'
      rw [ro_run_fresh _ _ hq'] at e
      simp only [bind_assoc, pure_bind] at e
      refine e.trans ?_
      exact mul_le_mul' (by exact_mod_cast h1) le_rfl
  obtain ⟨L, hL, hLc⟩ := hc
  have hc₁ : ∀ u, CacheBound (c.cacheQuery (.inl x) u) (K + 1) :=
    fun u ↦ CacheBound.cacheQuery_inl ⟨L, hL, hLc⟩ x u
  have hterm : ∀ u, Pr{let z ← (simulateQ ro (Y u)).run (c.cacheQuery (.inl x) u)}[Hit z.2 (pf z.1)] ≤
      (if Hit (c.cacheQuery (.inl x) u) u then 1 else 0) + (n : ℝ≥0∞) * ((Mb : ℝ≥0∞) / 2 ^ 256) := by
    intro u
    by_cases hit : Hit (c.cacheQuery (.inl x) u) u
    · simp only [hit, ↓reduceIte]
      exact (prEvent_le_one _).trans le_self_add
    · simp only [hit, ↓reduceIte, zero_add]
      exact one u _ (Y u) (hY u) (hc₁ u) hit
  have hsum : (∑ u : Digest, if Hit (c.cacheQuery (.inl x) u) u then (1 : ℝ≥0∞) else 0) ≤
      ((K + 1 : ℕ) : ℝ≥0∞) := by
    refine (sum_hit_le (insert x L) (fun u ↦ Hit (c.cacheQuery (.inl x) u) u) fun u hu ↦ ?_).trans ?_
    · obtain ⟨m, hm, hmu⟩ := hu
      refine ⟨m, ?_, hmu⟩
      by_cases hmx : m = x
      · rw [hmx]
        exact Finset.mem_insert_self _ _
      · rw [QueryCache.cacheQuery_of_ne _ _ (fun h ↦ hmx (Sum.inl_injective h))] at hm
        exact Finset.mem_insert_of_mem (hLc m hm)
    · exact_mod_cast (Finset.card_insert_le _ _).trans (by omega)
  rw [prEvent_fresh _ _ hx]
  calc (∑ u : Digest, Pr{let z ← (simulateQ ro (Y u)).run (c.cacheQuery (.inl x) u)}[Hit z.2 (pf z.1)]) / 2 ^ 256
      ≤ (∑ u : Digest, ((if Hit (c.cacheQuery (.inl x) u) u then 1 else 0) +
          (n : ℝ≥0∞) * ((Mb : ℝ≥0∞) / 2 ^ 256))) / 2 ^ 256 :=
        ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ hterm u) _
    _ = (∑ u : Digest, if Hit (c.cacheQuery (.inl x) u) u then (1 : ℝ≥0∞) else 0) / 2 ^ 256 +
          (n : ℝ≥0∞) * ((Mb : ℝ≥0∞) / 2 ^ 256) := by
        rw [Finset.sum_add_distrib, ENNReal.add_div, sum_const_div]
    _ ≤ (Mb : ℝ≥0∞) / 2 ^ 256 + (n : ℝ≥0∞) * ((Mb : ℝ≥0∞) / 2 ^ 256) := by
        refine add_le_add (ENNReal.div_le_div_right (hsum.trans ?_) _) le_rfl
        exact_mod_cast (show K + 1 ≤ Mb by omega)
    _ = ((n + 1 : ℕ) : ℝ≥0∞) * ((Mb : ℝ≥0∞) / 2 ^ 256) := by
        push_cast
        ring

/-! ## Chains that end with a `32`-byte challenge -/

/-- **`X` ends with a `32`-byte challenge**: from state `s`, followed by any tail `T` that hashes no `32`-byte input
(at most `NT`) and then any chain `G` from `X`'s final state (`P`), it is a chain. -/
def EndsT {β : Type} (P : β → Digest → Prop) (n N : ℕ) (s : Digest) (X : OracleComp KeccakCalls β) : Prop :=
  ∀ (δ γ : Type) (T : OracleComp KeccakCalls δ) (NT : ℕ) (G : β → δ → OracleComp KeccakCalls γ)
    (Q : γ → Digest → Prop) (n' N' : ℕ), HashOK (fun m ↦ m.length ≠ 32) T → HC T NT →
    (∀ b s' d, P b s' → ChainF Q n' N' s' (G b d)) →
    ChainF Q (n + n') (N + NT + N') s (X >>= fun b ↦ T >>= G b)

theorem EndsT.mono {β : Type} {P P' : β → Digest → Prop} {n N n' N' : ℕ} {s : Digest}
    {X : OracleComp KeccakCalls β} (h : EndsT P n N s X) (hn : n ≤ n') (hN : N ≤ N')
    (hP : ∀ b s, P b s → P' b s) : EndsT P' n' N' s X := by
  intro δ γ T NT G Q n₀ N₀ hT hTc hG
  exact (h δ γ T NT G Q n₀ N₀ hT hTc fun b s d hb ↦ hG b s d (hP b s hb)).mono (by omega) (by omega)

/-- The last challenge: the state alone, then the output. -/
theorem endsT_last {β : Type} {P : β → Digest → Prop} {s : Digest} (f : Digest → β) (hf : ∀ u, P (f u) u) :
    EndsT P 1 1 s (callKeccak256 (digestBytes s) >>= fun u ↦ pure (f u)) := by
  intro δ γ T NT G Q n' N' hT hTc hG
  simp only [bind_assoc, pure_bind]
  exact .stepT T (fun u d ↦ G (f u) d) hT hTc (by omega) (by omega) fun u d ↦ hG _ _ d (hf u)

theorem endsT_bind {β β' : Type} {Q₁ : β → Digest → Prop} {P : β' → Digest → Prop} {n₁ N₁ n₂ N₂ : ℕ}
    {s : Digest} {X : OracleComp KeccakCalls β} {F : β → OracleComp KeccakCalls β'} (hX : ChainF Q₁ n₁ N₁ s X)
    (hF : ∀ b s', Q₁ b s' → EndsT P n₂ N₂ s' (F b)) : EndsT P (n₁ + n₂) (N₁ + N₂) s (X >>= F) := by
  intro δ γ T NT G Q n' N' hT hTc hG
  rw [bind_assoc]
  exact (ChainF.bind (fun b s' hb ↦ hF b s' hb δ γ T NT G Q n' N' hT hTc hG) hX).mono (by omega) (by omega)

theorem endsT_map {β β' : Type} {P : β → Digest → Prop} {P' : β' → Digest → Prop} {n N : ℕ} {s : Digest}
    {X : OracleComp KeccakCalls β} (g : β → β') (hX : EndsT P n N s X) (hg : ∀ b s', P b s' → P' (g b) s') :
    EndsT P' n N s (X >>= fun b ↦ pure (g b)) := by
  intro δ γ T NT G Q n' N' hT hTc hG
  simp only [bind_assoc, pure_bind]
  exact hX δ γ T NT (fun b d ↦ G (g b) d) Q n' N' hT hTc fun b s' d hb ↦ hG _ _ d (hg b s' hb)

/-! ## The writer's chains -/

/-- **A writer's chain**: from every writer satisfying `pre`, a chain from its state, each outcome's state the
chain's final one, satisfying `post`. -/
def WCh {α : Type} (M : PM α) (n N : ℕ) (pre : Wr → Prop) (post : α → Wr → Prop) : Prop :=
  ∀ w, pre w → ChainF (fun p s ↦ p.2.state = s ∧ post p.1 p.2) n N w.state (M.run w)

/-- **A writer's chain that ends with a `32`-byte challenge.** -/
def WEnd {α : Type} (M : PM α) (n N : ℕ) (pre : Wr → Prop) (post : α → Wr → Prop) : Prop :=
  ∀ w, pre w → EndsT (fun p s ↦ p.2.state = s ∧ post p.1 p.2) n N w.state (M.run w)

section Writer

variable {α β : Type}

theorem WCh.mono {M : PM α} {n N n' N' : ℕ} {pre : Wr → Prop} {post post' : α → Wr → Prop}
    (h : WCh M n N pre post) (hn : n ≤ n') (hN : N ≤ N') (hp : ∀ a w, post a w → post' a w) :
    WCh M n' N' pre post' :=
  fun w hw ↦ ((h w hw).weakenQ fun _ _ hq ↦ ⟨hq.1, hp _ _ hq.2⟩).mono hn hN

theorem WCh.weaken {M : PM α} {n N : ℕ} {pre : Wr → Prop} {post : α → Wr → Prop}
    (h : WCh M n N (fun _ ↦ True) post) : WCh M n N pre post :=
  fun w _ ↦ h w trivial

/-- A precondition that does not read the writer is a hypothesis. -/
theorem WCh.const_pre {M : PM α} {n N : ℕ} {P : Prop} {post : α → Wr → Prop}
    (h : P → WCh M n N (fun _ ↦ True) post) : WCh M n N (fun _ ↦ P) post :=
  fun w hw ↦ h hw w trivial

theorem WEnd.const_pre {M : PM α} {n N : ℕ} {P : Prop} {post : α → Wr → Prop}
    (h : P → WEnd M n N (fun _ ↦ True) post) : WEnd M n N (fun _ ↦ P) post :=
  fun w hw ↦ h hw w trivial

theorem WEnd.mono {M : PM α} {n N n' N' : ℕ} {pre : Wr → Prop} {post post' : α → Wr → Prop}
    (h : WEnd M n N pre post) (hn : n ≤ n') (hN : N ≤ N') (hp : ∀ a w, post a w → post' a w) :
    WEnd M n' N' pre post' :=
  fun w hw ↦ (h w hw).mono hn hN fun _ _ hq ↦ ⟨hq.1, hp _ _ hq.2⟩

theorem wch_bind {M : PM α} {f : α → PM β} {n₁ N₁ n₂ N₂ : ℕ} {pre : Wr → Prop} {mid : α → Wr → Prop}
    {post : β → Wr → Prop} (hM : WCh M n₁ N₁ pre mid) (hf : ∀ a, WCh (f a) n₂ N₂ (mid a) post) :
    WCh (M >>= f) (n₁ + n₂) (N₁ + N₂) pre post := by
  intro w hw
  rw [StateT.run_bind]
  refine ChainF.bind (fun p s hp ↦ ?_) (hM w hw)
  rw [← hp.1]
  exact hf p.1 p.2 hp.2

/-- A step from the budget, the rest from what is left. -/
theorem wch_seq {M : PM α} {f : α → PM β} {n₁ N₁ n N : ℕ} {pre : Wr → Prop} {mid : α → Wr → Prop}
    {post : β → Wr → Prop} (hM : WCh M n₁ N₁ pre mid) (hf : ∀ a, WCh (f a) (n - n₁) (N - N₁) (mid a) post)
    (hn : n₁ ≤ n) (hN : N₁ ≤ N) : WCh (M >>= f) n N pre post :=
  (wch_bind hM hf).mono (by omega) (by omega) fun _ _ h ↦ h

theorem wend_bind {M : PM α} {f : α → PM β} {n₁ N₁ n₂ N₂ : ℕ} {pre : Wr → Prop} {mid : α → Wr → Prop}
    {post : β → Wr → Prop} (hM : WCh M n₁ N₁ pre mid) (hf : ∀ a, WEnd (f a) n₂ N₂ (mid a) post) :
    WEnd (M >>= f) (n₁ + n₂) (N₁ + N₂) pre post := by
  intro w hw
  rw [StateT.run_bind]
  refine endsT_bind (hM w hw) fun p s hp ↦ ?_
  rw [← hp.1]
  exact hf p.1 p.2 hp.2

theorem wend_seq {M : PM α} {f : α → PM β} {n₁ N₁ n N : ℕ} {pre : Wr → Prop} {mid : α → Wr → Prop}
    {post : β → Wr → Prop} (hM : WCh M n₁ N₁ pre mid) (hf : ∀ a, WEnd (f a) (n - n₁) (N - N₁) (mid a) post)
    (hn : n₁ ≤ n) (hN : N₁ ≤ N) : WEnd (M >>= f) n N pre post :=
  (wend_bind hM hf).mono (by omega) (by omega) fun _ _ h ↦ h

theorem wend_map {M : PM α} {n N : ℕ} {pre : Wr → Prop} {post : α → Wr → Prop} (g : α → β)
    (hM : WEnd M n N pre post) :
    WEnd (M >>= fun a ↦ pure (g a)) n N pre (fun b w ↦ ∃ a, b = g a ∧ post a w) := by
  intro w hw
  rw [StateT.run_bind]
  simp only [StateT.run_pure]
  refine endsT_map (fun p ↦ (g p.1, p.2)) (hM w hw) ?_
  intro p s hp
  exact ⟨hp.1, p.1, rfl, hp.2⟩

theorem wch_ret (a : α) {n N : ℕ} {pre : Wr → Prop} {post : α → Wr → Prop} (h : ∀ w, pre w → post a w) :
    WCh (pure a : PM α) n N pre post := by
  intro w hw
  rw [StateT.run_pure]
  exact .ret _ ⟨rfl, h w hw⟩

theorem wch_sendBytes (b : List UInt8) {pre : Wr → Prop} :
    WCh (sendBytes (m := OracleComp KeccakCalls) b) 0 0 pre (fun _ _ ↦ True) := by
  intro w _
  have e : (sendBytes (m := OracleComp KeccakCalls) b).run w =
      pure (PUnit.unit, { w with stream := w.stream ++ b.toArray }) := by
    simp [sendBytes]
  rw [e]
  exact .ret _ ⟨rfl, trivial⟩

theorem wch_sendScalar (x : E) {pre : Wr → Prop} :
    WCh (sendScalar (m := OracleComp KeccakCalls) x) 0 0 pre (fun _ _ ↦ True) :=
  wch_sendBytes _

theorem wch_sendScalars (xs : List E) {pre : Wr → Prop} :
    WCh (sendScalars (m := OracleComp KeccakCalls) xs) 0 0 pre (fun _ _ ↦ True) :=
  wch_sendBytes _

/-- **A challenge**: one step on the writer's state; afterwards nothing is pending. -/
theorem wch_sampleW {pre : Wr → Prop} :
    WCh (sampleW callKeccak256) 1 1 pre (fun _ w ↦ w.absorbed = w.stream.size) := by
  intro w _
  rw [run_sampleW]
  exact .step (n := 0) (N := 0) _ _ (take_digestBytes _ _) le_rfl le_rfl fun u ↦ .ret _ ⟨rfl, rfl⟩

/-- **A challenge with nothing pending** hashes the state alone (`32` bytes): it can end a chain. -/
theorem wend_sampleW :
    WEnd (sampleW callKeccak256) 1 1 (fun w ↦ w.absorbed = w.stream.size) (fun _ _ ↦ True) := by
  intro w hw
  rw [run_sampleW]
  have e : (w.stream.extract w.absorbed w.stream.size).toList = [] := by
    rw [hw]
    simp
  rw [e, List.append_nil]
  exact endsT_last _ fun u ↦ ⟨rfl, trivial⟩

theorem samplesW_zero : samplesW callKeccak256 0 = (pure [] : PM (List E)) := rfl

theorem samplesW_succ (k : ℕ) : samplesW callKeccak256 (k + 1) =
    (sampleW callKeccak256 >>= fun x ↦ samplesW callKeccak256 k >>= fun rest ↦ pure (x :: rest) : PM (List E)) :=
  rfl

theorem wch_samplesW : ∀ k : ℕ,
    WCh (samplesW callKeccak256 k) k k (fun _ ↦ True) (fun xs _ ↦ xs.length = k)
  | 0 => by
    rw [samplesW_zero]
    exact wch_ret _ fun _ _ ↦ rfl
  | k + 1 => by
    rw [samplesW_succ]
    refine wch_seq wch_sampleW (fun x ↦ ?_) (by omega) (by omega)
    refine wch_seq (wch_samplesW k).weaken (fun rest ↦ ?_) (by omega) (by omega)
    exact wch_ret _ fun _ h ↦ by rw [List.length_cons, h]

theorem wend_samplesW1 : ∀ k : ℕ,
    WEnd (samplesW callKeccak256 (k + 1)) (k + 1) (k + 1) (fun w ↦ w.absorbed = w.stream.size) (fun _ _ ↦ True)
  | 0 => by
    rw [samplesW_succ, samplesW_zero]
    simp only [pure_bind]
    exact (wend_map _ wend_sampleW).mono le_rfl le_rfl fun _ _ _ ↦ trivial
  | k + 1 => by
    rw [samplesW_succ]
    refine wend_seq wch_sampleW (fun x ↦ ?_) (by omega) (by omega)
    exact (wend_map _ (wend_samplesW1 k)).mono (by omega) (by omega) fun _ _ _ ↦ trivial

/-- **At least two challenges** end with one with nothing pending. -/
theorem wend_samplesW2 (k : ℕ) :
    WEnd (samplesW callKeccak256 (k + 1 + 1)) (k + 2) (k + 2) (fun _ ↦ True) (fun _ _ ↦ True) := by
  rw [samplesW_succ]
  refine wend_seq wch_sampleW (fun x ↦ ?_) (by omega) (by omega)
  exact (wend_map _ (wend_samplesW1 k)).mono (by omega) (by omega) fun _ _ _ ↦ trivial

end Writer

/-! ## Flock's honest prover is a chain that ends with a `32`-byte challenge -/

/-- The zerocheck's challenges: the `log_n − k − 7` sampled coordinates, the skip's `z`, one per round. -/
def zcSteps (logN k : ℕ) : ℕ := (logN - k - Flock.nFixed) + 1 + (Flock.nFixed + (logN - k - Flock.nFixed))

/-- The front's: the zerocheck's, `α`, the lincheck's. -/
def frontSteps (logN k : ℕ) : ℕ := zcSteps logN k + 1 + Flock.lincheckRounds

/-- Flock's: the front's, the ring map's six. -/
def flockSteps (logN k : ℕ) : ℕ := frontSteps logN k + 6

theorem wch_zcRounds (r : List E) : ∀ (claim : E) (a b c : Array E),
    WCh (FlockP.zcRounds callKeccak256 r claim a b c) r.length r.length (fun _ ↦ True) (fun _ _ ↦ True) := by
  induction r with
  | nil =>
    intro claim a b c
    simp only [FlockP.zcRounds]
    exact wch_ret _ fun _ _ ↦ trivial
  | cons x rest ih =>
    intro claim a b c
    simp only [FlockP.zcRounds, List.length_cons]
    refine wch_seq (wch_sendScalar _) (fun _ ↦ ?_) (Nat.zero_le _) (Nat.zero_le _)
    refine wch_seq (wch_sendScalar _) (fun _ ↦ ?_) (Nat.zero_le _) (Nat.zero_le _)
    refine wch_seq wch_sampleW (fun y ↦ ?_) (by omega) (by omega)
    refine wch_seq (ih _ _ _ _).weaken (fun _ ↦ ?_) (by omega) (by omega)
    exact wch_ret _ fun _ _ ↦ trivial

theorem wch_lcRounds (n : ℕ) : ∀ (claim : E) (w z : Array E),
    WCh (FlockP.lcRounds callKeccak256 n claim w z) n n (fun _ ↦ True) (fun _ _ ↦ True) := by
  induction n with
  | zero =>
    intro claim w z
    simp only [FlockP.lcRounds]
    exact wch_ret _ fun _ _ ↦ trivial
  | succ n ih =>
    intro claim w z
    simp only [FlockP.lcRounds]
    refine wch_seq (wch_sendScalar _) (fun _ ↦ ?_) (Nat.zero_le _) (Nat.zero_le _)
    refine wch_seq (wch_sendScalar _) (fun _ ↦ ?_) (Nat.zero_le _) (Nat.zero_le _)
    refine wch_seq wch_sampleW (fun y ↦ ?_) (by omega) (by omega)
    refine wch_seq (ih _ _ _).weaken (fun _ ↦ ?_) (by omega) (by omega)
    exact wch_ret _ fun _ _ ↦ trivial

theorem wch_skipW (k : ℕ) (r : List E) (wit : FlockP.Wit) :
    WCh (FlockP.skipW callKeccak256 k r wit) 1 1 (fun _ ↦ True) (fun _ _ ↦ True) := by
  unfold FlockP.skipW
  split_ifs
  · refine wch_seq (wch_sendScalars _) (fun _ ↦ ?_) (Nat.zero_le _) (Nat.zero_le _)
    refine wch_seq wch_sampleW (fun _ ↦ ?_) (by omega) (by omega)
    exact wch_ret _ fun _ _ ↦ trivial
  · exact wch_ret _ fun _ _ ↦ trivial

theorem wch_zerocheckW (logN k : ℕ) (wit : FlockP.Wit) :
    WCh (FlockP.zerocheckW callKeccak256 logN k wit) (zcSteps logN k) (zcSteps logN k) (fun _ ↦ True)
      (fun _ _ ↦ True) := by
  unfold FlockP.zerocheckW
  refine wch_seq (wch_samplesW _) (fun sampled ↦ WCh.const_pre fun hw ↦ ?_) (by unfold zcSteps; omega)
    (by unfold zcSteps; omega)
  have hlen : (Flock.fixedChallenges ++ sampled).length = Flock.nFixed + (logN - k - Flock.nFixed) := by
    rw [List.length_append, hw]
    rfl
  refine wch_seq (wch_skipW _ _ _) (fun st ↦ ?_) (by unfold zcSteps; omega) (by unfold zcSteps; omega)
  refine wch_seq (wch_zcRounds _ _ _ _ _) (fun zc ↦ ?_) (by rw [hlen]; unfold zcSteps; omega)
    (by rw [hlen]; unfold zcSteps; omega)
  refine wch_seq (wch_sendScalar _) (fun _ ↦ ?_) (Nat.zero_le _) (Nat.zero_le _)
  refine wch_seq (wch_sendScalar _) (fun _ ↦ ?_) (Nat.zero_le _) (Nat.zero_le _)
  exact wch_ret _ fun _ _ ↦ trivial

theorem wch_sendSlices (variant : Flock.Variant) (s : List E) (hv : variant.slices ≠ .claim) :
    WCh (FlockP.sendSlices (m := OracleComp KeccakCalls) variant s) 0 0 (fun _ ↦ True)
      (fun r _ ↦ r = some s) := by
  unfold FlockP.sendSlices
  simp only [hv, ↓reduceIte]
  refine wch_seq (wch_sendScalars _) (fun _ ↦ ?_) (Nat.zero_le _) (Nat.zero_le _)
  exact wch_ret _ fun _ _ ↦ rfl

theorem wch_frontW (logN : ℕ) (variant : Flock.Variant) (q : Array K) (hv : variant.slices ≠ .claim) :
    WCh (FlockP.frontW callKeccak256 logN variant q) (frontSteps logN variant.skip)
      (frontSteps logN variant.skip) (fun _ ↦ True) (fun frs _ ↦ ∃ s, frs.1.slices = some s) := by
  unfold FlockP.frontW
  refine wch_seq (wch_zerocheckW _ _ _) (fun zc ↦ ?_) (by unfold frontSteps; omega)
    (by unfold frontSteps; omega)
  refine wch_seq wch_sampleW (fun alpha ↦ ?_) (by unfold frontSteps; omega) (by unfold frontSteps; omega)
  refine wch_seq (wch_lcRounds _ _ _ _).weaken (fun lc ↦ ?_) (by unfold frontSteps; omega)
    (by unfold frontSteps; omega)
  refine wch_seq (wch_sendSlices _ _ hv).weaken (fun slices ↦ ?_) (Nat.zero_le _) (Nat.zero_le _)
  exact wch_ret _ fun _ hw ↦ ⟨_, hw⟩

/-- **Flock's honest prover is a chain of `flockSteps` challenges ending with a `32`-byte one** (the ring map's last),
at every variant whose slices are sent. -/
theorem wend_flockProve (logN : ℕ) (variant : Flock.Variant) (q : Array K) (hv : variant.slices ≠ .claim) :
    WEnd (FlockP.flockProve callKeccak256 logN variant q) (flockSteps logN variant.skip)
      (flockSteps logN variant.skip) (fun _ ↦ True) (fun _ _ ↦ True) := by
  simp only [FlockP.flockProve]
  refine wend_seq (wch_frontW logN variant q hv) (fun frs ↦ WEnd.const_pre fun h ↦ ?_)
    (by unfold flockSteps; omega) (by unfold flockSteps; omega)
  obtain ⟨s, hs⟩ := h
  rw [hs]
  simp only [FlockP.endW, FlockP.ringEndW, bind_assoc, pure_bind]
  rw [show Flock.ringMapShifts.length = 4 + 1 + 1 from rfl]
  exact (wend_map _ (wend_samplesW2 4)).mono (by unfold flockSteps; omega) (by unfold flockSteps; omega)
    fun _ _ _ ↦ trivial

/-! ## The staged run -/

/-- Flock's honest prover as the probability layer's parameter (the same function as `flockProveH` of branch
`lean-uni-fcostc`'s `FlockCost.lean`; a local name, so that the two merge without a clash). -/
abbrev flockP : FlockProverH := fun H ↦ FlockP.flockProve H

/-- Flock's challenges at the deployment (`flockMain`). -/
def flockStepsD (D : Deployment) : ℕ := flockSteps (Cost.flockLogN D.shape) flockMain.skip

/-- **The challenges after the first bus challenge**: `α₂ … α₄`, `β`, `γ`, Flock's. -/
def tSteps (D : Deployment) : ℕ := flockStepsD D + 5

/-- `C2`'s tree's hashed inputs, at most. -/
def c2Cost (D : Deployment) : ℕ := E2ECompleteness.Cost.treeCost (((layoutsOf D.shape).lookup .c2).getD default).vars

/-- **Stage A's hashed inputs**, at most: the setup's trees (twice: the experiment's and the prover's), the IV, the
seed, `C1`'s tree. -/
def stageACost (D : Deployment) : ℕ :=
  2 * Cost.setupCost D + 2 + E2ECompleteness.Cost.treeCost (c1Layout D.shape).vars

/-- **The hashed inputs before `t`**, at most (and one). -/
def tCache (D : Deployment) : ℕ := stageACost D + (tSteps D + c2Cost D) + 1

/-- **`t`'s cache-hit bound**: `(tSteps + 1) · tCache / 2^256`. -/
noncomputable def tFreshBound (D : Deployment) : ℝ≥0∞ :=
  ((tSteps D + 1 : ℕ) : ℝ≥0∞) * ((tCache D : ℝ≥0∞) / 2 ^ 256)

theorem honestTrace_shape (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    (honestTrace D input rows q).shape = D.shape := rfl

/-- **Stage A hashes at most `stageACost` inputs.** -/
theorem hc_stageA (flock : FlockProverH) (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.Stack rows) : HC (stagedU flock D input rows q).A (stageACost D) := by
  have hcm : ∀ (μ : ℕ) (stack : Array K),
      HC (E2ECompleteness.commitWithH callKeccak256 μ stack) (5 * 2 ^ (μ - 6 + 1)) :=
    fun μ stack ↦ hc_of_qc (E2ECompleteness.Cost.qc_commitWithH μ stack)
  simp only [stagedU, proverA, setupTreesOf, setupTreesWithH, contractIvOf, seedOf, bind_assoc, pure_bind]
  refine Common.QueryCostAtMost.mono (Common.QueryCostAtMost.bind (hcm _ _) fun _ ↦
    Common.QueryCostAtMost.bind (hcm _ _) fun _ ↦ Common.QueryCostAtMost.bind (hcm _ _) fun _ ↦
    Common.QueryCostAtMost.bind (hcm _ _) fun _ ↦ Common.QueryCostAtMost.bind (hcm _ _) fun _ ↦
    Common.QueryCostAtMost.bind (hcm _ _) fun _ ↦ Common.QueryCostAtMost.bind (hc_H _) fun _ ↦
    Common.QueryCostAtMost.bind (hc_H _) fun _ ↦ Common.QueryCostAtMost.bind (b := 0) (hcm _ _) fun _ ↦
    trivial) ?_
  simp only [stageACost, Cost.setupCost, E2ECompleteness.Cost.treeCost, honestTrace_shape]
  omega

theorem hashOK_commitReal (c : Commitment) (vars : ℕ) (stack : Array K) :
    HashOK (fun m ↦ m.length ≠ 32) (commitReal callKeccak256 c vars stack) := by
  unfold commitReal
  exact E2ECompleteness.HashOK.bind (HashOK.mono (fun _ h ↦ h.1) (hashOK_commitWithH vars stack)) fun _ ↦
    E2ECompleteness.HashOK.pure _ _

/-- `midB` over the two calls, run: `γ`, Flock's prover, `C2`'s commitment, its root written. -/
theorem run_midB (flock : FlockProver (OracleComp KeccakCalls)) (tr : Trace) (alphas : List E) (beta : E)
    (w : Wr) :
    (midB callKeccak256 (commitReal callKeccak256) flock tr alphas beta).run w =
      (sampleW callKeccak256).run w >>= fun p ↦
        (flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) flockMain tr.qflock).run p.2 >>= fun q ↦
          commitReal callKeccak256 .c2 (((layoutsOf tr.shape).lookup .c2).getD default).vars
              (c2DataOf tr (eqKernel alphas) beta p.1).stack >>= fun c ↦
            pure ((p.1, q.1, c), { q.2 with stream := q.2.stream ++ (rootWord c.halves).toArray }) := by
  simp only [midB, StateT.run_bind, StateT.run_lift, run_sendRoot, bind_assoc, pure_bind, StateT.run_pure]

/-- **The staged run after the first bus challenge**: `s₂ … s₅`, then `B` (`γ`, Flock, `C2`). -/
def preTail (S : UniStaged) (a : S.α) (s₁ : Digest) : OracleComp KeccakCalls (S.β × (List E × E)) := do
  let s₂ ← callKeccak256 (digestBytes s₁)
  let s₃ ← callKeccak256 (digestBytes s₂)
  let s₄ ← callKeccak256 (digestBytes s₃)
  let s₅ ← callKeccak256 (digestBytes s₄)
  let b ← S.B a s₁ s₂ s₃ s₄ s₅
  return (b, ([PcsQuotient.Transcript.challengeOf s₁, PcsQuotient.Transcript.challengeOf s₂,
    PcsQuotient.Transcript.challengeOf s₃, PcsQuotient.Transcript.challengeOf s₄],
    PcsQuotient.Transcript.challengeOf s₅))

theorem pre_eq (S : UniStaged) : S.pre = S.A >>= fun a ↦ callKeccak256 (S.inp a) >>= preTail S a := rfl

/-- **The staged run after the first bus challenge is a chain** of `tSteps` challenges and `tSteps + c2Cost` hashed
inputs, its final state the writer's before `t`. -/
theorem chainF_preTail (D : Deployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows)
    (a : SetupTrees × ProverA) (s₁ : Digest) :
    ChainF (fun (z : MidU × (List E × E)) s ↦ z.1.mw.2.state = s) (tSteps D) (tSteps D + c2Cost D) s₁
      (preTail (stagedU flockP D input rows q) a s₁) := by
  unfold preTail
  refine .step (n := flockStepsD D + 4) (N := flockStepsD D + c2Cost D + 4) _ _ (take_digestBytes' s₁)
    (by unfold tSteps; omega) (by unfold tSteps; omega) fun s₂ ↦ ?_
  refine .step (n := flockStepsD D + 3) (N := flockStepsD D + c2Cost D + 3) _ _ (take_digestBytes' s₂)
    (by omega) (by omega) fun s₃ ↦ ?_
  refine .step (n := flockStepsD D + 2) (N := flockStepsD D + c2Cost D + 2) _ _ (take_digestBytes' s₃)
    (by omega) (by omega) fun s₄ ↦ ?_
  refine .step (n := flockStepsD D + 1) (N := flockStepsD D + c2Cost D + 1) _ _ (take_digestBytes' s₄)
    (by omega) (by omega) fun s₅ ↦ ?_
  simp only [stagedU, midU, bind_assoc, pure_bind]
  rw [run_midB]
  simp only [bind_assoc, pure_bind]
  have h1 := wch_sampleW (pre := fun _ ↦ True) (writerAfter rows a.2.c1 s₁ s₂ s₃ s₄ s₅) trivial
  refine ChainF.mono (n := 1 + flockStepsD D) (N := 1 + (flockStepsD D + c2Cost D))
    (n' := flockStepsD D + 1) (N' := flockStepsD D + c2Cost D + 1)
    (ChainF.bind (n₂ := flockStepsD D) (N₂ := flockStepsD D + c2Cost D) (fun p s hp ↦ ?_) h1) (by omega) (by omega)
  obtain ⟨hs, -⟩ := hp
  subst hs
  have h := wend_flockProve (Cost.flockLogN D.shape) flockMain (honestTrace D input rows q).qflock (by decide)
    p.2 trivial
  refine ChainF.mono (n := flockSteps (Cost.flockLogN D.shape) flockMain.skip + 0)
    (N := flockSteps (Cost.flockLogN D.shape) flockMain.skip + c2Cost D + 0)
    (n' := flockStepsD D) (N' := flockStepsD D + c2Cost D)
    (h _ _ _ (c2Cost D) _ _ 0 0 (hashOK_commitReal _ _ _) (hc_of_qc (Cost.qc_commitReal _ _ _)) ?_)
    (by unfold flockStepsD; omega) (by unfold flockStepsD; omega)
  intro b s' d hb
  exact .ret _ hb.1

end TFresh

open TFresh

/-- **`t`'s query is fresh for Flock's honest prover**, at every deployment: its input is cached when asked with
probability at most `tFreshBound D = (tSteps D + 1) · tCache D / 2^256`. -/
theorem tQueryFresh_flockProve (D : Deployment) :
    TQueryFresh (fun H ↦ FlockP.flockProve H) D (tFreshBound D) := by
  intro input rows q hfit _
  have hmono := prEvent_mono ((simulateQ ro (stagedU flockP D input rows q).pre).run ∅)
    (fun p ↦ p.2 (.inl ((stagedU flockP D input rows q).tin p.1.1)) ≠ none)
    (fun (p : (MidU × (List E × E)) × Cache) ↦ Hit p.2 p.1.1.mw.2.state)
    (fun p hp ↦ ⟨_, hp, take_digestBytes _ _⟩)
  refine hmono.trans ?_
  rw [pre_eq, simulateQ_bind, StateT.run_bind]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p hp ↦ ?_
  rw [simulateQ_bind, simulateQ_callKeccak256, StateT.run_bind]
  have hc : CacheBound p.2 (stageACost D) :=
    (cacheBound_run (hc_stageA flockP D input rows q) cacheBound_empty hp).mono (by omega)
  have hx : p.2 (.inl ((stagedU flockP D input rows q).inp p.1)) = none := by
    by_contra h
    rcases cache_of_hashOK (hashA_stagedU flockP D input rows q) ∅ hp _ h with h' | h'
    · exact h' rfl
    · exact h'.2 (firstInput_length hfit.1 p.1.2)
  exact prHit_le _ (fun (z : MidU × (List E × E)) ↦ z.1.mw.2.state) (fun _ _ h ↦ h) (tCache D) (tSteps D)
    (tSteps D + c2Cost D) (stageACost D) _ _ _ (fun s₁ ↦ chainF_preTail D input rows q p.1 s₁) hc
    (by unfold tCache; omega) hx

/-! ## At the reference shape -/

theorem tSteps_reference (D : Deployment) (hD : D.shape = reference) : tSteps D = 72 := by
  unfold tSteps flockStepsD flockSteps frontSteps zcSteps
  rw [hD, Cost.reference_flockLogN]
  rfl

theorem tCache_reference (D : Deployment) (hD : D.shape = reference) : tCache D ≤ 2 ^ 28 := by
  obtain ⟨h1, h2, h3, -⟩ := Cost.reference_vars
  have hs := tSteps_reference D hD
  have hc1 : E2ECompleteness.Cost.treeCost (c1Layout D.shape).vars ≤ 20971520 := by
    rw [hD]
    exact (Cost.treeCost_mono h1).trans (by decide)
  have hc2 : c2Cost D ≤ 41943040 := by
    unfold c2Cost
    rw [hD]
    exact (Cost.treeCost_mono h2).trans (by decide)
  have hset : Cost.setupCost D ≤ 86507520 := by
    have h19 : 2 ^ ((setupLayout D.shape).vars - 6 + 1) ≤ 2 ^ 19 := by
      rw [hD]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hm : 2 ^ (matrixVars - 6 + 1) = 2 ^ 23 := rfl
    unfold Cost.setupCost
    omega
  unfold tCache stageACost
  omega

/-- **The reference bound**: `tFreshBound D ≤ 2^-200` (`(72 + 1) · 2^28 / 2^256 < 2^-221`). -/
theorem tFreshBound_reference (D : Deployment) (hD : D.shape = reference) :
    tFreshBound D ≤ (2 : ℝ≥0∞)⁻¹ ^ 200 := by
  have hN : (tSteps D + 1) * tCache D ≤ 2 ^ 56 := by
    rw [tSteps_reference D hD]
    have := tCache_reference D hD
    omega
  unfold tFreshBound
  rw [← mul_div_assoc, ← Nat.cast_mul]
  calc (((tSteps D + 1) * tCache D : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ ((2 ^ 56 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
        ENNReal.div_le_div_right (by exact_mod_cast hN) _
    _ = (2 : ℝ≥0∞)⁻¹ ^ 200 := by
        rw [Nat.cast_pow, Nat.cast_ofNat, ENNReal.div_eq_inv_mul, ENNReal.inv_pow, mul_comm,
          show (256 : ℕ) = 200 + 56 from rfl]
        exact E2ECompleteness.two_pow_mul_inv_pow 56 200

/-- **`t`'s query is fresh at the reference shape**, with probability of a cache hit at most `2^-200`: the hypothesis
`TQueryFresh` of `uniCompleteness_reference`, for Flock's honest prover (`flockProveH`). -/
theorem tQueryFresh_reference (D : Deployment) (hD : D.shape = reference) :
    TQueryFresh (fun H ↦ FlockP.flockProve H) D ((2 : ℝ≥0∞)⁻¹ ^ 200) :=
  fun input rows q hfit hrel ↦
    (tQueryFresh_flockProve D input rows q hfit hrel).trans (tFreshBound_reference D hD)

end UniComplete.Prob

/-! ## Axioms -/

/-- info: 'UniComplete.Prob.TFresh.prHit_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Prob.TFresh.prHit_le

/-- info: 'UniComplete.Prob.TFresh.wend_flockProve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Prob.TFresh.wend_flockProve

/-- info: 'UniComplete.Prob.tQueryFresh_flockProve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Prob.tQueryFresh_flockProve

/-- info: 'UniComplete.Prob.tQueryFresh_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Prob.tQueryFresh_reference
