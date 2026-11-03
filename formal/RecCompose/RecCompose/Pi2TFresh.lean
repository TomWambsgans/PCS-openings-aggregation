-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π2's analogue of `formal/UniComplete/UniComplete/
-- ProbTFresh.lean` (`t`'s query fresh), with its counting (`HC`, `CacheBound`, `cacheBound_run`, `sum_hit_le`,
-- `run_frame`), for π2's staged run (`RecCompose.Pi2ProbStaged`: `Q`'s tree between `γ` and `t`, `mid2`); uses
-- leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two
-- calls, their lazy random oracles, Merkle trees over a hash (`buildTreeWithHash`).
import RecCompose.Pi2Chain

/-!
# `t`'s query is fresh for π2 (`Pi2TFresh`), given `α`'s

π2's `t` is drawn right after `Q`'s root: its input is `s₃`'s `32` bytes (the state after `γ`) and `Q`'s root word,
`64` bytes, a Merkle node's length. π1's argument (`ProbTFresh`: `C2`'s tree does not depend on the last answer, so
the uniform answer and the tree's run swap) does not apply: **`Q`'s leaves depend on `s₃`** (`qEntry` of
`hNovel G w α β γ`). The argument here:

* `s₁` is fresh but with probability `εα` (`α`'s input, **`Pi2AlphaFresh`**, named; `Pi2Chain`); `s₂`'s and `s₃`'s
  inputs (`32` bytes) are fresh unless an earlier answer repeats or a cached input is the answer's bytes;
* `Q`'s tree hashes `512`-byte leaves (whatever they hold) and `64`-byte nodes, **each node beginning with a digest
  the tree received** (an answer to one of its own queries, or `default` for a missing child; **`APq`**,
  `apq_commitWithH`); it never asks a `32`-byte input, so its run from the cache with `s₃` answered is its run without
  it, the answer added (`run_frame`);
* so with `u = s₃` uniform: a cached `64`-byte input beginning with `u` is one cached before `s₃` (at most `K + 2`
  of the `2^256` answers), or a node whose first digest is `u`: `default` (one answer), an answer cached before
  (`K + 2`), or a fresh answer of the tree equal to `u` (`1 / 2^256` each, **`prHit64_le`**).

**`tFresh_of`** (any `Pi2Staged` whose `B` is such a tree then a writer whose `t` input begins with `s₃`): `t`'s input is
cached with probability at most `εα + (4 K + 6 + NT) / 2^256` (`K` stage A's hashed inputs, `NT` the tree's).
**`pi2TFresh_of`**: `Pi2TFresh D C Fa P1k (εα + (4 N + 6 + treeCost μQ) / 2^256)` from `Pi2RunCost D C Fa P1k N` and
`Pi2AlphaFresh D C Fa P1k εα`, for every `P1k`; **`tFreshBound2_le`**: below `2^-200` at `N ≤ 2^50`, `εα ≤ 2^-201`.

**`recCompleteness2_pi2_staged2`**: `recCompleteness2_pi2_staged` with `Pi2HashBeforeAlpha` (false at `p1k`) replaced
by `Pi2AlphaFresh εα` and `Pi2TFresh` proved, error `delta2' N εα εt' εpow`.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open E2ECompleteness (ro Cache HashOK cache_of_hashOK prEvent_fresh ro_run_fresh ro_run_cached length_digestBytes
  simulateQ_callKeccak256)
open UniComplete.Prob (prEvent_query_le sum_const_div sum_mem_le)
open UniComplete.Prob.TFresh (HC hq hc_of_qc CacheBound cacheBound_empty cacheBound_run sum_hit_le take_digestBytes
  take_digestBytes' run_frame)
open scoped ENNReal

set_option autoImplicit false

namespace RecCompose.Pi2P

namespace TF

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## Answers and `64`-byte hits -/

/-- `u` answers a cached hash query. -/
def Ans (c : Cache) (u : Digest) : Prop := ∃ m, c (.inl m) = some u

/-- **A `64`-byte hit at `u`**: a cached `64`-byte input begins with `u`'s bytes. -/
def Hit64 (c : Cache) (u : Digest) : Prop := ∃ m, c (.inl m) ≠ none ∧ m.length = 64 ∧ m.take 32 = digestBytes u

open Classical in
theorem sum_ans_le {c : Cache} {K : ℕ} (hc : CacheBound c K) :
    (∑ u : Digest, (if Ans c u then 1 else 0 : ℝ≥0∞)) ≤ K := by
  classical
  obtain ⟨L, hL, hm⟩ := hc
  rw [Finset.sum_boole]
  have hsub : (Finset.univ.filter fun u ↦ Ans c u) ⊆ L.image fun m ↦ (c (.inl m)).getD default := by
    intro u hu
    obtain ⟨m, hmu⟩ := (Finset.mem_filter.mp hu).2
    exact Finset.mem_image.mpr ⟨m, hm m (by rw [hmu]; exact Option.some_ne_none _), by rw [hmu]; rfl⟩
  exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_image_le.trans hL)

open Classical in
theorem sum_hit64_le {c : Cache} {K : ℕ} (hc : CacheBound c K) :
    (∑ u : Digest, (if Hit64 c u then 1 else 0 : ℝ≥0∞)) ≤ K := by
  classical
  obtain ⟨L, hL, hm⟩ := hc
  exact (sum_hit_le L (Hit64 c) fun u ⟨m, hmc, _, ht⟩ ↦ ⟨m, hm m hmc, ht⟩).trans
    (by exact_mod_cast hL : ((L.card : ℕ) : ℝ≥0∞) ≤ K)

/-! ## Computations whose `64`-byte queries begin with a received digest -/

/-- **`APq Q R X`**: every `64`-byte query of `X` begins with a digest in `R`, `R` growing by each answer; `Q` of the
output and the final list. -/
inductive APq {α : Type} (Q : α → List Digest → Prop) : List Digest → OracleComp KeccakCalls α → Prop
  | ret {R : List Digest} (a : α) : Q a R → APq Q R (pure a)
  | query {R : List Digest} (x : Bytes) (k : Digest → OracleComp KeccakCalls α) :
      (x.length = 64 → ∃ a ∈ R, x.take 32 = digestBytes a) → (∀ u, APq Q (u :: R) (k u)) →
      APq Q R (callKeccak256 x >>= k)

theorem APq.weakenQ {α : Type} {Q Q' : α → List Digest → Prop} (hQ : ∀ a R, Q a R → Q' a R) {R : List Digest}
    {X : OracleComp KeccakCalls α} (h : APq Q R X) : APq Q' R X := by
  induction h with
  | ret a ha => exact .ret a (hQ _ _ ha)
  | query x k hx _ ih => exact .query x k hx ih

theorem APq.bind {β γ : Type} {Q₁ : β → List Digest → Prop} {Q₂ : γ → List Digest → Prop}
    {F : β → OracleComp KeccakCalls γ} (hF : ∀ b R, Q₁ b R → APq Q₂ R (F b)) {R : List Digest}
    {X : OracleComp KeccakCalls β} (h : APq Q₁ R X) : APq Q₂ R (X >>= F) := by
  induction h with
  | ret b hb =>
    rw [pure_bind]
    exact hF b _ hb
  | query x k hx _ ih =>
    rw [bind_assoc]
    exact .query x _ hx ih

/-- The list only grows. -/
theorem APq.sub {α : Type} {Q : α → List Digest → Prop} {R : List Digest} {X : OracleComp KeccakCalls α}
    (h : APq Q R X) : APq (fun a R' ↦ Q a R' ∧ ∀ d ∈ R, d ∈ R') R X := by
  induction h with
  | ret a ha => exact .ret a ⟨ha, fun _ hd ↦ hd⟩
  | query x k hx _ ih =>
    refine .query x k hx fun u ↦ (ih u).weakenQ fun a R' h ↦ ⟨h.1, fun d hd ↦ h.2 d (List.mem_cons_of_mem _ hd)⟩

theorem apq_H (x : Bytes) {R : List Digest} (hx : x.length = 64 → ∃ a ∈ R, x.take 32 = digestBytes a) :
    APq (fun v R' ↦ v ∈ R' ∧ ∀ d ∈ R, d ∈ R') R (callKeccak256 x) := by
  rw [← bind_pure (callKeccak256 x)]
  exact .query x _ hx fun u ↦ .ret u ⟨List.mem_cons_self, fun d hd ↦ List.mem_cons_of_mem _ hd⟩

theorem apq_mapM {α : Type} (f : α → OracleComp KeccakCalls Digest) (G : List Digest → Prop)
    (hG : ∀ R R', G R → (∀ d ∈ R, d ∈ R') → G R')
    (hf : ∀ a R, G R → APq (fun v R' ↦ v ∈ R' ∧ ∀ d ∈ R, d ∈ R') R (f a)) :
    ∀ (l : List α) (R : List Digest), G R →
      APq (fun vs R' ↦ (∀ v ∈ vs, v ∈ R') ∧ ∀ d ∈ R, d ∈ R') R (l.mapM f)
  | [], R, _ => by
    rw [List.mapM_nil]
    exact .ret [] ⟨by simp, fun _ hd ↦ hd⟩
  | a :: l, R, hR => by
    rw [List.mapM_cons]
    refine (hf a R hR).bind fun v R₁ h₁ ↦ ?_
    refine (apq_mapM f G hG hf l R₁ (hG R R₁ hR h₁.2)).bind fun vs R₂ h₂ ↦ .ret _ ⟨?_, fun d hd ↦ h₂.2 d (h₁.2 d hd)⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact h₂.2 _ h₁.1
    · exact h₂.1 w hw

theorem apq_arrayMapM {α : Type} (f : α → OracleComp KeccakCalls Digest) (G : List Digest → Prop)
    (hG : ∀ R R', G R → (∀ d ∈ R, d ∈ R') → G R')
    (hf : ∀ a R, G R → APq (fun v R' ↦ v ∈ R' ∧ ∀ d ∈ R, d ∈ R') R (f a)) (xs : Array α) (R : List Digest)
    (hR : G R) : APq (fun vs R' ↦ (∀ v ∈ vs, v ∈ R') ∧ ∀ d ∈ R, d ∈ R') R (xs.mapM f) := by
  rw [Array.mapM_eq_mapM_toList, map_eq_bind_pure_comp]
  exact (apq_mapM f G hG hf _ R hR).bind fun vs R' h ↦
    .ret _ ⟨fun v hv ↦ h.1 v (by simpa using hv), h.2⟩

theorem getD_mem_or (level : Array Digest) (i : ℕ) :
    level.getD i default ∈ level ∨ level.getD i default = default := by
  by_cases h : i < level.size
  · left
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h, Option.getD_some]
    exact Array.getElem_mem h
  · right
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none]

/-- **A tree's levels**: each node begins with a digest of the level below, or `default`. -/
theorem apq_levels (k : ℕ) : ∀ (level : Array Digest) (R : List Digest), default ∈ R → (∀ d ∈ level, d ∈ R) →
    APq (fun _ _ ↦ True) R (LeanVM.Prover.levelsWithHash callKeccak256 k level) := by
  induction k with
  | zero => intro level R _ _; exact .ret _ trivial
  | succ k ih =>
    intro level R hd hl
    unfold LeanVM.Prover.levelsWithHash LeanVM.Prover.parentsWithHash
    refine (apq_arrayMapM _ (fun R' ↦ default ∈ R' ∧ ∀ d ∈ level, d ∈ R')
      (fun R₁ R₂ h h12 ↦ ⟨h12 _ h.1, fun d hd' ↦ h12 d (h.2 d hd')⟩)
      (fun j R₁ h ↦ apq_H _ fun _ ↦ ⟨level.getD (2 * j) default,
        (getD_mem_or level (2 * j)).elim (fun h' ↦ h.2 _ h') (fun h' ↦ by rw [h']; exact h.1), take_digestBytes _ _⟩)
      _ R ⟨hd, hl⟩).bind fun up R' h ↦ (ih up R' (h.2 _ hd) h.1).bind fun _ _ _ ↦ .ret _ trivial

/-- **A Merkle tree over rows of `64` words**: `512`-byte leaves, then the levels. -/
theorem apq_buildTree (height : ℕ) (word : LeanVM.Protocol.Compile.Word) (hw : ∀ p, (word p).length = 64)
    (R : List Digest) (hR : default ∈ R) :
    APq (fun _ _ ↦ True) R (LeanVM.Prover.buildTreeWithHash callKeccak256 height word) := by
  unfold LeanVM.Prover.buildTreeWithHash LeanVM.Prover.leafDigestsWithHash
  refine (apq_arrayMapM _ (fun _ ↦ True) (fun _ _ _ _ ↦ trivial)
    (fun i R₁ _ ↦ apq_H _ fun h64 ↦ absurd h64 (by rw [E2ECompleteness.length_flatMap_kBytes, hw]; omega))
    _ R trivial).bind fun leaves R' h ↦
      (apq_levels height leaves R' (h.2 _ hR) h.1).bind fun _ _ _ ↦ .ret _ trivial

theorem apq_commitWithH (μ : ℕ) (stack : Array K) (R : List Digest) (hR : default ∈ R) :
    APq (fun _ _ ↦ True) R (E2ECompleteness.commitWithH callKeccak256 μ stack) :=
  apq_buildTree _ _ (E2ECompleteness.length_stackWordFast μ 1 stack) R hR

/-! ## The probability -/

/-- **A tree avoids `u`**: from a cache that neither answers `u` nor holds a `64`-byte input beginning with it, `u`
off the received digests, a computation of at most `NT` hash queries whose `64`-byte queries begin with received
digests ends with a `64`-byte hit at `u` with probability at most `NT / 2^256` (a fresh answer equal to `u`). -/
theorem prHit64_le {α : Type} {Q : α → List Digest → Prop} {R : List Digest} {T : OracleComp KeccakCalls α}
    (h : APq Q R T) : ∀ {NT : ℕ}, HC T NT → ∀ (c : Cache) (u : Digest), u ∉ R → ¬ Ans c u → ¬ Hit64 c u →
      Pr{let z ← (simulateQ ro T).run c}[Hit64 z.2 u] ≤ (NT : ℝ≥0∞) / 2 ^ 256 := by
  classical
  induction h with
  | ret a _ =>
    intro NT _ c u _ _ hh
    rw [simulateQ_pure, StateT.run_pure]
    refine (le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ↦ ?_)).trans zero_le
    rw [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hh
  | @query R x k hx _ ih =>
    intro NT hT c u hu ha hh
    have hT' := (Common.isWeightBound_query_bind_iff _ _ _ _).1 hT
    have h1 : 1 ≤ NT := hT'.1
    have hk : ∀ v, HC (k v) (NT - 1) := hT'.2
    rw [simulateQ_bind, simulateQ_callKeccak256, StateT.run_bind]
    rcases hcx : c (.inl x) with _ | v
    · rw [prEvent_fresh _ _ hcx]
      have hterm : ∀ v, Pr{let z ← (simulateQ ro (k v)).run (c.cacheQuery (.inl x) v)}[Hit64 z.2 u] ≤
          (if v = u then 1 else 0) + ((NT - 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
        intro v
        by_cases hv : v = u
        · simp only [hv, ↓reduceIte]
          exact (prEvent_le_one _).trans le_self_add
        simp only [hv, ↓reduceIte, zero_add]
        refine ih v (hk v) _ u (fun hm ↦ ?_) (fun ⟨m, hm⟩ ↦ ?_) (fun ⟨m, hmc, hl, ht⟩ ↦ ?_)
        · rcases List.mem_cons.mp hm with h' | h'
          · exact hv h'.symm
          · exact hu h'
        · by_cases hmx : m = x
          · subst hmx
            rw [QueryCache.cacheQuery_self] at hm
            exact hv (Option.some_injective _ hm)
          · rw [QueryCache.cacheQuery_of_ne _ _ (fun h ↦ hmx (Sum.inl_injective h))] at hm
            exact ha ⟨m, hm⟩
        · by_cases hmx : m = x
          · subst hmx
            obtain ⟨a, haR, hat⟩ := hx hl
            have := E2ECompleteness.digestBytes_injective (hat.symm.trans ht)
            subst this
            exact hu haR
          · rw [QueryCache.cacheQuery_of_ne _ _ (fun h ↦ hmx (Sum.inl_injective h))] at hmc
            exact hh ⟨m, hmc, hl, ht⟩
      calc (∑ v : Digest, Pr{let z ← (simulateQ ro (k v)).run (c.cacheQuery (.inl x) v)}[Hit64 z.2 u]) / 2 ^ 256
          ≤ (∑ v : Digest, ((if v = u then 1 else 0) + ((NT - 1 : ℕ) : ℝ≥0∞) / 2 ^ 256)) / 2 ^ 256 :=
            ENNReal.div_le_div_right (Finset.sum_le_sum fun v _ ↦ hterm v) _
        _ = 1 / 2 ^ 256 + ((NT - 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
            rw [Finset.sum_add_distrib, ENNReal.add_div, sum_const_div, Finset.sum_ite_eq']
            simp
        _ = (NT : ℝ≥0∞) / 2 ^ 256 := by
            rw [← ENNReal.add_div]
            congr 1
            rw [← Nat.cast_one, ← Nat.cast_add]
            congr 1
            omega
    · rw [ro_run_cached _ _ hcx, pure_bind]
      have hvu : v ≠ u := fun e ↦ ha ⟨x, e ▸ hcx⟩
      refine (ih v (hk v) c u (fun hm ↦ ?_) ha hh).trans
        (ENNReal.div_le_div_right (by exact_mod_cast Nat.sub_le _ _) _)
      rcases List.mem_cons.mp hm with h' | h'
      · exact hvu h'.symm
      · exact hu h'

/-! ## `t`'s freshness for a staged run -/

/-- An event of a map's continuation, by the event before it. -/
theorem prEvent_map_bind_pure {β γ' δ' : Type} (X : ProbComp β) (f : β → γ') (F : γ' → δ') (Ev : δ' → Prop)
    (Ev' : β → Prop) (h : ∀ x, Ev (F (f x)) → Ev' x) :
    Pr{let z ← (f <$> X) >>= fun y ↦ pure (F y)}[Ev z] ≤ Pr{let x ← X}[Ev' x] := by
  have e : ((f <$> X) >>= fun y ↦ pure (F y)) = (F ∘ f) <$> X := by
    simp [map_eq_bind_pure_comp, bind_assoc]
    rfl
  rw [e, prEvent_map]
  exact prEvent_mono _ _ _ fun x hx ↦ h x hx

/-- **The staged run up to `t`, simulated**, `B` a computation `T` then a pure writer `g`. -/
theorem run_pre_tree (S : Pi2Staged) {δ : Type} (T : S.α → Digest → Digest → Digest → OracleComp KeccakCalls δ)
    (g : S.α → Digest → Digest → Digest → δ → S.β)
    (hB : ∀ a s₁ s₂ s₃, S.B a s₁ s₂ s₃ = T a s₁ s₂ s₃ >>= fun d ↦ pure (g a s₁ s₂ s₃ d)) (c₀ : Cache) :
    (simulateQ ro S.pre).run c₀ =
      (simulateQ ro S.A).run c₀ >>= fun p ↦
      (ro (.inl (S.inp p.1))).run p.2 >>= fun q₁ ↦
      (ro (.inl (digestBytes q₁.1))).run q₁.2 >>= fun q₂ ↦
      (ro (.inl (digestBytes q₂.1))).run q₂.2 >>= fun q₃ ↦
      (simulateQ ro (T p.1 q₁.1 q₂.1 q₃.1)).run q₃.2 >>= fun z ↦
      pure ((g p.1 q₁.1 q₂.1 q₃.1 z.1, (S.pr p.1, chalP q₁.1, chalP q₂.1, chalP q₃.1)), z.2) := by
  simp only [Pi2Staged.pre, hB, simulateQ_bind, simulateQ_pure, simulateQ_callKeccak256, StateT.run_bind,
    StateT.run_pure, bind_assoc, pure_bind]
  rfl

/-- **`t`'s query is fresh**: for a staged run whose stage A makes at most `KA` hash queries, `α`'s input of
`L ≠ 32` bytes cached after A with probability at most `εα`, and whose `B` is a computation `T` (at most `NT` hash
queries, none of `32` bytes, its `64`-byte queries beginning with received digests or `default`) then a writer whose
`t` input is `64` bytes beginning with `s₃`'s: `t`'s input is cached when asked with probability at most
`εα + (4 KA + 6 + NT) / 2^256`. -/
theorem tFresh_of (S : Pi2Staged) {δ : Type} (T : S.α → Digest → Digest → Digest → OracleComp KeccakCalls δ)
    (g : S.α → Digest → Digest → Digest → δ → S.β)
    (hB : ∀ a s₁ s₂ s₃, S.B a s₁ s₂ s₃ = T a s₁ s₂ s₃ >>= fun d ↦ pure (g a s₁ s₂ s₃ d))
    (hTap : ∀ a s₁ s₂ s₃, APq (fun _ _ ↦ True) [default] (T a s₁ s₂ s₃))
    (hT32 : ∀ a s₁ s₂ s₃, HashOK (fun m ↦ m.length ≠ 32) (T a s₁ s₂ s₃))
    {NT : ℕ} (hTc : ∀ a s₁ s₂ s₃, HC (T a s₁ s₂ s₃) NT)
    (htin : ∀ a s₁ s₂ s₃ d, (S.tin (g a s₁ s₂ s₃ d)).length = 64 ∧
      (S.tin (g a s₁ s₂ s₃ d)).take 32 = digestBytes s₃)
    {L : ℕ} (hL : L ≠ 32) (hinp : ∀ a, (S.inp a).length = L) {KA : ℕ} (hA : HC S.A KA) {εα : ℝ≥0∞}
    (hα : Pr{let p ← (simulateQ ro S.A).run ∅}[p.2 (.inl (S.inp p.1)) ≠ none] ≤ εα) :
    Pr{let p ← (simulateQ ro S.pre).run ∅}[p.2 (.inl (S.tin p.1.1)) ≠ none] ≤
      εα + ((4 * KA + 6 + NT : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  classical
  rw [run_pre_tree S T g hB]
  refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun p ↦ p.2 (.inl (S.inp p.1)) ≠ none) _
    fun p hp hpα ↦ ?_).trans (add_le_add hα le_rfl)
  have hfα : p.2 (.inl (S.inp p.1)) = none := not_not.mp hpα
  have hcp : CacheBound p.2 KA := by simpa using cacheBound_run hA cacheBound_empty hp
  set c := p.2 with hc
  have hne : ∀ s : Digest, (Sum.inl (digestBytes s) : Bytes ⊕ KeccakState) ≠ .inl (S.inp p.1) := fun s h ↦
    hL ((hinp p.1).symm.trans (by rw [← Sum.inl_injective h, length_digestBytes]))
  -- `s₁`: fresh.
  refine (prEvent_query_le _ _ False (fun _ ↦ hfα) _ _
    (fun s₁ ↦ (if c (.inl (digestBytes s₁)) ≠ none then 1 else 0) +
      ((KA + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 + ((2 * KA + 5 + NT : ℕ) : ℝ≥0∞) / 2 ^ 256)
    fun s₁ ↦ ?_).trans ?_
  rotate_left
  · simp only [↓reduceIte, zero_add]
    rw [Finset.sum_add_distrib, ENNReal.add_div, Finset.sum_add_distrib, ENNReal.add_div, sum_const_div,
      sum_const_div]
    refine (add_le_add (add_le_add (ENNReal.div_le_div_right (sum_cached_le hcp) _) le_rfl) le_rfl).trans
      (le_of_eq ?_)
    rw [← ENNReal.add_div, ← ENNReal.add_div]
    congr 1
    push_cast
    ring
  -- `s₂`: fresh unless `s₁`'s bytes were cached.
  refine (prEvent_query_le _ _ (c (.inl (digestBytes s₁)) ≠ none)
    (fun hs ↦ by rw [QueryCache.cacheQuery_of_ne _ _ (hne s₁)]; exact not_not.mp hs) _ _
    (fun s₂ ↦ (if s₂ = s₁ ∨ c (.inl (digestBytes s₂)) ≠ none then 1 else 0) +
      ((2 * KA + 5 + NT : ℕ) : ℝ≥0∞) / 2 ^ 256) fun s₂ ↦ ?_).trans ?_
  rotate_left
  · refine le_trans ?_ (le_of_eq (add_assoc _ _ _).symm)
    refine add_le_add le_rfl ?_
    rw [Finset.sum_add_distrib, ENNReal.add_div, sum_const_div]
    refine add_le_add (ENNReal.div_le_div_right ?_ _) le_rfl
    calc (∑ s₂ : Digest, (if s₂ = s₁ ∨ c (.inl (digestBytes s₂)) ≠ none then 1 else 0 : ℝ≥0∞))
        ≤ ∑ s₂ : Digest, ((if s₂ ∈ [s₁] then 1 else 0) + (if c (.inl (digestBytes s₂)) ≠ none then 1 else 0)) :=
          Finset.sum_le_sum fun s₂ _ ↦ by
            simpa only [List.mem_singleton] using ite_or_le (s₂ = s₁) (c (.inl (digestBytes s₂)) ≠ none)
      _ ≤ (([s₁].length : ℕ) : ℝ≥0∞) + KA := by
          rw [Finset.sum_add_distrib]
          exact add_le_add (sum_mem_le _) (sum_cached_le hcp)
      _ = ((KA + 1 : ℕ) : ℝ≥0∞) := by simp only [List.length_singleton, Nat.cast_one]; push_cast; ring
  -- the cache before `s₃`
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : Cache,
      (c.cacheQuery (.inl (S.inp p.1)) s₁).cacheQuery (.inl (digestBytes s₁)) s₂ = c₂ := ⟨_, rfl⟩
  have hc₂b : CacheBound c₂ (KA + 2) := by
    rw [← hc₂]
    exact (hcp.cacheQuery_inl _ _).cacheQuery_inl _ _
  dsimp only
  rw [hc₂]
  -- `s₃`: fresh unless `s₂ = s₁` or `s₂`'s bytes were cached.
  refine (prEvent_query_le _ _ (s₂ = s₁ ∨ c (.inl (digestBytes s₂)) ≠ none) (fun hs ↦ ?_) _ _
    (fun u ↦ (if u = default ∨ Ans c₂ u ∨ Hit64 c₂ u then 1 else 0) + (NT : ℝ≥0∞) / 2 ^ 256)
    fun u ↦ ?_).trans (add_le_add le_rfl ?_)
  · rw [not_or] at hs
    have h12 : (Sum.inl (digestBytes s₂) : Bytes ⊕ KeccakState) ≠ .inl (digestBytes s₁) := fun h ↦
      hs.1 (E2ECompleteness.digestBytes_injective (Sum.inl_injective h))
    rw [← hc₂, QueryCache.cacheQuery_of_ne _ _ h12, QueryCache.cacheQuery_of_ne _ _ (hne s₂)]
    exact not_not.mp hs.2
  · -- the tree after `u = s₃`
    by_cases hbad : u = default ∨ Ans c₂ u ∨ Hit64 c₂ u
    · simp only [hbad, ↓reduceIte]
      exact (prEvent_le_one _).trans le_self_add
    simp only [hbad, ↓reduceIte, zero_add]
    rw [not_or, not_or] at hbad
    have hT2 : HashOK (fun m ↦ m ≠ digestBytes s₂) (T p.1 s₁ s₂ u) :=
      UniComplete.Prob.HashOK.mono (P := fun m ↦ m.length ≠ 32) (Q := fun m ↦ m ≠ digestBytes s₂) (fun m hm he ↦ hm (by rw [he]; exact length_digestBytes s₂))
        (hT32 _ _ _ _)
    try dsimp only
    rw [run_frame _ u _ hT2 c₂]
    refine (prEvent_map_bind_pure _ _ _ _ (fun z ↦ Hit64 z.2 u) fun z hz ↦ ?_).trans ?_
    · obtain ⟨hl, ht⟩ := htin p.1 s₁ s₂ u z.1
      have hn : (Sum.inl (S.tin (g p.1 s₁ s₂ u z.1)) : Bytes ⊕ KeccakState) ≠ .inl (digestBytes s₂) := fun h ↦ by
        have := congrArg List.length (Sum.inl_injective h)
        rw [hl, length_digestBytes] at this
        omega
      dsimp only at hz
      rw [QueryCache.cacheQuery_of_ne _ _ hn] at hz
      exact ⟨_, hz, hl, ht⟩
    · exact prHit64_le (hTap p.1 s₁ s₂ u) (hTc _ _ _ _) c₂ u
        (fun hm ↦ hbad.1 (List.mem_singleton.mp hm)) hbad.2.1 hbad.2.2
  · -- the average over `u`
    rw [Finset.sum_add_distrib, ENNReal.add_div, sum_const_div]
    have hsum : (∑ u : Digest, (if u = default ∨ Ans c₂ u ∨ Hit64 c₂ u then 1 else 0 : ℝ≥0∞)) ≤
        ((2 * KA + 5 : ℕ) : ℝ≥0∞) := by
      calc (∑ u : Digest, (if u = default ∨ Ans c₂ u ∨ Hit64 c₂ u then 1 else 0 : ℝ≥0∞))
          ≤ ∑ u : Digest, ((if u ∈ [default] then 1 else 0) + ((if Ans c₂ u then 1 else 0) +
              (if Hit64 c₂ u then 1 else 0))) :=
            Finset.sum_le_sum fun u _ ↦ (ite_or_le _ _).trans (add_le_add (by simp) (ite_or_le _ _))
        _ ≤ (([default].length : ℕ) : ℝ≥0∞) + (((KA + 2 : ℕ) : ℝ≥0∞) + ((KA + 2 : ℕ) : ℝ≥0∞)) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
            exact add_le_add (sum_mem_le _) (add_le_add (sum_ans_le hc₂b) (sum_hit64_le hc₂b))
        _ = ((2 * KA + 5 : ℕ) : ℝ≥0∞) := by
            simp only [List.length_singleton, Nat.cast_one]
            push_cast
            ring
    refine (add_le_add (ENNReal.div_le_div_right hsum _) le_rfl).trans (le_of_eq ?_)
    rw [← ENNReal.add_div]
    congr 1
    push_cast
    ring

end TF

end RecCompose.Pi2P

/-- info: 'RecCompose.Pi2P.TF.prHit64_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2P.TF.prHit64_le

/-- info: 'RecCompose.Pi2P.TF.apq_commitWithH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2P.TF.apq_commitWithH

/-- info: 'RecCompose.Pi2P.TF.tFresh_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2P.TF.tFresh_of
