-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Compose.Final128Defs
import WhirBridge.Union

/-!
# The openings' doom at the run's end, charged once

`ListChainKDoom.lean`'s `prEvent_doomAt_le` charges each opening of the verifier its own F2 bound
at the queries before it (`doomSum`): five openings, five charges of `2^-128` per query. Here every
opening's doom is read at the end of the whole run (`DoomF`, `Final128Defs.lean`) and the openings
are charged **once**, as statements of one Fiat-Shamir family (`WhirBridge.union_sound`):

**`prEvent_doomF_le`**: for shapes `shs` at a per-group bound `ε` whose verifier prefixes are
distinct, openings whose shapes are among them (`hops`), and a run before the openings `X` of `QX`
queries, the probability that some opening accepts while doomed at the run's end is at most

`(QX + Σ_k QO_k + QV) · (ε + 5 (QX + Σ_k QO_k + QV) / 2^256)`,  `QV ≥` every shape's `QO`,

generic in the number and the shapes of the openings.

The proof has no per-stage argument. The union adversary (`pickU <$> expL view X ops`) runs the
whole run (`X`'s queries and every opening's) and outputs the first opening doomed at the run's end
(`firstDoom`, chosen classically from the transcript), as a statement of the union (`pickU`, along
`s.L = o.S.L`, `toU`). It has already run that opening's verifier on that very input, so the union
verifier's run asks only cached queries: a run of the lazy random oracle only extends its cache,
and from any larger cache returns the same result without a fresh query
(`run_replay_of_mem_support`), and every opening's run sits inside the openings' run
(`opsRun_replayF`, `expL_replayF`). The experiment's final cache is then the run's, whose
Keccak-256 answers are the transcript's (`consistent_run_loggedKC`), so the doom at the run's end
is the union's event (`prEvent_doomF_le_union`), and `union_sound` at `QA = QX + Σ_k QO_k` bounds
it.

**`prEvent_doomF_le_large`**: at `εExact = 269 · 2^-137 (= 2^-128.93)`, `largeShapes` and
`QV = 9018`, for openings on the plain layouts of `2^24 ..= 2^28` words (`WhirShape.large` of
`Layout.new μ μ μ [(0, 2^μ)]` has them by `rfl`).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm LeanVM LeanVM.Protocol LeanVM.Semantics
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open LeanVM.Protocol.Rom (romExperiment romExperiment_map romExperiment_eq)

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## The lazy random oracle replays -/

/-- **A run of the lazy random oracle only extends its cache, and replays**: on every outcome
`(a, c₁)` from the cache `c₀`, `c₀ ≤ c₁`, and from every cache `c₂ ≥ c₁` the run returns `a` and
leaves `c₂` unchanged (every query it asks is cached). -/
theorem run_replay_of_mem_support {α : Type} (oa : OracleComp KeccakCalls α) :
    ∀ (c₀ : KeccakCalls.QueryCache) (p : α × KeccakCalls.QueryCache),
      p ∈ support ((simulateQ randomOracle oa).run c₀) →
        c₀ ≤ p.2 ∧ ∀ c₂, p.2 ≤ c₂ → (simulateQ randomOracle oa).run c₂ = pure (p.1, c₂) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro c₀ p hp
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨le_rfl, fun c₂ _ ↦ by simp only [simulateQ_pure, StateT.run_pure]⟩
  | query_bind t k ih =>
    intro c₀ p hp
    rw [LeanVM.Protocol.Rom.run_simulateQ_bind, simulateQ_spec_query, randomOracle.run_eq] at hp
    rw [mem_support_bind_iff] at hp
    obtain ⟨q, hq, hp⟩ := hp
    have hq' : c₀ ≤ q.2 ∧ q.2 t = some q.1 := by
      cases hct : c₀ t with
      | some u =>
        rw [hct] at hq
        simp only [support_pure, Set.mem_singleton_iff] at hq
        subst hq
        exact ⟨le_rfl, hct⟩
      | none =>
        rw [hct] at hq
        rw [mem_support_bind_iff] at hq
        obtain ⟨u, -, hu⟩ := hq
        simp only [support_pure, Set.mem_singleton_iff] at hu
        subst hu
        exact ⟨QueryCache.le_cacheQuery _ hct, QueryCache.cacheQuery_self _ _ _⟩
    obtain ⟨h1, h2⟩ := ih q.1 q.2 p hp
    refine ⟨hq'.1.trans h1, fun c₂ hc₂ ↦ ?_⟩
    have hc : c₂ t = some q.1 := hc₂ (h1 hq'.2)
    rw [LeanVM.Protocol.Rom.run_simulateQ_bind, simulateQ_spec_query, randomOracle.run_eq]
    simp only [hc, pure_bind]
    exact h2 c₂ hc₂

section First

variable {F St M Pf : Type} [SampleableType F]

/-! ## Every opening's run sits inside the run -/

/-- **Every opening replays at the openings' end**: on every outcome `(bs, c)` of the openings,
opening `k`'s verifier on its input, from `c`, returns `bs[k]` without a fresh query. -/
theorem opsRun_replayF (view : Pf → St × List (RMsg F)) :
    ∀ (ops : List (WhirOp Pf F M)) (π : Pf) (ch : List (List F)) (c₁ : KeccakCalls.QueryCache)
      (r : List Bool × KeccakCalls.QueryCache),
      r ∈ support ((simulateQ randomOracle (opsRun view ops π ch)).run c₁) →
        ∀ k (hk : k < ops.length),
          (simulateQ randomOracle (ourVerifier ops[k].S.L ops[k].S.R
            (WhirOp.input view ops[k] π ch))).run r.2 = pure (r.1.getD k false, r.2)
  | [], _, _, _, _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | o :: os, π, ch, c₁, r, hr, k, hk => by
    simp only [opsRun] at hr
    rw [LeanVM.Protocol.Rom.run_simulateQ_bind, mem_support_bind_iff] at hr
    obtain ⟨p, hp, hr⟩ := hr
    rw [simulateQ_map, StateT.run_map, support_map] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    cases k with
    | zero =>
      exact (run_replay_of_mem_support _ _ _ hp).2 _ (run_replay_of_mem_support _ _ _ hr').1
    | succ k =>
      exact opsRun_replayF view os π ch p.2 r' hr' k (by simpa using hk)

/-- **The run's outcome**: the cache's Keccak-256 answers are the transcript's, and every opening
replays at the run's end. -/
theorem expL_replayF (view : Pf → St × List (RMsg F)) (X : OracleComp KeccakCalls (PreK Pf F))
    (ops : List (WhirOp Pf F M))
    (p : (OutK Pf F (List Bool) × Transcript) × KeccakCalls.QueryCache)
    (hp : p ∈ support ((simulateQ randomOracle (expL view X ops)).run ∅)) :
    Consistent p.1.2 p.2 ∧ ∀ k (hk : k < ops.length),
      (simulateQ randomOracle (ourVerifier ops[k].S.L ops[k].S.R
        (WhirOp.input view ops[k] p.1.1.1.1 p.1.1.1.2.1))).run p.2 =
          pure (p.1.1.1.2.2.getD k false, p.2) := by
  refine ⟨consistent_run_loggedKC _ [] ∅ consistent_nil p hp, ?_⟩
  obtain ⟨⟨z, tr⟩, c⟩ := p
  have hp' : (z, c) ∈ support ((simulateQ randomOracle
      (X >>= fun x ↦ opsOut x <$> opsRun view ops x.1 x.2.1)).run ∅) := by
    rw [← map_run_loggedKC (X >>= fun x ↦ opsOut x <$> opsRun view ops x.1 x.2.1) [] ∅,
      support_map]
    exact ⟨((z, tr), c), hp, rfl⟩
  rw [LeanVM.Protocol.Rom.run_simulateQ_bind, mem_support_bind_iff] at hp'
  obtain ⟨q, -, hq⟩ := hp'
  rw [simulateQ_map, StateT.run_map, support_map] at hq
  obtain ⟨r, hr, hqr⟩ := hq
  simp only [Prod.mk.injEq] at hqr
  obtain ⟨rfl, rfl⟩ := hqr
  intro k hk
  exact opsRun_replayF view ops q.1.1 q.1.2.1 q.2 r hr k hk

/-! ## The first opening doomed at the run's end -/

/-- Opening `k` accepts while doomed at the run's end (`DoomF`'s witness). -/
def DoomAtEnd (view : Pf → St × List (RMsg F)) (ops : List (WhirOp Pf F M))
    (z : OutK Pf F (List Bool) × Transcript) (k : ℕ) : Prop :=
  ∃ hk : k < ops.length, z.1.1.2.2.getD k false = true ∧
    OpeningDoomed ops[k].S.L ops[k].S.R (WhirOp.input view ops[k] z.1.1.1 z.1.1.2.1)
      (cacheOfTr z.2)

theorem doomF_iff_exists (view : Pf → St × List (RMsg F)) (ops : List (WhirOp Pf F M))
    (z : OutK Pf F (List Bool) × Transcript) :
    DoomF view ops z ↔ ∃ k, DoomAtEnd view ops z k := Iff.rfl

open Classical in
/-- **The first opening doomed at the run's end**, `0` if none. -/
noncomputable def firstDoom (view : Pf → St × List (RMsg F)) (ops : List (WhirOp Pf F M))
    (z : OutK Pf F (List Bool) × Transcript) : ℕ :=
  if h : ∃ k, DoomAtEnd view ops z k then Nat.find h else 0

open Classical in
theorem firstDoom_lt (view : Pf → St × List (RMsg F)) {ops : List (WhirOp Pf F M)}
    (hne : ops ≠ []) (z : OutK Pf F (List Bool) × Transcript) :
    firstDoom view ops z < ops.length := by
  unfold firstDoom
  split
  · rename_i h
    obtain ⟨hk, -⟩ := Nat.find_spec h
    exact hk
  · cases ops with
    | nil => exact absurd rfl hne
    | cons o os => exact Nat.succ_pos _

open Classical in
theorem doomAtEnd_firstDoom (view : Pf → St × List (RMsg F)) (ops : List (WhirOp Pf F M))
    {z : OutK Pf F (List Bool) × Transcript} (h : DoomF view ops z) :
    DoomAtEnd view ops z (firstDoom view ops z) := by
  have h' : ∃ k, DoomAtEnd view ops z k := h
  unfold firstDoom
  rw [dif_pos h']
  exact Nat.find_spec h'

/-! ## An opening as a statement of the union -/

/-- Every opening's shape is a shape of the union, by index. -/
theorem exists_shapeIdx {ε : ℝ≥0∞} {shs : List (ExactShape ε)} {ops : List (WhirOp Pf F M)}
    (hops : ∀ o ∈ ops, ∃ s ∈ shs, s.L = o.S.L ∧ s.R = o.S.R) (k : ℕ) (hk : k < ops.length) :
    ∃ j : Fin shs.length, (shs.get j).L = ops[k].S.L ∧ (shs.get j).R = ops[k].S.R := by
  obtain ⟨s, hs, hL, hR⟩ := hops _ (List.getElem_mem hk)
  obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hs
  exact ⟨j, hL, hR⟩

/-- **An opening's input as the union's**, along `(shs.get j).L = L`. -/
def toU {ε : ℝ≥0∞} (shs : List (ExactShape ε)) (j : Fin shs.length) {L : Layout}
    (hL : (shs.get j).L = L) (w : (Digest × Stmt L.stacking) × Proof) : UIn shs × Proof :=
  (⟨j, (w.1.1, (congrArg (fun L' : Layout ↦ Stmt L'.stacking) hL).mpr w.1.2)⟩, w.2)

theorem uVer_toU {ε : ℝ≥0∞} (shs : List (ExactShape ε)) (j : Fin shs.length) {L : Layout}
    {R : ℕ} (hL : (shs.get j).L = L) (hR : (shs.get j).R = R)
    (w : (Digest × Stmt L.stacking) × Proof) :
    uVer shs (toU shs j hL w) = ourVerifier L R w := by
  subst hL hR
  rfl

theorem uDoomed_toU {ε : ℝ≥0∞} (shs : List (ExactShape ε)) (j : Fin shs.length) {L : Layout}
    {R : ℕ} (hL : (shs.get j).L = L) (hR : (shs.get j).R = R)
    (w : (Digest × Stmt L.stacking) × Proof) (c : KeccakCalls.QueryCache) :
    UDoomed shs (toU shs j hL w) c ↔ OpeningDoomed L R w c := by
  subst hL hR
  rfl

/-- **The union adversary's output**: the first opening doomed at the run's end (opening `0`
if none), as a statement of the union. -/
noncomputable def pickU {ε : ℝ≥0∞} (shs : List (ExactShape ε)) (view : Pf → St × List (RMsg F))
    (ops : List (WhirOp Pf F M)) (hops : ∀ o ∈ ops, ∃ s ∈ shs, s.L = o.S.L ∧ s.R = o.S.R)
    (hne : ops ≠ []) (z : OutK Pf F (List Bool) × Transcript) : UIn shs × Proof :=
  toU shs (exists_shapeIdx hops _ (firstDoom_lt view hne z)).choose
    (exists_shapeIdx hops _ (firstDoom_lt view hne z)).choose_spec.1
    (WhirOp.input view (ops[firstDoom view ops z]'(firstDoom_lt view hne z)) z.1.1.1 z.1.1.2.1)

theorem uVer_pickU {ε : ℝ≥0∞} (shs : List (ExactShape ε)) (view : Pf → St × List (RMsg F))
    (ops : List (WhirOp Pf F M)) (hops : ∀ o ∈ ops, ∃ s ∈ shs, s.L = o.S.L ∧ s.R = o.S.R)
    (hne : ops ≠ []) (z : OutK Pf F (List Bool) × Transcript) :
    uVer shs (pickU shs view ops hops hne z) =
      ourVerifier (ops[firstDoom view ops z]'(firstDoom_lt view hne z)).S.L
        (ops[firstDoom view ops z]'(firstDoom_lt view hne z)).S.R
        (WhirOp.input view (ops[firstDoom view ops z]'(firstDoom_lt view hne z))
          z.1.1.1 z.1.1.2.1) :=
  uVer_toU shs (exists_shapeIdx hops _ (firstDoom_lt view hne z)).choose
    (exists_shapeIdx hops _ (firstDoom_lt view hne z)).choose_spec.1
    (exists_shapeIdx hops _ (firstDoom_lt view hne z)).choose_spec.2 _

theorem uDoomed_pickU {ε : ℝ≥0∞} (shs : List (ExactShape ε)) (view : Pf → St × List (RMsg F))
    (ops : List (WhirOp Pf F M)) (hops : ∀ o ∈ ops, ∃ s ∈ shs, s.L = o.S.L ∧ s.R = o.S.R)
    (hne : ops ≠ []) (z : OutK Pf F (List Bool) × Transcript) (c : KeccakCalls.QueryCache) :
    UDoomed shs (pickU shs view ops hops hne z) c ↔
      OpeningDoomed (ops[firstDoom view ops z]'(firstDoom_lt view hne z)).S.L
        (ops[firstDoom view ops z]'(firstDoom_lt view hne z)).S.R
        (WhirOp.input view (ops[firstDoom view ops z]'(firstDoom_lt view hne z))
          z.1.1.1 z.1.1.2.1) c :=
  uDoomed_toU shs (exists_shapeIdx hops _ (firstDoom_lt view hne z)).choose
    (exists_shapeIdx hops _ (firstDoom_lt view hne z)).choose_spec.1
    (exists_shapeIdx hops _ (firstDoom_lt view hne z)).choose_spec.2 _ c

/-! ## The queries -/

/-- The openings make at most `Σ_k QO_k` queries. -/
theorem isTotalQueryBound_opsRunFD (view : Pf → St × List (RMsg F)) :
    ∀ (ops : List (WhirOp Pf F M)) (π : Pf) (ch : List (List F)),
      IsTotalQueryBound (opsRun view ops π ch) (ops.map fun o => o.S.QO).sum
  | [], _, _ => trivial
  | o :: os, π, ch => by
    simp only [opsRun, List.map_cons, List.sum_cons]
    exact isTotalQueryBound_bind (o.S.queries _) fun _ =>
      (isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_opsRunFD view os π ch)

/-- The run with its whole transcript makes at most `QX + Σ_k QO_k` queries. -/
theorem isTotalQueryBound_expLFD (view : Pf → St × List (RMsg F))
    (X : OracleComp KeccakCalls (PreK Pf F)) (ops : List (WhirOp Pf F M)) (QX : ℕ)
    (hX : IsTotalQueryBound X QX) :
    IsTotalQueryBound (expL view X ops) (QX + (ops.map fun o => o.S.QO).sum) := by
  unfold expL
  exact isTotalQueryBound_loggedKC_run _ _ [] (isTotalQueryBound_bind hX fun x =>
    (isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_opsRunFD view ops x.1 x.2.1))

/-! ## The doom at the run's end is the union's event -/

/-- **The doom at the run's end is an event of the union's experiment**, against the adversary
that runs the whole run and outputs the first doomed opening. -/
theorem prEvent_doomF_le_union {ε : ℝ≥0∞} (shs : List (ExactShape ε))
    (view : Pf → St × List (RMsg F)) (ops : List (WhirOp Pf F M))
    (hops : ∀ o ∈ ops, ∃ s ∈ shs, s.L = o.S.L ∧ s.R = o.S.R) (hne : ops ≠ [])
    (X : OracleComp KeccakCalls (PreK Pf F)) :
    Pr{let z ← (simulateQ randomOracle (expL view X ops)).run' ∅}[DoomF view ops z] ≤
      Pr{let z ← romExperiment (pickU shs view ops hops hne <$> expL view X ops) (uVer shs)}[
        z.1.2 = true ∧ UDoomed shs z.1.1 z.2] := by
  rw [romExperiment_map, prEvent_map, romExperiment_eq, StateT.run'_eq, prEvent_map]
  conv_lhs => rw [← bind_pure ((simulateQ randomOracle (expL view X ops)).run ∅)]
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun p hp ↦ ?_
  classical
  by_cases hd : DoomF view ops p.1
  · obtain ⟨hcons, hrep⟩ := expL_replayF view X ops p hp
    obtain ⟨hk', hacc, hdoom⟩ := doomAtEnd_firstDoom view ops hd
    have hv : (simulateQ randomOracle (uVer shs (pickU shs view ops hops hne p.1))).run p.2 =
        pure (true, p.2) := by
      rw [uVer_pickU, hrep _ (firstDoom_lt view hne p.1), hacc]
    refine (prEvent_le_one _).trans (le_of_eq ?_)
    rw [hv, map_pure, prEvent_pure, if_pos]
    refine ⟨rfl, (uDoomed_pickU shs view ops hops hne p.1 p.2).2 ?_⟩
    have hc : (fun x ↦ p.2 (.inl x)) = fun x ↦ cacheOfTr p.1.2 (.inl x) :=
      funext fun x ↦ (hcons x).trans (cacheOfTr_inl _ _).symm
    unfold OpeningDoomed at hdoom ⊢
    rw [hc]
    exact hdoom
  · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun r hr hev ↦ ?_) bot_le
    rw [mem_support_pure_iff] at hr
    subst hr
    exact hd hev

end First

/-! ## The openings, charged once -/

/-- **The openings' doom at the run's end, charged once**: for shapes `shs` at a per-group bound
`ε` whose verifier prefixes are distinct, openings whose shapes are among them, and a run before
the openings of `QX` queries, some opening accepts while every candidate table of the word under
its root, read off the whole run's transcript, violates one of its claims with probability at most
`(QX + Σ_k QO_k + QV) · (ε + 5 (QX + Σ_k QO_k + QV) / 2^256)`, `QV` above every shape's query
count. -/
theorem prEvent_doomF_le {F St M Pf : Type} [SampleableType F] (ε : ℝ≥0∞)
    (shs : List (ExactShape ε)) (hpre : (shs.map fun s => openingPrefix s.L s.R).Nodup)
    (view : Pf → St × List (RMsg F)) (ops : List (WhirOp Pf F M))
    (hops : ∀ o ∈ ops, ∃ s ∈ shs, s.L = o.S.L ∧ s.R = o.S.R)
    (X : OracleComp KeccakCalls (PreK Pf F)) (QX : ℕ) (hX : IsTotalQueryBound X QX)
    (QV : ℕ) (hQV : ∀ s ∈ shs, s.QO ≤ QV) :
    Pr{let z ← (simulateQ randomOracle (expL view X ops)).run' ∅}[DoomF view ops z] ≤
      ((QX + (ops.map fun o => o.S.QO).sum + QV : ℕ) : ℝ≥0∞) *
        (ε + ((5 * (QX + (ops.map fun o => o.S.QO).sum + QV) : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  rcases eq_or_ne ops [] with rfl | hne
  · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun z hz ↦ ?_) bot_le
    obtain ⟨k, hk, -⟩ := hz
    exact absurd hk (Nat.not_lt_zero _)
  · exact (prEvent_doomF_le_union shs view ops hops hne X).trans
      (union_sound shs hpre _ _ ((isQueryBound_map_iff _ _ _ _ _).mpr
        (isTotalQueryBound_expLFD view X ops QX hX)) QV hQV)

/-- **At the exact bound, on the plain layouts of `2^24 ..= 2^28` words**: openings each on some
`Layout.new μ μ μ [(0, 2^μ)]`, `24 ≤ μ ≤ 28`, at rate `1/2` (every `WhirShape.large` of such a
layout), are doomed at the run's end with probability at most
`(QX + Σ_k QO_k + 9018) · (2^-128.93 + 5 (QX + Σ_k QO_k + 9018) / 2^256)`. -/
theorem prEvent_doomF_le_large {F St M Pf : Type} [SampleableType F]
    (view : Pf → St × List (RMsg F)) (ops : List (WhirOp Pf F M))
    (hops : ∀ o ∈ ops, ∃ μ, 24 ≤ μ ∧ μ ≤ 28 ∧ o.S.L = Layout.new μ μ μ [(0, 2 ^ μ)] ∧
      o.S.R = logInvRate)
    (X : OracleComp KeccakCalls (PreK Pf F)) (QX : ℕ) (hX : IsTotalQueryBound X QX) :
    Pr{let z ← (simulateQ randomOracle (expL view X ops)).run' ∅}[DoomF view ops z] ≤
      ((QX + (ops.map fun o => o.S.QO).sum + 9018 : ℕ) : ℝ≥0∞) *
        (εExact + ((5 * (QX + (ops.map fun o => o.S.QO).sum + 9018) : ℕ) : ℝ≥0∞) / 2 ^ 256) :=
  prEvent_doomF_le εExact largeShapes largeShapes_nodup view ops
    (fun o ho ↦ by
      obtain ⟨μ, h1, h2, hL, hR⟩ := hops o ho
      obtain ⟨s, hs, hsL, hsR⟩ := largeShapes_plain μ h1 h2
      exact ⟨s, hs, hsL.trans hL.symm, hsR.trans hR.symm⟩)
    X QX hX 9018 largeShapes_QO

end Compose

/-- info: 'Compose.run_replay_of_mem_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.run_replay_of_mem_support

/-- info: 'Compose.prEvent_doomF_le_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.prEvent_doomF_le_union

/-- info: 'Compose.prEvent_doomF_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.prEvent_doomF_le

/-- info: 'Compose.prEvent_doomF_le_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.prEvent_doomF_le_large
