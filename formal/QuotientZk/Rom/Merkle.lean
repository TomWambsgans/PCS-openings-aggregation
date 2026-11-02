-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): `common`'s identical-until-bad lemma (`Common.prEvent_run_le_add_bad`,
-- `Common.prEvent_run_bad_eq`).
import QuotientZk.Rom.Split

/-!
# The unopened leaves: fresh digests until a row is asked

`implSplit σ s` answers the oracle at an unopened row with that leaf's digest (consistently, as
the random oracle does); the simulator's `implView σ v` gives an unopened leaf a fresh private
digest and answers every query from the cache alone. With `v` the honest view, the two agree
until **a private leaf's row is in the cache** (someone, the prover or the distinguisher, asked the
oracle at an unopened row, or a Fiat–Shamir input is one) **or two unopened positions have the same
row** (`MBad`): identical until `MBad` (`prEvent_view_le_split`, `prEvent_split_le_view`).
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace QuotientZk

set_option linter.unusedSectionVars false

variable {S I O M K X Pf : Type} [DecidableEq I] [SampleableType O] [Inhabited O]
  [DecidableEq K] [DecidableEq X] [Inhabited I]
variable (P : Proto S I O M K X)

/-- **The Merkle bad event**: a private digest's row is answered in the cache, or two private
positions have the same row. -/
def MBad (rows : K → X → I) (st : St I O K X) : Prop :=
  ∃ e ∈ st.priv, (st.cache (rows e.1.1 e.1.2)).isSome ∨
    ∃ e' ∈ st.priv, e'.1 ≠ e.1 ∧ rows e'.1.1 e'.1.2 = rows e.1.1 e.1.2

/-- A step only adds to the cache's domain and to the private digests. -/
def Grows (st st' : St I O K X) : Prop :=
  (∀ r, (st.cache r).isSome → (st'.cache r).isSome) ∧ ∀ e ∈ st.priv, e ∈ st'.priv

theorem mBad_of_grows (rows : K → X → I) {st st' : St I O K X} (h : Grows st st')
    (hb : MBad rows st) : MBad rows st' := by
  obtain ⟨e, he, hb⟩ := hb
  refine ⟨e, h.2 e he, ?_⟩
  rcases hb with hb | ⟨e', he', hne, heq⟩
  · exact Or.inl (h.1 _ hb)
  · exact Or.inr ⟨e', h.2 e' he', hne, heq⟩

theorem grows_cacheQuery (st : St I O K X) (t : I) (u : O) (h : List O) (l : List I) (b : Bool) :
    Grows st { st with cache := st.cache.cacheQuery t u, hist := h, log := l, fs := b } := by
  refine ⟨fun r hr => ?_, fun e he => he⟩
  by_cases h : r = t
  · subst h; simp
  · simpa [QueryCache.cacheQuery, h] using hr

theorem grows_append (st : St I O K X) (e : (K × X) × O) :
    Grows st { st with priv := st.priv ++ [e] } :=
  ⟨fun _ hr => hr, fun _ he => List.mem_append_left _ he⟩

theorem grows_refl (st : St I O K X) : Grows st st := ⟨fun _ h => h, fun _ h => h⟩

theorem roStep_grows (t : I) (st : St I O K X) :
    ∀ z ∈ support (roStep (K := K) (X := X) t st), Grows st z.2 := by
  intro z hz
  unfold roStep at hz
  cases h : st.cache t with
  | some u =>
    simp only [h, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact grows_refl st
  | none =>
    simp only [h, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact grows_cacheQuery st t u st.hist _ st.fs

theorem roSplit_grows (rows : K → X → I) (t : I) (st : St I O K X) :
    ∀ z ∈ support (roSplit rows t st), Grows st z.2 := by
  intro z hz
  unfold roSplit at hz
  cases h : st.cache t with
  | some u =>
    simp only [h, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact grows_refl st
  | none =>
    simp only [h] at hz
    cases hf : (st.priv.find? fun e => decide (rows e.1.1 e.1.2 = t)).map Prod.snd with
    | some u =>
      simp only [hf, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact grows_cacheQuery st t u st.hist _ st.fs
    | none =>
      simp only [hf, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨u, -, rfl⟩ := hz
      exact grows_cacheQuery st t u st.hist _ st.fs

theorem progStep_grows (t : I) (u : O) (st : St I O K X) :
    ∀ z ∈ support (progStep (K := K) (X := X) t u st), Grows st z.2 := by
  intro z hz
  simp only [progStep, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact grows_cacheQuery st t u _ _ _

theorem implView_grows (σ : List O) (v : View M I K X) (t : Op I K X) (st : St I O K X) :
    ∀ z ∈ support ((implView P σ v t).run st), Grows st z.2 := by
  intro z hz
  cases t with
  | pub t => exact roStep_grows t st z hz
  | msg =>
    simp only [implView, StateT.run, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact grows_refl st
  | leaf k x =>
    simp only [implView, StateT.run] at hz
    split_ifs at hz with h1 h2
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact grows_refl st
    · exact roStep_grows _ st z hz
    · cases hl : st.priv.lookup (k, x) with
      | some u =>
        simp only [hl, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact grows_refl st
      | none =>
        simp only [hl, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
        obtain ⟨u, -, rfl⟩ := hz
        exact grows_append st _
  | chal t =>
    simp only [implView, StateT.run] at hz
    split_ifs at hz
    · exact progStep_grows t _ st z hz
    · exact roStep_grows t st z hz

theorem implSplit_grows (σ : List O) (s : S) (t : Op I K X) (st : St I O K X) :
    ∀ z ∈ support ((implSplit P σ s t).run st), Grows st z.2 := by
  intro z hz
  cases t with
  | pub t => exact roSplit_grows _ t st z hz
  | msg =>
    simp only [implSplit, StateT.run, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact grows_refl st
  | leaf k x =>
    simp only [implSplit, StateT.run] at hz
    by_cases h1 : st.hist.length < P.cK k
    · simp only [h1, ite_true, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact grows_refl st
    · simp only [h1, ite_false] at hz
      by_cases h2 : P.opened σ k x = true
      · simp only [h2, ite_true] at hz
        exact roSplit_grows _ _ st z hz
      · simp only [h2, Bool.false_eq_true, ite_false] at hz
        cases hl : unionLook (P.rows s σ) st (P.rows s σ k x) with
        | some u =>
          simp only [hl, support_pure, Set.mem_singleton_iff] at hz
          subst hz
          split_ifs
          · exact grows_refl st
          · exact grows_append st _
        | none =>
          simp only [hl, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
          obtain ⟨u, -, rfl⟩ := hz
          exact grows_append st _
  | chal t =>
    simp only [implSplit, StateT.run] at hz
    split_ifs at hz
    · exact progStep_grows t _ st z hz
    · exact roSplit_grows _ t st z hz

/-! ## Agreement off the bad event -/

/-- Two steps that are equal, or that both always reach a bad state, agree off the bad event. -/
theorem agree_of_eq_or_bad {α σ : Type} (bad : σ → Prop) (A B : ProbComp (α × σ))
    (h : A = B ∨ ((∀ z ∈ support A, bad z.2) ∧ ∀ z ∈ support B, bad z.2))
    (q : α × σ → Prop) :
    Pr{let z ← A}[q z ∧ ¬ bad z.2] = Pr{let z ← B}[q z ∧ ¬ bad z.2] := by
  rcases h with rfl | ⟨hA, hB⟩
  · rfl
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h => h.2 (hA z hz),
      prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h => h.2 (hB z hz)]

theorem find?_eq_some_mem {α : Type} {p : α → Bool} {l : List α} {a : α} (h : l.find? p = some a) :
    a ∈ l ∧ p a = true :=
  ⟨List.mem_of_find?_eq_some h, List.find?_some h⟩

/-- A random-oracle query at a row: `roStep` and `roSplit` agree off `MBad`. -/
theorem ro_agree (rows : K → X → I) (r : I) (st : St I O K X) (hst : ¬ MBad rows st) :
    roStep r st = roSplit rows r st ∨
      ((∀ z ∈ support (roStep (K := K) (X := X) r st), MBad rows z.2) ∧
        ∀ z ∈ support (roSplit rows r st), MBad rows z.2) := by
  unfold roStep roSplit
  cases hc : st.cache r with
  | some u => exact Or.inl rfl
  | none =>
    cases hf : st.priv.find? (fun e => decide (rows e.1.1 e.1.2 = r)) with
    | none => exact Or.inl (by simp [hf])
    | some e =>
      obtain ⟨he, her⟩ := find?_eq_some_mem hf
      have her : rows e.1.1 e.1.2 = r := by simpa using her
      refine Or.inr ⟨fun z hz => ?_, fun z hz => ?_⟩
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
        obtain ⟨u, -, rfl⟩ := hz
        exact ⟨e, he, Or.inl (by rw [her]; simp)⟩
      · simp only [Option.map_some, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact ⟨e, he, Or.inl (by rw [her]; simp)⟩

theorem lookup_eq_find? {α β : Type} [DecidableEq α] [BEq α] [LawfulBEq α] (l : List (α × β))
    (a : α) : l.lookup a = (l.find? fun e => decide (e.1 = a)).map Prod.snd := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨k, b⟩ := e
    by_cases h : k = a
    · subst h
      simp [List.lookup]
    · have hb : (a == k) = false := by
        rw [beq_eq_false_iff_ne]; exact Ne.symm h
      simp [List.lookup, hb, h, ih]

theorem find?_congr_mem {α : Type} {p q : α → Bool} (l : List α) (h : ∀ a ∈ l, p a = q a) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.find?_cons, h a List.mem_cons_self]
    rw [ih fun b hb => h b (List.mem_cons_of_mem a hb)]

/-- **Off `MBad`, the simulator's step is the split step** (with the honest view). -/
theorem implView_agree (σ : List O) (s : S) (t : Op I K X) (st : St I O K X)
    (hst : ¬ MBad (P.rows s σ) st) :
    (implView P σ (P.view s σ) t).run st = (implSplit P σ s t).run st ∨
      ((∀ z ∈ support ((implView P σ (P.view s σ) t).run st), MBad (P.rows s σ) z.2) ∧
        ∀ z ∈ support ((implSplit P σ s t).run st), MBad (P.rows s σ) z.2) := by
  cases t with
  | pub t => exact ro_agree _ t st hst
  | msg => exact Or.inl rfl
  | leaf k x =>
    simp only [implView, implSplit, StateT.run]
    by_cases h1 : st.hist.length < P.cK k
    · simp [h1]
    · simp only [h1, ite_false]
      by_cases h2 : P.opened σ k x = true
      · simp only [h2, ite_true, Proto.view]
        exact ro_agree _ _ st hst
      · simp only [h2, Bool.false_eq_true, ite_false]
        set rows := P.rows s σ
        set r := rows k x
        cases hl : st.priv.lookup (k, x) with
        | some u =>
          -- the position has a private digest: off `MBad`, the union finds it
          left
          have hfind := hl
          rw [lookup_eq_find?] at hfind
          obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hfind
          obtain ⟨hemem, hek⟩ := find?_eq_some_mem he
          have hek : e.1 = (k, x) := by simpa using hek
          have hc : st.cache r = none := by
            by_contra hc
            exact hst ⟨e, hemem, Or.inl (by rw [hek]; exact Option.ne_none_iff_isSome.mp hc)⟩
          have hcongr : st.priv.find? (fun e => decide (rows e.1.1 e.1.2 = r)) =
              st.priv.find? (fun e => decide (e.1 = (k, x))) := by
            refine find?_congr_mem _ fun a ha => ?_
            by_cases hak : a.1 = (k, x)
            · simp [hak, r]
            · have : rows a.1.1 a.1.2 ≠ r := by
                intro hr
                exact hst ⟨e, hemem, Or.inr ⟨a, ha, by rw [hek]; exact hak,
                  by rw [hr, hek]⟩⟩
              simp [hak, this]
          have hu : unionLook rows st r = some e.2 := by
            simp only [unionLook, hc, hcongr, he, Option.map_some]
          have hp : hasPriv st (k, x) = true := by simp [hasPriv, hl]
          simp [hu, hp]
        | none =>
          have hp : hasPriv st (k, x) = false := by simp [hasPriv, hl]
          cases hu : unionLook rows st r with
          | none => left; simp [hu, hp]
          | some w =>
            right
            -- the row is answered: in the cache, or by another position's digest
            have hbad : ∀ u : O, MBad rows { st with priv := st.priv ++ [((k, x), u)] } := by
              intro u
              unfold unionLook at hu
              cases hc : st.cache r with
              | some w' =>
                exact ⟨((k, x), u), List.mem_append_right _ (List.mem_singleton_self _),
                  Or.inl (by simp [hc, r])⟩
              | none =>
                rw [hc] at hu
                obtain ⟨e, he, -⟩ := Option.map_eq_some_iff.mp hu
                obtain ⟨hemem, her⟩ := find?_eq_some_mem he
                have her : rows e.1.1 e.1.2 = r := by simpa using her
                have hne : e.1 ≠ (k, x) := by
                  intro h
                  have : st.priv.lookup (k, x) ≠ none := by
                    rw [lookup_eq_find?]
                    intro h0
                    rw [Option.map_eq_none_iff, List.find?_eq_none] at h0
                    exact h0 e hemem (by simp [h])
                  exact this hl
                exact ⟨((k, x), u), List.mem_append_right _ (List.mem_singleton_self _),
                  Or.inr ⟨e, List.mem_append_left _ hemem, hne, her⟩⟩
            refine ⟨fun z hz => ?_, fun z hz => ?_⟩
            · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
              obtain ⟨u, -, rfl⟩ := hz
              exact hbad u
            · simp only [hu, hp, support_pure, Set.mem_singleton_iff] at hz
              subst hz
              exact hbad w
  | chal t =>
    simp only [implView, implSplit, StateT.run]
    split_ifs
    · exact Or.inl rfl
    · exact ro_agree _ t st hst

/-- **Identical until `MBad`**: the honest-view simulator against the split prover. -/
theorem prEvent_view_le_split {α : Type} (σ : List O) (s : S)
    (oa : OracleComp (OpSpec I O M K X) α) (st : St I O K X) (p : α → Prop) :
    Pr{let z ← (simulateQ (implView P σ (P.view s σ)) oa).run st}[p z.1] ≤
      Pr{let z ← (simulateQ (implSplit P σ s) oa).run st}[p z.1] +
        Pr{let z ← (simulateQ (implView P σ (P.view s σ)) oa).run st}[MBad (P.rows s σ) z.2] := by
  have hagree := fun t st (hst : ¬ MBad (P.rows s σ) st) q =>
    agree_of_eq_or_bad (MBad (P.rows s σ)) _ _ (implView_agree P σ s t st hst) q
  have hmono₁ := fun t st (hst : MBad (P.rows s σ) st) z hz =>
    mBad_of_grows (P.rows s σ) (implView_grows P σ (P.view s σ) t st z hz) hst
  have hmono₂ := fun t st (hst : MBad (P.rows s σ) st) z hz =>
    mBad_of_grows (P.rows s σ) (implSplit_grows P σ s t st z hz) hst
  have h := Common.prEvent_run_le_add_bad (implView P σ (P.view s σ)) (implSplit P σ s)
    (MBad (P.rows s σ)) hagree hmono₁ hmono₂ oa st p
  rwa [← Common.prEvent_run_bad_eq (implView P σ (P.view s σ)) (implSplit P σ s)
    (MBad (P.rows s σ)) hagree hmono₁ hmono₂ oa st] at h

/-- **Identical until `MBad`**, the other way. -/
theorem prEvent_split_le_view {α : Type} (σ : List O) (s : S)
    (oa : OracleComp (OpSpec I O M K X) α) (st : St I O K X) (p : α → Prop) :
    Pr{let z ← (simulateQ (implSplit P σ s) oa).run st}[p z.1] ≤
      Pr{let z ← (simulateQ (implView P σ (P.view s σ)) oa).run st}[p z.1] +
        Pr{let z ← (simulateQ (implView P σ (P.view s σ)) oa).run st}[MBad (P.rows s σ) z.2] := by
  have hagree := fun t st (hst : ¬ MBad (P.rows s σ) st) q =>
    agree_of_eq_or_bad (MBad (P.rows s σ)) _ _ (implView_agree P σ s t st hst) q
  have hmono₁ := fun t st (hst : MBad (P.rows s σ) st) z hz =>
    mBad_of_grows (P.rows s σ) (implView_grows P σ (P.view s σ) t st z hz) hst
  have hmono₂ := fun t st (hst : MBad (P.rows s σ) st) z hz =>
    mBad_of_grows (P.rows s σ) (implSplit_grows P σ s t st z hz) hst
  exact Common.prEvent_run_le_add_bad (implSplit P σ s) (implView P σ (P.view s σ))
    (MBad (P.rows s σ)) (fun t st hst q => (hagree t st hst q).symm) hmono₂ hmono₁ oa st p

end QuotientZk
