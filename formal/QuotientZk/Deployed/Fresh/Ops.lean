-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Deployed.Fresh.Core

/-!
# Fresh Fiat–Shamir inputs: the skeleton's operations as triples

`Ext Φ st st'`: the run from `st` to `st'` kept the flag, extended the challenges, logged only new
inputs satisfying `Φ`, and kept every answer. `HistGrow c`: it appended `c` challenges (fewer once
there are `n`). The skeleton's operations (`hashH`, `perm`, `chalH`, `chalF`, `leafH`, `getMsg`)
as triples, and `List.mapM`.
-/

open OracleComp OracleSpec QuotientRpm
open scoped ENNReal

namespace QuotientZk.Deployed.Fresh

set_option linter.unusedSectionVars false

/-! ## Extensions of a state -/

/-- `st'` extends `st`: the same flag, the challenges extended, the new log entries satisfying `Φ`,
every answer kept. -/
structure Ext (Φ : Inp → Prop) (st st' : DSt) : Prop where
  fs : st'.fs = st.fs
  hist : ∃ e, st'.hist = st.hist ++ e
  log : ∃ new, st'.log = new ++ st.log ∧ ∀ y ∈ new, Φ y
  cache : ∀ y v, st.cache y = some v → st'.cache y = some v

namespace Ext

variable {Φ Ψ : Inp → Prop}

theorem refl (st : DSt) : Ext Φ st st :=
  ⟨rfl, ⟨[], by simp⟩, ⟨[], by simp, by simp⟩, fun _ _ h => h⟩

theorem trans {st st' st'' : DSt} (h₁ : Ext Φ st st') (h₂ : Ext Φ st' st'') : Ext Φ st st'' where
  fs := h₂.fs.trans h₁.fs
  hist := by
    obtain ⟨e₁, h1⟩ := h₁.hist
    obtain ⟨e₂, h2⟩ := h₂.hist
    exact ⟨e₁ ++ e₂, by rw [h2, h1, List.append_assoc]⟩
  log := by
    obtain ⟨n₁, h1, p1⟩ := h₁.log
    obtain ⟨n₂, h2, p2⟩ := h₂.log
    refine ⟨n₂ ++ n₁, by rw [h2, h1, List.append_assoc], fun y hy => ?_⟩
    rcases List.mem_append.mp hy with hy | hy
    · exact p2 y hy
    · exact p1 y hy
  cache y v h := h₂.cache y v (h₁.cache y v h)

theorem mono {st st' : DSt} (h : Ext Φ st st') (hΦ : ∀ y, Φ y → Ψ y) : Ext Ψ st st' :=
  ⟨h.fs, h.hist, by
    obtain ⟨n, h1, p1⟩ := h.log
    exact ⟨n, h1, fun y hy => hΦ y (p1 y hy)⟩, h.cache⟩

/-- A new input of the extension is a new log entry or an old input. -/
theorem mem_dom {K0 : List Inp} {st st' : DSt} (h : Ext Φ st st') {y : Inp}
    (hy : y ∈ dom K0 st') : y ∈ dom K0 st ∨ Φ y := by
  obtain ⟨n, h1, p1⟩ := h.log
  simp only [dom, h1, List.mem_append] at hy ⊢
  rcases hy with hy | (hy | hy)
  · exact Or.inl (Or.inl hy)
  · exact Or.inr (p1 y hy)
  · exact Or.inl (Or.inr hy)

/-- An invariant of the inputs, kept by the new ones. -/
theorem forall_dom {K0 : List Inp} {st st' : DSt} (h : Ext Φ st st') {R : Inp → Prop}
    (hR : ∀ y ∈ dom K0 st, R y) (hΦ : ∀ y, Φ y → R y) : ∀ y ∈ dom K0 st', R y := fun y hy =>
  (h.mem_dom hy).elim (hR y) (hΦ y)

theorem log_sub {K0 : List Inp} {st st' : DSt} (h : Ext Φ st st') {y : Inp} (hy : y ∈ dom K0 st) :
    y ∈ dom K0 st' := by
  obtain ⟨n, h1, -⟩ := h.log
  simp only [dom, h1, List.mem_append] at hy ⊢
  tauto

theorem of_addE {st : DSt} {t : Inp} (u : Out) (ht : st.cache t = none) (hΦ : Φ t) :
    Ext Φ st (addE st t u) where
  fs := rfl
  hist := ⟨[], by simp⟩
  log := ⟨[t], by simp, by simpa using hΦ⟩
  cache y v h := by
    rw [addE_cache]
    by_cases hy : y = t
    · subst hy; rw [ht] at h; exact absurd h (by simp)
    · simp [hy, h]

theorem of_addH {n : ℕ} {st : DSt} {t : Inp} (u : Out) (ht : st.cache t = none) (hΦ : Φ t) :
    Ext Φ st { addE st t u with hist := if st.hist.length < n then st.hist ++ [u] else st.hist } where
  fs := rfl
  hist := by
    split_ifs
    · exact ⟨_, rfl⟩
    · exact ⟨[], by simp⟩
  log := (of_addE (Φ := Φ) u ht hΦ).log
  cache := (of_addE (Φ := Φ) u ht hΦ).cache

end Ext

/-- `c` challenges appended (none past `n`). -/
def HistGrow (n c : ℕ) (st st' : DSt) : Prop := st'.hist.length = min (st.hist.length + c) n

theorem HistGrow.refl {n : ℕ} {st : DSt} (h : st.hist.length ≤ n) : HistGrow n 0 st st := by
  unfold HistGrow; omega

theorem HistGrow.trans {n c₁ c₂ : ℕ} {st st' st'' : DSt} (h₁ : HistGrow n c₁ st st')
    (h₂ : HistGrow n c₂ st' st'') : HistGrow n (c₁ + c₂) st st'' := by
  unfold HistGrow at *; omega

theorem HistGrow.of_eq {n c : ℕ} {st st' : DSt} (h : st'.hist = st.hist) (hn : st.hist.length ≤ n)
    (hc : c = 0) : HistGrow n c st st' := by
  unfold HistGrow; rw [h]; omega

/-- The challenges after a fresh Fiat–Shamir answer. -/
def addH (n : ℕ) (st : DSt) (t : Inp) (u : Out) : DSt :=
  { addE st t u with hist := if st.hist.length < n then st.hist ++ [u] else st.hist }

theorem histGrow_addH {n : ℕ} {st : DSt} (t : Inp) (u : Out) (hn : st.hist.length ≤ n) :
    HistGrow n 1 st (addH n st t u) := by
  unfold HistGrow addH
  split_ifs with h <;> simp <;> omega

@[simp] theorem addH_fs (n : ℕ) (st : DSt) (t : Inp) (u : Out) : (addH n st t u).fs = st.fs := rfl
@[simp] theorem addH_log (n : ℕ) (st : DSt) (t : Inp) (u : Out) :
    (addH n st t u).log = t :: st.log := rfl

theorem addH_cache (n : ℕ) (st : DSt) (t : Inp) (u : Out) (y : Inp) :
    (addH n st t u).cache y = if y = t then some u else st.cache y := addE_cache st t u y

theorem mem_dom_addH (K0 : List Inp) (n : ℕ) (st : DSt) (t : Inp) (u : Out) (y : Inp) :
    y ∈ dom K0 (addH n st t u) ↔ y = t ∨ y ∈ dom K0 st := mem_dom_addE K0 st t u y

/-- A digest the cache holds. -/
def CachedDig (st : DSt) (x : Bytes32) : Prop := ∃ y v, st.cache y = some v ∧ v.1 = x

theorem CachedDig.ext {Φ : Inp → Prop} {st st' : DSt} (h : Ext Φ st st') {x : Bytes32}
    (hx : CachedDig st x) : CachedDig st' x := by
  obtain ⟨y, v, h1, h2⟩ := hx
  exact ⟨y, v, h.cache y v h1, h2⟩

/-! ## The operations -/

section Ops

variable {S : Type} {P : Proto S Inp Out Msg Tbl Pos} {s : S} {cw : Fin 3 → Bytes32 → List UInt8}
  {K0 : List Inp}

/-- Keccak-256. -/
theorem trip_hashH (m : List UInt8) (post : Bytes32 → DSt → Prop) :
    Trip P s cw K0
      (fun st => (∀ v, st.cache (.inl m) = some v → post v.1 st) ∧
        (st.cache (.inl m) = none → ∀ u, NoHit K0 st (.inl m) u → post u.1 (addE st (.inl m) u)))
      (hashH m) post :=
  Trip.bind (trip_pub (.inl m) (fun a st => post a.1 st)) fun a => Trip.pure a.1 post

/-- The permutation. -/
theorem trip_perm (x : KSt) (post : KSt → DSt → Prop) :
    Trip P s cw K0
      (fun st => (∀ v, st.cache (.inr x) = some v → post v.2 st) ∧
        (st.cache (.inr x) = none → ∀ u, NoHit K0 st (.inr x) u → post u.2 (addE st (.inr x) u)))
      (perm x) post :=
  Trip.bind (trip_pub (.inr x) (fun a st => post a.2 st)) fun a => Trip.pure a.2 post

/-- Keccak-256 of an input the oracle does not hold: a fresh answer. -/
theorem trip_hashH_fresh (m : List UInt8) (post : Bytes32 → DSt → Prop) :
    Trip P s cw K0
      (fun st => (.inl m : Inp) ∉ dom K0 st ∧
        ∀ u, NoHit K0 st (.inl m) u → post u.1 (addE st (.inl m) u))
      (hashH m) post :=
  Trip.ginv <| (trip_hashH m post).mono (fun st ⟨hg, hm, hp⟩ =>
    ⟨fun v hv => by rw [hg.cache_none hm] at hv; exact absurd hv (by simp), fun _ => hp⟩)
    (fun _ _ h => h)

/-- The permutation of an input the oracle does not hold: a fresh answer. -/
theorem trip_perm_fresh (x : KSt) (post : KSt → DSt → Prop) :
    Trip P s cw K0
      (fun st => (.inr x : Inp) ∉ dom K0 st ∧
        ∀ u, NoHit K0 st (.inr x) u → post u.2 (addE st (.inr x) u))
      (perm x) post :=
  Trip.ginv <| (trip_perm x post).mono (fun st ⟨hg, hm, hp⟩ =>
    ⟨fun v hv => by rw [hg.cache_none hm] at hv; exact absurd hv (by simp), fun _ => hp⟩)
    (fun _ _ h => h)

/-- A Fiat–Shamir Keccak-256 query. -/
theorem trip_chalH (m : List UInt8) (post : Bytes32 → DSt → Prop) :
    Trip P s cw K0
      (fun st => (.inl m : Inp) ∉ dom K0 st ∧ ∀ u, NoHit K0 st (.inl m) u →
        (Inc P.n (.chal (.inl m)) st → NoHitC cw K0 st (.inl m) u) →
        post u.1 (addH P.n st (.inl m) u))
      (chalH m) post :=
  Trip.bind (trip_chal (.inl m) (fun a st => post a.1 st)) fun a => Trip.pure a.1 post

/-- A Fiat–Shamir permutation. -/
theorem trip_chalF (x : KSt) (post : KSt → DSt → Prop) :
    Trip P s cw K0
      (fun st => (.inr x : Inp) ∉ dom K0 st ∧ ∀ u, NoHit K0 st (.inr x) u →
        post u.2 (addH P.n st (.inr x) u))
      (chalF x) post :=
  (Trip.bind (trip_chal (.inr x) (fun a st => post a.2 st)) fun a => Trip.pure a.2 post).mono
    (fun st h => ⟨h.1, fun u hu _ => h.2 u hu⟩) (fun _ _ h => h)

/-- The next message. -/
theorem trip_getMsg (post : Msg → DSt → Prop) :
    Trip P s cw K0 (fun st => post (P.msgFn s st.hist) st) getMsg post :=
  trip_msg post

/-- A secret leaf. -/
theorem trip_leafH (k : Tbl) (x : ℕ) (post : Bytes32 → DSt → Prop) :
    Trip P s cw K0
      (fun st =>
        let r := P.rowFn s (st.hist.take (P.cK k)) k ⟨x % 2 ^ 23, Nat.mod_lt _ (by positivity)⟩
        (st.hist.length < P.cK k → post (default : Out).1 st) ∧
        (P.cK k ≤ st.hist.length →
          (∀ v, st.cache r = some v → post v.1 st) ∧
          (st.cache r = none → ∀ u, NoHit K0 st r u → post u.1 (addE st r u))))
      (leafH k x) post :=
  Trip.bind (trip_leaf k _ (fun a st => post a.1 st)) fun a => Trip.pure a.1 post

/-! ## Lists -/

/-- `List.mapM`, with an invariant of the outputs so far. -/
theorem trip_mapM {α β : Type} (f : α → OracleComp DSpec β) (I : List β → DSt → Prop)
    (h : ∀ a acc, Trip P s cw K0 (I acc) (f a) (fun b st => I (acc ++ [b]) st)) :
    ∀ (l : List α) (acc : List β),
      Trip P s cw K0 (I acc) (l.mapM f) (fun bs st => I (acc ++ bs) st ∧ bs.length = l.length)
  | [], acc => by
    simp only [List.mapM_nil]
    exact (Trip.pure [] _).mono (fun st h => by simpa using h) (fun _ _ h => h)
  | a :: l, acc => by
    rw [List.mapM_cons]
    refine Trip.bind (h a acc) fun b => Trip.bind (trip_mapM f I h l (acc ++ [b])) fun bs => ?_
    exact (Trip.pure (b :: bs) _).mono (fun st hst => by simpa using hst) (fun _ _ h => h)

end Ops

end QuotientZk.Deployed.Fresh
