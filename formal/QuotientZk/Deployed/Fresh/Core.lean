-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): `common`'s run invariants and state projection (`Common.inv_of_mem_support_run`,
-- `Common.map_run_simulateQ_evalDistEq_of_inv`).
import QuotientZk.Deployed.Bound
import QuotientZk.Rom.MerkleBound

/-!
# Fresh Fiat–Shamir inputs: the bookkeeping

The real prover (`implReal`) raises its flag `fs` when a Fiat–Shamir query finds its input already
answered. To bound that, the run is tracked by `implB`: the same steps, and a second flag, *bad*,
raised when a fresh answer `u` (drawn for an input `t` the oracle did not hold) lands where it
should not (`Hit`): its digest is the first 32 bytes of an input the oracle holds, or their last
bytes are its root words; its digest is another answer's; its capacity is an input's or zero; the
seed state of its digest is an input; and, at the reduction's fourth and fifth challenges only
(`Inc`), one of the openings' claim windows (`cw`) read off it is the window of an input. The inputs
the oracle holds are the initial ones `K0` and the logged ones (`dom`).

Off *bad*, a run keeps the global invariant `GInv` (every answered input is in `dom`; logged
answers have digests no other answer has, and seed states not among the initial inputs), and
`Trip pre oa post` is a Hoare triple for the runs that end off *bad*. The primitive triples
(`trip_query_pub`, `trip_query_chal`, `trip_query_leaf`, `trip_query_msg`) give each operation's
effect, with `NoHit` for a fresh answer.
-/

open OracleComp OracleSpec QuotientRpm
open scoped ENNReal

namespace QuotientZk.Deployed.Fresh

set_option linter.unusedSectionVars false

/-- The states of the deployed prover's runs. -/
abbrev DSt := St Inp Out Tbl Pos

/-! ## Windows -/

/-- A state's capacity: lanes `16 .. 25`. -/
def capOf (w : KSt) : List UInt64 := w.toList.drop 16

/-- The zero capacity (the seed's input). -/
def zeroCap : List UInt64 := List.replicate 9 0

/-- The inputs the oracle holds: the initial ones, then the logged ones. -/
def dom (K0 : List Inp) (st : DSt) : List Inp := K0 ++ st.log

/-- A fresh answer `u` for the input `t` lands nowhere it should not. -/
structure NoHit (K0 : List Inp) (st : DSt) (t : Inp) (u : Out) : Prop where
  left : ∀ y, y = t ∨ y ∈ dom K0 st → ∀ b, y = .inl b → b.take 32 ≠ u.1.toList
  root : ∀ y, y = t ∨ y ∈ dom K0 st → ∀ b, y = .inl b → b.drop 32 ≠ rootWords u.1
  dig : ∀ y ∈ dom K0 st, ∀ v, st.cache y = some v → v.1 ≠ u.1
  cap : ∀ y, y = t ∨ y ∈ dom K0 st → ∀ w, y = .inr w → capOf w ≠ capOf u.2
  capz : capOf u.2 ≠ zeroCap
  seed : ∀ y, y = t ∨ y ∈ dom K0 st → y ≠ .inr (seedInput u.1)

/-- At the claims' challenges: no input holds a claim window read off `u`. -/
def NoHitC (cw : Fin 3 → Bytes32 → List UInt8) (K0 : List Inp) (st : DSt) (t : Inp) (u : Out) :
    Prop :=
  ∀ y, y = t ∨ y ∈ dom K0 st → ∀ b, y = .inl b → ∀ j, (b.drop 76).take 24 ≠ cw j u.1

/-- The steps that draw the reduction's fourth and fifth challenges. -/
def Inc (n : ℕ) (op : Op Inp Tbl Pos) (st : DSt) : Prop :=
  (∃ t, op = .chal t) ∧ (st.hist.length = 3 ∨ st.hist.length = 4) ∧ st.hist.length < n

/-- A fresh answer that lands where it should not. -/
def Hit (n : ℕ) (cw : Fin 3 → Bytes32 → List UInt8) (K0 : List Inp) (op : Op Inp Tbl Pos)
    (st : DSt) (t : Inp) (u : Out) : Prop :=
  ¬ NoHit K0 st t u ∨ (Inc n op st ∧ ¬ NoHitC cw K0 st t u)

/-- A step that logged a fresh answer that hits. -/
def StepHit (n : ℕ) (cw : Fin 3 → Bytes32 → List UInt8) (K0 : List Inp) (op : Op Inp Tbl Pos)
    (st st' : DSt) : Prop :=
  ∃ t u, st'.log = t :: st.log ∧ st'.cache t = some u ∧ Hit n cw K0 op st t u

/-- A fresh answer for `t`: in the cache and the log. -/
def addE (st : DSt) (t : Inp) (u : Out) : DSt :=
  { st with cache := st.cache.cacheQuery t u, log := t :: st.log }

@[simp] theorem addE_fs (st : DSt) (t : Inp) (u : Out) : (addE st t u).fs = st.fs := rfl
@[simp] theorem addE_hist (st : DSt) (t : Inp) (u : Out) : (addE st t u).hist = st.hist := rfl
@[simp] theorem addE_log (st : DSt) (t : Inp) (u : Out) : (addE st t u).log = t :: st.log := rfl

theorem addE_cache (st : DSt) (t : Inp) (u : Out) (y : Inp) :
    (addE st t u).cache y = if y = t then some u else st.cache y := by
  simp only [addE, QueryCache.cacheQuery]
  by_cases h : y = t
  · subst h; simp
  · simp [h]

theorem mem_dom_addE (K0 : List Inp) (st : DSt) (t : Inp) (u : Out) (y : Inp) :
    y ∈ dom K0 (addE st t u) ↔ y = t ∨ y ∈ dom K0 st := by
  simp only [dom, addE_log, List.mem_append, List.mem_cons]
  tauto

/-! ## The tracked implementation -/

section Impl

open Classical

/-- **The real prover, tracked**: `implReal`'s step, and the flag *bad* raised by a fresh answer
that hits. -/
noncomputable def implB {S : Type} (P : Proto S Inp Out Msg Tbl Pos) (s : S)
    (cw : Fin 3 → Bytes32 → List UInt8) (K0 : List Inp) :
    QueryImpl DSpec (StateT (DSt × Bool) ProbComp) := fun op b => do
  let z ← (implReal P s op).run b.1
  return (z.1, (z.2, b.2 || decide (StepHit P.n cw K0 op b.1 z.2)))

variable {S : Type} (P : Proto S Inp Out Msg Tbl Pos) (s : S) (cw : Fin 3 → Bytes32 → List UInt8)
  (K0 : List Inp)

theorem implB_run (op : Op Inp Tbl Pos) (b : DSt × Bool) :
    (implB P s cw K0 op).run b = (fun z => (z.1, (z.2, b.2 || decide (StepHit P.n cw K0 op b.1 z.2))))
      <$> (implReal P s op).run b.1 := by
  classical
  simp [implB, StateT.run, map_eq_bind_pure_comp]

/-- The tracked steps project to the real ones. -/
theorem implB_proj (op : Op Inp Tbl Pos) (b : DSt × Bool) :
    Prod.map id Prod.fst <$> (implB P s cw K0 op).run b = (implReal P s op).run b.1 := by
  rw [implB_run, Functor.map_map]
  simp

/-- **The tracked run is the real run**, once *bad* is forgotten. -/
theorem run_proj {α : Type} (oa : OracleComp DSpec α) (st : DSt) (bad : Bool) :
    Prod.map id Prod.fst <$> (simulateQ (implB P s cw K0) oa).run (st, bad) =ᵈ
      (simulateQ (implReal P s) oa).run st :=
  Common.map_run_simulateQ_evalDistEq_of_inv (implB P s cw K0) (implReal P s) (fun _ => True)
    Prod.fst (fun _ _ _ _ _ => trivial)
    (fun op b _ => by rw [implB_proj]) oa (st, bad) trivial

/-- *bad* never goes down. -/
theorem bad_mono {α : Type} (oa : OracleComp DSpec α) (b : DSt × Bool) (hb : b.2 = true) :
    ∀ z ∈ support ((simulateQ (implB P s cw K0) oa).run b), z.2.2 = true :=
  Common.inv_of_mem_support_run (implB P s cw K0) (fun b => b.2 = true)
    (fun op b hb z hz => by
      rw [implB_run] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨y, -, rfl⟩ := hz
      simp [hb]) oa hb

/-- Off *bad*, a step logged no fresh answer that hits. -/
theorem step_noHit (op : Op Inp Tbl Pos) (b : DSt × Bool)
    (z : DSpec.Range op × (DSt × Bool)) (hz : z ∈ support ((implB P s cw K0 op).run b))
    (hbad : z.2.2 = false) :
    b.2 = false ∧ (z.1, z.2.1) ∈ support ((implReal P s op).run b.1) ∧
      ¬ StepHit P.n cw K0 op b.1 z.2.1 := by
  rw [implB_run] at hz
  simp only [support_map, Set.mem_image] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hbad
  exact ⟨hbad.1, hy, hbad.2⟩

end Impl

/-! ## The global invariant -/

/-- **What every run keeps off *bad***: the cache answers only inputs of `dom`; a logged answer's
digest is no other answer's, and its seed state is not an initial input; at most `n` challenges. -/
structure GInv (n : ℕ) (K0 : List Inp) (st : DSt) : Prop where
  dom_of : ∀ y, (st.cache y).isSome → y ∈ dom K0 st
  dig : ∀ x ∈ st.log, ∀ y, x ≠ y → ∀ v w, st.cache x = some v → st.cache y = some w → v.1 ≠ w.1
  seed : ∀ x ∈ st.log, ∀ v, st.cache x = some v → (.inr (seedInput v.1) : Inp) ∉ K0
  hist : st.hist.length ≤ n

theorem GInv.cache_none {n : ℕ} {K0 : List Inp} {st : DSt} (h : GInv n K0 st) {t : Inp}
    (ht : t ∉ dom K0 st) : st.cache t = none := by
  cases hc : st.cache t with
  | none => rfl
  | some v => exact absurd (h.dom_of t (by simp [hc])) ht

theorem GInv.addE {n : ℕ} {K0 : List Inp} {st : DSt} (h : GInv n K0 st) {t : Inp} {u : Out}
    (ht : st.cache t = none) (hu : NoHit K0 st t u) : GInv n K0 (addE st t u) where
  dom_of y hy := by
    rw [mem_dom_addE]
    rw [addE_cache] at hy
    by_cases hyt : y = t
    · exact Or.inl hyt
    · simp only [hyt, ite_false] at hy
      exact Or.inr (h.dom_of y hy)
  dig x hx y hxy v w hv hw := by
    rw [addE_cache] at hv hw
    simp only [addE_log, List.mem_cons] at hx
    by_cases hxt : x = t
    · subst hxt
      simp only [ite_true, Option.some.injEq] at hv
      subst hv
      have hyt : y ≠ x := fun e => hxy e.symm
      simp only [hyt, ite_false] at hw
      exact fun e => hu.dig y (h.dom_of y (by simp [hw])) w hw e.symm
    · simp only [hxt, ite_false] at hv
      rcases hx with hx | hx
      · exact absurd hx hxt
      by_cases hyt : y = t
      · subst hyt
        simp only [ite_true, Option.some.injEq] at hw
        subst hw
        exact hu.dig x (List.mem_append_right _ hx) v hv
      · simp only [hyt, ite_false] at hw
        exact h.dig x hx y hxy v w hv hw
  seed x hx v hv := by
    rw [addE_cache] at hv
    simp only [addE_log, List.mem_cons] at hx
    by_cases hxt : x = t
    · subst hxt
      simp only [ite_true, Option.some.injEq] at hv
      subst hv
      exact fun hK => hu.seed _ (Or.inr (List.mem_append_left _ hK)) rfl
    · simp only [hxt, ite_false] at hv
      rcases hx with hx | hx
      · exact absurd hx hxt
      · exact h.seed x hx v hv
  hist := h.hist

theorem GInv.init (n : ℕ) (c₀ : List (Inp × Out)) :
    GInv n (c₀.map Prod.fst) (St.init (K := Tbl) (X := Pos) c₀) where
  dom_of y hy := by
    simp only [dom, St.init, List.append_nil]
    exact init_cache_isSome c₀ y hy
  dig x hx := by simp [St.init] at hx
  seed x hx := by simp [St.init] at hx
  hist := by simp [St.init]

section Steps

variable {S : Type} (P : Proto S Inp Out Msg Tbl Pos) (s : S) (cw : Fin 3 → Bytes32 → List UInt8)
  (K0 : List Inp)

/-- `roStep`'s outcomes. -/
theorem roStep_cases (t : Inp) (st : DSt) (z : Out × DSt)
    (hz : z ∈ support (roStep (K := Tbl) (X := Pos) t st)) :
    (st.cache t = some z.1 ∧ z.2 = st) ∨ (st.cache t = none ∧ z.2 = addE st t z.1) := by
  unfold roStep at hz
  cases h : st.cache t with
  | some u =>
    simp only [h, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact Or.inl ⟨rfl, rfl⟩
  | none =>
    simp only [h, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact Or.inr ⟨rfl, rfl⟩

theorem roStep_cases' (t : Inp) (st : DSt) (a : Out) (st' : DSt)
    (hz : (a, st') ∈ support (roStep (K := Tbl) (X := Pos) t st)) :
    (st.cache t = some a ∧ st' = st) ∨ (st.cache t = none ∧ st' = addE st t a) :=
  roStep_cases t st (a, st') hz

theorem stepHit_self (n : ℕ) (op : Op Inp Tbl Pos) (st : DSt) : ¬ StepHit n cw K0 op st st := by
  rintro ⟨t, u, h, -⟩
  have := congrArg List.length h
  simp at this

theorem stepHit_addE (n : ℕ) (op : Op Inp Tbl Pos) (st st' : DSt) (t : Inp) (u : Out)
    (h : ¬ StepHit n cw K0 op st st') (hst : st'.log = t :: st.log) (hc : st'.cache t = some u) :
    ¬ Hit n cw K0 op st t u := fun hh => h ⟨t, u, hst, hc, hh⟩

/-- The real step's outcomes: a hit of the cache (the state unchanged, or for a Fiat–Shamir query
the challenge appended and the flag raised), or a fresh answer (logged, appended for a challenge). -/
theorem implReal_cases (op : Op Inp Tbl Pos) (st : DSt) (a : DSpec.Range op) (st' : DSt)
    (hz : (a, st') ∈ support ((implReal P s op).run st)) :
    match op, a with
    | .pub t, a => (st.cache t = some a ∧ st' = st) ∨ (st.cache t = none ∧ st' = addE st t a)
    | .msg, a => a = P.msgFn s st.hist ∧ st' = st
    | .leaf k x, a =>
        (st.hist.length < P.cK k ∧ a = default ∧ st' = st) ∨
        (P.cK k ≤ st.hist.length ∧
          ((st.cache (P.rowFn s (st.hist.take (P.cK k)) k x) = some a ∧ st' = st) ∨
           (st.cache (P.rowFn s (st.hist.take (P.cK k)) k x) = none ∧
             st' = addE st (P.rowFn s (st.hist.take (P.cK k)) k x) a)))
    | .chal t, a =>
        (st.hist.length < P.n ∧
          ((st.cache t = some a ∧ st' = { st with hist := st.hist ++ [a], fs := true }) ∨
           (st.cache t = none ∧ st' = { addE st t a with hist := st.hist ++ [a] }))) ∨
        (P.n ≤ st.hist.length ∧
          ((st.cache t = some a ∧ st' = st) ∨ (st.cache t = none ∧ st' = addE st t a))) := by
  cases op with
  | pub t => exact roStep_cases' t st a st' hz
  | msg =>
    simp only [implReal, StateT.run, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hz
    exact hz
  | leaf k x =>
    simp only [implReal, StateT.run] at hz
    split_ifs at hz with h
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hz
      exact Or.inl ⟨h, hz⟩
    · exact Or.inr ⟨by omega, roStep_cases' _ st a st' hz⟩
  | chal t =>
    simp only [implReal, StateT.run] at hz
    split_ifs at hz with h
    · left
      refine ⟨h, ?_⟩
      cases hc : st.cache t with
      | some u =>
        simp only [hc, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hz
        obtain ⟨rfl, rfl⟩ := hz
        exact Or.inl ⟨rfl, rfl⟩
      | none =>
        simp only [hc, mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hz
        obtain ⟨u, -, rfl, rfl⟩ := hz
        exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inr ⟨by omega, roStep_cases' t st a st' hz⟩

/-- Off *bad*, a logged answer does not hit. -/
theorem noHit_of_step (n : ℕ) (op : Op Inp Tbl Pos) (st st' : DSt) (t : Inp) (u : Out)
    (h : ¬ StepHit n cw K0 op st st') (hst : st'.log = t :: st.log) (hc : st'.cache t = some u) :
    NoHit K0 st t u ∧ (Inc n op st → NoHitC cw K0 st t u) := by
  have := stepHit_addE cw K0 n op st st' t u h hst hc
  unfold Hit at this
  push Not at this
  exact ⟨this.1, this.2⟩

/-- **The global invariant is kept off *bad*.** -/
theorem ginv_step (op : Op Inp Tbl Pos) (b : DSt × Bool) (hb : GInv P.n K0 b.1)
    (z : DSpec.Range op × (DSt × Bool)) (hz : z ∈ support ((implB P s cw K0 op).run b))
    (hbad : z.2.2 = false) : GInv P.n K0 z.2.1 := by
  obtain ⟨-, hz', hnh⟩ := step_noHit P s cw K0 op b z hz hbad
  obtain ⟨z1, st', bd⟩ := z
  have hc := implReal_cases P s op b.1 z1 st' hz'
  dsimp only at hnh ⊢
  cases op with
  | pub t =>
    rcases hc with ⟨-, he⟩ | ⟨ht, he⟩
    · rw [he]; exact hb
    · subst he
      exact hb.addE ht (noHit_of_step cw K0 _ _ _ _ t z1 hnh rfl (by simp [addE_cache])).1
  | msg => rw [hc.2]; exact hb
  | leaf k x =>
    rcases hc with ⟨-, -, he⟩ | ⟨-, ⟨-, he⟩ | ⟨ht, he⟩⟩
    · rw [he]; exact hb
    · rw [he]; exact hb
    · subst he
      exact hb.addE ht (noHit_of_step cw K0 _ _ _ _ _ z1 hnh rfl (by simp [addE_cache])).1
  | chal t =>
    rcases hc with ⟨hn, ⟨-, he⟩ | ⟨ht, he⟩⟩ | ⟨-, ⟨-, he⟩ | ⟨ht, he⟩⟩
    · subst he
      exact { dom_of := hb.dom_of, dig := hb.dig, seed := hb.seed,
              hist := by simp; omega }
    · subst he
      have g := hb.addE ht (noHit_of_step cw K0 _ _ _ _ t z1 hnh rfl (by simp [addE_cache])).1
      exact { dom_of := g.dom_of, dig := g.dig, seed := g.seed, hist := by simp; omega }
    · rw [he]; exact hb
    · subst he
      exact hb.addE ht (noHit_of_step cw K0 _ _ _ _ t z1 hnh rfl (by simp [addE_cache])).1

/-- The global invariant along a run that ends off *bad*. -/
theorem ginv_run {α : Type} (oa : OracleComp DSpec α) :
    ∀ b : DSt × Bool, GInv P.n K0 b.1 →
      ∀ z ∈ support ((simulateQ (implB P s cw K0) oa).run b), z.2.2 = false → GInv P.n K0 z.2.1 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro b hb z hz _
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hb
  | query_bind t k ih =>
    intro b hb z hz hbad
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    have hy2 : y.2.2 = false := by
      by_contra h
      have := bad_mono P s cw K0 (k y.1) y.2 (by simpa using h) z hz
      rw [hbad] at this; exact Bool.false_ne_true this
    exact ih y.1 y.2 (ginv_step P s cw K0 t b hb y hy hy2) z hz hbad

end Steps

/-! ## Hoare triples off *bad* -/

section Triples

variable {S : Type} (P : Proto S Inp Out Msg Tbl Pos) (s : S) (cw : Fin 3 → Bytes32 → List UInt8)
  (K0 : List Inp)

/-- **A triple**: from a state of the invariant satisfying `pre`, every run of `oa` that ends off
*bad* ends in `post`. -/
def Trip {α : Type} (pre : DSt → Prop) (oa : OracleComp DSpec α) (post : α → DSt → Prop) : Prop :=
  ∀ st, GInv P.n K0 st → pre st →
    ∀ z ∈ support ((simulateQ (implB P s cw K0) oa).run (st, false)), z.2.2 = false →
      post z.1 z.2.1

variable {P s cw K0}

theorem Trip.bind {α β : Type} {pre : DSt → Prop} {oa : OracleComp DSpec α}
    {mid : α → DSt → Prop} {ob : α → OracleComp DSpec β} {post : β → DSt → Prop}
    (h1 : Trip P s cw K0 pre oa mid) (h2 : ∀ a, Trip P s cw K0 (mid a) (ob a) post) :
    Trip P s cw K0 pre (oa >>= ob) post := by
  intro st hg hpre z hz hbad
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  have hy2 : y.2.2 = false := by
    by_contra h
    have := bad_mono P s cw K0 (ob y.1) y.2 (by simpa using h) z hz
    rw [hbad] at this; exact Bool.false_ne_true this
  have hy' : y.2 = (y.2.1, false) := Prod.ext rfl hy2
  rw [hy'] at hz
  exact h2 y.1 y.2.1 (ginv_run P s cw K0 oa (st, false) hg y hy hy2) (h1 st hg hpre y hy hy2) z hz hbad

theorem Trip.pure {α : Type} (a : α) (post : α → DSt → Prop) :
    Trip P s cw K0 (post a) (pure a) post := by
  intro st _ hpre z hz _
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz; exact hpre

theorem Trip.mono {α : Type} {pre pre' : DSt → Prop} {oa : OracleComp DSpec α}
    {post post' : α → DSt → Prop} (h : Trip P s cw K0 pre oa post)
    (hpre : ∀ st, pre' st → pre st) (hpost : ∀ a st, post a st → post' a st) :
    Trip P s cw K0 pre' oa post' :=
  fun st hg hp z hz hbad => hpost _ _ (h st hg (hpre st hp) z hz hbad)

/-- A triple with the precondition's state named. -/
theorem Trip.intro {α : Type} {pre : DSt → Prop} {oa : OracleComp DSpec α}
    {post : α → DSt → Prop} (h : ∀ st₀, pre st₀ → Trip P s cw K0 (fun st => st = st₀) oa post) :
    Trip P s cw K0 pre oa post :=
  fun st hg hp z hz hbad => h st hp st hg rfl z hz hbad

/-- The invariant may be assumed in the precondition. -/
theorem Trip.ginv {α : Type} {pre : DSt → Prop} {oa : OracleComp DSpec α}
    {post : α → DSt → Prop} (h : Trip P s cw K0 (fun st => GInv P.n K0 st ∧ pre st) oa post) :
    Trip P s cw K0 pre oa post :=
  fun st hg hp z hz hbad => h st hg ⟨hg, hp⟩ z hz hbad

/-- The invariant holds after. -/
theorem Trip.post_ginv {α : Type} {pre : DSt → Prop} {oa : OracleComp DSpec α}
    {post : α → DSt → Prop} (h : Trip P s cw K0 pre oa post) :
    Trip P s cw K0 pre oa (fun a st => GInv P.n K0 st ∧ post a st) :=
  fun st hg hp z hz hbad => ⟨ginv_run P s cw K0 oa (st, false) hg z hz hbad, h st hg hp z hz hbad⟩

/-- The single step, as a triple. -/
theorem trip_query (op : Op Inp Tbl Pos) (pre : DSt → Prop) (post : DSpec.Range op → DSt → Prop)
    (h : ∀ st, GInv P.n K0 st → pre st → ∀ z ∈ support ((implReal P s op).run st),
      ¬ StepHit P.n cw K0 op st z.2 → post z.1 z.2) :
    Trip P s cw K0 pre (liftM (DSpec.query op)) post := by
  intro st hg hpre z hz hbad
  simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map] at hz
  obtain ⟨-, hz', hnh⟩ := step_noHit P s cw K0 op (st, false) z hz hbad
  exact h st hg hpre (z.1, z.2.1) hz' hnh

/-- **A public query** (`pub t`): a hit of the cache, or a fresh answer that does not hit. -/
theorem trip_pub (t : Inp) (post : Out → DSt → Prop) :
    Trip P s cw K0
      (fun st => (∀ v, st.cache t = some v → post v st) ∧
        (st.cache t = none → ∀ u, NoHit K0 st t u → post u (addE st t u)))
      (liftM (DSpec.query (.pub t))) post := by
  refine trip_query _ _ _ fun st _ hpre z hz hnh => ?_
  rcases roStep_cases t st z hz with ⟨hc, he⟩ | ⟨hc, he⟩
  · rw [he]; exact hpre.1 _ hc
  · have := noHit_of_step cw K0 P.n _ st z.2 t z.1 hnh (by rw [he]; rfl)
      (by rw [he, addE_cache]; simp)
    rw [he]; exact hpre.2 hc _ this.1

/-- **A Fiat–Shamir query whose input the oracle does not hold**: the flag stays down, the answer
is fresh and does not hit (nor, at the claims' challenges, do its claim windows), and it is
appended to the challenges if there are fewer than `n`. -/
theorem trip_chal (t : Inp) (post : Out → DSt → Prop) :
    Trip P s cw K0
      (fun st => t ∉ dom K0 st ∧ ∀ u, NoHit K0 st t u → (Inc P.n (.chal t) st → NoHitC cw K0 st t u) →
        post u { addE st t u with
          hist := if st.hist.length < P.n then st.hist ++ [u] else st.hist })
      (liftM (DSpec.query (.chal t))) post := by
  refine trip_query _ _ _ fun st hg hpre z hz hnh => ?_
  have hc0 := hg.cache_none hpre.1
  have hz' := implReal_cases P s (.chal t) st z.1 z.2 hz
  simp only at hz'
  rcases hz' with ⟨hn, ⟨hc, -⟩ | ⟨-, he⟩⟩ | ⟨hn, ⟨hc, -⟩ | ⟨-, he⟩⟩
  · rw [hc0] at hc; exact absurd hc (by simp)
  · have := noHit_of_step cw K0 P.n _ st z.2 t z.1 hnh (by rw [he]; rfl)
      (by rw [he]; simp [addE_cache])
    have hp := hpre.2 z.1 this.1 this.2
    simp only [hn, ite_true] at hp
    rw [he]; exact hp
  · rw [hc0] at hc; exact absurd hc (by simp)
  · have := noHit_of_step cw K0 P.n _ st z.2 t z.1 hnh (by rw [he]; rfl)
      (by rw [he]; simp [addE_cache])
    have hp := hpre.2 z.1 this.1 this.2
    simp only [show ¬ st.hist.length < P.n by omega, ite_false] at hp
    rw [he]; exact hp

/-- **A secret leaf**: before its challenges, the default and no query; after, a public query at
its row. -/
theorem trip_leaf (k : Tbl) (x : Pos) (post : Out → DSt → Prop) :
    Trip P s cw K0
      (fun st => (st.hist.length < P.cK k → post default st) ∧
        (P.cK k ≤ st.hist.length →
          (∀ v, st.cache (P.rowFn s (st.hist.take (P.cK k)) k x) = some v → post v st) ∧
          (st.cache (P.rowFn s (st.hist.take (P.cK k)) k x) = none → ∀ u,
            NoHit K0 st (P.rowFn s (st.hist.take (P.cK k)) k x) u →
            post u (addE st (P.rowFn s (st.hist.take (P.cK k)) k x) u))))
      (liftM (DSpec.query (.leaf k x))) post := by
  refine trip_query _ _ _ fun st _ hpre z hz hnh => ?_
  have hz' := implReal_cases P s (.leaf k x) st z.1 z.2 hz
  simp only at hz'
  rcases hz' with ⟨h, h1, he⟩ | ⟨h, ⟨hc, he⟩ | ⟨hc, he⟩⟩
  · rw [he, h1]; exact hpre.1 h
  · rw [he]; exact (hpre.2 h).1 _ hc
  · have := noHit_of_step cw K0 P.n _ st z.2 _ z.1 hnh (by rw [he]; rfl)
      (by rw [he, addE_cache]; simp)
    rw [he]; exact (hpre.2 h).2 hc _ this.1

/-- **The next message**: no query. -/
theorem trip_msg (post : Msg → DSt → Prop) :
    Trip P s cw K0 (fun st => post (P.msgFn s st.hist) st) (liftM (DSpec.query .msg)) post := by
  refine trip_query _ _ _ fun st _ hpre z hz _ => ?_
  have hz' := implReal_cases P s .msg st z.1 z.2 hz
  simp only at hz'
  rw [hz'.1, hz'.2]; exact hpre

end Triples

end QuotientZk.Deployed.Fresh
