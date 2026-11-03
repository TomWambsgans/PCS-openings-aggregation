-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.Arith

/-!
# Pure runs of programs: a Hoare judgment for Flock's pure parts

`PH p st Q`: recording the program `p` from `st` is a pure step (`PStep`), and its output satisfies `Q` in the state it
ends in. The rules: `PH.ret`, `PH.bind'`, `PH.mono`; the arithmetic operations (`PH.add`, `PH.mul`, `PH.const`,
`PH.zero`, `PH.one`, `PH.square`); and the loops (`PH.forIn_list`, `PH.forIn_range` with an index invariant;
`PH.forIn_rel`, `PH.forIn_rel_range` against an `Id` loop of `UniStatement`, step for step).

Arrays of nodes against arrays of `E` (`RpA`: the same size, entry `i` a node worth entry `i`), and the transport of
the representations along a pure step (`Rp.pgrow`, `RpA.pgrow`, `RpL.pgrow`; the tactic `grow_all`).
-/

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

/-- **A pure run**: `p` recorded from `st` is a pure step, its output `Q` in the state it ends in. -/
def PH {α : Type} (p : Prog α) (st : RecState) (Q : RecState → α → Prop) : Prop :=
  PStep st (p.record st).2 ∧ Q (p.record st).2 (p.record st).1

theorem PH.ret {α : Type} {a : α} {st : RecState} {Q : RecState → α → Prop} (hg : Good st) (h : Q st a) :
    PH (pure a) st Q := ⟨PStep.refl st hg, h⟩

theorem PH.bind' {α β : Type} {p : Prog α} {k : α → Prog β} {st : RecState} {Q : RecState → α → Prop}
    {R : RecState → β → Prop} (hp : PH p st Q) (hk : ∀ st' a, PStep st st' → Q st' a → PH (k a) st' R) :
    PH (p >>= k) st R := by
  obtain ⟨h1, h2⟩ := hk _ _ hp.1 hp.2
  unfold PH
  rw [record_bind]
  exact ⟨hp.1.trans h1, h2⟩

theorem PH.mono {α : Type} {p : Prog α} {st : RecState} {Q R : RecState → α → Prop} (h : PH p st Q)
    (hQR : ∀ st' a, PStep st st' → Q st' a → R st' a) : PH p st R := ⟨h.1, hQR _ _ h.1 h.2⟩

/-! ## Loops -/

/-- **A loop over a list**, by an invariant on the index. -/
theorem PH.forIn_list {α β : Type} (l : List α) (init : β) (f : α → β → Prog (ForInStep β)) (st : RecState)
    (I : ℕ → RecState → β → Prop) (hg : Good st) (h0 : I 0 st init)
    (hs : ∀ (j : ℕ) (hj : j < l.length) (st' : RecState) (b : β), PStep st st' → I j st' b →
      PH (f l[j] b) st' (fun st'' r ↦ ∃ b', r = .yield b' ∧ I (j + 1) st'' b')) :
    PH (forIn l init f) st (fun st' b ↦ I l.length st' b) := by
  suffices H : ∀ (rest : List α) (k : ℕ) (hk : k + rest.length = l.length),
      (∀ j (h : j < rest.length), rest[j] = l[k + j]'(by omega)) →
      ∀ st' b, PStep st st' → I k st' b → PH (forIn rest b f) st' (fun st'' b ↦ I l.length st'' b) by
    exact H l 0 (by simp) (fun j h ↦ by simp) st init (PStep.refl st hg) h0
  intro rest
  induction rest with
  | nil =>
    intro k hk _ st' b hs' hI
    simp only [List.length_nil, Nat.add_zero] at hk
    subst hk
    rw [List.forIn_nil]
    exact PH.ret hs'.good hI
  | cons a as ih =>
    intro k hk hr st' b hs' hI
    simp only [List.length_cons] at hk
    rw [List.forIn_cons]
    have ha : a = l[k]'(by omega) := by
      have h0 := hr 0 (by simp)
      simp only [List.getElem_cons_zero, Nat.add_zero] at h0
      exact h0
    subst ha
    refine PH.bind' (hs k (by omega) st' b hs' hI) ?_
    rintro st'' r hs'' ⟨b', rfl, hI'⟩
    exact ih (k + 1) (by omega) (fun j h ↦ by
      have := hr (j + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [this]; congr 1; omega) st'' b' (hs'.trans hs'') hI'

theorem range_size_one (s e : ℕ) : ({ start := s, stop := e, step := 1, step_pos := Nat.one_pos } : Std.Legacy.Range).size = e - s := by
  simp [Std.Legacy.Range.size]

/-- **A loop over a range**, by an invariant on the index. -/
theorem PH.forIn_range {β : Type} (s e : ℕ) (init : β) (f : ℕ → β → Prog (ForInStep β)) (st : RecState)
    (I : ℕ → RecState → β → Prop) (hg : Good st) (h0 : I 0 st init)
    (hs : ∀ (j : ℕ), j < e - s → ∀ (st' : RecState) (b : β), PStep st st' → I j st' b →
      PH (f (s + j) b) st' (fun st'' r ↦ ∃ b', r = .yield b' ∧ I (j + 1) st'' b')) :
    PH (forIn ({ start := s, stop := e, step := 1, step_pos := Nat.one_pos } : Std.Legacy.Range) init f) st
      (fun st' b ↦ I (e - s) st' b) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', range_size_one]
  have := PH.forIn_list (List.range' s (e - s) 1) init f st I hg h0 (fun j hj st' b h1 h2 ↦ by
    simp only [List.length_range'] at hj
    simpa using hs j hj st' b h1 h2)
  simpa using this

/-- **A loop against `UniStatement`'s loop**, step for step: related states step to related states, the
`UniStatement` loop yielding. -/
theorem PH.forIn_rel {α β γ : Type} (l : List α) (init : β) (f : α → β → Prog (ForInStep β)) (u0 : γ)
    (fU : α → γ → Id (ForInStep γ)) {U : Id γ} (hU : forIn (m := Id) l u0 fU = U) (st : RecState)
    (R : RecState → β → γ → Prop) (hg : Good st) (h0 : R st init u0)
    (hs : ∀ (j : ℕ) (hj : j < l.length) (st' : RecState) (b : β) (u : γ), PStep st st' → R st' b u →
      PH (f l[j] b) st' (fun st'' r ↦ ∃ b' u', r = .yield b' ∧ fU l[j] u = .yield u' ∧ R st'' b' u')) :
    PH (forIn l init f) st (fun st' b ↦ R st' b U) := by
  subst hU
  suffices H : ∀ (rest : List α) (k : ℕ) (hk : k + rest.length = l.length),
      (∀ j (h : j < rest.length), rest[j] = l[k + j]'(by omega)) →
      ∀ st' b u, PStep st st' → R st' b u →
        PH (forIn rest b f) st' (fun st'' b ↦ R st'' b (forIn (m := Id) rest u fU)) by
    have := H l 0 (by simp) (fun j h ↦ by simp) st init u0 (PStep.refl st hg) h0
    exact this
  intro rest
  induction rest with
  | nil =>
    intro k hk _ st' b u hs' hR
    rw [List.forIn_nil]
    exact PH.ret hs'.good (by rw [List.forIn_nil]; exact hR)
  | cons a as ih =>
    intro k hk hr st' b u hs' hR
    simp only [List.length_cons] at hk
    rw [List.forIn_cons]
    have ha : a = l[k]'(by omega) := by
      have h0 := hr 0 (by simp)
      simp only [List.getElem_cons_zero, Nat.add_zero] at h0
      exact h0
    subst ha
    refine PH.bind' (hs k (by omega) st' b u hs' hR) ?_
    rintro st'' r hs'' ⟨b', u', rfl, hu, hR'⟩
    have hrest := ih (k + 1) (by omega) (fun j h ↦ by
      have := hr (j + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [this]; congr 1; omega) st'' b' u' (hs'.trans hs'') hR'
    have hu' : forIn (m := Id) (l[k] :: as) u fU = forIn (m := Id) as u' fU := by
      rw [List.forIn_cons, hu]; rfl
    rw [hu']
    exact hrest

/-- **A loop over a range against `UniStatement`'s loop over a range.** -/
theorem PH.forIn_rel_range {β γ : Type} (s e : ℕ) (init : β) (f : ℕ → β → Prog (ForInStep β)) (u0 : γ)
    (fU : ℕ → γ → Id (ForInStep γ)) {U : Id γ}
    (hU : forIn (m := Id) ({ start := s, stop := e, step := 1, step_pos := Nat.one_pos } : Std.Legacy.Range) u0 fU = U)
    (st : RecState) (R : RecState → β → γ → Prop) (hg : Good st) (h0 : R st init u0)
    (hs : ∀ (j : ℕ), j < e - s → ∀ (st' : RecState) (b : β) (u : γ), PStep st st' → R st' b u →
      PH (f (s + j) b) st' (fun st'' r ↦ ∃ b' u', r = .yield b' ∧ fU (s + j) u = .yield u' ∧ R st'' b' u')) :
    PH (forIn ({ start := s, stop := e, step := 1, step_pos := Nat.one_pos } : Std.Legacy.Range) init f) st
      (fun st' b ↦ R st' b U) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', range_size_one]
  rw [Std.Legacy.Range.forIn_eq_forIn_range', range_size_one] at hU
  exact PH.forIn_rel _ init f u0 fU hU st R hg h0 (fun j hj st' b u h1 h2 ↦ by
    simp only [List.length_range'] at hj
    simpa using hs j hj st' b u h1 h2)

/-! ## Arrays -/

theorem iteT {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : c) : (if c then a else b) = a :=
  ite_eq_left_of_eq_true _ _ (eq_true h)

theorem ditT {c : Prop} [Decidable c] {α : Sort _} {a : c → α} {b : ¬ c → α} (h : c) : dite c a b = a h := by
  simp [h]

theorem iteF {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : ¬ c) : (if c then a else b) = b :=
  ite_eq_right_of_eq_false _ _ (eq_false h)

theorem getD_setB {α : Type} (a : Array α) (j i : ℕ) (v d : α) :
    (a.set! j v).getD i d = if j = i ∧ i < a.size then v else a.getD i d := by
  simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases h1 : j = i
  · subst h1
    by_cases h2 : j < a.size
    · simp [h2]
    · simp [h2]
  · simp [h1]

theorem getD_pushB {α : Type} (a : Array α) (v d : α) (i : ℕ) :
    (a.push v).getD i d = if i < a.size then a.getD i d else if i = a.size then v else d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  by_cases h1 : i < a.size
  · simp [h1, Nat.ne_of_lt h1]
  · by_cases h2 : i = a.size
    · simp [h2]
    · simp [h1, h2]

theorem size_setB {α : Type} (a : Array α) (j : ℕ) (v : α) : (a.set! j v).size = a.size := by
  simp [Array.set!_eq_setIfInBounds]

section Values

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- **An array of nodes represents an array of `E`**: the same size, entry `i` worth entry `i`. -/
def RpA (st : RecState) (a : Array Sym) (x : Array E) : Prop :=
  a.size = x.size ∧ ∀ i, i < a.size → Rp π iv publicInput stream st (a.getD i 0) (x.getD i 0)

variable {π iv publicInput stream}

theorem Rp.pgrow {st st' : RecState} (hg : Good st) (hs : PStep st st') {i : Nat} {x : E}
    (h : Rp π iv publicInput stream st i x) : Rp π iv publicInput stream st' i x :=
  h.grow π iv publicInput stream hg.inv.kinv hs.grows

theorem RpL.pgrow {st st' : RecState} (hg : Good st) (hs : PStep st st') {is : List Nat} {xs : List E}
    (h : RpL π iv publicInput stream st is xs) : RpL π iv publicInput stream st' is xs :=
  h.grow π iv publicInput stream hg.inv.kinv hs.grows

theorem RpA.pgrow {st st' : RecState} (hg : Good st) (hs : PStep st st') {a : Array Sym} {x : Array E}
    (h : RpA π iv publicInput stream st a x) : RpA π iv publicInput stream st' a x :=
  ⟨h.1, fun i hi ↦ (h.2 i hi).pgrow hg hs⟩

theorem RpA.get {st : RecState} {a : Array Sym} {x : Array E} (h : RpA π iv publicInput stream st a x) {i : ℕ}
    (hi : i < x.size) : Rp π iv publicInput stream st (a.getD i 0) (x.getD i 0) := h.2 i (h.1 ▸ hi)

theorem RpA.set {st : RecState} {a : Array Sym} {x : Array E} (h : RpA π iv publicInput stream st a x)
    {s : Sym} {v : E} (hv : Rp π iv publicInput stream st s v) (j : ℕ) :
    RpA π iv publicInput stream st (a.set! j s) (x.set! j v) := by
  refine ⟨by simp [h.1], fun i hi ↦ ?_⟩
  rw [size_setB] at hi
  rw [getD_setB, getD_setB, ← h.1]
  by_cases hj : j = i ∧ i < a.size
  · rw [iteT hj, iteT hj]; exact hv
  · rw [iteF hj, iteF hj]; exact h.2 i hi

theorem RpA.push {st : RecState} {a : Array Sym} {x : Array E} (h : RpA π iv publicInput stream st a x)
    {s : Sym} {v : E} (hv : Rp π iv publicInput stream st s v) :
    RpA π iv publicInput stream st (a.push s) (x.push v) := by
  refine ⟨by simp [h.1], fun i hi ↦ ?_⟩
  rw [getD_pushB, getD_pushB, ← h.1]
  simp only [Array.size_push] at hi
  by_cases hi' : i < a.size
  · rw [iteT hi', iteT hi']; exact h.2 i hi'
  · have he : i = a.size := by omega
    rw [iteF hi', iteF hi', iteT he, iteT he]; exact hv

theorem RpA.nil {st : RecState} : RpA π iv publicInput stream st #[] #[] := ⟨rfl, fun i hi ↦ by simp at hi⟩

theorem RpA.replicate {st : RecState} {z : Sym} {v : E} (hz : Rp π iv publicInput stream st z v) (n : ℕ) :
    RpA π iv publicInput stream st (Array.replicate n z) (Array.replicate n v) := by
  refine ⟨by simp, fun i hi ↦ ?_⟩
  simp only [Array.size_replicate] at hi
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, hi, ↓reduceIte, Option.getD_some]
  exact hz

theorem RpA.toRpL {st : RecState} {a : Array Sym} {x : Array E} (h : RpA π iv publicInput stream st a x) :
    RpL π iv publicInput stream st a.toList x.toList := by
  rw [RpL, List.forall₂_iff_get]
  refine ⟨by simp [h.1], fun i h1 h2 ↦ ?_⟩
  have := h.2 i (by simpa using h1)
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using h1),
    Array.getElem?_eq_getElem (h.1 ▸ (by simpa using h1) : i < x.size), Option.getD_some] at this
  simpa using this

theorem RpL.toRpA {st : RecState} {l : List Sym} {xs : List E} (h : RpL π iv publicInput stream st l xs) :
    RpA π iv publicInput stream st l.toArray xs.toArray := by
  rw [RpL, List.forall₂_iff_get] at h
  refine ⟨by simp [h.1], fun i hi ↦ ?_⟩
  simp only [List.size_toArray] at hi
  have := h.2 i hi (h.1 ▸ hi)
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (h.1 ▸ hi : i < xs.length), Option.getD_some]
  simpa using this

theorem RpA.ofFn {st : RecState} {a : Array Sym} {n : ℕ} {g : Fin n → E} (hs : a.size = n)
    (h : ∀ i (hi : i < n), Rp π iv publicInput stream st (a.getD i 0) (g ⟨i, hi⟩)) :
    RpA π iv publicInput stream st a (Array.ofFn g) := by
  refine ⟨by simp [hs], fun i hi ↦ ?_⟩
  rw [hs] at hi
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi]
  have := h i hi
  simpa [Array.getD_eq_getD_getElem?] using this

theorem RpL.length {st : RecState} {l : List Sym} {xs : List E} (h : RpL π iv publicInput stream st l xs) :
    l.length = xs.length := List.Forall₂.length_eq h

/-! ## The arithmetic operations -/

theorem PH.op_arith {st : RecState} (hg : Good st) (o : Op) (ho : Op.Arith o) (hok : OpOK st o) :
    PH (Pi1.op o) st (fun st' i ↦ Rp π iv publicInput stream st' i
      (Op.value π publicInput stream st (evalAll π iv publicInput stream st) o)) :=
  op_pstep π iv publicInput stream st hg o ho hok

theorem PH.add {st : RecState} (hg : Good st) {a b : Sym} {x y : E} (ha : Rp π iv publicInput stream st a x)
    (hb : Rp π iv publicInput stream st b y) :
    PH (Pi1.add a b) st (fun st' i ↦ Rp π iv publicInput stream st' i (x + y)) := by
  have h := PH.op_arith (π := π) (iv := iv) (publicInput := publicInput) (stream := stream) hg (.add a b) trivial
    ⟨ha.1, hb.1⟩
  refine h.mono fun st' i _ hr ↦ ⟨hr.1, hr.2.trans ?_⟩
  show val π iv publicInput stream st a + val π iv publicInput stream st b = x + y
  rw [ha.2, hb.2]

theorem PH.mul {st : RecState} (hg : Good st) {a b : Sym} {x y : E} (ha : Rp π iv publicInput stream st a x)
    (hb : Rp π iv publicInput stream st b y) :
    PH (Pi1.mul a b) st (fun st' i ↦ Rp π iv publicInput stream st' i (x * y)) := by
  have h := PH.op_arith (π := π) (iv := iv) (publicInput := publicInput) (stream := stream) hg (.mul a b) trivial
    ⟨ha.1, hb.1⟩
  refine h.mono fun st' i _ hr ↦ ⟨hr.1, hr.2.trans ?_⟩
  show val π iv publicInput stream st a * val π iv publicInput stream st b = x * y
  rw [ha.2, hb.2]

theorem PH.square {st : RecState} (hg : Good st) {a : Sym} {x : E} (ha : Rp π iv publicInput stream st a x) :
    PH (Pi1.square a) st (fun st' i ↦ Rp π iv publicInput stream st' i (x * x)) := PH.mul hg ha ha

theorem PH.const {st : RecState} (hg : Good st) (x : E) :
    PH (Pi1.const x) st (fun st' i ↦ Rp π iv publicInput stream st' i x) :=
  PH.op_arith (π := π) (iv := iv) (publicInput := publicInput) (stream := stream) hg (.constant x) trivial trivial

theorem PH.zero {st : RecState} (hg : Good st) :
    PH Pi1.zero st (fun st' i ↦ Rp π iv publicInput stream st' i 0) := PH.const hg 0

theorem PH.one {st : RecState} (hg : Good st) :
    PH Pi1.one st (fun st' i ↦ Rp π iv publicInput stream st' i 1) := PH.const hg 1

end Values

/-- `refine PH.bind' t fun st x hs hx ↦ ?_`, then `grow_all hg hs`. -/
syntax "phg " term " as " ident ident ident ident : tactic

/-! ## Transport along a pure step: `grow_all hg hs` -/

open Lean Elab Tactic Meta in
/-- `grow_all hg hs` (`hg : Good st`, `hs : PStep st st'`): every hypothesis `Rp … st …`, `RpL … st …`, `RpA … st …`,
`RW … st …`, `RpS … st …` is replaced by its transport to `st'` (`*.pgrow`), every `PStep a st` by `PStep a st'`,
then `hg` by `Good st'`. -/
elab "grow_all " hg:ident hs:ident : tactic => do
  let todo ← withMainContext do
    let hsType ← instantiateMVars (← inferType (← getLocalDeclFromUserName hs.getId).toExpr)
    let src := hsType.getAppArgs[0]!
    let lctx ← getLCtx
    let mut out : Array (Name × Name) := #[]
    for ldecl in lctx do
      if ldecl.isImplementationDetail then continue
      if ldecl.userName.hasMacroScopes then continue
      if ldecl.userName == hg.getId || ldecl.userName == hs.getId then continue
      let t ← instantiateMVars ldecl.type
      let args := t.getAppArgs
      match t.getAppFn.constName? with
      | some n =>
        let lem? : Option (Name × Nat) :=
          if n == ``Rp then some (``Rp.pgrow, 4)
          else if n == ``RpL then some (``RpL.pgrow, 4)
          else if n == ``RpA then some (``RpA.pgrow, 4)
          else if n == `RecGraph.Sim.RW then some (`RecGraph.Sim.RW.pgrow, 4)
          else if n == `RecGraph.Sim.RpS then some (`RecGraph.Sim.RpS.pgrow, 4)
          else if n == ``PStep then some (``PStep.trans, 1)
          else none
        match lem? with
        | some (lem, k) =>
          if h : k < args.size then
            if args[k] == src then out := out.push (ldecl.userName, lem)
        | none => pure ()
      | none => pure ()
    return out
  for (n, lem) in todo do
    if lem == ``PStep.trans then
      evalTactic (← `(tactic| replace $(mkIdent n):ident := PStep.trans $(mkIdent n) $hs))
    else
      evalTactic (← `(tactic| replace $(mkIdent n):ident := $(mkIdent lem) $hg $hs $(mkIdent n)))
  evalTactic (← `(tactic| replace $hg:ident := ($hs).good))

macro_rules
  | `(tactic| phg $t as $st $x $hs $hx) =>
    `(tactic| (refine PH.bind' $t fun $st $x $hs $hx ↦ ?_; grow_all $(Lean.mkIdent `hg) $hs))

end RecGraph.Sim
