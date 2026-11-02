-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Bridge.Circuit.Sim

/-!
# Loops

The statement's builder writes its loops as `for` loops over ranges, filling arrays by `set!`; F0b's
maps over `List.range`. `simR_forIn` simulates a `for` loop by a `mapM`, step by step, through an
invariant on the results so far; `simR_forIn_foldlM` and `simR_foldlM` do the same for a fold.
`Ow c₀ acc c`: the array `c` is `c₀` with its first entries overwritten by `acc` (read by `srcTr`);
`mapM_range_mul` splits a `mapM` over `range (A * B)` into `A` blocks of `B`.
-/

namespace Bridge.Circuit

/-! ## Lists of steps -/

theorem simR_mapM {α β γ : Type} (l : List γ) (g : γ → PcsQuotient.BuildM α)
    (g' : γ → PcsCircuit.BuildM β) (R : α → β → Prop) (h : ∀ x ∈ l, SimR (g x) (g' x) R) :
    SimR (l.mapM g) (l.mapM g') (List.Forall₂ R) := by
  induction l with
  | nil => exact SimR.pure List.Forall₂.nil
  | cons x l ih =>
    simp only [List.mapM_cons]
    exact (h x (List.mem_cons_self ..)).bind fun a c hac =>
      (ih fun y hy => h y (List.mem_cons_of_mem _ hy)).bind fun as cs has =>
        SimR.pure (List.Forall₂.cons hac has)

theorem forall₂_srcTr {as : List PcsQuotient.Src} {cs : List PcsCircuit.Src}
    (h : List.Forall₂ (fun a c => c = srcTr a) as cs) : cs = as.map srcTr := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [h, ih]

theorem simS_mapM {γ : Type} (l : List γ) (g : γ → PcsQuotient.BuildM PcsQuotient.Src)
    (g' : γ → PcsCircuit.BuildM PcsCircuit.Src) (h : ∀ x ∈ l, SimS (g x) (g' x)) :
    SimR (l.mapM g) (l.mapM g') (fun as cs => cs = as.map srcTr) :=
  (simR_mapM l g g' _ h).mono fun _ _ h => forall₂_srcTr h

/-- **A `for` loop simulated by a `mapM`**, through an invariant `Inv` on the results so far and
the loop's state. -/
theorem simR_forIn {β γ δ : Type} (l : List δ) (F : δ → β → PcsQuotient.BuildM (ForInStep β))
    (g : δ → PcsCircuit.BuildM γ) (Inv : List γ → β → Prop) :
    ∀ (acc : List γ) (init : β), Inv acc init →
      (∀ i (hi : i < l.length) (acc' : List γ) (s : β), acc'.length = acc.length + i → Inv acc' s →
        SimR (F l[i] s) (g l[i]) (fun st v => ∃ s', st = .yield s' ∧ Inv (acc' ++ [v]) s')) →
      SimR (forIn l init F) (l.mapM g) (fun s vs => Inv (acc ++ vs) s ∧ vs.length = l.length) := by
  induction l with
  | nil =>
    intro acc init hinit _
    exact SimR.pure (by simpa using hinit)
  | cons x l ih =>
    intro acc init hinit hstep
    rw [List.forIn_cons, List.mapM_cons]
    refine (hstep 0 (by simp) acc init (by simp) hinit).bind fun st v ⟨s', hst, hinv⟩ => ?_
    subst hst
    have hrest := ih (acc ++ [v]) s' hinv fun i hi acc' s hlen hs =>
      hstep (i + 1) (by simp; omega) acc' s (by simp at hlen; omega) hs
    have : SimR (forIn l s' F) (l.mapM g >>= fun vs => pure (v :: vs))
        (fun s vs => Inv (acc ++ vs) s ∧ vs.length = (x :: l).length) := by
      rw [← bind_pure (forIn l s' F)]
      exact hrest.bind fun s vs h => SimR.pure (by simpa using h)
    exact this

/-- **A `for` loop simulated by a fold**, the states related by `R`. -/
theorem simR_forIn_foldlM {β γ δ : Type} (l : List δ) (F : δ → β → PcsQuotient.BuildM (ForInStep β))
    (g : γ → δ → PcsCircuit.BuildM γ) (R : β → γ → Prop) :
    ∀ (init : β) (init' : γ), R init init' →
      (∀ x ∈ l, ∀ s t, R s t → SimR (F x s) (g t x) (fun st t' => ∃ s', st = .yield s' ∧ R s' t')) →
      SimR (forIn l init F) (l.foldlM g init') R := by
  induction l with
  | nil => intro init init' h _; exact SimR.pure h
  | cons x l ih =>
    intro init init' h hstep
    rw [List.forIn_cons, List.foldlM_cons]
    refine (hstep x (List.mem_cons_self ..) init init' h).bind fun st t ⟨s', hst, hr⟩ => ?_
    subst hst
    exact ih s' t hr fun y hy => hstep y (List.mem_cons_of_mem _ hy)

/-- **A fold simulated by a fold**. -/
theorem simR_foldlM {β γ δ : Type} (l : List δ) (f : β → δ → PcsQuotient.BuildM β)
    (g : γ → δ → PcsCircuit.BuildM γ) (R : β → γ → Prop) :
    ∀ (init : β) (init' : γ), R init init' →
      (∀ x ∈ l, ∀ s t, R s t → SimR (f s x) (g t x) R) →
      SimR (l.foldlM f init) (l.foldlM g init') R := by
  induction l with
  | nil => intro init init' h _; exact SimR.pure h
  | cons x l ih =>
    intro init init' h hstep
    rw [List.foldlM_cons, List.foldlM_cons]
    exact (hstep x (List.mem_cons_self ..) init init' h).bind fun s t hr =>
      ih s t hr fun y hy => hstep y (List.mem_cons_of_mem _ hy)

/-! ## `mapM` over `range (A * B)` -/

theorem mapM_congr_mem {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type} (l : List α)
    (f g : α → m β) (h : ∀ x ∈ l, f x = g x) : l.mapM f = l.mapM g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.mapM_cons]
    rw [h x (List.mem_cons_self ..), ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- A `mapM` over `range (A * B)` is `A` blocks of `B`. -/
theorem mapM_range_mul {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type} (B : ℕ)
    (g : ℕ → m α) : ∀ A : ℕ, (List.range (A * B)).mapM g =
      List.flatten <$> (List.range A).mapM fun x => (List.range B).mapM fun z => g (B * x + z)
  | 0 => by simp
  | A + 1 => by
    rw [show (A + 1) * B = A * B + B by ring, List.range_add, List.mapM_append,
      mapM_range_mul B g A, List.range_succ, List.mapM_append, List.mapM_map]
    simp only [List.mapM_cons, List.mapM_nil, map_eq_pure_bind, bind_assoc, pure_bind,
      List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, Function.comp_def,
      Nat.mul_comm A B]

/-! ## Arrays overwritten from the front -/

/-- `c` is `c₀` with its first `acc.length` entries overwritten by `acc` (read by `srcTr`). -/
def Ow (c₀ : Array PcsQuotient.Src) (acc : List PcsCircuit.Src) (c : Array PcsQuotient.Src) : Prop :=
  c.toList.map srcTr = acc ++ (c₀.toList.drop acc.length).map srcTr

theorem ow_init (c₀ : Array PcsQuotient.Src) : Ow c₀ [] c₀ := by simp [Ow]

theorem Ow.size {c₀ c : Array PcsQuotient.Src} {acc : List PcsCircuit.Src} (h : Ow c₀ acc c)
    (hl : acc.length ≤ c₀.size) : c.size = c₀.size := by
  unfold Ow at h
  have := congrArg List.length h
  simp only [List.length_map, Array.length_toList, List.length_append, List.length_drop] at this
  omega

theorem Ow.getD {c₀ c : Array PcsQuotient.Src} {acc : List PcsCircuit.Src} (h : Ow c₀ acc c)
    {k : ℕ} (hk : acc.length ≤ k) : c.getD k .zero = c₀.getD k .zero := by
  apply srcTr_injective
  unfold Ow at h
  have h1 : (c.toList.map srcTr).getD k .zero =
      (acc ++ (c₀.toList.drop acc.length).map srcTr).getD k .zero := by rw [h]
  have e : ∀ (d : Array PcsQuotient.Src), srcTr (d.getD k .zero) = (d.toList.map srcTr).getD k .zero := by
    intro d
    simp only [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_map,
      Array.getElem?_toList]
    cases d[k]? <;> rfl
  rw [e c, h1, e c₀, List.getD_append_right _ _ _ _ hk, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map, List.getElem?_drop,
    Nat.add_sub_cancel' hk]

theorem Ow.set {c₀ c : Array PcsQuotient.Src} {acc : List PcsCircuit.Src} (h : Ow c₀ acc c)
    (hl : acc.length < c₀.size) (v : PcsQuotient.Src) :
    Ow c₀ (acc ++ [srcTr v]) (c.set! acc.length v) := by
  unfold Ow at h ⊢
  have hd : c₀.toList.drop acc.length = c₀.toList[acc.length]'(by simpa using hl) ::
      c₀.toList.drop (acc.length + 1) := List.drop_eq_getElem_cons _
  rw [hd, List.map_cons] at h
  simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds, List.map_set, h,
    List.length_append, List.length_singleton]
  rw [List.set_append_right _ _ (by omega), Nat.sub_self, List.set_cons_zero, List.append_assoc]
  rfl

/-- An entry left as it was is an overwrite by itself. -/
theorem Ow.keep {c₀ c : Array PcsQuotient.Src} {acc : List PcsCircuit.Src} (h : Ow c₀ acc c)
    (hl : acc.length < c₀.size) : Ow c₀ (acc ++ [srcTr (c₀.getD acc.length .zero)]) c := by
  have hs := h.set hl (c₀.getD acc.length .zero)
  have hc : c.set! acc.length (c₀.getD acc.length .zero) = c := by
    rw [← h.getD (le_refl _)]
    have hsz : acc.length < c.size := by rw [h.size hl.le]; exact hl
    apply Array.toList_inj.mp
    simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hsz,
      Option.getD_some, Array.toList_setIfInBounds]
    exact List.set_getElem_self (by simpa using hsz)
  rwa [hc] at hs

theorem Ow.full {c₀ c : Array PcsQuotient.Src} {acc : List PcsCircuit.Src} (h : Ow c₀ acc c)
    (hl : acc.length = c₀.size) : c.map srcTr = acc.toArray := by
  unfold Ow at h
  apply Array.toList_inj.mp
  have hd : c₀.toList.drop acc.length = [] := List.drop_eq_nil_of_le (by simp [hl])
  rw [Array.toList_map, h, hd]
  simp

/-! ## Loops over ranges -/

theorem forIn_range {m : Type → Type} [Monad m] {β : Type} (n : ℕ) (init : β)
    (f : ℕ → β → m (ForInStep β)) : forIn [:n] init f = forIn (List.range n) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp [Std.Legacy.Range.size, List.range_eq_range']

/-- **Filling `64` entries from `o`**, the `z`-th the result of `body z` on the array so far. -/
theorem sim_fill1 (c₀ : Array PcsQuotient.Src) (o : ℕ) (ho : o + 64 ≤ c₀.size)
    (pos : ℕ → ℕ) (hpos : ∀ z, pos z = o + z)
    (body : ℕ → Array PcsQuotient.Src → PcsQuotient.BuildM PcsQuotient.Src)
    (G : ℕ → PcsCircuit.BuildM PcsCircuit.Src)
    (hbody : ∀ z < 64, ∀ acc s, acc.length = o + z → Ow c₀ acc s → SimS (body z s) (G z))
    (acc₀ : List PcsCircuit.Src) (hacc : acc₀.length = o) (s₀ : Array PcsQuotient.Src)
    (hs₀ : Ow c₀ acc₀ s₀) :
    SimR (forIn [:64] s₀ fun z s => do
        let v ← body z s
        pure (ForInStep.yield (s.set! (pos z) v)))
      ((List.range 64).mapM G) (fun s vs => Ow c₀ (acc₀ ++ vs) s ∧ vs.length = 64) := by
  rw [forIn_range]
  refine (simR_forIn (List.range 64) _ G (Ow c₀) acc₀ s₀ hs₀ fun i hi acc s hlen hs => ?_).mono
    fun s vs h => ⟨h.1, by simpa using h.2⟩
  simp only [List.length_range] at hi
  simp only [List.getElem_range]
  refine (hbody i hi acc s (by omega) hs).bind_left fun v c hvc => SimR.pure ⟨_, rfl, ?_⟩
  subst hvc
  rw [hpos, show o + i = acc.length by omega]
  exact hs.set (by omega) v

/-- **Filling `A` blocks of `64` entries from `base`**. -/
theorem sim_fill2 (A : ℕ) (c₀ : Array PcsQuotient.Src) (base : ℕ) (hA : base + 64 * A ≤ c₀.size)
    (pos : ℕ → ℕ → ℕ) (hpos : ∀ x z, pos x z = base + (64 * x + z))
    (body : ℕ → ℕ → Array PcsQuotient.Src → PcsQuotient.BuildM PcsQuotient.Src)
    (G : ℕ → ℕ → PcsCircuit.BuildM PcsCircuit.Src)
    (hbody : ∀ x < A, ∀ z < 64, ∀ acc s, acc.length = base + (64 * x + z) → Ow c₀ acc s →
      SimS (body x z s) (G x z))
    (acc₀ : List PcsCircuit.Src) (hacc : acc₀.length = base) (s₀ : Array PcsQuotient.Src)
    (hs₀ : Ow c₀ acc₀ s₀) :
    SimR (forIn [:A] s₀ fun x s => do
        let s ← forIn [:64] s fun z s => do
          let v ← body x z s
          pure (ForInStep.yield (s.set! (pos x z) v))
        pure (ForInStep.yield s))
      ((List.range A).mapM fun x => (List.range 64).mapM (G x))
      (fun s vss => Ow c₀ (acc₀ ++ vss.flatten) s ∧ vss.flatten.length = 64 * A) := by
  rw [forIn_range]
  refine (simR_forIn (List.range A) _ _
    (fun vss s => Ow c₀ (acc₀ ++ vss.flatten) s ∧ vss.flatten.length = 64 * vss.length) [] s₀
    ⟨by simpa using hs₀, by simp⟩ fun i hi acc s hlen hs => ?_).mono
    fun s vss h => ⟨by simpa using h.1.1, by simpa [h.2] using h.1.2⟩
  simp only [List.length_range] at hi
  simp only [List.length_nil, Nat.zero_add] at hlen
  simp only [List.getElem_range]
  refine (sim_fill1 c₀ (base + 64 * i) (by
      have : i + 1 ≤ A := hi
      nlinarith) (pos i) (fun z => by rw [hpos]; ring)
    (body i) (G i) (fun z hz acc' s' hl hs' => hbody i hi z hz acc' s' (by rw [hl]; ring) hs')
    (acc₀ ++ acc.flatten) (by simp [hacc, hs.2, hlen]) s hs.1).bind_left
    fun s' vs h => SimR.pure ⟨s', rfl, ?_, ?_⟩
  · simpa [List.append_assoc] using h.1
  · simp [hs.2, h.2, hlen]
    ring

end Bridge.Circuit
