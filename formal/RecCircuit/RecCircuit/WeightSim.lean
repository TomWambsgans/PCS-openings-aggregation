-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. About `Graph.lean`'s `weightAtM` (the transcription of
-- `crates/leanvm_flock_gas/src/ring_tower.rs`'s `weight_at`) and `Expand.lean`'s `weightSym`.
import RecCircuit.Expand
import RecGraph.Values
import UniStatement.Flock

/-!
# The ring switch's weight: on `E` it is `UniStatement`'s, and on the recorder's symbols it simulates `E`'s

* `weightAt_eq_tower`: `weightAt` (`weightAtM` on `F192` in `Id`) is `Flock.towerWeightAt`, for a map of
  `towerStages = 6` stages. The two programs differ in form only: `weightAtM` reads the map by `for f in map` with a
  counter, its stage `j`'s inner loop runs `(64 + 2·2^j − 1) / (2·2^j)` times (the Rust's `div_ceil`), and it squares
  by `frobeniusM`; `towerWeightAt` reads `map.getD j 0` for `j < 6`, runs `kBits / (2·2^j)` times (equal for `j < 6`:
  `2·2^j` divides 64) and squares by `sqn`. Both are rewritten into left folds (`forIn_id_yield`: in `Id`, a loop that
  only yields is a fold), then compared stage by stage.
* `weightSym_sim`: `weightRun` (`weightAtM` on the recorder's symbols, in `StateM RecState`) from a state with the
  recorder's invariant keeps the invariant, grows the state, keeps its kernels, and returns a symbol that denotes
  (`Rel`) `weightAt` of the values its operands denote. The proof is a simulation (`Sim`): a relational Hoare triple
  between a computation in `SM` and one in `Id`, Kripke-style (the postcondition is stated at the state reached, and
  every relation used is monotone along `Ext`, "a run of the recorder extends this state"), with rules for `pure`,
  `bind`, an `if` with a join point (`Sim.jp`), loops over lists and ranges (`Sim.forIn_list`, `Sim.forIn_range`),
  `List.mapM`, `frobeniusM`, and the three operations (`sim_add`, `sim_mul`, `sim_one`, from `RecGraph`'s `add_val`,
  `mul_val`, `constant_val`). Both sides are the same program `weightAtM`, so the proof follows its structure.

Decisions recorded here:
* `Sim` relates a computation in `SM` to one in `Id`, not any two monads: only that instance is needed.
* An array of symbols denotes an array of values (`ArrRel`) when both have the same size and each `getD i 0` denotes
  the other's (`0` the default symbol, which `h0` relates to the default value `0`), so `getD`, `push` and `set!`
  need no range reasoning.
* `Rel` and the two end theorems are in `RecCircuit`; the helpers (the folds, `Sim` and its rules) are in
  `RecCircuit.WeightSim`, so that their short names (`Sim`, `Ext`, `stage`, ...) do not collide with other files'.
* Both end theorems are stated exactly as asked; nothing in `Graph.lean` was changed.
-/

namespace RecCircuit

open Primitives LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement
open RecGraph (RecState RecInv Grows)

/-! ## (A) `weightAt` is `Flock.towerWeightAt` -/

namespace WeightSim

/-- In `Id`, a loop over a list whose body only yields is a left fold. -/
theorem forIn_id_yield {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β)) (g : α → β → β)
    (hf : ∀ a b, f a b = ForInStep.yield (g a b)) :
    forIn l init f = (pure (l.foldl (fun b a => g a b) init) : Id β) := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih => rw [List.forIn_cons, hf]; exact ih _

/-- A loop over `[:n]` is a loop over `List.range' 0 n`. -/
theorem forIn_range0 {m : Type → Type} [Monad m] {β : Type} (n : ℕ) (init : β) (f : ℕ → β → m (ForInStep β)) :
    forIn [:n] init f = forIn (List.range' 0 n) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]

/-- `frobeniusM` on `E` in `Id` is `sqn`. -/
theorem frobeniusM_id (p : E) (t : ℕ) :
    frobeniusM (m := Id) (fun a b : E => (pure (a * b) : Id E)) p t = (pure (sqn p t) : Id E) := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih => exact ih (p * p)

/-- One step of the 64 products' loop on `E`. -/
def gsStep (onePlusR : List E) (k : ℕ) (s : List E × Array E) : List E × Array E :=
  if k > 0 then
    (s.1.map (fun c => c * c), s.2.push (((s.1.map (fun c => c * c)).zip onePlusR).foldl
      (fun acc x => acc * (x.2 + x.1)) 1))
  else (s.1, s.2.push ((s.1.zip onePlusR).foldl (fun acc x => acc * (x.2 + x.1)) 1))

/-- The 64 products on `E`, as a fold. -/
def gsF (point onePlusR : List E) : Array E :=
  ((List.range' 0 64).foldl (fun s k => gsStep onePlusR k s) (point, #[])).2

/-- One step of a stage's loop on `E` (`step = 2^j`). -/
def tStep (step t : ℕ) (s : Array E × E) : Array E × E :=
  if t * (2 * step) > 0 then
    (s.1.set! (t * (2 * step)) (s.1.getD (t * (2 * step)) 0 +
      sqn s.2 (2 * step) * s.1.getD (t * (2 * step) + step) 0), sqn s.2 (2 * step))
  else
    (s.1.set! (t * (2 * step)) (s.1.getD (t * (2 * step)) 0 + s.2 * s.1.getD (t * (2 * step) + step) 0), s.2)

/-- Stage `j` (`n` rounds) on `E`, as a fold. -/
def stage (f : E) (j n : ℕ) (g : Array E) : Array E :=
  ((List.range' 0 n).foldl (fun s t => tStep (2 ^ j) t s) (g, f)).1

theorem weightGs_id (point onePlusR : List E) :
    weightGs (m := Id) (fun a b : E => (pure (a + b) : Id E)) (fun a b => pure (a * b)) (pure 1) point onePlusR =
      (pure (gsF point onePlusR) : Id (Array E)) := by
  unfold weightGs
  dsimp only
  rw [forIn_range0, forIn_id_yield _ _ _ (fun k s => gsStep onePlusR k s)]
  · rfl
  · intro k s
    by_cases hk : k > 0
    · simp only [gsStep, hk, ↓reduceIte, List.mapM_pure, pure_bind]
      rw [forIn_id_yield _ _ _ (fun x acc => acc * (x.2 + x.1))]
      · rfl
      · intro x acc; obtain ⟨c, a⟩ := x; rfl
    · simp only [gsStep, hk, ↓reduceIte, pure_bind]
      rw [forIn_id_yield _ _ _ (fun x acc => acc * (x.2 + x.1))]
      · rfl
      · intro x acc; obtain ⟨c, a⟩ := x; rfl

/-- `weightAt` as folds. -/
theorem weightAt_fold (point onePlusR map : List E) :
    weightAt point onePlusR map =
      ((map.foldl (fun s f => (stage f s.2 ((64 + 2 * 2 ^ s.2 - 1) / (2 * 2 ^ s.2)) s.1, s.2 + 1))
        (gsF point onePlusR, 0)).1).getD 0 0 := by
  unfold weightAt weightAtM
  rw [weightGs_id]
  simp only [pure_bind]
  rw [forIn_id_yield _ _ _ (fun f s => (stage f s.2 ((64 + 2 * 2 ^ s.2 - 1) / (2 * 2 ^ s.2)) s.1, s.2 + 1))]
  · simp only [pure_bind, Id.run_pure]
  · intro f s
    obtain ⟨g, j⟩ := s
    dsimp only
    rw [forIn_range0, forIn_id_yield _ _ _ (fun t s => tStep (2 ^ j) t s)]
    · rfl
    · intro t s
      obtain ⟨g, p⟩ := s
      dsimp only
      by_cases hk : t * (2 * 2 ^ j) > 0
      · simp only [hk, ↓reduceIte, frobeniusM_id, tStep, pure_bind]
        rfl
      · simp only [hk, ↓reduceIte, tStep]
        rfl

/-- `Flock.towerWeightAt` as folds. -/
theorem tower_fold (point onePlusR map : List E) :
    Flock.towerWeightAt point onePlusR map =
      ((List.range' 0 Flock.towerStages).foldl
        (fun g j => stage (map.getD j 0) j (Flock.kBits / (2 * 2 ^ j)) g) (gsF point onePlusR)).getD 0 0 := by
  unfold Flock.towerWeightAt
  dsimp only
  rw [forIn_range0, forIn_id_yield _ _ _ (fun k s => gsStep onePlusR k s)]
  · simp only [pure_bind]
    rw [forIn_range0, forIn_id_yield _ _ _ (fun j g => stage (map.getD j 0) j (Flock.kBits / (2 * 2 ^ j)) g)]
    · simp only [pure_bind, Id.run_pure]
      rfl
    · intro j g
      rw [forIn_range0, forIn_id_yield _ _ _ (fun t s => tStep (2 ^ j) t s)]
      · rfl
      · intro t s
        obtain ⟨g, p⟩ := s
        dsimp only
        by_cases hk : t * (2 * 2 ^ j) > 0
        · simp only [tStep, hk, ↓reduceIte]
          rfl
        · simp only [tStep, hk, ↓reduceIte]
          rfl
  · intro k s
    by_cases hk : k > 0
    · simp only [gsStep, hk, ↓reduceIte]
      rfl
    · simp only [gsStep, hk, ↓reduceIte]
      rfl

end WeightSim

open WeightSim in
/-- **(A) The E-level transcription is `UniStatement`'s**: `weightAt` is `Flock.towerWeightAt`, for a map of
`towerStages = 6` stages. -/
theorem weightAt_eq_tower (point onePlusR map : List F192) (hm : map.length = Flock.towerStages) :
    weightAt point onePlusR map = Flock.towerWeightAt point onePlusR map := by
  rw [weightAt_fold, tower_fold]
  rcases map with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, _ | ⟨f4, _ | ⟨f5, _ | ⟨f6, rest⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil, Flock.towerStages] at hm <;> try omega
  simp only [List.foldl_cons, List.foldl_nil, List.range', List.getD_cons_zero, List.getD_cons_succ, Flock.kBits,
    Flock.towerStages, Nat.reduceAdd, Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv]

/-! ## (B) The symbolic run simulates the run on `E` -/

/-- Symbol `i` denotes the element `x` in the recorder's state `st` (over `π`, the IV, the public input and the
stream). -/
def Rel (π : KeccakState → KeccakState) (iv pub : List UInt8) (stream : Array UInt8) (st : RecGraph.RecState)
    (i : ℕ) (x : E) : Prop :=
  i < st.nodes.size ∧ RecGraph.valE (RecGraph.evalAll π iv pub stream st) i = x

namespace WeightSim

section Sim

/-- **`st'` extends `st`** as the recorder's operations do: the invariant holds at `st'`, `st'` grows `st`, and the
kernels are unchanged. -/
structure Ext (st st' : RecState) : Prop where
  inv : RecInv st'
  grows : Grows st st'
  kernels : st'.kernels = st.kernels

theorem Ext.refl {st : RecState} (h : RecInv st) : Ext st st := ⟨h, Grows.refl st, rfl⟩

theorem Ext.trans {a b c : RecState} (h1 : Ext a b) (h2 : Ext b c) : Ext a c :=
  ⟨h2.inv, h1.grows.trans h2.grows, h2.kernels.trans h1.kernels⟩

theorem grows_size {st st' : RecState} (h : Grows st st') : st.nodes.size ≤ st'.nodes.size := by
  obtain ⟨⟨ys, e⟩, _⟩ := h
  have := congrArg List.length e
  simp only [Array.length_toList, List.length_append] at this
  omega

/-- The result of `c` run from `st`, and the state after it. -/
abbrev runSM {α : Type} (c : SM α) (st : RecState) : α × RecState := c.run st

/-- **`c` run from `st` simulates `v`**: the state reached extends `st`, and the result is related to `v` by `Q` at
the state reached. -/
structure Sim {α β : Type} (st : RecState) (c : SM α) (v : Id β) (Q : RecState → α → β → Prop) : Prop where
  ext : Ext st (runSM c st).2
  rel : Q (runSM c st).2 (runSM c st).1 v.run

theorem Sim.pure {α β : Type} {st : RecState} {a : α} {b : β} {Q : RecState → α → β → Prop} (h : RecInv st)
    (hq : Q st a b) : Sim st (Pure.pure a) (Pure.pure b) Q :=
  ⟨Ext.refl h, hq⟩

theorem Sim.bind {α β γ δ : Type} {st : RecState} {c : SM α} {k : α → SM β} {v : Id γ} {k' : γ → Id δ}
    {Q : RecState → α → γ → Prop} {R : RecState → β → δ → Prop}
    (hc : Sim st c v Q) (hk : ∀ st₁ a a', Ext st st₁ → Q st₁ a a' → Sim st₁ (k a) (k' a') R) :
    Sim st (c >>= k) (v >>= k') R :=
  have h2 := hk _ _ _ hc.ext hc.rel
  ⟨hc.ext.trans h2.ext, h2.rel⟩

/-- An `if` whose branches meet at a join point `K` (`do`'s `if` without `else` on a mutable variable). -/
theorem Sim.jp {α β γ δ : Type} {st : RecState} {c : Prop} [Decidable c] {x : SM α} {x' : Id β}
    {K : α → SM γ} {K' : β → Id δ} {a : α} {a' : β} {P : RecState → α → β → Prop} {Q : RecState → γ → δ → Prop}
    (h : RecInv st) (hx : c → Sim st x x' P) (ha : ¬c → P st a a')
    (hK : ∀ st₁ b b', Ext st st₁ → P st₁ b b' → Sim st₁ (K b) (K' b') Q) :
    Sim st (if c then x >>= K else K a) (if c then x' >>= K' else K' a') Q := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]
    exact Sim.bind (hx hc) hK
  · simp only [hc, ↓reduceIte]
    exact hK st a a' (Ext.refl h) (ha hc)

/-- A loop step's relation: both yield, or both stop, with related values. -/
def StepRel {β β' : Type} (R : RecState → β → β' → Prop) (st : RecState) : ForInStep β → ForInStep β' → Prop
  | .yield b, .yield b' => R st b b'
  | .done b, .done b' => R st b b'
  | _, _ => False

/-- **A loop over two related lists**, whose body keeps the loop's relation `R` (`E`, the elements' relation, is
monotone). -/
theorem Sim.forIn_list {α α' β β' : Type} {st₀ : RecState} (E : RecState → α → α' → Prop)
    (R : RecState → β → β' → Prop) {f : α → β → SM (ForInStep β)} {f' : α' → β' → Id (ForInStep β')}
    (hE : ∀ st st' a a', RecInv st → Ext st st' → E st a a' → E st' a a')
    (hf : ∀ st a a' b b', Ext st₀ st → E st a a' → R st b b' → Sim st (f a b) (f' a' b') (StepRel R)) :
    ∀ (l : List α) (l' : List α') (st : RecState) (b : β) (b' : β'), Ext st₀ st → List.Forall₂ (E st) l l' →
      R st b b' → Sim st (forIn l b f) (forIn l' b' f') R := by
  intro l
  induction l with
  | nil =>
    intro l' st b b' hst hl hb
    cases hl
    rw [List.forIn_nil, List.forIn_nil]
    exact Sim.pure hst.inv hb
  | cons a as ih =>
    intro l' st b b' hst hl hb
    cases hl with
    | cons ha has =>
      rw [List.forIn_cons, List.forIn_cons]
      refine Sim.bind (hf st _ _ b b' hst ha hb) ?_
      intro st₁ x x' h1 hx
      cases x <;> cases x' <;> simp only [StepRel] at hx
      · exact Sim.pure h1.inv hx
      · exact ih _ st₁ _ _ (hst.trans h1) (has.imp fun a a' => hE st st₁ a a' hst.inv h1) hx

/-- **A loop over a range.** -/
theorem Sim.forIn_range {β β' : Type} {st₀ : RecState} (r : Std.Legacy.Range) (R : RecState → β → β' → Prop)
    {f : ℕ → β → SM (ForInStep β)} {f' : ℕ → β' → Id (ForInStep β')}
    (hf : ∀ st (i : ℕ) b b', Ext st₀ st → R st b b' → Sim st (f i b) (f' i b') (StepRel R))
    (b : β) (b' : β') (h : RecInv st₀) (hb : R st₀ b b') : Sim st₀ (forIn r b f) (forIn r b' f') R := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  refine Sim.forIn_list (fun _ a a' => a = a') R (fun _ _ _ _ _ _ e => e) ?_ _ _ st₀ b b' (Ext.refl h)
    (List.forall₂_same.2 fun _ _ => rfl) hb
  intro st a a' c c' hst e hc
  subst e
  exact hf st a c c' hst hc

/-- The recorder's node constructor keeps the kernels. -/
theorem new_kernels (st : RecState) (n : RecGraph.Node) : (st.new n).2.kernels = st.kernels := by
  unfold RecGraph.RecState.new
  split <;> rfl

theorem add_kernels (st : RecState) (a b : ℕ) : (st.add a b).2.kernels = st.kernels := by
  unfold RecGraph.RecState.add
  split
  · exact new_kernels _ _
  · split
    · rfl
    · split
      · rfl
      · split
        · exact new_kernels _ _
        · exact new_kernels _ _

theorem mul_kernels (st : RecState) (a b : ℕ) : (st.mul a b).2.kernels = st.kernels := by
  unfold RecGraph.RecState.mul
  split
  · exact new_kernels _ _
  · split
    · exact new_kernels _ _
    · split
      · rfl
      · split
        · rfl
        · exact new_kernels _ _

theorem forall₂_zip {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} :
    ∀ {l : List α} {l' : List β} {m : List γ} {m' : List δ}, List.Forall₂ R l l' → List.Forall₂ S m m' →
      List.Forall₂ (fun p q => R p.1 q.1 ∧ S p.2 q.2) (l.zip m) (l'.zip m')
  | _, _, _, _, .nil, _ => by rw [List.zip_nil_left, List.zip_nil_left]; exact .nil
  | _, _, _, _, .cons _ _, .nil => by rw [List.zip_nil_right, List.zip_nil_right]; exact .nil
  | _, _, _, _, .cons h1 t1, .cons h2 t2 => by
    rw [List.zip_cons_cons, List.zip_cons_cons]; exact .cons ⟨h1, h2⟩ (forall₂_zip t1 t2)

variable (π : KeccakState → KeccakState) (iv pub : List UInt8) (stream : Array UInt8)

/-- **`Rel` is monotone**: a symbol keeps its value as the recorder's state grows. -/
theorem Rel.mono {st st' : RecState} (h : RecInv st) (e : Ext st st') {i : ℕ} {x : E}
    (r : Rel π iv pub stream st i x) : Rel π iv pub stream st' i x :=
  ⟨lt_of_lt_of_le r.1 (grows_size e.grows),
    (RecGraph.valE_congr (RecGraph.evalAll_grows π iv pub stream st st' h.kinv e.grows i r.1)).trans r.2⟩

theorem Rel.mono₂ {st st' : RecState} (h : RecInv st) (e : Ext st st') {l : List ℕ} {l' : List E}
    (r : List.Forall₂ (Rel π iv pub stream st) l l') : List.Forall₂ (Rel π iv pub stream st') l l' :=
  r.imp fun _ _ => Rel.mono π iv pub stream h e

/-- An array of symbols denotes an array of values: the same size, and entry by entry (`getD _ 0`). -/
structure ArrRel (st : RecState) (g : Array ℕ) (g' : Array E) : Prop where
  size : g.size = g'.size
  get : ∀ i, Rel π iv pub stream st (g.getD i 0) (g'.getD i 0)

theorem ArrRel.mono {st st' : RecState} (h : RecInv st) (e : Ext st st') {g : Array ℕ} {g' : Array E}
    (r : ArrRel π iv pub stream st g g') : ArrRel π iv pub stream st' g g' :=
  ⟨r.size, fun i => Rel.mono π iv pub stream h e (r.get i)⟩

theorem ArrRel.zero {st : RecState} {g : Array ℕ} {g' : Array E} (r : ArrRel π iv pub stream st g g') :
    Rel π iv pub stream st 0 0 := by
  have := r.get g.size
  rwa [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_refl _),
    Array.getElem?_eq_none (Nat.le_of_eq r.size.symm), Option.getD_none, Option.getD_none] at this

theorem ArrRel.empty {st : RecState} (h0 : Rel π iv pub stream st 0 0) : ArrRel π iv pub stream st #[] #[] :=
  ⟨rfl, fun i => by
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
    simpa using h0⟩

theorem ArrRel.push {st : RecState} {g : Array ℕ} {g' : Array E} {a : ℕ} {a' : E}
    (r : ArrRel π iv pub stream st g g') (ha : Rel π iv pub stream st a a') :
    ArrRel π iv pub stream st (g.push a) (g'.push a') := by
  refine ⟨by simp [r.size], fun i => ?_⟩
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_push, Array.getElem?_push]
  by_cases hi : i = g.size
  · have hi' : i = g'.size := hi.trans r.size
    rw [ite_eq_left_of_eq_true _ _ (eq_true hi), ite_eq_left_of_eq_true _ _ (eq_true hi')]
    exact ha
  · have hi' : ¬ i = g'.size := fun e => hi (e.trans r.size.symm)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hi), ite_eq_right_of_eq_false _ _ (eq_false hi'),
      ← Array.getD_eq_getD_getElem?, ← Array.getD_eq_getD_getElem?]
    exact r.get i

theorem ArrRel.set {st : RecState} {g : Array ℕ} {g' : Array E} {s : ℕ} {s' : E}
    (r : ArrRel π iv pub stream st g g') (hs : Rel π iv pub stream st s s') (k : ℕ) :
    ArrRel π iv pub stream st (g.set! k s) (g'.set! k s') := by
  refine ⟨by simp [r.size], fun i => ?_⟩
  rw [Array.set!_eq_setIfInBounds, Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases hk : k = i
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hk), ite_eq_left_of_eq_true _ _ (eq_true hk)]
    by_cases hlt : k < g.size
    · have hlt' : k < g'.size := r.size ▸ hlt
      rw [ite_eq_left_of_eq_true _ _ (eq_true hlt), ite_eq_left_of_eq_true _ _ (eq_true hlt')]
      exact hs
    · have hlt' : ¬ k < g'.size := r.size ▸ hlt
      rw [ite_eq_right_of_eq_false _ _ (eq_false hlt), ite_eq_right_of_eq_false _ _ (eq_false hlt')]
      exact ArrRel.zero π iv pub stream r
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hk), ite_eq_right_of_eq_false _ _ (eq_false hk),
      ← Array.getD_eq_getD_getElem?, ← Array.getD_eq_getD_getElem?]
    exact r.get i

/-! ### The operations -/

theorem sim_add {st : RecState} (h : RecInv st) {a b : ℕ} {x y : E} (ha : Rel π iv pub stream st a x)
    (hb : Rel π iv pub stream st b y) : Sim st (symAdd a b) (pure (x + y) : Id E) (Rel π iv pub stream) :=
  ⟨⟨RecGraph.add_inv st h a b ha.1 hb.1, (RecGraph.op_grows_kinv st (.add a b) h.kinv).1, add_kernels st a b⟩,
    RecGraph.op_lt st h (.add a b) ⟨ha.1, hb.1⟩,
    (RecGraph.add_val π iv pub stream st h a b ha.1 hb.1).trans (by rw [ha.2, hb.2]; rfl)⟩

theorem sim_mul {st : RecState} (h : RecInv st) {a b : ℕ} {x y : E} (ha : Rel π iv pub stream st a x)
    (hb : Rel π iv pub stream st b y) : Sim st (symMul a b) (pure (x * y) : Id E) (Rel π iv pub stream) :=
  ⟨⟨RecGraph.mul_inv st h a b ha.1 hb.1, (RecGraph.op_grows_kinv st (.mul a b) h.kinv).1, mul_kernels st a b⟩,
    RecGraph.op_lt st h (.mul a b) ⟨ha.1, hb.1⟩,
    (RecGraph.mul_val π iv pub stream st h a b ha.1 hb.1).trans (by rw [ha.2, hb.2]; rfl)⟩

theorem sim_one {st : RecState} (h : RecInv st) : Sim st symOne (pure 1 : Id E) (Rel π iv pub stream) :=
  ⟨⟨RecGraph.constant_inv st h 1, (RecGraph.op_grows_kinv st (.constant 1) h.kinv).1, new_kernels _ _⟩,
    RecGraph.op_lt st h (.constant 1) trivial, RecGraph.constant_val π iv pub stream st h 1⟩

theorem Sim.mapM {st₀ : RecState} {f : ℕ → SM ℕ} {f' : E → Id E}
    (hf : ∀ st a a', Ext st₀ st → Rel π iv pub stream st a a' → Sim st (f a) (f' a') (Rel π iv pub stream)) :
    ∀ (l : List ℕ) (l' : List E) (st : RecState), Ext st₀ st → List.Forall₂ (Rel π iv pub stream st) l l' →
      Sim st (l.mapM f) (l'.mapM f') (fun st r r' => List.Forall₂ (Rel π iv pub stream st) r r') := by
  intro l
  induction l with
  | nil =>
    intro l' st hst hl
    cases hl
    rw [List.mapM_nil, List.mapM_nil]
    exact Sim.pure hst.inv List.Forall₂.nil
  | cons a as ih =>
    intro l' st hst hl
    cases hl with
    | cons ha has =>
      rw [List.mapM_cons, List.mapM_cons]
      refine Sim.bind (hf st _ _ hst ha) fun st₁ x x' h1 hx => ?_
      refine Sim.bind (ih _ st₁ (hst.trans h1) (Rel.mono₂ π iv pub stream hst.inv h1 has))
        fun st₂ xs xs' h2 hxs => ?_
      exact Sim.pure h2.inv (List.Forall₂.cons (Rel.mono π iv pub stream h1.inv h2 hx) hxs)

theorem sim_frob (t : ℕ) : ∀ (st : RecState) (p : ℕ) (p' : E), RecInv st → Rel π iv pub stream st p p' →
    Sim st (frobeniusM symMul p t) (frobeniusM (m := Id) (fun a b : E => (pure (a * b) : Id E)) p' t)
      (Rel π iv pub stream) := by
  induction t with
  | zero => intro st p p' h hp; exact Sim.pure h hp
  | succ t ih =>
    intro st p p' h hp
    exact Sim.bind (sim_mul π iv pub stream h hp hp) fun st₁ v v' h1 hv => ih st₁ v v' h1.inv hv

/-! ### The weight -/

/-- The 64 products, on symbols and on `E`. -/
theorem sim_gs {st₀ : RecState} (h : RecInv st₀) (h0 : Rel π iv pub stream st₀ 0 0) {ps os : List ℕ}
    {xs ys : List E} (hp : List.Forall₂ (Rel π iv pub stream st₀) ps xs)
    (ho : List.Forall₂ (Rel π iv pub stream st₀) os ys) :
    Sim st₀ (weightGs symAdd symMul symOne ps os)
      (weightGs (m := Id) (fun a b : E => (pure (a + b) : Id E)) (fun a b => pure (a * b)) (pure 1) xs ys)
      (ArrRel π iv pub stream) := by
  unfold weightGs
  dsimp only
  refine Sim.bind (Sim.forIn_range _ (fun st (s : List ℕ × Array ℕ) (s' : List E × Array E) =>
      List.Forall₂ (Rel π iv pub stream st) s.1 s'.1 ∧ ArrRel π iv pub stream st s.2 s'.2) ?_ _ _ h
      ⟨hp, ArrRel.empty π iv pub stream h0⟩) fun st₁ s s' e1 hs => Sim.pure e1.inv hs.2
  rintro st₁ k ⟨chain, g⟩ ⟨chain', g'⟩ e1 ⟨hc, hg⟩
  dsimp only
  apply Sim.jp e1.inv (P := fun st r r' => List.Forall₂ (Rel π iv pub stream st) r r')
  · intro _
    exact Sim.mapM π iv pub stream (fun st a a' e r => sim_mul π iv pub stream e.inv r r) _ _ st₁
      (Ext.refl e1.inv) hc
  · intro _
    exact hc
  · intro st₂ c c' e2 hcc
    refine Sim.bind (sim_one π iv pub stream e2.inv) fun st₃ acc acc' e3 hacc => ?_
    refine Sim.bind (Sim.forIn_list (st₀ := st₃)
      (fun st (x : ℕ × ℕ) (x' : E × E) => Rel π iv pub stream st x.1 x'.1 ∧ Rel π iv pub stream st x.2 x'.2)
      (Rel π iv pub stream) ?_ ?_ _ _ st₃ acc acc' (Ext.refl e3.inv)
      (forall₂_zip (Rel.mono₂ π iv pub stream e2.inv e3 hcc)
        (Rel.mono₂ π iv pub stream h (e1.trans (e2.trans e3)) ho)) hacc) fun st₄ a4 a4' e4 h4 => ?_
    · intro st st' a a' hi e ha
      exact ⟨Rel.mono π iv pub stream hi e ha.1, Rel.mono π iv pub stream hi e ha.2⟩
    · rintro st ⟨c, a⟩ ⟨c', a'⟩ b b' e ⟨hc1, ha1⟩ hb
      dsimp only
      exact Sim.bind (sim_add π iv pub stream e.inv ha1 hc1) fun st₅ u u' e5 hu =>
        Sim.bind (sim_mul π iv pub stream e5.inv (Rel.mono π iv pub stream e.inv e5 hb) hu)
          fun st₆ w w' e6 hw => Sim.pure e6.inv hw
    · exact Sim.pure e4.inv ⟨Rel.mono₂ π iv pub stream e3.inv e4 (Rel.mono₂ π iv pub stream e2.inv e3 hcc),
        ArrRel.push π iv pub stream (ArrRel.mono π iv pub stream e1.inv (e2.trans (e3.trans e4)) hg) h4⟩

/-- The weight, on symbols and on `E`. -/
theorem sim_weight {st₀ : RecState} (h : RecInv st₀) (h0 : Rel π iv pub stream st₀ 0 0) {ps os ms : List ℕ}
    {xs ys zs : List E} (hp : List.Forall₂ (Rel π iv pub stream st₀) ps xs)
    (ho : List.Forall₂ (Rel π iv pub stream st₀) os ys) (hm : List.Forall₂ (Rel π iv pub stream st₀) ms zs) :
    Sim st₀ (weightAtM symAdd symMul symOne 0 ps os ms)
      (weightAtM (m := Id) (fun a b : E => (pure (a + b) : Id E)) (fun a b => pure (a * b)) (pure 1) 0 xs ys zs)
      (Rel π iv pub stream) := by
  unfold weightAtM
  dsimp only
  refine Sim.bind (sim_gs π iv pub stream h h0 hp ho) fun st₁ g g' e1 hg => ?_
  refine Sim.bind (Sim.forIn_list (st₀ := st₁) (Rel π iv pub stream)
      (fun st (s : Array ℕ × ℕ) (s' : Array E × ℕ) => ArrRel π iv pub stream st s.1 s'.1 ∧ s.2 = s'.2)
      (fun _ _ _ _ hi e r => Rel.mono π iv pub stream hi e r) ?_ ms zs st₁ (g, 0) (g', 0) (Ext.refl e1.inv)
      (Rel.mono₂ π iv pub stream h e1 hm) ⟨hg, rfl⟩) fun st₂ s s' e2 hs => Sim.pure e2.inv (hs.1.get 0)
  rintro st₂ f f' ⟨g, j⟩ ⟨g', j'⟩ e2 hf ⟨hg, hj⟩
  obtain rfl : j = j' := hj
  dsimp only
  refine Sim.bind (Sim.forIn_range _ (fun st (s : Array ℕ × ℕ) (s' : Array E × E) =>
      ArrRel π iv pub stream st s.1 s'.1 ∧ Rel π iv pub stream st s.2 s'.2) ?_ _ _ e2.inv ⟨hg, hf⟩)
    fun st₃ s s' e3 hs => Sim.pure e3.inv ⟨hs.1, rfl⟩
  rintro st₃ t ⟨g, p⟩ ⟨g', p'⟩ e3 ⟨hg, hp⟩
  dsimp only
  apply Sim.jp e3.inv (P := Rel π iv pub stream)
  · intro _
    exact sim_frob π iv pub stream _ st₃ p p' e3.inv hp
  · intro _
    exact hp
  · intro st₄ q q' e4 hq
    have hg4 := ArrRel.mono π iv pub stream e3.inv e4 hg
    refine Sim.bind (sim_mul π iv pub stream e4.inv hq (hg4.get _)) fun st₅ u u' e5 hu => ?_
    have hg5 := ArrRel.mono π iv pub stream e4.inv e5 hg4
    refine Sim.bind (sim_add π iv pub stream e5.inv (hg5.get _) hu) fun st₆ w w' e6 hw => ?_
    exact Sim.pure e6.inv ⟨ArrRel.set π iv pub stream (ArrRel.mono π iv pub stream e5.inv e6 hg5) hw _,
      Rel.mono π iv pub stream e4.inv (e5.trans e6) hq⟩

end Sim

end WeightSim

open WeightSim in
/-- **(B) The symbolic run simulates the E-level one**: run from a state with the recorder's invariant, on symbols
denoting the point, `1 + r` and the map, `weight_at` keeps the invariant, grows the state, keeps its kernels, and
returns a symbol denoting `weightAt` of their values. -/
theorem weightSym_sim (π : KeccakState → KeccakState) (iv pub : List UInt8) (stream : Array UInt8)
    (st : RecGraph.RecState) (h : RecGraph.RecInv st) (h0 : Rel π iv pub stream st 0 0)
    {ps os ms : List ℕ} {xs ys zs : List F192}
    (hp : List.Forall₂ (Rel π iv pub stream st) ps xs) (ho : List.Forall₂ (Rel π iv pub stream st) os ys)
    (hm : List.Forall₂ (Rel π iv pub stream st) ms zs) :
    RecGraph.RecInv (weightRun st ps os ms).2 ∧ RecGraph.Grows st (weightRun st ps os ms).2 ∧
      (weightRun st ps os ms).2.kernels = st.kernels ∧
      Rel π iv pub stream (weightRun st ps os ms).2 (weightRun st ps os ms).1 (weightAt xs ys zs) := by
  have hs := sim_weight π iv pub stream h h0 hp ho hm
  exact ⟨hs.ext.inv, hs.ext.grows, hs.ext.kernels, hs.rel⟩

end RecCircuit
