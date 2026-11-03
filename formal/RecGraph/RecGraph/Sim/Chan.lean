-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.Arith

/-!
# The simulation's judgment, and the channel's operations

**The judgment** `Sim π iv publicInput stream st p u n ch R`: from the recorder state `st`, the program part `p`
simulates `UniStatement`'s `u` (in `ChanM Id`, over `Fp π`), reading `n` bytes and drawing `ch` challenges, its
outputs related by `R`. For every channel `c` coupled with `st` (`Couple`) whose cursor is in the stream:

* with `n` bytes left, `u` succeeds, its final channel coupled with `p`'s recorded state, the cursor `n` further, the
  challenges `ch` more, the recorder's state grown, the outputs related;
* with fewer, `u` fails.

The cursor in the stream (`c.cursor ≤ c.data.size`) is an assumption of the judgment (the brief's had none): without
it a part that reads nothing could not fail when the cursor is past the stream's end, and the failure clause would be
false of `pure`. Every channel the verifier reaches has it (`Chan.start` at `0`; a read only within the stream).

**Its rules**: `Sim.bind` (both clauses compose; the bytes and the challenges add), `Sim.pure_of_pstep` (a pure part,
`PStep`, against `pure`), `Sim.of_psim`, `Sim.map`, `Sim.mono`, `Sim.congr`, `Sim.cast`, `Sim.forIn_list` (a `for`
loop on both sides, indexed invariant, both bodies yielding). The pure parts' judgment is `PSim st p b R` (a pure
step, its output related to `b`), with `PSim.bind`, `PSim.pure`, `PSim.forIn_list` (against a `foldl`),
`PSim.forIn_inv` (an invariant only) and the arithmetic operations (`PSim.add`, `mul`, `const`, `zero`, `one`,
`square`, `bits`, `statement`).

**The channel's operations**, as `Sim` instances: `sim_input` (any read), `sim_nextScalar`, `sim_nextInteger`,
`sim_nextRoot`, `sim_sampleDrawn` (`sim_sample`, `sim_sampleNarrow`: the challenge node new, the channel's challenge
pushed, `chIds` grown by it), `sim_requireZero`, `sim_nextScalars`, `sim_samples`; the start, `start_couple`, and the
public input's words, `statementWords_psim`, `start_sim`.
-/

-- The judgment is `RecGraph.Sim.Sim` (the brief's name, in the framework's namespace), and its rules `Sim.bind`, ….
set_option linter.dupNamespace false

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

/-- **The permutation as `UniStatement`'s `F`**: `π` in `Id`. -/
abbrev Fp (π : KeccakState → KeccakState) : KeccakState → Id KeccakState := fun s ↦ pure (π s)

/-! ## The program monad's laws -/

theorem prog_pure_bind {α β : Type} (a : α) (k : α → Prog β) : (pure a >>= k : Prog β) = k a := rfl

theorem prog_bind_pure {α : Type} (p : Prog α) : (p >>= pure : Prog α) = p := by
  induction p with
  | pure a => rfl
  | op o k ih =>
    show Prog.op o (fun i ↦ (k i).bind pure) = _
    congr 1; funext i; exact ih i
  | zero v k ih =>
    show Prog.zero v (k.bind pure) = _
    exact congrArg _ ih
  | nonzero v k ih =>
    show Prog.nonzero v (k.bind pure) = _
    exact congrArg _ ih

theorem prog_bind_assoc {α β γ : Type} (p : Prog α) (f : α → Prog β) (g : β → Prog γ) :
    (p >>= f >>= g : Prog γ) = p >>= fun a ↦ f a >>= g := by
  induction p with
  | pure a => rfl
  | op o k ih =>
    show Prog.op o (fun i ↦ ((k i).bind f).bind g) = Prog.op o (fun i ↦ (k i).bind fun a ↦ (f a).bind g)
    congr 1; funext i; exact ih i
  | zero v k ih =>
    show Prog.zero v ((k.bind f).bind g) = Prog.zero v (k.bind fun a ↦ (f a).bind g)
    exact congrArg _ ih
  | nonzero v k ih =>
    show Prog.nonzero v ((k.bind f).bind g) = Prog.nonzero v (k.bind fun a ↦ (f a).bind g)
    exact congrArg _ ih

instance Prog.instLawfulMonad : LawfulMonad Prog :=
  LawfulMonad.mk' Prog (fun x ↦ prog_bind_pure x) (fun _ _ ↦ rfl) prog_bind_assoc

theorem record_map {α β : Type} (p : Prog α) (f : α → β) (st : RecState) :
    (p >>= fun a ↦ pure (f a)).record st = (f (p.record st).1, (p.record st).2) := by
  rw [record_bind]; rfl

/-! ## The channel's runs in `Id` -/

theorem run_bind {β γ : Type} (u : ChanM Id β) (f : β → ChanM Id γ) (c : Chan) :
    ((u >>= f).run).run c = match (u.run).run c with
      | (.ok b, c') => ((f b).run).run c'
      | (.error e, c') => (.error e, c') := by
  rw [ExceptT.run_bind, StateT.run_bind]
  rcases (u.run).run c with ⟨r, c'⟩
  cases r <;> rfl

theorem run_bind_ok {β γ : Type} {u : ChanM Id β} (f : β → ChanM Id γ) {c c' : Chan} {b : β}
    (h : (u.run).run c = (.ok b, c')) : ((u >>= f).run).run c = ((f b).run).run c' := by
  rw [run_bind, h]

theorem run_bind_error {β γ : Type} {u : ChanM Id β} (f : β → ChanM Id γ) {c c' : Chan} {e : UniError}
    (h : (u.run).run c = (.error e, c')) : ((u >>= f).run).run c = (.error e, c') := by
  rw [run_bind, h]

theorem run_pure {β : Type} (b : β) (c : Chan) : ((pure b : ChanM Id β).run).run c = (.ok b, c) := rfl

/-- `takeBytes n` with the bytes there. -/
theorem takeBytes_run (n : Nat) (c : Chan) (hr : c.cursor + n ≤ c.data.size) :
    ((takeBytes (m := Id) n).run).run c =
      (.ok (c.data.extract c.cursor (c.cursor + n)), { c with cursor := c.cursor + n }) := by
  unfold takeBytes
  simp only [ExceptT.run, StateT.run, bind, ExceptT.bind, ExceptT.mk, StateT.bind, get, getThe, MonadStateOf.get,
    ExceptT.lift, liftM, monadLift, MonadLift.monadLift, pure, ExceptT.pure]
  simp only [Functor.map, StateT.map, StateT.get, ExceptT.bindCont]
  simp only [pure_bind]
  rw [show (pure (Except.ok c, c) : Id (Except UniError Chan × Chan)) = (Except.ok c, c) from rfl]
  dsimp only
  simp only [hr, ↓reduceIte]
  rfl

/-- `takeBytes n` without: `StreamExhausted`. -/
theorem takeBytes_fail (n : Nat) (c : Chan) (hr : c.data.size < c.cursor + n) :
    ((takeBytes (m := Id) n).run).run c = (.error .streamExhausted, c) := by
  unfold takeBytes
  simp only [ExceptT.run, StateT.run, bind, ExceptT.bind, ExceptT.mk, StateT.bind, get, getThe, MonadStateOf.get,
    ExceptT.lift, liftM, monadLift, MonadLift.monadLift, pure, ExceptT.pure]
  simp only [Functor.map, StateT.map, StateT.get, ExceptT.bindCont]
  simp only [pure_bind]
  rw [show (pure (Except.ok c, c) : Id (Except UniError Chan × Chan)) = (Except.ok c, c) from rfl]
  dsimp only
  simp only [Nat.not_le.mpr hr, ↓reduceIte]
  rfl

/-- The channel's next state, at a challenge: the Keccak-256 over `π` of its state and the bytes read since. -/
def hashOf (π : KeccakState → KeccakState) (c : Chan) : Digest :=
  Id.run (keccak256With (Fp π) (digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList))

/-- The challenge drawn at `c`, narrow or not. -/
def chalOf (π : KeccakState → KeccakState) (narrow : Bool) (c : Chan) : E :=
  (if narrow then narrowE else id) (PcsQuotient.Transcript.challengeOf (hashOf π c))

/-- **`sample` / `sampleNarrow`'s run**: the challenge, the state, the bytes absorbed, the challenge pushed. -/
theorem sampleDrawn_run (π : KeccakState → KeccakState) (narrow : Bool) (c : Chan) :
    ((sampleDrawn (Fp π) narrow).run).run c =
      (.ok (chalOf π narrow c),
        { c with
          absorbed := c.cursor
          state := hashOf π c
          challenges := c.challenges.push (chalOf π narrow c) }) := by
  cases narrow <;> rfl

theorem requireZero_run (x : E) (c : Chan) :
    ((UniStatement.requireZero (m := Id) x).run).run c = (.ok (), { c with zeros := c.zeros.push x }) := rfl

/-! ## Nodes -/

/-- The index `Sym::new(n)` returns holds `n`. -/
theorem new_get (st : RecState) (h : RecInv st) (n : Node) : (st.new n).2.nodes[(st.new n).1]? = some n := by
  unfold RecState.new
  split
  · rename_i i hi
    exact h.index n i hi
  · simp

/-- A node held stays as the state grows. -/
theorem nodes_grow {st st' : RecState} (h : Grows st st') {i : Nat} {n : Node} (hn : st.nodes[i]? = some n) :
    st'.nodes[i]? = some n := by
  obtain ⟨⟨ys, e⟩, _⟩ := h
  have hi : i < st.nodes.size := by
    rcases Nat.lt_or_ge i st.nodes.size with h | h
    · exact h
    · simp [Array.getElem?_eq_none h] at hn
  rw [← Array.getElem?_toList, e, List.getElem?_append_left (by simpa using hi), Array.getElem?_toList, hn]

theorem chIds_lt {st : RecState} {i : Nat} (h : i ∈ chIds st) : i < st.nodes.size := by
  unfold chIds at h
  simp only [List.mem_map, List.mem_filter] at h
  obtain ⟨⟨n, j⟩, ⟨hm, _⟩, rfl⟩ := h
  exact List.mem_range.mp (List.of_mem_zip hm).2

section Judgment

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- **Program part `p` from `st` simulates `UniStatement`'s `u`**, reading `n` bytes and drawing `ch` challenges,
outputs related by `R`: from every channel coupled with `st`, its cursor in the stream. -/
def Sim (st : RecState) {α β : Type} (p : Prog α) (u : ChanM Id β) (n ch : Nat)
    (R : RecState → α → β → Prop) : Prop :=
  ∀ c, Couple π iv publicInput stream st c → c.cursor ≤ c.data.size →
    (c.cursor + n ≤ c.data.size →
      ∃ b c', (u.run).run c = (.ok b, c') ∧ Couple π iv publicInput stream (p.record st).2 c' ∧
        c'.cursor = c.cursor + n ∧ c'.challenges.size = c.challenges.size + ch ∧
        Grows st (p.record st).2 ∧ R (p.record st).2 (p.record st).1 b) ∧
    (c.data.size < c.cursor + n → ∃ e c', (u.run).run c = (.error e, c'))

/-- **A pure program part**: a pure step, its output related to `b` by `R`. -/
def PSim (st : RecState) {α β : Type} (p : Prog α) (b : β) (R : RecState → α → β → Prop) : Prop :=
  PStep st (p.record st).2 ∧ R (p.record st).2 (p.record st).1 b

variable {π iv publicInput stream}

/-! ## The judgment's rules -/

theorem Sim.bind {st : RecState} {α β γ δ : Type} {p : Prog α} {u : ChanM Id β} {n ch : Nat}
    {R : RecState → α → β → Prop} {k : α → Prog γ} {f : β → ChanM Id δ} {m ch' : Nat}
    {S : RecState → γ → δ → Prop}
    (h1 : Sim π iv publicInput stream st p u n ch R)
    (h2 : ∀ st' a b, Good st' → Grows st st' → R st' a b → Sim π iv publicInput stream st' (k a) (f b) m ch' S) :
    Sim π iv publicInput stream st (p >>= k) (u >>= f) (n + m) (ch + ch') S := by
  intro c hc hle
  obtain ⟨hs1, hf1⟩ := h1 c hc hle
  rw [record_bind]
  refine ⟨fun hr ↦ ?_, fun hr ↦ ?_⟩
  · obtain ⟨b, c', hu, hc', hcur, hch, hg, hR⟩ := hs1 (by omega)
    have hd : c'.data = c.data := hc'.data.trans hc.data.symm
    obtain ⟨hs2, _⟩ := h2 _ _ _ hc'.good hg hR c' hc' (by rw [hd, hcur]; omega)
    obtain ⟨b2, c2, hu2, hc2, hcur2, hch2, hg2, hS⟩ := hs2 (by rw [hd, hcur]; omega)
    exact ⟨b2, c2, by rw [run_bind_ok f hu, hu2], hc2, by rw [hcur2, hcur, Nat.add_assoc],
      by rw [hch2, hch, Nat.add_assoc], hg.trans hg2, hS⟩
  · by_cases h : c.data.size < c.cursor + n
    · obtain ⟨e, c', hu⟩ := hf1 h
      exact ⟨e, c', run_bind_error f hu⟩
    · obtain ⟨b, c', hu, hc', hcur, _, hg, hR⟩ := hs1 (by omega)
      have hd : c'.data = c.data := hc'.data.trans hc.data.symm
      obtain ⟨_, hf2⟩ := h2 _ _ _ hc'.good hg hR c' hc' (by rw [hd, hcur]; omega)
      obtain ⟨e, c2, hu2⟩ := hf2 (by rw [hd, hcur]; omega)
      exact ⟨e, c2, by rw [run_bind_ok f hu, hu2]⟩

/-- **A pure part against `pure`**: no byte read, no challenge drawn. -/
theorem Sim.pure_of_pstep {st : RecState} {α β : Type} {p : Prog α} {b : β} {R : RecState → α → β → Prop}
    (h : PStep st (p.record st).2) (hR : R (p.record st).2 (p.record st).1 b) :
    Sim π iv publicInput stream st p (pure b) 0 0 R := by
  intro c hc hle
  exact ⟨fun _ ↦ ⟨b, c, rfl, hc.pstep π iv publicInput stream h, (Nat.add_zero _).symm, (Nat.add_zero _).symm,
    h.grows, hR⟩, fun hr ↦ absurd hr (by omega)⟩

theorem Sim.of_psim {st : RecState} {α β : Type} {p : Prog α} {b : β} {R : RecState → α → β → Prop}
    (h : PSim st p b R) : Sim π iv publicInput stream st p (pure b) 0 0 R :=
  Sim.pure_of_pstep h.1 h.2

theorem Sim.cast {st : RecState} {α β : Type} {p : Prog α} {u : ChanM Id β} {n n' ch ch' : Nat}
    {R : RecState → α → β → Prop} (hn : n = n') (hch : ch = ch') (h : Sim π iv publicInput stream st p u n ch R) :
    Sim π iv publicInput stream st p u n' ch' R := by
  subst hn hch; exact h

theorem Sim.congr {st : RecState} {α β : Type} {p p' : Prog α} {u u' : ChanM Id β} {n ch : Nat}
    {R : RecState → α → β → Prop} (hp : p = p') (hu : u = u') (h : Sim π iv publicInput stream st p u n ch R) :
    Sim π iv publicInput stream st p' u' n ch R := by
  subst hp hu; exact h

theorem Sim.mono {st : RecState} {α β : Type} {p : Prog α} {u : ChanM Id β} {n ch : Nat}
    {R S : RecState → α → β → Prop} (h : Sim π iv publicInput stream st p u n ch R)
    (hRS : ∀ st' a b, Good st' → Grows st st' → R st' a b → S st' a b) :
    Sim π iv publicInput stream st p u n ch S := by
  intro c hc hle
  obtain ⟨hs, hf⟩ := h c hc hle
  refine ⟨fun hr ↦ ?_, hf⟩
  obtain ⟨b, c', hu, hc', hcur, hch, hg, hR⟩ := hs hr
  exact ⟨b, c', hu, hc', hcur, hch, hg, hRS _ _ _ hc'.good hg hR⟩

/-- **Mapping both outputs** by pure functions. -/
theorem Sim.map {st : RecState} {α β γ δ : Type} {p : Prog α} {u : ChanM Id β} {n ch : Nat}
    {R : RecState → α → β → Prop} {f : α → γ} {g : β → δ} {S : RecState → γ → δ → Prop}
    (h : Sim π iv publicInput stream st p u n ch R)
    (hS : ∀ st' a b, Good st' → Grows st st' → R st' a b → S st' (f a) (g b)) :
    Sim π iv publicInput stream st (p >>= fun a ↦ pure (f a)) (u >>= fun b ↦ pure (g b)) n ch S :=
  Sim.cast (Nat.add_zero n) (Nat.add_zero ch) (Sim.bind h fun st' a b hg hgr hR ↦
    Sim.pure_of_pstep (PStep.refl st' hg) (hS st' a b hg hgr hR))

/-- A judgment needing `Good st` holds: every coupled channel gives it. -/
theorem Sim.of_good {st : RecState} {α β : Type} {p : Prog α} {u : ChanM Id β} {n ch : Nat}
    {R : RecState → α → β → Prop} (h : Good st → Sim π iv publicInput stream st p u n ch R) :
    Sim π iv publicInput stream st p u n ch R :=
  fun c hc hle ↦ h hc.good c hc hle

theorem RpL.snoc {st : RecState} {is : List Nat} {xs : List E} {i : Nat} {x : E}
    (h : RpL π iv publicInput stream st is xs) (hi : Rp π iv publicInput stream st i x) :
    RpL π iv publicInput stream st (is ++ [i]) (xs ++ [x]) :=
  List.rel_append h (List.Forall₂.cons hi List.Forall₂.nil)

/-! ## `for` loops on both sides -/

/-- **A `for` loop, simulated**: over lists of the same length, each body simulating the other's from a state grown
from the loop's start, the invariant `I i` before iteration `i`, both bodies yielding. -/
theorem Sim.forIn_list {γ δ σ τ : Type} (st0 : RecState) :
    ∀ (xs : List γ) (ys : List δ) (I : Nat → RecState → σ → τ → Prop) (n ch : Nat → Nat)
      (body : γ → σ → Prog (ForInStep σ)) (ubody : δ → τ → ChanM Id (ForInStep τ)),
      xs.length = ys.length →
      (∀ i (hi : i < xs.length) (hj : i < ys.length) st s t, Good st → Grows st0 st → I i st s t →
        Sim π iv publicInput stream st (body xs[i] s) (ubody ys[i] t) (n i) (ch i)
          (fun st' r v ↦ ∃ s' t', r = .yield s' ∧ v = .yield t' ∧ I (i + 1) st' s' t')) →
      ∀ st s t, Good st → Grows st0 st → I 0 st s t →
        Sim π iv publicInput stream st (forIn xs s body) (forIn ys t ubody)
          (∑ i ∈ Finset.range xs.length, n i) (∑ i ∈ Finset.range xs.length, ch i) (I xs.length) := by
  intro xs
  induction xs with
  | nil =>
    intro ys I n ch body ubody hlen _ st s t hg _ hI
    cases ys with
    | cons _ _ => simp at hlen
    | nil =>
      rw [List.forIn_nil, List.forIn_nil]
      exact Sim.pure_of_pstep (PStep.refl st hg) hI
  | cons x xs ih =>
    intro ys I n ch body ubody hlen hbody st s t hg hgr hI
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      rw [List.forIn_cons, List.forIn_cons]
      have hlen' : xs.length = ys.length := by simpa using hlen
      refine Sim.cast (n := n 0 + ∑ i ∈ Finset.range xs.length, n (i + 1))
        (ch := ch 0 + ∑ i ∈ Finset.range xs.length, ch (i + 1))
        (by rw [List.length_cons, Finset.sum_range_succ', Nat.add_comm])
        (by rw [List.length_cons, Finset.sum_range_succ', Nat.add_comm]) ?_
      refine Sim.bind (hbody 0 (by simp) (by simp) st s t hg hgr hI) ?_
      rintro st' r v hg' hgr' ⟨s', t', rfl, rfl, hI'⟩
      exact ih ys (fun i ↦ I (i + 1)) (fun i ↦ n (i + 1)) (fun i ↦ ch (i + 1)) body ubody hlen'
        (fun i hi hj st s t hg hgr hI ↦ hbody (i + 1) (by simpa using hi) (by simpa using hj) st s t hg hgr hI)
        st' s' t' hg' (hgr.trans hgr') hI'

/-- `[a:b]`'s loop is the loop over `List.range' a (b - a)`. -/
theorem forIn_range {m : Type → Type} [Monad m] {β : Type} (a b : Nat) (init : β) (f : Nat → β → m (ForInStep β)) :
    forIn [a:b] init f = forIn (List.range' a (b - a)) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp [Std.Legacy.Range.size]

theorem sum_const_range (len c : Nat) : ∑ _i ∈ Finset.range len, c = c * len := by
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm]

/-! ## The pure parts' rules -/

theorem PSim.bind {st : RecState} {α β γ δ : Type} {p : Prog α} {b : β} {R : RecState → α → β → Prop}
    {k : α → Prog γ} {c : δ} {S : RecState → γ → δ → Prop}
    (h1 : PSim st p b R)
    (h2 : ∀ st' a, PStep st st' → R st' a b → PSim st' (k a) c S) :
    PSim st (p >>= k) c S := by
  obtain ⟨hp, hR⟩ := h1
  obtain ⟨hp2, hS⟩ := h2 _ _ hp hR
  show PStep st ((p >>= k).record st).2 ∧ S ((p >>= k).record st).2 ((p >>= k).record st).1 c
  rw [record_bind]
  exact ⟨hp.trans hp2, hS⟩

theorem PSim.pure {st : RecState} {α β : Type} {a : α} {b : β} {R : RecState → α → β → Prop} (hg : Good st)
    (hR : R st a b) : PSim st (pure a) b R :=
  ⟨PStep.refl st hg, hR⟩

theorem PSim.mono {st : RecState} {α β : Type} {p : Prog α} {b : β} {R S : RecState → α → β → Prop}
    (h : PSim st p b R) (hRS : ∀ st' a, PStep st st' → R st' a b → S st' a b) :
    PSim st p b S :=
  ⟨h.1, hRS _ _ h.1 h.2⟩

theorem PSim.congr {st : RecState} {α β : Type} {p p' : Prog α} {b b' : β} {R : RecState → α → β → Prop}
    (hp : p = p') (hb : b = b') (h : PSim st p b R) :
    PSim st p' b' R := by
  subst hp hb; exact h

/-- A node held before a pure step is held after it, worth the same. -/
theorem Rp.pgrow {st st' : RecState} (hg : Good st) (h : PStep st st') {i : Nat} {x : E}
    (hr : Rp π iv publicInput stream st i x) : Rp π iv publicInput stream st' i x :=
  hr.grow π iv publicInput stream hg.inv.kinv h.grows

theorem RpL.pgrow {st st' : RecState} (hg : Good st) (h : PStep st st') {is : List Nat} {xs : List E}
    (hr : RpL π iv publicInput stream st is xs) : RpL π iv publicInput stream st' is xs :=
  hr.grow π iv publicInput stream hg.inv.kinv h.grows

/-- **A `for` loop against a `foldl`**: the invariant `I i` before iteration `i`, the body yielding. -/
theorem PSim.forIn_list {γ δ σ τ : Type} (st0 : RecState) :
    ∀ (xs : List γ) (ys : List δ) (I : Nat → RecState → σ → τ → Prop)
      (body : γ → σ → Prog (ForInStep σ)) (g : τ → δ → τ),
      xs.length = ys.length →
      (∀ i (hi : i < xs.length) (hj : i < ys.length) st s t, PStep st0 st → I i st s t →
        PSim st (body xs[i] s) (g t ys[i])
          (fun st' r v ↦ ∃ s', r = .yield s' ∧ I (i + 1) st' s' v)) →
      ∀ st s t, PStep st0 st → I 0 st s t →
        PSim st (forIn xs s body) (ys.foldl g t) (I xs.length) := by
  intro xs
  induction xs with
  | nil =>
    intro ys I body g hlen _ st s t hst hI
    cases ys with
    | cons _ _ => simp at hlen
    | nil =>
      rw [List.forIn_nil]
      exact PSim.pure hst.good hI
  | cons x xs ih =>
    intro ys I body g hlen hbody st s t hst hI
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      rw [List.forIn_cons, List.foldl_cons]
      have hlen' : xs.length = ys.length := by simpa using hlen
      refine PSim.bind (hbody 0 (by simp) (by simp) st s t hst hI) ?_
      rintro st' r hst' ⟨s', rfl, hI'⟩
      exact ih ys (fun i ↦ I (i + 1)) body g hlen'
        (fun i hi hj st s t hst hI ↦ hbody (i + 1) (by simpa using hi) (by simpa using hj) st s t hst hI)
        st' s' (g t y) (hst.trans hst') hI'

/-- **A `for` loop with an invariant only** (no `UniStatement` counterpart). -/
theorem PSim.forIn_inv {γ σ : Type} (st0 : RecState) (xs : List γ) (I : Nat → RecState → σ → Prop)
    (body : γ → σ → Prog (ForInStep σ))
    (hbody : ∀ i (hi : i < xs.length) st s, PStep st0 st → I i st s →
      PSim st (body xs[i] s) () (fun st' r _ ↦ ∃ s', r = .yield s' ∧ I (i + 1) st' s'))
    (st : RecState) (s : σ) (hst : PStep st0 st) (hI : I 0 st s) :
    PSim st (forIn xs s body) () (fun st' s' _ ↦ I xs.length st' s') := by
  have h := PSim.forIn_list st0 xs xs
    (fun i st s (_ : Unit) ↦ I i st s) body (fun _ _ ↦ ()) rfl
    (fun i hi _ st s _ hst hI ↦ hbody i hi st s hst hI) st s () hst hI
  exact h

/-! ## The arithmetic operations, as pure parts -/

theorem PSim.op {st : RecState} (hg : Good st) (o : Op) (ho : Op.Arith o) (hok : OpOK st o) :
    PSim st (Pi1.op o)
      (Op.value π publicInput stream st (evalAll π iv publicInput stream st) o) (Rp π iv publicInput stream) :=
  op_pstep π iv publicInput stream st hg o ho hok

theorem PSim.add {st : RecState} (hg : Good st) {a b : Nat} {x y : E} (ha : Rp π iv publicInput stream st a x)
    (hb : Rp π iv publicInput stream st b y) :
    PSim st (Pi1.add a b) (x + y) (Rp π iv publicInput stream) := by
  have h := PSim.op (π := π) (iv := iv) (publicInput := publicInput) (stream := stream) hg (.add a b) trivial
    ⟨ha.1, hb.1⟩
  have e : Op.value π publicInput stream st (evalAll π iv publicInput stream st) (.add a b) = x + y := by
    simp only [Op.value]; rw [← ha.2, ← hb.2]; rfl
  rw [e] at h
  exact h

theorem PSim.mul {st : RecState} (hg : Good st) {a b : Nat} {x y : E} (ha : Rp π iv publicInput stream st a x)
    (hb : Rp π iv publicInput stream st b y) :
    PSim st (Pi1.mul a b) (x * y) (Rp π iv publicInput stream) := by
  have h := PSim.op (π := π) (iv := iv) (publicInput := publicInput) (stream := stream) hg (.mul a b) trivial
    ⟨ha.1, hb.1⟩
  have e : Op.value π publicInput stream st (evalAll π iv publicInput stream st) (.mul a b) = x * y := by
    simp only [Op.value]; rw [← ha.2, ← hb.2]; rfl
  rw [e] at h
  exact h

theorem PSim.square {st : RecState} (hg : Good st) {a : Nat} {x : E} (ha : Rp π iv publicInput stream st a x) :
    PSim st (Pi1.square a) (x * x) (Rp π iv publicInput stream) :=
  PSim.mul hg ha ha

theorem PSim.const {st : RecState} (hg : Good st) (x : E) :
    PSim st (Pi1.const x) x (Rp π iv publicInput stream) :=
  PSim.op (π := π) (iv := iv) (publicInput := publicInput) (stream := stream) hg (.constant x) trivial trivial

theorem PSim.zero {st : RecState} (hg : Good st) :
    PSim st Pi1.zero 0 (Rp π iv publicInput stream) := PSim.const hg 0

theorem PSim.one {st : RecState} (hg : Good st) :
    PSim st Pi1.one 1 (Rp π iv publicInput stream) := PSim.const hg 1

theorem PSim.bits {st : RecState} (hg : Good st) {v : Nat} {x : E} (hv : Rp π iv publicInput stream st v x)
    (s w : Nat) : PSim st (Pi1.bits v s w) (bitsValue x s w) (Rp π iv publicInput stream) := by
  have h := PSim.op (π := π) (iv := iv) (publicInput := publicInput) (stream := stream) hg (.bits v s w) trivial
    hv.1
  have e : Op.value π publicInput stream st (evalAll π iv publicInput stream st) (.bits v s w) =
      bitsValue x s w := by
    simp only [Op.value]; rw [← hv.2]; rfl
  rw [e] at h
  exact h

theorem PSim.statement {st : RecState} (hg : Good st) (k : Nat) :
    PSim st (Pi1.statement k) (eK (beWordAt publicInput.toArray (8 * k)))
      (Rp π iv publicInput stream) :=
  PSim.op (π := π) (iv := iv) (publicInput := publicInput) (stream := stream) hg (.statement k) trivial trivial

end Judgment

/-! ## The channel's operations -/

section Ops

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- **A step that moves the cursor only** keeps the coupling, the channel's cursor moved with it. -/
theorem Couple.step {st st' : RecState} {c : Chan} (hc : Couple π iv publicInput stream st c) (hg' : Good st')
    (hgr : Grows st st') (ha : st'.absorbed = st.absorbed) (hs : st'.state = st.state) (hz : st'.zero = st.zero)
    (hch : chIds st' = chIds st) : Couple π iv publicInput stream st' { c with cursor := st'.cursor } := by
  have hp : PStep st { st' with cursor := st.cursor } :=
    ⟨⟨⟨hg'.inv.index, hg'.inv.before, hg'.inv.kinv, hg'.inv.state⟩, hg'.fresh⟩, hgr, rfl, ha, hs, hz, hch⟩
  have h := hc.pstep π iv publicInput stream hp
  exact ⟨hg', h.data, rfl, h.absorbed, h.state, h.zeroLt, h.zeros, h.chal⟩

/-- The input step: a new node of the stream's bytes at the cursor. -/
theorem input_step (st : RecState) (hg : Good st) (len : Nat) :
    Good (st.input len).2 ∧ Grows st (st.input len).2 ∧ (st.input len).2.cursor = st.cursor + len ∧
      (st.input len).2.absorbed = st.absorbed ∧ (st.input len).2.state = st.state ∧ (st.input len).2.zero = st.zero ∧
      chIds (st.input len).2 = chIds st ∧
      Rp π iv publicInput stream (st.input len).2 (st.input len).1
        (inputValue (stream.extract st.cursor (st.cursor + len)) len) := by
  have hp := new_pstep st (.input st.cursor len) hg (fun _ _ _ h ↦ by cases h) rfl
    (by simp [reads, Node.operands]) (fun k ⟨_, e⟩ ↦ by cases e)
  have hg' : Good (st.input len).2 :=
    ⟨⟨hp.good.inv.index, hp.good.inv.before, hp.good.inv.kinv, hp.good.inv.state⟩, hp.good.fresh⟩
  refine ⟨hg', hp.grows, by simp [RecState.input], hp.absorbed, hp.state,
    hp.zero, hp.chal, ?_⟩
  refine ⟨op_lt st hg.inv (.input len) trivial, ?_⟩
  have := input_val π iv publicInput stream st hg.inv len
  simp only [val, valE, this]

/-- **A read of `len` bytes** (`Recorder::input`) against `takeBytes len`: the bytes at the cursor, the node
`input cursor len`, worth `inputValue` of them. -/
theorem sim_input (st : RecState) (len : Nat) :
    Sim π iv publicInput stream st (Pi1.op (.input len)) (takeBytes (m := Id) len) len 0
      (fun st' i b ↦ b = stream.extract st.cursor (st.cursor + len) ∧ b.size = len ∧
        st'.cursor = st.cursor + len ∧ st'.nodes[i]? = some (.input st.cursor len) ∧
        Rp π iv publicInput stream st' i (inputValue b len)) := by
  intro c hc hle
  refine ⟨fun hr ↦ ?_, fun hr ↦ ⟨_, _, takeBytes_fail len c hr⟩⟩
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := input_step π iv publicInput stream st hc.good len
  have hb : c.data.extract c.cursor (c.cursor + len) = stream.extract st.cursor (st.cursor + len) := by
    rw [hc.data, hc.cursor]
  refine ⟨_, _, takeBytes_run len c hr, ?_, rfl, (Nat.add_zero _).symm, g2, hb, ?_, g3, ?_, by rw [hb]; exact g8⟩
  · have := Couple.step π iv publicInput stream hc g1 g2 g4 g5 g6 g7
    rw [g3, ← hc.cursor] at this
    exact this
  · rw [Array.size_extract]; omega
  · exact new_get st hc.good.inv _

theorem inputValue_24 (b : Array UInt8) : inputValue b 24 = eNew (beWordAt b 16) (beWordAt b 8) (beWordAt b 0) := by
  simp [inputValue]

theorem inputValue_16 (b : Array UInt8) : inputValue b 16 = eNew (beWordAt b 8) (beWordAt b 0) 0 := by
  simp [inputValue]

theorem inputValue_small (b : Array UInt8) (n : Nat) (hn : n ≤ 8) :
    inputValue b n = eK (UInt64.ofNat (b.foldl (fun acc x ↦ acc * 256 + x.toNat) 0)) := by
  simp [inputValue, show n ≠ 24 by omega, show n ≠ 16 by omega]

theorem foldl_bytes_lt (l : List UInt8) (acc k : Nat) (h : acc < 256 ^ k) :
    l.foldl (fun acc x ↦ acc * 256 + x.toNat) acc < 256 ^ (k + l.length) := by
  induction l generalizing acc k with
  | nil => simpa using h
  | cons x l ih =>
    rw [List.foldl_cons, List.length_cons, show k + (l.length + 1) = (k + 1) + l.length by omega]
    apply ih
    have hx : x.toNat < 256 := x.toNat_lt
    rw [Nat.pow_succ]
    have : acc + 1 ≤ 256 ^ k := h
    nlinarith

theorem bytes_lt (b : Array UInt8) : b.foldl (fun acc x ↦ acc * 256 + x.toNat) 0 < 256 ^ b.size := by
  rw [← Array.foldl_toList]
  have := foldl_bytes_lt b.toList 0 0 (by norm_num)
  simpa using this

/-- **`next_scalar`**: 24 bytes, the node worth the scalar `UniStatement` reads. -/
theorem sim_nextScalar (st : RecState) :
    Sim π iv publicInput stream st Pi1.nextScalar (UniStatement.nextScalar (m := Id)) 24 0
      (fun st' i x ↦ Rp π iv publicInput stream st' i x) := by
  have h := (sim_input π iv publicInput stream st 24).map (f := id)
    (g := fun b ↦ eNew (beWordAt b 16) (beWordAt b 8) (beWordAt b 0))
    (S := fun st' i x ↦ Rp π iv publicInput stream st' i x)
    (fun st' i b _ _ ⟨_, _, _, _, hr⟩ ↦ by rw [inputValue_24] at hr; exact hr)
  exact h

/-- **`next_integer(bytes)`** (`bytes ≤ 8`): the node worth `eK (UInt64.ofNat k)`, `k` the integer `UniStatement`
reads, below `256 ^ bytes`. -/
theorem sim_nextInteger (st : RecState) (bytes : Nat) (hb : bytes ≤ 8) :
    Sim π iv publicInput stream st (Pi1.nextInteger bytes) (UniStatement.nextInteger (m := Id) bytes) bytes 0
      (fun st' i k ↦ Rp π iv publicInput stream st' i (eK (UInt64.ofNat k)) ∧ k < 256 ^ bytes) := by
  have h := (sim_input π iv publicInput stream st bytes).map (f := id)
    (g := fun b ↦ b.foldl (fun acc x ↦ acc * 256 + x.toNat) 0)
    (S := fun st' i k ↦ Rp π iv publicInput stream st' i (eK (UInt64.ofNat k)) ∧ k < 256 ^ bytes)
    (fun st' i b _ _ ⟨_, hs, _, _, hr⟩ ↦ by
      rw [inputValue_small b bytes hb] at hr
      exact ⟨hr, hs ▸ bytes_lt b⟩)
  exact h

/-- **`next_root`**: two 16-byte halves, the nodes `input cursor 16` and `input (cursor + 16) 16`, worth the halves
`UniStatement` reads. -/
theorem sim_nextRoot (st : RecState) :
    Sim π iv publicInput stream st Pi1.nextRoot (UniStatement.nextRoot (m := Id)) 32 0
      (fun st' ab xy ↦ Rp π iv publicInput stream st' ab.1 xy.1 ∧ Rp π iv publicInput stream st' ab.2 xy.2 ∧
        st'.nodes[ab.1]? = some (.input st.cursor 16) ∧ st'.nodes[ab.2]? = some (.input (st.cursor + 16) 16)) := by
  have h := Sim.bind (sim_input π iv publicInput stream st 16)
    (k := fun a ↦ Pi1.op (.input 16) >>= fun b ↦ pure (a, b))
    (f := fun lo ↦ takeBytes (m := Id) 16 >>= fun hi ↦
      pure (eNew (beWordAt lo 8) (beWordAt lo 0) 0, eNew (beWordAt hi 8) (beWordAt hi 0) 0))
    (S := fun st' ab xy ↦ Rp π iv publicInput stream st' ab.1 xy.1 ∧ Rp π iv publicInput stream st' ab.2 xy.2 ∧
        st'.nodes[ab.1]? = some (.input st.cursor 16) ∧ st'.nodes[ab.2]? = some (.input (st.cursor + 16) 16))
    (fun st1 a lo hg1 _ ⟨_, _, hcur1, hn1, hr1⟩ ↦
      (sim_input π iv publicInput stream st1 16).map
        (fun st2 b hi _ hgr2 ⟨_, _, _, hn2, hr2⟩ ↦ by
          rw [inputValue_16] at hr1 hr2
          rw [hcur1] at hn2
          exact ⟨hr1.grow π iv publicInput stream hg1.inv.kinv hgr2, hr2, nodes_grow hgr2 hn1, hn2⟩))
  exact h

theorem hash_fresh (st : RecState) (hg : Good st) :
    st.index[(Node.hash st.state st.absorbed st.cursor)]? = none := by
  cases h : st.index[(Node.hash st.state st.absorbed st.cursor)]? with
  | none => rfl
  | some j =>
    exfalso
    have hj := hg.inv.index _ _ h
    have hjlt : j < st.nodes.size := by
      rcases Nat.lt_or_ge j st.nodes.size with h' | h'
      · exact h'
      · simp [Array.getElem?_eq_none h'] at hj
    have hjn : st.nodes[j] = .hash st.state st.absorbed st.cursor := by
      rw [Array.getElem?_eq_getElem hjlt] at hj; exact Option.some.inj hj
    have hb := hg.inv.before j hjlt st.state (by rw [hjn]; simp [reads, Node.operands])
    have hf := hg.fresh j hjlt _ _ _ hjn
    omega

/-- The state after a sample's hash: the hash appended, the new state, the bytes absorbed. -/
theorem afterHash_eq (st : RecState) (hg : Good st) :
    afterHash st =
      { st with
        nodes := st.nodes.push (.hash st.state st.absorbed st.cursor)
        index := st.index.insert (.hash st.state st.absorbed st.cursor) st.nodes.size
        state := st.nodes.size
        absorbed := st.cursor } := by
  unfold afterHash RecState.new
  rw [hash_fresh st hg]

/-- **The sample's nodes are new**: the hash (no hash reads the state node, the newest: `Fresh`, `RecInv.before`),
then the challenge (it reads the hash, the newest node). -/
theorem sample_struct (st : RecState) (hg : Good st) (narrow : Bool) :
    (st.sample narrow).1 = st.nodes.size + 1 ∧
      (st.sample narrow).2.nodes = ((afterHash st).nodes).push
        (if narrow then .narrow st.nodes.size else .low st.nodes.size) ∧
      (afterHash st).nodes = st.nodes.push (.hash st.state st.absorbed st.cursor) ∧
      (st.sample narrow).2.state = st.nodes.size ∧ (st.sample narrow).2.absorbed = st.cursor ∧
      (st.sample narrow).2.cursor = st.cursor ∧ (st.sample narrow).2.zero = st.zero ∧
      (st.sample narrow).2.kernels = st.kernels := by
  have hA := afterHash_eq st hg
  have hAi := afterHash_inv st hg.inv
  have hAn : (afterHash st).nodes = st.nodes.push (.hash st.state st.absorbed st.cursor) := by rw [hA]
  have h2 : (afterHash st).index[(if narrow then Node.narrow st.nodes.size else .low st.nodes.size)]? = none := by
    cases h : (afterHash st).index[(if narrow then Node.narrow st.nodes.size else .low st.nodes.size)]? with
    | none => rfl
    | some j =>
      exfalso
      have hj := hAi.index _ _ h
      have hsz : (afterHash st).nodes.size = st.nodes.size + 1 := by rw [hAn]; simp
      have hjlt : j < (afterHash st).nodes.size := by
        rcases Nat.lt_or_ge j (afterHash st).nodes.size with h' | h'
        · exact h'
        · simp [Array.getElem?_eq_none h'] at hj
      have hjn : (afterHash st).nodes[j] = (if narrow then Node.narrow st.nodes.size else .low st.nodes.size) := by
        rw [Array.getElem?_eq_getElem hjlt] at hj; exact Option.some.inj hj
      have hb := hAi.before j hjlt st.nodes.size (by rw [hjn]; cases narrow <;> simp [reads, Node.operands])
      omega
  have hs : (afterHash st).state = st.nodes.size := by rw [hA]
  have hsz : (afterHash st).nodes.size = st.nodes.size + 1 := by rw [hAn]; simp
  rw [sample_eq, hs]
  unfold RecState.new
  rw [h2]
  refine ⟨hsz, rfl, hAn, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hA]

theorem isChal_chal (narrow : Bool) (i : Nat) : isChal (if narrow then Node.narrow i else .low i) = true := by
  cases narrow <;> rfl

/-- **A challenge** (`Recorder::sample`, `sample_narrow`) against `sampleDrawn`: no byte read, one challenge drawn
(the channel's challenges pushed with it); the node new (`st.nodes.size + 1`, after the hash), worth the challenge,
and `chIds` grown by it. -/
theorem sim_sampleOp (st : RecState) (narrow : Bool) :
    Sim π iv publicInput stream st (Pi1.op (.sample narrow)) (sampleDrawn (Fp π) narrow) 0 1
      (fun st' i x ↦ Rp π iv publicInput stream st' i x ∧ chIds st' = chIds st ++ [i] ∧
        i = st.nodes.size + 1 ∧ st'.nodes.size = st.nodes.size + 2) := by
  intro c hc hle
  refine ⟨fun _ ↦ ?_, fun hr ↦ absurd hr (by omega)⟩
  have hg := hc.good
  obtain ⟨e1, e2, hAn, e3, e4, e5, e6, _⟩ := sample_struct st hg narrow
  have hrec : (Pi1.op (.sample narrow)).record st = st.sample narrow := rfl
  rw [hrec]
  have hinv := sample_inv st hg.inv narrow
  have hgr : Grows st (st.sample narrow).2 := (op_grows_kinv st (.sample narrow) hg.inv.kinv).1
  have hkA : KInv (afterHash st) := (afterHash_inv st hg.inv).kinv
  have hgrA : Grows (afterHash st) (st.sample narrow).2 := by
    rw [sample_eq]; exact new_grows _ _
  have hsz : (st.sample narrow).2.nodes.size = st.nodes.size + 2 := by rw [e2, hAn]; simp
  -- Fresh: the new state is the newest hash.
  have hfresh : Fresh (st.sample narrow).2 := by
    intro i hi s f u he
    rw [e3]
    have hst := hg.inv.state
    rcases Nat.lt_or_ge i st.nodes.size with hlt | hge
    · have : (st.sample narrow).2.nodes[i] = st.nodes[i] := by
        simp [e2, hAn, Array.getElem_push, hlt, Nat.lt_succ_of_lt hlt]
      rw [this] at he
      have := hg.fresh i hlt s f u he
      omega
    · rcases Nat.lt_or_ge i (st.nodes.size + 1) with hlt | hge'
      · omega
      · have hieq : i = st.nodes.size + 1 := by rw [hsz] at hi; omega
        subst hieq
        have : (st.sample narrow).2.nodes[st.nodes.size + 1] =
            (if narrow then Node.narrow st.nodes.size else .low st.nodes.size) := by
          simp [e2, hAn, Array.getElem_push]
        rw [this] at he
        cases narrow <;> cases he
  -- The challenge nodes.
  have hch : chIds (st.sample narrow).2 = chIds st ++ [st.nodes.size + 1] := by
    have c1 := chIds_push st (.hash st.state st.absorbed st.cursor) _ rfl (afterHash st) hAn
    have c2 := chIds_push (afterHash st) (if narrow then Node.narrow st.nodes.size else .low st.nodes.size) _ rfl
      (st.sample narrow).2 e2
    rw [c2, c1, isChal_chal]
    simp [isChal, hAn]
  -- The challenge's value.
  have hx : val π iv publicInput stream (st.sample narrow).2 (st.sample narrow).1 = chalOf π narrow c := by
    have := op_val π iv publicInput stream st hg.inv (.sample narrow) trivial
    unfold val
    rw [show st.sample narrow = st.op (.sample narrow) from rfl, this]
    unfold chalOf hashOf
    rw [hc.state, hc.data, hc.absorbed, hc.cursor]
    rfl
  -- The state's value.
  have hstate : stateVal π iv publicInput stream (st.sample narrow).2 = hashOf π c := by
    unfold stateVal
    rw [e3]
    have hAs : (afterHash st).state = st.nodes.size := by rw [afterHash_eq st hg]
    have hlt : st.nodes.size < (afterHash st).nodes.size := by rw [hAn]; simp
    have := evalAll_grows π iv publicInput stream _ _ hkA hgrA st.nodes.size hlt
    rw [valState_congr this, ← hAs, afterHash_val π iv publicInput stream st hg.inv]
    unfold hashOf
    rw [hc.state, hc.data, hc.absorbed, hc.cursor]
    rfl
  refine ⟨chalOf π narrow c,
    { c with
      absorbed := c.cursor
      state := hashOf π c
      challenges := c.challenges.push (chalOf π narrow c) }, sampleDrawn_run π narrow c, ?_,
    (Nat.add_zero _).symm, by simp, hgr, ?_⟩
  · refine ⟨⟨hinv, hfresh⟩, hc.data, hc.cursor.trans e5.symm, hc.cursor.trans e4.symm, hstate.symm, ?_, ?_, ?_⟩
    · intro z hz
      rw [e6] at hz
      exact lt_of_lt_of_le (hc.zeroLt z hz) (Grows.size_le hgr)
    · show c.zeros.toList = _
      rw [hc.zeros, e6]
      exact List.map_congr_left fun z hz ↦ (val_grow π iv publicInput stream hg.inv.kinv hgr (hc.zeroLt z hz)).symm
    · show (c.challenges.push (chalOf π narrow c)).toList = _
      rw [Array.toList_push, hc.chal, hch, List.map_append, List.map_singleton, ← e1, hx]
      congr 1
      exact List.map_congr_left fun i hi ↦ (val_grow π iv publicInput stream hg.inv.kinv hgr (chIds_lt hi)).symm
  · refine ⟨⟨by rw [e1, hsz]; omega, hx⟩, by rw [e1]; exact hch, e1, hsz⟩

/-- `Channel::sample`. -/
theorem sim_sample (st : RecState) :
    Sim π iv publicInput stream st Pi1.sample (UniStatement.sample (Fp π)) 0 1
      (fun st' i x ↦ Rp π iv publicInput stream st' i x ∧ chIds st' = chIds st ++ [i] ∧
        i = st.nodes.size + 1 ∧ st'.nodes.size = st.nodes.size + 2) :=
  sim_sampleOp π iv publicInput stream st false

/-- `Channel::sample_narrow`. -/
theorem sim_sampleNarrow (st : RecState) :
    Sim π iv publicInput stream st Pi1.sampleNarrow (UniStatement.sampleNarrow (Fp π)) 0 1
      (fun st' i x ↦ Rp π iv publicInput stream st' i x ∧ chIds st' = chIds st ++ [i] ∧
        i = st.nodes.size + 1 ∧ st'.nodes.size = st.nodes.size + 2) :=
  sim_sampleOp π iv publicInput stream st true

/-- **A challenge, narrow or not** (`Pi1.sampleDrawn` against `UniStatement.sampleDrawn`). -/
theorem sim_sampleDrawn (st : RecState) (narrow : Bool) :
    Sim π iv publicInput stream st (Pi1.sampleDrawn narrow) (UniStatement.sampleDrawn (Fp π) narrow) 0 1
      (fun st' i x ↦ Rp π iv publicInput stream st' i x ∧ chIds st' = chIds st ++ [i] ∧
        i = st.nodes.size + 1 ∧ st'.nodes.size = st.nodes.size + 2) := by
  cases narrow
  · exact sim_sampleOp π iv publicInput stream st false
  · exact sim_sampleOp π iv publicInput stream st true

/-- **`require_zero`**: the value collected; no byte, no challenge. -/
theorem sim_requireZero (st : RecState) (v : Nat) (x : E) (hv : Rp π iv publicInput stream st v x) :
    Sim π iv publicInput stream st (Pi1.requireZero v) (UniStatement.requireZero (m := Id) x) 0 0
      (fun st' _ _ ↦ st'.zero = st.zero.push v ∧ st'.nodes = st.nodes) := by
  intro c hc hle
  refine ⟨fun _ ↦ ⟨(), { c with zeros := c.zeros.push x }, requireZero_run x c, ?_, (Nat.add_zero _).symm,
    (Nat.add_zero _).symm, Grows.refl st, rfl, rfl⟩, fun hr ↦ absurd hr (by omega)⟩
  have hg := hc.good
  refine ⟨⟨⟨hg.inv.index, hg.inv.before, hg.inv.kinv, hg.inv.state⟩, hg.fresh⟩, hc.data, hc.cursor, hc.absorbed,
    hc.state, ?_, ?_, hc.chal⟩
  · intro z hz
    have hz' : z ∈ (st.zero.push v).toList := hz
    rw [Array.toList_push, List.mem_append, List.mem_singleton] at hz'
    rcases hz' with hz' | rfl
    · exact hc.zeroLt z hz'
    · exact hv.1
  · show (c.zeros.push x).toList = (st.zero.push v).toList.map (val π iv publicInput stream st)
    rw [Array.toList_push, Array.toList_push, List.map_append, hc.zeros, ← hv.2]
    rfl

/-- **`next_scalars(count)`**: `24 count` bytes, the nodes worth the scalars. -/
theorem sim_nextScalars (st : RecState) (count : Nat) :
    Sim π iv publicInput stream st (Pi1.nextScalars count) (UniStatement.nextScalars (m := Id) count) (24 * count) 0
      (fun st' is xs ↦ RpL π iv publicInput stream st' is xs) := by
  refine Sim.of_good fun hg ↦ ?_
  show Sim π iv publicInput stream st
    (forIn [:count] (#[] : Array Sym) (fun _ s ↦ Pi1.nextScalar >>= fun x ↦ pure (ForInStep.yield (s.push x))) >>=
      fun s ↦ pure s.toList)
    (forIn [:count] (#[] : Array E)
      (fun _ s ↦ UniStatement.nextScalar (m := Id) >>= fun x ↦ pure (ForInStep.yield (s.push x))) >>=
      fun s ↦ pure s.toList) _ _ _
  rw [forIn_range, forIn_range]
  have hl := Sim.forIn_list (π := π) (iv := iv) (publicInput := publicInput) (stream := stream) st
    (List.range' 0 (count - 0)) (List.range' 0 (count - 0))
    (fun _ st (s : Array Sym) (t : Array E) ↦ RpL π iv publicInput stream st s.toList t.toList)
    (fun _ ↦ 24) (fun _ ↦ 0) (fun _ s ↦ Pi1.nextScalar >>= fun x ↦ pure (ForInStep.yield (s.push x)))
    (fun _ s ↦ UniStatement.nextScalar (m := Id) >>= fun x ↦ pure (ForInStep.yield (s.push x))) rfl
    (fun i _ _ st' s t hg' _ hI ↦ (sim_nextScalar π iv publicInput stream st').map
      (fun st'' a b _ hgr'' hr ↦ ⟨s.push a, t.push b, rfl, rfl, by
        rw [Array.toList_push, Array.toList_push]
        exact (hI.grow π iv publicInput stream hg'.inv.kinv hgr'').snoc hr⟩))
    st #[] #[] hg (Grows.refl st) List.Forall₂.nil
  refine Sim.cast (by rw [sum_const_range, List.length_range', Nat.sub_zero]) (by simp)
    (hl.map fun _ _ _ _ _ h ↦ h)

/-- **`samples(count)`**: `count` challenges, the nodes worth them, `chIds` grown by them. -/
theorem sim_samples (st : RecState) (count : Nat) :
    Sim π iv publicInput stream st (Pi1.samples count) (UniStatement.samples (Fp π) count) 0 count
      (fun st' is xs ↦ RpL π iv publicInput stream st' is xs ∧ chIds st' = chIds st ++ is) := by
  refine Sim.of_good fun hg ↦ ?_
  show Sim π iv publicInput stream st
    (forIn [:count] (#[] : Array Sym) (fun _ s ↦ Pi1.sample >>= fun x ↦ pure (ForInStep.yield (s.push x))) >>=
      fun s ↦ pure s.toList)
    (forIn [:count] (#[] : Array E)
      (fun _ s ↦ UniStatement.sample (Fp π) >>= fun x ↦ pure (ForInStep.yield (s.push x))) >>=
      fun s ↦ pure s.toList) _ _ _
  rw [forIn_range, forIn_range]
  have hl := Sim.forIn_list (π := π) (iv := iv) (publicInput := publicInput) (stream := stream) st
    (List.range' 0 (count - 0)) (List.range' 0 (count - 0))
    (fun _ st' (s : Array Sym) (t : Array E) ↦
      RpL π iv publicInput stream st' s.toList t.toList ∧ chIds st' = chIds st ++ s.toList)
    (fun _ ↦ 0) (fun _ ↦ 1) (fun _ s ↦ Pi1.sample >>= fun x ↦ pure (ForInStep.yield (s.push x)))
    (fun _ s ↦ UniStatement.sample (Fp π) >>= fun x ↦ pure (ForInStep.yield (s.push x))) rfl
    (fun i _ _ st' s t hg' _ hI ↦ (sim_sample π iv publicInput stream st').map
      (fun st'' a b _ hgr'' hr ↦ ⟨s.push a, t.push b, rfl, rfl, by
        rw [Array.toList_push, Array.toList_push]
        exact (hI.1.grow π iv publicInput stream hg'.inv.kinv hgr'').snoc hr.1, by
        rw [hr.2.1, hI.2, Array.toList_push, List.append_assoc]⟩))
    st #[] #[] hg (Grows.refl st) ⟨List.Forall₂.nil, by simp⟩
  refine Sim.cast (by simp) (by rw [sum_const_range, List.length_range', Nat.sub_zero, Nat.one_mul])
    (hl.map fun _ _ _ _ _ h ↦ h)

/-! ## The start: the seed, then the public input's four words -/

theorem start_nodes : RecState.start.nodes = #[Node.seed] := by simp [RecState.start, RecState.new]
theorem start_state : RecState.start.state = 0 := by simp [RecState.start, RecState.new]
theorem start_cursor : RecState.start.cursor = 0 := by simp [RecState.start, RecState.new]
theorem start_absorbed : RecState.start.absorbed = 0 := by simp [RecState.start, RecState.new]
theorem start_zero : RecState.start.zero = #[] := by simp [RecState.start, RecState.new]

theorem start_good : Good RecState.start := by
  refine ⟨start_inv, ?_⟩
  intro i hi s f u he
  have h0 : i = 0 := by
    have hi' := hi
    rw [start_nodes] at hi'
    simp at hi'
    omega
  subst h0
  have : RecState.start.nodes[0] = Node.seed := by simp [start_nodes]
  rw [this] at he
  cases he

/-- **The recorder's start and `UniStatement`'s channel's, coupled**: the seed node worth the seed. -/
theorem start_couple :
    Couple π iv publicInput stream RecState.start (Chan.start (Id.run (seedWith (Fp π) iv publicInput)) stream) := by
  refine ⟨start_good, rfl, start_cursor.symm, start_absorbed.symm, ?_, ?_, ?_, ?_⟩
  · show Id.run (seedWith (Fp π) iv publicInput) =
      valState (evalP π iv publicInput stream RecState.start.kernels #[] RecState.start.nodes.toList)
        RecState.start.state
    rw [start_nodes, start_state]
    rfl
  · intro z hzm
    rw [start_zero] at hzm
    simp at hzm
  · show ([] : List E) = _
    rw [start_zero]
    rfl
  · show ([] : List E) = _
    have : chIds RecState.start = [] := by
      unfold chIds
      rw [start_nodes]
      rfl
    rw [this]
    rfl

/-- **The public input's four words** (`record_verifier_with`'s statement words, `pi1Rec3`'s first loop). -/
def statementWords : Prog (List Sym) := do
  let mut words : Array Sym := #[]
  for k in [0:4] do
    words := words.push (← statement k)
  return words.toList

/-- `pi1Rec3`'s shape: its first loop is `statementWords`, then the rest. -/
theorem statementWords_bind {α : Type} (f : List Sym → Prog α) :
    (do
      let mut words : Array Sym := #[]
      for k in [0:4] do
        words := words.push (← statement k)
      f words.toList : Prog α) = statementWords >>= f := by
  simp only [statementWords, prog_bind_assoc, prog_pure_bind]

/-- **The statement words are worth `publicWordsOf`**. -/
theorem statementWords_psim (st : RecState) (hg : Good st) :
    PSim st statementWords (publicWordsOf publicInput)
      (fun st' ws xs ↦ RpL π iv publicInput stream st' ws xs) := by
  show PSim st
    (forIn [:4] (#[] : Array Sym) (fun k s ↦ Pi1.statement k >>= fun x ↦ pure (ForInStep.yield (s.push x))) >>=
      fun s ↦ pure s.toList) _ _
  rw [forIn_range]
  refine PSim.bind (PSim.forIn_inv st
    (List.range' 0 (4 - 0))
    (fun i st' (s : Array Sym) ↦ RpL π iv publicInput stream st' s.toList
      ((List.range i).map fun k ↦ eK (beWordAt publicInput.toArray (8 * k))))
    (fun k s ↦ Pi1.statement k >>= fun x ↦ pure (ForInStep.yield (s.push x)))
    (fun i hi st' s hst hI ↦ PSim.bind (PSim.statement hst.good _) fun st'' a hst'' hr ↦
      PSim.pure hst''.good ⟨s.push a, rfl, by
        rw [Array.toList_push, List.range_succ, List.map_append, List.map_singleton]
        simp only [List.getElem_range', Nat.zero_add, Nat.one_mul] at hr
        exact (hI.pgrow hst.good hst'').snoc hr⟩)
    st #[] (PStep.refl st hg) List.Forall₂.nil) ?_
  intro st' s hst hI
  refine PSim.pure hst.good ?_
  simpa [publicWordsOf] using hI

/-- **The start, with the statement words**: coupled with `UniStatement`'s start, the words worth
`publicWordsOf publicInput`. -/
theorem start_sim :
    Couple π iv publicInput stream (statementWords.record RecState.start).2
        (Chan.start (Id.run (seedWith (Fp π) iv publicInput)) stream) ∧
      RpL π iv publicInput stream (statementWords.record RecState.start).2 (statementWords.record RecState.start).1
        (publicWordsOf publicInput) := by
  obtain ⟨hp, hr⟩ := statementWords_psim π iv publicInput stream RecState.start start_good
  exact ⟨(start_couple π iv publicInput stream).pstep π iv publicInput stream hp, hr⟩

end Ops

end RecGraph.Sim

