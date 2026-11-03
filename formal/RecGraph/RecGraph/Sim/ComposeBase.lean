-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.Transcript
import RecGraph.Sim.Tables

/-!
# The composition's framework: a judgment under a condition on the final channel, and monotone runs

* `SimQ Q st p u n ch R`: `Sim`, but only for the channels whose run ends in a channel satisfying `Q`. π1-rec3's
  verifier is simulated off the merge hazard (`MergeHazard`, the hazard at the final channel's challenges 42 and 49):
  `Q` is "no hazard at the final channel". Rules: `SimQ.of_sim`, `SimQ.bind` (a `Sim` first), `SimQ.pbind` (a pure part
  first), `SimQ.cast`, `SimQ.of_cond` (a `Sim` under a premise `P`, and off `P` no run ends in `Q`).
* `Mono u`: every run of `u` ends with the channel's challenges extended (nothing drawn is ever removed): `Mono.bind`,
  `Mono.ret`, `Mono.forIn`, and `UniStatement`'s transcript functions and `batchFs` at π1-rec3's shape.
* `chIds_grows`, `Sim.withChIds`: the challenge nodes grow as the state does, by as many as the challenges drawn.
* The transport of representations along a growth (`Rp.sg`, `RpL.sg`, `RpRels.sg`, …) and the tactic
  `sgrow hk hgr`.
-/

-- The judgments are `RecGraph.Sim.Sim`, `RecGraph.Sim.SimQ`.
set_option linter.dupNamespace false

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

/-! ## The challenge nodes grow with the state -/

theorem chIds_grows {st st' : RecState} (h : Grows st st') : ∃ l, chIds st' = chIds st ++ l := by
  obtain ⟨⟨ys, e⟩, _⟩ := h
  have hs : st'.nodes.size = st.nodes.size + ys.length := by
    have := congrArg List.length e
    simpa using this
  refine ⟨(((ys.zip (List.range' st.nodes.size ys.length)).filter fun p ↦ isChal p.1).map (·.2)), ?_⟩
  unfold chIds
  rw [e, hs, List.range_add, List.zip_append (by simp), List.filter_append, List.map_append]
  congr 3
  rw [List.range'_eq_map_range]

section Values

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

/-! ## Transport along a growth -/

theorem Rp.sg {st st' : RecState} (hk : KInv st) (hgr : Grows st st') {i : Nat} {x : E}
    (h : Rp π iv publicInput stream st i x) : Rp π iv publicInput stream st' i x :=
  h.grow π iv publicInput stream hk hgr

theorem RpL.sg {st st' : RecState} (hk : KInv st) (hgr : Grows st st') {is : List Nat} {xs : List E}
    (h : RpL π iv publicInput stream st is xs) : RpL π iv publicInput stream st' is xs :=
  h.grow π iv publicInput stream hk hgr

theorem OptRp.sg {st st' : RecState} (hk : KInv st) (hgr : Grows st st') {e : Option Nat} {x : Option E}
    (h : OptRp π iv publicInput stream st e x) : OptRp π iv publicInput stream st' e x :=
  h.grow hk hgr

theorem RpTerm.sg {st st' : RecState} (hk : KInv st) (hgr : Grows st st') {t : TermS} {u : Term}
    (h : RpTerm π iv publicInput stream st t u) : RpTerm π iv publicInput stream st' t u :=
  ⟨h.1, h.2.1, h.2.2.1.sg hk hgr, h.2.2.2.sg hk hgr⟩

theorem RpTermsC.sg {st st' : RecState} (hk : KInv st) (hgr : Grows st st') {ts : List TermS} {us : List Term}
    (h : RpTermsC π iv publicInput stream st ts us) : RpTermsC π iv publicInput stream st' ts us :=
  List.Forall₂.imp (fun _ _ h ↦ RpTerm.sg hk hgr h) h

theorem RpRel.sg {st st' : RecState} (hk : KInv st) (hgr : Grows st st') {r : RelationS} {u : Relation}
    (h : RpRel π iv publicInput stream st r u) : RpRel π iv publicInput stream st' r u :=
  ⟨RpTermsC.sg hk hgr h.1, h.2.sg hk hgr⟩

theorem RpRels.sg {st st' : RecState} (hk : KInv st) (hgr : Grows st st') {rs : List RelationS}
    {us : List Relation} (h : RpRels π iv publicInput stream st rs us) : RpRels π iv publicInput stream st' rs us :=
  List.Forall₂.imp (fun _ _ h ↦ RpRel.sg hk hgr h) h

/-- Lists of lists of nodes. -/
theorem RpLL.sg {st st' : RecState} (hk : KInv st) (hgr : Grows st st') {a : List (List Nat)} {b : List (List E)}
    (h : List.Forall₂ (RpL π iv publicInput stream st) a b) : List.Forall₂ (RpL π iv publicInput stream st') a b :=
  List.Forall₂.imp (fun _ _ h ↦ RpL.sg hk hgr h) h

/-- The value of a node held does not change as the state grows. -/
theorem val_sg {st st' : RecState} (hk : KInv st) (hgr : Grows st st') {i : Nat} (hi : i < st.nodes.size) :
    val π iv publicInput stream st' i = val π iv publicInput stream st i :=
  val_grow π iv publicInput stream hk hgr hi

end Values

/-! ## The tactic `sgrow hk hgr` -/

open Lean Elab Tactic Meta in
/-- `sgrow hk hgr` (`hk : KInv st`, `hgr : Grows st st'`): every hypothesis `Rp … st …`, `RpL … st …`, `OptRp … st …`,
`RpTerm`, `RpTermsC`, `RpRel`, `RpRels … st …` (or a `∀ …,` of one) is replaced by its transport to `st'`; every
`Grows a st` by `Grows a st'`. -/
elab "sgrow " hk:ident hgr:ident : tactic => do
  let g0 ← getMainGoal
  let (hkF, hgrF, todo) ← g0.withContext do
    let hkD ← getLocalDeclFromUserName hk.getId
    let hgrD ← getLocalDeclFromUserName hgr.getId
    let hgrType ← instantiateMVars hgrD.type
    let src := hgrType.getAppArgs[0]!
    let lctx ← getLCtx
    let mut out : Array (FVarId × Name × Name) := #[]
    for ldecl in lctx do
      if ldecl.isImplementationDetail then continue
      if ldecl.fvarId == hkD.fvarId || ldecl.fvarId == hgrD.fvarId then continue
      let t ← instantiateMVars ldecl.type
      let lem? ← forallTelescope t fun _ body ↦ do
        let args := body.getAppArgs
        match body.getAppFn.constName? with
        | some n =>
          let lem? : Option (Name × Nat) :=
            if n == ``Rp then some (``Rp.sg, 4)
            else if n == ``RpL then some (``RpL.sg, 4)
            else if n == ``OptRp then some (``OptRp.sg, 4)
            else if n == ``RpTerm then some (``RpTerm.sg, 4)
            else if n == ``RpTermsC then some (``RpTermsC.sg, 4)
            else if n == ``RpRel then some (``RpRel.sg, 4)
            else if n == ``RpRels then some (``RpRels.sg, 4)
            else if n == ``Grows then some (``Grows.trans, 1)
            else none
          match lem? with
          | some (lem, k) =>
            if h : k < args.size then
              if args[k] == src then return some lem else return none
            else return none
          | none => return none
        | none => return none
      if let some lem := lem? then out := out.push (ldecl.fvarId, ldecl.userName, lem)
    return (hkD.fvarId, hgrD.fvarId, out)
  let mut g := g0
  for (fv, n, lem) in todo do
    g ← g.withContext do
      let h := mkFVar fv
      let ty ← instantiateMVars (← inferType h)
      let prf ← forallTelescope ty fun xs _ ↦ do
        let inner ← if lem == ``Grows.trans then mkAppM lem #[mkAppN h xs, mkFVar hgrF]
          else mkAppM lem #[mkFVar hkF, mkFVar hgrF, mkAppN h xs]
        mkLambdaFVars xs inner
      let pty ← inferType prf
      let g1 ← g.assert n pty prf
      let (_, g2) ← g1.intro1P
      try g2.clear fv catch _ => pure g2
  replaceMainGoal [g]

/-! ## Monotone runs: nothing drawn is removed -/

/-- **Every run of `u` ends with the challenges extended.** -/
def Mono {β : Type} (u : ChanM Id β) : Prop :=
  ∀ c : Chan, ∃ l, ((u.run).run c).2.challenges.toList = c.challenges.toList ++ l

theorem Mono.ret {β : Type} (b : β) : Mono (pure b : ChanM Id β) := fun c ↦ ⟨[], by rw [List.append_nil]; rfl⟩

theorem Mono.bind {β γ : Type} {u : ChanM Id β} {f : β → ChanM Id γ} (hu : Mono u) (hf : ∀ b, Mono (f b)) :
    Mono (u >>= f) := by
  intro c
  obtain ⟨l1, h1⟩ := hu c
  rw [run_bind]
  rcases e : (u.run).run c with ⟨r, c1⟩
  rw [e] at h1
  cases r with
  | ok b =>
    obtain ⟨l2, h2⟩ := hf b c1
    exact ⟨l1 ++ l2, by simp only at h1 ⊢; rw [h2, h1, List.append_assoc]⟩
  | error e' => exact ⟨l1, h1⟩

theorem Mono.congr {β : Type} {u u' : ChanM Id β} (h : u = u') (hu : Mono u) : Mono u' := h ▸ hu

theorem Mono.takeBytes (n : Nat) : Mono (UniStatement.takeBytes (m := Id) n) := by
  intro c
  refine ⟨[], ?_⟩
  by_cases h : c.cursor + n ≤ c.data.size
  · rw [takeBytes_run n c h]; simp
  · rw [takeBytes_fail n c (by omega)]; simp

theorem Mono.sampleDrawn (π : KeccakState → KeccakState) (narrow : Bool) :
    Mono (UniStatement.sampleDrawn (Fp π) narrow) := fun c ↦
  ⟨[chalOf π narrow c], by rw [sampleDrawn_run]; simp⟩

theorem Mono.sample (π : KeccakState → KeccakState) : Mono (UniStatement.sample (Fp π)) :=
  Mono.sampleDrawn π false

theorem Mono.requireZero (x : E) : Mono (UniStatement.requireZero (m := Id) x) := fun c ↦
  ⟨[], by rw [requireZero_run]; simp⟩

theorem Mono.finish : Mono (UniStatement.finish (m := Id)) := fun c ↦ ⟨[], by rw [finish_run]; split <;> simp⟩

theorem Mono.forInL {γ σ : Type} (body : γ → σ → ChanM Id (ForInStep σ)) (hb : ∀ x s, Mono (body x s)) :
    ∀ (xs : List γ) (s : σ), Mono (forIn xs s body) := by
  intro xs
  induction xs with
  | nil => intro s; rw [List.forIn_nil]; exact Mono.ret s
  | cons x xs ih =>
    intro s
    rw [List.forIn_cons]
    refine Mono.bind (hb x s) fun r ↦ ?_
    cases r with
    | done b => exact Mono.ret b
    | yield b => exact ih b

theorem Mono.forInR {σ : Type} (body : Nat → σ → ChanM Id (ForInStep σ)) (hb : ∀ x s, Mono (body x s))
    (a b : Nat) (s : σ) : Mono (forIn [a:b] s body) := by
  rw [forIn_range]
  exact Mono.forInL body hb _ s

theorem Mono.nextScalar : Mono (UniStatement.nextScalar (m := Id)) :=
  Mono.bind (Mono.takeBytes 24) fun _ ↦ Mono.ret _

theorem Mono.nextScalars (count : Nat) : Mono (UniStatement.nextScalars (m := Id) count) := by
  unfold UniStatement.nextScalars
  exact Mono.bind (Mono.forInR _ (fun _ _ ↦ Mono.bind Mono.nextScalar fun _ ↦ Mono.ret _) _ _ _)
    fun _ ↦ Mono.ret _

theorem Mono.roundPoly (count : Nat) (claim : E) (e : Option E) :
    Mono (UniStatement.roundPoly (m := Id) count claim e) := by
  unfold UniStatement.roundPoly
  cases e with
  | none =>
    exact Mono.bind Mono.nextScalar fun _ ↦ Mono.bind (Mono.nextScalars _) fun _ ↦ Mono.ret _
  | some r => exact Mono.bind (Mono.nextScalars _) fun _ ↦ Mono.ret _

theorem Mono.sumcheckDrawn (π : KeccakState → KeccakState) (claim : E) (count : Nat) (eqs : List (Option E))
    (narrow : Bool) : Mono (UniStatement.sumcheckDrawn (Fp π) claim count eqs narrow) := by
  unfold UniStatement.sumcheckDrawn
  exact Mono.bind (Mono.forInL _ (fun e s ↦ Mono.bind (Mono.roundPoly _ _ _) fun _ ↦
    Mono.bind (Mono.sampleDrawn π narrow) fun _ ↦ Mono.ret _) _ _) fun _ ↦ Mono.ret _

theorem Mono.pairRoundPoly (degree : Nat) (claim : E) : Mono (UniStatement.pairRoundPoly (m := Id) degree claim) := by
  unfold UniStatement.pairRoundPoly
  exact Mono.bind (Mono.nextScalars _) fun _ ↦ Mono.bind (Mono.nextScalars _) fun _ ↦ Mono.ret _

theorem Mono.sumcheckPairsDrawn (π : KeccakState → KeccakState) (claim : E) (degree vars : Nat) (narrow : Bool) :
    Mono (UniStatement.sumcheckPairsDrawn (Fp π) claim degree vars narrow) := by
  unfold UniStatement.sumcheckPairsDrawn
  refine Mono.bind (Mono.forInR _ (fun _ _ ↦ Mono.bind (Mono.pairRoundPoly _ _) fun _ ↦
    Mono.bind (Mono.sampleDrawn π narrow) fun _ ↦ Mono.ret _) _ _ _) fun s ↦ ?_
  split
  · exact Mono.bind (Mono.sumcheckDrawn π _ _ _ _) fun _ ↦ Mono.ret _
  · exact Mono.ret _

/-- **`batchFs` at π1-rec3's shape** (paired rounds, no pending matrices) only draws. -/
theorem Mono.batchFs (π : KeccakState → KeccakState) (combined : List (Commitment × Combined))
    (layouts : List (Commitment × StackLayout)) (bitSlice : Option Combined) (ringMap : Option (List E)) :
    Mono (UniStatement.batchFs (Fp π) .rec3 combined layouts bitSlice ringMap none) := by
  unfold UniStatement.batchFs
  refine Mono.bind (Mono.sample π) fun lambda ↦ ?_
  dsimp only
  refine Mono.bind (Mono.sumcheckPairsDrawn π _ _ _ _) fun x ↦ ?_
  refine Mono.bind (Mono.ret _) fun x ↦ ?_
  refine Mono.bind (Mono.nextScalars _) fun values ↦ ?_
  refine Mono.bind (Mono.ret _) fun matrices ↦ ?_
  exact Mono.bind (Mono.requireZero _) fun _ ↦ Mono.ret _

/-! ## The judgment under a condition on the final channel -/

section Judgment

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- **`Sim`, for the runs ending in `Q`**: from every coupled channel whose run of `u` ends in a channel satisfying
`Q`, the success and the failure clauses of `Sim`. -/
def SimQ (Q : Chan → Prop) (st : RecState) {α β : Type} (p : Prog α) (u : ChanM Id β) (n ch : Nat)
    (R : RecState → α → β → Prop) : Prop :=
  ∀ c, Couple π iv publicInput stream st c → c.cursor ≤ c.data.size → Q ((u.run).run c).2 →
    (c.cursor + n ≤ c.data.size →
      ∃ b c', (u.run).run c = (.ok b, c') ∧ Couple π iv publicInput stream (p.record st).2 c' ∧
        c'.cursor = c.cursor + n ∧ c'.challenges.size = c.challenges.size + ch ∧
        Grows st (p.record st).2 ∧ R (p.record st).2 (p.record st).1 b) ∧
    (c.data.size < c.cursor + n → (∃ e c', (u.run).run c = (.error e, c')) ∧ c.data.size < (p.record st).2.cursor)

variable {π iv publicInput stream}

theorem SimQ.of_sim {Q : Chan → Prop} {st : RecState} {α β : Type} {p : Prog α} {u : ChanM Id β} {n ch : Nat}
    {R : RecState → α → β → Prop} (h : Sim π iv publicInput stream st p u n ch R) :
    SimQ π iv publicInput stream Q st p u n ch R :=
  fun c hc hle _ ↦ h c hc hle

theorem SimQ.cast {Q : Chan → Prop} {st : RecState} {α β : Type} {p : Prog α} {u : ChanM Id β} {n n' ch ch' : Nat}
    {R : RecState → α → β → Prop} (hn : n = n') (hch : ch = ch') (h : SimQ π iv publicInput stream Q st p u n ch R) :
    SimQ π iv publicInput stream Q st p u n' ch' R := by
  subst hn hch; exact h

theorem SimQ.congr {Q : Chan → Prop} {st : RecState} {α β : Type} {p p' : Prog α} {u u' : ChanM Id β} {n ch : Nat}
    {R : RecState → α → β → Prop} (hp : p = p') (hu : u = u') (h : SimQ π iv publicInput stream Q st p u n ch R) :
    SimQ π iv publicInput stream Q st p' u' n ch R := by
  subst hp hu; exact h

theorem SimQ.of_good {Q : Chan → Prop} {st : RecState} {α β : Type} {p : Prog α} {u : ChanM Id β} {n ch : Nat}
    {R : RecState → α → β → Prop} (h : Good st → SimQ π iv publicInput stream Q st p u n ch R) :
    SimQ π iv publicInput stream Q st p u n ch R :=
  fun c hc hle hq ↦ h hc.good c hc hle hq

/-- **A `Sim` first, then a `SimQ`.** -/
theorem SimQ.bind {Q : Chan → Prop} {st : RecState} {α β γ δ : Type} {p : Prog α} {u : ChanM Id β} {n ch : Nat}
    {R : RecState → α → β → Prop} {k : α → Prog γ} {f : β → ChanM Id δ} {m ch' : Nat}
    {S : RecState → γ → δ → Prop}
    (h1 : Sim π iv publicInput stream st p u n ch R)
    (h2 : ∀ st' a b, Good st' → Grows st st' → R st' a b → SimQ π iv publicInput stream Q st' (k a) (f b) m ch' S) :
    SimQ π iv publicInput stream Q st (p >>= k) (u >>= f) (n + m) (ch + ch') S := by
  intro c hc hle hq
  obtain ⟨hs1, hf1⟩ := h1 c hc hle
  rw [record_bind]
  refine ⟨fun hr ↦ ?_, fun hr ↦ ?_⟩
  · obtain ⟨b, c', hu, hc', hcur, hch, hg, hR⟩ := hs1 (by omega)
    have hd : c'.data = c.data := hc'.data.trans hc.data.symm
    rw [run_bind_ok f hu] at hq
    obtain ⟨hs2, _⟩ := h2 _ _ _ hc'.good hg hR c' hc' (by rw [hd, hcur]; omega) hq
    obtain ⟨b2, c2, hu2, hc2, hcur2, hch2, hg2, hS⟩ := hs2 (by rw [hd, hcur]; omega)
    exact ⟨b2, c2, by rw [run_bind_ok f hu, hu2], hc2, by rw [hcur2, hcur, Nat.add_assoc],
      by rw [hch2, hch, Nat.add_assoc], hg.trans hg2, hS⟩
  · by_cases h : c.data.size < c.cursor + n
    · obtain ⟨⟨e, c', hu⟩, hlt⟩ := hf1 h
      exact ⟨⟨e, c', run_bind_error f hu⟩, lt_of_lt_of_le hlt (record_cursor_le _ _)⟩
    · obtain ⟨b, c', hu, hc', hcur, _, hg, hR⟩ := hs1 (by omega)
      have hd : c'.data = c.data := hc'.data.trans hc.data.symm
      rw [run_bind_ok f hu] at hq
      obtain ⟨_, hf2⟩ := h2 _ _ _ hc'.good hg hR c' hc' (by rw [hd, hcur]; omega) hq
      obtain ⟨⟨e, c2, hu2⟩, hlt⟩ := hf2 (by rw [hd, hcur]; omega)
      exact ⟨⟨e, c2, by rw [run_bind_ok f hu, hu2]⟩, by rw [← hd]; exact hlt⟩

/-- **A pure part first, then a `SimQ`**: the continuation from the pure step's end. -/
theorem SimQ.pbind {Q : Chan → Prop} {st : RecState} {α β γ δ : Type} {p : Prog α} {b : β}
    {R : RecState → α → β → Prop} {k : α → Prog γ} {u : ChanM Id δ} {m ch : Nat} {S : RecState → γ → δ → Prop}
    (h1 : PSim st p b R)
    (h2 : ∀ st' a, PStep st st' → R st' a b → SimQ π iv publicInput stream Q st' (k a) u m ch S) :
    SimQ π iv publicInput stream Q st (p >>= k) u m ch S := by
  intro c hc hle hq
  obtain ⟨hp, hR⟩ := h1
  have hc' := hc.pstep π iv publicInput stream hp
  obtain ⟨hs, hf⟩ := h2 _ _ hp hR c hc' hle hq
  rw [record_bind]
  refine ⟨fun hr ↦ ?_, hf⟩
  obtain ⟨b2, c2, hu2, hc2, hcur2, hch2, hg2, hS⟩ := hs hr
  exact ⟨b2, c2, hu2, hc2, hcur2, hch2, hp.grows.trans hg2, hS⟩

/-- **A pure part first, then a `Sim`.** -/
theorem Sim.pbind' {st : RecState} {α β γ δ : Type} {p : Prog α} {b : β}
    {R : RecState → α → β → Prop} {k : α → Prog γ} {u : ChanM Id δ} {m ch : Nat} {S : RecState → γ → δ → Prop}
    (h1 : PSim st p b R)
    (h2 : ∀ st' a, PStep st st' → R st' a b → Sim π iv publicInput stream st' (k a) u m ch S) :
    Sim π iv publicInput stream st (p >>= k) u m ch S := by
  intro c hc hle
  obtain ⟨hp, hR⟩ := h1
  have hc' := hc.pstep π iv publicInput stream hp
  obtain ⟨hs, hf⟩ := h2 _ _ hp hR c hc' hle
  rw [record_bind]
  refine ⟨fun hr ↦ ?_, hf⟩
  obtain ⟨b2, c2, hu2, hc2, hcur2, hch2, hg2, hS⟩ := hs hr
  exact ⟨b2, c2, hu2, hc2, hcur2, hch2, hp.grows.trans hg2, hS⟩

/-- **A `Sim` under a premise `P`**; off `P`, no run from a coupled channel ends in `Q`. -/
theorem SimQ.of_cond {Q : Chan → Prop} {st : RecState} {α β : Type} {p : Prog α} {u : ChanM Id β} {n ch : Nat}
    {R : RecState → α → β → Prop} (P : Prop) (h : P → Sim π iv publicInput stream st p u n ch R)
    (hQ : ¬ P → ∀ c, Couple π iv publicInput stream st c → ¬ Q ((u.run).run c).2) :
    SimQ π iv publicInput stream Q st p u n ch R := by
  intro c hc hle hq
  by_cases hP : P
  · exact h hP c hc hle
  · exact absurd hq (hQ hP c hc)

/-- **The cursor**, `n` further. -/
theorem Sim.withCursor {st : RecState} {α β : Type} {p : Prog α} {u : ChanM Id β} {n ch : Nat}
    {R : RecState → α → β → Prop} (h : Sim π iv publicInput stream st p u n ch R) :
    Sim π iv publicInput stream st p u n ch (fun st' a b ↦ R st' a b ∧ st'.cursor = st.cursor + n) := by
  intro c hc hle
  obtain ⟨hs, hf⟩ := h c hc hle
  refine ⟨fun hr ↦ ?_, hf⟩
  obtain ⟨b, c', hu, hc', hcur, hch, hg, hR⟩ := hs hr
  exact ⟨b, c', hu, hc', hcur, hch, hg, hR, by rw [← hc'.cursor, hcur, hc.cursor]⟩

/-- **The challenge nodes**, as many more as the challenges drawn. -/
theorem Sim.withChIds {st : RecState} {α β : Type} {p : Prog α} {u : ChanM Id β} {n ch : Nat}
    {R : RecState → α → β → Prop} (h : Sim π iv publicInput stream st p u n ch R) :
    Sim π iv publicInput stream st p u n ch
      (fun st' a b ↦ R st' a b ∧ ∃ l, chIds st' = chIds st ++ l ∧ l.length = ch) := by
  intro c hc hle
  obtain ⟨hs, hf⟩ := h c hc hle
  refine ⟨fun hr ↦ ?_, hf⟩
  obtain ⟨b, c', hu, hc', hcur, hch, hg, hR⟩ := hs hr
  obtain ⟨l, hl⟩ := chIds_grows hg
  refine ⟨b, c', hu, hc', hcur, hch, hg, hR, l, hl, ?_⟩
  have e1 := congrArg List.length hc.chal
  have e2 := congrArg List.length hc'.chal
  simp only [Array.length_toList, List.length_map] at e1 e2
  rw [hl, List.length_append] at e2
  omega

end Judgment

end RecGraph.Sim
