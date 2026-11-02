-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The WHIR prover (`roundA`, `foldRoundsA`, `levelsA`, `openingFast`, this repository's
-- `openingScript`) and the scripts' language (`Script`, `Script.bind`, the moves `msgOf`, `afterSend`,
-- `afterSample`, `afterGrind`, `wordOf`, `afterCommit`, `afterQuery`) are leanerVM's (branch `mumbai`,
-- commit 6175f1a0, MIT OR Apache-2.0: `Statement/Prover/Whir.lean`, `Statement/Prover/Script.lean`,
-- `Statement/Prover/Run.lean`).
import ZK.CoreDrive

/-!
# Scripts making the same moves along a path

The renderer drives a script by an opening's events (`Render.evRun`), the statement runs one
(`runEvS`); both feed it challenges and read its moves, nothing else. Two scripts that make the same
moves along the challenges they are fed are then run alike:

* **`AgreeK Q cs S S'`**: `S` and `S'` make the same moves (the same scalars, words, grinding,
  queries) while they receive the challenges `cs`, in order; at the first sample past `cs` they may
  differ; where both return, `Q` holds of the values and the challenges left. `Agree` for `Q` true.
* **`evRun_congr`**: the drive is the same for two scripts agreeing along the draws' challenges
  (`drawChal`), with commitments that agree where the events open them (`CRel`, `PosOK`);
* **`runEvS_congr`**: the statement's run is the same for two scripts agreeing along the challenges
  the run itself squeezes (`chalsEvS`);
* **`agree_hybrid`**: two hybrid scripts (`hybridScript`) agree along `cs` when their lane rounds agree
  below `cs`'s length and their folded tables once `cs` has the seven lane challenges;
* **`agree_hybrid_honest`**: the hybrid script agrees with the honest one (`openingScript`) along `cs`
  when its lane round `j` is mumbai's round message of the weight and stack tables folded by the
  challenges `1 … j` of `cs` (`roundMsgArr`) and its folded table the stack table folded by the
  challenges `1 … 6` (`foldsA`), the weight table batched by the powers of `cs`'s first.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Complete
open QuotientZk.Deployed (Out Msg Item positionsOf sortedUnique)

namespace PcsQuotient.EndToEnd.Core

open Render (limbsOf evRun lastMsg RunSt sendsN drawChal roundMsgA laneFoldsH levelTailA
  hybridScript)

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

/-! ## Same moves along a path -/

/-- **`S` and `S'` make the same moves along the challenges `cs`**: the same scalars, words,
grinding and queries (for every rows given), each sample receiving the next challenge of `cs`; at a
sample past `cs` anything; where both return, `Q` of the values and the challenges left. -/
inductive AgreeK {α β : Type} (Q : α → β → List E → Prop) : List E → Script α → Script β → Prop
  | ret {cs : List E} {a : α} {b : β} : Q a b cs → AgreeK Q cs (.ret a) (.ret b)
  | send {cs : List E} (x : E) {k : Script α} {k' : Script β} : AgreeK Q cs k k' →
      AgreeK Q cs (.send x k) (.send x k')
  | grind {cs : List E} {k : Script α} {k' : Script β} : AgreeK Q cs k k' →
      AgreeK Q cs (.grind k) (.grind k')
  | commit {cs : List E} (w : Word) {k : Script α} {k' : Script β} : AgreeK Q cs k k' →
      AgreeK Q cs (.commit w k) (.commit w k')
  | query {cs : List E} {k : List (List K) → Script α} {k' : List (List K) → Script β} :
      (∀ r, AgreeK Q cs (k r) (k' r)) → AgreeK Q cs (.query k) (.query k')
  | stop {k : E → Script α} {k' : E → Script β} : AgreeK Q [] (.sample k) (.sample k')
  | sample {c : E} {cs : List E} {k : E → Script α} {k' : E → Script β} :
      AgreeK Q cs (k c) (k' c) → AgreeK Q (c :: cs) (.sample k) (.sample k')

/-- Same moves along `cs`, whatever the values. -/
abbrev Agree (cs : List E) (S S' : Script Unit) : Prop := AgreeK (fun _ _ _ ↦ True) cs S S'

theorem AgreeK.mono {α β : Type} {Q Q' : α → β → List E → Prop} (hQ : ∀ a b cs, Q a b cs → Q' a b cs)
    {cs : List E} {S : Script α} {S' : Script β} (h : AgreeK Q cs S S') : AgreeK Q' cs S S' := by
  induction h with
  | ret h => exact .ret (hQ _ _ _ h)
  | send x _ ih => exact .send x ih
  | grind _ ih => exact .grind ih
  | commit w _ ih => exact .commit w ih
  | query _ ih => exact .query ih
  | stop => exact .stop
  | sample _ ih => exact .sample ih

/-- **Sequencing**: agreeing scripts, then continuations agreeing from what they return. -/
theorem AgreeK.bind {α β γ δ : Type} {Q : α → β → List E → Prop} {R : γ → δ → List E → Prop}
    {f : α → Script γ} {f' : β → Script δ} (hf : ∀ a b cs, Q a b cs → AgreeK R cs (f a) (f' b))
    {cs : List E} {S : Script α} {S' : Script β} (h : AgreeK Q cs S S') :
    AgreeK R cs (S.bind f) (S'.bind f') := by
  induction h with
  | ret h => exact hf _ _ _ h
  | send x _ ih => exact .send x ih
  | grind _ ih => exact .grind ih
  | commit w _ ih => exact .commit w ih
  | query _ ih => exact .query ih
  | stop => exact .stop
  | sample _ ih => exact .sample ih

/-- A script agrees with itself, along any challenges. -/
theorem AgreeK.refl {α : Type} : ∀ (S : Script α) (cs : List E), AgreeK (fun a b _ ↦ a = b) cs S S
  | .ret _, _ => .ret rfl
  | .send x k, cs => .send x (AgreeK.refl k cs)
  | .grind k, cs => .grind (AgreeK.refl k cs)
  | .commit w k, cs => .commit w (AgreeK.refl k cs)
  | .query k, cs => .query fun r ↦ AgreeK.refl (k r) cs
  | .sample _, [] => .stop
  | .sample k, c :: cs => .sample (AgreeK.refl (k c) cs)

theorem Agree.refl (S : Script Unit) (cs : List E) : Agree cs S S :=
  (AgreeK.refl S cs).mono fun _ _ _ _ ↦ trivial

theorem Script.bind_assoc' {α β γ : Type} : ∀ (S : Script α) (f : α → Script β) (f₂ : β → Script γ),
    (S.bind f).bind f₂ = S.bind fun a ↦ (f a).bind f₂
  | .ret _, _, _ => rfl
  | .send x k, f, f₂ => congrArg (Script.send x) (Script.bind_assoc' k f f₂)
  | .sample k, f, f₂ => congrArg Script.sample (funext fun c ↦ Script.bind_assoc' (k c) f f₂)
  | .grind k, f, f₂ => congrArg Script.grind (Script.bind_assoc' k f f₂)
  | .commit w k, f, f₂ => congrArg (Script.commit w) (Script.bind_assoc' k f f₂)
  | .query k, f, f₂ => congrArg Script.query (funext fun r ↦ Script.bind_assoc' (k r) f f₂)

/-! ## The moves of agreeing scripts -/

/-- Agreement of a run's scripts (`none` once a script has left the events). -/
def OAgree (cs : List E) : Option (Script Unit) → Option (Script Unit) → Prop
  | none, none => True
  | some S, some S' => Agree cs S S'
  | _, _ => False

namespace OAgree

variable {cs : List E}

theorem msgOf : ∀ {S S' : Option (Script Unit)}, OAgree cs S S' → Script.msgOf S = Script.msgOf S'
  | none, none, _ => rfl
  | some _, some _, h => by cases h <;> rfl

theorem wordOf : ∀ {S S' : Option (Script Unit)}, OAgree cs S S' → Script.wordOf S = Script.wordOf S'
  | none, none, _ => rfl
  | some _, some _, h => by cases h <;> rfl

theorem afterSend : ∀ {S S' : Option (Script Unit)}, OAgree cs S S' →
    OAgree cs (Script.afterSend S) (Script.afterSend S')
  | none, none, _ => trivial
  | some _, some _, h => by
    cases h with
    | send _ h => exact h
    | _ => trivial

theorem afterGrind : ∀ {S S' : Option (Script Unit)}, OAgree cs S S' →
    OAgree cs (Script.afterGrind S) (Script.afterGrind S')
  | none, none, _ => trivial
  | some _, some _, h => by
    cases h with
    | grind h => exact h
    | _ => trivial

theorem afterCommit : ∀ {S S' : Option (Script Unit)}, OAgree cs S S' →
    OAgree cs (Script.afterCommit S) (Script.afterCommit S')
  | none, none, _ => trivial
  | some _, some _, h => by
    cases h with
    | commit _ h => exact h
    | _ => trivial

theorem afterQuery (rows : List (List K)) : ∀ {S S' : Option (Script Unit)}, OAgree cs S S' →
    OAgree cs (Script.afterQuery rows S) (Script.afterQuery rows S')
  | none, none, _ => trivial
  | some _, some _, h => by
    cases h with
    | query h => exact h rows
    | _ => trivial

theorem afterSample {c : E} : ∀ {S S' : Option (Script Unit)}, OAgree (c :: cs) S S' →
    OAgree cs (Script.afterSample c S) (Script.afterSample c S')
  | none, none, _ => trivial
  | some _, some _, h => by
    cases h with
    | sample h => exact h
    | _ => trivial

theorem sendsN : ∀ (k : ℕ) {S S' : Option (Script Unit)}, OAgree cs S S' →
    (Render.sendsN k S).1 = (Render.sendsN k S').1 ∧
      OAgree cs (Render.sendsN k S).2 (Render.sendsN k S').2
  | 0, _, _, h => ⟨rfl, h⟩
  | k + 1, S, S', h => by
    obtain ⟨h1, h2⟩ := OAgree.sendsN k h.afterSend
    refine ⟨?_, h2⟩
    show Script.msgOf S :: (Render.sendsN k (Script.afterSend S)).1 =
      Script.msgOf S' :: (Render.sendsN k (Script.afterSend S')).1
    rw [h.msgOf, h1]

theorem sendsS (π : Equiv.Perm Eager.St) : ∀ (k : ℕ) {S S' : Option (Script Unit)} (sp : Sponge),
    OAgree cs S S' →
    (Core.sendsS π k S sp).1 = (Core.sendsS π k S' sp).1 ∧
      (Core.sendsS π k S sp).2.2 = (Core.sendsS π k S' sp).2.2 ∧
      OAgree cs (Core.sendsS π k S sp).2.1 (Core.sendsS π k S' sp).2.1
  | 0, _, _, _, h => ⟨rfl, rfl, h⟩
  | k + 1, S, S', sp, h => by
    have hm := h.msgOf
    obtain ⟨h1, h2, h3⟩ := OAgree.sendsS π k (absorb (permId π) sp (Script.msgOf S) dsObserve).run
      h.afterSend
    simp only [Core.sendsS]
    rw [← hm]
    exact ⟨by rw [h1], h2, h3⟩

end OAgree

/-! ## The drive of agreeing scripts -/

/-- **The commitments agree where `G` holds**: the same after the first, the first of the same height
and the same rows at the positions satisfying `G`. -/
def CRel (G : ℕ → Prop) (cs cs' : List (ℕ × Word)) : Prop :=
  ∃ c c' rest, cs = c :: rest ∧ cs' = c' :: rest ∧ c.1 = c'.1 ∧
    ∀ p, G p → c.2 (p % 2 ^ c.1) = c'.2 (p % 2 ^ c.1)

theorem CRel.append {G : ℕ → Prop} {cs cs' : List (ℕ × Word)} (h : CRel G cs cs') (x : ℕ × Word) :
    CRel G (cs ++ [x]) (cs' ++ [x]) := by
  obtain ⟨c, c', rest, rfl, rfl, h1, h2⟩ := h
  exact ⟨c, c', rest ++ [x], rfl, rfl, h1, h2⟩

theorem CRel.rows {G : ℕ → Prop} {cs cs' : List (ℕ × Word)} (h : CRel G cs cs') (lvl : ℕ)
    (ps : List ℕ) (hps : lvl = 0 → ∀ p ∈ ps, G p) :
    (cs.getD lvl (0, fun _ ↦ [])).1 = (cs'.getD lvl (0, fun _ ↦ [])).1 ∧
      ∀ p ∈ ps, (cs.getD lvl (0, fun _ ↦ [])).2 (p % 2 ^ (cs.getD lvl (0, fun _ ↦ [])).1) =
        (cs'.getD lvl (0, fun _ ↦ [])).2 (p % 2 ^ (cs'.getD lvl (0, fun _ ↦ [])).1) := by
  obtain ⟨c, c', rest, rfl, rfl, h1, h2⟩ := h
  rcases lvl with _ | n
  · simp only [List.getD_cons_zero]
    exact ⟨h1, fun p hp ↦ by rw [← h1]; exact h2 p (hps rfl p hp)⟩
  · exact ⟨rfl, fun _ _ ↦ rfl⟩

/-- **The positions the events open at commitment `0` satisfy `G`**, the challenges `chs` answering
the draws. -/
def PosOK (G : ℕ → Prop) : List Render.Ev → List Out → List QuotientRpm.Limbs → Prop
  | [], _, _ => True
  | .draw :: _, [], _ => True
  | .draw :: evs, _ :: chs, pl => PosOK G evs chs pl
  | .posDraw :: _, [], _ => True
  | .posDraw :: evs, o :: chs, pl => PosOK G evs chs (pl ++ [(o.2[0], o.2[1], o.2[2])])
  | .send _ :: evs, chs, pl => PosOK G evs chs pl
  | .commit _ :: evs, chs, pl => PosOK G evs chs pl
  | .grind :: evs, chs, pl => PosOK G evs chs pl
  | .opened lvl q b :: evs, chs, pl => (lvl = 0 → ∀ p ∈ posOf pl b q, G p) ∧ PosOK G evs chs []

/-- **The drive of two agreeing scripts**: along the draws' challenges, with commitments agreeing at
the positions opened at commitment `0`, the same messages. -/
theorem evRun_congr (G : ℕ → Prop) : ∀ (evs : List Render.Ev) (chs : List Out) (st st' : RunSt),
    OAgree (chs.map drawChal) st.script st'.script → CRel G st.comms st'.comms →
    st.posLimbs = st'.posLimbs → st.acc = st'.acc → st.done = st'.done →
    PosOK G evs chs st.posLimbs → evRun evs chs st = evRun evs chs st'
  | [], _, st, st', _, _, _, ha, hd, _ => by simp only [evRun]; rw [ha, hd]
  | .draw :: _, [], st, st', _, _, _, ha, hd, _ => by simp only [evRun]; rw [ha, hd]
  | .draw :: evs, o :: chs, st, st', hS, hC, hp, ha, hd, hP => by
    simp only [evRun]
    exact evRun_congr G evs chs _ _ (OAgree.afterSample hS) hC hp rfl (by rw [ha, hd]) hP
  | .posDraw :: _, [], st, st', _, _, _, ha, hd, _ => by simp only [evRun]; rw [ha, hd]
  | .posDraw :: evs, o :: chs, st, st', hS, hC, hp, ha, hd, hP => by
    simp only [evRun]
    exact evRun_congr G evs chs _ _ (OAgree.afterSample hS) hC (by rw [hp]) rfl (by rw [ha, hd]) hP
  | .send k :: evs, chs, st, st', hS, hC, hp, ha, hd, hP => by
    simp only [evRun]
    obtain ⟨h1, h2⟩ := OAgree.sendsN k hS
    exact evRun_congr G evs chs _ _ h2 hC hp (by simp only; rw [ha, h1]) hd hP
  | .commit d :: evs, chs, st, st', hS, hC, hp, ha, hd, hP => by
    simp only [evRun]
    have hw := hS.wordOf
    refine evRun_congr G evs chs _ _ hS.afterCommit ?_ hp (by simp only; rw [ha, hw]) hd hP
    simp only
    rw [hw]
    exact hC.append _
  | .grind :: evs, chs, st, st', hS, hC, hp, ha, hd, hP => by
    simp only [evRun]
    exact evRun_congr G evs chs _ _ hS.afterGrind hC hp ha hd hP
  | .opened lvl q b :: evs, chs, st, st', hS, hC, hp, ha, hd, hP => by
    simp only [evRun]
    obtain ⟨hP0, hP1⟩ := hP
    obtain ⟨h1, h2⟩ := hC.rows lvl _ hP0
    have hr : ((st.posLimbs.flatMap (positionsOf (max b 1))).take q).map (fun p ↦
        (st.comms.getD lvl (0, fun _ ↦ [])).2 (p % 2 ^ (st.comms.getD lvl (0, fun _ ↦ [])).1)) =
        ((st'.posLimbs.flatMap (positionsOf (max b 1))).take q).map (fun p ↦
        (st'.comms.getD lvl (0, fun _ ↦ [])).2 (p % 2 ^ (st'.comms.getD lvl (0, fun _ ↦ [])).1)) := by
      rw [← hp]
      exact List.map_congr_left fun p hp' ↦ h2 p hp'
    have ho : (sortedUnique ((st.posLimbs.flatMap (positionsOf (max b 1))).take q)).map (fun p ↦
        ((st.comms.getD lvl (0, fun _ ↦ [])).2
          (p % 2 ^ (st.comms.getD lvl (0, fun _ ↦ [])).1)).map K.lane) =
        (sortedUnique ((st'.posLimbs.flatMap (positionsOf (max b 1))).take q)).map (fun p ↦
        ((st'.comms.getD lvl (0, fun _ ↦ [])).2
          (p % 2 ^ (st'.comms.getD lvl (0, fun _ ↦ [])).1)).map K.lane) := by
      rw [← hp]
      exact List.map_congr_left fun p hp' ↦ by
        rw [h2 p (Merkle.mem_sortedUnique.mp hp')]
    rw [hr, ho]
    exact evRun_congr G evs chs _ _ (OAgree.afterQuery _ hS) hC rfl (by simp only; rw [ha]) hd hP1

/-! ## The statement's run of agreeing scripts -/

section Run

variable (π : Equiv.Perm Eager.St) (fuel : ℕ)

/-- **The challenges the statement's run squeezes at the events' draws** (`runEvS`'s, in order; up to
a proof of work that finds no nonce or an opening of a missing commitment). -/
def chalsEvS : List Render.Ev → Option (Script Unit) → Sponge → List Tree →
    List QuotientRpm.Limbs → List E
  | [], _, _, _, _ => []
  | .draw :: evs, S, sp, cs, pl =>
    let r := (squeeze (permId π) sp).run
    r.1 :: chalsEvS evs (Script.afterSample r.1 S) r.2 cs pl
  | .posDraw :: evs, S, sp, cs, pl =>
    let r := (squeeze (permId π) sp).run
    r.1 :: chalsEvS evs (Script.afterSample r.1 S) r.2 cs (pl ++ [Render.limbsOf r.1])
  | .send k :: evs, S, sp, cs, pl =>
    let r := sendsS π k S sp
    chalsEvS evs r.2.1 r.2.2 cs pl
  | .commit d :: evs, S, sp, cs, pl =>
    let tree := (buildTreeM (permId π) d (Script.wordOf S)).run
    let sp0 := (absorb (permId π) sp (digestScalars tree.root).1 dsObserve).run
    let sp1 := (absorb (permId π) sp0 (digestScalars tree.root).2 dsObserve).run
    chalsEvS evs (Script.afterCommit S) sp1 (cs ++ [tree]) pl
  | .grind :: evs, S, sp, cs, pl =>
    match (findNonceM (permId π) 17 sp fuel).run with
    | none => []
    | some n => chalsEvS evs (Script.afterGrind S) (powStepM (permId π) sp n).run.2 cs pl
  | .opened lvl q b :: evs, S, sp, cs, pl =>
    match cs[lvl]? with
    | none => []
    | some tree =>
      chalsEvS evs (Script.afterQuery ((posOf pl b q).map fun p ↦ tree.word (p % 2 ^ tree.height)) S)
        sp cs []

/-- **The statement's run of two scripts agreeing along the challenges it squeezes** is the same. -/
theorem runEvS_congr : ∀ (evs : List Render.Ev) (S S' : Option (Script Unit)) (sp : Sponge)
    (cs : List Tree) (pl : List QuotientRpm.Limbs), OAgree (chalsEvS π fuel evs S sp cs pl) S S' →
    runEvS π fuel evs S sp cs pl = runEvS π fuel evs S' sp cs pl
  | [], _, _, _, _, _, _ => rfl
  | .draw :: evs, S, S', sp, cs, pl, h => by
    simp only [runEvS]
    exact runEvS_congr evs _ _ _ cs pl (OAgree.afterSample h)
  | .posDraw :: evs, S, S', sp, cs, pl, h => by
    simp only [runEvS]
    exact runEvS_congr evs _ _ _ cs _ (OAgree.afterSample (c := (squeeze (permId π) sp).run.1) h)
  | .send k :: evs, S, S', sp, cs, pl, h => by
    simp only [runEvS]
    obtain ⟨h1, h2, h3⟩ := OAgree.sendsS π k sp h
    rw [← h1, ← h2, runEvS_congr evs _ _ _ cs pl h3]
  | .commit d :: evs, S, S', sp, cs, pl, h => by
    simp only [runEvS]
    have hw := h.wordOf
    have h' := h.afterCommit
    rw [← hw, runEvS_congr evs _ _ _ _ pl h']
  | .grind :: evs, S, S', sp, cs, pl, h => by
    rw [runEvS_grind, runEvS_grind]
    unfold chalsEvS at h
    revert h
    rcases (findNonceM (permId π) 17 sp fuel).run with _ | n
    · intro _; rfl
    · intro h; simp only; exact congrArg _ (runEvS_congr evs _ _ _ cs pl (OAgree.afterGrind h))
  | .opened lvl q b :: evs, S, S', sp, cs, pl, h => by
    rw [runEvS_opened, runEvS_opened]
    unfold chalsEvS at h
    revert h
    rcases cs[lvl]? with _ | tree
    · intro _; rfl
    · intro h; simp only; exact congrArg _ (runEvS_congr evs _ _ _ cs [] (OAgree.afterQuery _ h))

end Run

/-! ## The hybrid scripts -/

/-- A round message given by its two scalars is mumbai's round of the tables giving them. -/
theorem roundMsgA_eq (claim : E) (W T : Array E) :
    roundMsgA claim (roundC0A W T, roundC2A W T) = roundA claim W T := rfl

/-- **A level of `levelsA`**: its fold rounds, then the rest of the level (`levelTailA`). -/
theorem levelsA_cons (μ : ℕ) (level : Whir.Level) (rest : List Whir.Level) (s : WhirState)
    (W T : Array E) :
    levelsA μ 0 (level :: rest) s W T = (foldRoundsA level.fold s [] W T).bind
      fun r ↦ levelTailA μ 0 level rest r.1 r.2.1 r.2.2.1 r.2.2.2 := rfl

/-- **The hybrid script after its lane rounds**: the last lane challenge `φ`, the round of the folded
weight table against the view's folded table `f1`, then mumbai's level from `f1`. -/
def hybK (μ : ℕ) (level : Whir.Level) (rest : List Whir.Level) (f1 : Array E)
    (r : WhirState × List E × Array E) : Script Unit :=
  Script.sample fun φ ↦ (roundA (polyEval r.1.quad φ) (foldPairsW φ r.2.2) f1).bind fun quad ↦
    levelTailA μ 0 level rest { r.1 with quad, folds := r.1.folds ++ [φ] } (r.2.1 ++ [φ])
      (foldPairsW φ r.2.2) f1

/-- **The hybrid script**, its ladder starting with `level`. -/
theorem hybridScript_eq (L : PcsQuotient.Layout) (claims : List PcsQuotient.Claim)
    (lane : ℕ → E × E) (f1 : Array E) {level : Whir.Level} {rest : List Whir.Level}
    (hl : Whir.ladder L.logN PcsQuotient.logInvRate = some (level :: rest)) :
    hybridScript L claims lane f1 = Script.sample fun c ↦
      (roundMsgA (dot (powers c (PcsQuotient.stackClaims L claims).length)
          ((PcsQuotient.stackClaims L claims).map (·.2))) (lane 0)).bind fun quad ↦
        (laneFoldsH lane (level.fold - 1) 1 ⟨quad, [], []⟩ []
          (PcsQuotient.weightTable L (powers c (PcsQuotient.stackClaims L claims).length)
            claims)).bind (hybK L.logN level rest f1) := by
  unfold hybridScript
  rw [hl]
  rfl

/-- **The honest script**, its ladder `level :: rest`. -/
theorem openingScript_eq (L : PcsQuotient.Layout) (stack : Array K)
    (claims : List PcsQuotient.Claim) {level : Whir.Level} {rest : List Whir.Level}
    (hl : Whir.ladder L.logN PcsQuotient.logInvRate = some (level :: rest)) :
    PcsQuotient.openingScript L stack claims = Script.sample fun c ↦
      (roundA (dot (powers c (PcsQuotient.stackClaims L claims).length)
          ((PcsQuotient.stackClaims L claims).map (·.2)))
        (PcsQuotient.weightTable L (powers c (PcsQuotient.stackClaims L claims).length) claims)
        (stackTableA L.logN stack)).bind fun quad ↦
        levelsA L.logN 0 (level :: rest) ⟨quad, [], []⟩
          (PcsQuotient.weightTable L (powers c (PcsQuotient.stackClaims L claims).length) claims)
          (stackTableA L.logN stack) := by
  unfold PcsQuotient.openingScript
  rw [hl]
  rfl

/-- Lane rounds of two lane functions agreeing below the challenges' count. -/
theorem laneFoldsH_agree (lane lane' : ℕ → E × E) {Kc Kc' : WhirState × List E × Array E → Script Unit} :
    ∀ (m j : ℕ) (s : WhirState) (lf : List E) (W : Array E) (cs : List E),
    (∀ i < m, i < cs.length → lane (j + i) = lane' (j + i)) →
    (m ≤ cs.length → ∀ r, Agree (cs.drop m) (Kc r) (Kc' r)) →
    Agree cs ((laneFoldsH lane m j s lf W).bind Kc) ((laneFoldsH lane' m j s lf W).bind Kc')
  | 0, _, _, _, _, _, _, hK => hK (Nat.zero_le _) _
  | _ + 1, _, _, _, _, [], _, _ => .stop
  | m + 1, j, s, lf, W, c :: cs, hl, hK => by
    have h0 : lane j = lane' j := hl 0 (by omega) (by simp)
    refine .sample ?_
    show Agree cs (((roundMsgA (polyEval s.quad c) (lane j)).bind fun quad ↦
        laneFoldsH lane m (j + 1) { s with quad, folds := s.folds ++ [c] } (lf ++ [c])
          (foldPairsW c W)).bind Kc)
      (((roundMsgA (polyEval s.quad c) (lane' j)).bind fun quad ↦
        laneFoldsH lane' m (j + 1) { s with quad, folds := s.folds ++ [c] } (lf ++ [c])
          (foldPairsW c W)).bind Kc')
    rw [h0, Script.bind_assoc', Script.bind_assoc']
    refine .send _ (.send _ (laneFoldsH_agree lane lane' m (j + 1) _ _ _ cs (fun i hi hic ↦ ?_)
      (fun hm r ↦ hK (by simp only [List.length_cons]; omega) r)))
    have := hl (i + 1) (by omega) (by simp only [List.length_cons]; omega)
    rwa [show j + (i + 1) = j + 1 + i by omega] at this

/-- **Two hybrid scripts agree along `cs`** when their lane rounds agree below `cs`'s length and their
folded tables once `cs` has the seven lane challenges. -/
theorem agree_hybrid (L : PcsQuotient.Layout) (claims : List PcsQuotient.Claim)
    (lane lane' : ℕ → E × E) (f1 f1' : Array E) {level : Whir.Level} {rest : List Whir.Level}
    (hl : Whir.ladder L.logN PcsQuotient.logInvRate = some (level :: rest)) (hfold : level.fold = 6)
    (cs : List E) (hlane : ∀ j, j < cs.length → lane j = lane' j) (hf : 7 ≤ cs.length → f1 = f1') :
    Agree cs (hybridScript L claims lane f1) (hybridScript L claims lane' f1') := by
  rw [hybridScript_eq L claims lane f1 hl, hybridScript_eq L claims lane' f1' hl, hfold]
  rcases cs with _ | ⟨c, cs⟩
  · exact .stop
  refine .sample ?_
  rw [hlane 0 (by simp)]
  refine .send _ (.send _ (laneFoldsH_agree lane lane' (6 - 1) 1 _ _ _ cs
    (fun i _ hic ↦ hlane (1 + i) (by simp only [List.length_cons]; omega)) fun hm r ↦ ?_))
  rcases hd : cs.drop (6 - 1) with _ | ⟨c', cs'⟩
  · exact .stop
  · have h7 : 7 ≤ (c :: cs).length := by
      have := congrArg List.length hd
      simp only [List.length_drop, List.length_cons] at this ⊢
      omega
    rw [hf h7]
    exact Agree.refl _ _

/-- Lane rounds from mumbai's round messages of the tables folded by the challenges, against mumbai's
fold rounds. -/
theorem laneFolds_honest (μ : ℕ) (level : Whir.Level) (rest : List Whir.Level) (f1 : Array E)
    (lane : ℕ → E × E) : ∀ (m j : ℕ) (s : WhirState) (lf : List E) (W T : Array E) (cs : List E),
    (∀ i < m, i < cs.length → lane (j + i) =
      (roundC0A (foldsA (cs.take (i + 1)) W) (foldsA (cs.take (i + 1)) T),
        roundC2A (foldsA (cs.take (i + 1)) W) (foldsA (cs.take (i + 1)) T))) →
    (m < cs.length → f1 = foldsA (cs.take (m + 1)) T) →
    Agree cs ((laneFoldsH lane m j s lf W).bind (hybK μ level rest f1))
      ((foldRoundsA (m + 1) s lf W T).bind fun r ↦ levelTailA μ 0 level rest r.1 r.2.1 r.2.2.1 r.2.2.2)
  | 0, _, _, _, _, _, [], _, _ => .stop
  | 0, j, s, lf, W, T, c :: cs, _, hf => by
    have e : f1 = foldPairsW c T := hf (by simp)
    subst e
    refine .sample ?_
    show Agree cs ((roundA (polyEval s.quad c) (foldPairsW c W) (foldPairsW c T)).bind _)
      (((roundA (polyEval s.quad c) (foldPairsW c W) (foldPairsW c T)).bind _).bind _)
    rw [Script.bind_assoc']
    exact Agree.refl _ _
  | _ + 1, _, _, _, _, _, [], _, _ => .stop
  | m + 1, j, s, lf, W, T, c :: cs, hl, hf => by
    have h0 : lane j = (roundC0A (foldPairsW c W) (foldPairsW c T),
        roundC2A (foldPairsW c W) (foldPairsW c T)) := hl 0 (by omega) (by simp)
    refine .sample ?_
    show Agree cs (((roundMsgA (polyEval s.quad c) (lane j)).bind fun quad ↦
        laneFoldsH lane m (j + 1) { s with quad, folds := s.folds ++ [c] } (lf ++ [c])
          (foldPairsW c W)).bind (hybK μ level rest f1))
      (((roundA (polyEval s.quad c) (foldPairsW c W) (foldPairsW c T)).bind fun quad ↦
        foldRoundsA (m + 1) { s with quad, folds := s.folds ++ [c] } (lf ++ [c]) (foldPairsW c W)
          (foldPairsW c T)).bind fun r ↦ levelTailA μ 0 level rest r.1 r.2.1 r.2.2.1 r.2.2.2)
    rw [h0, roundMsgA_eq, Script.bind_assoc', Script.bind_assoc']
    refine .send _ (.send _ (laneFolds_honest μ level rest f1 lane m (j + 1) _ _ _ _ cs
      (fun i hi hic ↦ ?_) (fun hm ↦ hf (by simp only [List.length_cons]; omega))))
    have := hl (i + 1) (by omega) (by simp only [List.length_cons]; omega)
    rwa [show j + (i + 1) = j + 1 + i by omega] at this

/-- **The hybrid script agrees with the honest one along `cs`** when its lane round `j < 6` (once
drawn for) is mumbai's round message of the weight table (batched by the powers of `cs`'s first
challenge) and the stack table, both folded by the challenges `1 … j` of `cs`, and its folded table
(once the seven are drawn) the stack table folded by the challenges `1 … 6`. -/
theorem agree_hybrid_honest (L : PcsQuotient.Layout) (stack : Array K)
    (claims : List PcsQuotient.Claim) (lane : ℕ → E × E) (f1 : Array E) {level : Whir.Level}
    {rest : List Whir.Level} (hl : Whir.ladder L.logN PcsQuotient.logInvRate = some (level :: rest))
    (hfold : level.fold = 6) (cs : List E)
    (hlane : ∀ j < 6, j < cs.length → lane j =
      roundMsgArr (PcsQuotient.weightTable L (powers (cs.headD 0)
        (PcsQuotient.stackClaims L claims).length) claims) (stackTableA L.logN stack)
        ((cs.drop 1).take j))
    (hf : 7 ≤ cs.length → f1 = foldsA ((cs.drop 1).take 6) (stackTableA L.logN stack)) :
    Agree cs (hybridScript L claims lane f1) (PcsQuotient.openingScript L stack claims) := by
  rw [hybridScript_eq L claims lane f1 hl, openingScript_eq L stack claims hl]
  obtain ⟨fold, lir, qs⟩ := level
  simp only at hfold
  subst hfold
  rcases cs with _ | ⟨c, cs⟩
  · exact .stop
  refine .sample ?_
  rw [hlane 0 (by omega) (by simp)]
  refine .send _ (.send _ (laneFolds_honest L.logN _ rest f1 lane (6 - 1) 1 _ [] _ _ cs
    (fun i hi hic ↦ ?_) (fun hm ↦ hf (by simp only [List.length_cons]; omega))))
  have := hlane (1 + i) (by omega) (by simp only [List.length_cons]; omega)
  rw [this, Nat.add_comm 1 i]
  rfl

end PcsQuotient.EndToEnd.Core

