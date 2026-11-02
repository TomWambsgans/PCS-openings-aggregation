-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The sponge (`absorb`, `squeeze`), the proof-of-work search (`findNonceM`, `searchM`) and the trees
-- (`buildTreeM`) are leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0).
import ZK.CoreSkel
import Bridge.Chain

/-!
# The skeleton's opening is the statement's, event by event

The lockstep of three machines on an opening's events: the skeleton on events (`skelEv`, its
messages the renderer's), the renderer's drive (`Render.evRun`, which every message re-runs from the
opening's start), and the statement's event-driven run (`runEvS`) of the same script. **`drive`**:
when the statement's run makes the stream `str` and the multiproofs `ms`, the skeleton's stream grows
by `str` (as limbs) and its multiproofs by `ms`, provided the three agree at the start: the duplex
and the sponge (`Duplex.Rel`), the script and the position draws, the commitments (the renderer's
words the trees', the skeleton's levels the trees' bytes), the pending items the renderer's, and every
later message of the skeleton the renderer's last message (`hmsg`).
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover
open QuotientZk.Deployed (OSt Dx drawO sendK commitNext takeOpened takeScalars takeRows sortedUnique
  prune grind positionsOf DSpec Out Inp Msg Item)

namespace PcsQuotient.EndToEnd.Core

open Render (limbsOf evRun lastMsg RunSt sendsN)

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

/-! ## The renderer's drive -/

/-- The draws among the events. -/
def drawsIn : List Render.Ev → ℕ
  | [] => 0
  | .draw :: evs => drawsIn evs + 1
  | .posDraw :: evs => drawsIn evs + 1
  | _ :: evs => drawsIn evs

/-- **The items the renderer sends before its next draw**, from the state `rs`. -/
def itemsAhead (evs : List Render.Ev) (rs : RunSt) : Msg :=
  lastMsg (evRun evs [] ⟨rs.script, rs.comms, rs.posLimbs, [], rs.done⟩)

theorem lastMsg_snoc (l : List Msg) (m : Msg) : lastMsg (l ++ [m]) = m := by
  simp [lastMsg]

/-- The last message accumulates. -/
theorem evRun_nil_acc : ∀ (evs : List Render.Ev) (rs : RunSt),
    lastMsg (evRun evs [] rs) =
      rs.acc ++ lastMsg (evRun evs [] ⟨rs.script, rs.comms, rs.posLimbs, [], rs.done⟩)
  | [], rs => by simp [evRun, lastMsg_snoc]
  | .draw :: evs, rs => by simp [evRun, lastMsg_snoc]
  | .posDraw :: evs, rs => by simp [evRun, lastMsg_snoc]
  | .send k :: evs, rs => by
    simp only [evRun]
    rw [evRun_nil_acc evs, evRun_nil_acc evs ⟨_, _, _, [] ++ _, _⟩]
    simp
  | .commit d :: evs, rs => by
    simp only [evRun]
    rw [evRun_nil_acc evs, evRun_nil_acc evs ⟨_, _, _, [] ++ _, _⟩]
    simp
  | .grind :: evs, rs => by
    simp only [evRun]
    rw [evRun_nil_acc evs, evRun_nil_acc evs ⟨_, _, _, [], _⟩]
  | .opened lvl q b :: evs, rs => by
    simp only [evRun]
    rw [evRun_nil_acc evs, evRun_nil_acc evs ⟨_, _, _, [] ++ _, _⟩]
    simp

/-! ## The statement's sends -/

section Sends

variable (π : Equiv.Perm Eager.St)

theorem sendsN_eq : ∀ (k : ℕ) (S : Option (Script Unit)) (sp : Sponge),
    sendsN k S = ((sendsS π k S sp).1, (sendsS π k S sp).2.1)
  | 0, S, sp => rfl
  | k + 1, S, sp => by
    simp only [sendsN, sendsS]
    rw [sendsN_eq k _ (absorb (permId π) sp (Script.msgOf S) dsObserve).run]

theorem length_sendsS : ∀ (k : ℕ) (S : Option (Script Unit)) (sp : Sponge),
    (sendsS π k S sp).1.length = k
  | 0, S, sp => rfl
  | k + 1, S, sp => by simp only [sendsS, List.length_cons, length_sendsS k]

/-- The sponge after the sends. -/
theorem sendsS_sponge : ∀ (k : ℕ) (S : Option (Script Unit)) (sp : Sponge),
    (sendsS π k S sp).2.2 =
      (sendsS π k S sp).1.foldl (fun sp x ↦ (absorb (permId π) sp x dsObserve).run) sp
  | 0, S, sp => rfl
  | k + 1, S, sp => by simp only [sendsS, List.foldl_cons]; exact sendsS_sponge k _ _

end Sends

/-! ## The skeleton's steps against the oracle -/

section Steps

variable {S₀ : Type} (P : QuotientZk.Proto S₀ Inp Out Msg QuotientZk.Deployed.Tbl
  QuotientZk.Deployed.Pos) (π : Equiv.Perm Eager.St) (gH : List UInt8 → QuotientZk.Deployed.KSt)
  (gF : QuotientZk.Deployed.KSt → DigestBytes) (s : S₀)

local notation "G" => Gof (kDet π) π gH gF

open Merkle (runDet_bind runDet_pure)

/-- **Absorbing scalars** keeps the duplex and the sponge related, no challenge. -/
theorem absorbAll_rel : ∀ (l : List E) (d : Dx) (sp : Sponge) (hist : List Out), Duplex.Rel d sp →
    (runDet P G s (d.absorbAll (l.map limbsOf)) hist).2 = hist ∧
      Duplex.Rel (runDet P G s (d.absorbAll (l.map limbsOf)) hist).1
        (l.foldl (fun sp x ↦ (absorb (permId π) sp x dsObserve).run) sp)
  | [], d, sp, hist, h => by
    rw [List.map_nil, Dx.absorbAll, runDet_pure, List.foldl_nil]
    exact ⟨rfl, h⟩
  | x :: l, d, sp, hist, h => by
    obtain ⟨h1, h2⟩ := Duplex.absorb_rel P (kDet π) π gH gF s h x dsObserve hist
    simp only [List.map_cons, Dx.absorbAll, runDet_bind, List.foldl_cons]
    have e : QuotientZk.Deployed.tagObserve = dsObserve.toUInt64 := rfl
    rw [e, h1]
    exact absorbAll_rel l _ _ hist h2

theorem runDet_mapM_hashH (f : ℕ → List UInt8) : ∀ (l : List ℕ) (hist : List Out),
    runDet P G s (l.mapM fun i ↦ QuotientZk.Deployed.hashH (f i)) hist =
      (l.map fun i ↦ kDet π (f i), hist)
  | [], hist => by rw [List.mapM_nil, runDet_pure]; rfl
  | i :: l, hist => by
    rw [List.mapM_cons, runDet_bind, Merkle.runDet_hashH, runDet_bind, runDet_mapM_hashH f l,
      runDet_pure]
    rfl

end Steps

theorem rootLimbs_toBytes (d : Digest) :
    QuotientZk.Deployed.rootLimbs (Digest.toBytes d) =
      [limbsOf (digestScalars d).1, limbsOf (digestScalars d).2] := by
  obtain ⟨⟨l⟩, hl⟩ := d
  match l, hl with
  | [a, b, c, e], _ =>
    have ht : (Digest.toBytes ⟨⟨[a, b, c, e]⟩, rfl⟩).toList =
        wordBytes a ++ (wordBytes b ++ (wordBytes c ++ (wordBytes e ++ []))) := by
      rw [Merkle.toBytes_toList]; rfl
    simp only [QuotientZk.Deployed.rootLimbs, QuotientRpm.rootScalars, ht,
      Bridge.drop_wordBytes_append, Bridge.drop_wordBytes_append₂, Bridge.drop_wordBytes_append₃,
      LeanVM.Rpm.bytesLane_wordBytes_append]
    rfl

/-! ## The lockstep -/

/-- **The three machines agree**: the duplex and the sponge, the renderer's script and position
draws the run's, its commitments the run's trees' words, the skeleton's levels the trees' bytes,
and (unless the events are over) the skeleton's pending items the renderer's next. -/
structure DriveInv (o : OSt) (rs : RunSt) (S : Option (Script Unit)) (sp : Sponge) (cs : List Tree)
    (pl : List QuotientRpm.Limbs) (evs : List Render.Ev) : Prop where
  rel : Duplex.Rel o.dx sp
  script : rs.script = S
  pos : rs.posLimbs = pl
  comms : rs.comms = cs.map fun t ↦ (t.height, t.word)
  trees : o.trees = cs.map treeBytesOf
  items : evs = [] ∨ o.items = itemsAhead evs rs

section Lock

variable {S₀ : Type} (P : QuotientZk.Proto S₀ Inp Out Msg QuotientZk.Deployed.Tbl
  QuotientZk.Deployed.Pos) (π : Equiv.Perm Eager.St) (gH : List UInt8 → QuotientZk.Deployed.KSt)
  (gF : QuotientZk.Deployed.KSt → DigestBytes) (s : S₀) (fuel : ℕ)

local notation "G" => Gof (kDet π) π gH gF

open Merkle (runDet_bind runDet_pure)

theorem runDet_getMsg (hist : List Out) :
    runDet P G s QuotientZk.Deployed.getMsg hist = (P.msgFn s hist, hist) := rfl

/-- **A draw** against the oracle. -/
theorem runDet_drawO (o : OSt) (hist : List Out) :
    runDet P G s (drawO o) hist =
      ((((π o.dx.input)[0], (π o.dx.input)[1], (π o.dx.input)[2]),
        ⟨⟨π o.dx.input, []⟩,
          P.msgFn s (if hist.length < P.n then hist ++ [(gF o.dx.input, π o.dx.input)] else hist),
          o.trees, o.stream, o.merkle⟩),
        if hist.length < P.n then hist ++ [(gF o.dx.input, π o.dx.input)] else hist) := by
  unfold drawO Dx.draw
  simp only [runDet_bind, Duplex.runDet_chalF, runDet_pure, runDet_getMsg]

theorem drawsIn_pos {evs : List Render.Ev} (h : evs.getLast? = some .draw) : 1 ≤ drawsIn evs := by
  induction evs with
  | nil => simp at h
  | cons e evs ih =>
    rcases evs with _ | ⟨e', evs'⟩
    · simp only [List.getLast?_singleton, Option.some.injEq] at h
      subst h
      simp [drawsIn]
    · have h' : (e' :: evs').getLast? = some .draw := by
        rw [List.getLast?_cons_cons] at h
        exact h
      have := ih h'
      cases e <;> simp [drawsIn] <;> omega

theorem lastDraw_tail {e : Render.Ev} {evs : List Render.Ev}
    (h : e :: evs = [] ∨ (e :: evs).getLast? = some .draw) :
    evs = [] ∨ evs.getLast? = some .draw := by
  rcases evs with _ | ⟨e', evs'⟩
  · exact Or.inl rfl
  · rcases h with h | h
    · cases h
    · exact Or.inr (by rw [List.getLast?_cons_cons] at h; exact h)

theorem rel_squeeze {d : Dx} {sp : Sponge} (h : Duplex.Rel d sp) :
    Duplex.Rel ⟨π d.input, []⟩ (squeeze (permId π) sp).run.2 := by
  refine ⟨fun i _ ↦ ?_, rfl⟩
  show (π d.input)[i] = Keccak.lane (π (duplexInput sp)) i
  rw [Duplex.lane_eq_getElem, Duplex.input_eq h]

theorem chal_squeeze {d : Dx} {sp : Sponge} (h : Duplex.Rel d sp) :
    Compile.challengeOf (π d.input) = (squeeze (permId π) sp).run.1 := by
  show _ = Compile.challengeOf (π (duplexInput sp))
  rw [Duplex.input_eq h]

/-- **The lockstep.** -/
theorem drive (hfuel : fuel < 2 ^ 64) : ∀ (evs : List Render.Ev) (o : OSt)
    (pl : List QuotientRpm.Limbs) (hist : List Out) (S : Option (Script Unit)) (sp : Sponge)
    (cs : List Tree) (rs : RunSt) (str : List E) (ops : List Opening) (ms : List Multi),
    DriveInv o rs S sp cs pl evs → (∀ t ∈ cs, TreeOK π t) → HeightsOK evs (cs.map (·.height)) →
    (evs = [] ∨ evs.getLast? = some .draw) → hist.length + drawsIn evs ≤ P.n →
    (∀ chs : List Out, 1 ≤ chs.length → chs.length < drawsIn evs →
      P.msgFn s (hist ++ chs) = lastMsg (evRun evs chs rs)) →
    runEvS π fuel evs S sp cs pl = some (str, ops, ms) →
    (runDet P G s (skelEv evs o pl) hist).1.stream = o.stream ++ str.map limbsOf ∧
      (runDet P G s (skelEv evs o pl) hist).1.merkle = o.merkle ++ ms
  | [], o, pl, hist, S, sp, cs, rs, str, ops, ms, _, _, _, _, _, _, hr => by
    simp only [runEvS, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, rfl⟩ := hr
    simp [skelEv, runDet_pure]
  | .draw :: evs, o, pl, hist, S, sp, cs, rs, str, ops, ms, hI, hT, hH, hL, hn, hmsg, hr => by
    have hlt : hist.length < P.n := by simp only [drawsIn] at hn; omega
    rw [skelEv, runDet_bind, runDet_drawO, if_pos hlt]
    have hn' : (hist ++ [(gF o.dx.input, π o.dx.input)]).length + drawsIn evs ≤ P.n := by
      simp only [List.length_append, List.length_singleton]
      simp only [drawsIn] at hn
      omega
    have hr' : runEvS π fuel evs (Script.afterSample (squeeze (permId π) sp).run.1 S)
        (squeeze (permId π) sp).run.2 cs pl = some (str, ops, ms) := hr
    refine drive hfuel evs _ pl _ _ _ cs ⟨Script.afterSample (Compile.challengeOf (π o.dx.input))
      rs.script, rs.comms, rs.posLimbs, [], rs.done ++ [rs.acc]⟩ str ops ms ?_ hT hH
      (lastDraw_tail hL) hn' ?_ hr'
    · refine ⟨rel_squeeze π hI.rel, by rw [hI.script, chal_squeeze π hI.rel], hI.pos, hI.comms,
        hI.trees, ?_⟩
      rcases hL with hL | hL
      · cases hL
      rcases hev : evs with _ | ⟨e', evs'⟩
      · exact Or.inl rfl
      · right
        subst hev
        have hd := drawsIn_pos (by rw [List.getLast?_cons_cons] at hL; exact hL)
        show P.msgFn s (hist ++ [(gF o.dx.input, π o.dx.input)]) = _
        rw [hmsg [(gF o.dx.input, π o.dx.input)] le_rfl
          (by simp only [drawsIn, List.length_singleton]; omega)]
        show lastMsg (evRun _ [] _) = _
        rw [evRun_nil_acc]
        rfl
    · intro chs h1 h2
      rw [List.append_assoc, List.singleton_append]
      exact hmsg _ (by simp) (by simp only [List.length_cons, drawsIn]; omega)
  | .posDraw :: evs, o, pl, hist, S, sp, cs, rs, str, ops, ms, hI, hT, hH, hL, hn, hmsg, hr => by
    have hlt : hist.length < P.n := by simp only [drawsIn] at hn; omega
    rw [skelEv, runDet_bind, runDet_drawO, if_pos hlt]
    have hn' : (hist ++ [(gF o.dx.input, π o.dx.input)]).length + drawsIn evs ≤ P.n := by
      simp only [List.length_append, List.length_singleton]
      simp only [drawsIn] at hn
      omega
    have hc : limbsOf (squeeze (permId π) sp).run.1 =
        ((π o.dx.input)[0], (π o.dx.input)[1], (π o.dx.input)[2]) := by
      rw [← chal_squeeze π hI.rel, Duplex.limbsOf_challengeOf]
    have hr' : runEvS π fuel evs (Script.afterSample (squeeze (permId π) sp).run.1 S)
        (squeeze (permId π) sp).run.2 cs
          (pl ++ [((π o.dx.input)[0], (π o.dx.input)[1], (π o.dx.input)[2])]) =
        some (str, ops, ms) := by rw [← hc]; exact hr
    refine drive hfuel evs _ _ _ _ _ cs ⟨Script.afterSample (Compile.challengeOf (π o.dx.input))
      rs.script, rs.comms, rs.posLimbs ++ [((π o.dx.input)[0], (π o.dx.input)[1], (π o.dx.input)[2])],
      [], rs.done ++ [rs.acc]⟩ str ops ms ?_ hT hH
      (lastDraw_tail hL) hn' ?_ hr'
    · refine ⟨rel_squeeze π hI.rel, by rw [hI.script, chal_squeeze π hI.rel], by rw [hI.pos],
        hI.comms, hI.trees, ?_⟩
      rcases hL with hL | hL
      · cases hL
      rcases hev : evs with _ | ⟨e', evs'⟩
      · exact Or.inl rfl
      · right
        subst hev
        have hd := drawsIn_pos (by rw [List.getLast?_cons_cons] at hL; exact hL)
        show P.msgFn s (hist ++ [(gF o.dx.input, π o.dx.input)]) = _
        rw [hmsg [(gF o.dx.input, π o.dx.input)] le_rfl
          (by simp only [drawsIn, List.length_singleton]; omega)]
        show lastMsg (evRun _ [] _) = _
        rw [evRun_nil_acc]
        rfl
    · intro chs h1 h2
      rw [List.append_assoc, List.singleton_append]
      exact hmsg _ (by simp) (by simp only [List.length_cons, drawsIn]; omega)
  | .send k :: evs, o, pl, hist, S, sp, cs, rs, str, ops, ms, hI, hT, hH, hL, hn, hmsg, hr => by
    change (runEvS π fuel evs (sendsS π k S sp).2.1 (sendsS π k S sp).2.2 cs pl).map
      (fun t ↦ ((sendsS π k S sp).1 ++ t.1, t.2)) = some (str, ops, ms) at hr
    obtain ⟨⟨t1, t2, t3⟩, ht, hte⟩ := Option.map_eq_some_iff.mp hr
    simp only [Prod.mk.injEq] at hte
    obtain ⟨rfl, rfl, rfl⟩ := hte
    have hN := sendsN_eq π k S sp
    have hitems : o.items = Item.scalars ((sendsS π k S sp).1.map limbsOf) ::
        itemsAhead evs ⟨(sendsS π k S sp).2.1, rs.comms, rs.posLimbs,
          rs.acc ++ [Item.scalars ((sendsS π k S sp).1.map limbsOf)], rs.done⟩ := by
      rcases hI.items with h | h
      · cases h
      rw [h, itemsAhead]
      show lastMsg (evRun evs [] ⟨(sendsN k rs.script).2, rs.comms, rs.posLimbs,
        [] ++ [Item.scalars ((sendsN k rs.script).1.map limbsOf)], rs.done⟩) = _
      rw [evRun_nil_acc, hI.script, hN]
      rfl
    have hsend : runDet P G s (sendK o k) hist =
        (⟨(runDet P G s (o.dx.absorbAll ((sendsS π k S sp).1.map limbsOf)) hist).1,
          itemsAhead evs ⟨(sendsS π k S sp).2.1, rs.comms, rs.posLimbs,
            rs.acc ++ [Item.scalars ((sendsS π k S sp).1.map limbsOf)], rs.done⟩,
          o.trees, o.stream ++ (sendsS π k S sp).1.map limbsOf, o.merkle⟩, hist) := by
      have hlen : ((sendsS π k S sp).1.map limbsOf).length = k := by
        rw [List.length_map, length_sendsS]
      obtain ⟨h1, -⟩ := absorbAll_rel P π gH gF s (sendsS π k S sp).1 o.dx sp hist hI.rel
      unfold sendK
      rw [hitems]
      simp only [takeScalars, List.take_append_of_le_length (le_of_eq hlen.symm),
        List.take_of_length_le (le_of_eq hlen), runDet_bind, runDet_pure, h1]
    obtain ⟨-, hrel⟩ := absorbAll_rel P π gH gF s (sendsS π k S sp).1 o.dx sp hist hI.rel
    rw [skelEv, runDet_bind, hsend]
    have hI' : DriveInv ⟨(runDet P G s (o.dx.absorbAll ((sendsS π k S sp).1.map limbsOf)) hist).1,
          itemsAhead evs ⟨(sendsS π k S sp).2.1, rs.comms, rs.posLimbs,
            rs.acc ++ [Item.scalars ((sendsS π k S sp).1.map limbsOf)], rs.done⟩,
          o.trees, o.stream ++ (sendsS π k S sp).1.map limbsOf, o.merkle⟩
        ⟨(sendsS π k S sp).2.1, rs.comms, rs.posLimbs,
          rs.acc ++ [Item.scalars ((sendsS π k S sp).1.map limbsOf)], rs.done⟩
        (sendsS π k S sp).2.1 (sendsS π k S sp).2.2 cs pl evs :=
      ⟨by rw [sendsS_sponge]; exact hrel, rfl, hI.pos, hI.comms, hI.trees, Or.inr rfl⟩
    obtain ⟨e1, e2⟩ := drive hfuel evs _ pl hist _ _ cs _ t1 t2 t3 hI' hT hH (lastDraw_tail hL)
      (by simpa [drawsIn] using hn)
      (fun chs h1 h2 ↦ by
        rw [hmsg chs h1 (by simpa [drawsIn] using h2)]
        show lastMsg (evRun evs chs ⟨(sendsN k rs.script).2, _, _, _, _⟩) = _
        rw [hI.script, hN]) ht
    refine ⟨?_, e2⟩
    rw [e1, List.map_append, List.append_assoc]
  | .commit d :: evs, o, pl, hist, S, sp, cs, rs, str, ops, ms, hI, hT, hH, hL, hn, hmsg, hr => by
    sorry
  | .grind :: evs, o, pl, hist, S, sp, cs, rs, str, ops, ms, hI, hT, hH, hL, hn, hmsg, hr => by
    rw [runEvS_grind] at hr
    rcases hfn : (findNonceM (permId π) 17 sp fuel).run with _ | n
    · rw [hfn] at hr
      cases hr
    rw [hfn] at hr
    obtain ⟨⟨t1, t2, t3⟩, ht, hte⟩ := Option.map_eq_some_iff.mp hr
    simp only [Prod.mk.injEq] at hte
    obtain ⟨rfl, rfl, rfl⟩ := hte
    have hs : searchM (m := Id) (fun y ↦ pure (π y)) 17 sp 0 fuel = some n := hfn
    obtain ⟨g1, g2, g3⟩ := Duplex.grind_rel P (kDet π) π gH gF s fuel 0 (2 ^ 64) o.dx sp hist hI.rel
      (by omega) (by omega) n hs
    have e0 : (UInt64.ofNat 0 : UInt64) = 0 := rfl
    rw [e0] at g1 g2 g3
    rw [skelEv, runDet_bind]
    generalize hg : runDet P G s (grind o.dx (2 ^ 64) 0) hist = gr at g1 g2 g3
    obtain ⟨⟨nonce, dx'⟩, hist'⟩ := gr
    simp only at g1 g2 g3 ⊢
    subst g1
    have hI' : DriveInv { o with dx := dx', stream := o.stream ++ [(nonce, 0, 0)] }
        ⟨Script.afterGrind rs.script, rs.comms, rs.posLimbs, rs.acc, rs.done⟩ (Script.afterGrind S)
        (powStepM (permId π) sp n).run.2 cs pl evs :=
      ⟨g3, by rw [hI.script], hI.pos, hI.comms, hI.trees, by
        rcases hI.items with h | h
        · cases h
        rcases evs with _ | ⟨e', evs'⟩
        · exact Or.inl rfl
        · exact Or.inr h⟩
    obtain ⟨e1, e2⟩ := drive hfuel evs _ pl hist' _ _ cs _ t1 t2 t3 hI' hT hH (lastDraw_tail hL)
      (by simpa [drawsIn] using hn) (fun chs h1 h2 ↦ hmsg chs h1 (by simpa [drawsIn] using h2)) ht
    refine ⟨?_, e2⟩
    rw [e1, List.map_cons, ← g2]
    simp
  | .opened lvl q b :: evs, o, pl, hist, S, sp, cs, rs, str, ops, ms, hI, hT, hH, hL, hn, hmsg,
      hr => by
    sorry

end Lock

end PcsQuotient.EndToEnd.Core
