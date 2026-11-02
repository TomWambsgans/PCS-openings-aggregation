-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.CoreFill
import ZK.ProverBridgeMerkle

/-!
# The skeleton's opening, event by event

The skeleton's opening (`Deployed.opening`) is written in phases (`rounds`, `commitNext`, `ood`,
`queryPhase`, `middle`). **`skelEv`** runs it event by event (`Render.Ev`): a draw is `drawO`, `k`
scalars `sendK`, a commitment `commitNext`, grinding `grind` (its nonce into the stream), the opened
rows the next item and the multiproof of the commitment at the positions of the position draws since
the last. Here: each phase is `skelEv` on its events (`rounds_skelEv`, `ood_skelEv`,
`queryPhase_skelEv`, …), the query phase given its commitment's depth; `middle_skelEv` and
`opening_skelEv` against the oracle (`runDet`), the trees' depths known from the run.
-/

open OracleComp OracleSpec
open QuotientZk.Deployed (OSt Dx drawO sendK commitNext takeOpened sortedUnique prune grind
  rounds drawMany ood queryPhase middle positionsOf DSpec Out)

namespace PcsQuotient.EndToEnd.Core

open Render (roundsEv oodEv queryEv middleEv)

set_option linter.unusedSectionVars false

/-- **The skeleton's opening on events.** -/
def skelEv : List Render.Ev → OSt → List QuotientRpm.Limbs → OracleComp DSpec OSt
  | [], o, _ => pure o
  | .draw :: evs, o, pl => do
    let (_, o) ← drawO o
    skelEv evs o pl
  | .posDraw :: evs, o, pl => do
    let (c, o) ← drawO o
    skelEv evs o (pl ++ [c])
  | .send k :: evs, o, pl => do
    let o ← sendK o k
    skelEv evs o pl
  | .commit d :: evs, o, pl => do
    let o ← commitNext o d
    skelEv evs o pl
  | .grind :: evs, o, pl => do
    let (nonce, dx) ← grind o.dx (2 ^ 64) 0
    skelEv evs { o with dx := dx, stream := o.stream ++ [(nonce, 0, 0)] } pl
  | .opened lvl q b :: evs, o, pl =>
    skelEv evs ⟨o.dx, (takeOpened o.items).2, o.trees, o.stream,
      o.merkle ++ [(sortedUnique (posOf pl b q), (takeOpened o.items).1,
        prune (o.trees.getD lvl []) (sortedUnique (posOf pl b q)))]⟩ []

/-! ## The phases as events -/

theorem rounds_skelEv (rest : List Render.Ev) (pl : List QuotientRpm.Limbs) :
    ∀ (k : ℕ) (o : OSt), (rounds o k >>= fun o ↦ skelEv rest o pl) = skelEv (roundsEv k ++ rest) o pl
  | 0, o => by simp only [rounds, pure_bind, roundsEv, List.nil_append]
  | k + 1, o => by
    simp only [rounds, roundsEv, bind_assoc, List.cons_append]
    refine bind_congr fun co ↦ ?_
    refine bind_congr fun o' ↦ ?_
    exact rounds_skelEv rest pl k o'

theorem drawMany_skelEv (rest : List Render.Ev) (pl : List QuotientRpm.Limbs) :
    ∀ (m : ℕ) (o : OSt), (drawMany o m >>= fun r ↦ skelEv rest r.2 pl) =
      skelEv (List.replicate m .draw ++ rest) o pl
  | 0, o => by simp only [drawMany, pure_bind, List.replicate_zero, List.nil_append]
  | m + 1, o => by
    simp only [drawMany, bind_assoc, List.replicate_succ, List.cons_append, pure_bind]
    refine bind_congr fun co ↦ ?_
    exact drawMany_skelEv rest pl m co.2

theorem drawMany_skelEv_pos (rest : List Render.Ev) :
    ∀ (m : ℕ) (o : OSt) (pl : List QuotientRpm.Limbs), (drawMany o m >>= fun r ↦
      skelEv rest r.2 (pl ++ r.1)) = skelEv (List.replicate m .posDraw ++ rest) o pl
  | 0, o, pl => by simp only [drawMany, pure_bind, List.replicate_zero, List.nil_append, List.append_nil]
  | m + 1, o, pl => by
    simp only [drawMany, bind_assoc, List.replicate_succ, List.cons_append, pure_bind]
    refine bind_congr fun co ↦ ?_
    have h := drawMany_skelEv_pos rest m co.2 (pl ++ [co.1])
    simp only [List.append_assoc, List.singleton_append] at h
    exact h

theorem ood_skelEv (rest : List Render.Ev) (pl : List QuotientRpm.Limbs) (m : ℕ) (o : OSt) :
    (ood o m >>= fun o ↦ skelEv rest o pl) = skelEv (oodEv m ++ rest) o pl := by
  simp only [ood, oodEv, bind_assoc, List.append_assoc, List.singleton_append]
  rw [← drawMany_skelEv]
  rfl

/-- The query phase with the opened commitment's levels read by `Tf` at the opening. -/
def qpF (rest : List Render.Ev) (lvl q b : ℕ) (Tf : OSt → List (List (List QuotientRpm.Bytes32))) (o : OSt) :
    OracleComp DSpec OSt := do
  let (nonce, dx) ← grind o.dx (2 ^ 64) 0
  let r ← drawMany { o with dx := dx, stream := o.stream ++ [(nonce, 0, 0)] }
    ((q + 192 / max b 1 - 1) / (192 / max b 1))
  let co ← drawO r.2
  let o' ← sendK ⟨co.2.dx, (takeOpened co.2.items).2, co.2.trees, co.2.stream,
    co.2.merkle ++ [(sortedUnique (posOf r.1 b q), (takeOpened co.2.items).1,
      prune ((Tf co.2).getD lvl []) (sortedUnique (posOf r.1 b q)))]⟩ 2
  skelEv rest o' []

theorem queryPhase_qpF (rest : List Render.Ev) (lvl q b : ℕ) (o : OSt)
    (hb : (o.trees.getD lvl []).length = b + 1) :
    (queryPhase o lvl q >>= fun o ↦ skelEv rest o []) = qpF rest lvl q b (fun _ ↦ o.trees) o := by
  simp only [queryPhase, qpF, bind_assoc]
  refine bind_congr fun nd ↦ ?_
  obtain ⟨nonce, dx⟩ := nd
  dsimp only
  rw [hb, Nat.add_sub_cancel]
  refine bind_congr fun r ↦ ?_
  obtain ⟨cs, o'⟩ := r
  simp only [bind_assoc]
  refine bind_congr fun co ↦ ?_
  obtain ⟨c, o''⟩ := co
  rcases ht : takeOpened o''.items with ⟨opened, items⟩
  rfl

theorem skelEv_qpF (rest : List Render.Ev) (lvl q b : ℕ) (o : OSt) :
    skelEv (queryEv lvl q b ++ rest) o [] = qpF rest lvl q b (fun o'' ↦ o''.trees) o := by
  simp only [queryEv, qpF, List.cons_append, skelEv, bind_assoc]
  refine bind_congr fun nd ↦ ?_
  obtain ⟨nonce, dx⟩ := nd
  rw [List.append_assoc, ← drawMany_skelEv_pos]
  refine bind_congr fun r ↦ ?_
  obtain ⟨cs, o'⟩ := r
  simp only [List.nil_append, List.cons_append, skelEv, bind_assoc]

/-! ## Against the oracle: the trees' depths -/

section Run

variable {S : Type} (P : QuotientZk.Proto S QuotientZk.Deployed.Inp Out QuotientZk.Deployed.Msg
  QuotientZk.Deployed.Tbl QuotientZk.Deployed.Pos) (G : QuotientZk.Deployed.Inp → Out) (s : S)

open Merkle (runDet_bind runDet_pure)

theorem levelsP_length (kh : List UInt8 → QuotientRpm.Bytes32) :
    ∀ (d : ℕ) (leaves : List QuotientRpm.Bytes32), (Merkle.levelsP kh d leaves).length = d + 1
  | 0, _ => rfl
  | d + 1, leaves => by rw [Merkle.levelsP, List.length_cons, levelsP_length kh d]

theorem trees_drawO (o : OSt) (hist : List Out) :
    (runDet P G s (drawO o) hist).1.2.trees = o.trees := by
  unfold drawO
  rw [runDet_bind, runDet_bind, runDet_pure]

theorem trees_drawMany : ∀ (m : ℕ) (o : OSt) (hist : List Out),
    (runDet P G s (drawMany o m) hist).1.2.trees = o.trees
  | 0, o, hist => by rw [drawMany, runDet_pure]
  | m + 1, o, hist => by
    rw [drawMany, runDet_bind, runDet_bind, runDet_pure, trees_drawMany m, trees_drawO]

theorem trees_sendK (o : OSt) (k : ℕ) (hist : List Out) :
    (runDet P G s (sendK o k) hist).1.trees = o.trees := by
  unfold sendK
  rw [runDet_bind, runDet_pure]

theorem trees_rounds : ∀ (k : ℕ) (o : OSt) (hist : List Out),
    (runDet P G s (rounds o k) hist).1.trees = o.trees
  | 0, o, hist => by rw [rounds, runDet_pure]
  | k + 1, o, hist => by
    rw [rounds, runDet_bind, runDet_bind, trees_rounds k, trees_sendK, trees_drawO]

theorem trees_ood (o : OSt) (m : ℕ) (hist : List Out) :
    (runDet P G s (ood o m) hist).1.trees = o.trees := by
  unfold ood
  rw [runDet_bind, trees_sendK, trees_drawMany]

theorem trees_commitNext (o : OSt) (d : ℕ) (hist : List Out) :
    ∃ lv : List (List QuotientRpm.Bytes32), (runDet P G s (commitNext o d) hist).1.trees =
      o.trees ++ [lv] ∧ lv.length = d + 1 := by
  unfold commitNext
  rw [runDet_bind, runDet_bind, Merkle.runDet_levels, runDet_bind, runDet_pure]
  exact ⟨_, rfl, levelsP_length _ _ _⟩

/-- `drawO` keeps the trees. -/
theorem drawO_trees (o : OSt) :
    drawO o = (drawO o >>= fun co ↦ pure (co.1, { co.2 with trees := o.trees })) := by
  simp only [drawO, bind_assoc, pure_bind]

/-- `drawMany` keeps the trees. -/
theorem drawMany_trees : ∀ (m : ℕ) (o : OSt),
    drawMany o m = (drawMany o m >>= fun r ↦ pure (r.1, { r.2 with trees := o.trees }))
  | 0, o => by simp only [drawMany, pure_bind]
  | m + 1, o => by
    simp only [drawMany]
    rw [drawO_trees]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun co ↦ ?_
    rw [drawMany_trees m]
    simp only [bind_assoc, pure_bind]

theorem qpF_trees (rest : List Render.Ev) (lvl q b : ℕ) (o : OSt) :
    qpF rest lvl q b (fun o'' ↦ o''.trees) o = qpF rest lvl q b (fun _ ↦ o.trees) o := by
  unfold qpF
  refine bind_congr fun nd ↦ ?_
  obtain ⟨nonce, dx⟩ := nd
  dsimp only
  rw [drawMany_trees]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun r ↦ ?_
  rw [drawO_trees]
  simp only [bind_assoc, pure_bind]

/-- **The query phase on its events**, the opened commitment of depth `b`. -/
theorem queryPhase_skelEv (rest : List Render.Ev) (lvl q b : ℕ) (o : OSt)
    (hb : (o.trees.getD lvl []).length = b + 1) :
    (queryPhase o lvl q >>= fun o ↦ skelEv rest o []) = skelEv (queryEv lvl q b ++ rest) o [] := by
  rw [queryPhase_qpF rest lvl q b o hb, skelEv_qpF, qpF_trees]

/-- No commitment among the events. -/
def NoCommit : List Render.Ev → Prop
  | [] => True
  | .commit _ :: _ => False
  | _ :: evs => NoCommit evs

theorem trees_skelEv : ∀ (evs : List Render.Ev) (o : OSt) (pl : List QuotientRpm.Limbs)
    (hist : List Out), NoCommit evs → (runDet P G s (skelEv evs o pl) hist).1.trees = o.trees
  | [], o, pl, hist, _ => by rw [skelEv, runDet_pure]
  | .draw :: evs, o, pl, hist, h => by
    rw [skelEv, runDet_bind, trees_skelEv evs _ _ _ h, trees_drawO]
  | .posDraw :: evs, o, pl, hist, h => by
    rw [skelEv, runDet_bind, trees_skelEv evs _ _ _ h, trees_drawO]
  | .send k :: evs, o, pl, hist, h => by
    rw [skelEv, runDet_bind, trees_skelEv evs _ _ _ h, trees_sendK]
  | .commit d :: evs, o, pl, hist, h => h.elim
  | .grind :: evs, o, pl, hist, h => by
    rw [skelEv, runDet_bind, trees_skelEv evs _ _ _ h]
  | .opened lvl q b :: evs, o, pl, hist, h => by
    rw [skelEv, trees_skelEv evs _ _ _ h]

theorem noCommit_queryEv (lvl q b : ℕ) : NoCommit (queryEv lvl q b) := by
  simp only [queryEv, List.cons_append, NoCommit]
  generalize (q + 192 / max b 1 - 1) / (192 / max b 1) = n
  induction n with
  | zero => simp [NoCommit]
  | succ n ih => simpa [List.replicate_succ, NoCommit] using ih

theorem queryPhase_eq_skelEv (lvl q b : ℕ) (o : OSt) (hb : (o.trees.getD lvl []).length = b + 1) :
    queryPhase o lvl q = skelEv (queryEv lvl q b) o [] := by
  have h := queryPhase_skelEv [] lvl q b o hb
  have e : ∀ o' : OSt, skelEv [] o' [] = pure o' := fun _ ↦ rfl
  simp only [e, bind_pure, List.append_nil] at h
  exact h

theorem trees_queryPhase (lvl q b : ℕ) (o : OSt) (hb : (o.trees.getD lvl []).length = b + 1)
    (hist : List Out) : (runDet P G s (queryPhase o lvl q) hist).1.trees = o.trees := by
  rw [queryPhase_eq_skelEv lvl q b o hb]
  exact trees_skelEv P G s _ o [] hist (noCommit_queryEv lvl q b)

end Run

end PcsQuotient.EndToEnd.Core
