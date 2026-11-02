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

theorem runDet_bind_congr {α β : Type} (X : OracleComp DSpec α) (K₁ K₂ : α → OracleComp DSpec β)
    (hist : List Out)
    (h : runDet P G s (K₁ (runDet P G s X hist).1) (runDet P G s X hist).2 =
      runDet P G s (K₂ (runDet P G s X hist).1) (runDet P G s X hist).2) :
    runDet P G s (X >>= K₁) hist = runDet P G s (X >>= K₂) hist := by
  rw [runDet_bind, runDet_bind, h]

theorem skelEv_commit (d : ℕ) (rest : List Render.Ev) (o : OSt) (pl : List QuotientRpm.Limbs) :
    skelEv (.commit d :: rest) o pl = commitNext o d >>= fun o ↦ skelEv rest o pl := rfl

theorem getD_append_lt {α : Type} (l l' : List α) (d : α) {i : ℕ} (hi : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-- **The later levels on their events**, against the oracle: commitment `lvl` (of depth `b`) the
last committed, the continuation `K` the events `R` once the trees are the levels'. -/
theorem middle_run {β : Type} (R : List Render.Ev) (K Fin : OSt → OracleComp DSpec β) :
    ∀ (L : List (ℕ × ℕ × ℕ)) (Q : List ℕ) (lvl b : ℕ) (o : OSt) (hist : List Out),
      L.length ≤ Q.length → o.trees.length = lvl + 1 → (o.trees.getD lvl []).length = b + 1 →
      (∀ (o' : OSt) (h' : List Out), o'.trees.length = lvl + 1 + L.length →
        (o'.trees.getD (lvl + L.length) []).length = QuotientZk.Instance.lastDepth b L + 1 →
        runDet P G s (K o') h' = runDet P G s (skelEv R o' [] >>= Fin) h') →
      runDet P G s (middle o lvl L Q >>= K) hist =
        runDet P G s (skelEv (middleEv lvl b L Q ++ R) o [] >>= Fin) hist
  | [], Q, lvl, b, o, hist, _, h1, h2, hK => by
    simp only [middle, pure_bind, middleEv, List.nil_append]
    exact hK o hist (by simpa using h1) (by simpa [QuotientZk.Instance.lastDepth] using h2)
  | (f, d, oo) :: L, [], lvl, b, o, hist, hl, _, _, _ => by simp at hl
  | (f, d, oo) :: L, q :: Q, lvl, b, o, hist, hl, h1, h2, hK => by
    simp only [middle, middleEv, bind_assoc, List.append_assoc]
    rw [← rounds_skelEv, bind_assoc]
    refine runDet_bind_congr P G s _ _ _ hist ?_
    have t1 := trees_rounds P G s f o hist
    generalize runDet P G s (rounds o f) hist = r1 at t1 ⊢
    obtain ⟨o1, h1'⟩ := r1
    simp only at t1 ⊢
    rw [List.singleton_append, skelEv_commit, bind_assoc]
    refine runDet_bind_congr P G s _ _ _ h1' ?_
    obtain ⟨lv, t2, hlv⟩ := trees_commitNext P G s o1 d h1'
    generalize runDet P G s (commitNext o1 d) h1' = r2 at t2 ⊢
    obtain ⟨o2, h2'⟩ := r2
    simp only at t2 ⊢
    rw [← ood_skelEv, bind_assoc]
    refine runDet_bind_congr P G s _ _ _ h2' ?_
    have t3 := trees_ood P G s o2 oo h2'
    generalize runDet P G s (ood o2 oo) h2' = r3 at t3 ⊢
    obtain ⟨o3, h3'⟩ := r3
    simp only at t3 ⊢
    have hb3 : (o3.trees.getD lvl []).length = b + 1 := by
      rw [t3, t2, t1, getD_append_lt _ _ _ (by omega), h2]
    rw [← queryPhase_skelEv _ lvl q b o3 hb3, bind_assoc]
    refine runDet_bind_congr P G s _ _ _ h3' ?_
    have t4 := trees_queryPhase P G s lvl q b o3 hb3 h3'
    generalize runDet P G s (queryPhase o3 lvl q) h3' = r4 at t4 ⊢
    obtain ⟨o4, h4'⟩ := r4
    simp only at t4 ⊢
    refine middle_run R K Fin L Q (lvl + 1) d o4 h4' (by simpa using hl)
      (by rw [t4, t3, t2, t1, List.length_append, h1]; rfl)
      (by rw [t4, t3, t2, t1, ← h1, List.getD_eq_getElem?_getD, List.getElem?_append_right
        (le_refl _), Nat.sub_self]; simpa using hlv) ?_
    intro o' h' ho1 ho2
    refine hK o' h' (by rw [ho1, List.length_cons]; ring) ?_
    have e : lvl + (L.length + 1) = lvl + 1 + L.length := by ring
    rw [List.length_cons, e]
    exact ho2

/-- The skeleton's opening from the batching draw on (`Deployed.opening` after the seed and the root). -/
def openTail (sh : QuotientZk.Deployed.OpenShape) (o : OSt) :
    OracleComp DSpec (List QuotientRpm.Limbs × List Multi) := do
  let (_, o) ← drawO o
  let o ← sendK o 2
  let o ← rounds o 6
  let o ← commitNext o sh.depth₁
  let o ← ood o sh.ood₀
  let o ← queryPhase o 0 (sh.queries.headD 0)
  let o ← middle o 1 sh.levels (sh.queries.drop 1)
  let o ← rounds o sh.lastFolds
  let o ← sendK o (2 ^ sh.residualVars)
  let o ← queryPhase o (sh.levels.length + 1) (sh.queries.getLastD 0)
  let o ← rounds o (sh.residualVars - 1)
  let (_, o) ← drawO o
  return (o.stream, o.merkle)

/-- The opening's last level and end, on their events. -/
theorem tail_run (sh : QuotientZk.Deployed.OpenShape) (o : OSt)
    (hb : (o.trees.getD (sh.levels.length + 1) []).length =
      QuotientZk.Instance.lastDepth sh.depth₁ sh.levels + 1) (hist : List Out) :
    runDet P G s (do
      let o ← rounds o sh.lastFolds
      let o ← sendK o (2 ^ sh.residualVars)
      let o ← queryPhase o (sh.levels.length + 1) (sh.queries.getLastD 0)
      let o ← rounds o (sh.residualVars - 1)
      let (_, o) ← drawO o
      return (o.stream, o.merkle)) hist =
    runDet P G s (skelEv (roundsEv sh.lastFolds ++ (.send (2 ^ sh.residualVars) ::
        (queryEv (sh.levels.length + 1) (sh.queries.getLastD 0)
          (QuotientZk.Instance.lastDepth sh.depth₁ sh.levels) ++
          (roundsEv (sh.residualVars - 1) ++ [.draw])))) o [] >>=
        fun o ↦ pure (o.stream, o.merkle)) hist := by
  rw [← rounds_skelEv, bind_assoc]
  refine runDet_bind_congr P G s _ _ _ hist ?_
  have t1 := trees_rounds P G s sh.lastFolds o hist
  generalize runDet P G s (rounds o sh.lastFolds) hist = r1 at t1 ⊢
  obtain ⟨o1, h1⟩ := r1
  simp only at t1 ⊢
  show _ = runDet P G s ((sendK o1 _ >>= fun o ↦ skelEv _ o []) >>= _) h1
  rw [bind_assoc]
  refine runDet_bind_congr P G s _ _ _ h1 ?_
  have t2 := trees_sendK P G s o1 (2 ^ sh.residualVars) h1
  generalize runDet P G s (sendK o1 (2 ^ sh.residualVars)) h1 = r2 at t2 ⊢
  obtain ⟨o2, h2⟩ := r2
  simp only at t2 ⊢
  have hb2 : (o2.trees.getD (sh.levels.length + 1) []).length =
      QuotientZk.Instance.lastDepth sh.depth₁ sh.levels + 1 := by rw [t2, t1, hb]
  rw [← queryPhase_skelEv _ _ _ _ o2 hb2, bind_assoc]
  refine runDet_bind_congr P G s _ _ _ h2 ?_
  generalize runDet P G s (queryPhase o2 (sh.levels.length + 1) (sh.queries.getLastD 0)) h2 = r3
  obtain ⟨o3, h3⟩ := r3
  simp only
  rw [← rounds_skelEv, bind_assoc]
  refine runDet_bind_congr P G s _ _ _ h3 ?_
  generalize runDet P G s (rounds o3 (sh.residualVars - 1)) h3 = r4
  obtain ⟨o4, h4⟩ := r4
  simp only [skelEv, bind_assoc, pure_bind]

/-- **The skeleton's opening on its events**, against the oracle: from the batching draw, the
level-0 tree `lv₀` (of depth `depth₀`) the only one, every later level with its queries. -/
theorem openTail_run (sh : QuotientZk.Deployed.OpenShape) (o : OSt) (lv₀ : List (List
    QuotientRpm.Bytes32)) (ht : o.trees = [lv₀]) (hlv : lv₀.length = sh.depth₀ + 1)
    (hq : sh.levels.length ≤ (sh.queries.drop 1).length) (hist : List Out) :
    runDet P G s (openTail sh o) hist =
      runDet P G s (skelEv (Render.openingEv sh) o [] >>= fun o ↦ pure (o.stream, o.merkle)) hist := by
  simp only [openTail, Render.openingEv, List.append_assoc, List.cons_append, List.nil_append]
  simp only [skelEv, bind_assoc]
  refine runDet_bind_congr P G s _ _ _ hist ?_
  have t1 := trees_drawO P G s o hist
  generalize runDet P G s (drawO o) hist = r1 at t1 ⊢
  obtain ⟨⟨c1, o1⟩, h1⟩ := r1
  simp only at t1 ⊢
  refine runDet_bind_congr P G s _ _ _ h1 ?_
  have t2 := trees_sendK P G s o1 2 h1
  generalize runDet P G s (sendK o1 2) h1 = r2 at t2 ⊢
  obtain ⟨o2, h2⟩ := r2
  simp only at t2 ⊢
  rw [← rounds_skelEv, bind_assoc]
  refine runDet_bind_congr P G s _ _ _ h2 ?_
  have t3 := trees_rounds P G s 6 o2 h2
  generalize runDet P G s (rounds o2 6) h2 = r3 at t3 ⊢
  obtain ⟨o3, h3⟩ := r3
  simp only at t3 ⊢
  rw [skelEv_commit, bind_assoc]
  refine runDet_bind_congr P G s _ _ _ h3 ?_
  obtain ⟨lv₁, t4, hlv₁⟩ := trees_commitNext P G s o3 sh.depth₁ h3
  generalize runDet P G s (commitNext o3 sh.depth₁) h3 = r4 at t4 ⊢
  obtain ⟨o4, h4⟩ := r4
  simp only at t4 ⊢
  rw [← ood_skelEv, bind_assoc]
  refine runDet_bind_congr P G s _ _ _ h4 ?_
  have t5 := trees_ood P G s o4 sh.ood₀ h4
  generalize runDet P G s (ood o4 sh.ood₀) h4 = r5 at t5 ⊢
  obtain ⟨o5, h5⟩ := r5
  simp only at t5 ⊢
  have htr : o5.trees = [lv₀, lv₁] := by rw [t5, t4, t3, t2, t1, ht]; rfl
  have hb5 : (o5.trees.getD 0 []).length = sh.depth₀ + 1 := by rw [htr]; exact hlv
  rw [← queryPhase_skelEv _ _ _ _ o5 hb5, bind_assoc]
  refine runDet_bind_congr P G s _ _ _ h5 ?_
  have t6 := trees_queryPhase P G s 0 (sh.queries.headD 0) sh.depth₀ o5 hb5 h5
  generalize runDet P G s (queryPhase o5 0 (sh.queries.headD 0)) h5 = r6 at t6 ⊢
  obtain ⟨o6, h6⟩ := r6
  simp only at t6 ⊢
  refine middle_run P G s _ _ _ sh.levels (sh.queries.drop 1) 1 sh.depth₁ o6 h6 hq
    (by rw [t6, htr]; rfl) (by rw [t6, htr]; exact hlv₁) ?_
  intro o' h' ho1 ho2
  have e : 1 + sh.levels.length = sh.levels.length + 1 := by ring
  rw [e] at ho2
  exact tail_run P G s sh o' ho2 h'

end Run

end PcsQuotient.EndToEnd.Core
