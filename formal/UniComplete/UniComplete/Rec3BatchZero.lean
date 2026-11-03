-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. π1-rec3's batch: the verifier's terminal on the honest
-- paired batch (`Rec3BatchSync.lean`'s `batchTerminal3`) vanishes, as `BatchProof.lean`'s `collectedAt_eq_zero` for
-- the main line.
import UniComplete.Rec3BatchSync

/-!
# π1-rec3's batch accepts the honest paired batch

**`batchTerminal3_eq_zero`**: for the honest batch (`BatchHolds … none none`: every combined claim holds of its
stack, is well formed on its aligned layout, its stack of `2^vars` words; no pending matrices), what
`batchFsH … .rec3` collects is zero, at every writer, so **`batchSyncs3_honest`**: `BatchSyncs3` at the zero
terminal.

The route: the target is the sum of products' total (`target_eq_T`: each claim's value is its weight's pairing with
its stack, `Combined.Holds`); along the pair rounds and the last plain round the verifier's claim stays the partial
sum at the point (`pairsRun_honest`, `batch3Run_honest`: `Rec3Pairs.lean`'s `pair_round_complete`,
`plain_round_complete` on `Rec3BatchAlg.lean`'s `pairMsg_honest`, `plainMsg_honest`), so the last claim is the main
line's `terminalOf` at the point (`prodOf_T_full`); the verifier's weighted sum at the point is the same (the main
line's `weightAt_eq_mle`, `mleAt_eq_tableEval`, `extensionAt_eq`); in characteristic two the two cancel.
-/

namespace UniComplete.Rec3

open UniStatement LeanVM.Parameters Finset
open LeanVM.Protocol (Digest)
open UniSound (pairCoeffs cantorBeta1_spec foldAll)

variable (H : List UInt8 → Digest)

theorem length_pairPoint' (z : E) : (pairPoint z).length = 2 := rfl

/-- **The honest pair rounds keep the verifier's claim the partial sum** at the point. -/
theorem pairsRun_honest (lambda : E) (V : ℕ) (Z : List (Array E × Array E)) :
    ∀ (n j : ℕ) (r : List E) (w : Wr), r.length = 2 * j → 2 * (j + n) ≤ V →
      (pairsRun H lambda V Z n j r ((prodOf lambda V Z).T r) w).2.1 =
        (prodOf lambda V Z).T (r ++ zsPoint (pairsRun H lambda V Z n j r ((prodOf lambda V Z).T r) w).1)
  | 0, _, r, _, _, _ => by simp [pairsRun, zsPoint]
  | n + 1, j, r, w, hr, hV => by
    have hcs : (pairStep H lambda V j Z r w).1 =
        pairMsgOf cantorBeta1 lambda (2 ^ (V - r.length - 2)) (stOf Z r).weights (stOf Z r).tabs := by
      simp only [pairStep, hr]
    have heval : ∀ x, polyEval (pairStep H lambda V j Z r w).1 x =
        (prodOf lambda V Z).T (r ++ UniSound.pairPoint cantorBeta1 x) := fun x ↦ by
      rw [hcs]; exact pairMsg_honest cantorBeta1 lambda V Z r x
    have hlen : (pairStep H lambda V j Z r w).1.length = 9 := by rw [hcs]; exact length_pairMsgOf _ _ _ _ _
    have hstep := (pair_round_complete (prodOf lambda V Z) cantorBeta1_spec r
      (by show r.length + 2 ≤ V; omega) _ hlen heval).2 (pairStep H lambda V j Z r w).2.1
    have ih := pairsRun_honest lambda V Z n (j + 1) (r ++ pairPoint (pairStep H lambda V j Z r w).2.1)
      (pairStep H lambda V j Z r w).2.2 (by rw [List.length_append, length_pairPoint', hr]; ring) (by omega)
    show (pairsRun H lambda V Z n (j + 1) (r ++ pairPoint (pairStep H lambda V j Z r w).2.1)
        (polyEval (pairCoeffs ((prodOf lambda V Z).T r) (msg8 (pairStep H lambda V j Z r w).1))
          (pairStep H lambda V j Z r w).2.1) (pairStep H lambda V j Z r w).2.2).2.1 =
      (prodOf lambda V Z).T (r ++ zsPoint ((pairStep H lambda V j Z r w).2.1 ::
        (pairsRun H lambda V Z n (j + 1) (r ++ pairPoint (pairStep H lambda V j Z r w).2.1)
          (polyEval (pairCoeffs ((prodOf lambda V Z).T r) (msg8 (pairStep H lambda V j Z r w).1))
            (pairStep H lambda V j Z r w).2.1) (pairStep H lambda V j Z r w).2.2).1))
    rw [hstep, ← UniSound.pairPoint_cantorBeta1, ih, zsPoint_cons, List.append_assoc]

/-- **The honest batch rounds**: from the true target, the point has `V` coordinates and the verifier's last claim is
the partial sum there. -/
theorem batch3Run_honest (lambda : E) (V : ℕ) (Z : List (Array E × Array E)) (w : Wr) :
    (batch3Run H lambda V Z ((prodOf lambda V Z).T []) w).1.length = V ∧
      (batch3Run H lambda V Z ((prodOf lambda V Z).T []) w).2.1 =
        (prodOf lambda V Z).T (batch3Run H lambda V Z ((prodOf lambda V Z).T []) w).1 := by
  have hp := pairsRun_honest H lambda V Z (V / 2) 0 [] w rfl (by omega)
  simp only [List.nil_append] at hp
  have hl : (zsPoint (pairsRun H lambda V Z (V / 2) 0 [] ((prodOf lambda V Z).T []) w).1).length = 2 * (V / 2) := by
    rw [length_zsPoint, length_pairsRun]
  unfold batch3Run
  by_cases hV : V % 2 = 1
  · simp only [hV, ↓reduceIte]
    refine ⟨by rw [List.length_append, hl, List.length_singleton]; omega, ?_⟩
    set rp := zsPoint (pairsRun H lambda V Z (V / 2) 0 [] ((prodOf lambda V Z).T []) w).1 with hrp
    have hr : rp.length < V := by omega
    have h := plainMsg_honest lambda V Z rp hr
      (plainStep H lambda Z rp (pairsRun H lambda V Z (V / 2) 0 [] ((prodOf lambda V Z).T []) w).2.2).2.1
    rw [show V - rp.length - 1 = 0 by omega, pow_zero] at h
    rw [hp]
    exact h
  · simp only [hV, ↓reduceIte]
    exact ⟨by rw [hl]; omega, hp⟩

/-- **The batch's target is the sum of products' total**, for claims that hold of their stacks. -/
theorem target_eq_T (combined : List (Commitment × Combined)) (stackLayouts : List (Commitment × StackLayout))
    (stackOf : Commitment → Array K) (ringMap : Option (List E))
    (h : BatchHolds combined stackLayouts stackOf ringMap none none) (lambda : E) :
    (targetFold lambda combined).1 =
      (prodOf lambda (batchVars stackLayouts) (batchZ combined stackLayouts stackOf ringMap)).T [] := by
  rw [targetFold_eq, prodOf_T_wsum, batchZ, List.map_map]
  refine wsum_congr _ _ _ _ fun x hx ↦ ?_
  obtain ⟨hh, -, -, hsz⟩ := h.claims x hx
  have hd := layoutIn_vars_le stackLayouts x.1
  simp only [Function.comp_apply, List.length_nil, Nat.sub_zero]
  rw [← hh, dotK_eq]
  unfold dotE
  have hW := denseWeight_size x.2 (layoutIn stackLayouts x.1) ringMap
  have hle : 2 ^ (layoutIn stackLayouts x.1).vars ≤ 2 ^ batchVars stackLayouts :=
    Nat.pow_le_pow_right (by norm_num) hd
  rw [hW, ← sum_range_add_sum_Ico _ hle, sum_eq_zero (s := Ico _ _) (fun i hi ↦ by
    simp only [foldAll, List.foldl_nil]
    rw [getD_ge _ (by rw [hW]; exact (mem_Ico.mp hi).1), zero_mul]), add_zero]
  rfl

/-- **What `batchFsH … .rec3` collects on the honest batch is zero**, at every writer. -/
theorem batchTerminal3_eq_zero (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E))
    (h : BatchHolds combined stackLayouts stackOf ringMap none none) (w : Wr) :
    batchTerminal3 H combined stackLayouts stackOf ringMap w = 0 := by
  unfold batchTerminal3
  dsimp only
  set lam := (Wr.sampled H w).1
  set pairs : List (Array E × Array E × ℕ) := combined.map fun x ↦
    (denseWeight x.2 (layoutIn stackLayouts x.1) ringMap, (stackOf x.1).map ofK, (layoutIn stackLayouts x.1).vars)
    with hpairs
  have hZ : batchZ combined stackLayouts stackOf ringMap = pairs.map fun p ↦ (p.1, p.2.1) := by
    simp [batchZ, hpairs, List.map_map, Function.comp_def]
  rw [target_eq_T combined stackLayouts stackOf ringMap h lam]
  obtain ⟨hlen, hlast⟩ := batch3Run_honest H lam (batchVars stackLayouts)
    (batchZ combined stackLayouts stackOf ringMap) (Wr.sampled H w).2
  rw [hlast]
  generalize (batch3Run H lam (batchVars stackLayouts) (batchZ combined stackLayouts stackOf ringMap)
    ((prodOf lam (batchVars stackLayouts) (batchZ combined stackLayouts stackOf ringMap)).T [])
    (Wr.sampled H w).2).1 = rs at hlen ⊢
  have hpairsWF : ∀ p ∈ pairs, p.1.size = 2 ^ p.2.2 ∧ p.2.1.size = 2 ^ p.2.2 ∧ p.2.2 ≤ batchVars stackLayouts := by
    intro p hp
    rw [hpairs] at hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    obtain ⟨-, -, -, hsz⟩ := h.claims x hx
    exact ⟨denseWeight_size _ _ _, by rw [Array.size_map, hsz], layoutIn_vars_le _ _⟩
  rw [hZ, prodOf_T_full lam _ pairs hpairsWF rs hlen]
  set S := wsum lam (pairs.map fun p ↦
    tableEval p.1 (rs.take p.2.2) * tableEval p.2.1 (rs.take p.2.2) * extOf rs p.2.2 ^ 2) with hS
  have hsum : (sumFold combined stackLayouts ringMap lam (batchVars stackLayouts) rs
      ((claimsOf combined stackLayouts stackOf rs).map (·.2.2))).1 = S := by
    rw [sumFold_eq, claimsOf_values, zip_map_self, hS, hpairs]
    dsimp only
    simp only [List.map_map]
    refine wsum_congr _ _ _ _ fun x hx ↦ ?_
    obtain ⟨-, hwf, hal, -⟩ := h.claims x hx
    have hd := layoutIn_vars_le stackLayouts x.1
    simp only [Function.comp_apply]
    rw [weightAt_eq_mle x.2 _ rs ringMap hal (by omega) hwf,
      mleAt_eq_tableEval _ _ (denseWeight_size _ _ _) rs (by omega), extensionAt_eq rs _ _ hlen]
    ring
  rw [hsum]
  simp only [terminalOf, mul_zero, add_zero, ← hS]
  exact add_self_E S

/-- **`batchFsH … .rec3` accepts the honest paired batch**: `BatchSyncs3` at the zero terminal. -/
theorem batchSyncs3_honest (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E))
    (h : BatchHolds combined stackLayouts stackOf ringMap none none) :
    BatchSyncs3 H combined stackLayouts stackOf ringMap (fun _ ↦ 0) := by
  intro w
  have := batchSyncs3 H combined stackLayouts stackOf ringMap w
  rwa [batchTerminal3_eq_zero H combined stackLayouts stackOf ringMap h w] at this

end UniComplete.Rec3

/-- info: 'UniComplete.Rec3.batchTerminal3_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.batchTerminal3_eq_zero

/-- info: 'UniComplete.Rec3.batchSyncs3_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniComplete.Rec3.batchSyncs3_honest
