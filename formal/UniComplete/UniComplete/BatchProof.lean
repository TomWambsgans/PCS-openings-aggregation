-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.BatchProofSync

/-!
# `batch` accepts the honest batching sumcheck (`BatchSyncs`)

On a channel synchronised with the prover's writer before step 9, at a pure Keccak-256 `H`, the verifier's
`batchH (pure ∘ H) combined layouts none ringMap pending` reads back the prover's messages (`batchProver`, SyncBasic's
transcription of `proveStreamWith`'s step 9): `λ`, the rounds, the stacks' values, Flock's `a`, `b`; it returns the
prover's point claims (`pointOpening`: `(c, .point (r.take vars_c) value_c none)`, `value_c` the stack's multilinear
extension at `r.take vars_c`) and the matrices' claim `p.matrixClaim r a b`, and collects one value, `batchTerminal`
(`batchSyncs`, SyncBasic's `BatchSyncs`). **That value is zero** (`batchTerminal_eq_zero`, at every writer: at every
`λ` and every challenge list of the batch's length, `collectedAt_eq_zero`) given

* every combined claim holds of its stack (`Combined.Holds`), is well formed for its layout (`WeightWF`), on an
  aligned layout (`Aligned`; `StackLayout.new`'s are, `aligned_new`), its stack of `2^vars` words;
* with Flock's matrices pending (`pending = some (p, _)`, `tables = some t`, `p.hasSlices`): the tables' shape
  (`PendingShape`), **`PendingSumHolds`** (`Σ_i G_i L_i S_i = p.claim`) and **`PendingTerminalHolds`**
  (`(a + α b) L̂(ρ) ŝ(σ) = G̃ L̃ S̃` at the point, `a`, `b` the extensions of `A0`, `B0` at the claim's point), and
  `p.rounds ≤ vars`; without (`Blake2s.omitted`): `pending = none`, `tables = none`.

The value is `sum + λ^n value extension + last` (`sum + last` without the matrices): `last` is the sumcheck's
terminal (`batch_rounds`: `Σ_k λ^k W̃_k C̃_k ext_k² + λ^n G̃ L̃ S̃ ext`), `sum` the verifier's `Σ_k λ^k weightAt ·
extension · value` (`weightAt_eq_mle`: `W̃_k ext_k`; the extension `ext_k`; the value `C̃_k`), the matrices'
term `λ^n G̃ L̃ S̃ ext` by `PendingTerminalHolds`: each part twice, zero in characteristic two.

Decisions: the verifier's and the prover's sub-computations are named by their text (`targetFold`, `sumFold`,
`claimsOf`, `extensionAt`), so that the synchronisation reads them by definitional unfolding and the algebra rewrites
them by closed forms (`targetFold_eq`, `sumFold_eq`, `extensionAt_eq`).
-/

open LeanVM.Parameters LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open LeanVM.Protocol.EndToEnd (boolPoint)
open UniStatement
open Finset

namespace UniComplete

/-! ## The Flock hypotheses -/

/-- **The pending matrices' tables fit the batch**: their rounds the pending claim's (`k + 6`), `2^rounds` entries
each, `L̂` on the low `k` bits (`L[x + 2^k y] = L̂(x)`) and `ŝ` on the others (`S[x + 2^k y] = ŝ(y)`). -/
structure PendingShape (p : Flock.Pending) (t : PendingTables) : Prop where
  rounds : t.rounds = p.rounds
  g_size : t.g.size = 2 ^ t.rounds
  l_size : t.l.size = 2 ^ t.rounds
  s_size : t.s.size = 2 ^ t.rounds
  low : LowDep t.l p.k
  high : 0 < p.k → HighDep t.s p.k

/-- **The pending sum identity**: the matrices' product sum `Σ_i G_i L̂_i ŝ_i` is the pending claim. -/
def PendingSumHolds (p : Flock.Pending) (t : PendingTables) : Prop := prod3 t.g t.l t.s = p.claim

/-- **The pending terminal identity**: at every point `r` (of at least the matrices' `k + 6` coordinates), the
summand's value `(a + α b) L̂(ρ) ŝ(σ)` (`Pending.terminal`), `a`, `b` the multilinear extensions of `A0`, `B0` at the
matrices' claim's point `(ρ, row_low, chi_in, σ, chi_in')` (as the prover computes them), is `G̃ L̃ S̃` at `r`'s first
`k + 6` coordinates. -/
def PendingTerminalHolds (p : Flock.Pending) (t : PendingTables) : Prop :=
  ∀ r : List E, p.rounds ≤ r.length →
    (p.terminal r (stackEval (flockMatrixStack true) (p.matrixClaim r 0 0).point)
        (stackEval (flockMatrixStack false) (p.matrixClaim r 0 0).point)).1 =
      tableEval t.g (r.take p.rounds) * tableEval t.l (r.take p.rounds) * tableEval t.s (r.take p.rounds)

/-! ## The verifier's and the prover's sub-computations, by their text -/

/-- `batch`'s target and scale (its text). -/
def targetFold (lambda : E) (combined : List (Commitment × Combined)) : E × E :=
  combined.foldl (fun (acc : E × E) (_, claim) ↦ (acc.1 + acc.2 * claim.value, acc.2 * lambda)) (0, 1)

/-- `batch`'s zero extension past `from` of the batch's `vars` (its text). -/
def extensionAt (r : List E) (fromVar vars : ℕ) : E :=
  (List.range' fromVar (vars - fromVar)).foldl (fun e j ↦ e * (1 + r.getD j 0)) 1

/-- `batch`'s terminal sum, scale and openings over the values read (its text, `bitSlice = none`). -/
def sumFold (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (ringMap : Option (List E)) (lambda : E) (vars : ℕ) (r : List E) (values : List E) :
    E × E × Array (Commitment × Opening) × Option Combined :=
  let layoutOf (c : Commitment) : StackLayout := ((layouts.find? (·.1 == c)).map (·.2)).getD default
  (combined.zip values).foldl
    (fun (acc : E × E × Array (Commitment × Opening) × Option Combined) ((commitment, claim), value) ↦
      let (sum, scale, openings, bitSlice) := acc
      let layout := layoutOf commitment
      let weight := weightAt claim layout r ringMap
      let extension := (List.range' layout.vars (vars - layout.vars)).foldl
        (fun e j ↦ e * (1 + r.getD j 0)) 1
      let (mine, rest) := if commitment == .c1 then (bitSlice, none) else (none, bitSlice)
      (sum + scale * weight * extension * value, scale * lambda,
        openings.push (commitment, .point (r.take layout.vars) value mine), rest))
    (0, 1, #[], none)

/-- The prover's point claims at the point `r` (`batchProver`'s text). -/
def claimsOf (combined : List (Commitment × Combined)) (stackLayouts : List (Commitment × StackLayout))
    (stackOf : Commitment → Array K) (r : List E) : List (Commitment × List E × E) :=
  combined.map fun (c, _) ↦
    let pt := r.take (layoutIn stackLayouts c).vars
    (c, pt, multilinearEval ((stackOf c).toList.map ofK) pt)

/-- The batch's variables (`batch`'s and `batchProver`'s). -/
def batchVars (stackLayouts : List (Commitment × StackLayout)) : ℕ := (stackLayouts.map (·.2.vars)).foldl max 0

/-- The prover's state before the rounds (`batchProver`'s text). -/
def batchInit (combined : List (Commitment × Combined)) (stackLayouts : List (Commitment × StackLayout))
    (stackOf : Commitment → Array K) (ringMap : Option (List E)) (tables : Option PendingTables) : BatchState :=
  ⟨combined.map (fun (c, claim) ↦ denseWeight claim (layoutIn stackLayouts c) ringMap),
    combined.map (fun (c, _) ↦ (stackOf c).map ofK), tables, 0, []⟩

/-- **What `batch` collects** at `λ` and the challenges `rs`, on the honest messages: `sum + scale · value ·
extension + last` with Flock's matrices pending (their slices sent), `sum + last` without. -/
def collectedAt (combined : List (Commitment × Combined)) (stackLayouts : List (Commitment × StackLayout))
    (stackOf : Commitment → Array K) (ringMap : Option (List E)) (tables : Option PendingTables)
    (pending : Option (Flock.Pending × List E)) (lambda : E) (rs : List E) : E :=
  let vars := batchVars stackLayouts
  let st := batchInit combined stackLayouts stackOf ringMap tables
  let target := match pending with
    | some (p, _) => (targetFold lambda combined).1 + (targetFold lambda combined).2 * p.claim
    | none => (targetFold lambda combined).1
  let last := claimRun lambda 0 rs st target
  let f4 := sumFold combined stackLayouts ringMap lambda vars rs ((claimsOf combined stackLayouts stackOf rs).map (·.2.2))
  match pending with
  | some (p, _) =>
    let mc := p.matrixClaim rs 0 0
    let a := multilinearEval ((flockMatrixStack true).toList.map ofK) mc.point
    let b := multilinearEval ((flockMatrixStack false).toList.map ofK) mc.point
    f4.1 + f4.2.1 * (p.terminal rs a b).1 * extensionAt rs p.rounds vars + last
  | none => f4.1 + last

/-- **The collected value at the writer `w`**: at its `λ` (`Wr.sampled`) and the rounds' challenges from there. -/
def batchTerminal (H : List UInt8 → Digest) (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E))
    (tables : Option PendingTables) (pending : Option (Flock.Pending × List E)) (w : Wr) : E :=
  collectedAt combined stackLayouts stackOf ringMap tables pending (Wr.sampled H w).1
    (loopChallenges H (Wr.sampled H w).1 (batchVars stackLayouts) 0
      (batchInit combined stackLayouts stackOf ringMap tables) (Wr.sampled H w).2)

/-! ## Closed forms -/

theorem foldl_scaled {α : Type} (lambda : E) (f : α → E) (step : E × E → α → E × E)
    (hstep : ∀ acc x, step acc x = (acc.1 + acc.2 * f x, acc.2 * lambda)) :
    ∀ (L : List α) (a s : E), L.foldl step (a, s) = (a + s * wsum lambda (L.map f), s * lambda ^ L.length)
  | [], a, s => by simp [wsum]
  | x :: L, a, s => by
    rw [List.foldl_cons, hstep, foldl_scaled lambda f step hstep L]
    simp only [List.map_cons, wsum, List.length_cons, Prod.mk.injEq]
    exact ⟨by ring, by ring⟩

theorem targetFold_eq (lambda : E) (combined : List (Commitment × Combined)) :
    targetFold lambda combined =
      (wsum lambda (combined.map fun x ↦ x.2.value), lambda ^ combined.length) := by
  unfold targetFold
  refine (foldl_scaled lambda (fun x ↦ x.2.value) _ (fun _ _ ↦ ?_) combined 0 1).trans ?_
  · rfl
  · rw [zero_add, one_mul, one_mul]

theorem foldl_four {α : Type} (lambda : E) (f : α → E) (o : α → Commitment × Opening)
    (step : E × E × Array (Commitment × Opening) × Option Combined → α →
      E × E × Array (Commitment × Opening) × Option Combined)
    (hstep : ∀ a s arr x, step (a, s, arr, none) x = (a + s * f x, s * lambda, arr.push (o x), none)) :
    ∀ (L : List α) (a s : E) (arr : Array (Commitment × Opening)), L.foldl step (a, s, arr, none) =
      (a + s * wsum lambda (L.map f), s * lambda ^ L.length, arr ++ (L.map o).toArray, none)
  | [], a, s, arr => by simp [wsum]
  | x :: L, a, s, arr => by
    rw [List.foldl_cons, hstep, foldl_four lambda f o step hstep L]
    simp only [List.map_cons, wsum, List.length_cons]
    refine Prod.ext (by dsimp only; ring) (Prod.ext (by dsimp only; ring) (Prod.ext ?_ rfl))
    apply Array.toList_inj.mp
    simp

/-- **`batch`'s terminal fold**: the sum `Σ_k λ^k weight · extension · value`, the scale `λ^n`, the openings. -/
theorem sumFold_eq (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (ringMap : Option (List E)) (lambda : E) (vars : ℕ) (r : List E) (values : List E) :
    sumFold combined layouts ringMap lambda vars r values =
      (wsum lambda ((combined.zip values).map fun x ↦
          weightAt x.1.2 (layoutIn layouts x.1.1) r ringMap * extensionAt r (layoutIn layouts x.1.1).vars vars * x.2),
        lambda ^ (combined.zip values).length,
        ((combined.zip values).map fun x ↦
          (x.1.1, Opening.point (r.take (layoutIn layouts x.1.1).vars) x.2 none)).toArray, none) := by
  unfold sumFold
  refine (foldl_four lambda (fun x ↦
      weightAt x.1.2 (layoutIn layouts x.1.1) r ringMap * extensionAt r (layoutIn layouts x.1.1).vars vars * x.2)
    (fun x ↦ (x.1.1, Opening.point (r.take (layoutIn layouts x.1.1).vars) x.2 none)) _
    (fun a s arr x ↦ ?_) (combined.zip values) 0 1 #[]).trans ?_
  · obtain ⟨⟨c, claim⟩, value⟩ := x
    dsimp only
    split
    all_goals
      refine Prod.ext ?_ rfl
      simp only [extensionAt, layoutIn]
      ring
  · simp only [zero_add, one_mul, Array.empty_append]

/-! ## Extensions, sizes, values -/

theorem prod_map_getD (f : E → E) : ∀ l : List E, (l.map f).prod = ∏ i ∈ range l.length, f (l.getD i 0)
  | [] => by simp
  | x :: l => by
    rw [List.map_cons, List.prod_cons, prod_map_getD f l, List.length_cons, prod_range_succ']
    simp [mul_comm]

/-- `Π_{j ≥ d} (1 + r_j)` as a product over the coordinates past `d`. -/
theorem extOf_eq (r : List E) (d : ℕ) :
    extOf r d = ∏ i ∈ range (r.length - d), (1 + r.getD (d + i) 0) := by
  unfold extOf
  rw [prod_map_getD, List.length_drop]
  refine prod_congr rfl fun i _ ↦ ?_
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **`batch`'s extension is the zero extension's factor** (the point of the batch's `vars` coordinates). -/
theorem extensionAt_eq (r : List E) (d vars : ℕ) (hr : r.length = vars) : extensionAt r d vars = extOf r d := by
  unfold extensionAt
  rw [List.range'_eq_map_range, List.foldl_map, foldl_mul_map, one_mul, prod_map_range, extOf_eq, hr]

theorem selector_zero (r : List E) (d : ℕ) : UniStatement.selector r d 0 = extOf r d := by
  rw [selector_eq, extOf_eq]
  simp

/-- **A table's extension over the batch's variables**, zero past its `2^d` entries: its extension at `r_{<d}`
times `Π_{j ≥ d} (1 + r_j)`. -/
theorem mleAt_eq_tableEval (W : Array E) (d : ℕ) (hW : W.size = 2 ^ d) (r : List E) (hd : d ≤ r.length) :
    mleAt r.length r W = tableEval W (r.take d) * extOf r d := by
  unfold mleAt
  have hle : 2 ^ d ≤ 2 ^ r.length := Nat.pow_le_pow_right (by norm_num) hd
  rw [← sum_range_add_sum_Ico _ hle, sum_eq_zero (s := Ico _ _) (fun x hx ↦ by
    rw [getD_ge W (by rw [hW]; exact (mem_Ico.mp hx).1), zero_mul]), add_zero]
  have hl : (r.take d).length = d := by simp [hd]
  unfold tableEval UniStatement.multilinearEval
  rw [Array.toArray_toList, foldl_foldOnce _ _ (by rw [hl, hW]), hl, sum_mul, ← selector_zero]
  refine sum_congr rfl fun x hx ↦ ?_
  have h0 := eqEval_block (r := r) (off := 0) hd (dvd_zero _) (mem_range.mp hx)
  rw [zero_add] at h0
  rw [h0, mul_assoc]

theorem foldl_size {α : Type} (f : Array E → α → Array E) (hf : ∀ W a, (f W a).size = W.size) :
    ∀ (l : List α) (W : Array E), (l.foldl f W).size = W.size
  | [], _ => rfl
  | a :: l, W => by rw [List.foldl_cons, foldl_size f hf l, hf]

/-- The dense weight has the stack's `2^vars` words. -/
theorem denseWeight_size (claim : Combined) (layout : StackLayout) (ringMap : Option (List E)) :
    (denseWeight claim layout ringMap).size = 2 ^ layout.vars := by
  rw [denseWeight_eq_fold, foldl_size _ (fun W t ↦ ?_), Array.size_replicate]
  obtain ⟨c, p, tw, co⟩ := t
  unfold denseStep
  dsimp only
  split
  all_goals
    refine foldl_size _ (fun W b ↦ ?_) _ _
    exact foldl_size _ (fun W u ↦ addAt_size _ _ _) _ _

/-- The pairing of a weight with a stack's words is `dotE` against the words in `E`. -/
theorem ofK_zero' : ofK (0 : K) = 0 := by
  have h := LeanVM.Parameters.ofK_add (0 : K) 0
  rw [add_zero] at h
  have : ofK (0 : K) + ofK 0 = ofK 0 + 0 := by rw [← h, add_zero]
  exact add_left_cancel this

theorem dotK_eq (w : Array E) (s : Array K) : dotK w s = dotE w (s.map ofK) := by
  unfold dotK dotE
  rw [foldl_add_map, zero_add, sum_map_range]
  refine sum_congr rfl fun u _ ↦ ?_
  congr 1
  by_cases hu : u < s.size
  · simp [Array.getD_eq_getD_getElem?, hu]
  · rw [getD_ge _ (by simpa using hu)]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (show s.size ≤ u by omega), Option.getD_none]
    exact ofK_zero'

theorem foldl_max_ge : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], a => ⟨le_rfl, by simp⟩
  | x :: l, a => by
    obtain ⟨h1, h2⟩ := foldl_max_ge l (max a x)
    rw [List.foldl_cons]
    refine ⟨le_trans (le_max_left a x) h1, fun y hy ↦ ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact le_trans (le_max_right a y) h1
    · exact h2 y hy

/-- Every commitment's layout has at most the batch's variables. -/
theorem layoutIn_vars_le (stackLayouts : List (Commitment × StackLayout)) (c : Commitment) :
    (layoutIn stackLayouts c).vars ≤ batchVars stackLayouts := by
  unfold layoutIn batchVars
  cases h : stackLayouts.find? (·.1 == c) with
  | none => exact Nat.zero_le _
  | some x =>
    simp only [Option.map_some, Option.getD_some]
    exact (foldl_max_ge _ 0).2 _ (List.mem_map.mpr ⟨x, List.mem_of_find?_eq_some h, rfl⟩)

theorem zip_map_self {α β : Type} (v : α → β) : ∀ l : List α, l.zip (l.map v) = l.map fun x ↦ (x, v x)
  | [] => rfl
  | x :: l => by simp [zip_map_self v l]

theorem claimsOf_values (combined : List (Commitment × Combined)) (stackLayouts : List (Commitment × StackLayout))
    (stackOf : Commitment → Array K) (r : List E) :
    (claimsOf combined stackLayouts stackOf r).map (·.2.2) =
      combined.map fun x ↦ tableEval ((stackOf x.1).map ofK) (r.take (layoutIn stackLayouts x.1).vars) := by
  unfold claimsOf tableEval
  simp [List.map_map, Function.comp_def, Array.toList_map]

/-- **A commitment's layout is aligned** when every listed layout is (`StackLayout.new`'s are, `aligned_new`; the
default, for an unlisted commitment, has no block). -/
theorem aligned_layoutIn (stackLayouts : List (Commitment × StackLayout)) (h : ∀ x ∈ stackLayouts, Aligned x.2)
    (c : Commitment) : Aligned (layoutIn stackLayouts c) := by
  unfold layoutIn
  cases hf : stackLayouts.find? (·.1 == c) with
  | none => intro _ _ _ _ hb; exact absurd hb (List.not_mem_nil)
  | some x => exact h x (List.mem_of_find?_eq_some hf)

/-- The pending matrices' rounds, as `verifyDeferred` makes them (`Pending.new`): `k + 6 ≤ 12`. -/
theorem pending_new_rounds_le (zSkip : Option E) (rowLow chiIn chiInPrime : List E) (alpha rLc : E)
    (slices : Option (List E)) :
    (Flock.Pending.new zSkip rowLow chiIn chiInPrime alpha rLc slices).rounds ≤ 12 := by
  simp only [Flock.Pending.new, Flock.Pending.rounds, Flock.packing]
  omega

/-- The verifier's stacks have at least `15` variables (`StackLayout.new`'s `MIN_STACKED_LOG`). -/
theorem batchVars_layouts_ge (shape : Shape) (c2Columns : List (Column × ℕ × Bool)) :
    15 ≤ batchVars (layouts shape c2Columns) := by
  have hmem : (Commitment.c2, StackLayout.new c2Columns) ∈ layouts shape c2Columns := by simp [layouts]
  have h15 : 15 ≤ (StackLayout.new c2Columns).vars := by
    unfold StackLayout.new
    simp only
    exact le_max_right _ _
  exact le_trans h15 ((foldl_max_ge _ 0).2 _ (List.mem_map.mpr ⟨_, hmem, rfl⟩))

/-! ## The collected value is zero -/

/-- **The honest batch's hypotheses**: every combined claim holds of its stack, is well formed for its aligned
layout, its stack of `2^vars` words; Flock's matrices pending (their slices sent, their rounds within the batch's,
their tables' shape and the two Flock identities), or neither pending matrices nor their tables. -/
structure BatchHolds (combined : List (Commitment × Combined)) (stackLayouts : List (Commitment × StackLayout))
    (stackOf : Commitment → Array K) (ringMap : Option (List E)) (tables : Option PendingTables)
    (pending : Option (Flock.Pending × List E)) : Prop where
  claims : ∀ x ∈ combined, Combined.Holds (layoutIn stackLayouts x.1) (stackOf x.1) ringMap x.2 ∧
    WeightWF x.2 (layoutIn stackLayouts x.1) ringMap ∧ Aligned (layoutIn stackLayouts x.1) ∧
    (stackOf x.1).size = 2 ^ (layoutIn stackLayouts x.1).vars
  flock : (pending = none ∧ tables = none) ∨
    ∃ p fp t, pending = some (p, fp) ∧ tables = some t ∧ p.hasSlices = true ∧ p.rounds ≤ batchVars stackLayouts ∧
      PendingShape p t ∧ PendingSumHolds p t ∧ PendingTerminalHolds p t

/-- **What `batch` collects on the honest messages is zero**, at every `λ` and every challenge list of the batch's
length. -/
theorem collectedAt_eq_zero (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E))
    (tables : Option PendingTables) (pending : Option (Flock.Pending × List E))
    (h : BatchHolds combined stackLayouts stackOf ringMap tables pending) (lambda : E) (rs : List E)
    (hrs : rs.length = batchVars stackLayouts) :
    collectedAt combined stackLayouts stackOf ringMap tables pending lambda rs = 0 := by
  set pairs : List (Array E × Array E × ℕ) := combined.map fun x ↦
    (denseWeight x.2 (layoutIn stackLayouts x.1) ringMap, (stackOf x.1).map ofK, (layoutIn stackLayouts x.1).vars)
    with hpairs
  have hinit : batchInit combined stackLayouts stackOf ringMap tables = initState pairs tables := by
    simp [batchInit, initState, hpairs, List.map_map, Function.comp_def]
  have hlen : pairs.length = combined.length := by rw [hpairs, List.length_map]
  -- The pairs' part of the terminal.
  set S := wsum lambda (pairs.map fun p ↦
    tableEval p.1 (rs.take p.2.2) * tableEval p.2.1 (rs.take p.2.2) * extOf rs p.2.2 ^ 2) with hS
  have hsum : (sumFold combined stackLayouts ringMap lambda (batchVars stackLayouts) rs
      ((claimsOf combined stackLayouts stackOf rs).map (·.2.2))).1 = S := by
    rw [sumFold_eq, claimsOf_values, zip_map_self, hS, hpairs]
    dsimp only
    simp only [List.map_map]
    refine wsum_congr _ _ _ _ fun x hx ↦ ?_
    obtain ⟨-, hwf, hal, -⟩ := h.claims x hx
    have hd := layoutIn_vars_le stackLayouts x.1
    simp only [Function.comp_apply]
    rw [weightAt_eq_mle x.2 _ rs ringMap hal (by omega) hwf,
      mleAt_eq_tableEval _ _ (denseWeight_size _ _ _) rs (by omega), extensionAt_eq rs _ _ hrs]
    ring
  have hscale : (sumFold combined stackLayouts ringMap lambda (batchVars stackLayouts) rs
      ((claimsOf combined stackLayouts stackOf rs).map (·.2.2))).2.1 = lambda ^ combined.length := by
    rw [sumFold_eq]
    simp [claimsOf]
  -- The pairs' part of the target.
  have htarget : (targetFold lambda combined).1 = wsum lambda (pairs.map fun p ↦ dotE p.1 p.2.1) := by
    rw [targetFold_eq, hpairs, List.map_map]
    refine wsum_congr _ _ _ _ fun x hx ↦ ?_
    obtain ⟨hh, -, -, -⟩ := h.claims x hx
    simp only [Function.comp_apply]
    rw [← hh, dotK_eq]
  have hpairsWF : ∀ q ∈ pairs, q.1.size = 2 ^ q.2.2 ∧ q.2.1.size = 2 ^ q.2.2 ∧ q.2.2 ≤ batchVars stackLayouts := by
    intro q hq
    rw [hpairs] at hq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
    obtain ⟨-, -, -, hsz⟩ := h.claims x hx
    exact ⟨denseWeight_size _ _ _, by rw [Array.size_map, hsz], layoutIn_vars_le _ _⟩
  rcases h.flock with ⟨rfl, rfl⟩ | ⟨p, fp, t, rfl, rfl, -, hR, hsh, hps, hpt⟩
  · -- Without Flock's matrices: `sum + last`, each the pairs' part.
    have hwf : BatchWF 0 (batchVars stackLayouts) pairs none := ⟨hpairsWF, fun t ht ↦ by simp at ht⟩
    have hlast := batch_rounds lambda 0 _ pairs none hwf rs hrs
    unfold collectedAt
    dsimp only
    rw [hsum, hinit, htarget, show wsum lambda (pairs.map fun p ↦ dotE p.1 p.2.1) = targetOf lambda pairs none by
      simp [targetOf], hlast]
    simp only [terminalOf, mul_zero, add_zero, ← hS]
    exact add_self_E S
  · -- With them: `sum + λ^n value extension + last`, each part twice.
    have hk : t.rounds = p.k + 6 := hsh.rounds
    have hwf : BatchWF p.k (batchVars stackLayouts) pairs (some t) := by
      refine ⟨hpairsWF, fun t' ht' ↦ ?_⟩
      obtain rfl : t = t' := Option.some.inj ht'
      refine ⟨by omega, by rw [hsh.rounds]; exact hR, hsh.g_size, hsh.l_size, hsh.s_size,
        fun h0 ↦ by rw [← h0]; exact hsh.low, fun h0 ↦ ⟨hsh.low, hsh.high h0⟩⟩
    have hlast := batch_rounds lambda p.k _ pairs (some t) hwf rs hrs
    have hterm := hpt rs (by omega)
    unfold collectedAt
    dsimp only
    rw [hsum, hscale, hinit, htarget, targetFold_eq, ← hps,
      show wsum lambda (pairs.map fun p ↦ dotE p.1 p.2.1) + lambda ^ combined.length * prod3 t.g t.l t.s =
        targetOf lambda pairs (some t) by simp [targetOf, hlen], hlast]
    simp only [terminalOf, hlen, ← hS]
    rw [show multilinearEval ((flockMatrixStack true).toList.map ofK) (p.matrixClaim rs 0 0).point =
        stackEval (flockMatrixStack true) (p.matrixClaim rs 0 0).point from rfl,
      show multilinearEval ((flockMatrixStack false).toList.map ofK) (p.matrixClaim rs 0 0).point =
        stackEval (flockMatrixStack false) (p.matrixClaim rs 0 0).point from rfl,
      hterm, extensionAt_eq rs _ _ hrs, hsh.rounds]
    rw [← sub_eq_zero]
    ring_nf
    simp [two_eq_zero_E']

/-! ## The synchronisation -/

/-- **Two scalars read against two sent.** -/
theorem syncs_two_scalars {γ δ : Type} (x y : E) (f : E → E → ChanM Id γ) (g : WrM Id δ) (w : Wr) (c : γ)
    (zs : List E) (h : Syncs (f x y) g (w.append ([x, y].flatMap scalarWire)) c zs) :
    Syncs (nextScalar (m := Id) >>= fun a ↦ nextScalar (m := Id) >>= fun b ↦ f a b)
      (sendScalars (m := Id) [x, y] >>= fun _ ↦ g) w c zs := by
  have hR : Reads (nextScalar (m := Id) >>= fun a ↦ nextScalar (m := Id) >>= fun b ↦ Pure.pure (a, b))
      ([x, y].flatMap scalarWire) (x, y) [] :=
    Reads.congr ((nextScalar_reads x).bind ((nextScalar_reads y).bind_pure (f := fun b ↦ (x, b)))) (by simp) rfl
      (by simp)
  have hab := (Steps.readWrite hR (sendScalars_writes [x, y] w)).syncs
  have := Syncs.bind (f := fun ab ↦ f ab.1 ab.2) (g := fun _ ↦ g) hab h
  refine Syncs.congr_v (Syncs.congr this rfl (by simp)) ?_
  simp [bind_assoc]

/-- **The last step**: the verifier collects `x` and returns, the prover returns. -/
theorem syncs_requireZero_last {α β : Type} (x : E) (a : α) (b : β) (w : Wr) :
    Syncs (requireZero (m := Id) x >>= fun _ ↦ Pure.pure a) (Pure.pure b : WrM Id β) w a [x] := by
  have h := Syncs.bind (f := fun _ ↦ Pure.pure a) (g := fun _ ↦ (Pure.pure b : WrM Id β))
    (syncs_requireZero x w) (syncs_pure a b _)
  refine Syncs.congr_p (Syncs.congr h rfl (by simp)) ?_
  rw [pure_bind]

/-- **The prover's output** with Flock's matrices pending: its point claims at its challenges, and the matrices'
claim at `a`, `b` the extensions of `A0`, `B0` at the claim's point. -/
theorem batchProver_run_some (H : List UInt8 → Digest) (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E))
    (tables : Option PendingTables) (p : Flock.Pending) (fp : List E) (w : Wr) :
    ((batchProver (m := Id) (Pure.pure ∘ H) combined stackLayouts stackOf ringMap tables (some (p, fp))).run w).1 =
      (claimsOf combined stackLayouts stackOf (loopChallenges H (Wr.sampled H w).1 (batchVars stackLayouts) 0
          (batchInit combined stackLayouts stackOf ringMap tables) (Wr.sampled H w).2),
        some (p.matrixClaim (loopChallenges H (Wr.sampled H w).1 (batchVars stackLayouts) 0
            (batchInit combined stackLayouts stackOf ringMap tables) (Wr.sampled H w).2)
          (stackEval (flockMatrixStack true) (p.matrixClaim (loopChallenges H (Wr.sampled H w).1
            (batchVars stackLayouts) 0 (batchInit combined stackLayouts stackOf ringMap tables)
              (Wr.sampled H w).2) 0 0).point)
          (stackEval (flockMatrixStack false) (p.matrixClaim (loopChallenges H (Wr.sampled H w).1
            (batchVars stackLayouts) 0 (batchInit combined stackLayouts stackOf ringMap tables)
              (Wr.sampled H w).2) 0 0).point))) := by
  unfold batchProver
  rw [wr_run_bind, sampleW_run]
  dsimp only
  rw [wr_run_bind, batchRounds_run H _ _ _ rfl]
  rfl

/-- **The prover's output** without Flock's matrices: its point claims at its challenges. -/
theorem batchProver_run_none (H : List UInt8 → Digest) (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E))
    (tables : Option PendingTables) (w : Wr) :
    ((batchProver (m := Id) (Pure.pure ∘ H) combined stackLayouts stackOf ringMap tables none).run w).1 =
      (claimsOf combined stackLayouts stackOf (loopChallenges H (Wr.sampled H w).1 (batchVars stackLayouts) 0
          (batchInit combined stackLayouts stackOf ringMap tables) (Wr.sampled H w).2), none) := by
  unfold batchProver
  rw [wr_run_bind, sampleW_run]
  dsimp only
  rw [wr_run_bind, batchRounds_run H _ _ _ rfl]
  rfl

/-- The verifier's openings are the prover's point claims. -/
theorem sumFold_openings (combined : List (Commitment × Combined)) (stackLayouts : List (Commitment × StackLayout))
    (stackOf : Commitment → Array K) (ringMap : Option (List E)) (lambda : E) (vars : ℕ) (rs : List E) :
    (sumFold combined stackLayouts ringMap lambda vars rs
        ((claimsOf combined stackLayouts stackOf rs).map (·.2.2))).2.2.1.toList =
      (claimsOf combined stackLayouts stackOf rs).map pointOpening := by
  rw [sumFold_eq]
  dsimp only
  rw [claimsOf_values, zip_map_self, List.map_map]
  simp only [claimsOf, List.map_map]
  refine List.map_congr_left fun x _ ↦ ?_
  simp [pointOpening, tableEval, Array.toList_map]

theorem batchSyncs_some (H : List UInt8 → Digest) (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E))
    (tables : Option PendingTables) (p : Flock.Pending) (fp : List E) (hp : p.hasSlices = true) :
    BatchSyncs H combined stackLayouts stackOf ringMap tables (some (p, fp))
      (batchTerminal H combined stackLayouts stackOf ringMap tables (some (p, fp))) := by
  intro w
  rw [batchProver_run_some]
  unfold batchH batchProver
  refine Syncs.bind (syncs_sample H w) ?_
  rw [sampleW_run]
  generalize hlam : (Wr.sampled H w).1 = lam
  generalize hw1 : (Wr.sampled H w).2 = w1
  dsimp only
  refine Syncs.bind (syncs_sumcheck H lam _ (batchVars stackLayouts)
    (batchInit combined stackLayouts stackOf ringMap tables) w1) ?_
  rw [batchRounds_run H _ _ _ rfl]
  generalize hrs : loopChallenges H lam (batchVars stackLayouts) 0
    (batchInit combined stackLayouts stackOf ringMap tables) w1 = rs
  generalize hw2 : ((batchRounds (m := Id) (Pure.pure ∘ H) lam (batchVars stackLayouts)
    (batchInit combined stackLayouts stackOf ringMap tables)).run w1).2 = w2
  dsimp only
  refine Syncs.bind (Syncs.congr_v (syncs_scalars _ _) (by simp)) ?_
  simp only [pure_bind]
  refine syncs_two_scalars _ _ _ _ _ _ _ ?_
  simp only [hp, ite_true]
  refine Syncs.congr (syncs_requireZero_last _ _ _ _) ?_ ?_
  · refine Prod.ext ?_ rfl
    exact sumFold_openings combined stackLayouts stackOf ringMap lam (batchVars stackLayouts) rs
  · unfold batchTerminal
    rw [hlam, hw1, hrs]
    rfl

theorem batchSyncs_none (H : List UInt8 → Digest) (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E))
    (tables : Option PendingTables) :
    BatchSyncs H combined stackLayouts stackOf ringMap tables none
      (batchTerminal H combined stackLayouts stackOf ringMap tables none) := by
  intro w
  rw [batchProver_run_none]
  unfold batchH batchProver
  refine Syncs.bind (syncs_sample H w) ?_
  rw [sampleW_run]
  generalize hlam : (Wr.sampled H w).1 = lam
  generalize hw1 : (Wr.sampled H w).2 = w1
  dsimp only
  refine Syncs.bind (syncs_sumcheck H lam _ (batchVars stackLayouts)
    (batchInit combined stackLayouts stackOf ringMap tables) w1) ?_
  rw [batchRounds_run H _ _ _ rfl]
  generalize hrs : loopChallenges H lam (batchVars stackLayouts) 0
    (batchInit combined stackLayouts stackOf ringMap tables) w1 = rs
  generalize hw2 : ((batchRounds (m := Id) (Pure.pure ∘ H) lam (batchVars stackLayouts)
    (batchInit combined stackLayouts stackOf ringMap tables)).run w1).2 = w2
  dsimp only
  refine Syncs.bind (Syncs.congr_v (syncs_scalars _ _) (by simp)) ?_
  simp only [pure_bind]
  refine Syncs.congr (syncs_requireZero_last _ _ _ _) ?_ ?_
  · refine Prod.ext ?_ rfl
    exact sumFold_openings combined stackLayouts stackOf ringMap lam (batchVars stackLayouts) rs
  · unfold batchTerminal
    rw [hlam, hw1, hrs]
    rfl

/-- **`batch` reads the honest batching sumcheck** (`BatchSyncs`): with Flock's matrices pending (their slices sent)
or not, from any writer, the verifier returns the prover's point claims and matrices' claim and collects
`batchTerminal` at that writer. -/
theorem batchSyncs (H : List UInt8 → Digest) (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E))
    (tables : Option PendingTables) (pending : Option (Flock.Pending × List E))
    (hslices : ∀ p fp, pending = some (p, fp) → p.hasSlices = true) :
    BatchSyncs H combined stackLayouts stackOf ringMap tables pending
      (batchTerminal H combined stackLayouts stackOf ringMap tables pending) := by
  rcases pending with _ | ⟨p, fp⟩
  · exact batchSyncs_none H combined stackLayouts stackOf ringMap tables
  · exact batchSyncs_some H combined stackLayouts stackOf ringMap tables p fp (hslices p fp rfl)

/-- **The collected value is zero** at every writer, for the honest batch. -/
theorem batchTerminal_eq_zero (H : List UInt8 → Digest) (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E))
    (tables : Option PendingTables) (pending : Option (Flock.Pending × List E))
    (h : BatchHolds combined stackLayouts stackOf ringMap tables pending) (w : Wr) :
    batchTerminal H combined stackLayouts stackOf ringMap tables pending w = 0 :=
  collectedAt_eq_zero combined stackLayouts stackOf ringMap tables pending h _ _ (loopChallenges_length H _ _ _ _ _)

/-- **`batch` accepts the honest batching sumcheck**: the verifier returns the prover's point claims and matrices'
claim, and collects zero (`BatchSyncs` at the zero terminal), for the honest batch (`BatchHolds`: every combined
claim holds and is well formed on its aligned layout; Flock's matrices pending with their slices, their shape,
`PendingSumHolds`, `PendingTerminalHolds`; or neither pending nor tables). -/
theorem batchSyncs_honest (H : List UInt8 → Digest) (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E))
    (tables : Option PendingTables) (pending : Option (Flock.Pending × List E))
    (h : BatchHolds combined stackLayouts stackOf ringMap tables pending) :
    BatchSyncs H combined stackLayouts stackOf ringMap tables pending (fun _ ↦ 0) := by
  intro w
  have hslices : ∀ p fp, pending = some (p, fp) → p.hasSlices = true := by
    intro p fp hpend
    rcases h.flock with ⟨h1, -⟩ | ⟨p', fp', t, h1, -, hs, -⟩
    · rw [h1] at hpend; exact absurd hpend (by simp)
    · rw [h1] at hpend
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hpend)
      exact hs
  have := batchSyncs H combined stackLayouts stackOf ringMap tables pending hslices w
  rwa [batchTerminal_eq_zero H combined stackLayouts stackOf ringMap tables pending h w] at this

end UniComplete

/-- info: 'UniComplete.batchSyncs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.batchSyncs

/-- info: 'UniComplete.batchTerminal_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.batchTerminal_eq_zero

/-- info: 'UniComplete.batchSyncs_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.batchSyncs_honest

/-- info: 'UniComplete.collectedAt_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.collectedAt_eq_zero
