-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Instance.Builder
import QuotientZk.Instance.Prover

/-!
# The deployed view simulator, compiled

The end theorem's view simulator (`deployedSimV`, `EndToEnd/ZK/End.lean`) is `jointSimV` read through
the deployed prover's public renderer `out`. Several of the definitions it reaches are `noncomputable`:
the openings `openW`, `openQ` (their claims' points `pointW`, `pointQ`, `pointS` and the novel basis
`novelEnc`), `out` (the claims' bytes, `claimMsg`), and the reduction's parameters `P₀ : Params E`
themselves, whose polynomials are Mathlib polynomials. This file gives the same computation as
compiled definitions, each proved equal to the noncomputable one:

* **the novel basis at the opened positions** (`encOf`, `encTab`, `subRoots`): the normalizers
  `W_k(v_k)` (`subRoots`, `k < ℓ`, `O(ℓ²)` operations), then at each opened position `p` the `ℓ`
  values `Ŵ_k(K(p)) = W_k(K(p)) / W_k(v_k)` (`hatW`, an array per position, `O(ℓ²)` each), and an
  entry `X_y(K(p)) = Π_{bit k of y} Ŵ_k(K(p))` (at most `ℓ` products): `encOf_eq`, `novelEnc`;
* **the public evaluations** (`PubEval`): the four functions of `P₀` the simulator evaluates
  (`θ`, `v_cells(t)`, `v_rows(t)`, `pub(γ)(t)`); `PubEval.Matches pe P₀` says they are `P₀`'s; the
  verifier's formulas on them (`claimDenP`, `claimValueP`, `pointQP`, `valsQP`, `claimMsgP`) equal
  the model's (`claimDenP_eq`, …, `claimMsgP_eq`);
* **the simulator's tables as data** (`solW`, `solQ`): the lists of weighted entries the Gaussian
  elimination of `Builder.lean` returns, whose sparse tables are `simTW`, `simTQ`
  (`sparse_solW`, `sparse_solQ`);
* **the openings' level-0 views, stored** (`viewW`, `viewQ`): `Gadget.levelMap` at the compiled
  weights and encoding, its three parts (lane rounds, folded table, opened rows) written into
  arrays once (`memoL0`, `memoL0_eq`), equal to `(openW rep Y).view`, `(openQ rep P₀ Y).view`
  (`viewW_eq`, `viewQ_eq`);
* **`jointSimVm`**: `jointSimV` with these (`jointSimVm_eq`), the tables and the encodings computed
  once per run; **`outP`**: `out` with the compiled claims (`outP_eq`).

Nothing here is `noncomputable`.
-/

open OracleComp Polynomial Module QuotientSecurity QuotientSecurity.Hiding QuotientRpm
open QuotientZk.Joint
open QuotientZk.Deployed (Inp Out Msg Item Tbl Pos)

namespace QuotientZk.Instance

set_option linter.unusedSectionVars false

namespace Compiled

open Builder

/-! ## The novel basis at the opened positions -/

section Novel

variable {K : Type} [Field K]

/-- `W_k(x)` from the normalizers `roots[j] = W_j(v_j)`, `j < k`: `k` steps `a ↦ a² + roots[j]·a`
from `a = x` (`whir.rs`'s `basis = basis.square() + roots[k] * basis`). -/
def subWAt (roots : Array K) (k : ℕ) (x : K) : K :=
  (List.range k).foldl (fun a j => a ^ 2 + roots.getD j 0 * a) x

theorem subWAt_succ (roots : Array K) (k : ℕ) (x : K) :
    subWAt roots (k + 1) x = subWAt roots k x ^ 2 + roots.getD k 0 * subWAt roots k x := by
  simp only [subWAt, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem subWAt_eq (v : ℕ → K) (roots : Array K) :
    ∀ k, (∀ j < k, roots.getD j 0 = subRoot v j) → ∀ x, subWAt roots k x = (subW v k).eval x
  | 0, _, x => by simp [subWAt, subW_zero]
  | k + 1, hr, x => by
    rw [subWAt_succ, subWAt_eq v roots k (fun j hj => hr j (by omega)) x, subW_succ_eval,
      hr k (by omega)]

/-- **The normalizers** `W_k(v_k)`, `k < n` (`subspace_roots`), each from the ones before it. -/
def subRoots (v : ℕ → K) : ℕ → Array K
  | 0 => #[]
  | n + 1 => let r := subRoots v n; r.push (subWAt r n (v n))

theorem subRoots_size (v : ℕ → K) : ∀ n, (subRoots v n).size = n
  | 0 => rfl
  | n + 1 => by simp [subRoots, subRoots_size v n]

theorem subRoots_getD (v : ℕ → K) : ∀ n, ∀ j < n, (subRoots v n).getD j 0 = subRoot v j
  | 0, j, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, j, hj => by
    have hs := subRoots_size v n
    have ih := subRoots_getD v n
    simp only [subRoots]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_push]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
    · rw [if_neg (by omega), ← Array.getD_eq_getD_getElem?, ih j h]
    · rw [if_pos hs.symm, Option.getD_some, subWAt_eq v _ j (fun i hi => ih i hi), subRoot]

/-- **The normalized subspace polynomials at `x`**: `Ŵ_k(x) = W_k(v_k)⁻¹ · W_k(x)`, `k < ℓ`. -/
def hatW (roots : Array K) (ℓ : ℕ) (x : K) : Array K :=
  Array.ofFn fun k : Fin ℓ => (roots.getD k 0)⁻¹ * subWAt roots k x

/-- **The encoding's table**: at each opened position `p`, the `ℓ` values `Ŵ_k(K(p))`. -/
def encTab (w : Words K) (roots : Array K) (ℓ : ℕ) (ps : List ℕ) : Array (Array K) :=
  (ps.map fun p => hatW roots ℓ (w.word p)).toArray

/-- **The novel basis at the opened positions, read from the table**: entry `y` at the `x`-th
position is `X_y(K(p_x)) = Π_{bit k of y} Ŵ_k(K(p_x))`. -/
def encOf (tab : Array (Array K)) (ℓ : ℕ) {q : ℕ} : Fin q → Fin (2 ^ ℓ) → K :=
  fun x y => ∏ k ∈ (Finset.range ℓ).filter (fun k => (y : ℕ).testBit k), (tab.getD x #[]).getD k 0

theorem hatW_getD (roots : Array K) (ℓ : ℕ) (x : K) {k : ℕ} (hk : k < ℓ) :
    (hatW roots ℓ x).getD k 0 = (roots.getD k 0)⁻¹ * subWAt roots k x := by
  rw [hatW, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp [hk]

/-- **The table's encoding is the novel basis at the positions** (`novelEnc`). -/
theorem encOf_eq (w : Words K) (ℓ : ℕ) {q : ℕ} (ps : List ℕ) (hlen : ps.length = q)
    (pos : Fin q → ℕ) (hpos : ∀ x : Fin q, ps[(x : ℕ)]'(by rw [hlen]; exact x.isLt) = pos x) :
    encOf (encTab w (subRoots w.v ℓ) ℓ ps) ℓ = novelEnc w ℓ pos := by
  funext x y
  have hx : (x : ℕ) < ps.length := by rw [hlen]; exact x.isLt
  have htab : (encTab w (subRoots w.v ℓ) ℓ ps).getD x #[] = hatW (subRoots w.v ℓ) ℓ (w.word (pos x)) := by
    rw [encTab, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_eq_getElem hx, Option.map_some, Option.getD_some, hpos x]
  simp only [encOf, novelEnc, novel, eval_prod, eval_mul, eval_C, htab]
  refine Finset.prod_congr rfl fun k hk => ?_
  have hkℓ : k < ℓ := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  rw [hatW_getD _ _ _ hkℓ, subRoots_getD w.v ℓ k hkℓ,
    subWAt_eq w.v _ k (fun j hj => subRoots_getD w.v ℓ j (by omega)) _]

end Novel

/-! ## Storing a level-0 view -/

section Memo

variable {E K : Type}

/-- **A level-0 view written into arrays**: the six lane rounds, the folded table, the opened rows,
each computed once; the view reads them back. -/
@[noinline] def memoL0 {a b q : ℕ} (lv : L0View E (Fin a) (Fin b) (Fin q) K) :
    L0View E (Fin a) (Fin b) (Fin q) K :=
  let r := Array.ofFn lv.1
  let f := Array.ofFn lv.2.1
  let o := Array.ofFn fun x => Array.ofFn (lv.2.2 x)
  (fun j => r[(j : ℕ)]'(by simp [r]), fun y => f[(y : ℕ)]'(by simp [f]),
    fun x l => (o[(x : ℕ)]'(by simp [o]))[(l : ℕ)]'(by simp [o]))

theorem memoL0_eq {a b q : ℕ} (lv : L0View E (Fin a) (Fin b) (Fin q) K) : memoL0 lv = lv := by
  obtain ⟨r, f, o⟩ := lv
  simp [memoL0]

end Memo

/-! ## The public evaluations and the verifier's formulas on them -/

section Formulas

variable {E : Type} [Field E] [DecidableEq E] [CharP E 2]

/-- **What the simulator evaluates of the reduction's parameters**: `θ`, the cells' and the rows'
vanishing polynomials and the public weight, as functions. -/
structure PubEval (E : Type) where
  θ : E
  vCells : E → E
  vRows : E → E
  pub : E → E → E

/-- The evaluations are those of `P`'s polynomials. -/
structure PubEval.Matches (pe : PubEval E) (P : Params E) : Prop where
  θ : pe.θ = P.θ
  vCells : ∀ t, pe.vCells t = P.vCells.eval t
  vRows : ∀ t, pe.vRows t = P.vRows.eval t
  pub : ∀ γ t, pe.pub γ t = (P.pub γ).eval t

variable {pe : PubEval E} {P : Params E}

/-- `Params.claimDen` on the evaluations. -/
def claimDenP (pe : PubEval E) (α β t : E) (a : Fin 4 → E) (s : E) : E :=
  (α + cellAtC pe.θ a t 0 + β * t) * (α + cellAtC pe.θ a t 0 + β * s) + pe.vCells t

theorem claimDenP_eq (hm : pe.Matches P) (α β t : E) (a : Fin 4 → E) (s : E) :
    claimDenP pe α β t a s = P.claimDen α β t a s := by
  rw [← claimDenC_eq, claimDenP, claimDenC, hm.θ, hm.vCells]

/-- `Params.claimValue` on the evaluations. -/
def claimValueP (pe : PubEval E) (α β γ t ρ : E) (a : Fin 4 → E) (s : E) : E :=
  ((1 + ρ) * ((α + cellAtC pe.θ a t 0 + β * t) + (α + cellAtC pe.θ a t 0 + β * s)
        + pe.pub γ t * cellAtC pe.θ a t 0
          * ((α + cellAtC pe.θ a t 0 + β * t) * (α + cellAtC pe.θ a t 0 + β * s))) * pe.vRows t
      + ρ * ((α + cellAtC pe.θ a t 0 + β * t) * (α + cellAtC pe.θ a t 0 + β * s))
        * gate (cellAtC pe.θ a t 0) (cellAtC pe.θ a t 1) (cellAtC pe.θ a t 2) (cellAtC pe.θ a t 3))
    / (claimDenP pe α β t a s * pe.vRows t)

theorem claimValueP_eq (hm : pe.Matches P) (α β γ t ρ : E) (a : Fin 4 → E) (s : E) :
    claimValueP pe α β γ t ρ a s = P.claimValue α β γ t ρ a s := by
  rw [← claimValueC_eq, claimValueP, claimValueC, claimDenP_eq hm, ← claimDenC_eq, hm.θ, hm.vRows,
    hm.pub]

/-- **The quotient claim's point** (`pointQ`) on the evaluations. -/
def pointQP (pe : PubEval E) (Y : E) (c : DChal E) (v : Vals E) : List E :=
  List.ofFn (claimPointC 0 (22 + 2 + 1 + 1) c.1.1.2) ++
    [pe.vCells c.1.1.2 / claimDenP pe c.1.1.1.1 c.1.1.1.2.1 c.1.1.2 v.1 v.2, c.1.2,
      Y / (1 + Y), Y ^ 2 / (1 + Y ^ 2)]

theorem pointQP_eq (hm : pe.Matches P) (Y : E) (c : DChal E) (v : Vals E) :
    pointQP pe Y c v = pointQ P Y c v := by
  rw [← pointQc_eq, pointQP, pointQc, hm.vCells, claimDenP_eq hm, claimDenC_eq]

/-- **The quotient table's claimed values** (`valsQ`) on the evaluations, the statement's target
`tgt γ`. -/
def valsQP (pe : PubEval E) (tgt : E → E) (Y : E) (c : DChal E) (v : Vals E) : Fin 2 → E :=
  ![claimValueP pe c.1.1.1.1 c.1.1.1.2.1 c.1.1.1.2.2 c.1.1.2 c.1.2 v.1 v.2 /
      ((1 + Y) * (1 + Y ^ 2)) / claimScaleC 0 (22 + 2 + 1 + 1) c.1.1.2,
    tgt c.1.1.1.2.2 / ((1 + Y) * (1 + Y ^ 2))]

theorem valsQP_eq (hm : pe.Matches P) {tgt : E → E} {stmt : Fin P.words → E}
    (htgt : ∀ γ, tgt γ = P.target stmt γ) (Y : E) (c : DChal E) (v : Vals E) :
    valsQP pe tgt Y c v = valsQ P stmt Y c v := by
  rw [valsQP, valsQ, claimValueP_eq hm, htgt, claimScaleC_eq]

/-- The wiring claim (`modelWiring`), compiled. -/
def modelWiringC (t s : E) : List E :=
  List.ofFn (claimPointC 0 (22 + 2) t) ++ [s / claimScaleC 0 (22 + 2) t]

theorem modelWiringC_eq (t s : E) : modelWiringC t s = Implementation.modelWiring t s := rfl

end Formulas

/-! ## The simulator's tables as data -/

section Tables

variable {K E : Type} [Field K] [DecidableEq K] [Field E] [Algebra K E] [DecidableEq E] [CharP E 2]
variable {pe : PubEval E} {P : Params E}

/-- **The witness table's entries**: the elimination `simTW` runs, as a list of weighted entries. -/
def solW (rep : Rep K E) (c : DChal E) (v : Vals E) : List ((ιW × YW) × K) :=
  solveElim (r := 1 * 3) (colOf rep.coords (wW c)) (entryAt candsW (enumL Lw okW))
    (candsW.length + 40 * 2 ^ 19) (tgtOf rep.coords (fun _ : Fin 1 => valWc c v))

theorem sparse_solW (rep : Rep K E) (Y : E) (c : DChal E) (v : Vals E) :
    sparse (solW rep c v) = simTW rep Y c v := rfl

/-- The quotient table's claims' weights on the evaluations. -/
def wQP (pe : PubEval E) (Y : E) (c : DChal E) (v : Vals E) : Fin 2 → ιQ → YQ → E :=
  Lq.claimW ![pointQP pe Y c v, pointSc Y]

theorem wQP_eq (hm : pe.Matches P) (Y : E) (c : DChal E) (v : Vals E) :
    wQP pe Y c v = wQ P Y c v := by
  rw [wQP, wQ, pointQP_eq hm, pointQc_eq]

/-- **The quotient table's entries**: the elimination `simTQ` runs. -/
def solQ (rep : Rep K E) (pe : PubEval E) (tgt : E → E) (Y : E) (c : DChal E) (v : Vals E) :
    List ((ιQ × YQ) × K) :=
  solveElim (r := 2 * 3) (colOf rep.coords (wQP pe Y c v)) (entryAt candsQ (enumL Lq okQ))
    (candsQ.length + 63 * 2 ^ 22) (tgtOf rep.coords (valsQP pe tgt Y c v))

theorem sparse_solQ (rep : Rep K E) (hm : pe.Matches P) {tgt : E → E} {stmt : Fin P.words → E}
    (htgt : ∀ γ, tgt γ = P.target stmt γ) (Y : E) (c : DChal E) (v : Vals E) :
    sparse (solQ rep pe tgt Y c v) = simTQ rep P stmt Y c v := by
  rw [solQ, simTQ, build, wQP_eq hm, valsQP_eq hm htgt, valsQc_eq]

end Tables

/-! ## The openings' level-0 views -/

section Views

variable {K E : Type} [Field K] [Field E] [Algebra K E] [DecidableEq E] [CharP E 2]
variable {pe : PubEval E} {P : Params E}

/-- **The witness opening's level-0 view**, stored: `Gadget.levelMap` at the claim's point
`pointWc c` (computed once) and the novel basis at the opened positions (`encTab`, computed once),
of the stack of the table `d` and the padding `r` (the values `v` unused, as in `openW`). -/
def viewW (rep : Rep K E) (Y : E) (roots : Array K) (c : DChal E) (_v : Vals E)
    (d r : ιW → YW → K) : L0View E ιW YW (Fin 224) K :=
  let p := pointWc c
  let tab := encTab rep.w roots Lw.logLane (slotsW c)
  memoL0 (Gadget.levelMap (Lw.toGadget okW) Lw.pos (Lw.claimW fun _ : Fin 1 => p) ![1, Y, Y ^ 2]
    (Gadget.powers 1 (lam₁ c)) (phi₁ c) (encOf tab Lw.logLane)
    ((Lw.toGadget okW).stackD d + (Lw.toGadget okW).stackR r))

theorem encOf_W (rep : Rep K E) (c : DChal E) :
    encOf (encTab rep.w (subRoots rep.w.v Lw.logLane) Lw.logLane (slotsW c)) Lw.logLane =
      novelEnc rep.w Lw.logLane (slotFn 20 224 (drawsW c)) :=
  encOf_eq rep.w Lw.logLane (slotsW c) (slotsOf_length _ _ _) _ fun _ => rfl

theorem viewW_eq (rep : Rep K E) (Y : E) (c : DChal E) (v : Vals E) (d r : ιW → YW → K) :
    viewW rep Y (subRoots rep.w.v Lw.logLane) c v d r = (openW rep Y).view lamV₁ phiV₁ (c, v) d r := by
  simp only [viewW, memoL0_eq, encOf_W, pointWc_eq]
  rfl

/-- **The quotient opening's level-0 view**, stored: the claims' points `pointQP pe Y c v`,
`pointSc Y` and the encoding computed once. -/
def viewQ (rep : Rep K E) (pe : PubEval E) (Y : E) (roots : Array K) (c : DChal E) (v : Vals E)
    (d r : ιQ → YQ → K) : L0View E ιQ YQ (Fin 225) K :=
  let p := pointQP pe Y c v
  let s := pointSc Y
  let tab := encTab rep.w roots Lq.logLane (slotsQ c)
  memoL0 (Gadget.levelMap (Lq.toGadget okQ) Lq.pos (Lq.claimW ![p, s]) ![1, Y, Y ^ 2]
    (Gadget.powers 2 (lam₂ c)) (phi₂ c) (encOf tab Lq.logLane)
    ((Lq.toGadget okQ).stackD d + (Lq.toGadget okQ).stackR r))

theorem encOf_Q (rep : Rep K E) (c : DChal E) :
    encOf (encTab rep.w (subRoots rep.w.v Lq.logLane) Lq.logLane (slotsQ c)) Lq.logLane =
      novelEnc rep.w Lq.logLane (slotFn 23 225 (drawsQ c)) :=
  encOf_eq rep.w Lq.logLane (slotsQ c) (slotsOf_length _ _ _) _ fun _ => rfl

theorem viewQ_eq (rep : Rep K E) (hm : pe.Matches P) (Y : E) (c : DChal E) (v : Vals E)
    (d r : ιQ → YQ → K) :
    viewQ rep pe Y (subRoots rep.w.v Lq.logLane) c v d r =
      (openQ rep P Y).view lamV₂ phiV₂ (c, v) d r := by
  simp only [viewQ, memoL0_eq, encOf_Q, pointQP_eq hm, pointQc_eq, pointSc_eq]
  rfl

end Views

/-! ## The joint view simulator and the renderer -/

section Sim

variable {K E : Type} [Field K] [DecidableEq K] [Field E] [Algebra K E] [DecidableEq E] [CharP E 2]
variable {pe : PubEval E} {P : Params E}

/-- **The joint view simulator, compiled** (`jointSimV` at the deployed openings and tables): the
five values (`simRed`), the two paddings, then each secret opening's level-0 view of the simulator's
table, the tables (`solW`, `solQ`) and the encodings computed once. -/
def jointSimVm [SampleableType K] [SampleableType E] [SampleableType (ιW → YW → K)]
    [SampleableType (ιQ → YQ → K)] (rep : Rep K E) (pe : PubEval E) (tgt : E → E) (Y : E)
    (inK : E → Bool) (sigmaAt : E → E) (c : DChal E) :
    ProbComp (Vals E × Unit × L0View E ιW YW (Fin 224) K × L0View E ιQ YQ (Fin 225) K) := do
  let v ← simRed (K := K) inK sigmaAt c.1.1.2
  let r₁ ← $ᵗ (ιW → YW → K)
  let r₂ ← $ᵗ (ιQ → YQ → K)
  return (v, (), viewW rep Y (subRoots rep.w.v Lw.logLane) c v (sparse (solW rep c v)) r₁,
    viewQ rep pe Y (subRoots rep.w.v Lq.logLane) c v (sparse (solQ rep pe tgt Y c v)) r₂)

/-- **`jointSimVm` is `jointSimV` at the deployed openings and tables.** -/
theorem jointSimVm_eq [SampleableType K] [SampleableType E] [SampleableType (ιW → YW → K)]
    [SampleableType (ιQ → YQ → K)] (rep : Rep K E) (hm : pe.Matches P) {tgt : E → E}
    {stmt : Fin P.words → E} (htgt : ∀ γ, tgt γ = P.target stmt γ) (Y : E) (inK : E → Bool)
    (sigmaAt : E → E) (c : DChal E) :
    jointSimVm rep pe tgt Y inK sigmaAt c =
      jointSimV inK sigmaAt (fun _ ↦ ()) (openW rep Y) (openQ rep P Y) (simTW rep Y)
        (simTQ rep P stmt Y) c := by
  simp only [jointSimVm, jointSimV, simulate, viewW_eq, viewQ_eq rep hm, sparse_solQ rep hm htgt]
  rfl

/-- **The claims' bytes** (`claimMsg`) on the evaluations. -/
def claimMsgP (rep : Rep K E) (pe : PubEval E) (tgt : E → E) (Y : E) (k : ℕ) (c : DChal E)
    (v : Vals E) : List Item :=
  if k = 5 then [.bytes (scalarsLE rep (pointWc c ++ [valWc c v]))]
  else if k = 128 then [.bytes (scalarsLE rep (modelWiringC c.1.1.2 v.2))]
  else if k = 242 then [.bytes (scalarsLE rep
    ((pointQP pe Y c v ++ [valsQP pe tgt Y c v 0]) ++ (pointSc Y ++ [valsQP pe tgt Y c v 1])))]
  else []

theorem claimMsgP_eq (rep : Rep K E) (hm : pe.Matches P) {tgt : E → E} {stmt : Fin P.words → E}
    (htgt : ∀ γ, tgt γ = P.target stmt γ) (Y : E) (k : ℕ) (c : DChal E) (v : Vals E) :
    claimMsgP rep pe tgt Y k c v = claimMsg rep P stmt Y k c v := by
  rw [claimMsgP, claimMsg, modelWitness_eq, modelQuotient_eq, modelSum_eq, pointQP_eq hm,
    valsQP_eq hm htgt, pointWc_eq, pointSc_eq, modelWiringC_eq]
  rfl

/-- `msgPub` on the evaluations. -/
def msgPubP (rep : Rep K E) (pe : PubEval E) (tgt : E → E) (Y : E) (R : Renderer K E) (k : ℕ)
    (h : List Out) (va : JV K E) : Msg :=
  claimMsgP rep pe tgt Y k (chOf rep.limbs h) va.1 ++ R k h va

/-- **The deployed prover's public renderer** (`out`) on the evaluations. -/
def outP (rep : Rep K E) (pe : PubEval E) (tgt : E → E) (Y : E) (R : Renderer K E)
    (σ : List Out) (v : JV K E) : QuotientZk.View Msg Inp Tbl Pos where
  msg c := msgPubP rep pe tgt Y R (min c σ.length) (σ.take c) (avail (min c σ.length) v)
  row k x := if PbOpened (E := E) rep σ k x then outRow rep σ v k x else default

theorem outP_eq [Fintype E] (rep : Rep K E) (hm : pe.Matches P) {tgt : E → E}
    {stmt : Fin P.words → E} (htgt : ∀ γ, tgt γ = P.target stmt γ) (Y : E) (R : Renderer K E)
    (gK : Fin 4 → K[X]) (van : K[X]) (TW : (Fin 4 → Fin 3 → K) → ιW → YW → K)
    (TQ : E × E × E → (Fin 4 → Fin 3 → K) → ιQ → YQ → K) (σ : List Out) (v : JV K E) :
    outP rep pe tgt Y R σ v = out rep P gK van stmt Y TW TQ R σ v := by
  simp only [outP, out, msgPubP, msgPub, claimMsgP_eq rep hm htgt]
  rfl

end Sim

end Compiled

end QuotientZk.Instance
