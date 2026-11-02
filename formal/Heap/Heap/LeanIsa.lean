-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Heap.Realize
import Lv42.Protocol.LeanIsa

/-!
# leanISA's heap

SPEC §5.2's heap for `leanIsaInstance F prog s` (`Lv42.Protocol`, leanVM 42422001's statement):

| block | leaves | leaf `k` pushes | leaf `k` pulls |
|---|---|---|---|
| memory | `2^logMem` | `(SEP_MEM, g^k, 1, m_k)` | `(SEP_MEM, g^k, MFCNT_k, m_k)` |
| bytecode | `2^logSize` | the seed, count `1` | the finalize, count `BFCNT_k` |
| opcode table `j` | `2^τ_j` | executed row `k`'s push flushes | its pull flushes |
| unused | any | nothing | nothing |

and at the root the state boundary, pushing `(SEP_STATE, 1, 1)` (`init`) and pulling
`(SEP_STATE, g^(2^logSize - 1), 1)` (`fin`). These are Lv42's six boundary blocks
(`LeanIsa.boundary`, `bd 0 … bd 5`) and the opcode tables' flushes; the memory, bytecode and Flock
column groups (tables `0, 1, 2`) flush nothing.

**`realizes`**: a heap whose blocks are these, in any order, with blocks of no tuple among them,
realizes the bus of every stack `q` (`Heap.Realizes`). So, with `Heap.prob_sat_not_balanced`,
**`prob_sat_not_balanced`**: a well-formed such heap holds at a uniform `(α, β)` while `q` is not
balanced with probability at most `busError N`. The order and the alignment of the blocks do not
matter to the products; they matter to the restriction through which the verifier reads each
block (`Heap.AlignedFrom`, `Heap.omega_add_of_dvd`).
-/

namespace Heap.LeanIsa

open LeanVM.Parameters Lv42.Protocol Lv42.Protocol.LeanIsa OracleComp
open scoped ENNReal

variable (F : FlockSpec) (prog : Lv42.Semantics.Program) (s : Sizes)

theorem length_boundary : (LeanIsa.boundary prog s).length = 6 := rfl

/-- Boundary block `k` of leanISA (`layout.rs:348-394`): the state push, the memory seed, the
bytecode seed, the state pull, the memory finalize, the bytecode finalize. -/
def bd (k : Fin 6) : BoundaryBlock (shape prog s) :=
  (LeanIsa.boundary prog s)[k.val]'(by rw [length_boundary]; exact k.isLt)

theorem boundary_push :
    ((leanIsaInstance F prog s).boundary.filter fun b ↦ decide (b.side = Side.push)) =
      [bd prog s 0, bd prog s 1, bd prog s 2] := rfl

theorem boundary_pull :
    ((leanIsaInstance F prog s).boundary.filter fun b ↦ decide (b.side = Side.pull)) =
      [bd prog s 3, bd prog s 4, bd prog s 5] := rfl

variable (q : LeanVM.Protocol.Column (leanIsaInstance F prog s).μ)

/-- **The named blocks of SPEC §5.2**: the memory (cell `k`'s leaf `D_init/D_fin`), the bytecode
(instruction `k`'s), and the six opcode tables. -/
def namedBlocks : List (LeafBlock (Vector K 16)) :=
  pairBlock (leanIsaInstance F prog s) q (bd prog s 1) (bd prog s 4) ::
    pairBlock (leanIsaInstance F prog s) q (bd prog s 2) (bd prog s 5) ::
      (List.finRange 6).map fun j ↦ tableBlock (leanIsaInstance F prog s) q (opIdx j)

/-- The state boundary's push `(SEP_STATE, 1, 1)`, at the root. -/
def init : Vector K 16 := boundaryRow (leanIsaInstance F prog s) q (bd prog s 0) 0

/-- The state boundary's pull `(SEP_STATE, g^(2^logSize - 1), 1)`, at the root. -/
def fin : Vector K 16 := boundaryRow (leanIsaInstance F prog s) q (bd prog s 3) 0

/-- **A heap of SPEC §5.2's shape**: depth `n`, the blocks `bs`, the state boundary at the root. -/
def heapData (n : ℕ) (bs : List (LeafBlock (Vector K 16))) : HeapData :=
  ⟨n, bs, init F prog s q, fin F prog s q⟩

/-- The blocks are the named ones, in some order, with blocks of no tuple among them. -/
def Shaped (bs : List (LeafBlock (Vector K 16))) : Prop :=
  ∃ us : List (LeafBlock (Vector K 16)),
    bs.Perm (namedBlocks F prog s q ++ us) ∧ ∀ u ∈ us, u.pushes = [] ∧ u.pulls = []

theorem flatMap_filter_of_nil {α β : Type*} (p : α → Bool) (g : α → List β) :
    ∀ l : List α, (∀ a ∈ l, p a = false → g a = []) → (l.filter p).flatMap g = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    have ih := flatMap_filter_of_nil p g l fun b hb ↦ h b (List.mem_cons_of_mem _ hb)
    by_cases hp : p a = true
    · rw [List.filter_cons_of_pos hp, List.flatMap_cons, List.flatMap_cons, ih]
    · rw [List.filter_cons_of_neg hp, List.flatMap_cons, h a (List.mem_cons_self ..)
        (by simpa using hp), List.nil_append, ih]

/-- The opcode tables are tables `3 … 8`. -/
theorem finRange_filter : (List.finRange 9).filter (fun j ↦ decide (3 ≤ j.val)) =
    (List.finRange 6).map opIdx := by decide

/-- The column groups flush nothing. -/
theorem tableTuples_nil (side : Side) (j : Fin 9) (hj : decide (3 ≤ j.val) = false) :
    tableTuples (leanIsaInstance F prog s) q j side = [] := by
  obtain ⟨_ | _ | _ | k, hk⟩ := j
  · rfl
  · rfl
  · rfl
  · simp at hj

/-- `flushTuples` is the opcode tables'. -/
theorem flushTuples_eq_opcode (side : Side) :
    (leanIsaInstance F prog s).flushTuples q side =
      (List.finRange 6).flatMap fun j ↦
        tableTuples (leanIsaInstance F prog s) q (opIdx j) side := by
  rw [flushTuples_eq]
  show (List.finRange 9).flatMap
    (fun j : Fin 9 ↦ tableTuples (leanIsaInstance F prog s) q j side) = _
  rw [← flatMap_filter_of_nil (fun j : Fin 9 ↦ decide (3 ≤ j.val)) _ _
    fun j _ hj ↦ tableTuples_nil F prog s q side j hj]
  exact (congrArg (fun l ↦ List.flatMap _ l) (finRange_filter)).trans (List.flatMap_map ..)

theorem allPush_of_shaped {bs : List (LeafBlock (Vector K 16))} (h : Shaped F prog s q bs) :
    (allPush bs).Perm (allPush (namedBlocks F prog s q)) := by
  obtain ⟨us, hperm, hus⟩ := h
  refine (hperm.flatMap_right _).trans ?_
  rw [List.flatMap_append, List.flatMap_eq_nil_iff.mpr fun u hu ↦ (hus u hu).1, List.append_nil]
  rfl

theorem allPull_of_shaped {bs : List (LeafBlock (Vector K 16))} (h : Shaped F prog s q bs) :
    (allPull bs).Perm (allPull (namedBlocks F prog s q)) := by
  obtain ⟨us, hperm, hus⟩ := h
  refine (hperm.flatMap_right _).trans ?_
  rw [List.flatMap_append, List.flatMap_eq_nil_iff.mpr fun u hu ↦ (hus u hu).2, List.append_nil]
  rfl

/-- **SPEC §5.2's heap realizes leanISA's bus**: for every stack `q`, a heap whose blocks are the
named ones in any order, with blocks of no tuple among them, and the state boundary at the root,
has the push tuples of `q` and its pull tuples. -/
theorem realizes (n : ℕ) {bs : List (LeafBlock (Vector K 16))} (h : Shaped F prog s q bs) :
    Realizes q (heapData F prog s q n bs) := by
  have hpushT : ((List.finRange 6).flatMap fun j ↦
      (tableBlock (leanIsaInstance F prog s) q (opIdx j)).pushes).Perm
      ((List.finRange 6).flatMap fun j ↦
        tableTuples (leanIsaInstance F prog s) q (opIdx j) .push) :=
    List.Perm.flatMap_left _ fun j _ ↦ pushes_tableBlock_perm _ q (opIdx j)
  have hpullT : ((List.finRange 6).flatMap fun j ↦
      (tableBlock (leanIsaInstance F prog s) q (opIdx j)).pulls).Perm
      ((List.finRange 6).flatMap fun j ↦
        tableTuples (leanIsaInstance F prog s) q (opIdx j) .pull) :=
    List.Perm.flatMap_left _ fun j _ ↦ pulls_tableBlock_perm _ q (opIdx j)
  constructor
  · refine ((allPush_of_shaped F prog s q h).append_right _).trans ?_
    rw [M3Instance.tuples, flushTuples_eq_opcode, boundaryTuples_eq, boundary_push]
    rw [← Multiset.coe_eq_coe] at hpushT ⊢
    simp only [allPush, namedBlocks, List.flatMap_cons, List.flatMap_map, List.flatMap_nil,
      pushes_pairBlock, boundaryRows_of_kappa_zero _ q (bd prog s 0) rfl, List.append_nil,
      heapData, init, ← Multiset.coe_add] at hpushT ⊢
    rw [hpushT]
    abel
  · refine ((allPull_of_shaped F prog s q h).append_right _).trans ?_
    rw [M3Instance.tuples, flushTuples_eq_opcode, boundaryTuples_eq, boundary_pull]
    rw [← Multiset.coe_eq_coe] at hpullT ⊢
    simp only [allPull, namedBlocks, List.flatMap_cons, List.flatMap_map, List.flatMap_nil,
      pulls_pairBlock _ q (bd prog s 1) (bd prog s 4) rfl,
      pulls_pairBlock _ q (bd prog s 2) (bd prog s 5) rfl,
      boundaryRows_of_kappa_zero _ q (bd prog s 3) rfl, List.append_nil,
      heapData, fin, ← Multiset.coe_add] at hpullT ⊢
    rw [hpullT]
    abel

/-- **leanISA's bus is sound on SPEC §5.2's heap.** For every stack `q` and every well-formed heap
of SPEC §5.2's shape, a uniform `(α, β)` makes the heap hold while `q` is not balanced with
probability at most `busError N = 4·N/|E|`, `N` bounding both sides' tuple counts. -/
theorem prob_sat_not_balanced (n : ℕ) {bs : List (LeafBlock (Vector K 16))}
    (h : Shaped F prog s q bs) (hD : (heapData F prog s q n bs).WellFormed) {N : ℕ}
    (hpush : busCount (leanIsaInstance F prog s) .push ≤ N)
    (hpull : busCount (leanIsaInstance F prog s) .pull ≤ N) :
    Pr{let ab ← $ᵗ ((Fin 4 → E) × E)}[(heapData F prog s q n bs).Sat ab.1 ab.2 ∧
        ¬ (leanIsaInstance F prog s).Balanced q] ≤ busError N :=
  Heap.prob_sat_not_balanced hD (realizes F prog s q n h) hpush hpull

end Heap.LeanIsa
