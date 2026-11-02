-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0), through `Completeness.Opening`.
import Completeness.Read
import Completeness.Opening

/-!
# An opening, and the wiring table's

`OpeningSystem`: what the end theorem needs of one row of `verify_openings` (a table's layout,
committed and opened with leanVM's WHIR): the honest stack of a table (`stack`, for any padding),
its root, the honest opening, `opening::verify`, and **completeness**: a table vanishing off the
entries the layout holds (`Held`) whose claims are true (`tableEvalN`) has its honest opening
accepted at its honest root, whenever the honest prover returns one (it fails only at a proof of
work, `exists_failed_pow`).

`wiringOpening` is the **wiring** table's, proven: the public layout `wiring_layout(22)`
(`Layout::new`, unchanged by the hidden layouts' redesign), the stack its `64` blocks (`fillPublic`,
`Table::new`), read back whole (`wiring_table_fillPublic`), the claims' meaning
(`WhirBridge.Layout.holds_iff`), and mumbai's completeness of the WHIR opening
(`openingVerify_honest`, `Opening.lean`).
-/

set_option linter.unusedSectionVars false

open Finset
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.EndToEnd LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile LeanVM.Semantics

namespace Completeness

/-- **One opening of `verify_openings`**: a layout's honest stack, root, prover and verifier, and
its completeness. -/
structure OpeningSystem where
  /-- The table's variables. -/
  vars : ℕ
  /-- The stack's. -/
  logN : ℕ
  /-- The table's entries the layout holds. -/
  Held : ℕ → Prop
  /-- The honest stack of a table, with its padding (`Table::new`, `Table::hidden`). -/
  stack : (ℕ → K) → (ℕ → ℕ → K) → Column logN
  /-- Its root (`opening::commit`). -/
  root : (Bytes → Digest) → Column logN → Digest
  /-- The honest opening (`opening::open`), `none` if a proof of work found no nonce. -/
  prove : (Bytes → Digest) → (KeccakState → KeccakState) → Column logN → List WhirBridge.Claim →
    ℕ → Option Proof
  /-- `opening::verify`. -/
  verify : (Bytes → Digest) → (KeccakState → KeccakState) → Digest → List WhirBridge.Claim →
    Proof → Bool
  /-- **Completeness**: true claims on a table the layout holds open. -/
  complete : ∀ (H : Bytes → Digest) (F : KeccakState → KeccakState) (T : ℕ → K)
    (pad : ℕ → ℕ → K) (cs : List WhirBridge.Claim) (fuel : ℕ) (π : Proof),
    (∀ t, ¬ Held t → T t = 0) →
    (∀ c ∈ cs, c.point.length = vars ∧ tableEvalN vars T c.point = c.value) →
    prove H F (stack T pad) cs fuel = some π → verify H F (root H (stack T pad)) cs π = true

/-! ## The wiring table's opening -/

/-- `wiring_layout(LOG_ROWS)`. -/
abbrev wL : WhirBridge.Layout := WhirBridge.wiringLayout WhirBridge.logRows

theorem wL_shape : wL.logN = 24 ∧ wL.vars = 24 ∧ wL.logLane = 18 ∧
    wL.lanes = (List.range 64).map WhirBridge.Lane.block ∧ wL.logPiece = none := by
  decide +kernel

/-- **`Table::new`**: a public layout's stack, lane `l` holding its block. -/
def fillPublic (L : WhirBridge.Layout) (T : ℕ → K) : Column L.logN :=
  ⟨Vector.ofFn fun x ↦
    if x.val / 2 ^ L.logLane < L.lanes.length then
      T ((L.lanes.getD (x.val / 2 ^ L.logLane) .random).blockD * 2 ^ L.logLane +
        x.val % 2 ^ L.logLane)
    else 0⟩

/-- **The wiring table is read back whole** from its stack. -/
theorem wiring_table_fillPublic (T : ℕ → K) {t : ℕ} (ht : t < 2 ^ 24) :
    wL.table (fillPublic wL T) t = T t := by
  obtain ⟨hN, hV, hl, hlanes, hp⟩ := wL_shape
  unfold WhirBridge.Layout.table
  rw [hp]
  dsimp only
  unfold WhirBridge.Blocks.table
  have hblocks : wL.toBlocks.blocks = List.range 64 := by
    show wL.lanes.map WhirBridge.Lane.blockD = _
    rw [hlanes, List.map_map]
    exact List.map_id'' (fun _ ↦ rfl) _
  have hlen : wL.toBlocks.lanes = 64 := by
    show wL.toBlocks.blocks.length = 64
    rw [hblocks, List.length_range]
  have hll : wL.toBlocks.logLane = 18 := hl
  rw [hlen, hll, hblocks]
  have hdiv : t / 2 ^ 18 < 64 := by omega
  rw [Finset.sum_eq_single (t / 2 ^ 18)]
  · rw [List.getD_eq_getElem _ _ (by simpa using hdiv), List.getElem_range, if_pos rfl]
    have hx : t % 2 ^ 18 + 2 ^ 18 * (t / 2 ^ 18) < 2 ^ wL.logN := by
      rw [hN]; omega
    unfold fillPublic
    dsimp only
    erw [getD_ofFn _ hx]
    dsimp only
    rw [hl, hlanes]
    have h1 : (t % 2 ^ 18 + 2 ^ 18 * (t / 2 ^ 18)) / 2 ^ 18 = t / 2 ^ 18 := by omega
    have h2 : (t % 2 ^ 18 + 2 ^ 18 * (t / 2 ^ 18)) % 2 ^ 18 = t % 2 ^ 18 := by omega
    rw [h1, h2, if_pos (by simpa using hdiv)]
    rw [List.getD_eq_getElem _ _ (by simpa using hdiv), List.getElem_map, List.getElem_range]
    show T (t / 2 ^ 18 * 2 ^ 18 + t % 2 ^ 18) = T t
    congr 1
    omega
  · intro l hl' hne
    rw [List.getD_eq_getElem _ _ (by simpa using hl'), List.getElem_range, if_neg hne]
  · intro h
    exact absurd (Finset.mem_range.mpr hdiv) h

/-- The claims on the wiring table, as the openings evaluate them, are `tableEvalN`'s. -/
theorem wiring_tableEval (T : ℕ → K) (p : List E) :
    wL.tableEval (fillPublic wL T) p = tableEvalN 24 T p := by
  unfold WhirBridge.Layout.tableEval tableEvalN
  rw [wL_shape.2.1]
  exact Finset.sum_congr rfl fun t ht ↦ by
    rw [wiring_table_fillPublic T (Finset.mem_range.mp ht)]

/-- **The wiring table's opening**, proven: the public layout, its stack `fillPublic`, mumbai's
honest prover and root, `opening::verify`; complete by `openingVerify_honest`. -/
noncomputable def wiringOpening : OpeningSystem where
  vars := 24
  logN := wL.logN
  Held t := t < 2 ^ 24
  stack T _ := fillPublic wL T
  root H q := honestRoot H wL.stacking WhirBridge.logInvRate q
  prove H F q cs fuel := honestOpen H F wL.stacking WhirBridge.logInvRate
    (WhirBridge.openingPrefix wL WhirBridge.logInvRate) q cs fuel
  verify H F r cs π := WhirBridge.openingVerifyWithHash (m := Id) H F wL WhirBridge.logInvRate r cs π
  complete H F T pad cs fuel π _ hcs hπ := by
    have hok := WhirBridge.layouts_ok WhirBridge.logRows (by decide) (by decide)
    have hw : Whir.Admissible wL.logN WhirBridge.logInvRate := hok.2.1
    have hval := (WhirBridge.layouts_valid WhirBridge.logRows (by decide) (by decide)).2.1
    refine openingVerify_honest H F wL hw (fillPublic wL T) cs
      (fun c hc ↦ by rw [wL_shape.2.1]; exact (hcs c hc).1) (fun c hc ↦ ?_) fuel hπ
    rw [wL.holds_iff hval c (by rw [wL_shape.2.1]; exact (hcs c hc).1), wiring_tableEval]
    exact (hcs c hc).2

end Completeness
