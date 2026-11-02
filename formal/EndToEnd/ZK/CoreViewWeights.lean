-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The WHIR prover's `powers`, `powersFrom`, `dot`, `eqKernelA` are leanerVM's (branch `mumbai`,
-- commit 6175f1a0, MIT OR Apache-2.0: `Statement/LeanVmVerifier.lean`, `Statement/Prover/Whir.lean`).
import ZK.CoreViewArrays
import E2ECompleteness.ProverOpening

/-!
# The statement's weight table is the joint model's combined weight

The statement's WHIR opening batches its claims and the gadget into one weight table
(`weightTable L scales claims`, `Statement/PcsQuotient/Prover.lean`: entry `i` is entry `i / 64` of
lane `i mod 64`, each claim weighing `Layout.weightAt`, the gadget `Layout.gadgetAt`, the scales
mumbai's `powers λ`); the joint model batches the claims' weights `Layout.claimW` and the gadget's
`gadgetW pos β` (`β = 1, Y, Y²`) by `Gadget.powers m λ` (`HiddenLayout.combinedW`). Here:

* `SameLayout`: the statement's layout and the model's have the same stack, piece, lanes and held
  pieces, decided for the deployed ones (`sameLayout_W`, `sameLayout_Q`, `decide +kernel` on the
  lists of `40`/`63` lanes and `33`/`167` pieces);
* `eqBits_SD`: the statement's `eq_bits` (a fold over the point) is the model's (a product);
  `eqKernel_D`: an entry of mumbai's equality kernel is the model's `eq_bits`;
* **`weightAt_eq_role`**: a claim's statement weight at lane `l`, entry `y` is `eq_bits` of the table
  entry the stack entry holds (`LayoutClaims.role`), or zero, which is the model's `claimW`
  (`LayoutClaims.claimW_eq`);
* **`gadgetAt_eq`**, **`gadgetW_eq_stmt`**: the gadget's statement weight and the model's are
  `β_i` at entry `247 + 3 g + i` of the lanes of pattern `g`, zero elsewhere;
* `dot_powers`, `powers_getD`: the scales are `λ^c`, the gadget's `λ^m`;
* **`weight_rep`**: the weight table represents (`ArrRep`) the model's combined weight.
-/

open Finset QuotientSecurity.Hiding
open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Prover
open QuotientZk.Joint QuotientZk.Instance
open Primitives

namespace PcsQuotient.EndToEnd.Core

attribute [local instance high] Primitives.instFintypeF64 Primitives.instSampleableTypeF64
  Primitives.instSampleableTypeF192

set_option linter.unusedSectionVars false

/-! ## The layouts -/

/-- A statement lane as the model's. -/
def laneD : PcsQuotient.Lane → QuotientSecurity.Hiding.Deployed.Lane
  | .block b => .block b
  | .overflow => .overflow
  | .random => .random

/-- **The statement's layout is the model's**: the same stack size, piece, lanes and held pieces. -/
def SameLayout (SL : PcsQuotient.Layout) (L : QuotientSecurity.Hiding.Deployed.Layout) : Prop :=
  SL.logN = L.logN ∧ SL.logPiece = some L.logPiece ∧ SL.lanes.map laneD = L.lanes ∧
    SL.pieces = L.pieces

instance (SL : PcsQuotient.Layout) (L : QuotientSecurity.Hiding.Deployed.Layout) :
    Decidable (SameLayout SL L) := by
  unfold SameLayout
  infer_instance

/-- The deployed witness layouts agree. -/
theorem sameLayout_W : SameLayout (PcsQuotient.witnessLayout logRows) Lw := by decide +kernel

/-- The deployed quotient layouts agree. -/
theorem sameLayout_Q : SameLayout (PcsQuotient.quotientLayout logRows) Lq := by decide +kernel

/-! ## `eq_bits` -/

theorem foldl_zipIdx_prod (g : E → E × ℕ → E) (h : E → ℕ → E)
    (hg : ∀ w q k, g w (q, k) = w * h q k) : ∀ (p : List E) (n : ℕ) (a : E),
      (p.zipIdx n).foldl g a = a * ∏ k ∈ range p.length, h (p.getD k 0) (n + k)
  | [], n, a => by simp
  | x :: xs, n, a => by
    rw [List.zipIdx_cons, List.foldl_cons, hg, foldl_zipIdx_prod g h hg xs (n + 1),
      List.length_cons, prod_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    have hp : ∏ k ∈ range xs.length, h (xs.getD k 0) (n + 1 + k) =
        ∏ k ∈ range xs.length, h (xs.getD k 0) (n + (k + 1)) :=
      prod_congr rfl fun k _ => by rw [show n + 1 + k = n + (k + 1) by ring]
    rw [hp]
    ring

/-- **The statement's `eq_bits` is the model's.** -/
theorem eqBits_SD (p : List E) (i : ℕ) :
    PcsQuotient.eqBits p i = QuotientSecurity.Hiding.Deployed.eqBits p i := by
  unfold PcsQuotient.eqBits QuotientSecurity.Hiding.Deployed.eqBits
  rw [foldl_zipIdx_prod _ (fun q k => if i.testBit k then q else 1 + q) (fun w q k => rfl) p 0 1]
  simp

/-- An entry of mumbai's equality kernel of the point's first `n` coordinates is the model's
`eq_bits`. -/
theorem eqKernel_D (p : List E) {n y : ℕ} (hn : n ≤ p.length) (hy : y < 2 ^ n) :
    (eqKernelA (p.take n)).getD y 0 = QuotientSecurity.Hiding.Deployed.eqBits (p.take n) y := by
  rw [E2ECompleteness.eqKernelA_getD_take p hn hy]
  have hl : (p.take n).length = n := by simp [hn]
  have h := WhirBridge.eqBits_eq_boolPoint (p.take n) y
  rw [hl] at h
  rw [← h, ← E2ECompleteness.OpeningTr.eqBits_eq, eqBits_SD]

/-! ## A claim's weight -/

/-- **A claim's statement weight at lane `l`, entry `y`** is `eq_bits` of the table entry the stack
entry holds, or zero (the model's `claimW`, `LayoutClaims.claimW_eq`). -/
theorem weightAt_eq_role {SL : PcsQuotient.Layout} {L : QuotientSecurity.Hiding.Deployed.Layout}
    (hS : SameLayout SL L) (h : L.OK) (cl : PcsQuotient.Claim) (hlen : L.logLane ≤ cl.point.length)
    (l : ℕ) {y : ℕ} (hy : y < 2 ^ L.logLane) :
    SL.weightAt (SL.claimWeights cl) l y = match LayoutClaims.role L l y with
      | some i => QuotientSecurity.Hiding.Deployed.eqBits cl.point i
      | none => 0 := by
  obtain ⟨hN, hP, hLanes, hPieces⟩ := hS
  have hs : L.logPiece = 8 := h.piece
  have hℓ : SL.logLane = L.logLane := by
    simp only [PcsQuotient.Layout.logLane, QuotientSecurity.Hiding.Deployed.Layout.logLane, hN,
      PcsQuotient.laneFold, QuotientSecurity.Hiding.Deployed.laneFold]
  have hℓ8 : 8 < L.logLane := h.lane
  have hP8 : SL.logPiece = some 8 := by rw [hP, hs]
  have hlanes : L.lanes[l]? = SL.lanes[l]?.map laneD := by rw [← hLanes, List.getElem?_map]
  have hkind : SL.lanes.toArray.getD l .random = SL.lanes.getD l .random :=
    E2ECompleteness.toArray_getD' _ _ _
  have hlow : (SL.scales cl.point).1.toArray.getD l 0 = (SL.scales cl.point).1.getD l 0 :=
    E2ECompleteness.toArray_getD' _ _ _
  have hy8 : y % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (by norm_num)
  simp only [PcsQuotient.Layout.weightAt, PcsQuotient.Layout.claimWeights, hP8, hkind, hlow,
    Nat.shiftRight_eq_div_pow, Option.getD_some]
  unfold LayoutClaims.role
  rw [hlanes, hs]
  rcases hSl : SL.lanes[l]? with _ | (b | _ | _)
  · have hd : SL.lanes.getD l .random = .random := by
      rw [List.getD_eq_getElem?_getD, hSl]
      rfl
    rw [hd]
    simp only [Option.map_none, ite_self]
  · -- a block lane
    have hd : SL.lanes.getD l .random = .block b := by
      rw [List.getD_eq_getElem?_getD, hSl]
      rfl
    rw [hd]
    simp only [Option.map_some, laneD]
    by_cases h0 : y / 2 ^ 8 = 0
    · rw [ite_eq_left h0, ite_eq_left h0]
    · simp only [h0, ite_false]
      rw [E2ECompleteness.scales_fst_getD, hSl]
      dsimp only
      rw [hℓ, eqBits_SD, eqKernel_D cl.point hlen hy, Nat.shiftLeft_eq,
        LayoutClaims.eqBits_entry cl.point hy]
      ring
  · -- the overflow lane
    have hd : SL.lanes.getD l .random = .overflow := by
      rw [List.getD_eq_getElem?_getD, hSl]
      rfl
    rw [hd]
    simp only [Option.map_some, laneD]
    rw [E2ECompleteness.toArray_getD', E2ECompleteness.scales_snd SL hP8 cl.point]
    by_cases h0 : y / 2 ^ 8 = 0
    · rw [ite_eq_left h0,
        ite_eq_right (by omega : ¬ (1 ≤ y / 2 ^ 8 ∧ y / 2 ^ 8 ≤ L.pieces.length))]
    · by_cases hk : y / 2 ^ 8 ≤ L.pieces.length
      · have hc : 1 ≤ y / 2 ^ 8 ∧ y / 2 ^ 8 ≤ L.pieces.length := ⟨by omega, hk⟩
        simp only [h0, hc, ite_false, ite_true, and_self]
        have hlt : y / 2 ^ 8 - 1 < L.pieces.length := by omega
        rw [List.getD_eq_getElem _ _ (by rw [List.length_map, hPieces]; exact hlt),
          List.getD_eq_getElem _ _ hlt, List.getElem_map]
        simp only [hPieces]
        rw [eqBits_SD, eqKernel_D cl.point (by omega) hy8,
          LayoutClaims.eqBits_entry cl.point hy8]
        ring
      · have hc : ¬ (1 ≤ y / 2 ^ 8 ∧ y / 2 ^ 8 ≤ L.pieces.length) := fun hc => hk hc.2
        simp only [h0, hc, ite_false]
        rw [List.getD_eq_default _ _ (by rw [List.length_map, hPieces]; omega), zero_mul]
  · -- a random lane
    have hd : SL.lanes.getD l .random = .random := by
      rw [List.getD_eq_getElem?_getD, hSl]
      rfl
    rw [hd]
    simp only [Option.map_some, laneD, ite_self]

/-- Past the last lane, the stack entry holds nothing. -/
theorem role_of_ge {L : QuotientSecurity.Hiding.Deployed.Layout} {l : ℕ} (hl : L.lanes.length ≤ l)
    (y : ℕ) : LayoutClaims.role L l y = none := by
  unfold LayoutClaims.role
  rw [List.getElem?_eq_none hl]

/-! ## The gadget -/

theorem gadgetLanes_SD (n : ℕ) :
    PcsQuotient.gadgetLanes n = QuotientSecurity.Hiding.Deployed.gadgetLanes n := by
  rcases n with _ | _ | n <;> rfl

theorem le_of_mem_gadgetLanes {n l : ℕ} (h : l ∈ QuotientSecurity.Hiding.Deployed.gadgetLanes n) :
    l ≤ 32 := by
  rcases n with _ | _ | n <;>
    simp [QuotientSecurity.Hiding.Deployed.gadgetLanes,
      QuotientSecurity.Hiding.Deployed.overflowLane] at h <;> omega

/-- **The gadget's statement weight**: `β_i` at entry `247 + 3 g + i` of the lanes of pattern `g`. -/
theorem gadgetAt_eq {SL : PcsQuotient.Layout} {L : QuotientSecurity.Hiding.Deployed.Layout}
    (hS : SameLayout SL L) (h : L.OK) (l y : ℕ) :
    SL.gadgetAt l y = if 247 ≤ y ∧ y < 256 ∧
        l ∈ QuotientSecurity.Hiding.Deployed.gadgetLanes ((y - 247) / 3)
      then PcsQuotient.gadgetBeta ((y - 247) % 3) else 0 := by
  have hs : L.logPiece = 8 := h.piece
  have hP8 : SL.logPiece = some 8 := by rw [hS.2.1, hs]
  have e1 : y + PcsQuotient.gadgetSize - 2 ^ 8 = y - 247 := by
    simp only [PcsQuotient.gadgetSize]
    omega
  have e2 : (2 : ℕ) ^ 8 - PcsQuotient.gadgetSize = 247 := by
    simp only [PcsQuotient.gadgetSize]
    norm_num
  simp only [PcsQuotient.Layout.gadgetAt, hP8, e1, e2, gadgetLanes_SD, List.contains_iff_mem]
  norm_num

/-- The pattern's lanes, as a sum of indicators. -/
theorem sum_map_ind (n l : ℕ) :
    ((QuotientSecurity.Hiding.Deployed.gadgetLanes n).map fun l' => if l = l' then (1 : E) else 0).sum =
      if l ∈ QuotientSecurity.Hiding.Deployed.gadgetLanes n then 1 else 0 := by
  rcases n with _ | _ | n
  · simp only [QuotientSecurity.Hiding.Deployed.gadgetLanes, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, List.mem_cons, List.not_mem_nil, or_false]
    by_cases h0 : l = 0
    · subst h0
      simp
    · by_cases h31 : l = 31
      · subst h31
        simp
      · simp [h0, h31]
  · simp only [QuotientSecurity.Hiding.Deployed.gadgetLanes, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, List.mem_cons, List.not_mem_nil, or_false]
    by_cases h0 : l = 1
    · subst h0
      simp
    · by_cases h31 : l = 30
      · subst h31
        simp
      · simp [h0, h31]
  · simp only [QuotientSecurity.Hiding.Deployed.gadgetLanes, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, List.mem_cons, List.not_mem_nil, or_false]

/-- **The gadget's model weight** (`gadgetW`): `β_i` at entry `247 + 3 g + i` of the lanes of
pattern `g`. -/
theorem gadgetW_eq {L : QuotientSecurity.Hiding.Deployed.Layout} (h : L.OK) (β : Fin 3 → E)
    (l : Fin L.lanes.length) (y : Fin (2 ^ L.logLane)) :
    (L.toGadget h).gadgetW L.pos β l y =
      if hr : 247 ≤ (y : ℕ) ∧ (y : ℕ) < 256 then
        (if (l : ℕ) ∈ QuotientSecurity.Hiding.Deployed.gadgetLanes (((y : ℕ) - 247) / 3)
          then β ⟨((y : ℕ) - 247) % 3, Nat.mod_lt _ (by norm_num)⟩ else 0)
      else 0 := by
  have hg : ∀ p i : Fin 3, ((L.toGadget h).gent p i = y ↔ 247 + 3 * (p : ℕ) + i = (y : ℕ)) := by
    intro p i
    simp only [QuotientSecurity.Hiding.Deployed.Layout.toGadget, Fin.ext_iff,
      QuotientSecurity.Hiding.Deployed.gadgetEntry, QuotientSecurity.Hiding.Deployed.logPieceD,
      QuotientSecurity.Hiding.Deployed.gadgetD]
    norm_num
  unfold GadgetLayout.gadgetW
  by_cases hr : 247 ≤ (y : ℕ) ∧ (y : ℕ) < 256
  · rw [dite_eq_left hr]
    have hp0 : ((y : ℕ) - 247) / 3 < 3 := by omega
    have hi0 : ((y : ℕ) - 247) % 3 < 3 := Nat.mod_lt _ (by norm_num)
    rw [sum_eq_single (⟨((y : ℕ) - 247) / 3, hp0⟩ : Fin 3),
      sum_eq_single (⟨((y : ℕ) - 247) % 3, hi0⟩ : Fin 3),
      ite_eq_left ((hg _ _).mpr (by simp only; omega)),
      QuotientSecurity.Hiding.Deployed.Layout.patE_pos h, sum_map_ind]
    · split_ifs <;> ring
    · intro i _ hi
      rw [ite_eq_right]
      rw [hg]
      intro he
      apply hi
      ext
      simp only
      omega
    · simp
    · intro p _ hp
      refine sum_eq_zero fun i _ => ?_
      rw [ite_eq_right]
      rw [hg]
      intro he
      apply hp
      ext
      simp only
      omega
    · simp
  · rw [dite_eq_right hr]
    refine sum_eq_zero fun p _ => sum_eq_zero fun i _ => ?_
    rw [ite_eq_right]
    rw [hg]
    have := p.isLt
    have := i.isLt
    omega

/-- The gadget's coefficients `1, Y, Y²` are the statement's `gadget_beta`. -/
theorem beta_eq (i : ℕ) (hi : i < 3) :
    (![1, F192.Y, F192.Y ^ 2] : Fin 3 → E) ⟨i, hi⟩ = PcsQuotient.gadgetBeta i := by
  interval_cases i
  · show (1 : E) = _
    rw [show PcsQuotient.gadgetBeta 0 = F192.ofLimbs 1 0 0 from rfl, F192.ofLimbs_eq]
    simp
  · show F192.Y = _
    rw [show PcsQuotient.gadgetBeta 1 = F192.ofLimbs 0 1 0 from rfl, F192.ofLimbs_eq]
    simp
  · show F192.Y ^ 2 = _
    rw [show PcsQuotient.gadgetBeta 2 = F192.ofLimbs 0 0 1 from rfl, F192.ofLimbs_eq]
    simp

/-- **The gadget's model weight is the statement's**, at `β = 1, Y, Y²`. -/
theorem gadgetW_eq_stmt {L : QuotientSecurity.Hiding.Deployed.Layout} (h : L.OK)
    (l : Fin L.lanes.length) (y : Fin (2 ^ L.logLane)) :
    (L.toGadget h).gadgetW L.pos ![1, F192.Y, F192.Y ^ 2] l y =
      if 247 ≤ (y : ℕ) ∧ (y : ℕ) < 256 ∧
          (l : ℕ) ∈ QuotientSecurity.Hiding.Deployed.gadgetLanes (((y : ℕ) - 247) / 3)
        then PcsQuotient.gadgetBeta (((y : ℕ) - 247) % 3) else 0 := by
  rw [gadgetW_eq h]
  by_cases hr : 247 ≤ (y : ℕ) ∧ (y : ℕ) < 256
  · rw [dite_eq_left hr]
    by_cases hl : (l : ℕ) ∈ QuotientSecurity.Hiding.Deployed.gadgetLanes (((y : ℕ) - 247) / 3)
    · rw [ite_eq_left hl, ite_eq_left ⟨hr.1, hr.2, hl⟩, beta_eq]
    · rw [ite_eq_right hl, ite_eq_right (fun hc => hl hc.2.2)]
  · rw [dite_eq_right hr, ite_eq_right (fun hc => hr ⟨hc.1, hc.2.1⟩)]

/-! ## The scales -/

theorem powersFrom_eq (base : E) : ∀ (n : ℕ) (acc : E),
    powersFrom acc base n = List.ofFn fun k : Fin n => acc * base ^ (k : ℕ)
  | 0, acc => by simp [powersFrom]
  | n + 1, acc => by
    rw [powersFrom, powersFrom_eq base n, List.ofFn_succ, Fin.val_zero, pow_zero, mul_one]
    refine congrArg (acc :: ·) (congrArg List.ofFn (funext fun k => ?_))
    rw [Fin.val_succ, pow_succ']
    ring

theorem powers_eq (lam : E) (n : ℕ) : powers lam n = List.ofFn fun k : Fin n => lam ^ (k : ℕ) := by
  rw [powers, powersFrom_eq]
  simp only [one_mul]

theorem dot_ofFn : ∀ (m : ℕ) (f : Fin (m + 1) → E) (u : Fin m → E),
    dot (List.ofFn f) (List.ofFn u) = ∑ c : Fin m, f c.castSucc * u c
  | 0, f, u => by simp [dot]
  | m + 1, f, u => by
    rw [List.ofFn_succ (f := f), List.ofFn_succ (f := u), LeanVM.Protocol.Whir.Complete.dot_cons, dot_ofFn m,
      Fin.sum_univ_succ]
    simp only [Fin.castSucc_zero, Fin.succ_castSucc]

/-- The claims' scales: `Σ_c λ^c · u c`. -/
theorem dot_powers (lam : E) (m : ℕ) (u : Fin m → E) :
    dot (powers lam (m + 1)) (List.ofFn u) = ∑ c : Fin m, lam ^ (c : ℕ) * u c := by
  rw [powers_eq, dot_ofFn]
  simp only [Fin.val_castSucc]

/-- The gadget's scale: `λ^m`. -/
theorem powers_getD (lam : E) (m : ℕ) : (powers lam (m + 1)).getD m 0 = lam ^ m := by
  rw [powers_eq, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

/-! ## The weight table -/

/-- The sum over the lanes at the index of `i`'s bits: lane `i mod 64`, if there is one. -/
theorem sum_lane_eq {nL : ℕ} (hnL : nL ≤ 2 ^ 6) (pos : Fin nL → Fin 6 → Bool)
    (hpos : ∀ l, pos l = bitsOf 6 l) (i : ℕ) (F : Fin nL → E) :
    (∑ l, if pos l = bitsOf 6 i then F l else 0) = if h : i % 64 < nL then F ⟨i % 64, h⟩ else 0 := by
  by_cases h : i % 64 < nL
  · rw [dite_eq_left h, sum_eq_single ⟨i % 64, h⟩]
    · rw [ite_eq_left (by rw [hpos]; exact (bitsOf_eq_iff i (Nat.mod_lt _ (by norm_num))).mpr rfl)]
    · intro l _ hne
      rw [ite_eq_right]
      intro he
      apply hne
      rw [hpos] at he
      exact Fin.ext ((bitsOf_eq_iff i (lt_of_lt_of_le l.isLt hnL)).mp he)
    · simp
  · rw [dite_eq_right h]
    refine sum_eq_zero fun l _ => ?_
    rw [ite_eq_right]
    intro he
    rw [hpos] at he
    have := (bitsOf_eq_iff i (lt_of_lt_of_le l.isLt hnL)).mp he
    have := l.isLt
    omega

/-- **The statement's weight table represents the model's combined weight**: for a statement layout
agreeing with the model's, claims `cl` at the points `points` (of at least `ℓ` coordinates), and the
batching powers of `λ`. -/
theorem weight_rep {SL : PcsQuotient.Layout} {L : QuotientSecurity.Hiding.Deployed.Layout}
    (hS : SameLayout SL L) (h : L.OK) {m : ℕ} (cl : Fin m → PcsQuotient.Claim)
    (claims : List PcsQuotient.Claim) (hcl : claims = List.ofFn cl) (points : Fin m → List E)
    (hpt : ∀ c, (cl c).point = points c) (hlen : ∀ c, L.logLane ≤ (points c).length) (lam : E) :
    ArrRep 6 (2 ^ L.logLane) (weightTable SL (powers lam (m + 1)) claims)
      (HiddenLayout.combinedW L.pos
        (Gadget.claimsW (L.toGadget h) L.pos (L.claimW points) ![1, F192.Y, F192.Y ^ 2])
        (Gadget.powers m lam)) := by
  subst hcl
  have h6 : L.logN = L.logLane + 6 := by
    have := h.lane
    simp only [QuotientSecurity.Hiding.Deployed.Layout.logLane,
      QuotientSecurity.Hiding.Deployed.laneFold] at this ⊢
    omega
  have hsz : 2 ^ SL.logN = 2 ^ 6 * 2 ^ L.logLane := by rw [hS.1, h6, pow_add, mul_comm]
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  refine ⟨by simp [weightTable, hsz], fun i hi => ?_⟩
  have hi' : i < 2 ^ SL.logN := by rw [hsz]; exact hi
  have hy : i / 2 ^ 6 < 2 ^ L.logLane := Nat.div_lt_of_lt_mul hi
  have hy' : i / 64 < 2 ^ L.logLane := hy
  rw [E2ECompleteness.weightTable_getD SL _ _ hi', List.length_ofFn, List.map_ofFn, powers_getD,
    dot_powers]
  simp only [tAt, dite_eq_left hy, HiddenLayout.combinedW, Function.comp_apply]
  rw [sum_lane_eq h.lanes_le L.pos (fun _ => rfl) i]
  by_cases hli : i % 64 < L.lanes.length
  · rw [dite_eq_left hli, Fin.sum_univ_castSucc]
    simp only [Gadget.powers, Gadget.claimsW, GadgetLayout.withGadget, Fin.snoc_castSucc,
      Fin.snoc_last]
    refine (add_comm _ _).trans (congrArg₂ (· + ·) ?_ ?_)
    · refine sum_congr rfl fun c _ => ?_
      rw [weightAt_eq_role hS h (cl c) (by rw [hpt]; exact hlen c) (i % 64) hy',
        LayoutClaims.claimW_eq h2 h, hpt]
      rfl
    · rw [gadgetAt_eq hS h, gadgetW_eq_stmt h]
      rfl
  · have hnL := h.lanes_ge
    rw [dite_eq_right hli, gadgetAt_eq hS h,
      ite_eq_right (fun hc => by have := le_of_mem_gadgetLanes hc.2.2; omega), mul_zero, zero_add]
    refine sum_eq_zero fun c _ => ?_
    rw [weightAt_eq_role hS h (cl c) (by rw [hpt]; exact hlen c) (i % 64) hy',
      role_of_ge (L := L) (not_lt.mp hli) (i / 64)]
    simp only [mul_zero]

end PcsQuotient.EndToEnd.Core
