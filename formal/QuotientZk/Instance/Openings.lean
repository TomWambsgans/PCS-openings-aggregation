-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Instance.Challenges
import QuotientSecurity.Hiding.Deployed
import Implementation.Claims

/-!
# The deployed secret openings

The witness and quotient tables' openings at `2^22` rows, as `SecretOpening`s over `ChV` (the
challenges and the five values), and their `Conditions`:

* **the layouts** (`Lw`, `Lq`): `witness_layout(22)` and `quotient_layout(22)` (`Hiding/DeployedLayout`,
  `deployed_ok`): `40` and `63` lanes of `2^19` and `2^22` words, as `GadgetLayout`s;
* **the claims** (`claimsW`, `claimsQ`, `claimsS`): the verifier's (`Implementation.modelWitness`,
  `modelQuotient`, `modelSum`: what `reduce` passes, `Implementation/Claims.lean`), points then
  value; their weights `opening::verify`'s closure (`Layout.claimW`, `DeployedWeights.lean`); the
  quotient claim's point reads the five values;
* **the opened positions** (`slotsOf`): level 0's query positions (`queryPhase`: the windows of the
  position draws, `positionsOf`), distinct, then the first positions not queried, `224` (witness) or
  `225` (quotient) in all; their encoding the novel basis at those positions (`novelEnc`);
* **the gadget's coefficients** `1, Y, Y²`.

`conditionsW`, `conditionsQ`: (Q) (`novel_firstEval_surjective`), `WeightsFit` (`weightsFit`), the
lanes (`DeployedLayout.lean`), the basis.
-/

open OracleComp Polynomial Module QuotientSecurity QuotientSecurity.Hiding QuotientRpm
open QuotientZk.Joint
open QuotientZk.Deployed (Out)

namespace QuotientZk.Instance

set_option linter.unusedSectionVars false

/-- **The fields' representations**: `K`'s 64-bit words (`Words`, the novel basis's points and the
rows' bytes), `E`'s limbs, and `E`'s coordinates over `K` (`coords`, a `K`-linear bijection; for
`F192` its three `F64` limbs), in which the simulator's tables are solved for (`Builder.lean`). -/
structure Rep (K E : Type) [Field K] [Field E] [Algebra K E] where
  w : Words K
  toWord : K → UInt64
  toWord_injective : Function.Injective toWord
  limbs : E ≃ Limbs
  coords : E ≃ₗ[K] (Fin 3 → K)

/-! ## The layouts -/

/-- `witness_layout(22)`. -/
abbrev Lw : QuotientSecurity.Hiding.Deployed.Layout :=
  QuotientSecurity.Hiding.Deployed.witnessLayout 22

/-- `quotient_layout(22)`. -/
abbrev Lq : QuotientSecurity.Hiding.Deployed.Layout :=
  QuotientSecurity.Hiding.Deployed.quotientLayout 22

theorem okW : Lw.OK := (QuotientSecurity.Hiding.Deployed.deployed_ok 22 (by norm_num) (by norm_num)).1
theorem okQ : Lq.OK := (QuotientSecurity.Hiding.Deployed.deployed_ok 22 (by norm_num) (by norm_num)).2

/-- The witness table's lanes and entries, the quotient table's. -/
abbrev ιW := Fin Lw.lanes.length
abbrev YW := Fin (2 ^ Lw.logLane)
abbrev ιQ := Fin Lq.lanes.length
abbrev YQ := Fin (2 ^ Lq.logLane)

theorem lanes_W : Lw.lanes.length = 40 :=
  (QuotientSecurity.Hiding.Deployed.deployed_shape 22 (by norm_num) (by norm_num)).1
theorem lanes_Q : Lq.lanes.length = 63 :=
  (QuotientSecurity.Hiding.Deployed.deployed_shape 22 (by norm_num) (by norm_num)).2.1
theorem logLane_W : Lw.logLane = 19 :=
  (QuotientSecurity.Hiding.Deployed.deployed_shape 22 (by norm_num) (by norm_num)).2.2.2.2.1
theorem logLane_Q : Lq.logLane = 22 :=
  (QuotientSecurity.Hiding.Deployed.deployed_shape 22 (by norm_num) (by norm_num)).2.2.2.2.2.1

theorem card_ιW : Fintype.card ιW = 40 := by rw [Fintype.card_fin, lanes_W]
theorem card_ιQ : Fintype.card ιQ = 63 := by rw [Fintype.card_fin, lanes_Q]

/-! ## The opened positions -/

/-- **Level 0's queries** (`queryPhase`): the `b`-bit windows of the position draws, the first `q`. -/
def queried (b q : ℕ) (ds : List Limbs) : List ℕ := (ds.flatMap (QuotientZk.Deployed.positionsOf b)).take q

/-- **The opened positions**: the distinct queries, then the first positions not queried, `q` in
all. -/
def slotsOf (b q : ℕ) (ds : List Limbs) : List ℕ :=
  ((queried b q ds).dedup ++
    (List.range (2 * q + 1)).filter fun x => decide (x ∉ queried b q ds)).take q

theorem lt_of_mem_positionsOf {b x : ℕ} {L : Limbs} (h : x ∈ QuotientZk.Deployed.positionsOf b L) :
    x < 2 ^ b := by
  unfold QuotientZk.Deployed.positionsOf at h
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp h
  exact Nat.mod_lt _ (by positivity)

theorem lt_of_mem_queried {b q x : ℕ} {ds : List Limbs} (h : x ∈ queried b q ds) : x < 2 ^ b := by
  obtain ⟨L, -, hL⟩ := List.mem_flatMap.mp (List.mem_of_mem_take h)
  exact lt_of_mem_positionsOf hL

theorem slotsOf_nodup (b q : ℕ) (ds : List Limbs) : (slotsOf b q ds).Nodup := by
  refine List.Nodup.sublist (List.take_sublist _ _) ?_
  refine List.nodup_append.mpr ⟨List.nodup_dedup _, List.nodup_range.filter _, ?_⟩
  intro a ha c hc hac
  rw [List.mem_dedup] at ha
  have := (List.mem_filter.mp hc).2
  subst hac
  simp [ha] at this

theorem slotsOf_length (b q : ℕ) (ds : List Limbs) : (slotsOf b q ds).length = q := by
  unfold slotsOf
  set p := queried b q ds
  rw [List.length_take]
  refine min_eq_left ?_
  have hsplit := List.length_eq_length_filter_add (l := List.range (2 * q + 1))
    (fun x => decide (x ∈ p))
  have hin : ((List.range (2 * q + 1)).filter fun x => decide (x ∈ p)).length ≤ p.dedup.length := by
    refine List.Subperm.length_le (List.Nodup.subperm (List.nodup_range.filter _) ?_)
    intro x hx
    rw [List.mem_dedup]
    simpa using (List.mem_filter.mp hx).2
  have hnot : ((List.range (2 * q + 1)).filter fun x => !decide (x ∈ p)) =
      (List.range (2 * q + 1)).filter fun x => decide (x ∉ p) := by
    congr 1
    funext x
    simp
  rw [List.length_range, hnot] at hsplit
  rw [List.length_append]
  omega

theorem lt_of_mem_slotsOf {b q x : ℕ} {ds : List Limbs} (hq : 2 * q + 1 ≤ 2 ^ b)
    (h : x ∈ slotsOf b q ds) : x < 2 ^ b := by
  rcases List.mem_append.mp (List.mem_of_mem_take h) with h | h
  · exact lt_of_mem_queried (List.mem_dedup.mp h)
  · exact lt_of_lt_of_le (List.mem_range.mp (List.mem_filter.mp h).1) hq

/-- The `i`-th opened position. -/
def slotFn (b q : ℕ) (ds : List Limbs) (i : Fin q) : ℕ :=
  (slotsOf b q ds)[(i : ℕ)]'(by rw [slotsOf_length]; exact i.isLt)

theorem slotFn_injective (b q : ℕ) (ds : List Limbs) : Function.Injective (slotFn b q ds) := by
  intro i j h
  exact Fin.ext ((slotsOf_nodup b q ds).getElem_inj_iff.mp h)

theorem slotFn_mem (b q : ℕ) (ds : List Limbs) (i : Fin q) : slotFn b q ds i ∈ slotsOf b q ds :=
  List.getElem_mem _

theorem slotFn_lt {b q : ℕ} (ds : List Limbs) (hq : 2 * q + 1 ≤ 2 ^ b) (i : Fin q) :
    slotFn b q ds i < 2 ^ b :=
  lt_of_mem_slotsOf hq (slotFn_mem b q ds i)

/-- The slot of an opened position (`0` for any other). -/
def slotOf (b q : ℕ) [NeZero q] (ds : List Limbs) (x : ℕ) : Fin q :=
  if h : x ∈ slotsOf b q ds then
    ⟨(slotsOf b q ds).idxOf x,
      lt_of_lt_of_eq (List.idxOf_lt_length_iff.mpr h) (slotsOf_length b q ds)⟩
  else 0

theorem slotFn_slotOf (b q : ℕ) [NeZero q] (ds : List Limbs) {x : ℕ} (h : x ∈ slotsOf b q ds) :
    slotFn b q ds (slotOf b q ds x) = x := by
  unfold slotOf slotFn
  rw [dif_pos h]
  exact List.getElem_idxOf _

/-! ## The deployed positions and claims -/

section Deployed

variable {E : Type} [Field E] [DecidableEq E] [CharP E 2]

/-- The witness opening's level-0 position draws: its answers `19 .. 44` after `λ` and `φ` (after
the first commitment's `19` out-of-domain coordinates). -/
def drawsW (c : DChal E) : List Limbs :=
  List.ofFn fun i : Fin 25 => drawLimbs (c.2.1.1.2 ⟨19 + (i : ℕ), by have := i.isLt; omega⟩)

/-- The quotient opening's: its answers `22 .. 51` after `λ` and `φ`. -/
def drawsQ (c : DChal E) : List Limbs :=
  List.ofFn fun i : Fin 29 => drawLimbs (c.2.2.1.1.2 ⟨22 + (i : ℕ), by have := i.isLt; omega⟩)

/-- **The witness table's opened positions**: `224` of the `2^20` codeword rows. -/
def slotsW (c : DChal E) : List ℕ := slotsOf 20 224 (drawsW c)
/-- **The quotient table's**: `225` of the `2^23`. -/
def slotsQ (c : DChal E) : List ℕ := slotsOf 23 225 (drawsQ c)

/-- The witness claim's point (`modelWitness`'s): `ρ, ρ², u_2 .. u_24`. -/
noncomputable def pointW (c : DChal E) : List E :=
  List.ofFn (Fin.cons c.1.2 (Fin.cons (c.1.2 ^ 2) (claimPoint 2 (22 + 1) c.1.1.2)) :
    Fin (22 + 1 + 1 + 1) → E)

theorem modelWitness_eq (c : DChal E) (a : Fin 4 → E) :
    Implementation.modelWitness c.1.1.2 c.1.2 a = pointW c ++
      [(∑ j, Params.opening c.1.2 j * a j) / claimScale 2 (22 + 1) c.1.1.2] := rfl

/-- The quotient claim's point (`modelQuotient`'s): `u_0 .. u_25`, `vCells(t)/claimDen`, `ρ`,
`Y/(1+Y)`, `Y²/(1+Y²)`: it reads the five values. -/
noncomputable def pointQ (P₀ : Params E) (Y : E) (c : DChal E) (v : Vals E) : List E :=
  List.ofFn (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (claimPoint 0 (22 + 2 + 1 + 1) c.1.1.2)
      (P₀.vCells.eval c.1.1.2 / P₀.claimDen c.1.1.1.1 c.1.1.1.2.1 c.1.1.2 v.1 v.2)) c.1.2)
      (Y / (1 + Y))) (Y ^ 2 / (1 + Y ^ 2)) :
    Fin (22 + 2 + 1 + 1 + 1 + 1 + 1 + 1) → E)

theorem modelQuotient_eq (P₀ : Params E) (Y : E) (c : DChal E) (v : Vals E) :
    Implementation.modelQuotient P₀ c.1.1.1.1 c.1.1.1.2.1 c.1.1.1.2.2 c.1.1.2 c.1.2 v.2 Y v.1 =
      pointQ P₀ Y c v ++ [P₀.claimValue c.1.1.1.1 c.1.1.1.2.1 c.1.1.1.2.2 c.1.1.2 c.1.2 v.1 v.2 /
        ((1 + Y) * (1 + Y ^ 2)) / claimScale 0 (22 + 2 + 1 + 1) c.1.1.2] := rfl

/-- The sum claim's point (`modelSum`'s, fixed). -/
noncomputable def pointS (Y : E) : List E := List.ofFn (sumPoint (22 + 2) Y)

theorem modelSum_eq (P₀ : Params E) (stmt : Fin P₀.words → E) (Y : E) (c : DChal E) :
    Implementation.modelSum P₀ stmt c.1.1.1.2.2 Y =
      pointS Y ++ [P₀.target stmt c.1.1.1.2.2 / ((1 + Y) * (1 + Y ^ 2))] := rfl

/-- **The verifier's claimed values**, from the challenges and the five values. -/
noncomputable def valsW (c : DChal E) (v : Vals E) : Fin 1 → E :=
  fun _ => (∑ j, Params.opening c.1.2 j * v.1 j) / claimScale 2 (22 + 1) c.1.1.2

noncomputable def valsQ (P₀ : Params E) (stmt : Fin P₀.words → E) (Y : E) (c : DChal E)
    (v : Vals E) : Fin 2 → E :=
  ![P₀.claimValue c.1.1.1.1 c.1.1.1.2.1 c.1.1.1.2.2 c.1.1.2 c.1.2 v.1 v.2 /
      ((1 + Y) * (1 + Y ^ 2)) / claimScale 0 (22 + 2 + 1 + 1) c.1.1.2,
    P₀.target stmt c.1.1.1.2.2 / ((1 + Y) * (1 + Y ^ 2))]

end Deployed

/-! ## The openings -/

section Openings

variable {K E : Type} [Field K] [Field E] [Algebra K E] [DecidableEq E] [CharP E 2]

/-- The level-0 view of an opening: the lane rounds, the folded table, the opened rows. -/
abbrev L0View (E ι Y Q K : Type) := (Fin 6 → E × E) × (Y → E) × (Q → ι → K)

/-- **The witness table's opening**: `witness_layout(22)` with the gadget, its claim at `pointW`,
the gadget's `1, Y, Y²`, the novel basis at the opened positions; WHIR after the first fold is a
public function of the level-0 view (`rest` the identity: the prover's later messages are built
from it, `Prover.lean`). -/
noncomputable def openW (rep : Rep K E) (Y : E) :
    SecretOpening K E (ChV E ΓW ΓQ Γσ) ιW YW (Fin 224) (L0View E ιW YW (Fin 224) K) where
  L := Lw.toGadget okW
  pos := Lw.pos
  m := 1
  Wc cv := Lw.claimW fun _ => pointW cv.1
  β := ![1, Y, Y ^ 2]
  enc cv := novelEnc rep.w Lw.logLane (slotFn 20 224 (drawsW cv.1))
  rest _ lv := lv

/-- **The quotient table's opening**: `quotient_layout(22)`, its two claims at `pointQ` (reading
the five values) and `pointS`. -/
noncomputable def openQ (rep : Rep K E) (P₀ : Params E) (Y : E) :
    SecretOpening K E (ChV E ΓW ΓQ Γσ) ιQ YQ (Fin 225) (L0View E ιQ YQ (Fin 225) K) where
  L := Lq.toGadget okQ
  pos := Lq.pos
  m := 2
  Wc cv := Lq.claimW ![pointQ P₀ Y cv.1 cv.2, pointS Y]
  β := ![1, Y, Y ^ 2]
  enc cv := novelEnc rep.w Lq.logLane (slotFn 23 225 (drawsQ cv.1))
  rest _ lv := lv

variable [CharP K 2] [FiniteDimensional K E]

theorem two_eq_zero_E : (2 : E) = 0 := CharTwo.two_eq_zero

theorem basis_of (h3 : finrank K E = 3) {Y : E} (hY : LinearIndependent K ![1, Y, Y ^ 2]) :
    ∃ b : Module.Basis (Fin 3) K E, ⇑b = ![1, Y, Y ^ 2] :=
  ⟨basisOfLinearIndependentOfCardEqFinrank hY (by rw [Fintype.card_fin, h3]),
    coe_basisOfLinearIndependentOfCardEqFinrank _ _⟩

/-- **The witness opening's conditions.** -/
theorem conditionsW (rep : Rep K E) (h3 : finrank K E = 3) {Y : E}
    (hY : LinearIndependent K ![1, Y, Y ^ 2]) : (openW rep Y).Conditions where
  placed := ⟨Deployed.Layout.pos_injective okW, Deployed.Layout.pos_pairA0 okW,
    Deployed.Layout.pos_pairB0 okW, Deployed.Layout.pos_pairA1 okW, Deployed.Layout.pos_pairB1 okW,
    Deployed.Layout.pos_ov okW⟩
  pairANotRand := Deployed.Layout.pairA_not_rand okW
  lowHalf := Deployed.Layout.pos_low okW
  cubeOn := Deployed.Layout.pos_cube okW
  cubeRand := Deployed.Layout.pos_rand okW
  weightsFit _ := Deployed.Layout.weightsFit two_eq_zero_E okW _
  condQ c := by
    have hl := logLane_W
    refine novel_firstEval_surjective rep.w (by omega) (by omega) _ (fun x => ?_)
      (slotFn_injective _ _ _) (by simp [freeEntries])
    rw [hl]
    exact slotFn_lt _ (by norm_num) x
  basis := basis_of h3 hY

/-- **The quotient opening's conditions.** -/
theorem conditionsQ (rep : Rep K E) (P₀ : Params E) (h3 : finrank K E = 3) {Y : E}
    (hY : LinearIndependent K ![1, Y, Y ^ 2]) : (openQ rep P₀ Y).Conditions where
  placed := ⟨Deployed.Layout.pos_injective okQ, Deployed.Layout.pos_pairA0 okQ,
    Deployed.Layout.pos_pairB0 okQ, Deployed.Layout.pos_pairA1 okQ, Deployed.Layout.pos_pairB1 okQ,
    Deployed.Layout.pos_ov okQ⟩
  pairANotRand := Deployed.Layout.pairA_not_rand okQ
  lowHalf := Deployed.Layout.pos_low okQ
  cubeOn := Deployed.Layout.pos_cube okQ
  cubeRand := Deployed.Layout.pos_rand okQ
  weightsFit _ := Deployed.Layout.weightsFit two_eq_zero_E okQ _
  condQ c := by
    have hl := logLane_Q
    refine novel_firstEval_surjective rep.w (by omega) (by omega) _ (fun x => ?_)
      (slotFn_injective _ _ _) (by simp [freeEntries])
    rw [hl]
    exact slotFn_lt _ (by norm_num) x
  basis := basis_of h3 hY

end Openings

end QuotientZk.Instance
