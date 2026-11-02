-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Implementation.Blocks

/-!
# What the graph's outputs are

`reduceIds_spec`: the program of `Program.lean`, which `reduceIds_eq` checks against the graph,
leaves nodes whose elements are `quotient::protocol::reduce`'s formulas over the field (`Formula`),
in terms of the leaves (the statement's halves, the challenges, the five values): the product of
the denominators that the contract requires nonzero, and, when it is nonzero, the three claims'
points and values and the sum's value.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Implementation

open Program Emitted QuotientSecurity

/-- The leaves' elements: the statement's four halves, the challenges `α, β, γ, t, ρ`, and the
five values `a_0 .. a_3`, `next`. -/
structure Vals (F : Type) where
  s : Fin 4 → F
  α : F
  β : F
  γ : F
  t : F
  a : Fin 4 → F
  next : F
  ρ : F

namespace Formula

variable {F : Type} [Field F] (limbs : F ≃ QuotientRpm.Limbs) (I : Vals F)

/-- `w_k(t)`. -/
noncomputable def w (k : ℕ) : F := sq^[k] I.t

/-- A cell of the row of `t` (`reduce`'s `cell`). -/
noncomputable def cellF (shift : Nat) (second : Bool) : F :=
  I.a 0 + (I.t + elem limbs shift) * I.a 1 +
    (if second then w I 1 + 1 else w I 1) * (I.a 2 + (I.t + elem limbs shift) * I.a 3)

noncomputable def x : F := cellF limbs I 0 false
noncomputable def c1 : F := cellF limbs I 1 false
noncomputable def c2 : F := cellF limbs I (beta.getD 1 0) true
noncomputable def c3 : F := cellF limbs I (beta.getD 1 0 ^^^ 1) true

/-- The gate, `v + x + c + y c`. -/
noncomputable def gate : F := c3 limbs I + x limbs I + c2 limbs I + c1 limbs I * c2 limbs I

/-- Coordinate `k` of the public region. -/
noncomputable def coord (k : ℕ) : F :=
  (List.range' (k + 1) (11 - (k + 1))).foldl
    (fun acc j => acc + elem limbs (coords.getD (j - k) 0) * w I j) (w I k)

noncomputable def gammas : List F := [I.γ, I.γ * I.γ, I.γ * I.γ * (I.γ * I.γ)]

/-- The slope of coordinate `k`. -/
noncomputable def slope (k : ℕ) : F :=
  if k < 8 then elem limbs (slopeConst k) else 1 + (gammas I).getD (k - 8) 0

/-- The public weight at `t`. -/
noncomputable def pub : F :=
  (List.range 11).foldl (fun acc k => acc * (1 + coord limbs I k * slope limbs I k))
    ((List.range' 11 13).foldl (fun acc k => acc * (1 + w I k)) 1)

/-- What the weighted public bits must sum to. -/
noncomputable def target : F :=
  I.s 0 + I.γ * I.s 1 + I.γ * I.γ * (I.s 2 + I.γ * I.s 3) + I.γ * I.γ * (I.γ * I.γ)

/-- The rows' polynomial at `t`. -/
noncomputable def rows : F :=
  (List.range 23).foldl (fun acc k => acc + elem limbs (tau.getD k 0) * w I k) 0

noncomputable def d : F := I.α + x limbs I + I.β * I.t
noncomputable def dNext : F := I.α + x limbs I + I.β * I.next
noncomputable def product : F := d limbs I * dNext limbs I
noncomputable def copies : F :=
  d limbs I + dNext limbs I + pub limbs I * x limbs I * product limbs I

/-- The denominators: every `1 + w_k`, the copy identity's, the rows'. -/
noncomputable def dens : List F :=
  (List.range 26).map (fun k => 1 + w I k) ++ [product limbs I + w I 24, rows limbs I]

/-- **The product the contract requires nonzero.** -/
noncomputable def check : F := (dens limbs I).prod

noncomputable def opened : F :=
  (1 + I.ρ * I.ρ) * (I.a 0 + I.ρ * (I.a 0 + I.a 1)) + I.ρ * I.ρ * (I.a 2 + I.ρ * (I.a 2 + I.a 3))

noncomputable def identities : F :=
  (1 + I.ρ) * copies limbs I * rows limbs I + I.ρ * product limbs I * gate limbs I

/-- `∏ (1 + w_k)⁻¹` over some `k`. -/
noncomputable def invProd (l : List ℕ) : F := (l.map fun k => (1 + w I k)⁻¹).prod

/-- `u_k = w_k / (1 + w_k)`. -/
noncomputable def u (k : ℕ) : F := w I k * (1 + w I k)⁻¹

/-- **The witness table's claim**: its point, then its value. -/
noncomputable def witness : List F :=
  [I.ρ, I.ρ * I.ρ] ++ (List.range 23).map (fun k => u I (k + 2)) ++
    [opened I * invProd I (List.range' 2 23)]

/-- **The wiring table's claim.** -/
noncomputable def wiring : List F :=
  (List.range 24).map (u I) ++ [I.next * invProd I (List.range 24)]

/-- **The quotient table's first claim.** -/
noncomputable def quotient : List F :=
  (List.range 26).map (u I) ++
    [w I 24 * (product limbs I + w I 24)⁻¹, I.ρ, elem limbs y0, elem limbs y1,
      elem limbs scale * invProd I (List.range 26) * (product limbs I + w I 24)⁻¹ *
        (rows limbs I)⁻¹ * identities limbs I]

/-- **The value of the claim at the fixed point.** -/
noncomputable def sum : F := elem limbs scale * target I

end Formula

variable {F : Type} [Field F] [CharP F 2] {limbs : F ≃ QuotientRpm.Limbs}
variable {H : List UInt8 → Vector UInt8 32} {idx cd : List UInt8}

variable (limbs H idx cd) in
/-- The leaves' elements. -/
noncomputable def leafVals : Vals F where
  s k := val limbs H idx cd (2 + k)
  α := val limbs H idx cd 9
  β := val limbs H idx cd 11
  γ := val limbs H idx cd 13
  t := val limbs H idx cd 17
  a k := val limbs H idx cd (18 + k)
  next := val limbs H idx cd 22
  ρ := val limbs H idx cd 24

theorem foldl_mul_eq {α : Type} (f : α → F) : ∀ (l : List α) (a : F),
    l.foldl (fun acc k => acc * f k) a = a * (l.map f).prod
  | [], a => by simp
  | k :: l, a => by rw [List.foldl_cons, foldl_mul_eq f l, List.map_cons, List.prod_cons, mul_assoc]

theorem prod_take_eq (l : List Nat) (i : Nat) (hi : i ≤ l.length) :
    ((l.take i).map (val limbs H idx cd)).prod =
      ((List.range i).map fun j => val limbs H idx cd (l.getD j 0)).prod := by
  have e : (l.take i).map (val limbs H idx cd) =
      (List.range i).map fun j => val limbs H idx cd (l.getD j 0) := by
    apply List.ext_getElem (by simp; omega)
    intro j h1 h2
    simp only [List.length_map, List.length_take, List.length_range] at h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < l.length by omega)]
  rw [e]

theorem dens_getD_lt (I : Vals F) (i : Nat) (hi : i < 26) :
    (Formula.dens limbs I).getD i 0 = 1 + Formula.w I i := by
  unfold Formula.dens
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

theorem dens_getD_26 (I : Vals F) :
    (Formula.dens limbs I).getD 26 0 = Formula.product limbs I + Formula.w I 24 := by
  unfold Formula.dens
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem dens_getD_27 (I : Vals F) : (Formula.dens limbs I).getD 27 0 = Formula.rows limbs I := by
  unfold Formula.dens
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem getD_of_map_eq {l : List Nat} {g : Nat → F} {n : Nat}
    (h : l.map (val limbs H idx cd) = (List.range n).map g) (i : Nat) (hi : i < n) :
    val limbs H idx cd (l.getD i 0) = g i := by
  have hl : l.length = n := by simpa using congrArg List.length h
  have := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some,
    List.getElem?_eq_getElem (show i < l.length by omega), Option.some.injEq] at this
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < l.length by omega)]
  exact this

variable (limbs H idx cd) in
/-- What the first stage leaves (`stageA`): the `w` chain and the formulas. -/
structure AOK (A : StageA) : Prop where
  w : ∀ k < 26, val limbs H idx cd (A.w.getD k 0) = Formula.w (leafVals limbs H idx cd) k
  x : val limbs H idx cd A.x = Formula.x limbs (leafVals limbs H idx cd)
  gate : val limbs H idx cd A.gate = Formula.gate limbs (leafVals limbs H idx cd)
  target : val limbs H idx cd A.target = Formula.target (leafVals limbs H idx cd)
  rows : val limbs H idx cd A.rows = Formula.rows limbs (leafVals limbs H idx cd)
  product : val limbs H idx cd A.product = Formula.product limbs (leafVals limbs H idx cd)
  copies : val limbs H idx cd A.copies = Formula.copies limbs (leafVals limbs H idx cd)

variable (limbs H idx cd) in
/-- What the second stage leaves (`stageB`): the denominators and their prefix products. -/
structure BOK (B : StageB) : Prop where
  dens : B.dens.map (val limbs H idx cd) = Formula.dens limbs (leafVals limbs H idx cd)
  pre : ∀ i ≤ B.dens.length, val limbs H idx cd (B.pre.getD i 0) = ((B.dens.take i).map (val limbs H idx cd)).prod
  total : B.total = B.pre.getD B.dens.length 0

variable (hF : IsF192 limbs)
include hF

local notation "V" => val limbs H idx cd
local notation "MUL" => mul_spec (H := H) (idx := idx) (cd := cd) hF
local notation "ADD" => add_spec (H := H) (idx := idx) (cd := cd) hF
local notation "CNST" => cnst_spec (H := H) (idx := idx) (cd := cd) hF

/-- A step of a program: bind, with the spec of its first operation. -/
macro "stp " h:term:max " => " x:ident hx:ident : tactic =>
  `(tactic| ((try dsimp only); apply Spec.bind; refine Spec.weaken $h fun $x $hx => ?_))

theorem one_val : V leaves₀.one = 1 := by
  show V 1 = 1
  rw [val_const hF (k := 1) (c := 1) (by decide +kernel), elem_one hF]

theorem stageA_spec : Spec (stageA leaves₀) (AOK limbs H idx cd) := by
  set I := leafVals limbs H idx cd with hI
  unfold stageA
  have hone := one_val (H := H) (idx := idx) (cd := cd) hF
  -- the `w` chain
  stp (wChain_spec (H := H) (idx := idx) (cd := cd) hF 17 25) => w hw
  obtain ⟨hwlen, hwv⟩ := hw
  have hW : ∀ k < 26, V (w.getD k 0) = Formula.w I k := fun k hk => hwv k hk
  -- the cells and the gate
  stp (cell_spec (H := H) (idx := idx) (cd := cd) hF leaves₀ hone _ _ _) => c0 hc0
  stp (cell_spec (H := H) (idx := idx) (cd := cd) hF leaves₀ hone _ _ _) => c1 hc1
  stp (cell_spec (H := H) (idx := idx) (cd := cd) hF leaves₀ hone _ _ _) => c2 hc2
  stp (cell_spec (H := H) (idx := idx) (cd := cd) hF leaves₀ hone _ _ _) => c3 hc3
  have hcell : ∀ (sh : Nat) (second : Bool) (c : Nat),
      V c = V (leaves₀.a.getD 0 0) + (V leaves₀.t + elem limbs sh) * V (leaves₀.a.getD 1 0) +
        (if second then V (w.getD 1 0) + 1 else V (w.getD 1 0)) *
          (V (leaves₀.a.getD 2 0) + (V leaves₀.t + elem limbs sh) * V (leaves₀.a.getD 3 0)) →
      V c = Formula.cellF limbs I sh second := by
    intro sh second c h
    rw [h, hW 1 (by norm_num)]
    rfl
  have hx := hcell _ _ _ hc0
  have hy := hcell _ _ _ hc1
  have hc := hcell _ _ _ hc2
  have hv := hcell _ _ _ hc3
  stp (ADD _ _) => g1 hg1
  stp (ADD _ _) => g2 hg2
  stp (MUL _ _) => g3 hg3
  stp (ADD _ _) => gate hgate
  have hG : V gate = Formula.gate limbs I := by
    rw [hgate, hg2, hg1, hg3, hx, hy, hc, hv]; rfl
  -- the public weight
  stp (MUL _ _) => gamma2 hgamma2
  stp (MUL _ _) => gamma4 hgamma4
  stp (foldO_spec (H := H) (idx := idx) (cd := cd) hF (fun acc k => acc * (1 + Formula.w I k))
    (List.range' 11 (24 - 11)) (fun acc k hk => by
      stp (ADD _ _) => o ho
      refine (MUL _ _).weaken fun r hr => ?_
      rw [hr, ho, hone, hW k (by simp at hk; omega)]) leaves₀.one) => pub0 hpub0
  stp (foldO_spec (H := H) (idx := idx) (cd := cd) hF
    (fun acc k => acc * (1 + Formula.coord limbs I k * Formula.slope limbs I k))
    (List.range 11) (fun acc k hk => by
      have hk11 : k < 11 := by simpa using hk
      stp (foldO_spec (H := H) (idx := idx) (cd := cd) hF
        (fun acc j => acc + elem limbs (coords.getD (j - k) 0) * Formula.w I j)
        (List.range' (k + 1) (11 - (k + 1))) (fun acc' j hj => by
          have hj11 : j < 11 := by simp at hj; omega
          stp (CNST _) => bc hbc
          stp (MUL _ _) => p hp
          refine (ADD _ _).weaken fun r hr => ?_
          rw [hr, hp, hbc, hW j (by omega)]) (w.getD k 0)) => coordinate hcoord
      stp (Spec.weaken (P := fun r => V r = Formula.slope limbs I k) (by
          unfold slopeOf Formula.slope
          split_ifs with h8
          · exact CNST _
          · refine (ADD _ _).weaken fun r hr => ?_
            rw [hr, hone]
            have : k - 8 < 3 := by omega
            interval_cases hk' : k - 8
            · rfl
            · simp [Formula.gammas, hgamma2]; rfl
            · simp [Formula.gammas, hgamma4, hgamma2]; rfl) fun r hr => hr) => slope hslope
      stp (MUL _ _) => cs hcs
      stp (ADD _ _) => o ho
      refine (MUL _ _).weaken fun r hr => ?_
      rw [hr, ho, hcs, hslope, hcoord, hone, hW k (by omega)]
      rfl) pub0) => pubW hpubW
  have hP : V pubW = Formula.pub limbs I := by
    rw [hpubW, hpub0, hone]; rfl
  -- the target
  stp (MUL _ _) => tg1 htg1
  stp (ADD _ _) => tg2 htg2
  stp (MUL _ _) => tg3 htg3
  stp (ADD _ _) => tg4 htg4
  stp (MUL _ _) => tg5 htg5
  stp (ADD _ _) => tg6 htg6
  stp (ADD _ _) => target htarget
  have hT : V target = Formula.target I := by
    rw [htarget, htg6, htg5, htg4, htg3, htg2, htg1, hgamma4, hgamma2]; rfl
  -- the rows' polynomial
  stp (CNST _) => zr hzr
  stp (foldO_spec (H := H) (idx := idx) (cd := cd) hF
    (fun acc k => acc + elem limbs (tau.getD k 0) * Formula.w I k) (List.range (24 - 1))
    (fun acc k hk => by
      stp (CNST _) => tk htk
      stp (MUL _ _) => p hp
      refine (ADD _ _).weaken fun r hr => ?_
      rw [hr, hp, htk, hW k (by simp at hk; omega)]) zr) => rows hrows
  have hR : V rows = Formula.rows limbs I := by
    rw [hrows, hzr, elem_zero hF]; rfl
  -- the copy identity
  stp (ADD _ _) => ax hax
  stp (MUL _ _) => bt hbt
  stp (ADD _ _) => dd0 hd
  stp (MUL _ _) => bn hbn
  stp (ADD _ _) => dNext hdNext
  stp (MUL _ _) => product hproduct
  stp (ADD _ _) => dd hdd
  stp (MUL _ _) => px hpx
  stp (MUL _ _) => pxp hpxp
  stp (ADD _ _) => copies hcopies
  have hD : V dd0 = Formula.d limbs I := by rw [hd, hax, hbt, hx]; rfl
  have hDN : V dNext = Formula.dNext limbs I := by rw [hdNext, hax, hbn, hx]; rfl
  have hPr : V product = Formula.product limbs I := by rw [hproduct, hD, hDN]; rfl
  have hC : V copies = Formula.copies limbs I := by
    rw [hcopies, hdd, hpxp, hpx, hD, hDN, hPr, hP, hx]; rfl
  apply Spec.pure
  exact ⟨hW, hx, hG, hT, hR, hPr, hC⟩

theorem stageB_spec (A : StageA) (hA : AOK limbs H idx cd A) : Spec (stageB leaves₀ A) (BOK limbs H idx cd) := by
  set I := leafVals limbs H idx cd with hI
  have hone := one_val (H := H) (idx := idx) (cd := cd) hF
  unfold stageB
  stp (mapO_spec (H := H) (idx := idx) (cd := cd) hF (fun k => 1 + Formula.w I k) (List.range (24 + 2))
    (fun k hk => (ADD _ _).weaken fun r hr => by rw [hr, hone, hA.w k (by simpa using hk)])) => ws hws
  stp (ADD _ _) => cw hcw
  stp (prefixes_spec (H := H) (idx := idx) (cd := cd) hF (ws ++ [cw, A.rows]) leaves₀.one) => pre hpre
  obtain ⟨-, hprev⟩ := hpre
  apply Spec.pure
  refine ⟨?_, fun i hi => by rw [hprev i hi, hone, one_mul], rfl⟩
  rw [List.map_append, hws]
  simp only [List.map_cons, List.map_nil, Formula.dens, hcw, hA.product, hA.w 24 (by norm_num), hA.rows]
  rfl

theorem dens_length (B : StageB) (hB : BOK limbs H idx cd B) : B.dens.length = 28 := by
  simpa [Formula.dens] using congrArg List.length hB.dens

theorem total_val (B : StageB) (hB : BOK limbs H idx cd B) :
    V B.total = Formula.check limbs (leafVals limbs H idx cd) := by
  rw [hB.total, hB.pre _ le_rfl, List.take_length, hB.dens]; rfl

/-- **What the graph requires nonzero** is the product of the denominators. -/
theorem checkId_spec : Spec checkId fun c => V c = Formula.check limbs (leafVals limbs H idx cd) := by
  unfold checkId
  rw [chain_eq]
  apply Spec.bind
  apply Spec.some
  stp (stageA_spec (H := H) (idx := idx) (cd := cd) hF) => A hA
  stp (stageB_spec (H := H) (idx := idx) (cd := cd) hF A hA) => B hB
  exact Spec.pure (total_val hF B hB)

variable [Fintype F]

theorem stageC_spec (hfr : FrobOK limbs) (A : StageA) (hA : AOK limbs H idx cd A) (B : StageB) (hB : BOK limbs H idx cd B)
    (hnz : Formula.check limbs (leafVals limbs H idx cd) ≠ 0) :
    Spec (stageC leaves₀ A B) fun o =>
      o.witness.map V = Formula.witness (leafVals limbs H idx cd) ∧
      o.wiring.map V = Formula.wiring (leafVals limbs H idx cd) ∧
      o.quotient.map V = Formula.quotient limbs (leafVals limbs H idx cd) ∧
      V o.sum = Formula.sum limbs (leafVals limbs H idx cd) := by
  set I := leafVals limbs H idx cd with hI
  have hone := one_val (H := H) (idx := idx) (cd := cd) hF
  have hW := hA.w
  have hdlen := dens_length hF B hB
  have hcheck := total_val hF B hB
  unfold stageC
  -- the inverses
  stp (inverse_spec (H := H) (idx := idx) (cd := cd) hF hfr _) => running hrunning
  set P : Nat → F := fun i => ((List.range i).map fun j => V (B.dens.getD j 0)).prod with hPdef
  have hPs : ∀ i, P (i + 1) = P i * V (B.dens.getD i 0) := fun i => by
    simp [hPdef, List.range_succ]
  have hP28 : P B.dens.length = Formula.check limbs I := by
    rw [hPdef]; dsimp only
    rw [← prod_take_eq _ _ le_rfl, List.take_length, hB.dens]; rfl
  stp (backInv_spec (H := H) (idx := idx) (cd := cd) hF (fun i => B.pre.getD i 0)
    (fun i => B.dens.getD i 0) P hPs _ running
    (fun i hi => by rw [hB.pre i hi.le, prod_take_eq _ _ hi.le])
    (by rw [hrunning, hcheck, hP28]) (by rw [hP28]; exact hnz)) => invsRev hinvs
  obtain ⟨-, hinvs⟩ := hinvs
  rw [hdlen] at hinvs
  have hDen : ∀ i < 28, V (B.dens.getD i 0) = (Formula.dens limbs I).getD i 0 := fun i hi => by
    rw [← hB.dens, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [List.getElem?_eq_getElem (show i < B.dens.length by omega)]
    rfl
  have hInv : ∀ i < 26, V (invsRev.reverse.getD i 0) = (1 + Formula.w I i)⁻¹ := fun i hi => by
    rw [hinvs i (by omega), hDen i (by omega), dens_getD_lt I i hi]
  have hCopyInv : V (invsRev.reverse.getD 26 0) = (Formula.product limbs I + Formula.w I 24)⁻¹ := by
    rw [hinvs 26 (by omega), hDen 26 (by omega), dens_getD_26]
  have hRowsInv : V (invsRev.reverse.getD 27 0) = (Formula.rows limbs I)⁻¹ := by
    rw [hinvs 27 (by omega), hDen 27 (by omega), dens_getD_27]
  stp (mapO_spec (H := H) (idx := idx) (cd := cd) hF (fun k => Formula.u I k) (List.range (24 + 2))
    (fun k hk => (MUL _ _).weaken fun r hr => by
      have hk' : k < 26 := by simpa using hk
      rw [hr, hW k hk', hInv k hk']; rfl)) => u hu
  stp (foldO_spec (H := H) (idx := idx) (cd := cd) hF (fun acc k => acc * (1 + Formula.w I k)⁻¹)
    (List.range' 3 (24 - 3)) (fun acc k hk => (MUL _ _).weaken fun r hr => by
      have hk' : k < 26 := by simp at hk; omega
      rw [hr, hInv k hk']) (invsRev.reverse.getD 2 0)) => middle hmiddle
  stp (MUL _ _) => ws0 hws0
  stp (MUL _ _) => wiringScale hwiringScale
  stp (MUL _ _) => qs0 hqs0
  stp (MUL _ _) => quotientScale hquotientScale
  -- the claims
  stp (MUL _ _) => rho2 hrho2
  stp (ADD _ _) => o1 ho1
  stp (ADD _ _) => o2 ho2
  stp (MUL _ _) => o3 ho3
  stp (ADD _ _) => o4 ho4
  stp (MUL _ _) => o5 ho5
  stp (ADD _ _) => o6 ho6
  stp (MUL _ _) => o7 ho7
  stp (ADD _ _) => o8 ho8
  stp (MUL _ _) => o9 ho9
  stp (ADD _ _) => opened hopened
  stp (CNST _) => sc hsc
  stp (ADD _ _) => i1 hi1
  stp (MUL _ _) => i2 hi2
  stp (MUL _ _) => i3 hi3
  stp (MUL _ _) => i4 hi4
  stp (MUL _ _) => i5 hi5
  stp (ADD _ _) => identities hidentities
  stp (MUL _ _) => wv0 hwv0
  stp (MUL _ _) => witnessValue hwitnessValue
  stp (MUL _ _) => wiringValue hwiringValue
  stp (MUL _ _) => wmc hwmc
  stp (CNST _) => cy0 hcy0
  stp (CNST _) => cy1 hcy1
  stp (MUL _ _) => qv0 hqv0
  stp (MUL _ _) => qv1 hqv1
  stp (MUL _ _) => qv2 hqv2
  stp (MUL _ _) => quotientValue hquotientValue
  stp (MUL _ _) => sum hsum
  apply Spec.pure
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the witness claim
    have hOp : V opened = Formula.opened I := by
      rw [hopened, ho5, ho9, ho1, ho4, ho8, ho3, ho7, ho2, ho6, hrho2, hone]; rfl
    have hMid : V middle * (1 + Formula.w I 24)⁻¹ = Formula.invProd I (List.range' 2 23) := by
      rw [hmiddle, hInv 2 (by norm_num), foldl_mul_eq, Formula.invProd,
        show List.range' 2 23 = [2] ++ List.range' 3 21 ++ [24] by decide]
      simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one]
      try ring
    have e1 : List.map V (List.take (24 - 1) (List.drop 2 u)) =
        (List.range 23).map fun k => Formula.u I (k + 2) := by
      rw [List.map_take, List.map_drop, hu]
      apply List.ext_getElem (by simp)
      intro j h1 h2
      simp [Nat.add_comm]
    have e2 : V witnessValue = Formula.opened I * Formula.invProd I (List.range' 2 23) := by
      rw [hwitnessValue, hwv0, hOp, mul_assoc, hInv 24 (by norm_num), hMid]
    simp only [List.map_append, List.map_cons, List.map_nil, Formula.witness]
    rw [e1, e2, hrho2]
    rfl
  · -- the wiring claim
    have hScale : V wiringScale = Formula.invProd I (List.range 24) := by
      rw [hwiringScale, hws0, hmiddle, hInv 0 (by norm_num), hInv 1 (by norm_num),
        hInv 2 (by norm_num), foldl_mul_eq, Formula.invProd,
        show List.range 24 = [0, 1, 2] ++ List.range' 3 21 by decide]
      simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one]
      try ring
    have e1 : List.map V (List.take 24 u) = (List.range 24).map (Formula.u I) := by
      rw [List.map_take, hu]
      apply List.ext_getElem (by simp)
      intro j h1 h2
      simp
    simp only [List.map_append, List.map_cons, List.map_nil, Formula.wiring]
    rw [e1, hwiringValue, hScale]
    rfl
  · -- the quotient table's first claim
    have hScale : V quotientScale = Formula.invProd I (List.range 26) := by
      rw [hquotientScale, hqs0, hwiringScale, hws0, hmiddle, hInv 0 (by norm_num),
        hInv 1 (by norm_num), hInv 2 (by norm_num), hInv 24 (by norm_num), hInv 25 (by norm_num),
        foldl_mul_eq, Formula.invProd,
        show List.range 26 = [0, 1, 2] ++ List.range' 3 21 ++ [24, 25] by decide]
      simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one]
      try ring
    have hId : V identities = Formula.identities limbs I := by
      rw [hidentities, hi3, hi2, hi1, hi5, hi4, hone, hA.copies, hA.rows, hA.product, hA.gate]; rfl
    simp only [List.map_append, List.map_cons, List.map_nil, Formula.quotient, hu]
    rw [hwmc, hW 24 (by norm_num), hCopyInv, hcy0, hcy1, hquotientValue, hqv2, hqv1, hqv0, hsc,
      hScale, hCopyInv, hRowsInv, hId]
    rfl
  · -- the sum
    rw [hsum, hsc, hA.target]; rfl

/-- **What the graph's outputs are.** The nodes `reduceIds` leaves (the graph's outputs,
`reduceIds_eq`) hold `Formula`'s claims at the leaves' elements, when the product of the
denominators (`checkId_spec`) is not zero. -/
theorem reduceIds_spec (hfr : FrobOK limbs)
    (hnz : Formula.check limbs (leafVals limbs H idx cd) ≠ 0) : Spec reduceIds fun o =>
      o.witness.map V = Formula.witness (leafVals limbs H idx cd) ∧
      o.wiring.map V = Formula.wiring (leafVals limbs H idx cd) ∧
      o.quotient.map V = Formula.quotient limbs (leafVals limbs H idx cd) ∧
      V o.sum = Formula.sum limbs (leafVals limbs H idx cd) := by
  unfold reduceIds
  rw [chain_eq]
  apply Spec.bind
  apply Spec.some
  stp (stageA_spec (H := H) (idx := idx) (cd := cd) hF) => A hA
  stp (stageB_spec (H := H) (idx := idx) (cd := cd) hF A hA) => B hB
  exact stageC_spec hF hfr A hA B hB hnz

end Implementation
