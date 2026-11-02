-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- About leanerVM `mumbai`'s list decoder (https://github.com/Verified-zkEVM/leanerVM, commit
-- 6175f1a07f0dc33bd3d640de0063d1006143ee91, MIT OR Apache-2.0: `Statement/Extractor.lean`), with
-- its lemmas (`lean_vm/LeanVM/Protocol/Extraction/{Prune,Lane,Novel}.lean`,
-- `lean_vm/LeanVM/Protocol/Whir/Sound/{Code,Candidates}.lean`); the bound on the prefixes the
-- pruning keeps is the one `Prune.lean`'s header describes (`length_pruneUpTo_le`, through the
-- Johnson bound `card_iList_johnsonAgreement_le_floor`), proved here.
import Compose.Decoder

/-!
# The decoder's running time

`decodeColumns μ R W` (mumbai's `decodeStacks`) is, with `κ = μ − 6`, `n = 2^(κ+R)` columns,
`k = 2^κ` and the agreement `A = johnsonThreshold μ R`:

1. for each lane `u < 2^6`, while prefixes remain: the lane decoder `gsLaneAt κ R A W u`
   (CompPoly's Guruswami–Sudan over `K` on the `n` pairs `(x_v, W_u(v))`, at the parameters
   `gsParamsFor k n A`: multiplicity `m`, weighted degree `W = m·A − 1`), its output turned into
   novel-basis coefficients (`toNovel`: `k` evaluations and `κ·k` butterflies each),
   deduplicated (the lane's list), each encoded (`novelFwd`: `κ·n` butterflies);
2. one pruning step: every kept prefix times every element of the lane's list, filtering the
   prefix's common columns (at most `n` comparisons each);
3. the `2^6`-lane survivors reassembled as stacks.

**Proved sizes** (at every admissible shape, `L = (code₀ μ R).listMax ≤ listHi ≤ 2^18`):

* `length_laneListAt_le`: each lane's list has at most `L` elements (an element is the
  coefficient array of a codeword agreeing with the lane on `≥ A` columns: GS's soundness);
* `length_pruneUpTo_le`: after each of the `2^6` lanes at most `L` prefixes are kept (a kept
  prefix of `U` lanes is an interleaved codeword of `U` rows agreeing with the word's first `U`
  lanes on `≥ A` common columns; the Johnson bound of the interleaved code, mumbai's
  `LevelCode.card_iList_le`, for `Fin U` rows);
* so the pruning makes at most `2^6 · L · L · n` symbol comparisons and `2^6 · L` forward
  transforms; the decoder's output is at most `L` stacks (`length_decodeColumns_le`).

**The lane decoder's shape** (`gsShape`, computed by the kernel, `gsShape_witness`,
`gsShape_quotient`, `gsShape_wiring`): `(n, A, m, W, ℓ, c)` with `ℓ = ⌊W/(k − 1)⌋` the `Y`-degree
bound of the interpolation polynomial (so at most `ℓ` roots, the GS list before filtering) and
`c = n·m(m+1)/2` the interpolation conditions. At `log_rows = 22`:

| table | `μ` | `n` | `A` | `m` | `W` | `ℓ` | conditions |
|---|---|---|---|---|---|---|---|
| wiring | 24 | `2^19` | 370765 | 1425 | 528340124 | 2015 | 532689715200 |
| witness | 25 | `2^20` | 741549 | 1149 | 852039800 | 1625 | 692767948800 |
| quotient | 28 | `2^23` | 5933305 | 522 | 3097185209 | 738 | 1145070157824 |

The interpolation is Lee–O'Sullivan's: a basis of the `F[X]`-module of the interpolation
polynomials of `Y`-degree at most `ℓ` (`ℓ + 1` generators, of `X`-degree at most `n·m`), reduced
to weak Popov form by Mulders–Storjohann; then Roth–Ruckenstein's root search, at most `ℓ` roots,
each a path of `k` steps of univariate root finding (Shoup's trace splitter over `GF(2^64)`).
These costs are polynomial in `n`, `m`, `ℓ` and are read off the algorithms (CompPoly's), not
proved; the sizes above are proved. At these sizes the interpolation is far beyond practical
computation (mumbai says the same of its extractor; an honest word is decoded by interpolation
alone, `fastStacks`): the decoder is explicit and polynomial-time, not fast.
-/

set_option linter.unusedSectionVars false

namespace Compose

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir (iList mem_iList IsInterleavedCodeword IsClose AgreeOn)
open LeanVM.Protocol.Whir.Sound (LevelCode encStack isInterleavedCodeword_encStack)
open LeanVM.Extraction LeanVM.Extraction.PruneProofs

/-! ## A coefficient array's encoding is a codeword -/

/-- **The encoding of an array of `2^κ` coefficients is a codeword** of level 0's code: it is
lane `0` of the stack all of whose lanes are the array. -/
theorem encoding_mem_code {μ R : ℕ} (hμ : laneBits ≤ μ) (h : μ - laneBits + R ≤ 64)
    {c : Array K} (hc : c.size = 2 ^ (μ - laneBits)) :
    (fun v : Fin (2 ^ (μ - laneBits + R)) ↦ ofK ((novelFwd (μ - laneBits) R c).getD v 0)) ∈
      ReedSolomon.code (Whir.domain (μ - laneBits) R h) (2 ^ (μ - laneBits)) := by
  set q : Column μ := ⟨stackOf μ (List.replicate (2 ^ Whir.initialFold) c)⟩
  have hl : lanesOf q.values = List.replicate (2 ^ Whir.initialFold) c :=
    lanesOf_stackOf hμ (by simp) fun u hu ↦ by
      rw [List.getD_eq_getElem _ _ (by simpa using hu), List.getElem_replicate]
      exact hc
  have hlane : laneCoeffs q.values 0 = c := by
    rw [← getD_lanesOf q.values (show 0 < 2 ^ Whir.initialFold by decide), hl]
    simp
  have hrow : (fun v : Fin (2 ^ (μ - laneBits + R)) ↦ ofK ((novelFwd (μ - laneBits) R c).getD v 0))
      = encStack μ R q 0 := by
    funext v
    have hκ : μ - Whir.initialFold ≤ 64 := by simp only [Whir.initialFold, laneBits] at h ⊢; omega
    have h1 := Sound.encode_eq (R := R) q 0 v
    have h2 := NovelProofs.encode_eq_novelFwd (R := R) hκ q.values
      ((0 : Fin (2 ^ laneBits)) : ℕ) (v := v.val) (by exact v.isLt)
    have hlane' : laneCoeffs q.values ((0 : Fin (2 ^ laneBits)) : ℕ) = c := hlane
    show _ = Whir.enc (μ - laneBits) R (blockOf q 0) v
    rw [h1, h2, hlane']
    rfl
  rw [hrow]
  exact isInterleavedCodeword_encStack h q 0

/-- **Encoded arrays agreeing with a target are a list member**: rows of coefficient arrays of
`2^κ` entries whose encodings agree with the rows of `O` on a common set of at least `A`
columns form an interleaved codeword of `iList` at `A`. -/
theorem encodings_mem_iList {μ R A U : ℕ} (hμ : laneBits ≤ μ) (h : μ - laneBits + R ≤ 64)
    (cs : Fin U → Array K) (hc : ∀ u, (cs u).size = 2 ^ (μ - laneBits))
    (O : Fin U → Fin (2 ^ (μ - laneBits + R)) → E) (S : Finset (Fin (2 ^ (μ - laneBits + R))))
    (hS : A ≤ S.card) (hag : ∀ u, ∀ v ∈ S, O u v = ofK ((novelFwd (μ - laneBits) R (cs u)).getD v 0)) :
    (fun u (v : Fin (2 ^ (μ - laneBits + R))) ↦ ofK ((novelFwd (μ - laneBits) R (cs u)).getD v 0)) ∈
      iList (ReedSolomon.code (Whir.domain (μ - laneBits) R h) (2 ^ (μ - laneBits))) A O := by
  rw [mem_iList]
  exact ⟨fun u ↦ encoding_mem_code hμ h (hc u), S, hS, fun u v hv ↦ hag u v hv⟩

/-- The columns of a list of columns, as a set of `Fin n`, have its length when it has no
repetition and all are below `n`. -/
theorem card_finOfList {n : ℕ} {l : List ℕ} (hnd : l.Nodup) (hlt : ∀ v ∈ l, v < n) :
    (Finset.univ.filter fun v : Fin n ↦ v.val ∈ l).card = l.length := by
  rw [LaneProofs.card_filter_fin n (· ∈ l), ← List.toFinset_card_of_nodup hnd]
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hlt v h, h⟩⟩

/-! ## The prefixes the pruning keeps -/

/-- **At most `listMax` prefixes are kept after each lane** (`U ≥ 1`), for any level code of
level 0's shape whose threshold is at most the pruning's agreement. -/
theorem length_pruneUpTo_le_of (P₀ : LevelCode) {μ R A : ℕ} (hκ : P₀.κ = μ - laneBits)
    (hR : P₀.R = R) (hμ : laneBits ≤ μ) (hA : P₀.thr ≤ A) (W : Word) {U : ℕ} (hU1 : 1 ≤ U)
    (hU : U ≤ 2 ^ laneBits) :
    (pruneUpTo (μ - Whir.initialFold) R A W U).length ≤ P₀.listMax := by
  classical
  rcases P₀ with ⟨κ, R', η, h64, hκ1, hR1, hη, hagr⟩
  simp only at hκ hR
  subst hκ hR
  set P₀ : LevelCode := ⟨μ - laneBits, R', η, h64, hκ1, hR1, hη, hagr⟩
  set st := pruneUpTo (μ - Whir.initialFold) R' A W U
  -- the target: the word's first `U` lanes
  set O : Fin U → Fin (2 ^ (μ - laneBits + R')) → E :=
    fun u v ↦ laneOf W ⟨u.val, lt_of_lt_of_le u.isLt hU⟩ v
  -- a prefix's encodings
  set encw : List (Array K) × List ℕ → Fin U → Fin (2 ^ (μ - laneBits + R')) → E :=
    fun s u v ↦ ofK ((novelFwd (μ - laneBits) R' (s.1.getD u.val #[])).getD v.val 0)
  have hmem : ∀ s ∈ st, encw s ∈ iList P₀.code P₀.thr O := by
    intro s hs
    obtain ⟨hlen, hlist, hcols, hcard⟩ := mem_pruneUpTo hs
    refine encodings_mem_iList (U := U) hμ h64 (fun u : Fin U ↦ s.1.getD u.val #[])
      (fun u : Fin U ↦ size_of_mem_laneListAt (hlist u.val u.isLt)) O
      (Finset.univ.filter fun v ↦ v.val ∈ s.2) ?_ ?_
    · rw [card_finOfList]
      · exact hA.trans (hcard hU1)
      · rw [hcols]; exact nodup_commonCols ..
      · intro v hv
        rw [hcols, commonCols, List.mem_filter, List.mem_range] at hv
        exact hv.1
    · intro u v hv
      have hv' := (Finset.mem_filter.mp hv).2
      rw [hcols, commonCols, List.mem_filter, decide_eq_true_eq] at hv'
      have he := hv'.2 u u.isLt
      show ofK ((W v.val).reverse.getD u.val 0) =
        ofK ((novelFwd (μ - Whir.initialFold) R' (s.1.getD u.val #[])).getD v.val 0)
      rw [he]
      rfl
  have hinj : Set.InjOn encw ↑st.toFinset := by
    intro s hs s' hs' he
    rw [Finset.mem_coe, List.mem_toFinset] at hs hs'
    obtain ⟨hlen, hlist, hcols, -⟩ := mem_pruneUpTo hs
    obtain ⟨hlen', hlist', hcols', -⟩ := mem_pruneUpTo hs'
    have hu : ∀ u < U, s.1.getD u #[] = s'.1.getD u #[] := by
      intro u hu
      refine eq_of_novelFwd_eq (κ := μ - laneBits) (R := R') (by omega)
        (size_of_mem_laneListAt (hlist u hu)) (size_of_mem_laneListAt (hlist' u hu)) fun v hv ↦ ?_
      exact ofK_injective (congrFun (congrFun he ⟨u, hu⟩) ⟨v, hv⟩)
    have h1 : s.1 = s'.1 := by
      refine List.ext_getElem (hlen.trans hlen'.symm) fun u h1 h2 ↦ ?_
      rw [← List.getD_eq_getElem _ #[] h1, ← List.getD_eq_getElem _ #[] h2]
      exact hu u (hlen ▸ h1)
    exact Prod.ext h1 (by rw [hcols, hcols', h1])
  have hnd : st.Nodup := List.Nodup.of_map Prod.fst (nodup_pruneUpTo _ _ _ _ _)
  calc st.length = st.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ (iList P₀.code P₀.thr O).card :=
        Finset.card_le_card_of_injOn encw (by
          intro s hs
          exact hmem s (List.mem_toFinset.mp hs)) hinj
    _ ≤ P₀.listMax := P₀.card_iList_le O

/-- **Each lane's list has at most `listMax` elements**, for any level code of level 0's shape
whose threshold is at most the agreement (and the agreement within GS's range). -/
theorem length_laneListAt_le_of (P₀ : LevelCode) {μ R A : ℕ} (hκ : P₀.κ = μ - laneBits)
    (hR : P₀.R = R) (hμ : 7 ≤ μ) (hA : P₀.thr ≤ A) (hAn : A ≤ 2 ^ (μ - laneBits + R))
    (hcap : (2 ^ (μ - laneBits) - 1) * 2 ^ (μ - laneBits + R) < A * A) (W : Word) {u : ℕ}
    (hu : u < 2 ^ laneBits) :
    (laneListAt (μ - Whir.initialFold) R A W u).length ≤ P₀.listMax := by
  classical
  rcases P₀ with ⟨κ, R', η, h64, hκ1, hR1, hη, hagr⟩
  simp only at hκ hR
  subst hκ hR
  set P₀ : LevelCode := ⟨μ - laneBits, R', η, h64, hκ1, hR1, hη, hagr⟩
  set l := laneListAt (μ - Whir.initialFold) R' A W u
  set O : Fin 1 → Fin (2 ^ (μ - laneBits + R')) → E := fun _ v ↦ laneOf W ⟨u, hu⟩ v
  set encw : Array K → Fin 1 → Fin (2 ^ (μ - laneBits + R')) → E :=
    fun c _ v ↦ ofK ((novelFwd (μ - laneBits) R' c).getD v 0)
  have hκ1' : 1 ≤ μ - laneBits := by simp only [laneBits]; omega
  have hmem : ∀ c ∈ l, encw c ∈ iList P₀.code P₀.thr O := by
    intro c hc
    have hsize := size_of_mem_laneListAt hc
    obtain ⟨cp, hcp, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hc)
    obtain ⟨hdeg, hagree⟩ := LaneProofs.gsLaneAt_sound (κ := μ - laneBits) (R := R') hκ1' h64
      hAn hcap W u hcp
    refine encodings_mem_iList (by simp only [laneBits]; omega) h64 (fun _ ↦ toNovel (μ - laneBits) cp)
      (fun _ ↦ hsize) O
      (Finset.univ.filter fun v : Fin (2 ^ (μ - laneBits + R')) ↦
        cp.toPoly.eval (K.ofBits v.val) = laneSymbol W u v.val) ?_ ?_
    · rw [LaneProofs.card_filter_fin _ (fun v ↦ cp.toPoly.eval (K.ofBits v) = laneSymbol W u v)]
      exact hA.trans hagree
    · intro _ v hv
      have hv' := (Finset.mem_filter.mp hv).2
      show ofK ((W v.val).reverse.getD u 0) = _
      rw [LaneProofs.novelFwd_toNovel h64 hdeg v.isLt, hv']
      rfl
  have hinj : Set.InjOn encw ↑l.toFinset := by
    intro c hc c' hc' he
    rw [Finset.mem_coe, List.mem_toFinset] at hc hc'
    exact eq_of_novelFwd_eq (κ := μ - laneBits) (R := R') (by omega)
      (size_of_mem_laneListAt hc) (size_of_mem_laneListAt hc') fun v hv ↦
        ofK_injective (congrFun (congrFun he 0) ⟨v, hv⟩)
  calc l.length = l.toFinset.card := (List.toFinset_card_of_nodup (List.nodup_dedup _)).symm
    _ ≤ (iList P₀.code P₀.thr O).card :=
        Finset.card_le_card_of_injOn encw (by
          intro c hc
          exact hmem c (List.mem_toFinset.mp hc)) hinj
    _ ≤ P₀.listMax := P₀.card_iList_le O

/-! ## At the deployed codes -/

theorem code₀_shape {μ R : ℕ} (hw : Whir.Admissible μ R) :
    (WhirBridge.code₀ μ R).κ = μ - laneBits ∧ (WhirBridge.code₀ μ R).R = R := by
  obtain ⟨level, rest, hc⟩ := Sound.exists_ladder hw
  obtain ⟨-, -, hκ, hR, -⟩ := Whir.Params.deployed_spec_hyps hw hc
  exact ⟨hκ, hR⟩

/-- **The decoder keeps at most `listMax` prefixes after every lane.** -/
theorem length_pruneUpTo_le {μ R : ℕ} (hw : Whir.Admissible μ R) (W : Word) {U : ℕ}
    (hU1 : 1 ≤ U) (hU : U ≤ 2 ^ laneBits) :
    (pruneUpTo (μ - Whir.initialFold) R (johnsonThreshold μ R) W U).length ≤
      (WhirBridge.code₀ μ R).listMax := by
  obtain ⟨hμ, -⟩ := admissible_bounds hw
  exact length_pruneUpTo_le_of _ (code₀_shape hw).1 (code₀_shape hw).2
    (by simp only [laneBits]; omega) (thr_eq hw).le W hU1 hU

/-- **Each lane's list has at most `listMax` elements.** -/
theorem length_laneListAt_le {μ R : ℕ} (hw : Whir.Admissible μ R) (W : Word) {u : ℕ}
    (hu : u < 2 ^ laneBits) :
    (laneListAt (μ - Whir.initialFold) R (johnsonThreshold μ R) W u).length ≤
      (WhirBridge.code₀ μ R).listMax := by
  obtain ⟨hμ, hR⟩ := admissible_bounds hw
  obtain ⟨hA, hcap⟩ := johnsonThreshold_bounds hμ hR
  exact length_laneListAt_le_of _ (code₀_shape hw).1 (code₀_shape hw).2 (by omega)
    (thr_eq hw).le hA hcap W hu

/-- The same, at the certified `listHi`. -/
theorem length_prune_le {μ R : ℕ} (hw : Whir.Admissible μ R) (W : Word) {U : ℕ}
    (hU1 : 1 ≤ U) (hU : U ≤ 2 ^ laneBits) :
    (pruneUpTo (μ - Whir.initialFold) R (johnsonThreshold μ R) W U).length ≤
      (Whir.Params.certOf μ R 0).listHi :=
  (length_pruneUpTo_le hw W hU1 hU).trans (WhirBridge.listMax_le_listHi hw)

theorem length_laneList_le {μ R : ℕ} (hw : Whir.Admissible μ R) (W : Word) {u : ℕ}
    (hu : u < 2 ^ laneBits) :
    (laneListAt (μ - Whir.initialFold) R (johnsonThreshold μ R) W u).length ≤
      (Whir.Params.certOf μ R 0).listHi :=
  (length_laneListAt_le hw W hu).trans (WhirBridge.listMax_le_listHi hw)

/-! ## The lane decoder's shape -/

/-- **The lane decoder's shape** at `(μ, R)`: the points `n = 2^(μ−6+R)`, the agreement `A`, the
multiplicity `m` and weighted degree `W = m·A − 1` it runs at (`gsParamsFor`), the `Y`-degree
bound `ℓ = ⌊W/(k−1)⌋` (`k = 2^(μ−6)`) and the number `n·m(m+1)/2` of interpolation
conditions. -/
def gsShape (μ R : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let k := 2 ^ (μ - Whir.initialFold)
  let n := 2 ^ (μ - Whir.initialFold + R)
  let p := gsParamsFor k n (johnsonThreshold μ R)
  (n, johnsonThreshold μ R, p.interp.multiplicity, p.interp.weightedDegreeBound,
    p.interp.weightedDegreeBound / (k - 1), gsNumConstraints n p.interp.multiplicity)

/-- The decoder's lane parameters are `gsShape`'s. -/
theorem gsLaneAt_params (μ R : ℕ) (W : Word) (u : ℕ) :
    gsLaneAt (μ - Whir.initialFold) R (johnsonThreshold μ R) W u =
      CompPoly.GuruswamiSudan.decodeWithParams gsContext
        (gsParamsFor (2 ^ (μ - Whir.initialFold)) (2 ^ (μ - Whir.initialFold + R))
          (johnsonThreshold μ R))
        ⟨lanePoints (2 ^ (μ - Whir.initialFold + R)) W u⟩ :=
  rfl

/-- **The witness table's lane decoder** at `log_rows = 22` (`μ = 25`, rate `1/2`). -/
theorem gsShape_witness :
    gsShape 25 1 = (2 ^ 20, 741549, 1149, 852039800, 1625, 692767948800) := by
  decide +kernel

/-- **The quotient table's lane decoder** at `log_rows = 22` (`μ = 28`). -/
theorem gsShape_quotient :
    gsShape 28 1 = (2 ^ 23, 5933305, 522, 3097185209, 738, 1145070157824) := by
  decide +kernel

/-- **The wiring table's lane decoder** at `log_rows = 22` (`μ = 24`). -/
theorem gsShape_wiring :
    gsShape 24 1 = (2 ^ 19, 370765, 1425, 528340124, 2015, 532689715200) := by
  decide +kernel

end Compose
