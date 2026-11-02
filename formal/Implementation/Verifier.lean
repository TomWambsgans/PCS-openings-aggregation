-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Implementation.Constants
import Implementation.Leaves

/-!
# The graph is the model's verifier

The end theorems of layer F5, for the calldata of a statement's 64 bytes `sb`, two roots
`r₁`, `r₂` and five values (`calldataOf`, as `crates/evm/src/quotient.rs` writes it), the index root
`idx` and any hash `H`, in any field `F` whose limbs are `F192`'s (`IsF192`, with `FrobOK`):

* `run_isSome_iff`: the contract reaches its calls of `PCS_OPEN` exactly when the product of the
  denominators is not zero, i.e. when every `1 + w_k(t)` and the denominator `Params.Accepts` asks
  nonzero are not zero (`check_eq`), at the challenges of the model's chain (`modelVals`);
* `run_words`: and then the words it hands `PCS_OPEN` are the three calls of the model's claims: the
  root word of `r₁`, the witness layout, one claim, the witness claim of
  `claims_iff_accepts_ofCantor`; the root word of the index root, the wiring layout, one claim, the
  wiring claim; the root word of `r₂`, the quotient layout, two claims, the quotient claim and the
  claim at the fixed point (each element as the word whose limbs `elem` reads);
* `run_accepts_iff`: so the contract reaches its calls with those claims true of tables `cW`, `cF`
  (a wiring table of `σ`), `cQ` exactly when no `1 + w_k(t)` vanishes and `Params.Accepts` holds of
  the polynomials the tables hold, at the model chain's challenges, on the protocol's parameters
  (`params`: the Cantor basis, coordinates and weights the graph carries).
-/

set_option linter.unusedSectionVars false

namespace Implementation

open QuotientRpm QuotientSecurity Program Emitted

local notation "SQ" => QuotientSecurity.sq

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] {limbs : F ≃ Limbs}
variable (hF : IsF192 limbs) (σ : Equiv.Perm (Fin (22 + 2) → Bool))

/-- **The protocol's parameters with the graph's constants**: the cells of the Cantor basis `beta`,
the wiring `σ`, the region's constants and weights (`membershipParams`). -/
noncomputable def params : Params F :=
  membershipParams (basis hF) le24 σ (bConst limbs) (cConst limbs) (basis_hb0 hF) (basis_hb hF)

theorem rootWord_eq (r : Bytes32) : rootWord r.toList = beNat (rootBytes r) := by
  have hl := r.length_toList
  rw [rootWord, rootBytes, beNat_append, leNat, leNat]
  simp only [List.length_reverse, List.length_drop, hl]
  norm_num

theorem checkId_eq' : checkId = some 419 := by decide +kernel

theorem node_419 : nodes[419]? = some (.mul 370 418) := by decide +kernel

theorem reduceIds_some : ∃ o, reduceIds = some o ∧ wordsOf o = outputs := by
  have h := reduceIds_eq
  cases e : reduceIds with
  | none => rw [e] at h; cases h
  | some o => rw [e] at h; exact ⟨o, rfl, Option.some.inj h⟩

variable (H : List UInt8 → Vector UInt8 32) (idx : Bytes32) (sb : Vector UInt8 64) (r₁ r₂ : Bytes32)
  (x0 x1 x2 x3 x4 : F)

local notation "CD" => calldataOf limbs sb r₁ r₂ [x0, x1, x2, x3, x4]
local notation "I" => modelVals H idx sb r₁ r₂ limbs x0 x1 x2 x3 x4

include hF

theorem wellFormed_calldataOf : WellFormed CD := by
  refine ⟨by rw [length_calldataOf]; rfl, ?_⟩
  rw [calldataOf_eq, List.take_left' length_selector]

theorem val_check (hfr : FrobOK limbs) :
    val limbs H idx.toList CD 419 = Formula.check limbs I := by
  have := checkId_spec (H := H) (idx := idx.toList) (cd := CD) hF 419 checkId_eq'
  rwa [leafVals_calldataOf] at this

/-- **The contract reaches its calls exactly when the product of the denominators is not zero.** -/
theorem run_isSome_iff (hfr : FrobOK limbs) :
    (run H idx CD).isSome ↔ Formula.check limbs I ≠ 0 := by
  have hnz : nonzero = [419] := by decide +kernel
  have hlt : (values H idx.toList CD).getD 419 0 < B192 := by
    rw [values_mul _ _ _ node_419]; exact mulE_lt _ _
  have hv := val_check hF H idx sb r₁ r₂ x0 x1 x2 x3 x4 hfr
  rw [val] at hv
  have key : (values H idx.toList CD).getD 419 0 = 0 ↔
      elem limbs ((values H idx.toList CD).getD 419 0) = 0 := by
    constructor
    · intro h0; rw [h0, elem_zero hF]
    · intro h0
      have := word_elem (limbs := limbs) ((values H idx.toList CD).getD 419 0)
      rw [h0, Nat.mod_eq_of_lt hlt] at this
      rw [← this]
      have hz := word_elem (limbs := limbs) 0
      rwa [elem_zero hF, Nat.zero_mod] at hz
  unfold run
  rw [if_pos (wellFormed_calldataOf hF sb r₁ r₂ x0 x1 x2 x3 x4), hnz]
  dsimp only
  simp only [List.all_cons, List.all_nil, Bool.and_true, bne_iff_ne, ne_eq]
  rw [← hv]
  split_ifs with hc
  · exact ⟨fun h => by simp at h, fun h => absurd (key.mp hc) h⟩
  · exact ⟨fun _ h0 => hc (key.mpr h0), fun _ => rfl⟩

/-- `sum_point`'s words are the fixed point of the model's sum claim. -/
theorem sumPointWords_elem :
    sumPointWords.map (elem limbs) = List.ofFn (sumPoint (22 + 2) (yConst limbs)) := by
  have hK := consts hF
  rw [sumPoint, ofFn_snoc, ofFn_snoc, ofFn_snoc, ofFn_snoc, ofFn_snoc, ofFn_snoc, sumPointWords]
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil, elem_one hF,
    elem_zero hF, hK.y0, hK.y1, List.ofFn_const]
  simp [List.replicate_succ, List.append_assoc]

/-- **The words the contract hands `PCS_OPEN` are the model's claims**: when it reaches its calls,
they are, back to back, the root word of `r₁`, the witness layout's id, one claim, the witness
claim (point, value); the root word of the index root, the wiring layout's id, one claim, the
wiring claim; the root word of `r₂`, the quotient layout's id, two claims, the quotient claim and
the claim at `sum_point` — each field element a word that `elem` reads as the model's. -/
theorem run_words (hfr : FrobOK limbs) (ws : List Nat) (h : run H idx CD = some ws) :
    ∃ wW wF wQ s, ws = [rootWord r₁.toList, 256 * 1 + 22, 1] ++ wW ++
        [rootWord idx.toList, 256 * 2 + 22, 1] ++ wF ++
        [rootWord r₂.toList, 256 * 3 + 22, 2] ++ wQ ++ sumPointWords ++ [s] ∧
      wW.map (elem limbs) = modelWitness (I).t (I).ρ (I).a ∧
      wF.map (elem limbs) = modelWiring (I).t (I).next ∧
      wQ.map (elem limbs) = modelQuotient (params hF σ) (I).α (I).β (I).γ (I).t (I).ρ (I).next
        (yConst limbs) (I).a ∧
      sumPointWords.map (elem limbs) = List.ofFn (sumPoint (22 + 2) (yConst limbs)) ∧
      elem limbs s = (params hF σ).target ![(I).s 0, (I).s 1, (I).s 2, (I).s 3, 1, 0, 0, 0] (I).γ /
        ((1 + yConst limbs) * (1 + yConst limbs ^ 2)) := by
  have hK := consts hF
  have hsome : (run H idx CD).isSome := by rw [h]; rfl
  have hnz := (run_isSome_iff hF H idx sb r₁ r₂ x0 x1 x2 x3 x4 hfr).mp hsome
  obtain ⟨o, ho, hwords⟩ := reduceIds_some
  have hspec := reduceIds_spec (H := H) (idx := idx.toList) (cd := CD) hF hfr
    (by rwa [leafVals_calldataOf]) o ho
  rw [leafVals_calldataOf] at hspec
  obtain ⟨hW, hF', hQ, hS⟩ := hspec
  unfold run at h
  rw [if_pos (wellFormed_calldataOf hF sb r₁ r₂ x0 x1 x2 x3 x4)] at h
  dsimp only at h
  split_ifs at h
  have hws := (Option.some.inj h).symm
  set vals := values H idx.toList CD
  refine ⟨o.witness.map (vals.getD · 0), o.wiring.map (vals.getD · 0),
    o.quotient.map (vals.getD · 0), vals.getD o.sum 0, ?_, ?_, ?_, ?_, sumPointWords_elem hF, ?_⟩
  · rw [hws, ← hwords]
    have h68 : cdWord CD (4 + 64) = rootWord r₁.toList := by
      rw [cdWord_slice _ _ (by rw [length_calldataOf]; omega),
        show 4 + 64 = 4 + 64 + 32 * 0 from rfl, drop_root sb r₁ r₂ x0 x1 x2 x3 x4 0 (by norm_num),
        rootWord_eq]
      rfl
    have h100 : cdWord CD (4 + 96) = rootWord r₂.toList := by
      rw [cdWord_slice _ _ (by rw [length_calldataOf]; omega),
        show 4 + 96 = 4 + 64 + 32 * 1 from rfl, drop_root sb r₁ r₂ x0 x1 x2 x3 x4 1 (by norm_num),
        rootWord_eq]
      rfl
    have e1 : (wordOf idx.toList CD vals ∘ Word.node) = fun x => vals.getD x 0 := by
      funext x; simp only [Function.comp, wordOf]
    have e2 : (wordOf idx.toList CD vals ∘ Word.const) = id := by
      funext x; simp only [Function.comp, wordOf, id]
    simp only [wordsOf, List.map_append, List.map_cons, List.map_nil, List.map_map, e1, e2,
      List.map_id]
    simp only [wordOf, h68, h100, List.append_assoc, List.cons_append, List.nil_append]
  · rw [List.map_map]
    exact hW.trans (witness_eq _)
  · rw [List.map_map]
    exact hF'.trans (wiring_eq _)
  · rw [List.map_map]
    exact hQ.trans (quotient_eq hK _ le24 σ (basis_hb0 hF) (basis_hb hF))
  · exact hS.trans (sum_eq _ le24 σ (basis_hb0 hF) (basis_hb hF) hK.scale)

/-- **The contract accepts exactly what the model accepts.** With `PCS_OPEN` attesting the claims
it is handed exactly when they hold of the tables `cW` (the witness table under `r₁`), `cF` (the
circuit's wiring table under the index root, a table of `σ`) and `cQ` (under `r₂`) — the claims
being the model's (`run_words`) — the contract reaches its calls and they hold exactly when no
`1 + w_k(t)` vanishes and `Params.Accepts` holds of the polynomials the tables hold
(`witnessOfTable`, `quotientsOfTable`), at the model chain's challenges and values
(`modelVals`). -/
theorem run_accepts_iff (hfr : FrobOK limbs) (cW : (Fin (22 + 1 + 1 + 1) → Bool) → F)
    (cF : (Fin (22 + 2) → Bool) → F)
    (hcF : ∀ x, (tablePoly cF).eval ((basis hF).point x) = (basis hF).point (σ x))
    (cQ : (Fin (22 + 2 + 1 + 1 + 1 + 1 + 1 + 1) → Bool) → F) :
    ((run H idx CD).isSome ∧
      (mle cW (Fin.cons (I).ρ (Fin.cons ((I).ρ ^ 2) (claimPoint 2 (22 + 1) (I).t)))
          = (∑ j, Params.opening (I).ρ j * (I).a j) / claimScale 2 (22 + 1) (I).t ∧
        mle cF (claimPoint 0 (22 + 2) (I).t) = (I).next / claimScale 0 (22 + 2) (I).t ∧
        mle cQ (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (claimPoint 0 (22 + 2 + 1 + 1) (I).t)
            ((params hF σ).vCells.eval (I).t /
              (params hF σ).claimDen (I).α (I).β (I).t (I).a (I).next)) (I).ρ)
              (yConst limbs / (1 + yConst limbs))) (yConst limbs ^ 2 / (1 + yConst limbs ^ 2)))
          = (params hF σ).claimValue (I).α (I).β (I).γ (I).t (I).ρ (I).a (I).next /
              ((1 + yConst limbs) * (1 + yConst limbs ^ 2)) /
            claimScale 0 (22 + 2 + 1 + 1) (I).t ∧
        mle cQ (sumPoint (22 + 2) (yConst limbs)) =
          (params hF σ).target ![(I).s 0, (I).s 1, (I).s 2, (I).s 3, 1, 0, 0, 0] (I).γ /
            ((1 + yConst limbs) * (1 + yConst limbs ^ 2)))) ↔
      ((∀ i : Fin (22 + 2 + 1 + 1), 1 + SQ^[(i : ℕ)] (I).t ≠ 0) ∧
        (params hF σ).Accepts ![(I).s 0, (I).s 1, (I).s 2, (I).s 3, 1, 0, 0, 0] (witnessOfTable cW)
          (quotientsOfTable (yConst limbs) cQ) (I).α (I).β (I).γ (I).t (I).a (I).next (I).ρ) := by
  have hK := consts hF
  have hiff := claims_iff_accepts_ofCantor (basis hF) le24 σ 8 _ _
    (membershipPub_hPub (basis hF) (bConst limbs) (cConst limbs) le24 (basis_hb0 hF) (basis_hb hF))
    cF hcF cW cQ (yConst limbs) hK.hY hK.hY2 ![(I).s 0, (I).s 1, (I).s 2, (I).s 3, 1, 0, 0, 0]
    (I).α (I).β (I).γ (I).t (I).ρ (I).next (I).a
  rw [run_isSome_iff hF H idx sb r₁ r₂ x0 x1 x2 x3 x4 hfr,
    check_eq hK (I) le24 σ (basis_hb0 hF) (basis_hb hF)]
  constructor
  · rintro ⟨hc, hcl⟩
    have ht : ∀ i : Fin (22 + 2 + 1 + 1), 1 + SQ^[(i : ℕ)] (I).t ≠ 0 := fun i h0 => by
      apply hc
      rw [Finset.prod_eq_zero (Finset.mem_range.mpr i.2) h0, zero_mul]
    exact ⟨ht, (hiff ht (right_ne_zero_of_mul hc)).mp hcl⟩
  · rintro ⟨ht, hacc⟩
    have hnz := hacc.2.2.1
    refine ⟨mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i hi => ht ⟨i, Finset.mem_range.mp hi⟩)
      hnz, (hiff ht hnz).mpr hacc⟩

end Implementation
