-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Instance.Prover

/-!
# `FSFresh`'s conditions on the deployed prover

`fsFresh_deployed_bits` (`Deployed/Fresh.lean`) asks of the prover `ofBytes Pb`:

* `hlong_Pb`: its leaves are longer than 192 bytes (`512`: the 64-word image);
* `hcK_Pb`: the witness table is committed before any challenge;
* `hn_Pb`: at least `242` Fiat–Shamir steps (`394`);
* `claimsAt_W`, `claimsAt_σ`, `claimsAt_Q`: at the openings' starts (`5`, `128`, `242` answers) the
  message begins with the claims' bytes, whose first coordinate is `ρ` (the witness claim's point
  starts `ρ, ρ², …`) or `t/(1+t)` (the wiring and quotient claims' `u_0`), read off the chain state
  that gives `ρ` (step `4`) or `t` (step `3`): the windows `cwD`;
* `hcw_deployed`: each window of a uniform state takes any value with probability at most `2^-191`
  (the low 192 bits of a uniform state are uniform in `E`; `t ↦ t/(1+t)` is at most 2-to-1);
* `hrow₀_Pb`: the witness table's first leaf takes any value with probability at most `2^-2368`
  (its row is the stack's first entries, free: `hidden_hδ` with an empty view).
-/

open OracleComp OracleSpec Polynomial Module QuotientSecurity QuotientSecurity.Hiding QuotientRpm
open QuotientZk.Joint QuotientZk.Deployed.Fresh
open QuotientZk.Deployed (Inp Out Msg Item Tbl Pos KSt)
open scoped ENNReal

namespace QuotientZk.Instance

set_option linter.unusedSectionVars false

section Fresh

variable {K E : Type} [Field K] [Field E] [Algebra K E] [DecidableEq E] [CharP E 2] [Fintype E]
  (rep : Rep K E) (P₀ : Params E) (gK : Fin 4 → K[X]) (van : K[X]) (stmt : Fin P₀.words → E)
  (Y : E) (TW : (Fin 4 → Fin 3 → K) → ιW → YW → K)
  (TQ : E × E × E → (Fin 4 → Fin 3 → K) → ιQ → YQ → K)

/-- `u_0 = t/(1+t)`, the wiring and quotient claims' first coordinate. -/
noncomputable def uOf (t : E) : E := t / (1 + t)

/-- **The claims' windows**: the first coordinate's 24 bytes, as a function of the chain state:
`ρ` for the witness opening, `t/(1+t)` for the wiring and quotient openings. -/
noncomputable def cwD : Fin 3 → Bytes32 → List UInt8 :=
  ![fun st => scalarLE (stateLimbs st),
    fun st => scalarLE (rep.limbs (uOf (rep.limbs.symm (stateLimbs st)))),
    fun st => scalarLE (rep.limbs (uOf (rep.limbs.symm (stateLimbs st))))]

theorem hlong_Pb (R : Renderer K E) :
    ∀ s h k x, 192 < ((Pb rep P₀ gK van stmt Y TW TQ R).rowFn s h k x).length := by
  intro s h k x
  rw [Pb_rowFn]
  obtain rfl | rfl : k = 0 ∨ k = 1 := by fin_cases k <;> simp
  · rw [PbRow_zero, length_rowBytes rep (by rw [lanes_W]; norm_num)]
    norm_num
  · rw [PbRow_one, length_rowBytes rep (by rw [lanes_Q]; norm_num)]
    norm_num

theorem hcK_Pb (R : Renderer K E) : (Pb rep P₀ gK van stmt Y TW TQ R).cK 0 = 0 := by
  rw [Pb_cK, PbcK_zero]

theorem hn_Pb (R : Renderer K E) : 242 ≤ (Pb rep P₀ gK van stmt Y TW TQ R).n := by
  rw [Pb_n]
  norm_num [nRaw]

/-! ### The claims at the openings' starts -/

theorem claimMsg_five (c : DChal E) (v : Vals E) :
    claimMsg rep P₀ stmt Y 5 c v =
      [.bytes (scalarsLE rep (Implementation.modelWitness c.1.1.2 c.1.2 v.1))] := by
  unfold claimMsg
  exact if_pos rfl

theorem claimMsg_wiring (c : DChal E) (v : Vals E) :
    claimMsg rep P₀ stmt Y 128 c v =
      [.bytes (scalarsLE rep (Implementation.modelWiring c.1.1.2 v.2))] := by
  unfold claimMsg
  rw [if_neg (by norm_num), if_pos rfl]

theorem claimMsg_quotient (c : DChal E) (v : Vals E) :
    claimMsg rep P₀ stmt Y 242 c v =
      [.bytes (scalarsLE rep
        (Implementation.modelQuotient P₀ c.1.1.1.1 c.1.1.1.2.1 c.1.1.1.2.2 c.1.1.2 c.1.2 v.2 Y v.1 ++
          Implementation.modelSum P₀ stmt c.1.1.1.2.2 Y))] := by
  unfold claimMsg
  rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]

theorem take_scalarsLE (x : E) (l : List E) :
    (scalarsLE rep (x :: l)).take 24 = scalarLE (rep.limbs x) := by
  unfold scalarsLE
  rw [List.flatMap_cons]
  exact List.take_left' (length_scalarLE _)

theorem ofBytes_msgFn {S : Type} (P : Proto S (List UInt8) Out Msg Tbl Pos) :
    (DRpm.ofBytes P).msgFn = P.msgFn := rfl

theorem msgFn_eq (R : Renderer K E) (s : RandD K) (h : List Out) :
    (DRpm.ofBytes (Pb rep P₀ gK van stmt Y TW TQ R)).msgFn s h =
      claimMsg rep P₀ stmt Y h.length (chOf rep.limbs h)
        (avail h.length (jv rep P₀ gK van Y TW TQ (chOf rep.limbs h) s)).1 ++
      R h.length h (avail h.length (jv rep P₀ gK van Y TW TQ (chOf rep.limbs h) s)) := by
  rw [ofBytes_msgFn, Pb_msgFn]
  rfl

/-- **The witness opening's claims read `ρ`** (chain state `4`). -/
theorem claimsAt_W (R : Renderer K E) :
    ClaimsAt (DRpm.ofBytes (Pb rep P₀ gK van stmt Y TW TQ R)) 5 4 (cwD rep 0) := by
  intro s h hh
  rw [msgFn_eq, hh, claimMsg_five]
  refine ⟨_, _, rfl, ?_⟩
  rw [modelWitness_eq, pointW, List.ofFn_succ, Fin.cons_zero, List.cons_append, take_scalarsLE]
  show scalarLE (rep.limbs (rep.limbs.symm (stateLimbs (h.getD 4 default).1))) = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem head_claimPoint (t : E) (n : ℕ) :
    claimPoint 0 (n + 1) t 0 = uOf t := by
  simp [claimPoint, uOf]

/-- **The wiring opening's claims read `t`** (chain state `3`). -/
theorem claimsAt_σ (R : Renderer K E) :
    ClaimsAt (DRpm.ofBytes (Pb rep P₀ gK van stmt Y TW TQ R)) 128 3 (cwD rep 1) := by
  intro s h hh
  rw [msgFn_eq, hh, claimMsg_wiring]
  refine ⟨_, _, rfl, ?_⟩
  unfold Implementation.modelWiring
  rw [List.ofFn_succ, List.cons_append, take_scalarsLE, head_claimPoint]
  rfl

theorem snoc4_zero {n : ℕ} (f : Fin (n + 1) → E) (a b c d : E) :
    (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc f a) b) c) d : Fin (n + 1 + 1 + 1 + 1 + 1) → E) 0 =
      f 0 := by
  simp [Fin.snoc]

/-- **The quotient opening's claims read `t`** (chain state `3`). -/
theorem claimsAt_Q (R : Renderer K E) :
    ClaimsAt (DRpm.ofBytes (Pb rep P₀ gK van stmt Y TW TQ R)) 242 3 (cwD rep 2) := by
  intro s h hh
  rw [msgFn_eq, hh, claimMsg_quotient]
  refine ⟨_, _, rfl, ?_⟩
  rw [modelQuotient_eq, pointQ, List.ofFn_succ, List.append_assoc, List.cons_append,
    List.cons_append, take_scalarsLE, snoc4_zero, head_claimPoint]
  rfl

/-! ### The windows' min-entropy -/

theorem card_uOf_le (e : E) : (Finset.univ.filter fun t : E => uOf t = e).card ≤ 2 := by
  classical
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  by_cases he : e = 0
  · subst he
    refine (Finset.card_le_card (t := {0, 1}) fun t ht => ?_).trans Finset.card_le_two
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, uOf, div_eq_zero_iff] at ht
    rcases ht with h | h
    · simp [h]
    · have : t = 1 := by linear_combination h - h2
      simp [this]
  · refine (Finset.card_le_card (t := {e / (1 + e)}) fun t ht => ?_).trans (by simp)
    have ht2 := (Finset.mem_filter.mp ht).2
    simp only [uOf] at ht2
    have h1t : 1 + t ≠ 0 := fun h => he (by rw [← ht2, h, div_zero])
    have ht' : t = e * (1 + t) := by rw [← ht2, div_mul_cancel₀ _ h1t]
    have h1e : 1 + e ≠ 0 := by
      intro h
      have he1 : e = 1 := by linear_combination h - h2
      rw [he1] at ht'
      have : (1 : E) = 0 := by linear_combination -ht'
      exact one_ne_zero this
    rw [Finset.mem_singleton, eq_div_iff h1e]
    linear_combination ht' + e * t * h2

theorem prob_limbs_le [SampleableType E] (hq : Fintype.card E = 2 ^ 192) (g : Limbs → List UInt8)
    (hg : ∀ y, (Finset.univ.filter fun t : E => g (rep.limbs t) = y).card ≤ 2) (y : List UInt8) :
    Pr{let u ← $ᵗ Out}[g (stateLimbs u.1) = y] ≤ ((2 : ℝ≥0∞) ^ 191)⁻¹ := by
  classical
  rw [SampleableType.prEvent_uniformSample_fst (fun b : Bytes32 => g (stateLimbs b) = y)]
  rw [show (fun b : Bytes32 => g (stateLimbs b) = y) =
      fun b => (fun p : Vector UInt8 8 × Limbs => g p.2 = y) (stateEquiv b) from rfl,
    SampleableType.prEvent_uniformSample_equiv stateEquiv (fun p => g p.2 = y),
    prEvent_uniform_snd (fun L : Limbs => g L = y)]
  rw [show (fun L : Limbs => g L = y) =
      fun L => (fun t : E => g (rep.limbs t) = y) (rep.limbs.symm L) by
        funext L; simp,
    SampleableType.prEvent_uniformSample_equiv rep.limbs.symm (fun t => g (rep.limbs t) = y),
    SampleableType.prEvent_uniformSample, hq]
  have h := HiddenLayout.natCast_div_le_natCast_div
    (a := (Finset.univ.filter fun t : E => g (rep.limbs t) = y).card) (b := 2 ^ 192) (c := 1)
    (d := 2 ^ 191) (by positivity) (by positivity) (by
      have := hg y
      calc _ ≤ 2 * 2 ^ 191 := Nat.mul_le_mul_right _ this
        _ = 1 * 2 ^ 192 := by norm_num)
  refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_))
  · push_cast; rfl
  · rw [Nat.cast_one, one_div, Nat.cast_pow, Nat.cast_ofNat]

/-- **The windows' min-entropy** (`hcw`): `2^-191`. -/
theorem hcw_deployed [SampleableType E] (hq : Fintype.card E = 2 ^ 192) :
    ∀ j y, Pr{let u ← $ᵗ Out}[cwD rep j u.1 = y] ≤ ((2 : ℝ≥0∞) ^ 191)⁻¹ := by
  classical
  intro j y
  fin_cases j
  · refine prob_limbs_le rep hq scalarLE (fun y => ?_) y
    refine le_trans (Finset.card_le_one.mpr fun a ha b hb => ?_) (by norm_num)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact rep.limbs.injective (scalarLE_injective (ha.trans hb.symm))
  all_goals
    refine prob_limbs_le rep hq (fun L => scalarLE (rep.limbs (uOf (rep.limbs.symm L))))
      (fun y => ?_) y
    simp only [Equiv.symm_apply_apply]
    by_cases hne : (Finset.univ.filter fun t : E => scalarLE (rep.limbs (uOf t)) = y).Nonempty
    · obtain ⟨t₀, ht₀⟩ := hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht₀
      refine le_trans (Finset.card_le_card fun t ht => ?_) (card_uOf_le (uOf t₀))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      exact rep.limbs.injective (scalarLE_injective (ht.trans ht₀.symm))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp

/-! ### The first witness leaf -/

variable [CharP K 2] [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K]
  [SampleableType E]

/-- The witness table's row `0` of a stack keeps `L - 3` elements of `K`. -/
theorem row0_le (h3 : finrank K E = 3) (base : ιW → YW → K) (r₀ : ιW → K) :
    Pr{let r ← $ᵗ (ιW → YW → K)}[Deployed.rowAt (codeAt rep Lw.logLane 0)
        (base + (Lw.toGadget okW).stackR r) = r₀] ≤
      ((Fintype.card K ^ (Fintype.card ιW - 3) : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  obtain ⟨u, hu, hu₀⟩ := free_one rep (ℓ := Lw.logLane) (by rw [logLane_W]; norm_num)
    (by rw [logLane_W]; norm_num) (Fin.elim0 : Fin 0 → ℕ) (fun i => i.elim0)
    (fun i => i.elim0) (by norm_num) 0 (by norm_num) (fun i => i.elim0)
  set enc : Fin 0 → YW → K := fun i => i.elim0
  have h := Deployed.hidden_hδ (E := E) (A := Unit) (Rd := Unit) h3 (Lw.toGadget okW).first
    (Lw.toGadget okW).stackR (Deployed.gadget_stackR_of_onFirst _) 0 (fun _ _ => rfl) 0 enc
    (codeAt rep Lw.logLane 0) 0 u hu.1 (fun x => x.elim0) hu₀ (by simp) (fun _ => base)
    (fun _ => r₀) () (viewMap (0 : (ιW → YW → K) →ₗ[K] Unit) (0 : ιW → E) enc 0)
  have hv : ∀ T, viewMap (0 : (ιW → YW → K) →ₗ[K] Unit) (0 : ιW → E) enc T =
      viewMap (0 : (ιW → YW → K) →ₗ[K] Unit) (0 : ιW → E) enc 0 := by
    intro T
    refine Prod.ext rfl (Prod.ext ?_ (funext fun i => i.elim0))
    funext y
    simp [viewMap, foldMap]
  simp only [hv, true_and, rowAt_zero, sub_zero] at h
  refine h.trans ?_
  have h1 : Pr{let r ← $ᵗ (ιW → YW → K)}[True] = 1 := by simp
  rw [h1, mul_one]

/-- **The first witness leaf's min-entropy** (`hrow₀`): `2^-2368`. -/
theorem hrow₀_Pb (h3 : finrank K E = 3) (hK : Fintype.card K = 2 ^ 64) (R : Renderer K E) :
    ∀ y, Pr{let s ← $ᵗ (RandD K)}[(DRpm.ofBytes (Pb rep P₀ gK van stmt Y TW TQ R)).rowFn s [] 0 0 =
      y] ≤ ((2 : ℝ≥0∞) ^ 2368)⁻¹ := by
  classical
  intro y
  set r₀ : ιW → K := preimage (fun r : ιW → K => (Sum.inl (rowBytes rep r) : Inp)) y
  have hinj : Function.Injective (fun r : ιW → K => (Sum.inl (rowBytes rep r) : Inp)) :=
    fun _ _ h => rowBytes_injective rep (Sum.inl_injective h)
  refine (prEvent_mono _ _ (fun s : RandD K => Deployed.rowAt (codeAt rep Lw.logLane 0)
      ((Lw.toGadget okW).stackD (TW s.1) + (Lw.toGadget okW).stackR s.2.1) = r₀)
      fun s hs => ?_).trans ?_
  · refine (preimage_eq hinj ?_).symm
    rw [← hs]
    show _ = Sum.inl ((Pb rep P₀ gK van stmt Y TW TQ R).rowFn s [] 0 0)
    rw [Pb_rowFn, PbRow_zero, stackV₁_eq]
    rfl
  · refine SampleableType.prEvent_uniformSample_prod_le_of_forall_fst _ fun m => ?_
    rw [SampleableType.prEvent_uniformSample_fst (fun r => Deployed.rowAt (codeAt rep Lw.logLane 0)
      ((Lw.toGadget okW).stackD (TW m) + (Lw.toGadget okW).stackR r) = r₀)]
    exact (row0_le rep h3 _ r₀).trans (delta_le hK ιW (by rw [card_ιW]))

end Fresh

end QuotientZk.Instance
