/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.

The per-group bound of leanVM's WHIR at `2^24 ..= 2^28` words, rate `1/2`, at its certified value
(`2^-128.93`) instead of `2^-128`, and this package's opening chain (`Sound.lean`'s `stackedAt`,
`openingSpec`; `Variant.lean`'s `variantSpec`, `variantCert`; `Family.lean`'s `famCert`,
`family_sound`; `LargeSound.lean`'s `family_sound_q`, `opening_sound_q`, `ours_sound_public_at`)
with that bound a parameter. The ladder check `chkLevelsQ` is leanerVM `mumbai`'s `chkLevels`
(https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, MIT OR Apache-2.0:
`lean_vm/LeanVM/Protocol/Whir/Params/Check.lean`, `FoldOK`, `OodOK`, `QueryOK`, `FinalOK`,
`nat_div_le`, `query_le`, `grind_le`, `eTail_le`, `chkLevels_sound`) at a rational threshold
`num · 2^-D`; the certificate of a family of statements with prefix-free roots (`RootsOK.cert`) is
mumbai's `anyCert` (`lean_vm/LeanVM/Protocol/EndToEnd/Sound/Statements.lean`) for any family.
-/
import WhirBridge.LargeSound

/-!
# The exact per-group bound at `2^24 ..= 2^28`

mumbai certifies every admissible WHIR shape at `2^-128` per group of challenges
(`shapeOK_all`); at the shapes `2^24 ..= 2^28`, rate `1/2`, its own certificates give more: the
weakest group is at `2^-128.95` (`review/whir_params.py --large`, level 0's query group at
`2^26`). This file states that bound and carries it through the opening.

* **`εExact = 269 · 2^-137`** (`≈ 0.5254 · 2^-128 = 2^-128.93`). The smallest `num` at `D = 137`
  that passes all five shapes is `266`; `269` is the brief's value and passes.
* **`chkLevelsQ num D cs i levels`**: mumbai's `chkLevels` with every group's `Nat` inequality at
  `num · 2^-D` instead of `2^-B` (the query groups after grinding's `2^-17`, the tail round's
  `2/|E|` checked too). It checks the escape bounds only: the ladder's arithmetic (`LadderArith`)
  is mumbai's (`deployed_spec_hyps`), unchanged. **`chkLevelsQ_sound`**:
  `levelEps (codesOf cs) i levels ≤ num · 2^-D`.
* **`chkQ_large`**: the check passes at `269 · 2^-137` on `certOf μ 1` and `largeLadder μ`,
  `24 ≤ μ ≤ 28` (kernel evaluation on the certificates' numbers and the ladders, as
  `shapeOK_large`). **`whirEps_le_exact`**, **`eBatch_le_exact`** (`(J − 1)·9952/2^192 ≤ 2^-132`
  for `J ≤ 2^46 + 1`).
* **The opening chain at a parameter `ε`**: `stackedAtE`, `openingSpecE`, `variantSpecE`,
  `variantCertE`, with two hypotheses in place of `εWhir`'s facts: the deployed codes meet `ε`
  (`hε`) and the batching lead is below `ε` (`hB`).
* **`RootsOK`, `RootsOK.cert`**: a program whose statements' roots are prefix-free histories of
  reads, with a certificate per root, has a certificate (mumbai's `anyCert`, `Family.lean`'s
  `famCert`, for any family). **`roots_sound`**: Fiat-Shamir soundness of such a family of
  openings (`family_sound_q`'s proof, on any family, at `ε`). `family_sound_qE` is it on
  `Family.lean`'s family; `Union.lean` uses it on the union of several shapes.
* **`ours_sound_public_atE`** (`ε` generic) and **`ours_sound_public_exact`** (at `εExact`): every
  public layout `Layout.new` accepts at `2^24 ..= 2^28`, with the bound
  `openingBoundAtE ε QO QA = (QA + QO) · (ε + 5 (QA + QO) / 2^256)`.
-/

namespace WhirBridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.Rom
open LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (commitSpec commitSpec_D retSplit_eq_none_of_after
  commitStack_after_ret boundary_append_of extractedFrom_eq reachable_drop after_drop esc_drop
  boundary_drop)
open OracleComp OracleSpec
open scoped ENNReal

attribute [local irreducible] instFintypeDigest instFintypeKState

/-! ## The bound -/

/-- **The per-group bound at `2^24 ..= 2^28`**, rate `1/2`: `269 · 2^-137 ≈ 0.5254 · 2^-128`,
`2^-128.93`. -/
noncomputable def εExact : ℝ≥0∞ := 269 * (2 : ℝ≥0∞)⁻¹ ^ 137

/-! ## The ladder check at a rational threshold -/

section Check

open LeanVM.Protocol.Whir.Params (certOf codesOf mkCode mkCode_eq card_E_cast nat_div_add_div
  deployedCodes)

/-- `a / d ≤ num · 2^-D` from `a · 2^D ≤ num · d` (mumbai's `nat_div_le` at `num · 2^-D`). -/
theorem nat_div_le_q {a d : ℕ} (num D : ℕ) (h : a * 2 ^ D ≤ num * d) :
    (a : ℝ≥0∞) / d ≤ (num : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ D := by
  refine ENNReal.div_le_of_le_mul ?_
  have h2 : (2 : ℝ≥0∞) ^ D * (2 : ℝ≥0∞)⁻¹ ^ D = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  calc (a : ℝ≥0∞) = (a : ℝ≥0∞) * 2 ^ D * (2 : ℝ≥0∞)⁻¹ ^ D := by rw [mul_assoc, h2, mul_one]
    _ ≤ ((num * d : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ D := by
        gcongr
        exact_mod_cast h
    _ = (num : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ D * d := by push_cast; ring

/-- The fold group of a level with `ℓ` folds at most `num · 2^-D` (mumbai's `FoldOK`). -/
def FoldOKQ (num D : ℕ) (c : Whir.Params.Cert) (ℓ : ℕ) : Prop :=
  (2 * c.listHi + 2 ^ (ℓ - 1) * c.excHi) * 2 ^ D ≤ num * 2 ^ 192

/-- The out-of-domain group at most `num · 2^-D` (mumbai's `OodOK`). -/
def OodOKQ (num D : ℕ) (c c' : Whir.Params.Cert) : Prop :=
  c'.listHi * c'.listHi * c.κ * 2 ^ D ≤ num * 2 ^ 192

/-- The query group with a next level at most `num · 2^-D` after the `2^-17` of grinding
(mumbai's `QueryOK`). -/
def QueryOKQ (num D : ℕ) (c c' : Whir.Params.Cert) (t : ℕ) : Prop :=
  ((c.thrHi - 1) ^ t * 2 ^ 192 + (t + 1) * c'.listHi * c.n ^ t) * 2 ^ (D - 17) ≤
    num * (c.n ^ t * 2 ^ 192)

/-- The final query group at most `num · 2^-D` after the `2^-17` of grinding (mumbai's
`FinalOK`). -/
def FinalOKQ (num D : ℕ) (c : Whir.Params.Cert) (t : ℕ) : Prop :=
  ((c.thrHi - 1) ^ t * 2 ^ 192 + t * c.n ^ t) * 2 ^ (D - 17) ≤ num * (c.n ^ t * 2 ^ 192)

instance {num D ℓ : ℕ} {c : Whir.Params.Cert} : Decidable (FoldOKQ num D c ℓ) := by
  unfold FoldOKQ; infer_instance

instance {num D : ℕ} {c c' : Whir.Params.Cert} : Decidable (OodOKQ num D c c') := by
  unfold OodOKQ; infer_instance

instance {num D t : ℕ} {c c' : Whir.Params.Cert} : Decidable (QueryOKQ num D c c' t) := by
  unfold QueryOKQ; infer_instance

instance {num D t : ℕ} {c : Whir.Params.Cert} : Decidable (FinalOKQ num D c t) := by
  unfold FinalOKQ; infer_instance

/-- The query part `(x/n)^t + y/|E|` below `num · 2^-D'` (mumbai's `query_le`). -/
theorem query_le_q {x n t y X Y : ℕ} (num D' : ℕ) (hn : 0 < n) (hx : x ≤ X) (hy : y ≤ Y)
    (h : (X ^ t * 2 ^ 192 + Y * n ^ t) * 2 ^ D' ≤ num * (n ^ t * 2 ^ 192)) :
    ((x : ℝ≥0∞) / n) ^ t + (y : ℝ≥0∞) / Fintype.card E ≤ (num : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ D' := by
  rw [card_E_cast]
  calc ((x : ℝ≥0∞) / n) ^ t + (y : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞)
      ≤ ((X : ℝ≥0∞) / n) ^ t + (Y : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞) := by
        gcongr
    _ = ((X ^ t : ℕ) : ℝ≥0∞) / (n ^ t : ℕ) + (Y : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞) := by
        rw [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow, ← div_eq_mul_inv]
        simp only [Nat.cast_pow]
    _ ≤ _ := by
        rw [nat_div_add_div (pow_pos hn t) (by positivity)]
        exact nat_div_le_q num D' h

/-- `2^-17·z ≤ num · 2^-D` from `z ≤ num · 2^-(D−17)` (mumbai's `grind_le`). -/
theorem grind_le_q {z : ℝ≥0∞} {num D : ℕ} (hD : 17 ≤ D)
    (h : z ≤ (num : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (D - 17)) :
    (2 : ℝ≥0∞)⁻¹ ^ Whir.queryGrindingBits * z ≤ (num : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ D := by
  rw [show Whir.queryGrindingBits = 17 from rfl]
  calc (2 : ℝ≥0∞)⁻¹ ^ 17 * z
      ≤ (2 : ℝ≥0∞)⁻¹ ^ 17 * ((num : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (D - 17)) := by gcongr
    _ = (num : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (17 + (D - 17)) := by rw [pow_add]; ring
    _ = _ := by rw [show 17 + (D - 17) = D by omega]

/-- The fold group of a checked level. -/
theorem eFold_le_q {num D : ℕ} {c : Whir.Params.Cert} (h : c.OK) {ℓ : ℕ}
    (hf : FoldOKQ num D c ℓ) :
    eFold (mkCode c) ℓ ≤ (num : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ D := by
  rw [eFold, mkCode_eq h, card_E_cast]
  refine le_trans ?_ (nat_div_le_q num D hf)
  gcongr
  · exact Whir.Params.Cert.listMax_le h
  · exact Whir.Params.Cert.mcaMax_le h

/-- The out-of-domain group of a checked level. -/
theorem eOod_le_q {num D : ℕ} {c c' : Whir.Params.Cert} (h : c.OK) (h' : c'.OK)
    (ho : OodOKQ num D c c') :
    eOod (mkCode c') (mkCode c).κ ≤ (num : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ D := by
  rw [eOod, mkCode_eq h, mkCode_eq h', card_E_cast]
  refine le_trans ?_ (nat_div_le_q num D ho)
  have hL := Whir.Params.Cert.listMax_le h'
  gcongr
  · rw [Nat.choose_two_right]
    calc (c'.toCode h').listMax * ((c'.toCode h').listMax - 1) / 2
        ≤ (c'.toCode h').listMax * ((c'.toCode h').listMax - 1) := Nat.div_le_self _ _
      _ ≤ c'.listHi * c'.listHi := Nat.mul_le_mul hL (by omega)
  · exact le_rfl

/-- The query group of a checked level, before the grinding discount. -/
theorem eQuery_le_q {num D : ℕ} {c c' : Whir.Params.Cert} (h : c.OK) (h' : c'.OK) {t : ℕ}
    (hq : QueryOKQ num D c c' t) :
    eQuery (mkCode c) (mkCode c') t ≤ (num : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (D - 17) := by
  rw [eQuery, mkCode_eq h, mkCode_eq h']
  exact query_le_q num (D - 17) (Nat.two_pow_pos _)
    (Nat.sub_le_sub_right (Whir.Params.Cert.thr_le h) 1)
    (Nat.mul_le_mul_left _ (Whir.Params.Cert.listMax_le h')) hq

/-- The final query group of a checked level, before the grinding discount. -/
theorem eQueryFinal_le_q {num D : ℕ} {c : Whir.Params.Cert} (h : c.OK) {t : ℕ}
    (hq : FinalOKQ num D c t) :
    eQueryFinal (mkCode c) t ≤ (num : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (D - 17) := by
  rw [eQueryFinal, mkCode_eq h]
  exact query_le_q num (D - 17) (Nat.two_pow_pos _)
    (Nat.sub_le_sub_right (Whir.Params.Cert.thr_le h) 1) le_rfl hq

/-- A tail round's escape `2/|E|`. -/
theorem eTail_le_q {num D : ℕ} (h : 2 * 2 ^ D ≤ num * 2 ^ 192) :
    eTail ≤ (num : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ D := by
  rw [eTail, card_E_cast]
  exact_mod_cast nat_div_le_q (a := 2) num D h

/-- **The check of a ladder at `num · 2^-D`** from level `i` against the certificates `cs`: each
level's certificate checks and bounds its groups' escapes by `num · 2^-D` (mumbai's `chkLevels`
at a rational threshold, without the ladder arithmetic, which is mumbai's). -/
def chkLevelsQ (num D : ℕ) (cs : ℕ → Whir.Params.Cert) : ℕ → List Whir.Level → Bool
  | _, [] => true
  | i, [l] => decide ((cs i).OK ∧ FoldOKQ num D (cs i) l.fold ∧
      FinalOKQ num D (cs i) l.queries ∧ 2 * 2 ^ D ≤ num * 2 ^ 192)
  | i, l :: l' :: rest => decide ((cs i).OK ∧ FoldOKQ num D (cs i) l.fold ∧
      OodOKQ num D (cs i) (cs (i + 1)) ∧ QueryOKQ num D (cs i) (cs (i + 1)) l.queries) &&
    chkLevelsQ num D cs (i + 1) (l' :: rest)

/-- A checked ladder's first certificate checks. -/
theorem chkLevelsQ_head {num D : ℕ} {cs : ℕ → Whir.Params.Cert} {i : ℕ} {l : Whir.Level}
    {rest : List Whir.Level} (h : chkLevelsQ num D cs i (l :: rest) = true) : (cs i).OK := by
  cases rest with
  | nil => exact (of_decide_eq_true h).1
  | cons l' rest =>
    simp only [chkLevelsQ, Bool.and_eq_true] at h
    exact (of_decide_eq_true h.1).1

/-- **A checked ladder has escapes at most `num · 2^-D`.** -/
theorem chkLevelsQ_sound {num D : ℕ} {cs : ℕ → Whir.Params.Cert} (hD : 17 ≤ D) :
    ∀ (levels : List Whir.Level) (i : ℕ), chkLevelsQ num D cs i levels = true →
      levelEps (codesOf cs) i levels ≤ (num : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ D
  | [], _, _ => by simp [levelEps]
  | [l], i, hc => by
    obtain ⟨hok, hf, hq, ht⟩ := of_decide_eq_true hc
    exact max_le (eFold_le_q hok hf)
      (max_le (grind_le_q hD (eQueryFinal_le_q hok hq)) (eTail_le_q ht))
  | l :: l' :: rest, i, hc => by
    simp only [chkLevelsQ, Bool.and_eq_true] at hc
    obtain ⟨⟨hok, hf, ho, hq⟩, hrest⟩ := And.imp_left of_decide_eq_true hc
    have hok' := chkLevelsQ_head hrest
    have ih := chkLevelsQ_sound hD (l' :: rest) (i + 1) hrest
    exact max_le (max_le (eFold_le_q hok hf) (eOod_le_q hok hok' ho))
      (max_le (grind_le_q hD (eQuery_le_q hok hok' hq)) ih)

/-- **The check passes at `269 · 2^-137`** on the deployed certificates and ladders of
`2^24 ..= 2^28` words, rate `1/2` (kernel evaluation on the certificates' numbers). -/
theorem chkQ_large :
    ∀ μ, largeMin ≤ μ → μ ≤ largeMax →
      chkLevelsQ 269 137 (certOf μ logInvRate) 0 (largeLadder μ) = true := by
  decide +kernel

/-- **The deployed per-group bound at `2^24 ..= 2^28`** is `εExact`. -/
theorem whirEps_le_exact {μ : ℕ} (h1 : largeMin ≤ μ) (h2 : μ ≤ largeMax)
    {config : List Whir.Level} (hc : Whir.ladder μ logInvRate = some config) :
    whirEps (deployedCodes μ logInvRate) config ≤ εExact := by
  rw [ladder_large μ h1 h2] at hc
  cases hc
  exact chkLevelsQ_sound (by norm_num) _ 0 (chkQ_large μ h1 h2)

/-- Level 0's list at these shapes is at most `9952`. -/
theorem largeList_le : ∀ μ, largeMin ≤ μ → μ ≤ largeMax → largeList μ ≤ 9952 := by
  decide

/-- **The batching lead at `2^24 ..= 2^28`**: `(J − 1)·L₀/2^192 ≤ 2^46 · 9952 / 2^192 ≤ 2^-132`,
below `εExact`, for `J ≤ 2^46 + 1` stack claims. -/
theorem eBatch_le_exact {μ J : ℕ} (h1 : largeMin ≤ μ) (h2 : μ ≤ largeMax) (hJ : J ≤ 2 ^ 46 + 1) :
    eBatch J (code₀ μ logInvRate) ≤ εExact := by
  rw [eBatch, card_E_cast, εExact]
  refine nat_div_le_q 269 137 ?_
  have hL := (listMax_large h1 h2).trans (largeList_le μ h1 h2)
  calc (J - 1) * (code₀ μ logInvRate).listMax * 2 ^ 137 ≤ 2 ^ 46 * 9952 * 2 ^ 137 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) hL)
    _ ≤ 269 * 2 ^ 192 := by norm_num

end Check

/-! ## The opening chain at a per-group bound `ε` -/

/-- **The stacked opening at an admissible shape**, at any per-group bound `ε` the deployed codes
meet (`stackedAt` with `ε` for `εWhir`). -/
noncomputable def stackedAtE {μ R : ℕ} (hw : Whir.Admissible μ R) (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine μ c.1) {ε : ℝ≥0∞}
    (hε : ∀ config, Whir.ladder μ R = some config →
      whirEps (LeanVM.Protocol.Whir.Params.deployedCodes μ R) config ≤ ε) :
    Spec (verifyStackedOpening μ R claims)
      (fun h ↦ StackedPre μ R (code₀ μ R) claims (commits h)) (fun _ _ ↦ False) ε
      (eBatch claims.length (code₀ μ R)) 0 :=
  have hex := LeanVM.Protocol.Whir.Complete.exists_ladder hw
  have hc := hex.choose_spec.choose_spec.1
  have hd := LeanVM.Protocol.Whir.Params.deployed_spec_hyps hw hc
  stackedSpec claims hcl hc hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.2.1 (hε _ hc) 0

/-- **The opening check is round-by-round sound at `ε`** (`openingSpec` with `ε` for `εWhir`). -/
noncomputable def openingSpecE (S : Stacking) (R : ℕ) (hw : Whir.Admissible S.logN R)
    (claims : List Claim) {ε : ℝ≥0∞}
    (hε : ∀ config, Whir.ladder S.logN R = some config →
      whirEps (LeanVM.Protocol.Whir.Params.deployedCodes S.logN R) config ≤ ε) :
    Spec (S.check R claims) (fun h ↦ OpeningDoom S R claims (commits h))
      (fun _ _ ↦ False) ε (eBatch (claims.length + S.extra.length) (code₀ S.logN R)) 0 :=
  (Spec.ite
    (fun _ ↦ (stackedAtE hw (S.claims claims) (S.isMultiaffine_claims claims) hε).mono
      (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by rw [Stacking.length_claims]) le_rfl)
    (fun _ ↦ (Spec.fail (Pre := fun h ↦ OpeningDoom S R claims (commits h))
      (Post := fun (_ : Unit) _ ↦ False)).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl
        zero_le le_rfl)).congr (S.check_eq_ite R claims).symm

section Variant

variable (L : Stacking) (R : ℕ) (hw : Whir.Admissible L.logN R) (claims : List Claim)
  (hJ : claims.length + L.extra.length ≤ 2 ^ 46 + 1) {ε : ℝ≥0∞}
  (hε : ∀ config, Whir.ladder L.logN R = some config →
    whirEps (LeanVM.Protocol.Whir.Params.deployedCodes L.logN R) config ≤ ε)
  (hB : ∀ J ≤ 2 ^ 46 + 1, eBatch J (code₀ L.logN R) ≤ ε)

/-- The variant's specification at `ε` (`variantSpec`): the root creates `OpeningDoom`, the
opening check follows (`openingSpecE`). -/
noncomputable def variantSpecE :
    Spec (variantProg L R claims) (fun _ ↦ False) (fun b _ ↦ b = false) ε 0 0 :=
  (commitSpec (fun _ h ↦ OpeningDoom L R claims (commits h)) L.logN R (hB _ hJ)).bind' fun _ ↦
    (openingSpecE L R hw claims hε).bind' fun _ ↦
      (Spec.ret (Post := fun b _ ↦ b = false) true).mono (fun _ h ↦ h.elim) (fun _ _ h ↦ h)
        le_rfl le_rfl le_rfl

/-- The variant's doom certificate at `ε`. -/
noncomputable def variantCertE : Cert (variantProg L R claims) :=
  (variantSpecE L R hw claims hJ hε hB).toCert

/-- Doom never holds at the empty history. -/
theorem variantSpecE_D_nil : ¬ (variantSpecE L R hw claims hJ hε hB).D [] [] := by
  intro hD
  have hs : (commitStack L.logN R).retSplit [] = none :=
    retSplit_eq_none_of_after (after_nil' _) fun a ↦ commitStack_ne_ret _ _ a
  have h1 := (Spec.bindD_none hs).1 hD
  unfold commitSpec at h1
  rw [Spec.bind_D] at h1
  rcases hl : Whir.ladder L.logN R with _ | c
  · have hs' : (Verifier.liftOption (Whir.ladder L.logN R)).retSplit [] = none := by rw [hl]; rfl
    exact (Spec.bindD_none hs').1 h1
  · have hs' : (Verifier.liftOption (Whir.ladder L.logN R)).retSplit [] = some (c, [], []) := by
      rw [hl]; rfl
    exact ((Spec.bindD_some hs').1 h1).1 rfl

/-- **The certificate's bound at `ε`**: every group's escape, discounted by the proof of work
before it, is at most `ε`. -/
theorem variantCertE_bound (h : List Ev) :
    (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * (variantCertE L R hw claims hJ hε hB).ε h ≤ ε := by
  by_cases hr : (variantProg L R claims).Reachable h
  · rw [min_eq_left ((movesOK_variant L R claims).grindBits_le hr)]
    exact Spec.toCert_bound _ (fun hD ↦ absurd hD (variantSpecE_D_nil L R hw claims hJ hε hB)) h
  · simp only [variantCertE, Spec.toCert_ε, hr, false_and, ↓reduceIte, mul_zero, zero_le]

/-- **Doom right after the root** is the opening's doom of the root's word. -/
theorem variantCertE_D_root {e : Ev} (hce : (commitStack L.logN R).after [e] = some (.ret ()))
    (hdoom : OpeningDoom L R claims (commits [e])) :
    (variantCertE L R hw claims hJ hε hB).D [e] := by
  obtain ⟨level, rest, W, hc, he⟩ := commitStack_after_ret hce
  rw [variantCertE, Spec.toCert_D]
  show Spec.bindD _ _ [] [e]
  refine (Spec.bindD_some (Prog.retSplit_of_after _ [e] [] hce)).2 ⟨fun _ ↦ ?_, ?_⟩
  · exact (commitSpec_D _ (hB _ hJ) hc [] e).2 (by simpa using hdoom)
  · exact Spec.start_D _ _ (by simpa using hdoom)

end Variant

/-! ## A program whose statements' roots are prefix-free -/

/-- **Prefix-free roots**: every statement's root is a root of `P` (mumbai's `RootOk`: reachable,
a boundary, no proof of work, no commitment) at which `P` continues as the statement's program
`Q x`, and two roots on one history are one statement's. -/
structure RootsOK {X : Type} (P : Prog Bool) (root : X → List Ev) (Q : X → Prog Bool) : Prop where
  after : ∀ x, P.after (root x) = some (Q x)
  ok : ∀ x, RootOk P (root x)
  inj : ∀ {x x' : X} {h : List Ev}, root x <+: h → root x' <+: h → x = x'

/-- Doom for every statement: past a statement's root, its certificate's doom on the rest. -/
def rootsD {X : Type} {Q : X → Prog Bool} (root : X → List Ev) (C : ∀ x, Cert (Q x))
    (h : List Ev) : Prop :=
  ∃ x, root x <+: h ∧ (C x).D (h.drop (root x).length)

open Classical in
/-- The escape bound for every statement: its certificate's past its root, `0` elsewhere. -/
noncomputable def rootsε {X : Type} {Q : X → Prog Bool} (root : X → List Ev)
    (C : ∀ x, Cert (Q x)) (h : List Ev) : ℝ≥0∞ :=
  if hx : ∃ x, root x <+: h then (C hx.choose).ε (h.drop (root hx.choose).length) else 0

namespace RootsOK

variable {X : Type} {P : Prog Bool} {root : X → List Ev} {Q : X → Prog Bool}
  (hR : RootsOK P root Q) (C : ∀ x, Cert (Q x))
include hR

theorem commits_root (x : X) : commits (root x) = [] := (hR.ok x).2.2.2.1

theorem D_iff (x : X) (h' : List Ev) : rootsD root C (root x ++ h') ↔ (C x).D h' := by
  constructor
  · rintro ⟨x', hx', hD⟩
    obtain rfl := hR.inj hx' (List.prefix_append _ _)
    simpa using hD
  · intro hD
    exact ⟨x, List.prefix_append _ _, by simpa using hD⟩

theorem ε_eq (x : X) (h' : List Ev) : rootsε root C (root x ++ h') = (C x).ε h' := by
  unfold rootsε
  split
  · rename_i hx
    rw [hR.inj hx.choose_spec (List.prefix_append _ _)]
    simp
  · rename_i hx
    exact absurd ⟨x, List.prefix_append _ _⟩ hx

omit hR in
theorem D_split {h : List Ev} (hD : rootsD root C h) :
    ∃ (x : X) (h' : List Ev), h = root x ++ h' ∧ (C x).D h' := by
  obtain ⟨x, ⟨h', rfl⟩, hD⟩ := hD
  exact ⟨x, h', rfl, by simpa using hD⟩

/-- **The certificate of every statement** (mumbai's `anyCert`, `Family.lean`'s `famCert`, for
any family with prefix-free roots). -/
noncomputable def cert : Cert P where
  D := rootsD root C
  ε := rootsε root C
  read := by
    intro h k e hr ha hD
    obtain ⟨x, h', rfl, hDx⟩ := RootsOK.D_split C hD
    have hax := hR.after x
    rw [List.append_assoc, hR.D_iff C]
    exact (C x).read e (reachable_drop hax (hR.commits_root x) hr h' rfl)
      (by rwa [after_drop hax] at ha) hDx
  grind := by
    intro h b k hr ha hD
    obtain ⟨x, h', rfl, hDx⟩ := RootsOK.D_split C hD
    have hax := hR.after x
    rw [List.append_assoc, hR.D_iff C]
    exact (C x).grind (reachable_drop hax (hR.commits_root x) hr h' rfl)
      (by rwa [after_drop hax] at ha) hDx
  commit := by
    intro h ht w k word hr ha hws hD
    obtain ⟨x, h', rfl, hDx⟩ := RootsOK.D_split C hD
    have hax := hR.after x
    rw [List.append_assoc, hR.D_iff C]
    exact (C x).commit word (reachable_drop hax (hR.commits_root x) hr h' rfl)
      (by rwa [after_drop hax] at ha) hws hDx
  group := by
    intro h p hr hb ha hp hD
    obtain ⟨x, h', rfl, hDx⟩ := RootsOK.D_split C hD
    have hax := hR.after x
    rw [esc_drop (h₀ := root x) (hR.commits_root x) (hR.D_iff C x), hR.ε_eq C]
    exact (C x).group (reachable_drop hax (hR.commits_root x) hr h' rfl)
      (boundary_drop hb) (by rwa [after_drop hax] at ha) hp hDx
  final := by
    intro h hr ha hD
    obtain ⟨x, h', rfl, hDx⟩ := RootsOK.D_split C hD
    have hax := hR.after x
    exact (C x).final (reachable_drop hax (hR.commits_root x) hr h' rfl)
      (by rwa [after_drop hax] at ha) hDx

theorem cert_D : (hR.cert C).D = rootsD root C := rfl

theorem grindBits_root (x : X) (h' : List Ev) : grindBits (root x ++ h') = grindBits h' := by
  rcases List.eq_nil_or_concat h' with rfl | ⟨h'', e, rfl⟩
  · rw [List.append_nil]; exact (hR.ok x).2.2.1
  · rw [List.concat_eq_append, ← List.append_assoc]
    simp [grindBits]

/-- **The certificate's bound**: the statements' bound. -/
theorem cert_bound {ε : ℝ≥0∞}
    (hC : ∀ x h, (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * (C x).ε h ≤ ε) (h : List Ev) :
    (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * (hR.cert C).ε h ≤ ε := by
  by_cases hx : ∃ x, root x <+: h
  · obtain ⟨x, h', rfl⟩ : ∃ x h', h = root x ++ h' := by
      obtain ⟨x, h', he⟩ := hx
      exact ⟨x, h', he.symm⟩
    show _ * rootsε root C _ ≤ _
    rw [hR.ε_eq C, hR.grindBits_root]
    exact hC x h'
  · show _ * rootsε root C _ ≤ _
    simp only [rootsε, hx, ↓reduceDIte, mul_zero, zero_le]

end RootsOK

/-! ## Fiat-Shamir soundness of a family of openings with prefix-free roots -/

/-- **The event of a family of openings**: for the root the proof's first two scalars encode,
every candidate of the word extracted for it violates one of the statement's claims, on the
statement's stacking (`FamDoomed`, for any family). -/
def RootsDoomed {X : Type} (Lx : X → Stacking) (Rx : X → ℕ) (cl : X → List Claim)
    (z : X × Proof) (c : KeccakCalls.QueryCache) : Prop :=
  ∀ r, rootOf z.2 = some r →
    ∀ q ∈ Candidates (Lx z.1).logN (Rx z.1) (code₀ (Lx z.1).logN (Rx z.1)).thr
        (extract (fun x ↦ c (.inl x)) r (rootHeight (Lx z.1).logN (Rx z.1)) (2 ^ laneFold)),
      ∃ c' ∈ cl z.1, ¬ StackClaim.Holds (Lx z.1).logN ((Lx z.1).weight c', c'.value) q

/-- **Fiat-Shamir soundness of a family of openings**: statements `x` on stackings `Lx x` at rates
`Rx x` with claims `cl x`, rooted at prefix-free histories of one program (`RootsOK`) at which it
continues as the opening `variantProg`, seeded by `σ`; an adversary of at most `QA` queries
outputs a statement and a proof; the verifier accepts while every candidate of the word extracted
for the proof's root violates one of the statement's claims with probability at most
`(QA + QV) · (ε + failBound σ (QA + QV))`, for any per-group bound `ε` the deployed codes meet
(`hε`) above the batching lead (`hB`). `family_sound_q`'s proof, on any family. -/
theorem roots_sound {X : Type} {P : Prog Bool} {root : X → List Ev}
    (Lx : X → Stacking) (Rx : X → ℕ) (cl : X → List Claim)
    (hR : RootsOK P root fun x ↦ variantProg (Lx x) (Rx x) (cl x))
    (σ : Seeds X) (hσ : ∀ x, σ.root x = root x)
    (hw : ∀ x, Whir.Admissible (Lx x).logN (Rx x))
    (hJ : ∀ x, (cl x).length + (Lx x).extra.length ≤ 2 ^ 46 + 1)
    (ε : ℝ≥0∞)
    (hε : ∀ x config, Whir.ladder (Lx x).logN (Rx x) = some config →
      whirEps (LeanVM.Protocol.Whir.Params.deployedCodes (Lx x).logN (Rx x)) config ≤ ε)
    (hB : ∀ x, ∀ J ≤ 2 ^ 46 + 1, eBatch J (code₀ (Lx x).logN (Rx x)) ≤ ε)
    (A : OracleComp KeccakCalls (X × Proof)) (QA : ℕ) (hA : IsTotalQueryBound A QA)
    (QV : ℕ) (hV : ∀ z, IsTotalQueryBound (verifierFam σ P z) QV) :
    Pr{let z ← romExperiment A (verifierFam σ P)}[
        z.1.2 = true ∧ RootsDoomed Lx Rx cl z.1.1 z.2] ≤
      (QA + QV : ℕ) * (ε + failBound σ (QA + QV)) := by
  refine romSound_of_imp P
    (hR.cert fun x ↦ variantCertE (Lx x) (Rx x) (hw x) (cl x) (hJ x) (hε x) (hB x)) σ
    (fun x ↦ by rw [hσ]; exact hR.ok x) ε
    (hR.cert_bound _ fun x h ↦ variantCertE_bound (Lx x) (Rx x) (hw x) (cl x) (hJ x) (hε x)
      (hB x) h)
    A QA hA QV hV (RootsDoomed Lx Rx cl) fun z c hv hbad ↦ ?_
  have hnode : nodeAt P (σ.root z.1) = variantProg (Lx z.1) (Rx z.1) (cl z.1) := by
    rw [hσ, nodeAt, hR.after]
    rfl
  rw [hnode] at hv
  obtain ⟨e, rest, hhist, hce⟩ :=
    extracted_root (L := Lx z.1) (R := Rx z.1) (claims := cl z.1) hv
  obtain ⟨r, rest', hr, hhist'⟩ := extracted_root_word (hw z.1) hv
  have he : e = Ev.commit (rootHeight (Lx z.1).logN (Rx z.1)) (2 ^ laneFold)
      (extract (fun x ↦ c (.inl x)) r (rootHeight (Lx z.1).logN (Rx z.1)) (2 ^ laneFold)) :=
    (List.cons.inj (hhist.symm.trans hhist')).1
  have hws := (Sound.after_extractedHistory _ _ hv).2
  rw [hhist] at hws
  unfold Doomed
  rw [hnode, hσ]
  refine ⟨root z.1 ++ [e], ?_, by rw [List.length_append]; omega, ?_, ?_⟩
  · rw [extractedFrom_eq _ _ _ _ _ _ hv, hhist]
    exact (List.prefix_append_right_inj _).mpr ⟨rest, rfl⟩
  · obtain ⟨level, rest', W, -, he⟩ := commitStack_after_ret hce
    rw [List.singleton_inj.1 he]
    exact boundary_append_of (h := []) trivial
  · refine (hR.D_iff _ z.1 [e]).2 (variantCertE_D_root (Lx z.1) (Rx z.1) (hw z.1) (cl z.1)
      (hJ z.1) (hε z.1) (hB z.1) hce
      ⟨shapeOK_root (Lx z.1) (Rx z.1) (hw z.1) hce
        fun ht w W he ↦ hws ht w W (he ▸ List.mem_cons_self ..), fun q hq ↦ ?_⟩)
    have hq' : q ∈ Candidates (Lx z.1).logN (Rx z.1) (code₀ (Lx z.1).logN (Rx z.1)).thr
        (extract (fun x ↦ c (.inl x)) r (rootHeight (Lx z.1).logN (Rx z.1)) (2 ^ laneFold)) := by
      rw [he] at hq
      simpa [LeanVM.Protocol.Whir.Sound.wordOf, commits] using hq
    obtain ⟨cl', hcl, hn⟩ := hbad r hr q hq'
    exact ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨cl', hcl, rfl⟩), hn⟩

/-! ## The family of `Family.lean`, at `ε` -/

/-- `Family.lean`'s statements have prefix-free roots. -/
theorem famRootsOK (L : Stacking) (R : ℕ) :
    RootsOK (famProgram L R) (famHistory (L := L)) fun x ↦ variantProg L R x.claims :=
  ⟨fun x ↦ after_famHistory x, fun x ↦ rootOk_famHistory x, fun hx hx' ↦ fam_eq_of_prefix hx hx'⟩

/-- **`family_sound_q` at a per-group bound `ε`**: the deployed codes meet `ε` (`hε`), the
batching lead is below it (`hB`). -/
theorem family_sound_qE {L : Stacking} {R : ℕ} (hw : Whir.Admissible L.logN R) (pre : Bytes)
    (ε : ℝ≥0∞)
    (hε : ∀ config, Whir.ladder L.logN R = some config →
      whirEps (LeanVM.Protocol.Whir.Params.deployedCodes L.logN R) config ≤ ε)
    (hB : ∀ J ≤ 2 ^ 46 + 1, eBatch J (code₀ L.logN R) ≤ ε)
    (A : OracleComp KeccakCalls (Stmt L × Proof)) (QA : ℕ) (hA : IsTotalQueryBound A QA)
    (QV : ℕ) (hV : ∀ z, IsTotalQueryBound (verifierFam (famSeeds L pre) (famProgram L R) z) QV) :
    Pr{let z ← romExperiment A (verifierFam (famSeeds L pre) (famProgram L R))}[
        z.1.2 = true ∧ FamDoomed L R z.1.1 z.2] ≤
      (QA + QV : ℕ) * (ε + failBound (famSeeds L pre) (QA + QV)) :=
  roots_sound (fun _ ↦ L) (fun _ ↦ R) Stmt.claims (famRootsOK L R) (famSeeds L pre)
    (fun _ ↦ rfl) (fun _ ↦ hw) (fun x ↦ x.short) ε (fun _ ↦ hε) (fun _ ↦ hB) A QA hA QV hV

/-! ## `opening::verify` at `ε` -/

/-- The bound of `opening_sound` at a per-group bound `ε` and the verifier's query count `QV`:
`(QA + QV) · (ε + 5 (QA + QV) / 2^256)`. -/
noncomputable def openingBoundAtE (ε : ℝ≥0∞) (QV QA : ℕ) : ℝ≥0∞ :=
  ((QA + QV : ℕ) : ℝ≥0∞) * (ε + ((5 * (QA + QV) : ℕ) : ℝ≥0∞) / 2 ^ 256)

theorem openingBoundAtE_εWhir (QV QA : ℕ) : openingBoundAtE εWhir QV QA = openingBoundAt QV QA :=
  rfl

/-- **`opening_sound_q` at a per-group bound `ε`** (the proof is `opening_sound_q`'s). -/
theorem opening_sound_qE (L : Layout) (hL : L.Valid) {R : ℕ} (hw : Whir.Admissible L.logN R)
    (ε : ℝ≥0∞)
    (hε : ∀ config, Whir.ladder L.logN R = some config →
      whirEps (LeanVM.Protocol.Whir.Params.deployedCodes L.logN R) config ≤ ε)
    (hB : ∀ J ≤ 2 ^ 46 + 1, eBatch J (code₀ L.logN R) ≤ ε)
    (QV : ℕ) (hV : ∀ z, IsTotalQueryBound
      (verifierFam (famSeeds L.stacking (openingPrefix L R)) (famProgram L.stacking R) z) QV)
    (A : OracleComp KeccakCalls ((Digest × Stmt L.stacking) × Proof)) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (ourVerifier L R)}[z.1.2 = true ∧ OpeningDoomed L R z.1.1 z.2] ≤
      openingBoundAtE ε QV QA := by
  set pre := openingPrefix L R
  set f : (Digest × Stmt L.stacking) × Proof → Stmt L.stacking × Proof := fun w ↦ (w.1.2, w.2)
  have hA' : IsTotalQueryBound (f <$> A) QA := (isQueryBound_map_iff A f QA _ _).mpr hA
  have hfam := family_sound_qE (L := L.stacking) hw pre ε hε hB (f <$> A) QA hA' QV hV
  rw [romExperiment_map, prEvent_map] at hfam
  have hbound : (QA + QV : ℕ) * (ε + failBound (famSeeds L.stacking pre) (QA + QV)) =
      openingBoundAtE ε QV QA := by
    rw [openingBoundAtE, failBound]
    simp [famSeeds]
  rw [hbound] at hfam
  refine le_trans ?_ hfam
  have hV' : (fun w ↦ verifierFam (famSeeds L.stacking pre) (famProgram L.stacking R) (f w)) =
      fun w ↦ seedComp pre w.1.2.claims >>= fun seed ↦
        runProofWithHash callKeccak256 callKeccakF1600 (variantProg L.stacking R w.1.2.claims)
          seed w.2 := funext fun w ↦ verifierFam_eq L R w
  have hO : ourVerifier L R = fun w ↦ if w.1.2.claims.isEmpty = false then
      (seedComp pre w.1.2.claims >>= fun seed ↦
        if rootOf w.2 = some w.1.1 then
          runProofWithHash callKeccak256 callKeccakF1600 (variantProg L.stacking R w.1.2.claims)
            seed w.2
        else pure false) else pure false := funext fun w ↦ ourVerifier_eq L R w
  rw [hV', hO]
  refine romExperiment_le_of_reject A (fun w ↦ seedComp pre w.1.2.claims)
    (fun w seed ↦ runProofWithHash callKeccak256 callKeccakF1600
      (variantProg L.stacking R w.1.2.claims) seed w.2)
    (fun w ↦ w.1.2.claims.isEmpty = false) (fun w ↦ rootOf w.2 = some w.1.1)
    (fun w cache ↦ OpeningDoomed L R w cache)
    (fun w cache ↦ FamDoomed L.stacking R (f w) cache) fun w cache _ hr hbad ↦ ?_
  intro r hr' q hq
  rw [hr'] at hr
  obtain rfl := (Option.some.inj hr).symm
  obtain ⟨cl, hcl, hne⟩ := hbad q hq
  exact ⟨cl, hcl, fun h ↦ hne ((L.holds_iff hL cl (w.1.2.wide cl hcl) q).1 h)⟩

/-- **Fiat-Shamir soundness of `opening::verify` on every public layout of `(table, height)`
chunks of `2^24 ..= 2^28` words** that `Layout::new` accepts, at rate `1/2`, at any per-group
bound `ε` the deployed codes meet (`hε`) above the batching lead (`hB`), with the shape's own
query count `QO = largeQueries log_n`: `openingBoundAtE ε QO QA`. -/
theorem ours_sound_public_atE (ε : ℝ≥0∞) (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ))
    (hS : NewOK vars logChunk logN chunks) (h1 : largeMin ≤ logN) (h2 : logN ≤ largeMax)
    (hε : ∀ config, Whir.ladder logN logInvRate = some config →
      whirEps (LeanVM.Protocol.Whir.Params.deployedCodes logN logInvRate) config ≤ ε)
    (hB : ∀ J ≤ 2 ^ 46 + 1, eBatch J (code₀ logN logInvRate) ≤ ε)
    (A : OracleComp KeccakCalls
      ((Digest × Stmt (Layout.new vars logChunk logN chunks).stacking) × Proof))
    (QA : ℕ) (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (ourVerifier (Layout.new vars logChunk logN chunks) logInvRate)}[
        z.1.2 = true ∧
          OpeningDoomed (Layout.new vars logChunk logN chunks) logInvRate z.1.1 z.2] ≤
      openingBoundAtE ε (largeQueries logN) QA :=
  opening_sound_qE _ (Layout.new_valid hS) (admissible_large h1 h2) ε hε hB _
    (isTotalQueryBound_fam_large _ h1 h2 _) A QA hA

/-- **At the exact bound**: `openingBoundAtE εExact QO QA`,
`(QA + QO) · (2^-128.93 + 5 (QA + QO) / 2^256)`. -/
theorem ours_sound_public_exact (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ))
    (hS : NewOK vars logChunk logN chunks) (h1 : largeMin ≤ logN) (h2 : logN ≤ largeMax)
    (A : OracleComp KeccakCalls
      ((Digest × Stmt (Layout.new vars logChunk logN chunks).stacking) × Proof))
    (QA : ℕ) (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (ourVerifier (Layout.new vars logChunk logN chunks) logInvRate)}[
        z.1.2 = true ∧
          OpeningDoomed (Layout.new vars logChunk logN chunks) logInvRate z.1.1 z.2] ≤
      openingBoundAtE εExact (largeQueries logN) QA :=
  ours_sound_public_atE εExact vars logChunk logN chunks hS h1 h2
    (fun _ hc ↦ whirEps_le_exact h1 h2 hc) (fun _ hJ ↦ eBatch_le_exact h1 h2 hJ) A QA hA

end WhirBridge

/-- info: 'WhirBridge.chkLevelsQ_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.chkLevelsQ_sound

/-- info: 'WhirBridge.whirEps_le_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.whirEps_le_exact

/-- info: 'WhirBridge.eBatch_le_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.eBatch_le_exact

/-- info: 'WhirBridge.roots_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.roots_sound

/-- info: 'WhirBridge.family_sound_qE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.family_sound_qE

/-- info: 'WhirBridge.ours_sound_public_atE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.ours_sound_public_atE

/-- info: 'WhirBridge.ours_sound_public_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.ours_sound_public_exact
