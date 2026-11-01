/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.

The soundness of this repository's opening check from leanerVM `mumbai`'s WHIR theorems
(https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, MIT OR Apache-2.0):
`stackedSpec` (`lean_vm/LeanVM/Protocol/Whir/Sound/Spec.lean`) with the deployed codes
(`deployed_spec_hyps`, `lean_vm/LeanVM/Protocol/Whir/Params/Deployed.lean`). `stackedAt` is
mumbai's `stackedGen` (`lean_vm/LeanVM/Protocol/EndToEnd/Sound/Assemble.lean`), restated here so
that this file does not import the leanVM end-to-end assembly.
-/
import WhirBridge.Opening
import LeanVM.Protocol.Whir.Params.Deployed
import LeanVM.Protocol.Whir.Complete.Opening

/-!
# The opening check is round-by-round sound

`openingSpec L R hw claims`: for every layout whose stack size and rate are admissible
(`15 ≤ log_n ≤ 28`, `1 ≤ R ≤ 4`) and **every** list of claims, a specification (mumbai's `Spec`,
`lean_vm/LeanVM/Protocol/Compile/Spec.lean`) of `openingCheck L R claims`, from
`OpeningDoom` (the level-0 commitment has the stack's shape and **every candidate** of its word
at level 0's Johnson threshold violates one of the claims), never returning in doom (the
postcondition is `False`), with

* every later group of challenges escaping doom with probability at most `εWhir = 2^-128`,
  discounted by the proof of work before it (`whirEps (deployedCodes μ R) config ≤ 2^-128`,
  certified for every admissible shape; at our three shapes it certifies at `2^-128` and not at
  `2^-129`, a kernel evaluation of `shapeOK`);
* the batching challenge `λ` (the lead) escaping with probability at most
  `eBatch J code₀ = (J − 1)·L₀/|E| ≤ (J − 1)·2^18/2^192` (`eBatch_le`): `0` for one claim,
  `2^-174` for two.

A `Spec` is the input of mumbai's Fiat-Shamir theorem (`Compile.Rom.romSound`), through
`Spec.toCert` once it is placed in a whole program; what that needs and what it does not cover
of this repository's transcript is `WhirBridge/Gaps.lean`.

`witnessLayout`, `wiringLayout`, `quotientLayout` transcribe `crates/quotient/src/protocol.rs`;
at `LOG_ROWS = 22` their stacks have `25`, `24` and `28` variables, and for every
`13 ≤ log_rows ≤ 22` all three are admissible at rate `1/2` and pass `Layout::new`'s assertions
(`layouts_ok`, decided).
-/

namespace WhirBridge

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open scoped ENNReal

/-! ## The deployed codes -/

/-- The deployed code of level `0` of the ladder `(μ, R)`. -/
noncomputable abbrev code₀ (μ R : ℕ) : LevelCode := LeanVM.Protocol.Whir.Params.deployedCodes μ R 0

/-- The per-group escape bound mumbai certifies for every admissible shape, `2^-128`. -/
noncomputable abbrev εWhir : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ 128

/-- **The stacked opening at an admissible shape**, with the deployed codes (mumbai's
`stackedGen`). -/
noncomputable def stackedAt {μ R : ℕ} (hw : Whir.Admissible μ R) (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine μ c.1) :
    Spec (verifyStackedOpening μ R claims)
      (fun h ↦ StackedPre μ R (code₀ μ R) claims (commits h)) (fun _ _ ↦ False) εWhir
      (eBatch claims.length (code₀ μ R)) 0 :=
  have hex := LeanVM.Protocol.Whir.Complete.exists_ladder hw
  have hc := hex.choose_spec.choose_spec.1
  have hd := LeanVM.Protocol.Whir.Params.deployed_spec_hyps hw hc
  stackedSpec claims hcl hc hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.2.1 hd.2.2.2.2.2.2 0

/-- The deployed per-group bound at an admissible shape. -/
theorem whirEps_le {μ R : ℕ} (hw : Whir.Admissible μ R) {config : List Whir.Level}
    (hc : Whir.ladder μ R = some config) :
    whirEps (LeanVM.Protocol.Whir.Params.deployedCodes μ R) config ≤ εWhir := by
  obtain ⟨q₀, rest, hc', -⟩ := LeanVM.Protocol.Whir.Complete.exists_ladder hw
  rw [hc] at hc'
  cases hc'
  exact (LeanVM.Protocol.Whir.Params.deployed_spec_hyps hw hc).2.2.2.2.2.2

/-! ## The opening check -/

/-- **The opening's doom** (mumbai's `StackedPre` on our claims): the level-0 commitment has the
stack's shape, and every candidate of its word at level 0's Johnson threshold violates at least
one claim. -/
def OpeningDoom (L : Layout) (R : ℕ) (claims : List Claim) (cs : List (ℕ × ℕ × Word)) : Prop :=
  StackedPre L.logN R (code₀ L.logN R) (stackClaims L claims) cs

/-- **The opening check is round-by-round sound**: for every admissible layout and every list of
claims, from `OpeningDoom` it never returns in doom; its first group (the batching challenge)
escapes with probability at most `eBatch J code₀`, every later one at most `2^-128`. -/
noncomputable def openingSpec (L : Layout) (R : ℕ) (hw : Whir.Admissible L.logN R)
    (claims : List Claim) :
    Spec (openingCheck L R claims) (fun h ↦ OpeningDoom L R claims (commits h))
      (fun _ _ ↦ False) εWhir (eBatch claims.length (code₀ L.logN R)) 0 :=
  (Spec.ite
    (fun _ ↦ (stackedAt hw (stackClaims L claims) (isMultiaffine_stackClaims L claims)).mono
      (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by rw [stackClaims, List.length_map]) le_rfl)
    (fun _ ↦ (Spec.fail (Pre := fun h ↦ OpeningDoom L R claims (commits h))
      (Post := fun (_ : Unit) _ ↦ False)).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl
        zero_le le_rfl)).congr (openingCheck_eq_ite L R claims).symm

/-! ## The numbers -/

theorem card_E_ennreal : (Fintype.card E : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 192 := by
  rw [LeanVM.Protocol.card_E, Nat.cast_pow, Nat.cast_ofNat]

/-- `2^a / 2^(a + c) = 2^-c`. -/
theorem two_pow_div_two_pow (a c : ℕ) : (2 : ℝ≥0∞) ^ a / 2 ^ (a + c) = (2 : ℝ≥0∞)⁻¹ ^ c := by
  rw [pow_add, ← ENNReal.inv_pow, div_eq_mul_inv, ENNReal.mul_inv (by simp) (by simp),
    ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

/-- **The batching challenge's escape**: at most `(J − 1)·2^18 / 2^192`. -/
theorem eBatch_le {μ R : ℕ} (hw : Whir.Admissible μ R) (J : ℕ) :
    eBatch J (code₀ μ R) ≤ (((J - 1) * 2 ^ 18 : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 192 := by
  obtain ⟨q₀, rest, hc, -⟩ := LeanVM.Protocol.Whir.Complete.exists_ladder hw
  have hL := (LeanVM.Protocol.Whir.Params.deployed_spec_hyps hw hc).2.2.2.2.1
  rw [eBatch, card_E_ennreal]
  gcongr

/-- One claim: the batching challenge cannot escape. -/
theorem eBatch_one {μ R : ℕ} (hw : Whir.Admissible μ R) : eBatch 1 (code₀ μ R) = 0 := by
  refine le_antisymm ((eBatch_le hw 1).trans ?_) zero_le
  simp

/-- Two claims (the quotient table's opening): at most `2^-174`. -/
theorem eBatch_two {μ R : ℕ} (hw : Whir.Admissible μ R) :
    eBatch 2 (code₀ μ R) ≤ (2 : ℝ≥0∞)⁻¹ ^ 174 := by
  refine (eBatch_le hw 2).trans (le_of_eq ?_)
  rw [show ((2 - 1) * 2 ^ 18 : ℕ) = 2 ^ 18 from rfl, Nat.cast_pow, Nat.cast_ofNat,
    show (192 : ℕ) = 18 + 174 from rfl, two_pow_div_two_pow]

/-- The lead is below the per-group bound for up to `2^46 + 1` claims. -/
theorem eBatch_le_εWhir {μ R : ℕ} (hw : Whir.Admissible μ R) {J : ℕ} (hJ : J ≤ 2 ^ 46 + 1) :
    eBatch J (code₀ μ R) ≤ εWhir := by
  refine (eBatch_le hw J).trans ?_
  have h : ((J - 1) * 2 ^ 18 : ℕ) ≤ 2 ^ 64 := by
    calc (J - 1) * 2 ^ 18 ≤ 2 ^ 46 * 2 ^ 18 := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ 64 := by norm_num
  calc ((((J - 1) * 2 ^ 18 : ℕ) : ℝ≥0∞)) / (2 : ℝ≥0∞) ^ 192
      ≤ ((2 ^ 64 : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 192 := by gcongr
    _ = εWhir := by
      rw [Nat.cast_pow, Nat.cast_ofNat, show (192 : ℕ) = 64 + 128 from rfl,
        two_pow_div_two_pow]

/-- Level 0's list bound is its certificate's `listHi` (as in mumbai's `deployed_spec_hyps`). -/
theorem listMax_le_listHi {μ R : ℕ} (h : Whir.Admissible μ R) :
    (code₀ μ R).listMax ≤ (LeanVM.Protocol.Whir.Params.certOf μ R 0).listHi := by
  obtain ⟨q₀, rest, hc, -⟩ := LeanVM.Protocol.Whir.Complete.exists_ladder h
  have hok := LeanVM.Protocol.Whir.Params.shapeOK_all μ
    (by have := h.2.1; unfold Whir.maxLogStack at this; omega) R
    (by have := h.2.2.2; unfold Whir.maxLogInvRate at this; omega) h
  rw [LeanVM.Protocol.Whir.Params.shapeOK, hc] at hok
  simp only [Bool.and_eq_true] at hok
  have h0 := LeanVM.Protocol.Whir.Params.chkLevels_head hok.1
  rw [code₀, LeanVM.Protocol.Whir.Params.deployedCodes, LeanVM.Protocol.Whir.Params.codesOf,
    LeanVM.Protocol.Whir.Params.mkCode_eq h0]
  exact LeanVM.Protocol.Whir.Params.Cert.listMax_le h0

/-- **The candidates per commitment at our shapes** (rate `1/2`): level 0's Johnson list has at
most `9952` stacks at `log_n = 24` (wiring), `7908` at `25` (witness), `3564` at `28`
(quotient), below mumbai's global `2^18`. -/
theorem listMax_ours :
    (code₀ 24 1).listMax ≤ 9952 ∧ (code₀ 25 1).listMax ≤ 7908 ∧ (code₀ 28 1).listMax ≤ 3564 := by
  refine ⟨(listMax_le_listHi (by decide)).trans (le_of_eq (by decide +kernel)),
    (listMax_le_listHi (by decide)).trans (le_of_eq (by decide +kernel)),
    (listMax_le_listHi (by decide)).trans (le_of_eq (by decide +kernel))⟩

/-! ## The layouts of `crates/quotient/src/protocol.rs` -/

/-- `cell_vars(log_rows) = log_rows + 2` (`protocol.rs:84-86`). -/
def cellVars (logRows : ℕ) : ℕ := logRows + 2

/-- `wiring_layout` (`protocol.rs:89-92`): the stack is the table. -/
def wiringLayout (logRows : ℕ) : Layout :=
  Layout.new (cellVars logRows) (cellVars logRows) (cellVars logRows) [(0, 2 ^ cellVars logRows)]

/-- `witness_layout` (`protocol.rs:95-98`): the four row polynomials, then their masks, sixteen
entries of the next chunk. -/
def witnessLayout (logRows : ℕ) : Layout :=
  Layout.new (cellVars logRows + 1) (cellVars logRows) (cellVars logRows + 1)
    [(0, 2 ^ cellVars logRows), (1, 16)]

/-- `Q_SPILL = PUBLIC_EXCESS + 64` (`protocol.rs:34-37`). -/
def qSpill : ℕ := 9216 + 64

/-- The chunks of `quotient_layout` (`protocol.rs:104-115`). -/
def quotientChunks (logRows : ℕ) : List (ℕ × ℕ) :=
  let n := 2 ^ cellVars logRows
  ((List.range 3).flatMap fun e ↦
      (16 * e, n) :: (List.range 3).map (fun digit ↦ (16 * e + 4 + digit, n)) ++
        [(16 * e + 7, qSpill)]) ++
    [(8, n), (9, 3 * n / 4 + 64)]

/-- `quotient_layout` (`protocol.rs:104-115`): `m + 6` variables, stacked in lanes of a quarter
chunk. -/
def quotientLayout (logRows : ℕ) : Layout :=
  Layout.new (cellVars logRows + 6) (cellVars logRows) (cellVars logRows + 4)
    (quotientChunks logRows)

/-- `LOG_ROWS` (`crates/quotient/src/circuit.rs:22`). -/
def logRows : ℕ := 22

/-- At `LOG_ROWS = 22`: the witness, wiring and quotient stacks have `25`, `24`, `28`
variables, `33`, `64`, `59` lanes. -/
theorem deployed_sizes :
    (witnessLayout logRows).logN = 25 ∧ (wiringLayout logRows).logN = 24 ∧
      (quotientLayout logRows).logN = 28 ∧
      (witnessLayout logRows).lanes = 33 ∧ (wiringLayout logRows).lanes = 64 ∧
      (quotientLayout logRows).lanes = 59 := by
  decide +kernel

/-- **The protocol's layouts are admissible** at rate `1/2` and pass `Layout::new`'s assertions,
for every `13 ≤ log_rows ≤ 22` (the deployed `22` the largest). -/
theorem layouts_ok : ∀ r, 13 ≤ r → r ≤ 22 →
    Whir.Admissible (witnessLayout r).logN logInvRate ∧
      Whir.Admissible (wiringLayout r).logN logInvRate ∧
      Whir.Admissible (quotientLayout r).logN logInvRate ∧
      Layout.NewOK (cellVars r + 1) (cellVars r) (cellVars r + 1)
        [(0, 2 ^ cellVars r), (1, 16)] ∧
      Layout.NewOK (cellVars r) (cellVars r) (cellVars r) [(0, 2 ^ cellVars r)] ∧
      Layout.NewOK (cellVars r + 6) (cellVars r) (cellVars r + 4) (quotientChunks r) := by
  decide +kernel

/-- **Our three openings at `LOG_ROWS = 22`**, round-by-round: the witness and wiring openings
(one claim each, lead `0`) and the quotient opening (two claims, lead at most `2^-174`), every
later group at most `2^-128`. -/
noncomputable def witnessSpec (claims : List Claim) :=
  openingSpec (witnessLayout logRows) logInvRate (layouts_ok 22 (by norm_num) le_rfl).1 claims

noncomputable def wiringSpec (claims : List Claim) :=
  openingSpec (wiringLayout logRows) logInvRate (layouts_ok 22 (by norm_num) le_rfl).2.1 claims

noncomputable def quotientSpec (claims : List Claim) :=
  openingSpec (quotientLayout logRows) logInvRate (layouts_ok 22 (by norm_num) le_rfl).2.2.1
    claims

end WhirBridge
