-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM `mumbai` (https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, MIT OR
-- Apache-2.0): `buildTreeM_eq_withHash`, `Enc.stackWordFast_eq`, `simulateQ_buildTreeM`,
-- `stackWord`, `Column`, `KeccakCalls`.
import Bridge.Ntt
import PcsQuotient.Security
import Compose.WiringSetup
import LeanVM.Prover.Ntt
import Soundness.Hypotheses
import Bridge.Opening

/-!
# The circuit's commitment is the composition's setup

The statement's setup (`PcsQuotient.setupWith F`, `Circuit.indexRootWith`) commits the circuit's
wiring table with mumbai's prover pieces over the permutation `F`: the Merkle tree (`buildTreeM`) of
the stack's word computed by the NTT (`stackWordFast`). The composition (`formal/Compose`,
`stackSetup`, `wiringSetup`) commits a `Column` with mumbai's specification of the word
(`stackWord`) and Keccak-256 an oracle call (`buildTreeWithHash callKeccak256`). Here:

* `indexRootWith_eq`, **`setupWith_eq`**: `setupWith F` is the root of
  `buildTreeWithHash (keccak256With F) 19 (stackWord 24 wiringColumn)`, `wiringColumn` the circuit's
  wiring table as a `Column 24` (`columnOf`: its first `2^24` entries; no size hypothesis), for every
  monad and permutation;
* `indexTreeWith_eq`, `setupTreeWith_eq`: the same for the setup's tree (`setupTreeWith`);
* `wiringSetup_eq`: Compose's `wiringSetup 19 (stackWord 24 wiringColumn)` run with Keccak-256 the
  sponge over `F` and Keccak-f[1600] `F` (`Bridge.keccakCallsWith F`, `Opening.lean`) is
  `setupWith F`'s root as bytes;
* **`wiringColumn_tablePoly`** (`hq₀`): the table the wiring layout reads from `wiringColumn`
  (`WhirBridge.Layout.table`, entry `t` the column's entry `t`) holds the wiring polynomial: at F1's
  point of the cube point `x` (for the statement's basis, `IsCantorBasis`) its `tablePoly` is the
  point of `σ(x)`, given that `σ` has `2^24` entries (the circuit's `sigma.size`; `Bridge/Circuit`
  relates it to F0b's), from `Ntt.lean`'s `tablePoly_coefficients_cantor`.
-/

set_option linter.unusedSectionVars false

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Complete
open LeanVM.Prover (Tree buildTreeM buildTreeWithHash stackWordFast stackCodes)
open PcsQuotient PcsQuotient.Domain QuotientSecurity Finset OracleComp

namespace Bridge.Setup

/-! ## A stack as a `Column` -/

/-- **A stack as mumbai's `Column μ`**: its first `2^μ` entries, zero past its end. -/
def columnOf (μ : ℕ) (a : Array K) : Column μ := ⟨Vector.ofFn fun i : Fin (2 ^ μ) ↦ a.getD i 0⟩

theorem columnOf_getD (μ : ℕ) (a : Array K) {i : ℕ} (hi : i < 2 ^ μ) :
    (columnOf μ a).values.getD i 0 = a.getD i 0 := by
  simp [columnOf, Vector.getD, Array.getD_eq_getD_getElem?, hi]

theorem columnOf_toArray_getD (μ : ℕ) (a : Array K) {i : ℕ} (hi : i < 2 ^ μ) :
    (columnOf μ a).values.toArray.getD i 0 = a.getD i 0 := by
  simp [columnOf, Array.getD_eq_getD_getElem?, hi]

/-- **The NTT's word reads the stack's first `2^μ` entries only.** -/
theorem stackWordFast_congr (μ R : ℕ) (h6 : 6 ≤ μ) {a b : Array K}
    (h : ∀ i < 2 ^ μ, a.getD i 0 = b.getD i 0) : stackWordFast μ R a = stackWordFast μ R b := by
  have hsplit : 2 ^ μ = 2 ^ (μ - 6) * 64 := by
    rw [show (64 : ℕ) = 2 ^ 6 from rfl, ← pow_add]; congr 1; omega
  have hidx : ∀ v u : ℕ, v < 2 ^ (μ - 6) → u < 64 → v + 2 ^ (μ - 6) * u < 2 ^ μ := by
    intro v u hv hu
    rw [hsplit]
    calc v + 2 ^ (μ - 6) * u < 2 ^ (μ - 6) + 2 ^ (μ - 6) * u := by omega
      _ = 2 ^ (μ - 6) * (u + 1) := by ring
      _ ≤ 2 ^ (μ - 6) * 64 := Nat.mul_le_mul_left _ hu
  have hcodes : stackCodes μ R a = stackCodes μ R b := by
    simp only [stackCodes]
    congr 1
    funext u
    congr 2
    funext v
    exact h _ (hidx v u v.isLt u.isLt)
  funext p
  simp only [stackWordFast, stackWordFast.stackWordOf, hcodes]
  split
  · rfl
  · refine congrArg List.reverse (List.map_congr_left fun u hu ↦ ?_)
    refine congrArg (fun g ↦ encKAt (μ - 6) g p) (funext fun x ↦ ?_)
    exact h _ (hidx _ u (LeanVM.Protocol.Whir.bitsToNat_lt x) (List.mem_range.mp hu))

/-- **The NTT's word is mumbai's specification's** (`stackWord`) of the stack as a `Column`. -/
theorem stackWordFast_eq_columnOf (μ R : ℕ) (h6 : 6 ≤ μ) (h64 : μ ≤ 64) (a : Array K) :
    stackWordFast μ R a = stackWord μ (columnOf μ a) := by
  rw [stackWordFast_congr μ R h6 (b := (columnOf μ a).values.toArray)
    (fun i hi ↦ (columnOf_toArray_getD μ a hi).symm)]
  exact LeanVM.Prover.Enc.stackWordFast_eq h64 R _

/-! ## The setup -/

section With

variable {m : Type → Type} [Monad m] [LawfulMonad m] (F : KeccakState → m KeccakState)

/-- **The statement's WHIR commitment is mumbai's tree of `stackWord`**, Keccak-256 the sponge over
`F`. -/
theorem commitWith_eq (μ : ℕ) (h6 : 6 ≤ μ) (h64 : μ ≤ 64) (a : Array K) :
    commitWith F μ a = buildTreeWithHash (keccak256With F) (μ - 6 + 1) (stackWord μ (columnOf μ a)) := by
  rw [commitWith, stackWordFast_eq_columnOf μ 1 h6 h64, LeanVM.Prover.buildTreeM_eq_withHash]

/-- **A circuit's commitment** is the root of mumbai's tree of `stackWord` of its wiring table. -/
theorem indexRootWith_eq (c : Circuit) {μ : ℕ} (hμ : c.logRows + 2 = μ) (h6 : 6 ≤ μ)
    (h64 : μ ≤ 64) :
    c.indexRootWith F = (fun t : Tree ↦ t.root) <$>
      buildTreeWithHash (keccak256With F) (μ - 6 + 1) (stackWord μ (columnOf μ c.wiringTable)) := by
  subst hμ
  rw [Circuit.indexRootWith, commitWith_eq F _ h6 h64, map_eq_bind_pure_comp]
  rfl

end With

/-- The membership circuit has `2^L` rows (by definition: its fields are read off the builder's
run by projections, so this never runs the builder). -/
theorem membership_logRows (L : ℕ) : (membership L).logRows = L := rfl

/-- **The deployed circuit's wiring table as a `Column 24`.** -/
def wiringColumn : Column 24 := columnOf 24 (membership logRows).wiringTable

/-- **`setupWith F` is the root of mumbai's tree** of `stackWord 24 wiringColumn` at height `19`,
Keccak-256 the sponge over `F`, in any monad. -/
theorem setupWith_eq {m : Type → Type} [Monad m] [LawfulMonad m] (F : KeccakState → m KeccakState) :
    setupWith F = (fun t : Tree ↦ t.root) <$>
      buildTreeWithHash (keccak256With F) 19 (stackWord 24 wiringColumn) := by
  have hμ : (membership logRows).logRows + 2 = 24 := by rw [membership_logRows]; rfl
  have h := indexRootWith_eq (μ := 24) F (membership logRows) hμ (by norm_num) (by norm_num)
  rw [show (24 : ℕ) - 6 + 1 = 19 from rfl] at h
  exact h

/-- **A circuit's commitment tree** is mumbai's tree of `stackWord` of its wiring table. -/
theorem indexTreeWith_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    (F : KeccakState → m KeccakState) (c : Circuit) {μ : ℕ} (hμ : c.logRows + 2 = μ) (h6 : 6 ≤ μ)
    (h64 : μ ≤ 64) :
    c.indexTreeWith F =
      buildTreeWithHash (keccak256With F) (μ - 6 + 1) (stackWord μ (columnOf μ c.wiringTable)) := by
  subst hμ
  exact commitWith_eq F _ h6 h64 _

/-- **The setup's tree** (`setupTreeWith F`, whose Keccak-256 evaluations the extractor reads) is
mumbai's tree of `stackWord 24 wiringColumn` at height `19`, Keccak-256 the sponge over `F`. -/
theorem setupTreeWith_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    (F : KeccakState → m KeccakState) :
    setupTreeWith F = buildTreeWithHash (keccak256With F) 19 (stackWord 24 wiringColumn) := by
  have h := indexTreeWith_eq (μ := 24) F (membership logRows) rfl (by norm_num) (by norm_num)
  rw [show (24 : ℕ) - 6 + 1 = 19 from rfl] at h
  exact h

/-! ## In the composition's two-oracle model -/

theorem implH_keccakCallsWith {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState) :
    LeanVM.Protocol.Compile.Rom.implH (keccakCallsWith F) = keccak256With F := by
  funext x
  rfl

/-- **Compose's setup, the calls answered over `F`**, is the statement's setup's root, as bytes. -/
theorem wiringSetup_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    (F : KeccakState → m KeccakState) :
    simulateQ (keccakCallsWith F) (Compose.wiringSetup 19 (stackWord 24 wiringColumn)) =
      LeanVM.Rpm.Digest.toRpm <$> setupWith F := by
  rw [Compose.wiringSetup, simulateQ_map, simulateQ_buildTreeM, implH_keccakCallsWith,
    setupWith_eq, Functor.map_map]

/-! ## `Soundness.SetupBridge`: the wiring table's polynomial carries the deployed `σ` -/

/-- F0b's `σ` has `4 · 2^22 = 2^24` entries (`wiring_inv`'s invariant). -/
theorem pcsCircuit_sigma_size : PcsCircuit.membership.sigma.size = 2 ^ 24 := by
  obtain ⟨st, hst, hinv⟩ :=
    PcsCircuit.wiring_inv PcsCircuit.membership.rows PcsCircuit.membership_hsrc
  rw [PcsCircuit.membership_sigma, ← hst, hinv.sigma_size, PcsCircuit.membership_rows_size]
  rfl

/-- The statement's wiring table has `2^24` entries, given that its `σ` is F0b's. -/
theorem wiringTable_size (hσ : (membership 22).sigma = PcsCircuit.membership.sigma) :
    (membership logRows).wiringTable.size = 2 ^ 24 := by
  have hσ' : (membership logRows).sigma = PcsCircuit.membership.sigma := hσ
  rw [Circuit.wiringTable, Ntt.coefficients_size, Array.size_map, hσ', pcsCircuit_sigma_size]

theorem columnOf_toArray (μ : ℕ) (a : Array K) (ha : a.size = 2 ^ μ) :
    (columnOf μ a).values.toArray = a := by
  refine Array.ext (by simp [columnOf, ha]) fun i h1 h2 ↦ ?_
  simp [columnOf, Array.getD_eq_getD_getElem?, h2]

theorem bitsToNat_eq_idx {m : ℕ} (b : Fin m → Bool) :
    LeanVM.Protocol.Whir.bitsToNat b = Completeness.idx b := by
  rw [LeanVM.Protocol.Whir.bitsToNat, Completeness.idx]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  cases b k <;> simp

theorem getD_map_point (s : Array ℕ) {i : ℕ} (hi : i < s.size) :
    (s.map point).getD i 0 = point (s.getD i 0) := by
  simp [Array.getD_eq_getD_getElem?, hi]

/-- F4's wiring table function of a stack, entry by entry: the wiring layout's table at the cube
point's number. -/
theorem wiringFn_tabOf (q : Column (WhirBridge.wiringLayout 22).logN) (b : Fin (22 + 2) → Bool) :
    Compose.wiringFn 22 (Compose.tabOf (WhirBridge.wiringLayout 22) q) b =
      ofK ((WhirBridge.wiringLayout 22).table q (Completeness.idx b)) := by
  show ofK ((Vector.ofFn fun t : Fin (2 ^ 24) ↦ (WhirBridge.wiringLayout 22).table q t.val)[
    LeanVM.Protocol.Whir.bitsEquiv 24 b]) = _
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, LeanVM.Protocol.Whir.bitsEquiv_val,
    bitsToNat_eq_idx]

/-- `wiringColumn` at the wiring layout's stack size (`(wiringLayout 22).logN = 24`). -/
def wiringColumnL : Column (WhirBridge.wiringLayout 22).logN := wiringColumn

theorem wiringColumnL_getD {i : ℕ} (hi : i < 2 ^ 24) :
    wiringColumnL.values.getD i 0 = (membership logRows).wiringTable.getD i 0 :=
  columnOf_getD 24 _ hi

theorem cellOf_idx (x : Fin (22 + 2) → Bool) : QuotientSecurity.cellOf (Completeness.idx x) = x :=
  funext fun k ↦ Completeness.testBit_idx x k

/-- **`SetupBridge`** (`formal/EndToEnd/Soundness/Hypotheses.lean`), for constants whose basis is the
statement's (`hβ`), a Cantor basis (`h`), given that the statement's `σ` is F0b's (`hσ`,
`Bridge/Circuit`): the column `wiringColumn` is the statement's wiring table, and its table's
polynomial sends the point of every cell to the point of its successor under `deployedSigma`.
From the additive transform (`Ntt.tablePoly_coefficients_cantor`: `coefficients` of the `σ`-points
is the table of the polynomial taking them) and `deployedSigma_cellOf`. -/
theorem setupBridge (c : Compose.Reduce.Consts) (hβ : c.beta = betaAt)
    (h : Compose.IsCantor c.beta)
    (hσ : (membership 22).sigma = PcsCircuit.membership.sigma) : Soundness.SetupBridge c h := by
  have hσ' : (membership logRows).sigma = PcsCircuit.membership.sigma := hσ
  have hB : Ntt.CantorUpTo 24 := by
    rw [hβ] at h
    exact ⟨h.1, h.2⟩
  have hsz := wiringTable_size hσ
  have hvsz : ((membership logRows).sigma.map point).size = 2 ^ 24 := by
    rw [Array.size_map, hσ', pcsCircuit_sigma_size]
  -- The two bases' points are the statement's.
  have hpt : ∀ y : Fin (22 + 2) → Bool,
      (Compose.basisK c h).point y = (Ntt.cantorOf hB).point y := by
    intro y
    simp only [CantorBasis.point, Compose.basisK, Ntt.cantorOf, hβ]
  refine ⟨wiringColumnL, columnOf_toArray 24 _ hsz, fun x ↦ ?_⟩
  -- The table read through the wiring layout is the wiring table.
  have hfn : Compose.wiringFn 22 (Compose.tabOf (WhirBridge.wiringLayout 22) wiringColumnL) =
      fun b ↦ ofK ((membership logRows).wiringTable.getD (Completeness.idx b) 0) := by
    funext b
    have hb : Completeness.idx b < 2 ^ 24 := Completeness.idx_lt b
    rw [wiringFn_tabOf, Compose.wiring_table _ _ hb, wiringColumnL_getD hb]
  have hofK : ∀ a : K, ofK a = algebraMap K E a := fun _ ↦ rfl
  -- The left side: the transform's table at the cell's point.
  have hL := Ntt.tablePoly_coefficients_cantor hB (by decide) _ hvsz x
  have hx : Completeness.idx x < (membership logRows).sigma.size := by
    rw [hσ', pcsCircuit_sigma_size]; exact Completeness.idx_lt x
  rw [getD_map_point _ hx] at hL
  show (tablePoly (Compose.wiringFn 22 (Compose.tabOf (WhirBridge.wiringLayout 22) wiringColumnL))).eval
      ((Compose.basisE c h).point x) = (Compose.basisE c h).point (QuotientSecurity.deployedSigma x)
  rw [hfn, ← Compose.map_tablePoly, Compose.point_basisE, Compose.point_basisE, hofK, hofK,
    Polynomial.eval_map, Polynomial.eval₂_at_apply, hpt, hpt]
  congr 1
  refine hL.trans ?_
  -- The right side: `deployedSigma` on the cell's number.
  have hn : PcsCircuit.membership.sigma.getD (Completeness.idx x) 0 < 2 ^ 24 :=
    PcsCircuit.membership_sigma_lt _ (lt_of_lt_of_eq (Completeness.idx_lt x) (by rfl))
  conv_rhs => rw [← cellOf_idx x, QuotientSecurity.deployedSigma_cellOf (Completeness.idx_lt x)]
  rw [hσ', Ntt.point_eq_cantor hB (by decide) hn]
  rfl

end Bridge.Setup

/-! ## Axioms -/

/-- info: 'Bridge.Setup.stackWordFast_eq_columnOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.Setup.stackWordFast_eq_columnOf

/-- info: 'Bridge.Setup.indexRootWith_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.Setup.indexRootWith_eq

/-- info: 'Bridge.Setup.setupWith_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.Setup.setupWith_eq

/-- info: 'Bridge.Setup.setupTreeWith_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.Setup.setupTreeWith_eq

/-- info: 'Bridge.Setup.wiringSetup_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.Setup.wiringSetup_eq

/-- info: 'Bridge.Setup.wiringTable_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.Setup.wiringTable_size

/-- info: 'Bridge.Setup.setupBridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.Setup.setupBridge
