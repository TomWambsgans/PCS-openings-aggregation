-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Deployed.Fresh.Skel
import QuotientZk.Deployed.Main

/-!
# The honest prover's Fiat–Shamir inputs are fresh (`FSFresh`, proved)

**`fsFresh_deployed`**: for the deployed skeleton (`skel (deployedShape …)`, `2^22` rows) and a
prover `P` with

* **long rows** (`hrow`): every secret leaf's input is a Keccak-256 input of more than 192 bytes
  (a leaf image is a row of a codeword over `F64`: at least `40 · 64 · 8` bytes deployed);
* **the witness table first** (`hcK`): its leaves need no challenge (`cK 0 = 0`), and its first
  row has min-entropy (`hrow₀`: each value has probability at most `δ₀`; `2^-2368` from the hidden
  layout's random lanes);
* **claims that read a challenge** (`hclW`, `hclσ`, `hclQ`): at each opening's start (after 5, 128
  and 242 challenges) the prover's message begins with the claims, whose first 24 bytes are a
  window `cw j` of a chain state: `ρ`'s (the fifth state) for the witness opening, `t`'s (the
  fourth) for the wiring and quotient openings (`opening::iv` hashes each claim's point first:
  `ρ` and `t / (1 + t)`); each window takes a value with probability at most `εc` (`hcw`) over a
  uniform state (`2^-192` for `ρ`'s limbs, `2^-191` for `t / (1 + t)`, two states to a value);
* **these challenges among the protocol's** (`hn`): `242 ≤ P.n`;

the honest prover's Fiat–Shamir inputs are fresh but with probability

  `εFS = Q · 6 (|c₀| + Q) / 2^256 + 2 (|c₀| + Q) · 3 εc + |c₀| δ₀`,  `Q = skelBound`

(`≤ 2^-54` for `|c₀| ≤ 2^127`, `εc = 2^-191`, `δ₀ = 2^-2368`: `fsFresh_deployed_bits`).

**Why** (`Fresh/`): the run is tracked by `implB`, which raises *bad* when a fresh answer lands
where it should not (`Prob.lean`: probability at most `Q · 6 (|c₀| + Q) / 2^256` over all draws,
and `2 (|c₀| + Q) · 3 εc` at the fourth and fifth chain states). Off *bad*, every Fiat–Shamir input
is fresh (`trip_skel`): the chain's first input holds the witness table's root, fresh since its
first leaf is (unless the first row is an initial input: `|c₀| δ₀`); each later chain input begins
with the previous state; each opening's seed state is fresh, since the claims' window of a fresh
chain state is in no initial input and the seeds of the other openings have other digests; then
the duplex's capacity stays fresh, through the grinding.

**What is honest about the model**: the first Fiat–Shamir input of the reduction (label, statement,
index root) is public and the state after it may be in `c₀`; its freshness comes from the witness
root. Each opening's IV hashes public data (its prefix, and claims the verifier recomputes): its
freshness comes from the claims holding a challenge drawn after `c₀` was fixed. That is the
inherent `|c₀| · 2^-191` term: a distinguisher that guessed `t` before the proof had queried the
wiring opening's whole first draw. In the end theorem (`PcsQuotient.EndToEnd.zeroKnowledge_closed`)
the term is `0`: `c₀ = []` there (`fsFresh_setup_deployed_bits`, `Fresh/Setup.lean`: the Statement's
`realExperiment` starts from an empty permutation and its distinguisher queries only after the
proof); `epsFS`'s first argument then holds only the setup's `2^19` public rows, which the prover
hashes itself, not a distinguisher's queries. A pre-proof phase for the distinguisher is planned;
it will make this term nonzero.

**`zk_deployed_fs`**, **`zk_deployed_fs_bits`**: `zk_deployed_bits` with `FSFresh` discharged:
advantage at most `εFS + εhv + 2^-2200`, and `2^-54 + εhv + 2^-2200` at these sizes.
-/

open OracleComp OracleSpec QuotientRpm
open scoped ENNReal

namespace QuotientZk.Deployed.Fresh

set_option linter.unusedSectionVars false

open Classical in
/-- Averaging a bound that holds but on an event of the first draw. -/
theorem prEvent_bind_le_add {α β : Type} (mx : ProbComp α) (f : α → ProbComp β) (p : β → Prop)
    (q : α → Prop) (B : ℝ≥0∞) (h : ∀ a, Pr{let y ← f a}[p y] ≤ B + (if q a then 1 else 0)) :
    Pr{let y ← mx >>= f}[p y] ≤ B + Pr{let a ← mx}[q a] := by
  classical
  rw [prEvent_bind_eq_tsum, prEvent_eq_tsum_ite mx q]
  calc ∑' a, Pr{let y ← mx}[y = a] * Pr{let y ← f a}[p y]
      ≤ ∑' a, Pr{let y ← mx}[y = a] * (B + (if q a then 1 else 0)) :=
        ENNReal.tsum_le_tsum fun a => mul_le_mul_right (h a) _
    _ = ∑' a, Pr{let y ← mx}[y = a] * B + ∑' a, (if q a then Pr{let y ← mx}[y = a] else 0) := by
        rw [← ENNReal.tsum_add]
        refine tsum_congr fun a => ?_
        rw [mul_add]
        split_ifs <;> simp
    _ = B + ∑' a, (if q a then Pr{let y ← mx}[y = a] else 0) := by
        rw [ENNReal.tsum_mul_right, tsum_prEvent_eq_one, one_mul]

section General

variable {S : Type} [SampleableType S]

/-- **`FSFresh` for a skeleton of the deployed form.** -/
theorem fsFresh_skel (sh : Shape) (hsh : SkelOK sh) (P : Proto S Inp Out Msg Tbl Pos)
    (c₀ : List (Inp × Out)) (cw : Fin 3 → Bytes32 → List UInt8) (εc δ₀ : ℝ≥0∞)
    (hcw : ∀ j y, Pr{let u ← $ᵗ Out}[cw j u.1 = y] ≤ εc)
    (hrow₀ : ∀ y, Pr{let s ← $ᵗ S}[P.rowFn s [] 0 0 = y] ≤ δ₀)
    (hrow : ∀ s h k x, RowLike (P.rowFn s h k x)) (hcK : P.cK 0 = 0)
    (hclW : ClaimsAt P 5 4 (cw 0))
    (hclσ : ClaimsAt P (5 + openChals sh.witness) 3 (cw 1))
    (hclQ : ClaimsAt P (5 + openChals sh.witness + openChals sh.wiring) 3 (cw 2))
    (hn : 5 + openChals sh.witness + openChals sh.wiring ≤ P.n) :
    FSFresh P (skel sh) c₀
      ((skelBound sh : ℝ≥0∞) * (6 * ((c₀.length + skelBound sh : ℕ) : ℝ≥0∞) / 2 ^ 256) +
        2 * (((c₀.length + skelBound sh : ℕ) : ℝ≥0∞) * (3 * εc)) + c₀.length * δ₀) := by
  classical
  set K0 := c₀.map Prod.fst with hK0
  set Q := skelBound sh
  set B := (Q : ℝ≥0∞) * (6 * ((c₀.length + Q : ℕ) : ℝ≥0∞) / 2 ^ 256) +
    2 * (((c₀.length + Q : ℕ) : ℝ≥0∞) * (3 * εc))
  unfold FSFresh
  have hlen : K0.length = c₀.length := by simp [hK0]
  have hmain : Pr{let x ← (do
      let s ← $ᵗ S
      let z ← (simulateQ (implReal P s) (skel sh)).run (St.init c₀)
      return z.2.fs)}[x = true] ≤ B + Pr{let s ← $ᵗ S}[P.rowFn s [] 0 0 ∈ K0] := by
    refine prEvent_bind_le_add _ _ _ _ B fun s => ?_
    -- the tracked run
    have hproj := run_proj P s cw K0 (skel sh) (St.init c₀) false
    have e1 : Pr{let x ← (do
          let z ← (simulateQ (implReal P s) (skel sh)).run (St.init c₀)
          return z.2.fs)}[x = true] =
        Pr{let z ← (simulateQ (implB P s cw K0) (skel sh)).run (St.init c₀, false)}[
          z.2.1.fs = true] := by
      rw [show (do
          let z ← (simulateQ (implReal P s) (skel sh)).run (St.init c₀)
          return z.2.fs : ProbComp Bool) =
          (fun z => z.2.fs) <$> (simulateQ (implReal P s) (skel sh)).run (St.init c₀) by
        simp [map_eq_bind_pure_comp], prEvent_map, ← hproj.prEvent_eq, prEvent_map]
      rfl
    rw [e1]
    have hbad := prEvent_bad_le P s cw K0 εc hcw (skel sh) Q (skel_queryBound sh)
      (St.init c₀) rfl rfl
    rw [hlen] at hbad
    have hsplit : Pr{let z ← (simulateQ (implB P s cw K0) (skel sh)).run (St.init c₀, false)}[
          z.2.1.fs = true] ≤
        Pr{let z ← (simulateQ (implB P s cw K0) (skel sh)).run (St.init c₀, false)}[
          z.2.2 = true] +
        Pr{let z ← (simulateQ (implB P s cw K0) (skel sh)).run (St.init c₀, false)}[
          z.2.1.fs = true ∧ z.2.2 = false] := by
      refine le_trans (prEvent_mono _ _ _ fun z hz => ?_) (prEvent_or_le _ _ _)
      by_cases hb : z.2.2 = true
      · exact Or.inl hb
      · exact Or.inr ⟨hz, by simpa using hb⟩
    refine hsplit.trans (add_le_add hbad ?_)
    split_ifs with hr
    · exact prEvent_le_one _
    · refine le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hfs => ?_)
      have := trip_skel sh hsh (hrow s) hcK hclW hclσ hclQ hn (St.init c₀) (St.init c₀)
        (GInv.init P.n c₀) ⟨rfl, rfl, rfl, rfl, hr⟩ z hz hfs.2
      rw [this] at hfs
      exact Bool.false_ne_true hfs.1
  refine hmain.trans (add_le_add le_rfl ?_)
  have h := pr_exists_mem_le ($ᵗ S) K0 (fun y s => P.rowFn s [] 0 0 = y) δ₀
    (fun y _ => hrow₀ y)
  rw [hlen] at h
  refine le_trans (prEvent_mono _ _ _ fun s hs => ⟨_, hs, rfl⟩) h

end General

/-! ## The deployed shape -/

theorem ivPrefix_length (a : Bytes32) (n : ℕ) : (ivPrefix a n).length = 76 := by
  simp [ivPrefix, LeanVM.Rpm.wordBytes_len]; decide +kernel

theorem ivPrefix_ne (a b : Bytes32) (m n : ℕ)
    (h : LeanVM.Protocol.KeccakHash.wordBytes m.toUInt64 ≠
      LeanVM.Protocol.KeccakHash.wordBytes n.toUInt64) :
    ivPrefix a m ≠ ivPrefix b n := by
  intro he
  simp only [ivPrefix, List.append_assoc] at he
  obtain ⟨-, he⟩ := List.append_inj he rfl
  obtain ⟨-, he⟩ := List.append_inj he rfl
  obtain ⟨-, he⟩ := List.append_inj he (by simp)
  obtain ⟨he, -⟩ := List.append_inj he rfl
  exact h he

theorem openChals_witness (a : Bytes32) : openChals (witnessShape a) = 123 := by
  simp [openChals, witnessShape, qpCount, posDraws, middleChals, middleLens]

theorem openChals_wiring (a : Bytes32) (r : List (List UInt8)) :
    openChals (wiringShape a r) = 114 := by
  simp [openChals, wiringShape, qpCount, posDraws, middleChals, middleLens]

theorem skelOK_deployed (st : Statement) (idW idσ idQ : Bytes32) (rows : List (List UInt8)) :
    SkelOK (deployedShape st idW idσ idQ rows) where
  witness := rfl
  depth := show 1 ≤ 20 by decide
  quotient := rfl
  wiring := rfl
  okW := by
    show 1 ≤ 19 ∧ (∀ e ∈ [((4 : ℕ), (18 : ℕ), (15 : ℕ)), (4, 17, 11), (4, 16, 7)], 1 ≤ e.2.2) ∧
      absorbN 2 (2 ^ 3) < 4
    decide
  okσ := by
    show 1 ≤ 18 ∧ (∀ e ∈ [((4 : ℕ), (17 : ℕ), (14 : ℕ)), (4, 16, 10), (4, 15, 6)], 1 ≤ e.2.2) ∧
      absorbN 2 (2 ^ 2) < 4
    decide
  okQ := by
    show 1 ≤ 22 ∧ (∀ e ∈ [((4 : ℕ), (21 : ℕ), (18 : ℕ)), (4, 20, 14), (4, 19, 10), (4, 18, 6)],
      1 ≤ e.2.2) ∧ absorbN 2 (2 ^ 2) < 4
    decide
  preW := ivPrefix_length _ _
  preσ := ivPrefix_length _ _
  preQ := ivPrefix_length _ _
  neWσ := ivPrefix_ne idW idσ 25 24 (by decide)
  neWQ := ivPrefix_ne idW idQ 25 28 (by decide)
  neσQ := ivPrefix_ne idσ idQ 24 28 (by decide)

/-- The explicit bound: `Q · 6 (|c₀| + Q) / 2^256 + 2 (|c₀| + Q) · 3 εc + |c₀| δ₀`. -/
noncomputable def epsFS (c Q : ℕ) (εc δ₀ : ℝ≥0∞) : ℝ≥0∞ :=
  (Q : ℝ≥0∞) * (6 * ((c + Q : ℕ) : ℝ≥0∞) / 2 ^ 256) + 2 * (((c + Q : ℕ) : ℝ≥0∞) * (3 * εc)) +
    c * δ₀

section Deployed

variable {S : Type} [SampleableType S]

/-- **The honest prover's Fiat–Shamir inputs are fresh** (`FSFresh`), for the deployed skeleton,
but with probability `epsFS |c₀| (skelBound …) εc δ₀`. -/
theorem fsFresh_deployed (stmt : Statement) (idW idσ idQ : Bytes32) (rows : List (List UInt8))
    (P : Proto S Inp Out Msg Tbl Pos) (c₀ : List (Inp × Out)) (cw : Fin 3 → Bytes32 → List UInt8)
    (εc δ₀ : ℝ≥0∞) (hcw : ∀ j y, Pr{let u ← $ᵗ Out}[cw j u.1 = y] ≤ εc)
    (hrow₀ : ∀ y, Pr{let s ← $ᵗ S}[P.rowFn s [] 0 0 = y] ≤ δ₀)
    (hrow : ∀ s h k x, RowLike (P.rowFn s h k x)) (hcK : P.cK 0 = 0)
    (hclW : ClaimsAt P 5 4 (cw 0)) (hclσ : ClaimsAt P 128 3 (cw 1))
    (hclQ : ClaimsAt P 242 3 (cw 2)) (hn : 242 ≤ P.n) :
    FSFresh P (skel (deployedShape stmt idW idσ idQ rows)) c₀
      (epsFS c₀.length (skelBound (deployedShape stmt idW idσ idQ rows)) εc δ₀) :=
  fsFresh_skel _ (skelOK_deployed stmt idW idσ idQ rows) P c₀ cw εc δ₀ hcw hrow₀ hrow hcK hclW
    (by simpa [deployedShape, openChals_witness] using hclσ)
    (by simpa [deployedShape, openChals_witness, openChals_wiring] using hclQ)
    (by simp [deployedShape, openChals_witness, openChals_wiring]; omega)

theorem two_pow_inv_split (a b n : ℕ) (h : a + b = n) :
    ((2 : ℝ≥0∞) ^ a)⁻¹ = 2 ^ b * ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  subst h
  rw [pow_add, ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by simp)), ← mul_assoc,
    mul_comm ((2 : ℝ≥0∞) ^ b), mul_assoc, ENNReal.mul_inv_cancel (by positivity) (by simp),
    mul_one]

set_option exponentiation.threshold 4000 in
/-- **At our sizes**: `|c₀| ≤ 2^127`, at most `2^70` operations, `εc = 2^-191`, `δ₀ = 2^-2368`:
`εFS ≤ 2^-54`. -/
theorem epsFS_le (c Q : ℕ) (hc : c ≤ 2 ^ 127) (hQ : Q ≤ 2 ^ 70) :
    epsFS c Q ((2 : ℝ≥0∞) ^ 191)⁻¹ ((2 : ℝ≥0∞) ^ 2368)⁻¹ ≤ ((2 : ℝ≥0∞) ^ 54)⁻¹ := by
  have hcQ : c + Q ≤ 2 ^ 128 := by
    have : (2 : ℕ) ^ 127 + 2 ^ 70 ≤ 2 ^ 128 := by norm_num
    exact le_trans (add_le_add hc hQ) this
  have hN : Q * 6 * (c + Q) + 2 * (c + Q) * 3 * 2 ^ 65 + c ≤ 2 ^ 202 := by
    have h1 : Q * 6 * (c + Q) ≤ 2 ^ 70 * 6 * 2 ^ 128 :=
      Nat.mul_le_mul (Nat.mul_le_mul hQ le_rfl) hcQ
    have h2 : 2 * (c + Q) * 3 * 2 ^ 65 ≤ 2 * 2 ^ 128 * 3 * 2 ^ 65 :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl hcQ) le_rfl) le_rfl
    have h3 : (2 : ℕ) ^ 70 * 6 * 2 ^ 128 + 2 * 2 ^ 128 * 3 * 2 ^ 65 + 2 ^ 127 ≤ 2 ^ 202 := by
      norm_num
    exact le_trans (add_le_add (add_le_add h1 h2) hc) h3
  have e1 : ((2 : ℝ≥0∞) ^ 191)⁻¹ = 2 ^ 65 * ((2 : ℝ≥0∞) ^ 256)⁻¹ :=
    two_pow_inv_split 191 65 256 rfl
  have e2 : ((2 : ℝ≥0∞) ^ 54)⁻¹ = 2 ^ 202 * ((2 : ℝ≥0∞) ^ 256)⁻¹ :=
    two_pow_inv_split 54 202 256 rfl
  have e3 : ((2 : ℝ≥0∞) ^ 2368)⁻¹ ≤ ((2 : ℝ≥0∞) ^ 256)⁻¹ :=
    ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ (by norm_num) (by norm_num))
  unfold epsFS
  rw [e1, e2, div_eq_mul_inv]
  set U := ((2 : ℝ≥0∞) ^ 256)⁻¹
  calc _ ≤ (Q : ℝ≥0∞) * (6 * ((c + Q : ℕ) : ℝ≥0∞) * U) +
        2 * (((c + Q : ℕ) : ℝ≥0∞) * (3 * (2 ^ 65 * U))) + c * U := by gcongr
    _ = ((Q * 6 * (c + Q) + 2 * (c + Q) * 3 * 2 ^ 65 + c : ℕ) : ℝ≥0∞) * U := by push_cast; ring
    _ ≤ ((2 ^ 202 : ℕ) : ℝ≥0∞) * U := by gcongr
    _ = 2 ^ 202 * U := by norm_num

/-- **`fsFresh_deployed` at our sizes**: `εFS ≤ 2^-54`. -/
theorem fsFresh_deployed_bits (stmt : Statement) (idW idσ idQ : Bytes32) (rows : List (List UInt8))
    (hrows : rows.length = 2 ^ 19) (P : Proto S Inp Out Msg Tbl Pos) (c₀ : List (Inp × Out))
    (hc₀ : c₀.length ≤ 2 ^ 127) (cw : Fin 3 → Bytes32 → List UInt8)
    (hcw : ∀ j y, Pr{let u ← $ᵗ Out}[cw j u.1 = y] ≤ ((2 : ℝ≥0∞) ^ 191)⁻¹)
    (hrow₀ : ∀ y, Pr{let s ← $ᵗ S}[P.rowFn s [] 0 0 = y] ≤ ((2 : ℝ≥0∞) ^ 2368)⁻¹)
    (hrow : ∀ s h k x, RowLike (P.rowFn s h k x)) (hcK : P.cK 0 = 0)
    (hclW : ClaimsAt P 5 4 (cw 0)) (hclσ : ClaimsAt P 128 3 (cw 1))
    (hclQ : ClaimsAt P 242 3 (cw 2)) (hn : 242 ≤ P.n) :
    FSFresh P (skel (deployedShape stmt idW idσ idQ rows)) c₀ ((2 : ℝ≥0∞) ^ 54)⁻¹ :=
  le_trans (fsFresh_deployed stmt idW idσ idQ rows P c₀ cw _ _ hcw hrow₀ hrow hcK hclW hclσ hclQ hn)
    (epsFS_le _ _ hc₀ (skelBound_deployed stmt idW idσ idQ rows hrows))

/-- **Zero knowledge of the deployed proof, `FSFresh` discharged**: `zk_deployed_bits` for a
prover meeting `fsFresh_deployed`'s conditions (long rows, the witness table first with a
first row of min-entropy `δ₀`, claims that read a challenge through windows of min-entropy `εc`,
`242 ≤ P.n`): every distinguisher of at most `QD` queries, with `|c₀| + QD ≤ 2^127`, has advantage
at most `epsFS |c₀| (skelBound …) εc δ₀ + εhv + 2^-2200`. -/
theorem zk_deployed_fs (stmt : Statement) (idW idσ idQ : Bytes32) (rows : List (List UInt8))
    (hrows : rows.length = 2 ^ 19) (P : Proto S Inp Out Msg Tbl Pos) (c₀ : List (Inp × Out))
    (simV : List Out → ProbComp (View Msg Inp Tbl Pos)) (good : List Out → Prop)
    (εhv : ℝ≥0∞) (QD : ℕ) (hQ : c₀.length + QD ≤ 2 ^ 127)
    (cw : Fin 3 → Bytes32 → List UInt8) (εc δ₀ : ℝ≥0∞)
    (hcw : ∀ j y, Pr{let u ← $ᵗ Out}[cw j u.1 = y] ≤ εc)
    (hrow₀ : ∀ y, Pr{let s ← $ᵗ S}[P.rowFn s [] 0 0 = y] ≤ δ₀)
    (hrow : ∀ s h k x, RowLike (P.rowFn s h k x)) (hcK : P.cK 0 = 0)
    (hclW : ClaimsAt P 5 4 (cw 0)) (hclσ : ClaimsAt P 128 3 (cw 1))
    (hclQ : ClaimsAt P 242 3 (cw 2)) (hn : 242 ≤ P.n)
    (hHV : JointHVZK P simV good εhv)
    (hfac : ∀ σ k x, P.opened σ k x = false → ∀ y,
      Nonempty (Factors P σ (fun s => P.rows s σ k x = y) ((2 : ℝ≥0∞) ^ 2368)⁻¹))
    (hfac₂ : ∀ σ k x k' x', P.opened σ k x = false → P.opened σ k' x' = false →
      (k, x) ≠ (k', x') →
      Nonempty (Factors P σ (fun s => P.rows s σ k x = P.rows s σ k' x') ((2 : ℝ≥0∞) ^ 2368)⁻¹))
    (D : Proof → OracleComp (Inp →ₒ Out) Bool) (hD : ∀ π, IsTotalQueryBound (D π) QD) :
    Close (realGame P (skel (deployedShape stmt idW idσ idQ rows)) c₀ D)
      (simGame P simV (skel (deployedShape stmt idW idσ idQ rows)) c₀ D)
      (epsFS c₀.length (skelBound (deployedShape stmt idW idσ idQ rows)) εc δ₀ + εhv +
        ((2 : ℝ≥0∞) ^ 2200)⁻¹) :=
  zk_deployed_bits stmt idW idσ idQ rows hrows P c₀ simV good _ εhv QD hQ
    (fsFresh_deployed stmt idW idσ idQ rows P c₀ cw εc δ₀ hcw hrow₀ hrow hcK hclW hclσ hclQ hn)
    hHV hfac hfac₂ D hD

/-- **Zero knowledge of the deployed proof at our sizes, `FSFresh` discharged**: with the claims'
windows of min-entropy `2^-191` and the first witness row's `2^-2368`, advantage at most
`2^-54 + εhv + 2^-2200`. -/
theorem zk_deployed_fs_bits (stmt : Statement) (idW idσ idQ : Bytes32) (rows : List (List UInt8))
    (hrows : rows.length = 2 ^ 19) (P : Proto S Inp Out Msg Tbl Pos) (c₀ : List (Inp × Out))
    (simV : List Out → ProbComp (View Msg Inp Tbl Pos)) (good : List Out → Prop)
    (εhv : ℝ≥0∞) (QD : ℕ) (hQ : c₀.length + QD ≤ 2 ^ 127)
    (cw : Fin 3 → Bytes32 → List UInt8)
    (hcw : ∀ j y, Pr{let u ← $ᵗ Out}[cw j u.1 = y] ≤ ((2 : ℝ≥0∞) ^ 191)⁻¹)
    (hrow₀ : ∀ y, Pr{let s ← $ᵗ S}[P.rowFn s [] 0 0 = y] ≤ ((2 : ℝ≥0∞) ^ 2368)⁻¹)
    (hrow : ∀ s h k x, RowLike (P.rowFn s h k x)) (hcK : P.cK 0 = 0)
    (hclW : ClaimsAt P 5 4 (cw 0)) (hclσ : ClaimsAt P 128 3 (cw 1))
    (hclQ : ClaimsAt P 242 3 (cw 2)) (hn : 242 ≤ P.n)
    (hHV : JointHVZK P simV good εhv)
    (hfac : ∀ σ k x, P.opened σ k x = false → ∀ y,
      Nonempty (Factors P σ (fun s => P.rows s σ k x = y) ((2 : ℝ≥0∞) ^ 2368)⁻¹))
    (hfac₂ : ∀ σ k x k' x', P.opened σ k x = false → P.opened σ k' x' = false →
      (k, x) ≠ (k', x') →
      Nonempty (Factors P σ (fun s => P.rows s σ k x = P.rows s σ k' x') ((2 : ℝ≥0∞) ^ 2368)⁻¹))
    (D : Proof → OracleComp (Inp →ₒ Out) Bool) (hD : ∀ π, IsTotalQueryBound (D π) QD) :
    Close (realGame P (skel (deployedShape stmt idW idσ idQ rows)) c₀ D)
      (simGame P simV (skel (deployedShape stmt idW idσ idQ rows)) c₀ D)
      (((2 : ℝ≥0∞) ^ 54)⁻¹ + εhv + ((2 : ℝ≥0∞) ^ 2200)⁻¹) :=
  zk_deployed_bits stmt idW idσ idQ rows hrows P c₀ simV good _ εhv QD hQ
    (fsFresh_deployed_bits stmt idW idσ idQ rows hrows P c₀ (by omega) cw hcw hrow₀ hrow hcK hclW
      hclσ hclQ hn)
    hHV hfac hfac₂ D hD

end Deployed

end QuotientZk.Deployed.Fresh
