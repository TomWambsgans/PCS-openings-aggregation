-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The margins of `ListChainK.lean`'s rounds, as `Compose/Bits.lean` of this repository does them for
-- `ListChain.lean`'s.
import Compose.ListChainKComposed

/-!
# The margins: which identity degrees keep each round at 128 bits

Round `j`'s term in `maxErrK` is its error times the product of the list bounds of the roots of
the rounds `0..j` (the setup's commitment, a fixed root with one candidate, adds no factor). For a
Schwartz–Zippel round of a field of `2^192` elements, the error is `d / 2^192`, `d` the degree of
the identity the round's challenge tests, so the round keeps 128 bits exactly when

`f · d ≤ 2^64`, `f` the product of the list bounds of the roots before it (`factor_mul_err_le`).

With `r` roots before the round, each of at most `L` candidates (`facL_le_pow`):

| lists `L` | `r = 1` (after root 1) | `r = 2` (after roots 1, 2) | `r = 3` |
|---|---|---|---|
| `2^18` (leanerVM's generic bound) | `d ≤ 2^46` | `d ≤ 2^28` | `d ≤ 2^10` |
| `7908` (certified, `log_n = 25`) | `d ≤ 2^51` | `d ≤ 2^38` | `d ≤ 2^25` |
| `7908 · 3564` (`quotient::protocol`'s two roots) | | `d ≤ 2^39` | |

(`bits_generic₁` … `bits_certified₃`, `bits_quot`, each `f · d ≤ 2^64` by `norm_num`.) The exact
ceilings are `⌊2^64 / L^r⌋`: `2^46`, `2^28`, `2^10` for `L = 2^18`; `2.33·10^18 ≈ 2^51.05`,
`2.95·10^11 ≈ 2^38.10`, `3.73·10^7 ≈ 2^25.15` for `L = 7908`.

`maxErrK_le_bits`: if every round's error is at most `d_j / 2^192` and `facL_j · d_j ≤ 2^64`,
`maxErrK ≤ 2^-128`; then `knowledgeSoundness_listChainK_bits` is the composed bound with
`2^-128` in place of `maxErrK` (about `2^-64` at `N = 2^64` queries, as `quotient::protocol`'s).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm LeanVM LeanVM.Protocol LeanVM.Semantics

/-- **A round keeps 128 bits** when its factor times its identity's degree is at most `2^64`. -/
theorem factor_mul_err_le {f d : ℕ} (h : f * d ≤ 2 ^ 64) :
    (f : ℝ≥0∞) * (((d : ℝ≥0) / 2 ^ 192 : ℝ≥0) : ℝ≥0∞) ≤ ((1 / 2 ^ 128 : ℝ≥0) : ℝ≥0∞) := by
  have key : (f : ℝ≥0) * ((d : ℝ≥0) / 2 ^ 192) ≤ 1 / 2 ^ 128 := by
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have hc : ((f * d : ℕ) : ℝ≥0) ≤ 2 ^ 64 := by exact_mod_cast h
    calc (f : ℝ≥0) * d * 2 ^ 128 ≤ 2 ^ 64 * 2 ^ 128 := by
          gcongr
          exact_mod_cast hc
      _ = 2 ^ 192 := by norm_num
  have e : (f : ℝ≥0∞) * (((d : ℝ≥0) / 2 ^ 192 : ℝ≥0) : ℝ≥0∞) =
      (((f : ℝ≥0) * ((d : ℝ≥0) / 2 ^ 192) : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_mul, ENNReal.coe_natCast]
  rw [e]
  exact_mod_cast key

section Fac

variable {M : Type}

/-- The number of rounds with a root. -/
def nRoots : List RoundSpec → ℕ
  | [] => 0
  | s :: rs => (if s.root then 1 else 0) + nRoots rs

/-- **The factor of `r` roots of at most `L` candidates is at most `L^r`.** -/
theorem facL_le_pow (C : ℕ → ListCommit M) (L : ℕ) (hL : ∀ i, (C i).bound ≤ L) (h1 : 1 ≤ L) :
    ∀ (i : ℕ) (rs : List RoundSpec), facL C i rs ≤ L ^ nRoots rs
  | _, [] => by simp [facL, nRoots]
  | i, s :: rs => by
    simp only [facL, nRoots]
    rw [pow_add]
    refine Nat.mul_le_mul ?_ (facL_le_pow C L hL h1 (i + 1) rs)
    split <;> simp [hL i]

end Fac

/-! ## The numbers -/

theorem bits_generic₁ : (2 ^ 18) ^ 1 * 2 ^ 46 ≤ 2 ^ 64 := by norm_num
theorem bits_generic₂ : (2 ^ 18) ^ 2 * 2 ^ 28 ≤ 2 ^ 64 := by norm_num
theorem bits_generic₃ : (2 ^ 18) ^ 3 * 2 ^ 10 ≤ 2 ^ 64 := by norm_num
theorem bits_certified₁ : 7908 ^ 1 * 2 ^ 51 ≤ 2 ^ 64 := by norm_num
theorem bits_certified₂ : 7908 ^ 2 * 2 ^ 38 ≤ 2 ^ 64 := by norm_num
theorem bits_certified₃ : 7908 ^ 3 * 2 ^ 25 ≤ 2 ^ 64 := by norm_num
theorem bits_quot : 7908 * 3564 * 2 ^ 39 ≤ 2 ^ 64 := by norm_num

/-- The ceilings are tight to a bit: one more bit of degree loses the 128 bits. -/
theorem bits_generic₂_tight : ¬ (2 ^ 18) ^ 2 * 2 ^ 29 ≤ 2 ^ 64 := by norm_num
theorem bits_certified₂_tight : ¬ 7908 ^ 2 * 2 ^ 39 ≤ 2 ^ 64 := by norm_num

/-! ## The composed bound at 128 bits per round -/

variable {F St M Pf β : Type} [SampleableType F]
variable (K : ChainSpec F St) (C : ℕ → ListCommit M) (R : Piop K M)

/-- **Every round at 128 bits**: each round's error at most `d_j / 2^192` with
`facL_j · d_j ≤ 2^64`. -/
theorem maxErrK_le_bits (d : ℕ → ℕ)
    (herr : ∀ j < K.rounds.length, R.err j ≤ (((d j : ℝ≥0) / 2 ^ 192 : ℝ≥0) : ℝ≥0∞))
    (hd : ∀ j < K.rounds.length, facL C 0 (K.rounds.take (j + 1)) * d j ≤ 2 ^ 64) :
    maxErrK K C R ≤ ((1 / 2 ^ 128 : ℝ≥0) : ℝ≥0∞) := by
  refine Finset.sup_le fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  calc (facL C 0 (K.rounds.take (j + 1)) : ℝ≥0∞) * R.err j
      ≤ (facL C 0 (K.rounds.take (j + 1)) : ℝ≥0∞) * (((d j : ℝ≥0) / 2 ^ 192 : ℝ≥0) : ℝ≥0∞) := by
        gcongr
        exact herr j hj'
    _ ≤ _ := factor_mul_err_le (hd j hj')

variable [Fintype F] [DecidableEq F] (view : Pf → St × List (RMsg F)) (Op : OpeningsK Pf F β M)

/-- **The composed bound with every round at 128 bits**: the openings' terms plus
`N (2^-128 + 5 N / 2^256)`. -/
theorem knowledgeSoundness_listChainK_bits (A : OracleComp KeccakCalls Pf)
    (post : Pf → List (List F) → OracleComp KeccakCalls β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (post p ch) QV)
    (hfit : ∀ π ch b, Op.check π ch b → FitsAll K.rounds (view π).2)
    (hlink : ∀ π ch b (cs : List (Option M)), Op.check π ch b →
      cs.length = K.rounds.length →
      (∀ i (h : i < cs.length), (K.spec i).root → Op.good i π ch cs[i]) → Op.goodS π ch →
      ∃ p m c, opened cs (view π).2 ch = p ++ [(m, c)] ∧ R.post (view π).1 p m c)
    (d : ℕ → ℕ)
    (herr : ∀ j < K.rounds.length, R.err j ≤ (((d j : ℝ≥0) / 2 ^ 192 : ℝ≥0) : ℝ≥0∞))
    (hd : ∀ j < K.rounds.length, facL C 0 (K.rounds.take (j + 1)) * d j ≤ 2 ^ 64)
    (εD : ℕ → ℝ≥0∞) (εS : ℝ≥0∞)
    (hD : ∀ i < K.rounds.length, (K.spec i).root →
      Pr{let z ← (simulateQ randomOracle (expK K view A post)).run' ∅}[DoomK C view Op i z] ≤ εD i)
    (hS : Pr{let z ← (simulateQ randomOracle (expK K view A post)).run' ∅}[DoomSK Op z] ≤ εS) :
    Pr{let z ← (simulateQ randomOracle (expK K view A post)).run' ∅}[BreaksK K C R view Op z] ≤
      (∑ i ∈ Finset.range K.rounds.length, εD i) + εS +
        ((Q + K.nQ + QV : ℕ) : ℝ≥0∞) * (((1 / 2 ^ 128 : ℝ≥0) : ℝ≥0∞) +
          5 * ((Q + K.nQ + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  refine (knowledgeSoundness_listChainK K C R view Op A post Q QV hQ hV hfit hlink εD εS hD
    hS).trans ?_
  gcongr
  exact maxErrK_le_bits K C R d herr hd

end Compose
