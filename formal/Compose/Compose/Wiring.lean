-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM `mumbai`'s Reed–Solomon facts (https://github.com/Verified-zkEVM/leanerVM, commit
-- 6175f1a0, MIT OR Apache-2.0): `range_enc`, `enc_injective`, `eq_of_mem_code_of_agreeOn`,
-- `eq_of_blockOf_eq`, `LevelCode.two_pow_le_thr`, `deployed_spec_hyps`.
import Compose.Deployed

/-!
# The circuit's commitment has one candidate

The wiring opening's doom quantifies over the candidates of the word the circuit's commitment
commits to: the stacks whose encoding agrees with the word on at least the level-0 Johnson
threshold of columns (`Candidates`, mumbai's `EndToEnd` notion for stacked tables: every lane of
the column agrees). When the word **is** the encoding of a stack `q₀` (the setup's: the honest
wiring table), `q₀` is its only candidate (`candidates_of_codeword`): two Reed–Solomon codewords
of degree `< 2^κ` agreeing on `2^κ` points are equal, and the threshold is at least `2^κ`
(`LevelCode.two_pow_le_thr`: at rate `1/2` the Johnson agreement `√ρ + η` exceeds the rate, that
is the Johnson radius `1 − √ρ ≈ 0.293` is below the relative distance `1/2`). At the deployed codes
(`candidates_honest`): `κ = μ − 6` (`deployed_spec_hyps`).
-/

set_option linter.unusedSectionVars false

namespace Compose

open LeanVM LeanVM.Protocol LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir
  LeanVM.Protocol.Whir.Sound WhirBridge

/-- **A word is the encoding of the stack `q₀`**: every lane of every column is the encoding of
`q₀`'s block. -/
def HonestWord (μ R : ℕ) (W : Word) (q₀ : Column μ) : Prop :=
  ∀ (u : Fin (2 ^ laneBits)) (v : Fin (2 ^ (μ - laneBits + R))),
    laneOf W u v = enc (μ - laneBits) R (blockOf q₀ u) v

/-- **A codeword's candidates at a threshold of at least `2^κ` are itself.** -/
theorem candidates_of_codeword {μ R A : ℕ} (hμ : laneBits ≤ μ) (h64 : μ - laneBits + R ≤ 64)
    (hA : 2 ^ (μ - laneBits) ≤ A) {W : Word} {q₀ : Column μ} (hW : HonestWord μ R W q₀)
    {q : Column μ} (hq : q ∈ Candidates μ R A W) : q = q₀ := by
  obtain ⟨S, hS, hag⟩ := hq
  refine eq_of_blockOf_eq hμ fun u => ?_
  have hmem : ∀ g, enc (μ - laneBits) R g ∈
      ReedSolomon.code (domain (μ - laneBits) R h64) (2 ^ (μ - laneBits)) := fun g => by
    rw [← range_enc h64]
    exact LinearMap.mem_range_self _ g
  have he := eq_of_mem_code_of_agreeOn (domain (μ - laneBits) R h64) (hmem (blockOf q u))
    (hmem (blockOf q₀ u)) S (hA.trans hS) fun v hv => (hag v hv u).symm.trans (hW u v)
  exact enc_injective h64 he

/-- **At the deployed codes**, the candidates of the encoding of `q₀` are `q₀`. -/
theorem candidates_honest {μ R : ℕ} (hw : Whir.Admissible μ R) {W : Word} {q₀ : Column μ}
    (hW : HonestWord μ R W q₀) {q : Column μ} (hq : q ∈ Candidates μ R (code₀ μ R).thr W) :
    q = q₀ := by
  obtain ⟨level, rest, hc, -⟩ := LeanVM.Protocol.Whir.Complete.exists_ladder hw
  have hd := LeanVM.Protocol.Whir.Params.deployed_spec_hyps hw hc
  have hκ : (code₀ μ R).κ = μ - laneBits := hd.2.2.1
  have hR : (code₀ μ R).R = R := hd.2.2.2.1
  have h64 : μ - laneBits + R ≤ 64 := by
    have := (code₀ μ R).h64
    rw [hκ, hR] at this
    exact this
  have hthr : 2 ^ (μ - laneBits) ≤ (code₀ μ R).thr := by
    have := (code₀ μ R).two_pow_le_thr
    rwa [hκ] at this
  exact candidates_of_codeword hd.2.1 h64 hthr hW hq

end Compose
