-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Cantor
import Field.F192

/-!
# The deployed Cantor basis

`quotient::domain::beta()` (`crates/quotient/src/domain.rs`): `beta[0] = 1` and
`S(beta[k + 1]) = beta[k]`, `S(x) = x^2 + x`, each the solution with its low bit clear (`solve`
returns a preimage and clears its bit 0; the two preimages differ by `1`, `S`'s kernel being
`{0, 1}`). The instance uses its first `24` words, one for each bit of a cell's index:

* `betaWords`: those words, which `crates/quotient/tests/lean_beta_vector.rs` asserts of the Rust;
* `deployedBasis`: they are a Cantor basis of `F64` (`betaF64_succ`, checked by the kernel, which
  evaluates CompPoly's products), with every vector but the first of low bit clear
  (`betaF64_low`);
* `deployedBasis_unique`: **the rule determines the basis**: any Cantor basis of `F64` whose
  vectors after the first have their low bit clear is this one. So `deployedBasis` is `beta()`
  by the rule `domain.rs` computes by, not only by the test.
-/

namespace QuotientSecurity

open Primitives

/-- The first `24` words of `beta()`. -/
def betaWords : List UInt64 :=
  [0x0000000000000001, 0x19c9369f278adc02, 0xa181e7d66f5ff794, 0x5db84357ce785d08,
    0xb973d466f5c9d0ca, 0x521ac889831a075e, 0x033ce8beddc8a656, 0xb5846c4e07b91010,
    0x4087b8cbb37a32ec, 0x00d0d3888c0ae17c, 0xafd5ac70237f2222, 0xe3f5af99cc3aaaf8,
    0x5a1db3b16a0b58b8, 0x09947c54fe7ee248, 0x0e8eaf0e0068f544, 0xa2a113500b4b4f5a,
    0xe96f9805d6ce0bb0, 0x53496f8b5c9edd4c, 0xad325cb6f4ac2a9e, 0x4a8dcf8bd7ede826,
    0xa3e9c552b6434210, 0x5fa92ad9c9bc7ed0, 0xa389f910cd7734de, 0xe916f3dfca4609d8]

/-- `beta()[k]` as an element of `F64` (zero from `24` on, which the basis never reads). -/
def betaF64 (k : ℕ) : F64 := F64.ofU64 (betaWords.getD k 0)

/-- Bit 0 of an element's word. -/
def lowBit (a : F64) : Bool := a.toU64.toNat.testBit 0

theorem betaF64_zero : betaF64 0 = 1 := rfl

/-- **`S(beta[k + 1]) = beta[k]`**, checked by the kernel. -/
theorem betaF64_succ : ∀ k : Fin 23, sq (betaF64 ((k : ℕ) + 1)) = betaF64 k := by decide +kernel

/-- **Every vector but the first has its low bit clear.** -/
theorem betaF64_low : ∀ k : Fin 23, lowBit (betaF64 ((k : ℕ) + 1)) = false := by decide +kernel

/-- **The deployed Cantor basis** of `F64`: `beta()`'s first `24` vectors. -/
def deployedBasis : CantorBasis F64 (22 + 2) where
  β := betaF64
  zero := betaF64_zero
  succ k hk := betaF64_succ ⟨k, by omega⟩

theorem lowBit_add (a b : F64) : lowBit (a + b) = (lowBit a ^^ lowBit b) := by
  unfold lowBit
  rw [F64.toU64_add, UInt64.toNat_xor, Nat.testBit_xor]

theorem lowBit_one : lowBit 1 = true := by decide +kernel

/-- Two solutions of `S(x) = c` are equal or differ by `1`. -/
theorem sq_eq_sq {a b : F64} (h : sq a = sq b) : a = b ∨ a + b = 1 := by
  have two : (2 : F64) = 0 := CharTwo.two_eq_zero
  have h2 : (a + b) * (a + b + 1) = 0 := by
    unfold sq at h
    linear_combination h + (a * b + b * b + b) * two
  rcases mul_eq_zero.mp h2 with h0 | h0
  · exact Or.inl (CharTwo.add_eq_zero.mp h0)
  · exact Or.inr (CharTwo.add_eq_zero.mp h0)

/-- **The low bits determine the basis**: a Cantor basis of `F64` whose vectors after the first
have their low bit clear is `deployedBasis` (on the `24` vectors it has). -/
theorem deployedBasis_unique (B : CantorBasis F64 (22 + 2))
    (hlow : ∀ k, 0 < k → k < 22 + 2 → lowBit (B.β k) = false) :
    ∀ k, k < 22 + 2 → B.β k = deployedBasis.β k
  | 0, _ => by rw [B.zero, deployedBasis.zero]
  | k + 1, hk => by
    have ih := deployedBasis_unique B hlow k (by omega)
    have h : sq (B.β (k + 1)) = sq (deployedBasis.β (k + 1)) := by
      rw [B.succ k hk, deployedBasis.succ k hk, ih]
    rcases sq_eq_sq h with h0 | h1
    · exact h0
    · exfalso
      have e := lowBit_add (B.β (k + 1)) (deployedBasis.β (k + 1))
      have hd : lowBit (deployedBasis.β (k + 1)) = false := betaF64_low ⟨k, by omega⟩
      rw [h1, lowBit_one, hlow (k + 1) (by omega) hk, hd] at e
      exact absurd e (by decide)

end QuotientSecurity
