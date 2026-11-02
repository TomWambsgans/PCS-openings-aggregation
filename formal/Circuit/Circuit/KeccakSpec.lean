/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
The specification is leanerVM's Keccak (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`,
commit 6175f1a0, `Statement/Keccak.lean`, MIT OR Apache-2.0), imported; its lanes written out
(`Statement/Fast/Keccak.lean`'s `roundLanes`, `round_eq_roundLanes`) are used to read it bit by bit.
-/
import Circuit.Defs
import Statement.Fast.Keccak
import Mathlib.Tactic.IntervalCases

/-!
# Keccak-f[1600] bit by bit

`KeccakBits.round` is a round of Keccak-f[1600] on a state of bits, written as the circuit computes
it: θ's column parities as chains of four XORs, its mixes, ρ and π by the inverse lane map, χ, ι.
`round_bits`: it is leanerVM's `Keccak.round`, bit `z` of lane `i` (through mumbai's own restatement
of the round with its lanes written out, `round_eq_roundLanes`); `keccakF_bits`: the `24` rounds are
`keccakF1600`.
-/

namespace PcsCircuit

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol Builder

/-- A Keccak state of bits: bit `z` of lane `i`. -/
abbrev Bits := Nat → Nat → Bool

namespace KeccakBits

/-- θ's column parity: lane `x`, then XOR lanes `x + 5`, `x + 10`, `x + 15`, `x + 20`. -/
def thetaC (s : Bits) (x z : Nat) : Bool := [1, 2, 3, 4].foldl (fun acc y => acc ^^ s (x + 5 * y) z) (s x z)

/-- θ's mix of column `x`: the parity of column `x - 1` and that of column `x + 1` rotated by one. -/
def thetaD (s : Bits) (x z : Nat) : Bool := thetaC s ((x + 4) % 5) z ^^ thetaC s ((x + 1) % 5) ((z + 63) % 64)

/-- θ. -/
def theta (s : Bits) : Bits := fun i z => s i z ^^ thetaD s (i % 5) z

/-- ρ and π: lane `j` bit `z` is lane `piInv j` bit `z - rho (piInv j)`. -/
def rhoPi (s : Bits) : Bits := fun j z => s (piInv j) ((z + 64 - rho (piInv j)) % 64)

/-- χ: `a[x] ⊕ (¬a[x + 1] ∧ a[x + 2])` along each row. -/
def chi (s : Bits) : Bits := fun i z =>
  s i z ^^ (!s ((i % 5 + 1) % 5 + 5 * (i / 5)) z && s ((i % 5 + 2) % 5 + 5 * (i / 5)) z)

/-- ι: the round constant XORed into lane `0`. -/
def iota (rc : UInt64) (s : Bits) : Bits := fun i z => s i z ^^ (decide (i = 0) && rc.toBitVec.getLsbD z)

/-- One round. -/
def round (s : Bits) (rc : UInt64) : Bits := iota rc (chi (rhoPi (theta s)))

/-- Keccak-f[1600]: the `24` rounds. -/
def keccakF (s : Bits) : Bits := keccakRC.foldl round s

end KeccakBits

/-- The bits of a state of lanes. -/
def laneBits (a : KeccakState) : Bits := fun i z => (Keccak.lane a i).toBitVec.getLsbD z

/-- Two bit states agree on the `25 × 64` bits of a state. -/
def BitsEq (s s' : Bits) : Prop := ∀ i < 25, ∀ z < 64, s i z = s' i z

/-! ## Lemmas on bits -/

theorem mod64_lt (n : Nat) : n % 64 < 64 := Nat.mod_lt _ (by decide)

/-- Bit `z` of a lane rotated left by `n < 64`. -/
theorem getLsbD_rot (x : UInt64) (n z : Nat) (hn : n < 64) :
    (Keccak.rot x n).toBitVec.getLsbD z = (decide (z < 64) && x.toBitVec.getLsbD ((z + 64 - n) % 64)) := by
  unfold Keccak.rot
  split
  · subst n
    by_cases hz : z < 64
    · simp [hz, Nat.add_mod_right, Nat.mod_eq_of_lt hz]
    · simp [hz]; exact BitVec.getLsbD_of_ge _ _ (by omega)
  · rename_i hn0
    have h1 : (n.toUInt64.toBitVec % 64).toNat = n := by
      simp [UInt64.toNat_toBitVec]; omega
    have h2 : ((64 - n).toUInt64.toBitVec % 64).toNat = 64 - n := by
      simp; omega
    simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, BitVec.getLsbD_or,
      BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', h1, h2, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
    by_cases hz : z < 64
    · by_cases hzn : z < n
      · simp [hz, hzn]
        have : (z + 64 - n) % 64 = 64 - n + z := by omega
        rw [this]
      · simp [hz, hzn]
        have : (z + 64 - n) % 64 = z - n := by omega
        rw [this, BitVec.getLsbD_of_ge x.toBitVec (64 - n + z) (by omega), Bool.or_false]
    · simp [hz]
      exact BitVec.getLsbD_of_ge _ _ (by omega)

/-- `piInv` inverts leanerVM's `keccakPi`, and `rho` is its `keccakRho`. -/
theorem piInv_keccakPi : ∀ i < 25, piInv (keccakPi i) = i := by decide
theorem keccakPi_piInv : ∀ j < 25, keccakPi (piInv j) = j := by decide
theorem rho_eq : ∀ i < 25, keccakRho.getD i 0 = rho i := by decide

set_option maxHeartbeats 4000000 in
/-- **A round, bit by bit, is leanerVM's `Keccak.round`.** -/
theorem round_bits (a : KeccakState) (rc : UInt64) : ∀ i < 25, ∀ z < 64,
    laneBits (Keccak.round a rc) i z = KeccakBits.round (laneBits a) rc i z := by
  intro i hi z hz
  rw [LeanVM.Fast.Keccak.round_eq_roundLanes]
  interval_cases i
  all_goals
    simp [LeanVM.Fast.Keccak.roundLanes, laneBits, Keccak.lane, KeccakBits.round, KeccakBits.iota,
      KeccakBits.chi, KeccakBits.rhoPi, KeccakBits.theta, KeccakBits.thetaD, KeccakBits.thetaC, piInv, rho,
      getLsbD_rot, mod64_lt, hz, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not,
      -BitVec.getLsbD_eq_getElem]

/-! ## The rounds -/

theorem BitsEq.refl (s : Bits) : BitsEq s s := fun _ _ _ _ => rfl

theorem BitsEq.trans {s s' s'' : Bits} (h : BitsEq s s') (h' : BitsEq s' s'') : BitsEq s s'' :=
  fun i hi z hz => (h i hi z hz).trans (h' i hi z hz)

theorem piInv_lt : ∀ j < 25, piInv j < 25 := by decide

/-- A round reads only the state's `25 × 64` bits. -/
theorem round_congr {s s' : Bits} (rc : UInt64) (h : BitsEq s s') :
    BitsEq (KeccakBits.round s rc) (KeccakBits.round s' rc) := by
  have hC : ∀ x < 5, ∀ z < 64, KeccakBits.thetaC s x z = KeccakBits.thetaC s' x z := by
    intro x hx z hz
    simp only [KeccakBits.thetaC, List.foldl_cons, List.foldl_nil]
    rw [h x (by omega) z hz, h (x + 5 * 1) (by omega) z hz, h (x + 5 * 2) (by omega) z hz,
      h (x + 5 * 3) (by omega) z hz, h (x + 5 * 4) (by omega) z hz]
  have hT : BitsEq (KeccakBits.theta s) (KeccakBits.theta s') := by
    intro i hi z hz
    simp only [KeccakBits.theta, KeccakBits.thetaD]
    rw [h i hi z hz, hC _ (by omega) z hz, hC _ (by omega) _ (mod64_lt _)]
  have hR : BitsEq (KeccakBits.rhoPi (KeccakBits.theta s)) (KeccakBits.rhoPi (KeccakBits.theta s')) := by
    intro j hj z _
    exact hT _ (piInv_lt j hj) _ (mod64_lt _)
  intro i hi z hz
  simp only [KeccakBits.round, KeccakBits.iota, KeccakBits.chi]
  rw [hR i hi z hz, hR _ (by omega) z hz, hR _ (by omega) z hz]

theorem foldl_round_congr {s s' : Bits} (rcs : List UInt64) (h : BitsEq s s') :
    BitsEq (rcs.foldl KeccakBits.round s) (rcs.foldl KeccakBits.round s') := by
  induction rcs generalizing s s' with
  | nil => exact h
  | cons rc rcs ih => exact ih (round_congr rc h)

/-- **Keccak-f[1600], bit by bit, is leanerVM's `keccakF1600`.** -/
theorem keccakF_bits (a : KeccakState) : BitsEq (laneBits (keccakF1600 a)) (KeccakBits.keccakF (laneBits a)) := by
  suffices ∀ (rcs : List UInt64) (a : KeccakState),
      BitsEq (laneBits (rcs.foldl Keccak.round a)) (rcs.foldl KeccakBits.round (laneBits a)) by
    unfold keccakF1600 KeccakBits.keccakF; exact this _ a
  intro rcs
  induction rcs with
  | nil => intro a; exact BitsEq.refl _
  | cons rc rcs ih =>
    intro a
    rw [List.foldl_cons, List.foldl_cons]
    exact (ih (Keccak.round a rc)).trans (foldl_round_congr rcs (round_bits a rc))

end PcsCircuit
