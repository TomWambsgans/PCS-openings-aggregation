-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Keccak-f[1600] and Keccak-256 are leanerVM's
-- (https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, `Statement/Keccak.lean`), read bit by bit through
-- `formal/Circuit`'s `KeccakBits` (`Circuit/KeccakSpec.lean`, `Circuit/Keccak256Spec.lean`).
import Circuit.Keccak256Spec
import Field.F192

/-!
# Keccak-f[1600] and Keccak-256 as D16v computes them, on words of `K`

The value-level relations a satisfied D16v Keccak-f instance gives (`crates/leanvm_rec/src/circuit/keccak16.rs`):
words of `K = F64` that the template's expression slots push, read through the copy argument. `D16Rel A C D` says:

* `C 0` is θ's column parity of the input `A 0` (`kprep`'s `C_0` units);
* `D j x z = C j (x − 1) z + C j (x + 1) (z − 1)` (a D unit);
* `A (j + 1)` is round `j`'s χ (and ι by `κ`) of the χ inputs that ρ and π bring to its rows: cell `x'` of the
  `(plane y', slice z')` row is `A j l z₀` for the lane `l = π⁻¹(x' + 5y')` at `z₀ = z' − ρ_l`, and cell `5 + x'`
  is `D j (l mod 5) z₀` (`chiIn`), so the row's `b_(x') = c_(x') + c_(5+x')` is θ's output there;
* `C (j + 1)` is `A (j + 1)`'s column parity (the partial sums `P_(y')`).

`d16_keccakF`: on bits (`ofBool`), `A 24` is `keccakF` of `A 0`. `keccak256_bits_multi`: Keccak-256 of any byte
string, bit by bit, is the sponge `spongeState` over `KeccakBits.keccakF` (any number of blocks, `pad10*1`), which is
what the circuit's `Sponge::keccak256` lays out.
-/

namespace RecCircuit

open Primitives PcsCircuit PcsCircuit.Builder LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- A bit as a word of `K`: `0` or `1`. -/
def ofBool (b : Bool) : F64 := if b then 1 else 0

/-- Bit `z` of round `j`'s constant as a word: ι's `κ` at `k0`'s roles 0 and 5 (`rc >> z & 1 == 1`). -/
def rcBit (j z : ℕ) : F64 := ofBool ((keccakRC.getD j 0).toNat.testBit z)

/-- The χ input `b_x` of lane `x + 5y` at slice `z`: θ's output at the lane ρ and π bring there, `A l z₀ + D (l mod 5)
z₀` with `l = π⁻¹(x + 5y)`, `z₀ = z − ρ_l`. -/
def chiIn (A D : ℕ → ℕ → F64) (x y z : ℕ) : F64 :=
  A (piInv (x + 5 * y)) ((z + 64 - rho (piInv (x + 5 * y))) % 64)
    + D (piInv (x + 5 * y) % 5) ((z + 64 - rho (piInv (x + 5 * y))) % 64)

/-- χ's output at `x` on a row of inputs `b`: `b_x + b_(x+2) + b_(x+1)·b_(x+2)` (`b ⊕ (¬b₁ ∧ b₂)` on bits). -/
def chiOut (b : ℕ → F64) (x : ℕ) : F64 := b x + b ((x + 2) % 5) + b ((x + 1) % 5) * b ((x + 2) % 5)

/-- θ's column parity of a state of words. -/
def colSum (A : ℕ → ℕ → F64) (x z : ℕ) : F64 := A x z + A (x + 5) z + A (x + 10) z + A (x + 15) z + A (x + 20) z

/-- **The relations of a D16v Keccak-f instance**, round `j < 24` taking `A j` to `A (j + 1)`. -/
structure D16Rel (A C D : ℕ → ℕ → ℕ → F64) : Prop where
  c0 : ∀ x < 5, ∀ z < 64, C 0 x z = colSum (A 0) x z
  cNext : ∀ j < 23, ∀ x < 5, ∀ z < 64, C (j + 1) x z = colSum (A (j + 1)) x z
  d : ∀ j < 24, ∀ x < 5, ∀ z < 64, D j x z = C j ((x + 4) % 5) z + C j ((x + 1) % 5) ((z + 63) % 64)
  chi : ∀ j < 24, ∀ x < 5, ∀ y < 5, ∀ z < 64,
    A (j + 1) (x + 5 * y) z = chiOut (fun x' => chiIn (A j) (D j) x' y z) x + (if x = 0 ∧ y = 0 then rcBit j z else 0)

/-! ### Bits as words: the algebra in characteristic 2 -/

theorem one_add_one_F64 : (1 : F64) + 1 = 0 := CharTwo.add_self_eq_zero 1

theorem ofBool_xor (a b : Bool) : ofBool (a ^^ b) = ofBool a + ofBool b := by
  cases a <;> cases b <;> simp [ofBool, one_add_one_F64]

theorem ofBool_chi (a b c : Bool) :
    ofBool (a ^^ (!b && c)) = ofBool a + ofBool c + ofBool b * ofBool c := by
  cases a <;> cases b <;> cases c <;> simp [ofBool, one_add_one_F64]

theorem testBit_toNat64 (w : UInt64) (z : ℕ) : w.toNat.testBit z = w.toBitVec.getLsbD z := by
  rw [← UInt64.toNat_toBitVec, BitVec.testBit_toNat]

/-! ### The rounds, one at a time -/

/-- The bit state after the first `j` rounds of Keccak-f. -/
def stAfter (s : Bits) (j : ℕ) : Bits := (keccakRC.take j).foldl KeccakBits.round s

theorem keccakRC_length : keccakRC.length = 24 := rfl

theorem stAfter_succ (s : Bits) (j : ℕ) (hj : j < 24) :
    stAfter s (j + 1) = KeccakBits.round (stAfter s j) (keccakRC.getD j 0) := by
  have h1 : keccakRC[j]? = some (keccakRC.getD j 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [keccakRC_length]; exact hj)]
    rfl
  unfold stAfter
  rw [List.take_add_one, List.foldl_append, h1]
  rfl

theorem stAfter_24 (s : Bits) : stAfter s 24 = KeccakBits.keccakF s := by
  unfold stAfter KeccakBits.keccakF
  rw [List.take_of_length_le (by rw [keccakRC_length])]

/-- θ's column parity, its four XORs written out. -/
theorem thetaC_eq (s : Bits) (x z : ℕ) :
    KeccakBits.thetaC s x z = (s x z ^^ s (x + 5) z ^^ s (x + 10) z ^^ s (x + 15) z ^^ s (x + 20) z) := rfl

/-- A round at lane `x + 5y`, χ's neighbours in the row written out. -/
theorem round_apply (t : Bits) (rc : UInt64) (x y z : ℕ) (hx : x < 5) :
    KeccakBits.round t rc (x + 5 * y) z =
      ((KeccakBits.rhoPi (KeccakBits.theta t) (x + 5 * y) z ^^
        (!KeccakBits.rhoPi (KeccakBits.theta t) ((x + 1) % 5 + 5 * y) z &&
          KeccakBits.rhoPi (KeccakBits.theta t) ((x + 2) % 5 + 5 * y) z)) ^^
        (decide (x + 5 * y = 0) && rc.toBitVec.getLsbD z)) := by
  have e1 : (x + 5 * y) % 5 = x := by omega
  have e2 : (x + 5 * y) / 5 = y := by omega
  simp only [KeccakBits.round, KeccakBits.iota, KeccakBits.chi, e1, e2]

/-- The relations, round by round: `A j` is the state after `j` rounds. -/
theorem d16_state {A C D : ℕ → ℕ → ℕ → F64} (h : D16Rel A C D) (s : Bits)
    (hs : ∀ l < 25, ∀ z < 64, A 0 l z = ofBool (s l z)) :
    ∀ j ≤ 24, ∀ l < 25, ∀ z < 64, A j l z = ofBool (stAfter s j l z) := by
  intro j
  induction j with
  | zero => intro _ l hl z hz; exact hs l hl z hz
  | succ j ih =>
    intro hj l hl z hz
    have hA := ih (by omega)
    have hCcol : ∀ x < 5, ∀ z < 64, C j x z = colSum (A j) x z := by
      intro x hx z hz
      rcases j with _ | j'
      · exact h.c0 x hx z hz
      · exact h.cNext j' (by omega) x hx z hz
    have hC : ∀ x < 5, ∀ z < 64, C j x z = ofBool (KeccakBits.thetaC (stAfter s j) x z) := by
      intro x hx z hz
      rw [hCcol x hx z hz, colSum, hA x (by omega) z hz, hA (x + 5) (by omega) z hz, hA (x + 10) (by omega) z hz,
        hA (x + 15) (by omega) z hz, hA (x + 20) (by omega) z hz, thetaC_eq]
      simp only [ofBool_xor]
    have hD : ∀ x < 5, ∀ z < 64, D j x z = ofBool (KeccakBits.thetaD (stAfter s j) x z) := by
      intro x hx z hz
      rw [h.d j (by omega) x hx z hz, hC ((x + 4) % 5) (Nat.mod_lt _ (by decide)) z hz,
        hC ((x + 1) % 5) (Nat.mod_lt _ (by decide)) ((z + 63) % 64) (Nat.mod_lt _ (by decide))]
      simp only [KeccakBits.thetaD, ofBool_xor]
    have hT : ∀ x < 5, ∀ y < 5, ∀ z < 64, chiIn (A j) (D j) x y z
        = ofBool (KeccakBits.rhoPi (KeccakBits.theta (stAfter s j)) (x + 5 * y) z) := by
      intro x hx y hy z _
      have hp : piInv (x + 5 * y) < 25 := piInv_lt _ (by omega)
      simp only [chiIn, KeccakBits.rhoPi, KeccakBits.theta, ofBool_xor]
      rw [hA (piInv (x + 5 * y)) hp ((z + 64 - rho (piInv (x + 5 * y))) % 64) (Nat.mod_lt _ (by decide)),
        hD (piInv (x + 5 * y) % 5) (Nat.mod_lt _ (by decide)) ((z + 64 - rho (piInv (x + 5 * y))) % 64)
          (Nat.mod_lt _ (by decide))]
    obtain ⟨x, y, hx, hy, rfl⟩ : ∃ x y, x < 5 ∧ y < 5 ∧ l = x + 5 * y :=
      ⟨l % 5, l / 5, Nat.mod_lt _ (by decide), by omega, by omega⟩
    rw [h.chi j (by omega) x hx y hy z hz, stAfter_succ s j (by omega), round_apply _ _ x y z hx]
    simp only [chiOut]
    rw [hT x hx y hy z hz, hT ((x + 2) % 5) (Nat.mod_lt _ (by decide)) y hy z hz,
      hT ((x + 1) % 5) (Nat.mod_lt _ (by decide)) y hy z hz, ofBool_xor, ofBool_chi]
    congr 1
    by_cases hxy : x = 0 ∧ y = 0
    · have e : x + 5 * y = 0 := by omega
      rw [ite_eq_left hxy, decide_eq_true e, Bool.true_and, rcBit, testBit_toNat64]
    · have e : ¬ x + 5 * y = 0 := by omega
      rw [ite_eq_right hxy, decide_eq_false e, Bool.false_and]
      rfl

/-- **D16v's Keccak-f is Keccak-f[1600]**: on bits, the relations take the input to `keccakF` of it. -/
theorem d16_keccakF {A C D : ℕ → ℕ → ℕ → F64} (h : D16Rel A C D) (s : Bits)
    (hs : ∀ l < 25, ∀ z < 64, A 0 l z = ofBool (s l z)) :
    ∀ l < 25, ∀ z < 64, A 24 l z = ofBool (KeccakBits.keccakF s l z) := by
  intro l hl z hz
  have := d16_state h s hs 24 le_rfl l hl z hz
  rwa [stAfter_24] at this

/-! ## Keccak-256, any number of blocks -/

/-- Keccak-256's padded message, bit by bit: the message's `n` bits, then `pad10*1` (`0x01` after the message, `0x80`
in the last byte of block `n / 1088`), as `Sponge::keccak256`'s `bit_of`. -/
def padBit (m : ℕ → Bool) (n i : ℕ) : Bool :=
  if i < n then m i else decide (i = n) || decide (i = (n / 1088 + 1) * 1088 - 1)

/-- The sponge's state after block `b`: block 0 is the padded message's first `1088` bits in the rate and zeros in the
capacity, a later block is XORed into the rate of the state before; then Keccak-f. -/
def spongeState (m : ℕ → Bool) (n : ℕ) : ℕ → Bits
  | 0 => KeccakBits.keccakF fun l z => if l < 17 then padBit m n (64 * l + z) else false
  | b + 1 => KeccakBits.keccakF fun l z =>
      if l < 17 then spongeState m n b l z ^^ padBit m n ((b + 1) * 1088 + 64 * l + z) else spongeState m n b l z

/-- Keccak-256 of an `n`-bit message (`n` a multiple of 8), bit `k < 256` of its digest: the first four lanes of the
last block's state. -/
def keccak256Bits (m : ℕ → Bool) (n k : ℕ) : Bool := spongeState m n (n / 1088) (k / 64) (k % 64)

section Sponge

open LeanVM.Semantics

/-- Keccak-f[1600] as the permutation `keccak256` absorbs with. -/
abbrev permF : KeccakState → Id KeccakState := fun s => pure (keccakF1600 s)

/-- One block XORed into the rate of a state of lanes, then Keccak-f[1600] (`absorbBlockWith` in `Id`). -/
def absorbBlk (state : KeccakState) (block : List UInt8) : KeccakState :=
  keccakF1600 (Vector.ofFn fun i => if i.val < 17 then Keccak.lane state i ^^^ leLane block i else Keccak.lane state i)

theorem absorbWith_zero (st : KeccakState) (d : List UInt8) :
    Id.run (absorbWith permF 0 st d) = absorbBlk st (padBlock d) := rfl

theorem absorbWith_succ (k : ℕ) (st : KeccakState) (d : List UInt8) :
    Id.run (absorbWith permF (k + 1) st d) = Id.run (absorbWith permF k (absorbBlk st (d.take 136)) (d.drop 136)) :=
  rfl

theorem keccak256_eq_absorb (data : List UInt8) :
    keccak256 data = #v[Keccak.lane (Id.run (absorbWith permF (data.length / 136) (Vector.replicate 25 0) data)) 0,
      Keccak.lane (Id.run (absorbWith permF (data.length / 136) (Vector.replicate 25 0) data)) 1,
      Keccak.lane (Id.run (absorbWith permF (data.length / 136) (Vector.replicate 25 0) data)) 2,
      Keccak.lane (Id.run (absorbWith permF (data.length / 136) (Vector.replicate 25 0) data)) 3] := rfl

/-- Bit `k < 256` of a digest of the first four lanes of a state is that state's bit. -/
theorem digest_bit (st : KeccakState) (k : ℕ) (hk : k < 256) :
    bitOf (digestBytes #v[Keccak.lane st 0, Keccak.lane st 1, Keccak.lane st 2, Keccak.lane st 3]) k
      = laneBits st (k / 64) (k % 64) := by
  unfold bitOf
  rw [digestBytes_getD _ _ _ _ _ (by omega), wordBytes_bit _ _ _ (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide))]
  have e : 8 * (k / 8 % 8) + k % 8 = k % 64 := by omega
  rw [e, show k / 8 / 8 = k / 64 by omega]
  have hj : k / 64 < 4 := by omega
  simp only [laneBits]
  generalize k / 64 = j at hj ⊢
  have g : ∀ (w0 w1 w2 w3 : UInt64) (j : Nat), j < 4 → #[w0, w1, w2, w3].getD j 0 = [w0, w1, w2, w3].getD j 0 :=
    fun _ _ _ _ _ _ => by simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  rw [g _ _ _ _ _ hj]
  interval_cases j <;> simp only [List.getD_cons_zero, List.getD_cons_succ]

theorem laneBits_ofFn (f : Fin 25 → UInt64) (i z : ℕ) (hi : i < 25) :
    laneBits (Vector.ofFn f) i z = (f ⟨i, hi⟩).toBitVec.getLsbD z := by
  simp only [laneBits, Keccak.lane, Vector.toArray_ofFn, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi,
    dite_true, Option.getD_some]

theorem keccakF_congr {s s' : Bits} (h : BitsEq s s') : BitsEq (KeccakBits.keccakF s) (KeccakBits.keccakF s') :=
  foldl_round_congr keccakRC h

/-- A block absorbed, bit by bit. -/
theorem laneBits_absorbBlk (st : KeccakState) (block : List UInt8) :
    BitsEq (laneBits (absorbBlk st block)) (KeccakBits.keccakF fun l z =>
      if l < 17 then laneBits st l z ^^ (leLane block l).toBitVec.getLsbD z else laneBits st l z) := by
  refine (keccakF_bits _).trans (keccakF_congr ?_)
  intro i hi z _
  rw [laneBits_ofFn _ i z hi]
  by_cases h17 : i < 17
  · simp only [h17, ite_true, laneBits, UInt64.toBitVec_xor, BitVec.getLsbD_xor]
  · simp only [h17, ite_false, laneBits]

theorem getD_take_drop (d : List UInt8) (a q : ℕ) (hq : q < 136) :
    ((d.drop a).take 136).getD q 0 = d.getD (a + q) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hq, ite_true, List.getElem?_drop]

theorem getD_drop (d : List UInt8) (a q : ℕ) : (d.drop a).getD q 0 = d.getD (a + q) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- Byte `q` of the padded last block of `0` to `135` bytes. -/
theorem padBlock_getD' (rest : List UInt8) (hr : rest.length < 136) (q : ℕ) (hq : q < 136) :
    (padBlock rest).getD q 0 = if q < rest.length then rest.getD q 0
      else (if q = rest.length then (1 : UInt8) else 0) ^^^ (if q = 135 then (0x80 : UInt8) else 0) := by
  simp only [padBlock, rate, padFirst, padLast, List.getD_eq_getElem?_getD, List.getElem?_modify,
    List.getElem?_append, List.getElem?_replicate]
  generalize rest.length = r at hr ⊢
  by_cases hqr : q < r
  · have h1 : ¬ r = q := by omega
    have h2 : ¬ 135 = q := by omega
    simp [hqr, h1, h2]
  · have hq2 : q - r < 136 - r := by omega
    simp only [hqr, hq2, ite_false, ite_true]
    by_cases h1 : q = r <;> by_cases h2 : q = 135
    · subst h1; subst h2
      simp
    · subst h1
      simp [h2, Ne.symm h2]
    · subst h2
      simp [h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

/-- Bit `t` of byte `q` of the padded last block. -/
theorem padBlock_bit (rest : List UInt8) (hr : rest.length < 136) (q t : ℕ) (hq : q < 136) (ht : t < 8) :
    ((padBlock rest).getD q 0).toNat.testBit t = if q < rest.length then (rest.getD q 0).toNat.testBit t
      else ((decide (q = rest.length) && decide (t = 0)) || (decide (q = 135) && decide (t = 7))) := by
  rw [padBlock_getD' rest hr q hq]
  generalize rest.length = r at hr ⊢
  by_cases hqr : q < r
  · rw [ite_eq_left hqr, ite_eq_left hqr]
  · rw [ite_eq_right hqr, ite_eq_right hqr]
    by_cases h1 : q = r <;> by_cases h2 : q = 135
    · rw [ite_eq_left h1, ite_eq_left h2, decide_eq_true h1, decide_eq_true h2]
      interval_cases t <;> decide
    · rw [ite_eq_left h1, ite_eq_right h2, decide_eq_true h1, decide_eq_false h2]
      interval_cases t <;> decide
    · rw [ite_eq_right h1, ite_eq_left h2, decide_eq_false h1, decide_eq_true h2]
      interval_cases t <;> decide
    · rw [ite_eq_right h1, ite_eq_right h2, decide_eq_false h1, decide_eq_false h2]
      interval_cases t <;> decide

/-- A whole block's bits are the message's. -/
theorem wholeBlock_bit (data : List UInt8) (b l z : ℕ) (hb : 136 * (b + 1) ≤ data.length) (hl : l < 17)
    (hz : z < 64) :
    (leLane ((data.drop (136 * b)).take 136) l).toBitVec.getLsbD z
      = padBit (bitOf data) (8 * data.length) (b * 1088 + 64 * l + z) := by
  rw [leLane_bit _ _ _ hz, getD_take_drop _ _ _ (by omega)]
  unfold padBit bitOf
  rw [ite_eq_left (by omega), show (b * 1088 + 64 * l + z) / 8 = 136 * b + (8 * l + z / 8) by omega,
    show (b * 1088 + 64 * l + z) % 8 = z % 8 by omega]

/-- The last block's bits are the padded message's. -/
theorem lastBlock_bit (data : List UInt8) (l z : ℕ) (hl : l < 17) (hz : z < 64) :
    (leLane (padBlock (data.drop (136 * (data.length / 136)))) l).toBitVec.getLsbD z
      = padBit (bitOf data) (8 * data.length) (data.length / 136 * 1088 + 64 * l + z) := by
  have hlen : (data.drop (136 * (data.length / 136))).length = data.length - 136 * (data.length / 136) :=
    List.length_drop
  have hr : (data.drop (136 * (data.length / 136))).length < 136 := by omega
  rw [leLane_bit _ _ _ hz, padBlock_bit _ hr _ _ (by omega) (Nat.mod_lt _ (by decide)), hlen]
  unfold padBit bitOf
  by_cases hqr : 8 * l + z / 8 < data.length - 136 * (data.length / 136)
  · rw [ite_eq_left hqr, ite_eq_left (by omega), getD_drop,
      show (data.length / 136 * 1088 + 64 * l + z) / 8 = 136 * (data.length / 136) + (8 * l + z / 8) by omega,
      show (data.length / 136 * 1088 + 64 * l + z) % 8 = z % 8 by omega]
  · rw [ite_eq_right hqr, ite_eq_right (by omega)]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    omega

/-- The state before block `b`: zeros for block `0`, the state after block `b - 1` for the others. -/
def prevState (m : ℕ → Bool) (n : ℕ) : ℕ → Bits
  | 0 => fun _ _ => false
  | b + 1 => spongeState m n b

theorem spongeState_eq (m : ℕ → Bool) (n b : ℕ) :
    spongeState m n b = KeccakBits.keccakF fun l z =>
      if l < 17 then prevState m n b l z ^^ padBit m n (b * 1088 + 64 * l + z) else prevState m n b l z := by
  cases b with
  | zero => simp only [spongeState, prevState, Nat.zero_mul, Nat.zero_add, Bool.false_xor]
  | succ b => rfl

/-- **The sponge, block by block**: absorbing the blocks from block `b` on, from the state before block `b`. -/
theorem absorb_main (data : List UInt8) : ∀ (k b : ℕ) (st : KeccakState), k + b = data.length / 136 →
    BitsEq (laneBits st) (prevState (bitOf data) (8 * data.length) b) →
    BitsEq (laneBits (Id.run (absorbWith permF k st (data.drop (136 * b)))))
      (spongeState (bitOf data) (8 * data.length) (data.length / 136)) := by
  intro k
  induction k with
  | zero =>
    intro b st hkb hst
    have hb : b = data.length / 136 := by omega
    subst hb
    rw [absorbWith_zero, spongeState_eq]
    refine (laneBits_absorbBlk _ _).trans (keccakF_congr ?_)
    intro l hl z hz
    beta_reduce
    by_cases h17 : l < 17
    · rw [ite_eq_left h17, ite_eq_left h17, hst l hl z hz, lastBlock_bit data l z h17 hz]
    · rw [ite_eq_right h17, ite_eq_right h17, hst l hl z hz]
  | succ k ih =>
    intro b st hkb hst
    have e : (data.drop (136 * b)).drop 136 = data.drop (136 * (b + 1)) := by
      rw [List.drop_drop]; exact congrArg (List.drop · data) (by omega)
    rw [absorbWith_succ, e]
    refine ih (b + 1) _ (by omega) ?_
    show BitsEq _ (spongeState _ _ b)
    rw [spongeState_eq]
    refine (laneBits_absorbBlk _ _).trans (keccakF_congr ?_)
    intro l hl z hz
    beta_reduce
    by_cases h17 : l < 17
    · rw [ite_eq_left h17, ite_eq_left h17, hst l hl z hz, wholeBlock_bit data b l z (by omega) h17 hz]
    · rw [ite_eq_right h17, ite_eq_right h17, hst l hl z hz]

theorem laneBits_zero : BitsEq (laneBits (Vector.replicate 25 0)) (fun _ _ => false) := by
  intro i hi z _
  simp [laneBits, Keccak.lane, Array.getD_eq_getD_getElem?, hi]

end Sponge

/-- **Keccak-256 of a byte string, bit by bit, is the sponge** (leanerVM's `keccak256`, its digest's bytes). -/
theorem keccak256_bits_multi (data : List UInt8) (k : ℕ) (hk : k < 256) :
    bitOf (digestBytes (keccak256 data)) k = keccak256Bits (bitOf data) (8 * data.length) k := by
  rw [keccak256_eq_absorb, digest_bit _ k hk]
  unfold keccak256Bits
  rw [show 8 * data.length / 1088 = data.length / 136 by omega]
  have := absorb_main data (data.length / 136) 0 (Vector.replicate 25 0) (by omega) laneBits_zero
  rw [Nat.mul_zero, List.drop_zero] at this
  exact this (k / 64) (by omega) (k % 64) (Nat.mod_lt _ (by decide))

end RecCircuit
