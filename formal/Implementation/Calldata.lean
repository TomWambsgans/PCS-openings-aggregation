-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Implementation.Interp
import Implementation.Field
import QuotientRpm.Chain

/-!
# Calldata and the chain, byte for byte

The graph reads big-endian words of calldata and hashes big-endian words (`Interp.lean`); the
model (`QuotientRpm`) reads limbs of bytes and hashes `scalarWord`s and `rootWords`. This file
proves they agree:

* `beNat` / `beBytes` (`MSTORE` of a `CALLDATALOAD`) round-trip, and a state's low 192 bits as a
  number are its `stateLimbs` (`natLimbs_state`);
* `calldataOf`: the calldata of a statement's 64 bytes, two roots and five values, as
  `crates/evm/src/quotient.rs`'s `calldata` writes it (a root's halves reversed, a value's limbs
  `c2, c1, c0` big-endian); and the words the graph reads from it (`cdWord_window`).
-/

set_option linter.unusedSectionVars false

namespace Implementation

open QuotientRpm LeanVM.Protocol.KeccakHash LeanVM.Rpm

/-! ## Big-endian numbers -/

theorem foldl_beNat (l : List UInt8) (acc : Nat) :
    l.foldl (fun acc b => acc * 256 + b.toNat) acc = acc * 256 ^ l.length + beNat l := by
  induction l generalizing acc with
  | nil => simp [beNat]
  | cons x l ih =>
    simp only [List.foldl_cons, beNat] at *
    rw [ih, ih (0 * 256 + x.toNat), List.length_cons, pow_succ]
    ring

theorem beNat_append (a b : List UInt8) : beNat (a ++ b) = beNat a * 256 ^ b.length + beNat b := by
  rw [beNat, List.foldl_append, foldl_beNat]
  rfl

theorem beNat_cons (x : UInt8) (l : List UInt8) :
    beNat (x :: l) = x.toNat * 256 ^ l.length + beNat l := by
  rw [show x :: l = [x] ++ l from rfl, beNat_append]
  simp [beNat]

theorem beNat_lt (l : List UInt8) : beNat l < 256 ^ l.length := by
  induction l with
  | nil => simp [beNat]
  | cons x l ih =>
    rw [beNat_cons, List.length_cons, pow_succ]
    have hx : x.toNat < 256 := x.toNat_lt
    nlinarith

theorem beNat_replicate_zero (k : Nat) : beNat (List.replicate k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, beNat_cons, ih]; simp

theorem beNat_take_div (l : List UInt8) (j : Nat) (hj : j ≤ l.length) :
    beNat l / 256 ^ (l.length - j) = beNat (l.take j) := by
  have e := beNat_append (l.take j) (l.drop j)
  rw [List.take_append_drop, List.length_drop] at e
  have hlt := beNat_lt (l.drop j)
  rw [List.length_drop] at hlt
  rw [e, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]

theorem beNat_snoc_mod (l : List UInt8) (x : UInt8) : beNat (l ++ [x]) % 256 = x.toNat := by
  rw [beNat_append]
  simp [beNat, Nat.add_mod, x.toNat_lt]

theorem beBytes_beNat (l : List UInt8) : beBytes l.length (beNat l) = l := by
  apply List.ext_getElem (by simp [beBytes])
  intro k h1 h2
  have hk : k < l.length := by
    simp only [beBytes, List.length_map, List.length_range] at h1; exact h1
  simp only [beBytes, List.getElem_map, List.getElem_range]
  have hpow : 2 ^ (8 * (l.length - 1 - k)) = 256 ^ (l.length - (k + 1)) := by
    rw [pow_mul, show l.length - 1 - k = l.length - (k + 1) by omega]; norm_num
  rw [Nat.shiftRight_eq_div_pow, hpow, beNat_take_div l (k + 1) hk,
    List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, beNat_snoc_mod]
  exact UInt8.toNat.inj (by simp)

theorem beBytes_pad (k : Nat) (l : List UInt8) :
    beBytes (k + l.length) (beNat l) = List.replicate k 0 ++ l := by
  have e : beNat l = beNat (List.replicate k 0 ++ l) := by
    rw [beNat_append, beNat_replicate_zero, zero_mul, zero_add]
  rw [e, show k + l.length = (List.replicate k 0 ++ l).length by simp, beBytes_beNat]

/-! ## Limbs -/

theorem toNat_bytesLane (l : List UInt8) (hl : l.length = 8) :
    (bytesLane l).toNat = beNat l.reverse := by
  match l, hl with
  | [x0, x1, x2, x3, x4, x5, x6, x7], _ =>
    have h0 := x0.toNat_lt; have h1 := x1.toNat_lt; have h2 := x2.toNat_lt; have h3 := x3.toNat_lt
    have h4 := x4.toNat_lt; have h5 := x5.toNat_lt; have h6 := x6.toNat_lt; have h7 := x7.toNat_lt
    simp only [bytesLane, List.range_succ, List.range_zero, List.nil_append, List.foldr_append,
      List.foldr_cons, List.foldr_nil, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, beNat, List.foldl_cons, List.foldl_nil,
      UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (by omega)]
    ring

theorem toNat_ofBe64 (l : List UInt8) (hl : 8 ≤ l.length) : (ofBe64 l).toNat = beNat (l.take 8) := by
  rw [ofBe64, toNat_bytesLane _ (by simp; omega), List.reverse_reverse]

theorem beNat_be64 (w : UInt64) : beNat (be64 w) = w.toNat := by
  rw [be64, ← toNat_bytesLane _ (wordBytes_len w)]
  have := bytesLane_wordBytes_append w []
  rw [List.append_nil] at this
  rw [this]

theorem length_be64' (w : UInt64) : (be64 w).length = 8 := length_be64 w

/-- A state's low 192 bits, as a number, are its `stateLimbs`. -/
theorem limbsNat_stateLimbs (st : Bytes32) : limbsNat (stateLimbs st) = beNat st.toList % B192 := by
  have hl : st.toList.length = 32 := st.length_toList
  simp only [limbsNat, stateLimbs, wordLimbs, ofLimbs]
  rw [toNat_ofBe64 _ (by simp only [List.length_drop]; omega),
    toNat_ofBe64 _ (by simp only [List.length_drop]; omega),
    toNat_ofBe64 _ (by simp only [List.length_drop]; omega)]
  generalize st.toList = l at hl ⊢
  have h24 : (l.drop 24).take 8 = l.drop 24 := List.take_of_length_le (by simp; omega)
  have e : l = l.take 8 ++ (l.drop 8).take 8 ++ (l.drop 16).take 8 ++ l.drop 24 := by
    have e1 := List.take_append_drop 8 l
    have e2 := List.take_append_drop 8 (l.drop 8)
    have e3 := List.take_append_drop 8 (l.drop 16)
    rw [List.drop_drop] at e2 e3
    rw [List.append_assoc, List.append_assoc, e3, e2, e1]
  rw [h24]
  conv_rhs => rw [e]
  have b1 := beNat_lt ((l.drop 8).take 8)
  have b2 := beNat_lt ((l.drop 16).take 8)
  have b3 := beNat_lt (l.drop 24)
  simp only [List.length_take, List.length_drop, hl] at b1 b2 b3
  norm_num at b1 b2 b3
  rw [beNat_append, beNat_append, beNat_append]
  simp only [List.length_take, List.length_drop, hl]
  norm_num
  try unfold B192
  try unfold B64
  omega

theorem natLimbs_state (st : Bytes32) : natLimbs (beNat st.toList % B192) = stateLimbs st := by
  rw [← limbsNat_stateLimbs, natLimbs_limbsNat]

/-- The bytes of `F192`'s limbs, `c2, c1, c0`, big-endian: a scalar in calldata. -/
def scalarBytes (x : Limbs) : List UInt8 := be64 x.2.2 ++ be64 x.2.1 ++ be64 x.1

@[simp] theorem length_scalarBytes (x : Limbs) : (scalarBytes x).length = 24 := by
  simp [scalarBytes]

theorem beNat_scalarBytes (x : Limbs) : beNat (scalarBytes x) = limbsNat x := by
  simp only [scalarBytes, beNat_append, beNat_be64, length_be64, limbsNat, ofLimbs]
  unfold B64
  ring

theorem scalarWord_eq (x : Limbs) : scalarWord x = List.replicate 8 0 ++ scalarBytes x := by
  simp [scalarWord, scalarBytes]

/-- A root's bytes in calldata: its halves reversed (`quotient.rs`'s `calldata`: each scalar's
limbs `c1, c0` big-endian, the limbs the little-endian words of the half). -/
def rootBytes (r : Bytes32) : List UInt8 := (r.toList.take 16).reverse ++ (r.toList.drop 16).reverse

@[simp] theorem length_rootBytes (r : Bytes32) : (rootBytes r).length = 32 := by
  have := r.length_toList
  simp [rootBytes, this]

/-! ## Words of calldata -/

theorem cdWord_window (A B C : List UInt8) (hB : B.length = 32) :
    cdWord (A ++ B ++ C) A.length = beNat B := by
  unfold cdWord
  congr 1
  apply List.ext_getElem (by simp [hB])
  intro j h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega)]
  rfl

theorem cdWord_tail (A B : List UInt8) (hB : B.length = 24) :
    cdWord (A ++ B) A.length = beNat B * 2 ^ 64 := by
  unfold cdWord
  have e : (List.range 32).map (fun k => (A ++ B).getD (A.length + k) 0) = B ++ List.replicate 8 0 := by
    apply List.ext_getElem (by simp [hB])
    intro j h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    by_cases hj : j < 24
    · rw [List.getElem_append_left (by omega), List.getElem?_eq_getElem (by omega)]; rfl
    · rw [List.getElem_append_right (by omega), List.getElem_replicate,
        List.getElem?_eq_none (by omega)]
      rfl
  rw [e, beNat_append, beNat_replicate_zero]
  simp

theorem half_beNat (a b : List UInt8) (ha : a.length = 16) (hb : b.length = 16) (k : Nat) :
    half (beNat (a ++ b)) k = if k % 2 = 0 then beNat a else beNat b := by
  have hlt := beNat_lt b
  rw [hb] at hlt
  rw [half, beNat_append, hb]
  split_ifs
  · rw [Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 128 = 256 ^ 16 by norm_num,
      Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]
  · rw [show (2 : Nat) ^ 128 = 256 ^ 16 by norm_num, Nat.add_comm, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hlt]

/-- The calldata of a call of the verifier (`quotient.rs`'s `calldata`): the selector, the
statement's 64 bytes, the two roots, the five values. -/
def calldataOf {F : Type} (limbs : F ≃ Limbs) (sb : Vector UInt8 64) (r₁ r₂ : Bytes32) (vs : List F) :
    List UInt8 :=
  bytesOf Emitted.selector ++ sb.toList ++ rootBytes r₁ ++ rootBytes r₂ ++
    vs.flatMap fun x => scalarBytes (limbs x)

end Implementation
