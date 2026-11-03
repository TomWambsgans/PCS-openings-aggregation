-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCircuit.ExpandProof

/-!
# π1's `PCS_OPEN` inputs, rebuilt from π2's ports

π2's verifier makes π1's `PCS_OPEN` calls from π2's public inputs, which the ports carry (`spec.rs`'s
`Circuit::call_inputs`): a constant word as it is; a root its port's word (`word_limbs`'s inverse); an element its
port's `element_word`; a pair's coordinate (π1-rec3's paired batch) `element_word` of `pair_point` of its element's
port (`Circuit.callWordBytes`, `Circuit.callInputs`).

On a satisfied circuit the compiler accepted, each of these words is π1's graph's word in `RecGraph`'s semantics over
Keccak-f[1600] (`compile_sound_calls`), word 0 (a call's root, a stream root or a setup root) as `PCS_OPEN`'s root
word (`machine::root_word`, each 16-byte half reversed: `pcsWord`), all other words byte for byte. The calls check
(`callsOk`) ties π2's call words to π1's; the pair's semantics (`pair_val`) is `pair_point`'s on the expanded graph's
values (`y_1 = z·z + z`, `y_0 = z + β_1 y_1`, `β_1 = UniStatement.cantorBeta1`); `expandSound` takes a node's
image's value back to the original graph.
-/

namespace RecCircuit

open Primitives LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement

/-! ## π2's rebuild (`Circuit::call_inputs`) -/

namespace Circuit

variable (C : Circuit)

/-- The 32 bytes whose `word_limbs` are four limbs (limb `l` the big-endian bytes `24 − 8l .. 32 − 8l`). -/
def limbsBytes (ls : List K) : List UInt8 :=
  be64 (K.lane (ls.getD 3 0)) ++ be64 (K.lane (ls.getD 2 0)) ++ be64 (K.lane (ls.getD 1 0)) ++
    be64 (K.lane (ls.getD 0 0))

/-- An element of its three limbs. -/
def limbsE (ls : List K) : E := eNew (K.lane (ls.getD 0 0)) (K.lane (ls.getD 1 0)) (K.lane (ls.getD 2 0))

/-- A source's port's limbs. -/
def sourceLimbs (w : ℕ → K) (s : Source) : List K := C.portLimbs w ((C.portOf s).getD 0)

/-- **π1's `PCS_OPEN` word rebuilt from π2's ports** (`Circuit::call_inputs` on the public inputs the ports carry). -/
def callWordBytes (w : ℕ → K) : CallWord → List UInt8
  | .const x => wordBytes32 x
  | .root i => limbsBytes (C.sourceLimbs w (.root i))
  | .element e => UniStatement.elementWord (limbsE (C.sourceLimbs w (.element e)))
  | .pair e co => UniStatement.elementWord ((pairPoint (limbsE (C.sourceLimbs w (.element e)))).getD co 0)

/-- **π1's `PCS_OPEN` inputs rebuilt from π2's ports**, in call order. -/
def callInputs (w : ℕ → K) : List (List UInt8) := C.calls.map (·.flatMap (C.callWordBytes w))

end Circuit

/-- **The word of a `PCS_OPEN` call at position `k`**, of the graph's word bytes: word 0 (the call's root) as
`PCS_OPEN`'s root word (`machine::root_word`). -/
def pcsWord (k : ℕ) (bytes : List UInt8) : List UInt8 := if k = 0 then rootWordBytes bytes else bytes

/-! ## Bytes -/

theorem leNat_cons (b : UInt8) (bs : List UInt8) : leNat (b :: bs) = b.toNat + 256 * leNat bs := rfl

theorem leNat_lt : ∀ s : List UInt8, leNat s < 256 ^ s.length
  | [] => by simp [leNat]
  | b :: bs => by
    rw [leNat_cons, List.length_cons, pow_succ]
    have := leNat_lt bs
    have := b.toNat_lt
    omega

theorem leNat_digit : ∀ (s : List UInt8) (j : ℕ) (hj : j < s.length), leNat s / 256 ^ j % 256 = (s[j]).toNat
  | [], j, hj => absurd hj (by simp)
  | b :: bs, 0, _ => by
    rw [leNat_cons, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.toNat_lt]
    rfl
  | b :: bs, j + 1, hj => by
    rw [leNat_cons, pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by norm_num),
      Nat.div_eq_of_lt b.toNat_lt, zero_add, leNat_digit bs j (by simpa using hj)]
    rfl

/-- `be64` of a little-endian word is its bytes reversed. -/
theorem be64_leNat (s : List UInt8) (hs : s.length = 8) : be64 (UInt64.ofNat (leNat s)) = s.reverse := by
  have hlt : leNat s < 2 ^ 64 := by
    have := leNat_lt s; rw [hs] at this; simpa using this
  apply List.ext_getElem
  · simp [be64, hs]
  · intro k h1 h2
    have hk : k < 8 := by simpa [be64] using h1
    simp only [be64, List.getElem_map, List.getElem_range, List.getElem_reverse]
    apply UInt8.toNat.inj
    rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]
    have h8 : (8 * (7 - k)).toUInt64.toNat % 64 = 8 * (7 - k) := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [h8, Nat.shiftRight_eq_div_pow, pow_mul, show (2 : ℕ) ^ 8 = 256 by norm_num,
      leNat_digit s (7 - k) (by omega)]
    have : s.length - 1 - k = 7 - k := by omega
    simp only [this]

theorem lane_ofNat (n : ℕ) : K.lane (F64.ofNat n) = UInt64.ofNat n := by
  rw [← ofLane_ofNat, lane_ofLane]

/-- **A root port's word is the root's `PCS_OPEN` word** (the stream's 32 bytes, each half reversed). -/
theorem root_bytes (raw : List UInt8) (hr : raw.length = 32) :
    Circuit.limbsBytes ((List.range 4).map fun l => F64.ofNat (leNat (slice raw ([16, 24, 0, 8].getD l 0) 8))) =
      rootWordBytes raw := by
  have hs : ∀ a, a + 8 ≤ 32 → (slice raw a 8).length = 8 := fun a ha => slice_length raw a 8 (by omega)
  show Circuit.limbsBytes [F64.ofNat (leNat (slice raw 16 8)), F64.ofNat (leNat (slice raw 24 8)),
    F64.ofNat (leNat (slice raw 0 8)), F64.ofNat (leNat (slice raw 8 8))] = _
  simp only [Circuit.limbsBytes, List.getD_cons_succ, List.getD_cons_zero, lane_ofNat]
  rw [be64_leNat _ (hs 8 (by norm_num)), be64_leNat _ (hs 0 (by norm_num)), be64_leNat _ (hs 24 (by norm_num)),
    be64_leNat _ (hs 16 (by norm_num))]
  have ht : raw.take 16 = slice raw 0 8 ++ slice raw 8 8 := by
    rw [show (16 : ℕ) = 8 + 8 from rfl, List.take_add]
    simp [slice]
  have hd : raw.drop 16 = slice raw 16 8 ++ slice raw 24 8 := by
    have hl : (raw.drop 16).length = 8 + 8 := by simp [hr]
    rw [← List.take_length (l := raw.drop 16), hl, List.take_add]
    simp [slice, List.drop_drop]
  rw [rootWordBytes, ht, hd, List.reverse_append, List.reverse_append]
  simp only [List.append_assoc]

/-- `limbsL`'s limbs rebuild the element. -/
theorem limbsE_limbsL (x : E) : Circuit.limbsE (Compiled.limbsL x) = x := by
  simp only [Circuit.limbsE, Compiled.limbsL, List.getD_cons_succ, List.getD_cons_zero]
  exact RecGraph.eNew_limbs x

end RecCircuit
