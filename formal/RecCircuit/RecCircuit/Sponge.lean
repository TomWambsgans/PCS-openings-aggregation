-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCircuit.Gates

/-!
# Keccak-256's sponge on a satisfied circuit

A checked sponge (`spongeOk`) over checked Keccak-f instances computes Keccak-256 of its message bit by bit
(`sponge_digest`): block 0 is the padded message with zeros in the capacity (`pad10*1`'s constants and the capacity's
are `κ`), a later block the state XOR the padded message's rate (a zero bit passed through, a one through a fresh
constant 1), each block's state `keccakF` of its input (`keccak_out`), the digest the last state's first 256 bits;
that is `KeccakMath.spongeState`, hence `keccak256Bits`.
-/

namespace RecCircuit

open Primitives

namespace Ctx

variable {X : Ctx} {w : ℕ → K}

/-- **What a message bit means**: a value carries the bit, a constant is it. -/
def BitMeans (X : Ctx) (w : ℕ → K) (b : Bit) (bit : Bool) : Prop :=
  match b with
  | .v u => X.val w u = ofBool bit
  | .one => bit = true
  | .zero => bit = false

/-- **The meaning of a message**: bit `i` means `mb i`. -/
def MsgOk (X : Ctx) (w : ℕ → K) (msg : Array Bit) (mb : ℕ → Bool) : Prop :=
  ∀ i < msg.size, BitMeans X w (msg.getD i .zero) (mb i)

theorem getD_mem {α : Type} {a : Array α} {i : ℕ} (d : α) (h : i < a.size) : a.getD i d ∈ a := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- The padded message's bits, as the sponge makes them, mean `padBit`. -/
theorem padBitOf_rel {msg : Array Bit} {mb : ℕ → Bool} (hm : MsgOk X w msg mb) (i : ℕ) :
    BitMeans X w (padBitOf msg i) (padBit mb msg.size i) := by
  unfold padBitOf padBit
  by_cases hi : i < msg.size
  · simp only [hi, ite_true]
    exact hm i hi
  · simp only [hi, ite_false]
    by_cases hp : (i == msg.size || i == (msg.size / 1088 + 1) * 1088 - 1) = true
    · simp only [hp, ite_true, BitMeans]
      simpa using hp
    · simp only [hp, Bool.false_eq_true, ite_false, BitMeans]
      simpa using hp

theorem inOk_val (G : X.Good w) {b : Bit} {x : ℕ} {bit : Bool} (h : X.inOk b x = true)
    (hb : BitMeans X w b bit) : X.val w x = ofBool bit := by
  unfold BitMeans at hb
  cases b with
  | v u => simp only [inOk, beq_iff_eq] at h; subst h; exact hb
  | one => simp only [inOk] at h; rw [const_val G h, hb]; rfl
  | zero => simp only [inOk] at h; rw [const_val G h, hb]; rfl

/-- **A checked sponge computes Keccak-256 of its message, bit by bit.** -/
theorem sponge_digest (G : X.Good w) {keccaks : Array KeccakT} (hk : ∀ t ∈ keccaks, X.keccakOk t = true)
    {s : SpongeT} (h : X.spongeOk keccaks s = true) {mb : ℕ → Bool} (hm : MsgOk X w s.message mb) :
    ∀ k < 256, X.val w (s.digest.getD k NONE) = ofBool (keccak256Bits mb s.message.size k) := by
  simp only [spongeOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Array.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hsize, hperms⟩, h0⟩, hlater⟩, hdsize⟩, hdig⟩ := h
  set n := s.message.size
  let inst := fun (b : ℕ) => keccaks.getD (s.perms.getD b 0) default
  have hinst : ∀ b < n / 1088 + 1, X.keccakOk (inst b) = true := by
    intro b hb
    apply hk
    have hb' : b < s.perms.size := hsize ▸ hb
    have hlt := hperms b hb'
    simp only [decide_eq_true_eq] at hlt
    have : s.perms.getD b 0 = s.perms[b] := by simp [Array.getD_eq_getD_getElem?, hb']
    simp only [inst, this]
    exact getD_mem _ hlt
  -- The state after each block.
  have hstate : ∀ b < n / 1088 + 1, ∀ l < 25, ∀ z < 64,
      KeccakT.A X w (inst b) 24 l z = ofBool (spongeState mb n b l z) := by
    intro b
    induction b with
    | zero =>
      intro hb
      apply keccak_out G (hinst 0 hb)
      intro l hl z hz
      have hi : 64 * l + z < 1600 := by omega
      have := allBelow_spec h0 _ hi
      rw [KeccakT.A]
      apply inOk_val G this
      by_cases hr : 64 * l + z < 1088
      · have hl17 : l < 17 := by omega
        simp only [hr, ite_true, hl17]
        exact padBitOf_rel hm _
      · have hl17 : ¬ l < 17 := by omega
        simp only [hr, ite_false, hl17]
        rfl
    | succ b ih =>
      intro hb
      apply keccak_out G (hinst (b + 1) hb)
      intro l hl z hz
      have hi : 64 * l + z < 1600 := by omega
      have hprev := ih (by omega) l hl z hz
      have := allBelow_spec (allBelow_spec hlater (b + 1) hb) (64 * l + z) hi
      simp only [Nat.add_one_ne_zero, beq_iff_eq, false_or, Nat.add_sub_cancel] at this
      rw [KeccakT.A]
      by_cases hr : 1088 ≤ 64 * l + z
      · have hl17 : ¬ l < 17 := by omega
        simp only [hr, ite_true, beq_iff_eq] at this
        simp only [hl17, ite_false]
        rw [this]; exact hprev
      · have hl17 : l < 17 := by omega
        simp only [hr, ite_false] at this
        simp only [hl17, ite_true]
        have hrel := padBitOf_rel hm ((b + 1) * 1088 + (64 * l + z))
        have e : (b + 1) * 1088 + 64 * l + z = (b + 1) * 1088 + (64 * l + z) := by ring
        rw [e]
        unfold BitMeans at hrel
        revert this hrel
        cases padBitOf s.message ((b + 1) * 1088 + (64 * l + z)) with
        | zero =>
          intro this hrel
          simp only [beq_iff_eq] at this
          rw [this, hrel, Bool.xor_false]; exact hprev
        | v u =>
          intro this hrel
          rw [xor_val G this, hrel, ofBool_xor, ← hprev]; rfl
        | one =>
          intro this hrel
          simp only [Bool.and_eq_true] at this
          rw [xor_val G this.1, const_val G this.2, hrel, ofBool_xor, ← hprev]; rfl
  intro k hk
  have := allBelow_spec hdig k hk
  simp only [beq_iff_eq] at this
  rw [this]
  have e : k = 64 * (k / 64) + k % 64 := by omega
  have hst := hstate (n / 1088) (by omega) (k / 64) (by omega) (k % 64) (Nat.mod_lt _ (by norm_num))
  rw [KeccakT.A, ← e] at hst
  simp only [Nat.add_sub_cancel]
  exact hst

end Ctx

end RecCircuit
