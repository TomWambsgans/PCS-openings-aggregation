-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import PcsQuotient.Verifier
import Soundness.Defs

/-!
# The statement's Keccak-256 chain is F4's

The statement's reduction (`PcsQuotient.reduceWith`, `Transcript.lean`) and F4's chain
(`Compose.chainWith`, F4a's bytes `QuotientRpm`) both transcribe `crates/quotient/src/transcript.rs`.
Here, byte for byte:

* the label (`label_eq`), a digest's bytes (`toB_toList`), a scalar's word (`scalarBytes_eq`: the
  statement's `scalarBytes` is `scalarWord` of `eLimbs`), a root's two scalars (`rootScalars_eq`:
  the proof's two scalars, when they name a digest, are the words F4 hashes for it), the challenge of
  a state (`challengeOf_eq`: the low 192 bits, big-endian, `beWord_eq`);
* **`reduceWith_eq`**: for every monad and permutation `F`, on a proof whose two roots' scalars
  name digests `r₁`, `r₂`, the statement's reduction is F4's chain over Keccak-256 `= keccak256With F`
  (`chainWith` of any `Wire` with limbs `eLimbs`, on the converted proof), followed by the statement's
  claims (`claimsAt`) at the chain's challenges.
-/

namespace Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open QuotientRpm QuotientSecurity

/-! ## Bytes -/

theorem toB_toList (d : Digest) : (Compose.toB d).toList = digestBytes d := by
  rw [Compose.toB, LeanVM.Rpm.toList_digestToRpm]
  rfl

theorem tag_eq : "pcs-quotient-kc1".toUTF8.toList = QuotientRpm.tag := by decide +kernel

/-- **The chain's label** (`protocol::label`), transcribed twice. -/
theorem label_eq (ir : Digest) (stmt : PcsQuotient.Statement) :
    PcsQuotient.label ir stmt = Compose.labelOf (Compose.toB ir) (stmt.y ++ stmt.root) := by
  simp only [PcsQuotient.label, Compose.labelOf, tag_eq, toB_toList, Vector.toList_append,
    List.append_assoc]

/-- **A scalar's word** (`Chain::sample`): the statement's `scalarBytes` is F4a's `scalarWord` of
its limbs. -/
theorem scalarBytes_eq (x : E) :
    PcsQuotient.Transcript.scalarBytes x = scalarWord (Soundness.eLimbs x) := rfl

theorem lane_zero : (0 : K).lane = 0 := rfl

theorem drop_wordBytes_append (w : UInt64) (rest : List UInt8) :
    (wordBytes w ++ rest).drop 8 = rest :=
  List.drop_left' (LeanVM.Rpm.wordBytes_len w)

theorem drop_wordBytes_append₂ (a b : UInt64) (rest : List UInt8) :
    (wordBytes a ++ (wordBytes b ++ rest)).drop 16 = rest := by
  rw [show 16 = 8 + 8 from rfl, ← List.drop_drop, drop_wordBytes_append, drop_wordBytes_append]

theorem drop_wordBytes_append₃ (a b c : UInt64) (rest : List UInt8) :
    (wordBytes a ++ (wordBytes b ++ (wordBytes c ++ rest))).drop 24 = rest := by
  rw [show 24 = 8 + 16 from rfl, ← List.drop_drop, drop_wordBytes_append, drop_wordBytes_append₂]

/-- **A root's two scalars** (`root_scalars`): when the proof's two scalars name a digest `r`, the words
F4 hashes for `r` (`rootWords`) are the statement's words of the two scalars. -/
theorem rootScalars_eq (w : E × E) (r : Digest) (h : digestOfScalars w = some r) :
    rootWords (Compose.toB r) =
      PcsQuotient.Transcript.scalarBytes w.1 ++ PcsQuotient.Transcript.scalarBytes w.2 := by
  unfold digestOfScalars at h
  split_ifs at h with hc
  cases h
  obtain ⟨h1, h2⟩ := hc
  rw [scalarBytes_eq, scalarBytes_eq, rootWords]
  have hl : (Compose.toB #v[(w.1.limb 0).lane, (w.1.limb 1).lane, (w.2.limb 0).lane,
      (w.2.limb 1).lane]).toList = wordBytes (w.1.limb 0).lane ++ (wordBytes (w.1.limb 1).lane ++
        (wordBytes (w.2.limb 0).lane ++ (wordBytes (w.2.limb 1).lane ++ []))) := by
    rw [toB_toList]; rfl
  have e1 : (w.1.limb 2).lane = 0 := by rw [show w.1.limb 2 = 0 from h1]; rfl
  have e2 : (w.2.limb 2).lane = 0 := by rw [show w.2.limb 2 = 0 from h2]; rfl
  simp only [rootScalars, hl, drop_wordBytes_append, drop_wordBytes_append₂, drop_wordBytes_append₃,
    LeanVM.Rpm.bytesLane_wordBytes_append, Soundness.eLimbs, Equiv.coe_fn_mk, e1, e2]

/-! ## The challenge of a state -/

theorem shift_or_toNat (a : UInt64) (x : UInt8) (ha : a.toNat < 2 ^ 56) :
    ((a <<< 8) ||| x.toUInt64).toNat = x.toNat + 256 * a.toNat := by
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft]
  have h8 : (8 : UInt64).toNat % 64 = 8 := rfl
  rw [h8, UInt8.toNat_toUInt64]
  have hlt : a.toNat <<< 8 < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq]; omega
  rw [Nat.mod_eq_of_lt hlt, ← Nat.shiftLeft_add_eq_or_of_lt (by have := x.toNat_lt; omega),
    Nat.shiftLeft_eq]
  omega

theorem foldl_shift_or_toNat : ∀ (l : List UInt8) (a : UInt64), l.length ≤ 8 →
    a.toNat < 256 ^ (8 - l.length) →
      (l.foldl (fun (acc : UInt64) (x : UInt8) => (acc <<< 8) ||| x.toUInt64) a).toNat =
        l.foldl (fun (acc : ℕ) (x : UInt8) => x.toNat + 256 * acc) a.toNat
  | [], a, _, _ => rfl
  | x :: l, a, hl, h => by
    simp only [List.length_cons] at hl h
    simp only [List.foldl_cons]
    have hk : 8 - l.length = (8 - (l.length + 1)) + 1 := by omega
    have hP : 256 ^ (8 - (l.length + 1)) ≤ 256 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have ha : a.toNat < 2 ^ 56 := by
      have : (256 : ℕ) ^ 7 = 2 ^ 56 := by norm_num
      omega
    have hs := shift_or_toNat a x ha
    rw [foldl_shift_or_toNat l _ (by omega) ?_, hs]
    rw [hs, hk, pow_succ]
    have hx := x.toNat_lt
    omega

theorem getD_take_drop (b : List UInt8) (s k : ℕ) (hk : k < 8) :
    ((b.drop s).take 8).getD k 0 = b.getD (s + k) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk, List.getElem?_drop]

/-- **The low 192 bits read big-endian**: the statement's `beWord` of eight bytes is F4a's `ofBe64`. -/
theorem beWord_eq (b : List UInt8) (s : ℕ) (h : s + 8 ≤ b.length) :
    PcsQuotient.Transcript.beWord b s = ofBe64 (b.drop s) := by
  set l := (b.drop s).take 8 with hl
  have hlen : l.length = 8 := by simp [hl]; omega
  have hmap : (List.range 8).map (fun k => b.getD (s + k) 0) = l := by
    rw [← range_map_getD l hlen]
    refine List.map_congr_left fun k hk => ?_
    rw [getD_take_drop b s k (List.mem_range.mp hk)]
  have hL : PcsQuotient.Transcript.beWord b s =
      l.foldl (fun (acc : UInt64) (x : UInt8) => (acc <<< 8) ||| x.toUInt64) 0 := by
    rw [← hmap, List.foldl_map]
    rfl
  have hR : ofBe64 (b.drop s) =
      UInt64.ofNat (l.foldl (fun (acc : ℕ) (x : UInt8) => x.toNat + 256 * acc) 0) := by
    have hrev : (List.range 8).map (fun i => l.reverse.getD i 0) = l.reverse :=
      range_map_getD l.reverse (by simp [hlen])
    rw [ofBe64, ← hl, LeanVM.Rpm.bytesLane]
    refine congrArg UInt64.ofNat ?_
    rw [← List.foldr_reverse]
    conv_rhs => rw [← hrev]
    rw [List.foldr_map]
  rw [hL, hR]
  have hN := foldl_shift_or_toNat l 0 (by omega) (by simp [hlen])
  have h0 : (0 : UInt64).toNat = 0 := rfl
  rw [h0] at hN
  refine UInt64.toNat_inj.mp ?_
  rw [hN, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (hN ▸ UInt64.toNat_lt _)]

/-- **The challenge of a state** (`Chain::sample`): the statement's `challengeOf` is F4's `chal` with
the limbs `eLimbs`, on the state's 32 bytes. -/
theorem challengeOf_eq (st : Digest) :
    PcsQuotient.Transcript.challengeOf st = Soundness.eLimbs.symm (stateLimbs (Compose.toB st)) := by
  have hlen : (digestBytes st).length = 32 := by
    simp [digestBytes, LeanVM.Rpm.wordBytes_len, List.length_flatMap]
  simp only [PcsQuotient.Transcript.challengeOf, stateLimbs, wordLimbs, toB_toList,
    beWord_eq _ _ (by omega : 24 + 8 ≤ (digestBytes st).length),
    beWord_eq _ _ (by omega : 16 + 8 ≤ (digestBytes st).length),
    beWord_eq _ _ (by omega : 8 + 8 ≤ (digestBytes st).length)]
  rfl

/-! ## The reduction's chain -/

/-- **The reduction's proof as F4 reads it** (`Compose.RootProof`): the statement's bytes `y ‖ root`,
the two roots the proof's scalars name, the four values and `next`, the circuit's commitment `ir`
(the label's). -/
def rootProofIr (ir : Digest) (stmt : PcsQuotient.Statement) (p : PcsQuotient.ReductionProof)
    (r₁ r₂ : Digest) : Compose.RootProof E :=
  ⟨stmt.y ++ stmt.root, Compose.toB r₁, Compose.toB r₂, (fun i => p.values.get i, p.next),
    Compose.toB ir⟩

theorem foldl_absorb (l : List E) (c : PcsQuotient.Transcript.Chain) :
    (l.foldl PcsQuotient.Transcript.Chain.absorb c).pending = c.pending ++ l := by
  induction l generalizing c with
  | nil => simp
  | cons x l ih => simp [List.foldl_cons, ih, PcsQuotient.Transcript.Chain.absorb]

theorem foldl_absorb_state (l : List E) (c : PcsQuotient.Transcript.Chain) :
    (l.foldl PcsQuotient.Transcript.Chain.absorb c).state = c.state := by
  induction l generalizing c with
  | nil => simp
  | cons x l ih => simp [List.foldl_cons, ih, PcsQuotient.Transcript.Chain.absorb]

/-- **The statement's reduction is F4's chain, then the statement's claims**: for every monad and
permutation `F`, on a proof whose roots' scalars name digests `r₁`, `r₂`, `reduceWith F 22` hashes
exactly what `Compose.chainWith` hashes over Keccak-256 `= keccak256With F` (any `Wire` with the
limbs `eLimbs`), in the same order, and returns the claims `claimsAt` at its challenges. -/
theorem reduceWith_eq {m : Type → Type} [Monad m] [LawfulMonad m] (F : KeccakState → m KeccakState)
    {P : Params E} {B : P.Bounds} (W : Wire P B) (hW : W.limbs = Soundness.eLimbs) (ir : Digest)
    (stmt : PcsQuotient.Statement) (p : PcsQuotient.ReductionProof) (r₁ r₂ : Digest)
    (h₁ : digestOfScalars p.witnessRoot = some r₁) (h₂ : digestOfScalars p.quotientRoot = some r₂) :
    PcsQuotient.reduceWith F 22 ir stmt p =
      (fun ch : Compose.Chals E => (PcsQuotient.claimsAt 22 stmt ch.α ch.β ch.γ ch.t ch.ρ p.values
          p.next).map fun cl => (⟨r₁, r₂, cl⟩ : PcsQuotient.Reduced)) <$>
        Compose.chainWith W (fun l => Compose.toB <$> keccak256With F l)
          (rootProofIr ir stmt p r₁ r₂) := by
  have hS : PcsQuotient.Supported 22 := by decide
  have hchal : ∀ st : Digest, W.chal (Compose.toB st) = PcsQuotient.Transcript.challengeOf st := by
    intro st
    rw [challengeOf_eq, Wire.chal, hW]
  have hword : ∀ x : E, W.word x = PcsQuotient.Transcript.scalarBytes x := by
    intro x
    rw [Wire.word, hW, scalarBytes_eq]
  rcases p with ⟨⟨w0, w1⟩, ⟨q0, q1⟩, ⟨⟨vs⟩, hvs⟩, next⟩
  match vs, hvs with
  | [a0, a1, a2, a3], _ =>
  simp only [PcsQuotient.reduceWith, hS, not_true_eq_false, ↓reduceIte,
    PcsQuotient.Transcript.Chain.startWith, PcsQuotient.Transcript.Chain.squeezeWith,
    PcsQuotient.Transcript.Chain.absorb, Compose.chainWith, rootProofIr, h₁, h₂, map_bind,
    bind_assoc, pure_bind, bind_map_left, map_pure, label_eq]
  have h₁' : digestOfScalars (w0, w1) = some r₁ := h₁
  have h₂' : digestOfScalars (q0, q1) = some r₂ := h₂
  simp only [Wire.afterRoot, Wire.afterValues, Wire.valueWords, toB_toList, hchal, hword,
    rootScalars_eq _ _ h₁', rootScalars_eq _ _ h₂', List.flatMap_cons, List.flatMap_nil,
    List.nil_append, List.append_nil, List.cons_append, List.append_assoc]
  rfl

end Bridge

/-- info: 'Bridge.toB_toList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.toB_toList

/-- info: 'Bridge.label_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.label_eq

/-- info: 'Bridge.scalarBytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.scalarBytes_eq

/-- info: 'Bridge.rootScalars_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.rootScalars_eq

/-- info: 'Bridge.beWord_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.beWord_eq

/-- info: 'Bridge.challengeOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.challengeOf_eq

/-- info: 'Bridge.reduceWith_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.reduceWith_eq
