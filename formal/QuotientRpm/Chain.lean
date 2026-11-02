-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientRpm.Bytes
import QuotientSecurity.RandomOracle

/-!
# The reduction with the deployed transcript

`crates/quotient/src/transcript.rs` and `quotient::protocol::reduce`, over a hash
`H : bytes → 32 bytes` in any monad (`Wire.verifyWith`). The chain's seed is `H` of the label
(the tag `pcs-quotient-kc1`, the circuit's commitment, the statement's 64 bytes `y ‖ root`); each
challenge is `H` of the state and the words of the scalars sent since the last challenge, its low
192 bits read as an element of `F192` (`Wire.chal`). The verifier reads the witness table's root
(two scalars), draws `α`, `β`, `γ`, reads the quotient table's root, draws `t`, reads five values
and draws `ρ`.

**The commitments are ideal**, as in `RandomOracle.lean`: a proof carries its two messages, the
polynomials themselves, and the verifier checks its claims on them (`Params.Accepts`). The root
the chain absorbs for a message is `H` of an injective encoding of it (`Wire.enc₁`, `Wire.enc₂`):
the commitment binds exactly as far as `H` has no collision, which the bounds count. (The
deployed root is a Merkle root of the message's Reed–Solomon encoding, over Keccak-256 too; that
step, with the openings, is not modelled.)

What the chain reads besides the proof is a `Wire`: the circuit's commitment, how the statement's
64 bytes are read as the statement `Params.Sat` speaks of (`decode`), how a field element is held
as limbs (`limbs`, `F192`'s `(c0, c1, c2)`), and the two encodings.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp

namespace QuotientRpm

open QuotientSecurity

/-- The transcript's tag, the label's first sixteen bytes: `b"pcs-quotient-kc1"` in ASCII
(`quotient::protocol::label`). -/
def tag : List UInt8 :=
  [0x70, 0x63, 0x73, 0x2d, 0x71, 0x75, 0x6f, 0x74, 0x69, 0x65, 0x6e, 0x74, 0x2d, 0x6b, 0x63, 0x31]

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]

/-- **What the chain reads besides the proof.** -/
structure Wire (P : Params F) (B : P.Bounds) where
  /-- The circuit's commitment (`index_root`), the label's second part. -/
  indexRoot : Bytes32
  /-- The statement that the 64 bytes `y ‖ root` stand for. -/
  decode : Vector UInt8 64 → (Fin P.words → F)
  /-- A field element as its three limbs `(c0, c1, c2)`, `c0` the lowest (`F192`). -/
  limbs : F ≃ Limbs
  /-- The bytes the first message's root hashes. -/
  enc₁ : B.Msg₁ → List UInt8
  enc₁_injective : Function.Injective enc₁
  /-- The bytes the second message's root hashes. -/
  enc₂ : B.Msg₂ → List UInt8
  enc₂_injective : Function.Injective enc₂

/-- **A statement and a proof**: the statement's 64 bytes, the two messages and the five values. -/
structure ChainProof (P : Params F) (B : P.Bounds) where
  stmt : Vector UInt8 64
  g : B.Msg₁
  R : B.Msg₂
  v : (Fin 4 → F) × F

variable {P : Params F} {B : P.Bounds} (W : Wire P B)

namespace Wire

/-- **The label**: the tag, the circuit's commitment, the statement (`quotient::protocol::label`,
112 bytes). -/
def label (sb : Vector UInt8 64) : List UInt8 := tag ++ W.indexRoot.toList ++ sb.toList

/-- A field element as the chain hashes it. -/
def word (x : F) : List UInt8 := scalarWord (W.limbs x)

/-- **A challenge**: the low 192 bits of the new state, as a field element. -/
def chal (st : Bytes32) : F := W.limbs.symm (stateLimbs st)

/-- The five values as the chain hashes them, in the order sent: the four cells, then the last. -/
def valueWords (v : (Fin 4 → F) × F) : List UInt8 :=
  W.word (v.1 0) ++ W.word (v.1 1) ++ W.word (v.1 2) ++ W.word (v.1 3) ++ W.word v.2

/-- The chain's input after a root: the state, then the root's two words. -/
def afterRoot (st r : Bytes32) : List UInt8 := st.toList ++ rootWords r

/-- The chain's input after the five values. -/
def afterValues (st : Bytes32) (v : (Fin 4 → F) × F) : List UInt8 := st.toList ++ W.valueWords v

open Classical in
/-- **The verifier with the deployed transcript**, over a hash `H` in any monad: the chain's
eight hashes (the seed, the two roots, the five challenges' states), then the claims on the
proof's polynomials at the chain's challenges. -/
noncomputable def verifyWith {m : Type → Type} [Monad m] (H : List UInt8 → m Bytes32)
    (π : ChainProof P B) : m Bool := do
  let st₀ ← H (W.label π.stmt)
  let r₁ ← H (W.enc₁ π.g)
  let st₁ ← H (afterRoot st₀ r₁)
  let st₂ ← H st₁.toList
  let st₃ ← H st₂.toList
  let r₂ ← H (W.enc₂ π.R)
  let st₄ ← H (afterRoot st₃ r₂)
  let st₅ ← H (W.afterValues st₄ π.v)
  pure (decide (P.Accepts (W.decode π.stmt) π.g.1 π.R.1 (W.chal st₁) (W.chal st₂) (W.chal st₃)
    (W.chal st₄) π.v.1 π.v.2 (W.chal st₅)))

end Wire

/-- The hash as a random oracle on byte strings. -/
abbrev HashSpec := (List UInt8 →ₒ Bytes32)

/-- A query of the hash. -/
def hashQuery (m : List UInt8) : OracleComp HashSpec Bytes32 := liftM (HashSpec.query m)

/-- **The experiment in the random-oracle model**: the adversary's statement and proof, then the
verifier on them, both asking the same random oracle. -/
noncomputable def chainExperiment (A : OracleComp HashSpec (ChainProof P B)) :
    OracleComp HashSpec (ChainProof P B × Bool) :=
  A >>= fun π => W.verifyWith hashQuery π >>= fun b => pure (π, b)

/-- What a proof wins: the verifier accepts, and the cells read off its first message do not
satisfy the relation for the statement its bytes stand for. -/
def Wins (r : ChainProof P B × Bool) : Prop :=
  r.2 = true ∧ ¬ P.Sat (W.decode r.1.stmt) (P.cells r.1.g.1)

/-! ## The chain's inputs determine what they absorb -/

namespace Wire

theorem label_injective : Function.Injective W.label := fun a b h => by
  simp only [Wire.label, List.append_assoc, List.append_cancel_left_eq] at h
  exact Vector.toList_inj.mp h

theorem word_injective : Function.Injective W.word := fun _ _ h =>
  W.limbs.injective (scalarWord_injective h)

@[simp] theorem length_word (x : F) : (W.word x).length = 32 := by simp [Wire.word]

theorem valueWords_injective : Function.Injective W.valueWords := by
  intro a b h
  simp only [Wire.valueWords] at h
  obtain ⟨h, h4⟩ := List.append_inj h (by simp)
  obtain ⟨h, h3⟩ := List.append_inj h (by simp)
  obtain ⟨h, h2⟩ := List.append_inj h (by simp)
  obtain ⟨h0, h1⟩ := List.append_inj h (by simp)
  have e0 := W.word_injective h0
  have e1 := W.word_injective h1
  have e2 := W.word_injective h2
  have e3 := W.word_injective h3
  have e4 := W.word_injective h4
  refine Prod.ext (funext fun i => ?_) e4
  fin_cases i
  · exact e0
  · exact e1
  · exact e2
  · exact e3

@[simp] theorem length_afterRoot (st r : Bytes32) : (Wire.afterRoot st r).length = 96 := by
  simp [Wire.afterRoot]

@[simp] theorem length_afterValues (st : Bytes32) (v : (Fin 4 → F) × F) :
    (W.afterValues st v).length = 192 := by
  simp [Wire.afterValues, Wire.valueWords]

theorem take_afterRoot (st r : Bytes32) : (Wire.afterRoot st r).take 32 = st.toList := by
  simp [Wire.afterRoot, List.take_append]

theorem rootPart_afterRoot (st r : Bytes32) :
    ((Wire.afterRoot st r).drop 32).take 64 = rootWords r := by
  simp [Wire.afterRoot, List.drop_append]

theorem take_afterValues (st : Bytes32) (v : (Fin 4 → F) × F) :
    (W.afterValues st v).take 32 = st.toList := by
  simp [Wire.afterValues, List.take_append]

theorem afterRoot_injective {st r st' r' : Bytes32}
    (h : Wire.afterRoot st r = Wire.afterRoot st' r') : st = st' ∧ r = r' := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  exact ⟨Vector.toList_inj.mp h1, rootWords_injective h2⟩

theorem afterValues_injective {st st' : Bytes32} {v v' : (Fin 4 → F) × F}
    (h : W.afterValues st v = W.afterValues st' v') : st = st' ∧ v = v' := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  exact ⟨Vector.toList_inj.mp h1, W.valueWords_injective h2⟩

end Wire

end QuotientRpm
