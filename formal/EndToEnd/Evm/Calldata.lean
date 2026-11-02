-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The calldata's layout is `crates/evm/src/quotient.rs`'s `calldata`, which the tests' `parse`
-- (`crates/evm/src/lean.rs`) inverts.
import Evm.Contract

/-!
# Every calldata the contract can accept is a proof's

The contract reverts on calldata of another length or selector (F5's `WellFormed`:
`accepts_of_not_wellFormed`), and every well-formed calldata is the calldata of a statement and a
reduction proof whose roots' scalars name digests (`calldata_surjective`: the statement's 64 bytes,
each root's halves reversed back, each value's limbs read big-endian — the inverse of `quotient.rs`'s
`calldata`, the tests' `parse`). So over **all** calldata:

**`evm_accepts_iff_exists`**: with `PCS_OPEN` the opening check `pcsOpen` given the openings `w`, `f`,
`q` of the three tables, the contract accepts `cd` exactly when `cd` is the calldata of a statement
and a reduction proof that, with those openings, the statement's verifier accepts.
-/

set_option linter.unusedSectionVars false

namespace Evm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash QuotientRpm
open Implementation

/-- The contract reverts on calldata of another length or selector. -/
theorem accepts_of_not_wellFormed (attest : List UInt8 → Bool) (H : List UInt8 → Vector UInt8 32)
    (idx : Vector UInt8 32) {cd : List UInt8} (h : ¬ WellFormed cd) :
    accepts attest H idx cd = false := by
  unfold accepts Implementation.run
  rw [if_neg h]

/-- The value of 24 calldata bytes (the tests' `parse`, `crates/evm/src/lean.rs`): its limbs
`c2, c1, c0`, each big-endian. -/
def scalarOfBytes (X : List UInt8) : E :=
  limbsEquiv.symm (ofBe64 (X.drop 16), ofBe64 (X.drop 8), ofBe64 X)

theorem scalarBytes_scalarOfBytes {X : List UInt8} (h : X.length = 24) :
    scalarBytes (limbsEquiv (scalarOfBytes X)) = X := by
  rw [scalarOfBytes, Equiv.apply_symm_apply, scalarBytes]
  dsimp only
  rw [be64_ofBe64 _ (by omega), be64_ofBe64 _ (by simp; omega), be64_ofBe64 _ (by simp; omega),
    List.take_of_length_le (show (X.drop 16).length ≤ 8 by simp; omega)]
  have e1 : (X.drop 8).take 8 ++ X.drop 16 = X.drop 8 := by
    conv_rhs => rw [← List.take_append_drop 8 (X.drop 8)]
    simp only [List.drop_drop]
  rw [List.append_assoc, e1, List.take_append_drop]

/-- The root of 32 calldata bytes (the tests' `parse`): its two halves reversed back. -/
def rootOfBytes (B : List UInt8) (h : B.length = 32) : Digest :=
  Compose.ofB ⟨((B.take 16).reverse ++ (B.drop 16).reverse).toArray, by simp; omega⟩

theorem rootBytes_rootOfBytes {B : List UInt8} (h : B.length = 32) :
    rootBytes (Compose.toB (rootOfBytes B h)) = B := by
  rw [rootOfBytes, show Compose.toB (Compose.ofB _) = _ from LeanVM.Rpm.digestToRpm_ofRpm _,
    rootBytes]
  simp only [Vector.toList_mk]
  rw [List.take_left' (by simp; omega), List.drop_left' (by simp; omega), List.reverse_reverse,
    List.reverse_reverse, List.take_append_drop]

/-- **Every well-formed calldata is a proof's** (the tests' `parse` inverts `quotient.rs`'s
`calldata`). -/
theorem calldata_surjective {cd : List UInt8} (h : WellFormed cd) :
    ∃ stmt p, calldata stmt p = some cd := by
  obtain ⟨hlen, hsel⟩ := h
  have hlen' : cd.length = 252 := by rw [hlen]; rfl
  have split : ∀ k n m, k + n = m → (cd.drop k).take n ++ cd.drop m = cd.drop k := by
    intro k n m hm
    subst hm
    rw [← List.drop_drop]
    exact List.take_append_drop n (cd.drop k)
  have e : cd.take 4 ++ ((cd.drop 4).take 32 ++ ((cd.drop 36).take 32 ++ ((cd.drop 68).take 32 ++
      ((cd.drop 100).take 32 ++ ((cd.drop 132).take 24 ++ ((cd.drop 156).take 24 ++
      ((cd.drop 180).take 24 ++ ((cd.drop 204).take 24 ++ (cd.drop 228).take 24)))))))) = cd := by
    rw [List.take_of_length_le (show (cd.drop 228).length ≤ 24 by simp; omega),
      split 204 24 228 rfl, split 180 24 204 rfl, split 156 24 180 rfl, split 132 24 156 rfl,
      split 100 32 132 rfl, split 68 32 100 rfl, split 36 32 68 rfl, split 4 32 36 rfl,
      List.take_append_drop]
  have l32 : ∀ k, k + 32 ≤ 252 → ((cd.drop k).take 32).length = 32 := fun k hk => by
    simp; omega
  have l24 : ∀ k, k + 24 ≤ 252 → ((cd.drop k).take 24).length = 24 := fun k hk => by
    simp; omega
  let y : Vector UInt8 32 := ⟨((cd.drop 4).take 32).toArray, by simpa using l32 4 (by norm_num)⟩
  let rt : Vector UInt8 32 := ⟨((cd.drop 36).take 32).toArray, by simpa using l32 36 (by norm_num)⟩
  let r₁ := rootOfBytes ((cd.drop 68).take 32) (l32 68 (by norm_num))
  let r₂ := rootOfBytes ((cd.drop 100).take 32) (l32 100 (by norm_num))
  refine ⟨⟨y, rt⟩, ⟨digestScalars r₁, digestScalars r₂,
    #v[scalarOfBytes ((cd.drop 132).take 24), scalarOfBytes ((cd.drop 156).take 24),
      scalarOfBytes ((cd.drop 180).take 24), scalarOfBytes ((cd.drop 204).take 24)],
    scalarOfBytes ((cd.drop 228).take 24)⟩, ?_⟩
  simp only [calldata, digestOfScalars_digestScalars]
  refine congrArg some ?_
  rw [calldataOf_eq]
  show bytesOf Emitted.selector ++ ((y ++ rt).toList ++ (rootBytes (Compose.toB r₁) ++
    (rootBytes (Compose.toB r₂) ++ (scalarBytes (limbsEquiv (scalarOfBytes ((cd.drop 132).take 24))) ++
    (scalarBytes (limbsEquiv (scalarOfBytes ((cd.drop 156).take 24))) ++
    (scalarBytes (limbsEquiv (scalarOfBytes ((cd.drop 180).take 24))) ++
    (scalarBytes (limbsEquiv (scalarOfBytes ((cd.drop 204).take 24))) ++
    scalarBytes (limbsEquiv (scalarOfBytes ((cd.drop 228).take 24)))))))))) = cd
  rw [rootBytes_rootOfBytes, rootBytes_rootOfBytes,
    scalarBytes_scalarOfBytes (l24 132 (by norm_num)),
    scalarBytes_scalarOfBytes (l24 156 (by norm_num)),
    scalarBytes_scalarOfBytes (l24 180 (by norm_num)),
    scalarBytes_scalarOfBytes (l24 204 (by norm_num)),
    scalarBytes_scalarOfBytes (l24 228 (by norm_num)), Vector.toList_append, ← hsel]
  simp only [y, rt, Vector.toList_mk, List.append_assoc]
  exact e

/-- **On any calldata, the contract accepts exactly the proofs the statement's verifier accepts**:
with `PCS_OPEN`'s semantics `pcsOpen` given the openings `w`, `f`, `q` of the three tables, the
deployed contract (F5's graph, the deployed Keccak-256, the circuit's commitment `ir` in storage)
accepts the calldata `cd` exactly when `cd` is the calldata of a statement and a reduction proof that,
with those openings, `PcsQuotient.verify` (`verifyWith` at Keccak-f[1600]) accepts. -/
theorem evm_accepts_iff_exists (ir : Digest) (cd : List UInt8) (w f q : Compile.Proof) :
    accepts (pcsOpen (openingsOf w f q)) keccakBytes (Compose.toB ir) cd = true ↔
      ∃ stmt p, calldata stmt p = some cd ∧ PcsQuotient.verify 22 ir stmt ⟨p, w, f, q⟩ = true := by
  constructor
  · intro h
    by_cases hw : WellFormed cd
    · obtain ⟨stmt, p, hcd⟩ := calldata_surjective hw
      exact ⟨stmt, p, hcd, (evm_accepts_iff_verify ir stmt ⟨p, w, f, q⟩ hcd).mp h⟩
    · rw [accepts_of_not_wellFormed _ _ _ hw] at h
      cases h
  · rintro ⟨stmt, p, hcd, hv⟩
    exact (evm_accepts_iff_verify ir stmt ⟨p, w, f, q⟩ hcd).mpr hv

end Evm
