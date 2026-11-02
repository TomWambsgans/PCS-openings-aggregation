-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): a digest's 32 bytes (`Digest.toRpm`, `common/Common/Lanes.lean`).
import Completeness.HiddenOpenings
import QuotientRpm.Chain

/-!
# The deployed transcript

`keccakTranscript H limbs indexRoot` is `crates/quotient/src/transcript.rs`'s chain over the hash
`H` (F4a's bytes, `QuotientRpm`, and Compose's `chainWith`): the seed `H(pcs-quotient-kc1 ‖
index_root ‖ y ‖ root)`, then `H` of the state and the witness root's two words for `α`, of the
state alone for `β` and `γ`, of the state and the quotient root's words for `t`, of the state and
the five values' words for `ρ`; a challenge the state's low 192 bits as `E` (`limbs`, `F192`'s
`(c0, c1, c2)`, a parameter as in F4a's `Wire`). The end theorems hold for every transcript, so
for this one (`completeness_keccak`); their probability statement (`completeness_end_bad_set`) is
over uniform challenges, which the chain's answers are in the random-oracle model as long as its
queries are fresh (F4a's `prEvent_chal`; the collision terms of an honest run, a few
`Q² / 2^256`, are not formalised here).
-/

set_option linter.unusedSectionVars false

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Semantics

namespace Completeness

open QuotientSecurity QuotientRpm

/-- **`transcript.rs`'s chain** over a hash `H`, the statement's 64 bytes after the tag and the
circuit's commitment. -/
noncomputable def keccakTranscript (H : Bytes → Digest) (limbs : E ≃ QuotientRpm.Limbs) (indexRoot : Digest) :
    Transcript :=
  let h : List UInt8 → QuotientRpm.Bytes32 := fun l => LeanVM.Rpm.Digest.toRpm (H l)
  let chal : QuotientRpm.Bytes32 → E := fun st => limbs.symm (stateLimbs st)
  let st₀ : Statement → QuotientRpm.Bytes32 := fun st =>
    h (tag ++ (LeanVM.Rpm.Digest.toRpm indexRoot).toList ++ List.ofFn st.y ++ List.ofFn st.root)
  let st₁ : Statement → Digest → QuotientRpm.Bytes32 := fun st r₁ =>
    h ((st₀ st).toList ++ rootWords (LeanVM.Rpm.Digest.toRpm r₁))
  let st₂ := fun st r₁ => h (st₁ st r₁).toList
  let st₃ := fun st r₁ => h (st₂ st r₁).toList
  let st₄ : Statement → Digest → Digest → QuotientRpm.Bytes32 := fun st r₁ r₂ =>
    h ((st₃ st r₁).toList ++ rootWords (LeanVM.Rpm.Digest.toRpm r₂))
  { abc := fun st r₁ => (chal (st₁ st r₁), chal (st₂ st r₁), chal (st₃ st r₁))
    t := fun st r₁ r₂ => chal (st₄ st r₁ r₂)
    ρ := fun st r₁ r₂ a s => chal (h ((st₄ st r₁ r₂).toList ++
      scalarWord (limbs (a 0)) ++ scalarWord (limbs (a 1)) ++ scalarWord (limbs (a 2)) ++
        scalarWord (limbs (a 3)) ++ scalarWord (limbs s))) }

/-- **End-to-end completeness on the deployed chain**: `completeness_end` with `transcript.rs`'s
chain over `H` itself, the circuit's commitment the setup's honest wiring root. -/
theorem completeness_keccak (I : Instance E) (BK : CantorBasis K (22 + 2))
    (hB : ∀ k, I.basis.β k = algebraMap K E (BK.β k)) (M : MembershipCircuit) {x Y : E}
    (hc : I.c = coordWeight x Y) (hw : I.wiring = wiringOf M.C) (limbs : E ≃ QuotientRpm.Limbs)
    (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ) (s : Secret)
    (m : Fin 4 → Fin 3 → K) (padW padQ : ℕ → ℕ → K) (π : DeployedProof)
    (hπ : honestProve I x Y BK M (keccakTranscript H limbs (wiringOpening.root H (wiringStack I BK)))
      witnessOpening.toSystem quotientOpening.toSystem H F fuel s m padW padQ = some π)
    (hab : ¬ Reduction.BadAB I
      (honestRun I BK M (keccakTranscript H limbs (wiringOpening.root H (wiringStack I BK)))
        witnessOpening.toSystem quotientOpening.toSystem H s m padW padQ).g
      (honestRun I BK M (keccakTranscript H limbs (wiringOpening.root H (wiringStack I BK)))
        witnessOpening.toSystem quotientOpening.toSystem H s m padW padQ).α
      (honestRun I BK M (keccakTranscript H limbs (wiringOpening.root H (wiringStack I BK)))
        witnessOpening.toSystem quotientOpening.toSystem H s m padW padQ).β)
    (ht : ¬ Reduction.Degenerate I
      (honestRun I BK M (keccakTranscript H limbs (wiringOpening.root H (wiringStack I BK)))
        witnessOpening.toSystem quotientOpening.toSystem H s m padW padQ).g
      (honestRun I BK M (keccakTranscript H limbs (wiringOpening.root H (wiringStack I BK)))
        witnessOpening.toSystem quotientOpening.toSystem H s m padW padQ).α
      (honestRun I BK M (keccakTranscript H limbs (wiringOpening.root H (wiringStack I BK)))
        witnessOpening.toSystem quotientOpening.toSystem H s m padW padQ).β
      (honestRun I BK M (keccakTranscript H limbs (wiringOpening.root H (wiringStack I BK)))
        witnessOpening.toSystem quotientOpening.toSystem H s m padW padQ).t) :
    deployedVerify I x Y (keccakTranscript H limbs (wiringOpening.root H (wiringStack I BK)))
      wiringOpening witnessOpening.toSystem quotientOpening.toSystem H F
      (wiringOpening.root H (wiringStack I BK)) s.statement π :=
  completeness_end I BK hB M hc hw _ H F fuel s m padW padQ π hπ hab ht

end Completeness
