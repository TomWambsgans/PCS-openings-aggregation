-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCompose.Basic

/-!
# π1's contract IV has 32 bytes

`RecDeployment.pi1IvAt D roots` is `digestBytes` of a Keccak-256 output (`UniStatement.contractIvForWith`, either
branch), so it has 32 bytes at every deployment and every setup's roots (`pi1IvAt_length`). The statements' per-IV
premises (`Pi2Circuits.compile_ok`, `stream_eq`, `Pi2ViewChecked`, `RecDeployment.SetupFromCompiler`) are stated for
32-byte IVs only, and this lemma is how their consumers reach `pi1IvAt`. (At other lengths the checker rejects:
`graphOk` asks `r.iv.length == 32`, which is why the review's 49,152-byte IV fails, `STATEMENT_REVIEW.md` finding 1.)
-/

namespace RecStatement

open LeanVM.Protocol LeanVM.Protocol.KeccakHash

theorem length_digestBytes32 (d : Digest) : (digestBytes d).length = 32 := by
  obtain ⟨⟨l⟩, hl⟩ := d
  match l, hl with
  | [_, _, _, _], _ => rfl

/-- **π1's contract IV has 32 bytes**, at every deployment and every setup's roots. -/
theorem pi1Iv_length (s : UniStatement.Shape) (programIv : List UInt8) (roots : UniStatement.SetupRoots) :
    (pi1Iv s programIv roots).length = 32 := by
  simp only [pi1Iv, pi1IvWith, UniStatement.contractIvForWith, UniStatement.contractIvWith]
  split <;> exact length_digestBytes32 _

/-- **π1's contract IV at the setup's roots has 32 bytes.** -/
theorem RecDeployment.pi1IvAt_length (D : RecDeployment) (roots : UniStatement.SetupRoots) :
    (D.pi1IvAt roots).length = 32 :=
  pi1Iv_length _ _ _

end RecStatement

/-- info: 'RecStatement.RecDeployment.pi1IvAt_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.RecDeployment.pi1IvAt_length
