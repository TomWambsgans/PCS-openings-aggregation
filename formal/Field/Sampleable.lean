-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The samplers are leanerVM's `mumbai` (https://github.com/Verified-zkEVM/leanerVM, commit
-- 6175f1a07f0dc33bd3d640de0063d1006143ee91, `lean_vm/LeanVM/Protocol/Field.lean`: `finEquivK`,
-- `instSampleableTypeK`, `limbsEquiv`, `instSampleableTypeE`; MIT OR Apache-2.0), restated on
-- `Primitives.F64`, `Primitives.F192` (the same types) so that the main package need not import
-- mumbai's `lean_vm`.
import Field.F192
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Uniform sampling of `F64` and `F192`

`F64` as the `2^64` bit patterns of a uniform `Fin (2^64)`; `F192` as three independent uniform
limbs. Neither enumerates its field. As mumbai's, so that the two agree by unfolding.
-/

namespace Primitives

/-- `F64` as the `2^64` bit patterns, the `BitVec` view of `Fin (2^64)` (mumbai's `finEquivK`). -/
def finEquivF64 : Fin (2 ^ 64) ≃ F64 where
  toFun i := BF64.ofBitVec (BitVec.ofFin i)
  invFun x := x.toBitVec.toFin
  left_inv _ := rfl
  right_inv _ := rfl

/-- Uniform sampling of `F64`: a uniform `Fin (2^64)` read as a bit pattern. -/
instance instSampleableTypeF64 : SampleableType F64 :=
  haveI : NeZero (2 ^ 64) := ⟨by norm_num⟩
  SampleableType.ofEquiv finEquivF64

/-- `F192` as its three limbs (mumbai's `limbsEquiv`). -/
def limbsEquiv : Vector F64 3 ≃ F192 where
  toFun v := CompPoly.Extension.Ext.ofVector (P := BF64.ext3Params) v
  invFun x := CompPoly.Extension.Ext.coeffs (P := BF64.ext3Params) x
  left_inv _ := rfl
  right_inv _ := rfl

/-- Uniform sampling of `F192`: three independent uniform limbs. -/
instance instSampleableTypeF192 : SampleableType F192 := SampleableType.ofEquiv limbsEquiv

end Primitives
