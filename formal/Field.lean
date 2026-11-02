-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Field.F192
import Field.Test

/-- info: 'BF64.basePoly_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BF64.basePoly_irreducible

/-- info: 'BF64.ext3Poly_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BF64.ext3Poly_irreducible

/-- info: 'Primitives.F192.card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Primitives.F192.card

/-- info: 'Primitives.F192.ofLimbs_mul_ofLimbs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Primitives.F192.ofLimbs_mul_ofLimbs

/-- info: 'Primitives.F192.new_add_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Primitives.F192.new_add_new

/-- info: 'Primitives.F64.G_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Primitives.F64.G_pow

/-- info: 'Primitives.F64.sum_testBit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Primitives.F64.sum_testBit

/-- info: 'Primitives.F64.bits_eq_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Primitives.F64.bits_eq_false
