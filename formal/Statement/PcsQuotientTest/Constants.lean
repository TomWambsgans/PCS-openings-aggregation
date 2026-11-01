-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import PcsQuotient

/-!
# The constants' properties, checked

The constants of `PcsQuotient/Domain.lean` have the properties that make them the protocol's, at the sizes the
protocol uses: the Cantor basis (all `28` vectors), the coordinates of the public region (`11` basis vectors,
`Reduction.lean`'s `region`), and the rows' polynomial at every supported size (`m = logRows + 2`,
`19 ≤ m ≤ 24`).

They are checked by **compiled evaluation** (`native_decide`, which trusts the compiler: the axiom
`Lean.ofReduceBool`), not by the kernel: the kernel's evaluation of the computed constants, through `K`'s
products and inverses, did not finish in twenty minutes. The differential test checks the same constants
another way: the verifier's claims, which depend on all of them, are the Rust's.
-/

open PcsQuotient.Domain

theorem cantor_basis : IsCantorBasis := by native_decide

theorem coordinates_read : CoordinatesRead 11 := by native_decide

theorem row_vanishing : ∀ m : Fin 6, RowVanishingProperty (m.val + 19) := by native_decide
