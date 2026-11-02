-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Compose.DecoderCost

/-!
# The decoder runs: a toy shape

`decodeColumns` is mumbai's `decodeStacks`, `decodeStacksAt` at the Johnson threshold, whose lane
decoder at our shapes is far too large to run (`DecoderCost.lean`). This file runs the same code,
`decodeStacksAt μ R A W` (CompPoly's Guruswami–Sudan on each of the `64` lanes, then the
pruning), at a toy shape: a stack of `2^8` words (lanes of `k = 4` coefficients), rate `1/2`
(`n = 8` columns), agreement `A = 6` (`(k − 1)·n = 24 < 36 = A²`), on the encoding of a stack
with two columns corrupted on every lane. It returns that stack, and nothing at `A = 7`.

Not part of the library build (about two and a half minutes in the interpreter, mostly the root
finding over `GF(2^64)`); run it with `lake env lean Test/DecoderToy.lean` from `formal/Compose`.
-/

open LeanVM.Parameters LeanVM.Extraction

/-- A toy stack of `2^8` words (`κ = 2`). -/
def toyStack : Vector K (2 ^ 8) := Vector.ofFn fun i ↦ K.ofBits (i.val * 7919 + 13)

/-- Its encoding at rate `1/2` (`8` columns, a leaf holding lane `u` at word `63 − u`), with every
lane of columns `1` and `5` replaced. -/
def toyWord : ℕ → List K := fun v ↦
  if v = 1 ∨ v = 5 then List.replicate 64 (K.ofBits 12345)
  else ((List.range 64).map fun u ↦ (novelFwd 2 1 (laneCoeffs toyStack u)).getD v 0).reverse

#guard decodeStacksAt 8 1 6 toyWord == [toyStack]
#guard decodeStacksAt 8 1 7 toyWord == []
