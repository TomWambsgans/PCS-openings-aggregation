/-
  Lv42.Parameters.Flock

  Adapted from leanerVM (https://github.com/Verified-zkEVM/leanerVM), branch mumbai, commit
  f0393df4, file lean_vm/LeanVM/Spec/Verifier.lean (its section "The Flock constants", lines
  225-307). MIT OR Apache-2.0; see NOTICE.md.

  The constants of leanVM's Flock argument for BLAKE2s: the block sizes, the constant wire, the
  map `φ_8`, the fixed coordinates of the zerocheck point and the ring-switching shifts.
  `Spec/Verifier.lean`, the transcription of leanVM's BLAKE2s-era verifier, is not ported; the
  arithmetization reads only these constants of it (`FlockRegion`, `FlockSpec`, the BLAKE2s
  circuit), so they are its own module here, unchanged.
-/

module

public import LeanVM.Parameters.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Lv42.Parameters
open LeanVM.Parameters

@[expose] public section

/-!
## The Flock constants

Transcribed from leanVM at pin `3f7dc2196e43ca60034c5803eb307c050b4f91d9`. The
specification fixes the sizes and the shape of the fixed coordinates (Annex C, §C.1 to §C.2) but
not their values; the values below are the Rust's, cross-checked against the Python verifier.

* `kBlock`, `kSkip`, `kIn` = `14`, `6`, `8`: `python-verifier/verifier.py:650-655`;
  `crates/flock/src/zerocheck.rs:45`.
* `constPos` = `512`: `crates/flock/src/hash.rs:144`; `verifier.py:657`.
* `phi8Basis`, the images of `1, t, …, t^7` under `φ_8 : GF(2^8) → K`:
  `crates/primitives/src/field/phi8_tower.rs:15-24`; `verifier.py:1111`.
* `fixedBytes` = `0xF7, 0x53, 0xB5`: `crates/flock/src/zerocheck/univariate_skip_optimized.rs:68`;
  `verifier.py:1116-1119`.
* `g0`, the limbs `0x243F…08D3, 0x1319…7344, 0xA409…31D0` (π in hexadecimal):
  `univariate_skip_optimized.rs:104-106`; `verifier.py:1114`.
* `ringShifts` = `32, 16, 8, 4, 2, 1`: `crates/pcs/src/ring_switch.rs:80`; `verifier.py:1327`.

`φ_8` is `F_2`-linear in its byte, the sum of the basis images of the byte's set bits
(`phi8_tower.rs:27-42`, `verifier.py:1112`); its image lies in `K`, the `y^0` limb of `E`. The
skip domain is `φ_8(0), …, φ_8(63)` and its coset `φ_8(64), …, φ_8(127)` (Annex C,
§C.2). The fixed coordinates of the zerocheck point are `φ_8` of the three bytes, then
`g0^(2^j) / (1 + g0^(2^j))` for `j < 4` (`univariate_skip_optimized.rs:90-101`,
`verifier.py:1116-1119`). The modulus of `GF(2^8)` is not needed: only the images are used.
-/

namespace Flock

/-- Log-size of a witness block: `2 ^ 14` positions per BLAKE2s compression. -/
abbrev kBlock : ℕ := 14

/-- The univariate skip replaces the low `6` coordinates; `2 ^ 6 = 64` bits pack into one `K`
element. -/
abbrev kSkip : ℕ := 6

/-- The within-block coordinates that remain after the skip, bound by the lincheck. -/
abbrev kIn : ℕ := 8

/-- The position of the constant wire in every block. -/
def constPos : Fin (2 ^ (kSkip + kIn)) := ⟨512, by decide⟩

/-- The images of the polynomial basis `1, t, …, t^7` of `GF(2^8)` under `φ_8`, in `K`
(`phi8_tower.rs:15-24`). -/
def phi8Basis : Vector K 8 :=
  #v[K.ofBits 0x0000000000000001, K.ofBits 0x033CE8BEDDC8A656, K.ofBits 0x512620375ED2A108,
    K.ofBits 0x0C9E636090AAFC01, K.ofBits 0xBA4F3CD82801769C, K.ofBits 0xBA26E7904ADB4A47,
    K.ofBits 0x467698598926DC01, K.ofBits 0x4418AE808B28BDD0]

/-- `φ_8` of a byte: the sum of the basis images of its set bits. -/
def phi8 (b : ℕ) : K := ∑ i : Fin 8, if b.testBit i then phi8Basis[i] else 0

/-- The `i`-th node of the skip domain and its coset, `φ_8(i)` in `E`: nodes `0` to `63` are the
skip domain, `64` to `127` its coset. -/
def skipNode (i : Fin 128) : E := ofK (phi8 i)

/-- The three bytes whose images are the first three fixed coordinates. -/
def fixedBytes : Vector ℕ 3 := #v[0xF7, 0x53, 0xB5]

/-- The public element `g_0` whose powers give the last four fixed coordinates. -/
def g0 : E :=
  E.ofLimbs (K.ofBits 0x243F6A8885A308D3) (K.ofBits 0x13198A2E03707344)
    (K.ofBits 0xA4093822299F31D0)

/-- The coordinate `g_0^(2^j) / (1 + g_0^(2^j))`. -/
def mediumCoord (j : ℕ) : E := g0 ^ 2 ^ j / (1 + g0 ^ 2 ^ j)

/-- The seven fixed coordinates of the zerocheck point, coordinates `0` to `6`. -/
def fixedPoint : Vector E 7 :=
  #v[ofK (phi8 fixedBytes[0]), ofK (phi8 fixedBytes[1]), ofK (phi8 fixedBytes[2]),
    mediumCoord 0, mediumCoord 1, mediumCoord 2, mediumCoord 3]

/-- The Frobenius shifts of the six stages of the ring-switching map: stage `p` adds
`f_p · a^(2^(2^(5 − p)))`. -/
def ringShifts : Vector ℕ 6 := #v[32, 16, 8, 4, 2, 1]

end Flock

end
end Lv42.Parameters
