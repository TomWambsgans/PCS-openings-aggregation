-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Transcribed from `crates/evm/src/machine.rs` (`element_word`, `root_word`, `layout_id`, `layout`,
-- `pcs_open_input`, `PcsOpen::well_sized`, the input format of its module documentation).
import PcsQuotient.Verifier
import Implementation.Calldata
import Soundness.Defs

/-!
# `PCS_OPEN`: its input, and what it attests

The contract hands the precompile `PCS_OPEN` (`crates/evm/src/machine.rs`) one input per commitment:
`3 + k (v + 1)` words of 32 bytes, each big-endian — the root's word (`rootWordOf`,
`s₀ · 2^128 + s₁`, the root's two scalars as the transcript carries them), the layout's id
(`layoutId`, `256 · table + log_rows`), the number `k` of claims, then each claim's `v` coordinates
and its value, each element of `E` the word of its limbs (`elementWord`, `c0 + 2^64 c1 + 2^128 c2`,
its top 64 bits zero). `openInput` writes such an input (`pcs_open_input`); `parse` reads one as the
precompile reads it (`well_sized`: whole words, an id naming a layout it knows (`layoutOf`, `layout`),
`k ≥ 1`, exactly the length the layout's `v` and `k` fix, element words below `2^192`);
`parse_openInput` proves it reads back exactly what `openInput` wrote.

**`PCS_OPEN`'s semantics** (`pcsOpen`), the named model of the precompile: the input read by
`parse`, then the statement's opening check `PcsQuotient.opening` (WHIR over Keccak-f[1600],
`opening::verify`) for the layout its id names, at the root and claims read, with the opening proof
the block carries for the call (`proofFor id`); an input `parse` does not read attests nothing. The
mock attests an input when the block holds an opening of exactly those claims that
`opening::verify` accepted: that the mock and `opening::verify` are this (`PcsQuotient.opening`) is
tested, not proved (`crates/evm`'s tests, `formal/Statement`'s differential tests).
-/

set_option linter.unusedSectionVars false

namespace Evm

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash PcsQuotient
open Implementation (beNat beBytes limbsNat natLimbs)

/-! ## Words -/

/-- **`machine::element_word`**: an element of `E` as `PCS_OPEN` reads it, the number
`c0 + 2^64 c1 + 2^128 c2` of its limbs (`F192`'s `(c0, c1, c2)`), its top 64 bits zero. -/
def elementWord (x : E) : ℕ := limbsNat (Soundness.eLimbs x)

/-- The element of a word: its low 192 bits as limbs. -/
def elementOf (w : ℕ) : E := Soundness.eLimbs.symm (natLimbs w)

theorem elementOf_elementWord (x : E) : elementOf (elementWord x) = x := by
  simp [elementOf, elementWord, Implementation.natLimbs_limbsNat]

theorem elementWord_lt (x : E) : elementWord x < 2 ^ 192 := Implementation.limbsNat_lt _

/-- **`machine::root_word`**: a root as `PCS_OPEN` reads it, `s₀ · 2^128 + s₁`, `s_h` the
little-endian number of bytes `16 h .. 16 h + 16` of the root, i.e. of its words `d₀ + 2^64 d₁` and
`d₂ + 2^64 d₃` (`root_scalars`; the digest's words little-endian, `digestBytes`). -/
def rootWordOf (d : Digest) : ℕ :=
  (d[0].toNat + 2 ^ 64 * d[1].toNat) * 2 ^ 128 + (d[2].toNat + 2 ^ 64 * d[3].toNat)

/-- The root a word names (`rootWordOf`'s inverse). -/
def digestOfWord (w : ℕ) : Digest :=
  #v[UInt64.ofNat (w / 2 ^ 128 % 2 ^ 64), UInt64.ofNat (w / 2 ^ 192 % 2 ^ 64),
    UInt64.ofNat (w % 2 ^ 64), UInt64.ofNat (w / 2 ^ 64 % 2 ^ 64)]

theorem rootWordOf_lt (d : Digest) : rootWordOf d < 2 ^ 256 := by
  have h0 := d[0].toNat_lt
  have h1 := d[1].toNat_lt
  have h2 := d[2].toNat_lt
  have h3 := d[3].toNat_lt
  unfold rootWordOf
  norm_num at h0 h1 h2 h3 ⊢
  omega

theorem digestOfWord_rootWordOf (d : Digest) : digestOfWord (rootWordOf d) = d := by
  have h0 := d[0].toNat_lt
  have h1 := d[1].toNat_lt
  have h2 := d[2].toNat_lt
  have h3 := d[3].toNat_lt
  norm_num at h0 h1 h2 h3
  apply Vector.ext
  intro i hi
  simp only [digestOfWord, rootWordOf]
  interval_cases i <;>
    · apply UInt64.toNat_inj.mp
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, UInt64.toNat_ofNat']
      norm_num
      omega

/-- **`machine::layout_id`**: `256 · table + log_rows`, the witness table `1`, the wiring table `2`,
the quotient table `3`. -/
def layoutId (table logRows : ℕ) : ℕ := 256 * table + logRows

/-- **`machine::layout`**: the layout an id names, at the sizes the layouts take (`Supported`). -/
def layoutOf (id : ℕ) : Option Layout :=
  if Supported (id % 256) then
    if id / 256 = 1 then some (witnessLayout (id % 256))
    else if id / 256 = 2 then some (wiringLayout (id % 256))
    else if id / 256 = 3 then some (quotientLayout (id % 256))
    else none
  else none

theorem layoutOf_witness : layoutOf (layoutId 1 22) = some (witnessLayout 22) := by
  unfold layoutOf layoutId
  rw [if_pos (by decide), if_pos (by norm_num)]

theorem layoutOf_wiring : layoutOf (layoutId 2 22) = some (wiringLayout 22) := by
  unfold layoutOf layoutId
  rw [if_pos (by decide), if_neg (by norm_num), if_pos (by norm_num)]

theorem layoutOf_quotient : layoutOf (layoutId 3 22) = some (quotientLayout 22) := by
  unfold layoutOf layoutId
  rw [if_pos (by decide), if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num)]

/-- A claim's words: its point's coordinates, then its value. -/
def claimWords (claims : List Claim) : List ℕ :=
  claims.flatMap fun c => (c.point ++ [c.value]).map elementWord

/-- **`PCS_OPEN`'s input, as words** (`machine::pcs_open_input`): the root's word, the layout's id,
the number of claims, then the claims. -/
def openWords (root : Digest) (id : ℕ) (claims : List Claim) : List ℕ :=
  [rootWordOf root, id, claims.length] ++ claimWords claims

/-- **`PCS_OPEN`'s input**: its words, each 32 bytes big-endian (`MSTORE`). -/
def openInput (root : Digest) (id : ℕ) (claims : List Claim) : List UInt8 :=
  (openWords root id claims).flatMap (beBytes 32)

/-! ## Reading an input -/

/-- The first `n` 32-byte words of some bytes, each big-endian (`U256::from_be_slice`). -/
def wordsOf : ℕ → List UInt8 → List ℕ
  | 0, _ => []
  | n + 1, l => beNat (l.take 32) :: wordsOf n (l.drop 32)

/-- `k` claims of `v` variables from their words: each its `v` coordinates, then its value. -/
def claimsOfWords (v : ℕ) : ℕ → List ℕ → List Claim
  | 0, _ => []
  | k + 1, ws =>
    ⟨(ws.take v).map elementOf, elementOf (ws.getD v 0)⟩ :: claimsOfWords v k (ws.drop (v + 1))

/-- **How `PCS_OPEN` reads its input** (`machine::PcsOpen::well_sized` and the format of
`machine.rs`): whole words; a root word, an id naming a layout (`layoutOf`), `k ≥ 1`, then exactly
`k (v + 1)` words, `v` the layout's variables, each an element word (below `2^192`): the root, the id,
the layout and the claims. -/
def parse (input : List UInt8) : Option (Digest × ℕ × Layout × List Claim) :=
  if input.length % 32 = 0 then
    match wordsOf (input.length / 32) input with
    | r :: id :: k :: rest =>
      match layoutOf id with
      | some L =>
        if 1 ≤ k ∧ rest.length = k * (L.vars + 1) ∧ rest.all (· < 2 ^ 192) = true then
          some (digestOfWord r, id, L, claimsOfWords L.vars k rest)
        else none
      | none => none
    | _ => none
  else none

/-- **`PCS_OPEN`'s semantics**: the input as the precompile reads it (`parse`), checked by the
statement's opening check (`PcsQuotient.opening`, WHIR over Keccak-f[1600], `opening::verify`) of the
layout its id names, at the root and claims read, with the opening proof `proofFor id` the block
carries for the call; nothing else attests. -/
def pcsOpen (proofFor : ℕ → Compile.Proof) (input : List UInt8) : Bool :=
  match parse input with
  | some (root, id, L, claims) => opening L root claims (proofFor id)
  | none => false

/-! ## Reading back what was written -/

theorem length_beBytes (n w : ℕ) : (beBytes n w).length = n := by simp [beBytes]

theorem beBytes_succ (n w : ℕ) :
    beBytes (n + 1) w = ((w >>> (8 * n)) % 256).toUInt8 :: beBytes n w := by
  unfold beBytes
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply, Nat.succ_eq_add_one]
  rw [show n + 1 - 1 - (k + 1) = n - 1 - k by omega]

theorem beNat_beBytes : ∀ (n w : ℕ), beNat (beBytes n w) = w % 256 ^ n
  | 0, w => by simp [beBytes, beNat, Nat.mod_one]
  | n + 1, w => by
    rw [beBytes_succ, Implementation.beNat_cons, length_beBytes, beNat_beBytes n w]
    have h1 : (((w >>> (8 * n)) % 256).toUInt8).toNat = w / 256 ^ n % 256 := by
      rw [Nat.shiftRight_eq_div_pow, pow_mul]
      simp
    rw [h1, pow_succ, Nat.mod_mul]
    ring

theorem length_flatMap_beBytes (ws : List ℕ) : (ws.flatMap (beBytes 32)).length = 32 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [List.flatMap_cons, List.length_append, length_beBytes, ih, List.length_cons]
    ring

theorem wordsOf_flatMap : ∀ (ws : List ℕ), (∀ w ∈ ws, w < 256 ^ 32) →
    wordsOf ws.length (ws.flatMap (beBytes 32)) = ws
  | [], _ => rfl
  | w :: ws, h => by
    rw [List.length_cons, List.flatMap_cons, wordsOf, List.take_left' (length_beBytes 32 w),
      List.drop_left' (length_beBytes 32 w), beNat_beBytes,
      Nat.mod_eq_of_lt (h w (List.mem_cons_self ..)),
      wordsOf_flatMap ws (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem length_claimWords (v : ℕ) : ∀ (claims : List Claim), (∀ c ∈ claims, c.point.length = v) →
    (claimWords claims).length = claims.length * (v + 1)
  | [], _ => by simp [claimWords]
  | c :: cs, h => by
    have hc := h c (List.mem_cons_self ..)
    have ih := length_claimWords v cs (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [claimWords, List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons, List.length_nil] at ih ⊢
    rw [ih, hc]
    ring

theorem claimWords_lt (claims : List Claim) : ∀ w ∈ claimWords claims, w < 2 ^ 192 := by
  intro w hw
  simp only [claimWords, List.mem_flatMap, List.mem_map] at hw
  obtain ⟨_, _, x, _, rfl⟩ := hw
  exact elementWord_lt x

theorem claimsOfWords_claimWords (v : ℕ) : ∀ (claims : List Claim),
    (∀ c ∈ claims, c.point.length = v) → claimsOfWords v claims.length (claimWords claims) = claims
  | [], _ => rfl
  | ⟨p, x⟩ :: cs, h => by
    have hc : p.length = v := h ⟨p, x⟩ (List.mem_cons_self ..)
    have ih := claimsOfWords_claimWords v cs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hp : (p.map elementWord).length = v := by rw [List.length_map, hc]
    have e : claimWords (⟨p, x⟩ :: cs) = p.map elementWord ++ (elementWord x :: claimWords cs) := by
      simp [claimWords, List.append_assoc]
    have hg : (p.map elementWord ++ (elementWord x :: claimWords cs)).getD v 0 = elementWord x := by
      rw [List.getD_append_right _ _ _ _ (by rw [hp]), hp, Nat.sub_self, List.getD_cons_zero]
    have hd :
        (p.map elementWord ++ (elementWord x :: claimWords cs)).drop (v + 1) = claimWords cs := by
      rw [show p.map elementWord ++ (elementWord x :: claimWords cs) =
          (p.map elementWord ++ [elementWord x]) ++ claimWords cs by simp,
        List.drop_left' (by simp [hp])]
    rw [List.length_cons, claimsOfWords, e, List.take_left' hp, hg, hd, ih, List.map_map]
    simp [Function.comp_def, elementOf_elementWord]

/-- **`PCS_OPEN` reads back exactly what `openInput` writes**: the root, the id, the layout it names
and the claims, when there are claims, each of the layout's variables. -/
theorem parse_openInput {root : Digest} {id : ℕ} {L : Layout} {claims : List Claim}
    (hL : layoutOf id = some L) (hne : claims ≠ []) (hv : ∀ c ∈ claims, c.point.length = L.vars)
    (hid : id < 256 ^ 32) (hk : claims.length < 256 ^ 32) :
    parse (openInput root id claims) = some (root, id, L, claims) := by
  have hws : ∀ w ∈ openWords root id claims, w < 256 ^ 32 := by
    intro w hw
    simp only [openWords, List.cons_append, List.nil_append, List.mem_cons] at hw
    rcases hw with rfl | rfl | rfl | hw
    · have := rootWordOf_lt root
      norm_num at this ⊢
      omega
    · exact hid
    · exact hk
    · have := claimWords_lt claims w hw
      norm_num at this ⊢
      omega
  have hlen := length_flatMap_beBytes (openWords root id claims)
  have hk1 : 1 ≤ claims.length := by
    cases claims with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  have hall : (claimWords claims).all (· < 2 ^ 192) = true := by
    rw [List.all_eq_true]
    intro w hw
    exact decide_eq_true (claimWords_lt claims w hw)
  unfold parse openInput
  rw [hlen, if_pos (by omega), show 32 * (openWords root id claims).length / 32 =
    (openWords root id claims).length by omega, wordsOf_flatMap _ hws]
  simp only [openWords, List.cons_append, List.nil_append, hL]
  rw [if_pos ⟨hk1, length_claimWords L.vars claims hv, hall⟩, digestOfWord_rootWordOf,
    claimsOfWords_claimWords L.vars claims hv]

/-- **`PCS_OPEN` on an input `openInput` wrote** is the opening check of the layout its id names, at
that root and those claims, with the block's opening for it. -/
theorem pcsOpen_openInput (proofFor : ℕ → Compile.Proof) {root : Digest} {id : ℕ} {L : Layout}
    {claims : List Claim} (hL : layoutOf id = some L) (hne : claims ≠ [])
    (hv : ∀ c ∈ claims, c.point.length = L.vars) (hid : id < 256 ^ 32)
    (hk : claims.length < 256 ^ 32) :
    pcsOpen proofFor (openInput root id claims) = opening L root claims (proofFor id) := by
  rw [pcsOpen, parse_openInput hL hne hv hid hk]

end Evm
