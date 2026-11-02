-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the little-endian bytes of a 64-bit word (`wordBytes`, `Statement/Keccak.lean`)
-- and the word of eight little-endian bytes (`bytesLane`, `common/Common/Lanes.lean`).
import Common.Lanes
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# The bytes the chain hashes

`crates/quotient/src/transcript.rs`, byte for byte. The chain's state is a Keccak-256 digest, 32
bytes (`Bytes32`). An `F192` scalar is three 64-bit limbs `(c0, c1, c2)`, `c0` the lowest
(`Limbs`); the chain hashes it as a 256-bit big-endian word: eight zero bytes, then `c2`, `c1`,
`c0`, each big-endian (`scalarWord`, `Chain::sample`). A challenge is the low 192 bits of the new
state, limb `i` the big-endian word of bytes `24 - 8i` to `32 - 8i` (`stateLimbs`). A root is two
scalars, its 128-bit halves, each read as two little-endian words (`rootScalars`,
`fiat_shamir::merkle::hash_to_scalars`), hashed as their two words (`rootWords`), which are the
root's two halves reversed after sixteen zero bytes each (`rootWords_eq`).

* `scalarWord_injective`, `rootWords_injective`: a word determines its scalar, and the words a root.
* `stateLimbs_fiber`: every limb triple is the low 192 bits of exactly `2^64` states (`256^8`), so
  the challenge of a uniform state is uniform (`prEvent_uniform_balanced`, in the chain's file).
-/

open LeanVM.Protocol.KeccakHash LeanVM.Rpm

namespace QuotientRpm

/-- A Keccak-256 digest, 32 bytes: the chain's state, a root (`Common.DigestBytes`). -/
abbrev Bytes32 := Common.DigestBytes

/-- An `F192` scalar as its three 64-bit limbs `(c0, c1, c2)`, `c0` the lowest
(`primitives::field::F192::new`). -/
abbrev Limbs := UInt64 × UInt64 × UInt64

/-! ## Big-endian words -/

/-- The eight big-endian bytes of a 64-bit word (`u64::to_be_bytes`). -/
def be64 (w : UInt64) : List UInt8 := (wordBytes w).reverse

/-- The 64-bit word of the first eight bytes, big-endian (`u64::from_be_bytes`). -/
def ofBe64 (b : List UInt8) : UInt64 := bytesLane (b.take 8).reverse

@[simp] theorem length_be64 (w : UInt64) : (be64 w).length = 8 := by
  simp [be64, wordBytes_len]

theorem take_be64_append (w : UInt64) (rest : List UInt8) : (be64 w ++ rest).take 8 = be64 w := by
  simp

theorem ofBe64_be64_append (w : UInt64) (rest : List UInt8) : ofBe64 (be64 w ++ rest) = w := by
  rw [ofBe64, take_be64_append, be64, List.reverse_reverse]
  simpa using bytesLane_wordBytes_append w []

theorem ofBe64_be64 (w : UInt64) : ofBe64 (be64 w) = w := by
  simpa using ofBe64_be64_append w []

theorem be64_injective : Function.Injective be64 := fun a b h => by
  rw [← ofBe64_be64 a, h, ofBe64_be64]

/-- Reading the first `n` bytes with zeros past the end gives back a list of length `n`. -/
theorem range_map_getD (m : List UInt8) {n : ℕ} (h : m.length = n) :
    (List.range n).map (fun k => m.getD k 0) = m := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- The little-endian word of eight bytes, written back: the eight bytes. -/
theorem wordBytes_bytesLane_take (l : List UInt8) (h : 8 ≤ l.length) :
    wordBytes (bytesLane l) = l.take 8 := by
  rw [wordBytes_bytesLane]
  have h8 : (l.take 8).length = 8 := by simp [h]
  rw [← range_map_getD (l.take 8) h8]
  refine List.map_congr_left fun k hk => ?_
  have hk8 : k < 8 := List.mem_range.mp hk
  simp [List.getD_eq_getElem?_getD, hk8]

theorem be64_ofBe64 (l : List UInt8) (h : 8 ≤ l.length) : be64 (ofBe64 l) = l.take 8 := by
  have h8 : ((l.take 8).reverse).length = 8 := by simp [h]
  rw [be64, ofBe64, wordBytes_bytesLane_take _ (by omega), List.take_of_length_le (by omega),
    List.reverse_reverse]

theorem be64_bytesLane (l : List UInt8) (h : 8 ≤ l.length) : be64 (bytesLane l) = (l.take 8).reverse := by
  rw [be64, wordBytes_bytesLane_take l h]

/-! ## Scalars, states, roots -/

/-- **A scalar as the chain hashes it**: a 256-bit big-endian word, eight zero bytes then the
limbs `c2`, `c1`, `c0`, each big-endian (`Chain::sample`: `[0u8; 8]`, then
`limb.to_be_bytes()` for `limb` in `[x.c2, x.c1, x.c0]`). -/
def scalarWord (x : Limbs) : List UInt8 := List.replicate 8 0 ++ be64 x.2.2 ++ be64 x.2.1 ++ be64 x.1

/-- The limbs of the low 192 bits of a 256-bit big-endian word: limb `i` the big-endian word of
bytes `24 - 8i` to `32 - 8i`. -/
def wordLimbs (w : List UInt8) : Limbs := (ofBe64 (w.drop 24), ofBe64 (w.drop 16), ofBe64 (w.drop 8))

/-- **The challenge's limbs**: the low 192 bits of the state (`Chain::sample`: `limb(i)` is
`u64::from_be_bytes(state[24 - 8i .. 32 - 8i])`, and the challenge `F192::new(limb(0), limb(1),
limb(2))`). -/
def stateLimbs (st : Bytes32) : Limbs := wordLimbs st.toList

@[simp] theorem length_scalarWord (x : Limbs) : (scalarWord x).length = 32 := by
  simp [scalarWord]

/-- A word's low 192 bits are its scalar. -/
theorem wordLimbs_scalarWord (x : Limbs) : wordLimbs (scalarWord x) = x := by
  obtain ⟨c0, c1, c2⟩ := x
  have h24 : (scalarWord (c0, c1, c2)).drop 24 = be64 c0 := by
    simp [scalarWord, List.drop_append]
  have h16 : (scalarWord (c0, c1, c2)).drop 16 = be64 c1 ++ be64 c0 := by
    simp [scalarWord, List.drop_append]
  have h8 : (scalarWord (c0, c1, c2)).drop 8 = be64 c2 ++ be64 c1 ++ be64 c0 := by
    simp [scalarWord, List.drop_append]
  simp only [wordLimbs, h24, h16, h8, ofBe64_be64, List.append_assoc, ofBe64_be64_append]

theorem scalarWord_injective : Function.Injective scalarWord := fun a b h => by
  rw [← wordLimbs_scalarWord a, h, wordLimbs_scalarWord]

/-- **A root as two scalars**: its 128-bit halves, each the two little-endian words of its
bytes, the third limb zero (`fiat_shamir::merkle::hash_to_scalars`). -/
def rootScalars (r : Bytes32) : Limbs × Limbs :=
  ((bytesLane r.toList, bytesLane (r.toList.drop 8), 0),
    (bytesLane (r.toList.drop 16), bytesLane (r.toList.drop 24), 0))

/-- **A root as the chain hashes it**: the words of its two scalars (`ProverChain::send_root`). -/
def rootWords (r : Bytes32) : List UInt8 := scalarWord (rootScalars r).1 ++ scalarWord (rootScalars r).2

theorem be64_zero : be64 0 = List.replicate 8 0 := by decide

/-- The words of a root are its two halves, each reversed after sixteen zero bytes: a 128-bit
half read little-endian and written big-endian. -/
theorem rootWords_eq (r : Bytes32) :
    rootWords r = List.replicate 16 0 ++ (r.toList.take 16).reverse ++
      List.replicate 16 0 ++ (r.toList.drop 16).reverse := by
  have hl : r.toList.length = 32 := r.length_toList
  have e0 : be64 (bytesLane r.toList) = (r.toList.take 8).reverse := be64_bytesLane _ (by omega)
  have e1 : be64 (bytesLane (r.toList.drop 8)) = ((r.toList.drop 8).take 8).reverse :=
    be64_bytesLane _ (by simp)
  have e2 : be64 (bytesLane (r.toList.drop 16)) = ((r.toList.drop 16).take 8).reverse :=
    be64_bytesLane _ (by simp)
  have e3 : be64 (bytesLane (r.toList.drop 24)) = ((r.toList.drop 24).take 8).reverse :=
    be64_bytesLane _ (by simp)
  have t16 : (r.toList.take 16).reverse =
      ((r.toList.drop 8).take 8).reverse ++ (r.toList.take 8).reverse := by
    rw [show 16 = 8 + 8 from rfl, List.take_add, List.reverse_append]
  have d16 : (r.toList.drop 16).reverse =
      ((r.toList.drop 24).take 8).reverse ++ ((r.toList.drop 16).take 8).reverse := by
    have h24 : (r.toList.drop 24).take 8 = r.toList.drop 24 := List.take_of_length_le (by simp)
    rw [h24, ← List.reverse_append, show r.toList.drop 24 = (r.toList.drop 16).drop 8 by simp,
      List.take_append_drop]
  rw [t16, d16]
  simp only [rootWords, rootScalars, scalarWord, be64_zero, e0, e1, e2, e3, List.append_assoc,
    List.replicate_append_replicate, Nat.reduceAdd]

@[simp] theorem length_rootWords (r : Bytes32) : (rootWords r).length = 64 := by
  simp [rootWords]

theorem rootWords_injective : Function.Injective rootWords := fun a b h => by
  rw [rootWords_eq, rootWords_eq] at h
  have ha : a.toList.length = 32 := a.length_toList
  have hb : b.toList.length = 32 := b.length_toList
  simp only [List.append_assoc] at h
  obtain ⟨-, h⟩ := List.append_inj h rfl
  obtain ⟨h1, h⟩ := List.append_inj h (by simp [ha, hb])
  obtain ⟨-, h2⟩ := List.append_inj h rfl
  rw [List.reverse_inj] at h1 h2
  apply Vector.toList_inj.mp
  rw [← List.take_append_drop 16 a.toList, ← List.take_append_drop 16 b.toList, h1, h2]

/-! ## The low 192 bits of a uniform state -/

/-- The state's top eight bytes and its limbs determine it. -/
def splitState (st : Bytes32) : Vector UInt8 8 × Limbs :=
  (⟨(st.toList.take 8).toArray, by simp⟩, stateLimbs st)

/-- The state of given top bytes and limbs. -/
def joinState (p : Vector UInt8 8 × Limbs) : Bytes32 :=
  ⟨(p.1.toList ++ be64 p.2.2.2 ++ be64 p.2.2.1 ++ be64 p.2.1).toArray, by simp⟩

theorem joinState_splitState (st : Bytes32) : joinState (splitState st) = st := by
  have hl : st.toList.length = 32 := st.length_toList
  apply Vector.toList_inj.mp
  have a8 : be64 (ofBe64 (st.toList.drop 8)) = (st.toList.drop 8).take 8 := be64_ofBe64 _ (by simp)
  have a16 : be64 (ofBe64 (st.toList.drop 16)) = (st.toList.drop 16).take 8 :=
    be64_ofBe64 _ (by simp)
  have a24 : be64 (ofBe64 (st.toList.drop 24)) = st.toList.drop 24 := by
    rw [be64_ofBe64 _ (by simp)]
    exact List.take_of_length_le (by simp)
  have j16 : (st.toList.drop 16).take 8 ++ st.toList.drop 24 = st.toList.drop 16 := by
    rw [show st.toList.drop 24 = (st.toList.drop 16).drop 8 by simp, List.take_append_drop]
  have j8 : (st.toList.drop 8).take 8 ++ st.toList.drop 16 = st.toList.drop 8 := by
    rw [show st.toList.drop 16 = (st.toList.drop 8).drop 8 by simp, List.take_append_drop]
  simp only [joinState, splitState, stateLimbs, wordLimbs, Vector.toList_mk, a8, a16, a24,
    List.append_assoc, j16, j8, List.take_append_drop]

theorem splitState_joinState (p : Vector UInt8 8 × Limbs) : splitState (joinState p) = p := by
  obtain ⟨top, c0, c1, c2⟩ := p
  have ht : top.toList.length = 8 := top.length_toList
  have h24 : (top.toList ++ (be64 c2 ++ (be64 c1 ++ be64 c0))).drop 24 = be64 c0 := by
    simp [List.drop_append, ht, List.drop_of_length_le]
  have h16 : (top.toList ++ (be64 c2 ++ (be64 c1 ++ be64 c0))).drop 16 = be64 c1 ++ be64 c0 := by
    simp [List.drop_append, ht, List.drop_of_length_le]
  have h8 : (top.toList ++ (be64 c2 ++ (be64 c1 ++ be64 c0))).drop 8 =
      be64 c2 ++ (be64 c1 ++ be64 c0) := by
    simp [List.drop_append, ht]
  have ht8 : (top.toList ++ (be64 c2 ++ (be64 c1 ++ be64 c0))).take 8 = top.toList := by
    simp [List.take_append, ht]
  simp only [splitState, joinState, stateLimbs, wordLimbs, Vector.toList_mk, List.append_assoc,
    h24, h16, h8, ht8, ofBe64_be64, ofBe64_be64_append]
  rfl

/-- A state is its top eight bytes and its low 192 bits. -/
def stateEquiv : Bytes32 ≃ Vector UInt8 8 × Limbs where
  toFun := splitState
  invFun := joinState
  left_inv := joinState_splitState
  right_inv := splitState_joinState

theorem stateEquiv_snd (st : Bytes32) : (stateEquiv st).2 = stateLimbs st := rfl

-- The linter's traversal of this proof's terms runs out of recursion depth.
set_option linter.constructorNameAsVariable false in
/-- **Every limb triple is the low 192 bits of as many states as there are top bytes**
(`256^8`). -/
theorem stateLimbs_fiber (c : Limbs) :
    (Finset.univ.filter fun st : Bytes32 => stateLimbs st = c).card =
      (Finset.univ : Finset (Vector UInt8 8)).card := by
  refine Finset.card_bij (fun st _ => (stateEquiv st).1) ?_ ?_ ?_
  · intro a _
    simp
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    apply stateEquiv.injective
    refine Prod.ext hab ?_
    rw [stateEquiv_snd, stateEquiv_snd, ha, hb]
  · intro top _
    refine ⟨stateEquiv.symm (top, c), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h := congrArg Prod.snd (stateEquiv.apply_symm_apply (top, c))
      rwa [stateEquiv_snd] at h
    · rw [stateEquiv.apply_symm_apply]

end QuotientRpm
