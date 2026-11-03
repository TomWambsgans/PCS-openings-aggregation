-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The walk is `UniStatement.runWith`
-- (`formal/UniStatement/UniStatement/Run.lean`), the chain `Compose.ChainSpecU.chain`
-- (`formal/Compose/Compose/ListChainU.lean`); the byte facts follow `formal/EndToEnd/Bridge/Chain.lean`.
import UniSound.FsWalk
import Bridge.Chain

/-!
# The walk is the chain (`UniWalk`, `UniWalkReject`)
-/

set_option linter.unusedSectionVars false

namespace UniSound

open Compose QuotientRpm LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics UniStatement
open OracleSpec OracleComp

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack

/-! ## The stream's bytes -/

/-- The stream's `n` bytes from byte `s`. -/
def bytesAt (b : Array UInt8) (s n : ℕ) : List UInt8 := (b.toList.drop s).take n

theorem bytesAt_add (b : Array UInt8) (s n k : ℕ) :
    bytesAt b s (n + k) = bytesAt b s n ++ bytesAt b (s + n) k := by
  simp only [bytesAt, List.take_add, List.drop_drop]

theorem bytesAt_add_of (b : Array UInt8) {s n k t : ℕ} (h : s + n = t) :
    bytesAt b s (n + k) = bytesAt b s n ++ bytesAt b t k := by
  subst h
  exact bytesAt_add b s n k

theorem toList_extract_eq (b : Array UInt8) (a c : ℕ) :
    (b.extract a c).toList = bytesAt b a (c - a) := by
  simp only [Array.toList_extract, List.extract_eq_take_drop, bytesAt]

theorem getD_toList (b : Array UInt8) (i : ℕ) : b.toList.getD i 0 = b.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

theorem bytesAt_eq_map (b : Array UInt8) (s n : ℕ) (h : s + n ≤ b.size) :
    bytesAt b s n = (List.range n).map fun j => b.getD (s + j) 0 := by
  apply List.ext_getElem
  · simp only [bytesAt, List.length_take, List.length_drop, Array.length_toList, List.length_map,
      List.length_range]
    omega
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h2
    simp only [bytesAt, List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range,
      Array.getElem_toList, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega : s + i < b.size),
      Option.getD_some]

theorem beWordAt_eq_beWord (b : Array UInt8) (s : ℕ) :
    beWordAt b s = PcsQuotient.Transcript.beWord b.toList s := by
  simp only [beWordAt, PcsQuotient.Transcript.beWord, getD_toList]

theorem be64_beWordAt (b : Array UInt8) (s : ℕ) (h : s + 8 ≤ b.size) :
    QuotientRpm.be64 (beWordAt b s) = bytesAt b s 8 := by
  rw [beWordAt_eq_beWord, Bridge.beWord_eq _ _ (by simpa using h),
    be64_ofBe64 _ (by simp only [List.length_drop, Array.length_toList]; omega)]
  rfl

theorem foldl_congr_mem {α β : Type} {f g : β → α → β} :
    ∀ {l : List α} (init : β), (∀ x ∈ l, ∀ acc, f acc x = g acc x) → l.foldl f init = l.foldl g init
  | [], _, _ => rfl
  | x :: l, init, h => by
    simp only [List.foldl_cons]
    rw [h x List.mem_cons_self init]
    exact foldl_congr_mem _ fun y hy acc => h y (List.mem_cons_of_mem _ hy) acc

theorem getD_extract (b : Array UInt8) (o n i : ℕ) (h : o + n ≤ b.size) (hi : i < n) :
    (b.extract o (o + n)).getD i 0 = b.getD (o + i) 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  rw [ite_eq_left (by omega)]

theorem beWordAt_extract (b : Array UInt8) (o n k : ℕ) (h : o + n ≤ b.size) (hk : k + 8 ≤ n) :
    beWordAt (b.extract o (o + n)) k = beWordAt b (o + k) := by
  unfold beWordAt
  apply foldl_congr_mem
  intro j hj acc
  rw [getD_extract b o n (k + j) h (by simp only [List.mem_range] at hj; omega), Nat.add_assoc]

theorem uLimbs_eNew (a b c : UInt64) : uLimbs (eNew a b c) = (a, b, c) :=
  uLimbs.apply_symm_apply (a, b, c)

theorem bytesAt_24 (b : Array UInt8) (o : ℕ) :
    bytesAt b o 24 = bytesAt b o 8 ++ bytesAt b (o + 8) 8 ++ bytesAt b (o + 16) 8 := by
  rw [← bytesAt_add_of b (rfl : o + 8 = o + 8), ← bytesAt_add_of b (by omega : o + (8 + 8) = o + 16)]

theorem bytesAt_32 (b : Array UInt8) (o : ℕ) :
    bytesAt b o 32 =
      bytesAt b o 8 ++ bytesAt b (o + 8) 8 ++ (bytesAt b (o + 16) 8 ++ bytesAt b (o + 24) 8) := by
  rw [← bytesAt_add_of b (rfl : o + 8 = o + 8), ← bytesAt_add_of b (rfl : o + 16 + 8 = o + 16 + 8),
    ← bytesAt_add_of b (by omega : o + (8 + 8) = o + 16)]

/-- **A scalar as the stream carries it** is the stream's 24 bytes it is read from. -/
theorem scalar24_scalarAt (b : Array UInt8) (o : ℕ) (h : o + 24 ≤ b.size) :
    scalar24 (scalarAt b o) = bytesAt b o 24 := by
  rw [scalar24, scalarAt, uLimbs_eNew, be64_beWordAt b o (by omega),
    be64_beWordAt b (o + 8) (by omega), be64_beWordAt b (o + 16) (by omega), bytesAt_24]

theorem revRoot_vec (w0 w1 w2 w3 : UInt64) :
    revRoot (toB #v[w0, w1, w2, w3]) =
      QuotientRpm.be64 w1 ++ QuotientRpm.be64 w0 ++ (QuotientRpm.be64 w3 ++ QuotientRpm.be64 w2) := by
  have hl : (toB #v[w0, w1, w2, w3]).toList =
      (wordBytes w0 ++ wordBytes w1) ++ (wordBytes w2 ++ wordBytes w3) := by
    rw [Bridge.toB_toList]
    simp [digestBytes]
  have h16 : (wordBytes w0 ++ wordBytes w1).length = 16 := by
    simp [wordBytes_length]
  rw [revRoot, hl, List.take_left' h16, List.drop_left' h16, List.reverse_append,
    List.reverse_append]
  rfl

theorem rootOf_halvesAt (b : Array UInt8) (o : ℕ) :
    UniStatement.rootOf (halvesAt b o) =
      #v[beWordAt b (o + 8), beWordAt b o, beWordAt b (o + 24), beWordAt b (o + 16)] := by
  have e : ∀ x y : UInt64, IsCanonical128 (eNew x y 0) := fun _ _ => rfl
  unfold UniStatement.rootOf digestOfScalars halvesAt
  rw [ite_eq_left ⟨e _ _, e _ _⟩]
  rfl

/-- **A root as the stream carries it** is the stream's 32 bytes it is read from. -/
theorem revRoot_halvesAt (b : Array UInt8) (o : ℕ) (h : o + 32 ≤ b.size) :
    revRoot (toB (UniStatement.rootOf (halvesAt b o))) = bytesAt b o 32 := by
  rw [rootOf_halvesAt, revRoot_vec, be64_beWordAt b o (by omega), be64_beWordAt b (o + 8) (by omega),
    be64_beWordAt b (o + 16) (by omega), be64_beWordAt b (o + 24) (by omega), bytesAt_32]

/-- The stream's `n` scalars from byte `o`. -/
def scalarsAt (b : Array UInt8) (o n : ℕ) : List E := (List.range n).map fun k => scalarAt b (o + 24 * k)

theorem scalarsAt_zero (b : Array UInt8) (o : ℕ) : scalarsAt b o 0 = [] := rfl

theorem scalarsAt_succ (b : Array UInt8) (o n : ℕ) :
    scalarsAt b o (n + 1) = scalarAt b o :: scalarsAt b (o + 24) n := by
  simp only [scalarsAt, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.mul_zero,
    Nat.add_zero, List.cons.injEq, true_and]
  apply List.map_congr_left
  intro k _
  simp only [Function.comp_apply]
  congr 1
  omega

theorem scalars24_scalarsAt (b : Array UInt8) :
    ∀ (n o : ℕ), o + 24 * n ≤ b.size → scalars24 (scalarsAt b o n) = bytesAt b o (24 * n)
  | 0, o, _ => by simp [scalarsAt_zero, scalars24, bytesAt]
  | n + 1, o, h => by
    rw [scalarsAt_succ, show 24 * (n + 1) = 24 + 24 * n by ring, bytesAt_add]
    simp only [scalars24, List.flatMap_cons]
    rw [scalar24_scalarAt b o (by omega)]
    congr 1
    exact scalars24_scalarsAt b n (o + 24) (by omega)

/-- **A round's message as the channel reads it** from byte `o` (`msgsAt`'s head). -/
def msgOf (b : Array UInt8) (o : ℕ) (r : RoundSpec) : UMsg :=
  ((if r.root then some (halvesAt b o) else none),
    (List.range r.nv).map fun k => scalarAt b (o + (if r.root then 32 else 0) + 24 * k))

theorem msgsAt_cons (b : Array UInt8) (o : ℕ) (r : RoundSpec) (rs : List RoundSpec) :
    msgsAt b o (r :: rs) = msgOf b o r :: msgsAt b (o + roundBytes r) rs := rfl

/-- **A round's message as the chain hashes it** is the stream's bytes it is read from. -/
theorem uniEnc_msgOf (b : Array UInt8) (o : ℕ) (r : RoundSpec) (h : o + roundBytes r ≤ b.size) :
    uniEnc (toRMsg (msgOf b o r)) = bytesAt b o (roundBytes r) := by
  rcases r with ⟨root, nv, ns⟩
  cases root with
  | false =>
    simp only [roundBytes, Bool.false_eq_true, ite_false, Nat.zero_add] at h ⊢
    have := scalars24_scalarsAt b nv o h
    simp only [scalarsAt] at this
    simpa [msgOf, toRMsg, uniEnc] using this
  | true =>
    simp only [roundBytes, ite_true] at h ⊢
    rw [bytesAt_add, ← revRoot_halvesAt b o (by omega), ← scalars24_scalarsAt b nv (o + 32) (by omega)]
    rfl

/-! ## The bytes each sample absorbs -/

/-- **The bytes the samples absorb**, round by round from byte `o`: a round's first sample the bytes
not yet absorbed (`pre`, then the round's message), its other samples nothing. -/
def wAbs (b : Array UInt8) : ℕ → List UInt8 → List RoundSpec → List (List UInt8)
  | _, _, [] => []
  | o, pre, r :: rs =>
    (pre ++ bytesAt b o (roundBytes r)) :: (List.replicate r.ns [] ++ wAbs b (o + roundBytes r) [] rs)

/-- **The chain absorbs what the walk absorbs**: the encoding of the stream's messages at round
`i`, round `0`'s after the statement's bytes `pre`, are the stream's bytes. -/
theorem absorbsI_wAbs (b : Array UInt8) (pre : List UInt8) :
    ∀ (i o : ℕ) (rs : List RoundSpec), o + roundsBytes rs ≤ b.size →
      absorbsI (fun j m => if j = 0 then pre ++ uniEnc m else uniEnc m) i rs
          ((msgsAt b o rs).map toRMsg) =
        wAbs b o (if i = 0 then pre else []) rs
  | _, _, [], _ => rfl
  | i, o, r :: rs, h => by
    simp only [roundsBytes] at h
    rw [msgsAt_cons, List.map_cons, absorbsI, List.headD_cons, List.tail_cons, wAbs,
      absorbsI_wAbs b pre (i + 1) (o + roundBytes r) rs (by omega), uniEnc_msgOf b o r (by omega)]
    simp only [Nat.add_one_ne_zero, ite_false]
    split_ifs <;> simp

/-- The row counts' 24 bytes are the stream's first 24. -/
theorem rowBytes_toList (b : Array UInt8) (h : 24 ≤ b.size) : (rowBytes b).toList = bytesAt b 0 24 := by
  rw [bytesAt_eq_map b 0 24 (by omega)]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [rowBytes]

end UniSound
