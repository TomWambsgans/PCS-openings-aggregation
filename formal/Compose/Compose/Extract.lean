-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Relates this repository's Merkle extraction (`Merkle.lean`) to leanerVM `mumbai`'s
-- (https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, MIT OR Apache-2.0:
-- `lean_vm/LeanVM/Protocol/Compile/Rom/Extract.lean`, `extract`, whose lemmas it uses).
import Compose.TwoOracle
import Compose.Merkle
import LeanVM.Protocol.Compile.Rom.Extract
import LeanVM.Protocol.Extraction.Merkle

/-!
# The Merkle extraction is mumbai's, without collisions

mumbai's `extract H r ht w` reads, at a position, the leaf of an opening that `openOne` accepts
against the root `r` through the partial hash `H` (the oracle's answers so far), and the zero row
where there is none. `merkleWord` (`Merkle.lean`) climbs down from the root through the history's
unique preimages instead. With the history's answers as mumbai's partial hash (`ansOf`):

* **`leafAt_of_climb`**: a climb from a leaf digest to a node through the answers is the descent
  from that node to the leaf, when the answers are injective on the history;
* **`merkleWord_of_openOne`**: so an accepted opening at a position is read by `merkleWord` there:
  the leaf's bytes (`kBytes`, eight per word);
* **`merkleWord_eq_extract`**: and the row is mumbai's `extract` there (`extract_eq_of_openOne`).

Injective answers is what neither failure event admits: mumbai's `Fail` (an answer colliding with
a digest the log refers to) and `ListChain.lean`'s `Coll` (an answer repeating an earlier one);
on a run without them the two extractions read the same rows.
-/

set_option linter.unusedSectionVars false

namespace Compose

open QuotientRpm
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Extraction LeanVM.Extraction.MerkleProofs

/-! ## The history's answers as mumbai's partial hash -/

/-- The answers of the history `H` under the table `T`, as digests. -/
def ansOf (H : Hist) (T : Table) : List UInt8 → Option Digest := fun x =>
  if x ∈ H then some (LeanVM.Digest.ofRpm (T x)) else none

theorem toList_toB (D : Digest) : (toB D).toList = digestBytes D :=
  LeanVM.Rpm.toList_digestToRpm D

theorem ansOf_eq_some {H : Hist} {T : Table} {x : List UInt8} {D : Digest} :
    ansOf H T x = some D ↔ x ∈ H ∧ T x = toB D := by
  unfold ansOf
  split
  · rename_i hx
    simp only [Option.some.injEq, hx, true_and]
    constructor
    · rintro rfl
      exact (LeanVM.Rpm.digestToRpm_ofRpm _).symm
    · intro h
      rw [h]
      exact LeanVM.Rpm.digestOfRpm_toRpm D
  · rename_i hx
    simp [hx]

/-- Injective answers on the history are mumbai's `AnswersInj`. -/
theorem answersInj_ansOf {H : Hist} {T : Table} (hinj : Set.InjOn T ↑H) :
    Rom.AnswersInj (ansOf H T) := by
  intro x y v hx hy
  obtain ⟨hxH, hxv⟩ := ansOf_eq_some.mp hx
  obtain ⟨hyH, hyv⟩ := ansOf_eq_some.mp hy
  exact hinj hxH hyH (hxv.trans hyv.symm)

theorem uniq_singleton {α : Type} (y : α) : uniq ({y} : Finset α) = some y := rfl

/-- With injective answers, an input of the history is the unique preimage of its answer. -/
theorem below_eq_some {H : Hist} {T : Table} (hinj : Set.InjOn T ↑H) {y : List UInt8}
    (hy : y ∈ H) {n : ℕ} (hn : y.length = n) : below H T (T y).toList n = some y := by
  unfold below
  have hf : (H.filter fun z => (T z).toList = (T y).toList ∧ z.length = n) = {y} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, hzy, -⟩
      exact hinj hz hy (Vector.toList_inj.mp hzy)
    · rintro rfl
      exact ⟨hy, rfl, hn⟩
  rw [hf, uniq_singleton]

/-! ## A climb is a descent -/

theorem posBits_succ (k q : ℕ) : posBits (k + 1) q = q.testBit k :: posBits k q := by
  simp [posBits, List.range_succ, List.reverse_append]

/-- A climb's last step. -/
theorem climb_snoc (H : List UInt8 → Option Digest) :
    ∀ (ss : List Digest) (s n : Digest) (q : ℕ),
      climbWithHash (m := Option) H n q (ss ++ [s]) =
        (climbWithHash (m := Option) H n q ss).bind fun m => H (nodeInput m s (q / 2 ^ ss.length))
  | [], s, n, q => by
    rw [List.nil_append, climb_cons]
    simp [climbWithHash]
  | a :: ss, s, n, q => by
    rw [List.cons_append, climb_cons, climb_cons, Option.bind_assoc]
    congr 1
    funext p
    rw [climb_snoc H ss s p (q / 2), List.length_cons, Nat.div_div_eq_div_mul, ← pow_succ']

/-- The child a position's bit picks out of a node's input is the climb's node. -/
theorem child_nodeInput (m s : Digest) (q k : ℕ) :
    (if q.testBit k then ((nodeInput m s (q / 2 ^ k)).drop 32).take 32
      else (nodeInput m s (q / 2 ^ k)).take 32) = digestBytes m := by
  have hb : q.testBit k = decide (q / 2 ^ k % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
  rcases Nat.mod_two_eq_zero_or_one (q / 2 ^ k) with h | h
  · have hf : q.testBit k = false := by rw [hb, h]; rfl
    rw [hf]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold nodeInput
    simp only [h, ↓reduceIte]
    exact List.take_left' (digestBytes_length m)
  · have ht : q.testBit k = true := by rw [hb, h]; rfl
    rw [ht]
    simp only [↓reduceIte]
    unfold nodeInput
    simp only [show ¬ q / 2 ^ k % 2 = 0 by omega, ↓reduceIte]
    rw [List.drop_left' (digestBytes_length s)]
    exact List.take_of_length_le (by rw [digestBytes_length])

/-- **A climb from a leaf digest to a node, through the history's answers, is the descent from
that node to the leaf digest's preimages**, when the answers are injective on the history. -/
theorem leafAt_of_climb {H : Hist} {T : Table} (hinj : Set.InjOn T ↑H) (leafLen : ℕ) :
    ∀ (k q : ℕ) (path : List Digest) (ld D : Digest), path.length = k →
      climbWithHash (m := Option) (ansOf H T) ld q path = some D →
      leafAt H T leafLen k (digestBytes D) (posBits k q) = below H T (digestBytes ld) leafLen
  | 0, q, path, ld, D, hl, hc => by
    rw [List.length_eq_zero_iff.mp hl] at hc
    simp only [climbWithHash, Option.pure_def, Option.some.injEq] at hc
    subst hc
    rfl
  | k + 1, q, path, ld, D, hl, hc => by
    obtain ⟨ss, s, rfl⟩ := List.eq_nil_or_concat path |>.resolve_left (by
      rintro rfl
      simp at hl)
    rw [List.concat_eq_append] at hl hc
    have hss : ss.length = k := by simpa using hl
    rw [climb_snoc, Option.bind_eq_some_iff] at hc
    obtain ⟨m, hm, hD⟩ := hc
    rw [hss] at hD
    obtain ⟨hyH, hyT⟩ := ansOf_eq_some.mp hD
    rw [posBits_succ]
    show (below H T (digestBytes D) 64).bind (fun y => leafAt H T leafLen k
      (if q.testBit k then (y.drop 32).take 32 else y.take 32) (posBits k q)) = _
    have hb := below_eq_some hinj hyH (n := 64) (by
      unfold nodeInput
      split <;> simp [digestBytes_length])
    rw [hyT, toList_toB] at hb
    rw [hb, Option.bind_some, child_nodeInput]
    exact leafAt_of_climb hinj leafLen k q ss ld m hss hm

/-! ## The two extractions read the same rows -/

theorem length_flatMap_kBytes (ws : List K) : (ws.flatMap kBytes).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    rw [List.flatMap_cons, List.length_append, kBytes_length, ih, List.length_cons]
    ring

/-- **An accepted opening is read by `merkleWord`**: at its position, the leaf's bytes. -/
theorem merkleWord_of_openOne {H : Hist} {T : Table} (hinj : Set.InjOn T ↑H) {R : Digest}
    {ht w q : ℕ} (hq : q < 2 ^ ht) {o : Opening}
    (h : openOneWithHash (m := Option) (ansOf H T) R ht w q o = some true) :
    merkleWord H T ht (8 * w) (toB R) ⟨q, hq⟩ = some (o.leaf.flatMap kBytes) := by
  obtain ⟨hw, hl, ld, hld, hc⟩ := (openOne_eq_some_true_iff _ _ _ _ _ _).mp h
  obtain ⟨hlH, hlT⟩ := ansOf_eq_some.mp hld
  show leafAt H T (8 * w) ht (toB R).toList (posBits ht q) = _
  rw [toList_toB, leafAt_of_climb hinj (8 * w) ht q o.path ld R hl hc, ← toList_toB, ← hlT]
  exact below_eq_some hinj hlH (by rw [length_flatMap_kBytes, hw])

/-- **`merkleWord` is mumbai's `extract`** where an opening is accepted: without collisions, the
row `merkleWord` reads at the position is the bytes of the row mumbai's `extract` reads there. -/
theorem merkleWord_eq_extract {H : Hist} {T : Table} (hinj : Set.InjOn T ↑H) {R : Digest}
    {ht w q : ℕ} (hq : q < 2 ^ ht) {o : Opening}
    (h : openOneWithHash (m := Option) (ansOf H T) R ht w q o = some true) :
    merkleWord H T ht (8 * w) (toB R) ⟨q, hq⟩ =
      some ((Rom.extract (ansOf H T) R ht w q).flatMap kBytes) := by
  rw [merkleWord_of_openOne hinj hq h]
  have he := extract_eq_of_openOne (answersInj_ansOf hinj) h
  rw [Nat.mod_eq_of_lt hq] at he
  rw [he]

/-- **A descent is a climb**: a leaf `merkleWord`'s descent reaches is the end of a climb through
the history's answers to the node it started from. -/
theorem leafAt_some {H : Hist} {T : Table} (leafLen : ℕ) :
    ∀ (k q : ℕ) (D : Digest) (bs : List UInt8),
      leafAt H T leafLen k (digestBytes D) (posBits k q) = some bs →
      ∃ (path : List Digest) (ld : Digest), path.length = k ∧
        climbWithHash (m := Option) (ansOf H T) ld q path = some D ∧
        below H T (digestBytes ld) leafLen = some bs
  | 0, _, D, _, h => ⟨[], D, rfl, rfl, h⟩
  | k + 1, q, D, bs, h => by
    rw [posBits_succ] at h
    change (below H T (digestBytes D) 64).bind (fun y => leafAt H T leafLen k
      (if q.testBit k then (y.drop 32).take 32 else y.take 32) (posBits k q)) = some bs at h
    obtain ⟨y, hy, hrest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hyH, hyD, hylen⟩ := Finset.mem_filter.mp (mem_of_uniq hy)
    have ha : digestBytes (bytesDigest y) = y.take 32 := digestBytes_bytesDigest y (by omega)
    have hb : digestBytes (bytesDigest (y.drop 32)) = (y.drop 32).take 32 :=
      digestBytes_bytesDigest (y.drop 32) (by simp [hylen])
    have hsplit : y.take 32 ++ (y.drop 32).take 32 = y := by
      rw [List.take_of_length_le (l := y.drop 32) (by simp [hylen]), List.take_append_drop]
    have hans : ansOf H T y = some D :=
      ansOf_eq_some.mpr ⟨hyH, Vector.toList_inj.mp (hyD.trans (toList_toB D).symm)⟩
    have hbit : q.testBit k = decide (q / 2 ^ k % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
    rcases Nat.mod_two_eq_zero_or_one (q / 2 ^ k) with h0 | h1
    · have hf : q.testBit k = false := by rw [hbit, h0]; rfl
      rw [hf] at hrest
      simp only [Bool.false_eq_true, ↓reduceIte] at hrest
      rw [← ha] at hrest
      obtain ⟨path, ld, hl, hc, hbl⟩ := leafAt_some leafLen k q _ bs hrest
      refine ⟨path ++ [bytesDigest (y.drop 32)], ld, by simp [hl], ?_, hbl⟩
      rw [climb_snoc, hc, Option.bind_some, hl]
      have hnode : nodeInput (bytesDigest y) (bytesDigest (y.drop 32)) (q / 2 ^ k) = y := by
        unfold nodeInput
        simp only [h0, ↓reduceIte]
        rw [ha, hb, hsplit]
      rw [hnode]
      exact hans
    · have ht : q.testBit k = true := by rw [hbit, h1]; rfl
      rw [ht] at hrest
      simp only [↓reduceIte] at hrest
      rw [← hb] at hrest
      obtain ⟨path, ld, hl, hc, hbl⟩ := leafAt_some leafLen k q _ bs hrest
      refine ⟨path ++ [bytesDigest y], ld, by simp [hl], ?_, hbl⟩
      rw [climb_snoc, hc, Option.bind_some, hl]
      have hnode : nodeInput (bytesDigest (y.drop 32)) (bytesDigest y) (q / 2 ^ k) = y := by
        unfold nodeInput
        simp only [show ¬ q / 2 ^ k % 2 = 0 by omega, ↓reduceIte]
        rw [ha, hb, hsplit]
      rw [hnode]
      exact hans

/-- `merkleWord`'s word as mumbai's: at a position, the words of the leaf's input the descent
reaches, and the zero row where it reaches none (or beyond the tree). -/
def wordOfMerkle (ht w : ℕ) (W : Fin (2 ^ ht) → Option (List UInt8)) (p : ℕ) : List K :=
  if h : p < 2 ^ ht then ((W ⟨p, h⟩).map (bytesWords w)).getD (List.replicate w 0)
  else List.replicate w 0

/-- **The Merkle extraction is mumbai's `extract`, without collisions**: at every position of the
tree, `merkleWord`'s row, read as words, is the row mumbai's `extract` reads through the
history's answers, when those are injective on the history. -/
theorem wordOfMerkle_eq_extract {H : Hist} {T : Table} (hinj : Set.InjOn T ↑H) (R : Digest)
    (ht w : ℕ) {p : ℕ} (hp : p < 2 ^ ht) :
    wordOfMerkle ht w (merkleWord H T ht (8 * w) (toB R)) p = Rom.extract (ansOf H T) R ht w p := by
  unfold wordOfMerkle
  simp only [hp, ↓reduceDIte]
  by_cases hex : ∃ o, openOneWithHash (m := Option) (ansOf H T) R ht w p o = some true
  · obtain ⟨o, ho⟩ := hex
    rw [merkleWord_of_openOne hinj hp ho, Option.map_some, Option.getD_some]
    have he := extract_eq_of_openOne (answersInj_ansOf hinj) ho
    rw [Nat.mod_eq_of_lt hp] at he
    rw [he]
    have hw := ((openOne_eq_some_true_iff _ _ _ _ _ _).mp ho).1
    rw [← hw]
    exact bytesWords_flatMap_kBytes o.leaf
  · have hz : Rom.extract (ansOf H T) R ht w p = List.replicate w 0 := by
      unfold Rom.extract Rom.pickLeaf
      simp only [hex, ↓reduceDIte]
    rw [hz]
    cases hm : merkleWord H T ht (8 * w) (toB R) ⟨p, hp⟩ with
    | none => rfl
    | some bs =>
      exfalso
      apply hex
      have h' : leafAt H T (8 * w) ht (digestBytes R) (posBits ht p) = some bs := by
        rw [← toList_toB]
        exact hm
      obtain ⟨path, ld, hl, hc, hbl⟩ := leafAt_some (8 * w) ht p R bs h'
      obtain ⟨hbH, hbT, hblen⟩ := Finset.mem_filter.mp (mem_of_uniq hbl)
      refine ⟨⟨bytesWords w bs, path⟩, (openOne_eq_some_true_iff _ _ _ _ _ _).mpr
        ⟨length_bytesWords w bs, hl, ld, ?_, hc⟩⟩
      rw [flatMap_kBytes_bytesWords w bs hblen]
      exact ansOf_eq_some.mpr ⟨hbH, Vector.toList_inj.mp (hbT.trans (toList_toB ld).symm)⟩

end Compose
