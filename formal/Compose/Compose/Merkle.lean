-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The extraction (the word a Merkle root commits to, read off the hash's answers by climbing down
-- from the root through answered inputs) follows leanerVM `mumbai`'s `extract`
-- (https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, MIT OR Apache-2.0:
-- `lean_vm/LeanVM/Protocol/Compile/Rom/Extract.lean`), restated over the transcript's inputs.
import Compose.ListChain

/-!
# A Merkle tree's list commitment

The roots of the witness and quotient tables are Merkle roots over Keccak-256 (`hash_pair`: a
node is the hash of its children's 64 bytes, a leaf the hash of its row's bytes). Their
candidates are read off the inputs asked so far (`merkleCommit`):

* **the word** (`merkleWord`): at each position, climb down from the root: the input of the
  history whose answer is the current digest, of 64 bytes for a node and of the leaf length at
  the bottom, **if there is exactly one** (`uniq`), its first or second 32 bytes being the next
  digest as the position's bit says; the row is the leaf's input, or nothing;
* **the candidates**: any list decoder `dec` of the word, with lists of at most `L`.

It is a `ListCommit` (`merkleCommit`): it reads only the history's answers (`congr`), and it is
**stable** (`merkleWord_stable`): every input a climb passes through answers the root or a
digest an input of the climb refers to (`Refers`, its first or second chunk), so when those
are in `H`, the climb in `H' ⊇ H` is the climb in `H`. Everything here is computable: the
extractor `extractor (merkleCommit …)` reads the transcript, climbs, and decodes.
-/

set_option linter.unusedSectionVars false

namespace Compose

open QuotientRpm

/-! ## The unique element of a finite set -/

/-- The element of a one-element list. -/
def uniqList {α : Type} (l : List α) : Option α := if l.length = 1 then l.head? else none

theorem uniqList_perm {α : Type} {l l' : List α} (h : l.Perm l') : uniqList l = uniqList l' := by
  unfold uniqList
  rw [h.length_eq]
  split
  · rename_i h1
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp (h.length_eq ▸ h1)
    rw [List.perm_singleton.mp h.symm]
  · rfl

/-- **The element of a one-element set**, or nothing (computable). -/
def uniq {α : Type} (s : Finset α) : Option α :=
  Quot.liftOn s.val uniqList fun _ _ h => uniqList_perm h

theorem mem_of_uniq {α : Type} {s : Finset α} {y : α} (h : uniq s = some y) : y ∈ s := by
  obtain ⟨l, hl⟩ := Quot.exists_rep s.val
  have hu : uniq s = uniqList l := by
    show Quot.liftOn s.val uniqList _ = _
    rw [← hl]
  rw [hu] at h
  unfold uniqList at h
  split at h
  · rename_i h1
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp h1
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    show a ∈ s.val
    rw [← hl]
    exact Multiset.mem_coe.mpr List.mem_cons_self
  · exact absurd h (by simp)

/-! ## The word under a root -/

/-- The input of the history answering the bytes `d`, of length `n`, if exactly one. -/
def below (H : Hist) (T : Table) (d : List UInt8) (n : ℕ) : Option (List UInt8) :=
  uniq (H.filter fun z => (T z).toList = d ∧ z.length = n)

/-- The leaf's input at the position `bs` (the bits from the root down), `k` levels below the
digest bytes `d`. -/
def leafAt (H : Hist) (T : Table) (leafLen : ℕ) : ℕ → List UInt8 → List Bool → Option (List UInt8)
  | 0, d, _ => below H T d leafLen
  | _ + 1, _, [] => none
  | k + 1, d, b :: bs =>
      (below H T d 64).bind fun y => leafAt H T leafLen k (if b then (y.drop 32).take 32 else y.take 32) bs

/-- A position's bits, from the root down. -/
def posBits (height p : ℕ) : List Bool := (List.range height).reverse.map fun i => p.testBit i

/-- **The word a root commits to**: at each position, the leaf's input the climb reaches. -/
def merkleWord (H : Hist) (T : Table) (height leafLen : ℕ) (r : Bytes32) :
    Fin (2 ^ height) → Option (List UInt8) :=
  fun p => leafAt H T leafLen height r.toList (posBits height p)

/-! ## It reads the history only, and is stable -/

theorem below_congr {H : Hist} {T T' : Table} (h : ∀ d ∈ H, T d = T' d) (d : List UInt8) (n : ℕ) :
    below H T d n = below H T' d n := by
  unfold below
  congr 1
  exact Finset.filter_congr fun z hz => by rw [h z hz]

theorem leafAt_congr {H : Hist} {T T' : Table} (h : ∀ d ∈ H, T d = T' d) (leafLen : ℕ) :
    ∀ (k : ℕ) (d : List UInt8) (bs : List Bool),
      leafAt H T leafLen k d bs = leafAt H T' leafLen k d bs
  | 0, d, _ => below_congr h d leafLen
  | _ + 1, _, [] => rfl
  | k + 1, d, b :: bs => by
    simp only [leafAt, below_congr h d 64]
    congr 1
    funext y
    exact leafAt_congr h leafLen k _ bs

/-- The bytes a climb may stand at: the root's, or a chunk of an input of `H`. -/
def Covered (H : Hist) (r : Bytes32) (d : List UInt8) : Prop :=
  d = r.toList ∨ ∃ y ∈ H, d = y.take 32 ∨ d = (y.drop 32).take 32

section Stable

variable {H H' : Hist} {T : Table} {r : Bytes32}

theorem below_stable (hsub : H ⊆ H') (hroot : ∀ z ∈ H', T z = r → z ∈ H)
    (hdown : ∀ y ∈ H, ∀ z ∈ H', Refers y (T z) → z ∈ H) {d : List UInt8} (hd : Covered H r d)
    (n : ℕ) : below H' T d n = below H T d n := by
  unfold below
  congr 1
  ext z
  simp only [Finset.mem_filter]
  refine ⟨fun ⟨hz, hzd, hn⟩ => ⟨?_, hzd, hn⟩, fun ⟨hz, hzd, hn⟩ => ⟨hsub hz, hzd, hn⟩⟩
  rcases hd with rfl | ⟨y, hy, rfl | rfl⟩
  · exact hroot z hz (Vector.toList_inj.mp hzd)
  · exact hdown y hy z hz (Or.inl hzd)
  · exact hdown y hy z hz (Or.inr (Or.inl hzd))

theorem leafAt_stable (hsub : H ⊆ H') (hroot : ∀ z ∈ H', T z = r → z ∈ H)
    (hdown : ∀ y ∈ H, ∀ z ∈ H', Refers y (T z) → z ∈ H) (leafLen : ℕ) :
    ∀ (k : ℕ) (d : List UInt8) (bs : List Bool), Covered H r d →
      leafAt H' T leafLen k d bs = leafAt H T leafLen k d bs
  | 0, d, _, hd => below_stable hsub hroot hdown hd leafLen
  | _ + 1, _, [], _ => rfl
  | k + 1, d, b :: bs, hd => by
    simp only [leafAt, below_stable hsub hroot hdown hd 64]
    cases hb : below H T d 64 with
    | none => rfl
    | some y =>
      have hy : y ∈ H := (Finset.mem_filter.mp (mem_of_uniq hb)).1
      simp only [Option.bind_some]
      refine leafAt_stable hsub hroot hdown leafLen k _ bs ?_
      split
      · exact Or.inr ⟨y, hy, Or.inr rfl⟩
      · exact Or.inr ⟨y, hy, Or.inl rfl⟩

/-- **The word is stable**: once every input answering the root, or a digest an input of `H`
refers to, is in `H`, the word in `H' ⊇ H` is the word in `H`. -/
theorem merkleWord_stable (hsub : H ⊆ H') (hroot : ∀ z ∈ H', T z = r → z ∈ H)
    (hdown : ∀ y ∈ H, ∀ z ∈ H', Refers y (T z) → z ∈ H) (height leafLen : ℕ) :
    merkleWord H' T height leafLen r = merkleWord H T height leafLen r := by
  funext p
  exact leafAt_stable hsub hroot hdown leafLen height _ _ (Or.inl rfl)

end Stable

/-! ## The list commitment -/

/-- **A Merkle tree's list commitment**: the word under the root, read off the history, then any
list decoder `dec` of lists of at most `L` (for a WHIR root: the level-0 Johnson list of the
word's stacks, read back as tables). -/
def merkleCommit {M : Type} (height leafLen L : ℕ)
    (dec : (Fin (2 ^ height) → Option (List UInt8)) → List M) (hdec : ∀ w, (dec w).length ≤ L) :
    ListCommit M where
  bound := L
  cands H T r := dec (merkleWord H T height leafLen r)
  length_le _ _ _ := hdec _
  congr H T T' r h := by
    show dec _ = dec _
    congr 1
    funext p
    exact leafAt_congr h leafLen height _ _
  stable H H' T r hsub hroot hdown := by
    show dec _ = dec _
    rw [merkleWord_stable hsub hroot hdown height leafLen]

end Compose
