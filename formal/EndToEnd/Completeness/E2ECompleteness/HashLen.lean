-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import E2ECompleteness.Staging

/-!
# What the stages hash

Before `α` and between `γ` and `t` the honest run hashes Merkle leaves (a row of `64` words of `K`,
`512` bytes), Merkle nodes (two digests, `64` bytes) and the label (`112` bytes): never `32` or `96`
bytes, the lengths of the chain's challenge queries (`Good`). **`hashOK_stageAG`**,
**`hashOK_stageBG`**: the first and second stages are `HashOK Good` (`Chain.lean`), for any circuit
and cells, given a setup that is.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Prover (Tree)
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript

set_option autoImplicit false

namespace E2ECompleteness

theorem HashOK.mapM {P : Bytes → Prop} {α β : Type} (f : α → OracleComp KeccakCalls β)
    (hf : ∀ a, HashOK P (f a)) : ∀ l : List α, HashOK P (l.mapM f)
  | [] => HashOK.pure _ _
  | a :: l => by
    rw [List.mapM_cons]
    exact HashOK.bind (hf a) fun _ ↦ HashOK.bind (HashOK.mapM f hf l) fun _ ↦ HashOK.pure _ _

theorem HashOK.arrayMapM {P : Bytes → Prop} {α β : Type} (f : α → OracleComp KeccakCalls β)
    (hf : ∀ a, HashOK P (f a)) (xs : Array α) : HashOK P (xs.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  exact HashOK.map _ (HashOK.mapM f hf _)

theorem good_of_length {m : Bytes} (h : m.length = 512 ∨ m.length = 64 ∨ m.length = 112) :
    Good m := by
  refine ⟨?_, ?_⟩ <;> omega

theorem length_flatMap_kBytes (row : List K) : (row.flatMap kBytes).length = 8 * row.length := by
  induction row with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    simp only [kBytes, LeanVM.Rpm.wordBytes_len]
    ring

/-- A Merkle tree of rows of `64` words hashes `512`-byte leaves and `64`-byte nodes. -/
theorem hashOK_buildTree (height : ℕ) (word : LeanVM.Protocol.Compile.Word)
    (hw : ∀ p, (word p).length = 64) :
    HashOK Good (LeanVM.Prover.buildTreeWithHash callKeccak256 height word) := by
  unfold LeanVM.Prover.buildTreeWithHash
  refine HashOK.bind ?_ fun leaves ↦ HashOK.bind ?_ fun _ ↦ HashOK.pure _ _
  · unfold LeanVM.Prover.leafDigestsWithHash
    refine HashOK.arrayMapM _ (fun i ↦ hashOK_callKeccak256 (good_of_length (Or.inl ?_))) _
    rw [length_flatMap_kBytes, hw]
  · suffices h : ∀ k (level : Array Digest),
        HashOK Good (LeanVM.Prover.levelsWithHash callKeccak256 k level) from h _ _
    intro k
    induction k with
    | zero => intro level; exact HashOK.pure _ _
    | succ k ih =>
      intro level
      unfold LeanVM.Prover.levelsWithHash
      refine HashOK.bind ?_ fun up ↦ HashOK.bind (ih up) fun _ ↦ HashOK.pure _ _
      unfold LeanVM.Prover.parentsWithHash
      refine HashOK.arrayMapM _ (fun j ↦ hashOK_callKeccak256 (good_of_length (Or.inr (Or.inl ?_))))
        _
      rw [List.length_append, length_digestBytes, length_digestBytes]

theorem length_stackWordFast (μ R : ℕ) (stack : Array K) (p : ℕ) :
    (LeanVM.Prover.stackWordFast μ R stack p).length = 64 := by
  unfold LeanVM.Prover.stackWordFast LeanVM.Prover.stackWordFast.stackWordOf
  split <;> simp

theorem hashOK_commitWithH (μ : ℕ) (stack : Array K) :
    HashOK Good (commitWithH callKeccak256 μ stack) :=
  hashOK_buildTree _ _ (length_stackWordFast μ 1 stack)

theorem hashOK_setupWithH : HashOK Good (setupWithH callKeccak256) :=
  HashOK.bind (hashOK_commitWithH _ _) fun _ ↦ HashOK.pure _ _

theorem length_label (ir : Digest) (stmt : Statement) : (label ir stmt).length = 112 := by
  simp only [label, List.length_append, length_digestBytes, Vector.length_toList]
  have h16 : "pcs-quotient-kc1".toUTF8.toList.length = 16 := by decide +kernel
  omega

/-- **The first stage hashes nothing of the chain's lengths.** -/
theorem hashOK_stageAG (setup : OracleComp KeccakCalls Digest) (hs : HashOK Good setup)
    (circuit : Circuit) (cells : Array K) (masks : Masks) (witnessPad : Padding)
    (stmt : Statement) :
    HashOK Good (stageAG setup circuit cells masks witnessPad stmt) := by
  unfold stageAG
  refine HashOK.bind hs fun _ ↦ HashOK.bind (hashOK_commitWithH _ _) fun indexTree ↦
    HashOK.bind (hashOK_commitWithH _ _) fun _ ↦ HashOK.bind ?_ fun _ ↦ HashOK.pure _ _
  exact hashOK_callKeccak256 (good_of_length (Or.inr (Or.inr (length_label _ _))))

/-- **The second stage hashes nothing of the chain's lengths.** -/
theorem hashOK_stageBG (circuit : Circuit) (cells : Array K) (quotientPad : Padding) (a : AuxA)
    (s₁ s₂ s₃ : Digest) :
    HashOK Good (stageBG circuit cells quotientPad a s₁ s₂ s₃) := by
  unfold stageBG
  exact HashOK.bind (hashOK_commitWithH _ _) fun _ ↦ HashOK.pure _ _

end E2ECompleteness
