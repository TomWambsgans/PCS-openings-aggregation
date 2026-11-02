-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Soundness.Defs

/-!
# The setup's log is its tree's evaluations

Compose's random-permutation experiment logs the setup's Keccak-256 queries (`loggedKC`); the
Statement's extractor reads the setup's tree's evaluations (`PcsQuotient.Tree.evaluations`). They
are the same list: building a Merkle tree (mumbai's `buildTreeWithHash`) asks the hash of each
leaf's bytes, then of each pair of children, level by level, and the tree records every answer.

* **`loggedKC_buildTree`**: the logged build is the build, its log the tree's evaluations
  (`treeTr`), an equality of computations of the two oracles;
* **`loggedKC_stackSetup`**: the same for Compose's setup (`stackSetup`, the tree's root as 32
  bytes).

The route: `simulateQ_buildTreeM` (mumbai) makes the logged build the build with the logging hash
`logH`; hashing a range of inputs with it (`run_arrayMapM_range`) is hashing them plainly and
appending each input with its answer; so the leaves (`run_leafDigests`), each level's parents
(`run_parents`), the levels (`run_levels`, their log `levLog`) and the tree (`run_buildTree`) log
what `Tree.evaluations` reads off the tree, in its order.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp

namespace Soundness

open QuotientRpm Compose LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile WhirBridge

/-! ## The logging hash -/

/-- Keccak-256 as `logImplKC` answers it (mumbai's `implH`): the query, its answer appended to the
log. -/
abbrev logH : Bytes → StateT Transcript (OracleComp KeccakCalls) Digest :=
  LeanVM.Protocol.Compile.Rom.implH logImplKC

theorem logH_run (x : Bytes) (l : Transcript) :
    (logH x).run l = (fun u => (u, l ++ [(x, toB u)])) <$> callKeccak256 x := rfl

/-- Hashing the inputs `g s, …, g (s + n - 1)` with the log: the plain hashes, the log extended by
each input with its answer. -/
theorem run_mapM_range' (g : ℕ → Bytes) :
    ∀ (n s : ℕ) (l : Transcript),
      ((List.range' s n).mapM fun i => logH (g i)).run l =
        (fun ds : List Digest =>
            (ds, l ++ (List.range n).map fun i => (g (s + i), toB (ds.getD i default)))) <$>
          (List.range' s n).mapM fun i => callKeccak256 (g i)
  | 0, s, l => by simp
  | n + 1, s, l => by
    simp only [List.range'_succ, List.mapM_cons, StateT.run_bind, logH_run, bind_map_left,
      StateT.run_pure, run_mapM_range' g n (s + 1), map_bind, map_pure]
    refine bind_congr fun d => bind_congr fun ds => ?_
    simp [List.range_succ_eq_map, Nat.add_assoc, Nat.add_comm 1]

/-- The same over `Array.range n`. -/
theorem run_arrayMapM_range (g : ℕ → Bytes) (n : ℕ) (l : Transcript) :
    ((Array.range n).mapM fun i => logH (g i)).run l =
      (fun ds : Array Digest =>
          (ds, l ++ (List.range n).map fun i => (g i, toB (ds.getD i default)))) <$>
        (Array.range n).mapM fun i => callKeccak256 (g i) := by
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList, StateT.run_map, Array.toList_range]
  rw [show List.range n = List.range' 0 n from List.range_eq_range' ..]
  rw [run_mapM_range', Functor.map_map, Functor.map_map]
  congr 1
  funext ds
  simp [List.range_eq_range']

/-! ## The levels -/

/-- The log of a tree's levels above the first: level by level, each parent's two children's bytes
with its digest. -/
def levLog (k : ℕ) (lv : List (Array Digest)) : Transcript :=
  (List.range k).flatMap fun s => (List.range (2 ^ (k - (s + 1)))).map fun j =>
    (digestBytes ((lv.getD s #[]).getD (2 * j) default) ++
        digestBytes ((lv.getD s #[]).getD (2 * j + 1) default),
      toB ((lv.getD (s + 1) #[]).getD j default))

/-- The first level's parents, then the levels above. -/
theorem levLog_succ (k : ℕ) (level up : Array Digest) (r : List (Array Digest)) :
    levLog (k + 1) (level :: up :: r) =
      (List.range (2 ^ k)).map (fun j =>
        (digestBytes (level.getD (2 * j) default) ++ digestBytes (level.getD (2 * j + 1) default),
          toB (up.getD j default))) ++ levLog k (up :: r) := by
  simp only [levLog, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  simp [Nat.add_sub_add_right]

/-- The levels a build computes start with the level it starts from. -/
theorem levelsWithHash_bind_congr {β : Type} (k : ℕ) (level : Array Digest)
    (f g : List (Array Digest) → OracleComp KeccakCalls β)
    (h : ∀ r, f (level :: r) = g (level :: r)) :
    LeanVM.Prover.levelsWithHash callKeccak256 k level >>= f =
      LeanVM.Prover.levelsWithHash callKeccak256 k level >>= g := by
  cases k with
  | zero => simp [LeanVM.Prover.levelsWithHash, h]
  | succ k => simp only [LeanVM.Prover.levelsWithHash, bind_assoc, pure_bind, h]

/-- The parents of a level, logged. -/
theorem run_parents (level : Array Digest) (n : ℕ) (l : Transcript) :
    (LeanVM.Prover.parentsWithHash logH level n).run l =
      (fun up : Array Digest => (up, l ++ (List.range n).map fun j =>
        (digestBytes (level.getD (2 * j) default) ++ digestBytes (level.getD (2 * j + 1) default),
          toB (up.getD j default)))) <$>
        LeanVM.Prover.parentsWithHash callKeccak256 level n :=
  run_arrayMapM_range _ n l

/-- The levels, logged: their log is `levLog`. -/
theorem run_levels : ∀ (k : ℕ) (level : Array Digest) (l : Transcript),
    (LeanVM.Prover.levelsWithHash logH k level).run l =
      (fun lv => (lv, l ++ levLog k lv)) <$> LeanVM.Prover.levelsWithHash callKeccak256 k level
  | 0, level, l => by simp [LeanVM.Prover.levelsWithHash, levLog]
  | k + 1, level, l => by
    simp only [LeanVM.Prover.levelsWithHash, StateT.run_bind, run_parents, bind_map_left,
      run_levels k, StateT.run_pure, map_bind, map_pure]
    refine bind_congr fun up => ?_
    apply levelsWithHash_bind_congr
    intro r
    simp [levLog_succ]

/-! ## The tree -/

/-- The leaves, logged. -/
theorem run_leafDigests (ht : ℕ) (word : Word) (l : Transcript) :
    (LeanVM.Prover.leafDigestsWithHash logH ht word).run l =
      (fun ds : Array Digest => (ds, l ++ (List.range (2 ^ ht)).map fun i =>
        ((word i).flatMap kBytes, toB (ds.getD i default)))) <$>
        LeanVM.Prover.leafDigestsWithHash callKeccak256 ht word :=
  run_arrayMapM_range _ _ l

/-- The tree, logged: its log is the tree's evaluations. -/
theorem run_buildTree (ht : ℕ) (word : Word) :
    (LeanVM.Prover.buildTreeWithHash logH ht word).run [] =
      (fun t => (t, treeTr t)) <$> LeanVM.Prover.buildTreeWithHash callKeccak256 ht word := by
  simp only [LeanVM.Prover.buildTreeWithHash, StateT.run_bind, run_leafDigests, bind_map_left,
    run_levels, StateT.run_pure, map_bind, map_pure]
  refine bind_congr fun leaves => ?_
  apply levelsWithHash_bind_congr
  intro r
  simp [treeTr, PcsQuotient.Tree.evaluations, levLog, List.map_flatMap, Function.comp_def]

/-- Logging commutes with mapping the result. -/
theorem loggedKC_map {α β : Type} (f : α → β) (oa : OracleComp KeccakCalls α) :
    loggedKC (f <$> oa) = (fun p => (f p.1, p.2)) <$> loggedKC oa := by
  simp [loggedKC, simulateQ_map, StateT.run_map]

/-- **The logged build is the build, its log the tree's evaluations.** -/
theorem loggedKC_buildTree (ht : ℕ) (word : Word) :
    loggedKC (LeanVM.Prover.buildTreeWithHash callKeccak256 ht word) =
      (fun t => (t, treeTr t)) <$> LeanVM.Prover.buildTreeWithHash callKeccak256 ht word := by
  rw [loggedKC, LeanVM.Protocol.Compile.simulateQ_buildTreeM]
  exact run_buildTree ht word

/-- **The setup's log is its tree's evaluations.** -/
theorem loggedKC_stackSetup {F : Type} (D : Deploy F) (q₀ : Column D.Lσ.logN) :
    loggedKC (stackSetup D q₀) =
      (fun t => (toB t.root, treeTr t)) <$> LeanVM.Prover.buildTreeWithHash callKeccak256
        (rootHeight D.Lσ.logN D.R) (LeanVM.Protocol.Whir.Complete.stackWord D.Lσ.logN q₀) := by
  rw [stackSetup, wiringSetup, loggedKC_map, loggedKC_buildTree, Functor.map_map]

end Soundness

/-- info: 'Soundness.loggedKC_stackSetup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Soundness.loggedKC_stackSetup
