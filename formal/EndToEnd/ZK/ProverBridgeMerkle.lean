-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The statement's trees are leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0:
-- `Statement/Prover/Run.lean`'s `buildTreeM`, `leafDigestsM`, `parentsM`, `levelsM`,
-- `Tree.opening`); `levelUpP`, `levelsP` are `QuotientZk/Deployed/Skeleton.lean`'s `levelUp`,
-- `levels` with Keccak-256 a function.
import ZK.ProverBridgeReduce

/-!
# The three Merkle trees agree

With the permutation `π` fixed, Keccak-256 is the function `kDet π` and three codes compute Merkle
trees: the statement's prover (mumbai's `buildTreeM`, over arrays of `Digest`), the skeleton
(`Deployed.levels`, over lists of 32 bytes, its hashes `pub` queries) and `fmt` (`expandMulti`, the
full paths of a pruned multiproof). They agree:

* **(a)** `digestOfBytes_toBytes`: a digest's 32 bytes read back as its lanes.
* **(b)** `runDet_levels`: the skeleton's tree against an oracle `G` is the pure `levelsP` of
  Keccak-256 `m ↦ (G (inl m)).1`, the challenges untouched.
* **(c)** `tree_levels`, `tree_root`: the statement's tree, its levels read as bytes, is `levelsP`
  of `kDet π` on the leaves' digests; its root is the skeleton's `rootOf`.
* **(d)** `expandMulti_eq`: `fmt`'s expansion of the multiproof `prune` sends (the sorted distinct
  positions, their rows, the siblings) gives, at every queried position, the statement's opening
  (`Tree.opening`). By induction over the levels: the nodes `expandLevel` knows at a level are the
  active positions and their siblings with their true digests (the siblings `pruneLevel` sends are
  consumed in the order sent, `expandLevel_pruneLevel`), and the parents `pairUp` hashes are the
  next level's active positions with their true digests (`pairUpP_comp`).

No tree is evaluated: every statement is for a general height.
-/

open OracleComp OracleSpec
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Prover
open QuotientRpm (Bytes32)
open QuotientZk.Deployed (Inp Out Msg Tbl Pos DSpec levelUp rootOf sortedUnique pruneLevel prune
  hashH)

namespace PcsQuotient.EndToEnd.Merkle

open QuotientZk (Proto)

set_option linter.unusedSectionVars false

/-! ## (a) Digests and their bytes -/

theorem ofLane_lane (x : K) : K.ofLane (K.lane x) = x := rfl

theorem toBytes_toList (d : Digest) : (Digest.toBytes d).toList = digestBytes d := rfl

theorem toBytes_default : Digest.toBytes (default : Digest) = default := rfl

/-- Lane `i` of words, read from their bytes. -/
theorem lane_at : ∀ (ws : List UInt64) (i : ℕ) (_ : i < ws.length),
    LeanVM.Rpm.bytesLane (((ws.flatMap wordBytes).drop (8 * i)).take 8) = ws[i]
  | w :: ws, 0, _ => by
    simp only [List.flatMap_cons, Nat.mul_zero, List.drop_zero, List.getElem_cons_zero]
    rw [List.take_left' (LeanVM.Rpm.wordBytes_len w)]
    simpa using LeanVM.Rpm.bytesLane_wordBytes_append w []
  | w :: ws, i + 1, hi => by
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    rw [show 8 * (i + 1) = 8 + 8 * i by ring, ← List.drop_drop,
      List.drop_left' (LeanVM.Rpm.wordBytes_len w)]
    exact lane_at ws i (by simpa using hi)

/-- **A digest's bytes read back as its lanes.** -/
theorem digestOfBytes_toBytes (d : Digest) : digestOfBytes (Digest.toBytes d) = d := by
  apply Vector.ext
  intro i hi
  have h1 : (digestOfBytes (Digest.toBytes d))[i] =
      LeanVM.Rpm.bytesLane ((((Digest.toBytes d).toList).drop (8 * i)).take 8) := by
    unfold digestOfBytes
    rw [Vector.getElem_ofFn]
  rw [h1, toBytes_toList]
  unfold digestBytes
  rw [lane_at d.toList i (by simpa using hi)]
  exact Vector.getElem_toList _

/-- The converse on the image: 32 bytes that are a digest's are its bytes again. -/
theorem toBytes_digestOfBytes {b : Bytes32} {d : Digest} (h : b = Digest.toBytes d) :
    Digest.toBytes (digestOfBytes b) = b := by
  rw [h, digestOfBytes_toBytes]

/-! ## (b) The skeleton's tree with Keccak-256 a function -/

/-- `levelUp` with Keccak-256 the function `kh`. -/
def levelUpP (kh : List UInt8 → Bytes32) : List Bytes32 → List Bytes32
  | a :: b :: rest => kh (a.toList ++ b.toList) :: levelUpP kh rest
  | _ => []

/-- `levels` with Keccak-256 the function `kh`. -/
def levelsP (kh : List UInt8 → Bytes32) : ℕ → List Bytes32 → List (List Bytes32)
  | 0, leaves => [leaves]
  | d + 1, leaves => leaves :: levelsP kh d (levelUpP kh leaves)

section Skel

variable {S : Type} (P : Proto S Inp Out Msg Tbl Pos) (G : Inp → Out) (s : S)

theorem runDet_pure {β : Type} (a : β) (hist : List Out) :
    runDet P G s (pure a) hist = (a, hist) := by
  simp only [runDet, simulateQ_pure, StateT.run_pure]
  rfl

theorem runDet_bind {α β : Type} (X : OracleComp DSpec α) (f : α → OracleComp DSpec β)
    (hist : List Out) :
    runDet P G s (X >>= f) hist =
      runDet P G s (f (runDet P G s X hist).1) (runDet P G s X hist).2 := by
  simp only [runDet, simulateQ_bind, StateT.run_bind]
  rfl

theorem runDet_hashH (m : List UInt8) (hist : List Out) :
    runDet P G s (hashH m) hist = ((G (.inl m)).1, hist) := by
  unfold hashH
  rw [runDet_query_bind]
  exact runDet_pure P G s _ _

/-- **`levelUp` against `G`**: the pure `levelUpP` of `m ↦ (G (inl m)).1`, no challenge. -/
theorem runDet_levelUp : ∀ (leaves : List Bytes32) (hist : List Out),
    runDet P G s (levelUp leaves) hist = (levelUpP (fun m ↦ (G (.inl m)).1) leaves, hist)
  | a :: b :: rest, hist => by
    rw [levelUp, runDet_bind, runDet_hashH, runDet_bind, runDet_levelUp rest, runDet_pure]
    rfl
  | [], hist => runDet_pure P G s _ _
  | [_], hist => runDet_pure P G s _ _

/-- **`levels` against `G`**: the pure `levelsP` of `m ↦ (G (inl m)).1`, no challenge. -/
theorem runDet_levels : ∀ (d : ℕ) (leaves : List Bytes32) (hist : List Out),
    runDet P G s (QuotientZk.Deployed.levels d leaves) hist =
      (levelsP (fun m ↦ (G (.inl m)).1) d leaves, hist)
  | 0, leaves, hist => by
    rw [QuotientZk.Deployed.levels]
    exact runDet_pure P G s _ _
  | d + 1, leaves, hist => by
    rw [QuotientZk.Deployed.levels, runDet_bind, runDet_levelUp, runDet_bind, runDet_levels d,
      runDet_pure]
    rfl

end Skel

/-! ## (c) The statement's tree -/

section Tree

variable (π : Equiv.Perm Eager.St)

/-- `H(x ‖ y)` over `π`. -/
def hashD (x y : Digest) : Digest :=
  (keccak256With (permId π) (digestBytes x ++ digestBytes y)).run

/-- The levels of the statement's tree over `π`, leaves first. -/
def treeLevels (d : ℕ) (word : Compile.Word) : List (Array Digest) :=
  (levelsM (permId π) d (leafDigestsM (permId π) d word).run).run

/-- The levels of the statement's tree, each as a list of 32-byte digests. -/
def treeBytes (d : ℕ) (word : Compile.Word) : List (List Bytes32) :=
  (buildTreeM (permId π) d word).run.levels.toList.map fun a ↦ a.toList.map Digest.toBytes

theorem buildTree_run (d : ℕ) (word : Compile.Word) :
    (buildTreeM (permId π) d word).run = ⟨d, word, (treeLevels π d word).toArray⟩ := rfl

theorem treeBytes_eq (d : ℕ) (word : Compile.Word) :
    treeBytes π d word = (treeLevels π d word).map fun a ↦ a.toList.map Digest.toBytes := by
  simp only [treeBytes, buildTree_run, List.toList_toArray]

theorem getD_toArray (L : List (Array Digest)) (k : ℕ) : L.toArray.getD k #[] = L.getD k #[] := by
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

theorem getD_map_toBytes (a : Array Digest) (i : ℕ) :
    (a.toList.map Digest.toBytes).getD i default = Digest.toBytes (a.getD i default) := by
  rw [← toBytes_default, List.getD_map]
  simp only [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

theorem getD_bytes (L : List (Array Digest)) (k i : ℕ) :
    digestOfBytes (((L.map fun a ↦ a.toList.map Digest.toBytes).getD k []).getD i default) =
      (L.getD k #[]).getD i default := by
  have e : ([] : List Bytes32) = (fun a : Array Digest ↦ a.toList.map Digest.toBytes) #[] := rfl
  rw [e, List.getD_map, getD_map_toBytes, digestOfBytes_toBytes]

theorem parentsM_run (level : Array Digest) (n : ℕ) :
    (parentsM (permId π) level n).run =
      (Array.range n).map fun j ↦
        hashD π (level.getD (2 * j) default) (level.getD (2 * j + 1) default) := by
  simp only [parentsM, Array.idRun_mapM]
  rfl

theorem parentsM_size (level : Array Digest) (n : ℕ) :
    (parentsM (permId π) level n).run.size = n := by
  rw [parentsM_run, Array.size_map, Array.size_range]

theorem parentsM_getD (level : Array Digest) (n i : ℕ) (hi : i < n) :
    (parentsM (permId π) level n).run.getD i default =
      hashD π (level.getD (2 * i) default) (level.getD (2 * i + 1) default) := by
  rw [parentsM_run, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range,
    ite_eq_left hi]
  rfl

theorem levelsM_succ_run (k : ℕ) (level : Array Digest) :
    (levelsM (permId π) (k + 1) level).run =
      level :: (levelsM (permId π) k (parentsM (permId π) level (2 ^ k)).run).run := rfl

theorem levelsM_length : ∀ (k : ℕ) (level : Array Digest),
    (levelsM (permId π) k level).run.length = k + 1
  | 0, _ => rfl
  | k + 1, level => by
    rw [levelsM_succ_run, List.length_cons, levelsM_length k]

theorem levelsM_getD_zero : ∀ (k : ℕ) (level : Array Digest),
    (levelsM (permId π) k level).run.getD 0 #[] = level
  | 0, _ => rfl
  | k + 1, level => by rw [levelsM_succ_run]; rfl

/-- Level `j + 1` of a tree is the parents of level `j`. -/
theorem levelsM_getD_succ : ∀ (k : ℕ) (level : Array Digest) (j : ℕ), j < k →
    (levelsM (permId π) k level).run.getD (j + 1) #[] =
      (parentsM (permId π) ((levelsM (permId π) k level).run.getD j #[]) (2 ^ (k - j - 1))).run
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | k + 1, level, 0, _ => by
    rw [levelsM_succ_run, List.getD_cons_succ, levelsM_getD_zero, List.getD_cons_zero]
    rfl
  | k + 1, level, j + 1, hj => by
    rw [levelsM_succ_run, List.getD_cons_succ, List.getD_cons_succ,
      levelsM_getD_succ k _ j (by omega), show k + 1 - (j + 1) - 1 = k - j - 1 by omega]

theorem leafDigestsM_size (d : ℕ) (word : Compile.Word) :
    (leafDigestsM (permId π) d word).run.size = 2 ^ d := by
  simp only [leafDigestsM, Array.idRun_mapM, Array.size_map, Array.size_range]

theorem leafDigestsM_getD (d : ℕ) (word : Compile.Word) (p : ℕ) (hp : p < 2 ^ d) :
    (leafDigestsM (permId π) d word).run.getD p default =
      (keccak256With (permId π) ((word p).flatMap kBytes)).run := by
  simp only [leafDigestsM, Array.idRun_mapM, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_range, ite_eq_left hp]
  rfl

/-- `levelUpP` of a list of `2n` digests: `n` hashes of pairs. -/
theorem levelUpP_range (kh : List UInt8 → Bytes32) :
    ∀ (n : ℕ) (L : List Bytes32), L.length = 2 * n →
    levelUpP kh L = (List.range n).map fun j ↦
      kh ((L.getD (2 * j) default).toList ++ (L.getD (2 * j + 1) default).toList)
  | 0, [], _ => rfl
  | 0, _ :: _, hL => by simp at hL
  | n + 1, [], hL => by simp at hL
  | n + 1, [_], hL => by simp at hL; omega
  | n + 1, a :: b :: L, hL => by
    have hL' : L.length = 2 * n := by simp at hL; omega
    rw [levelUpP, levelUpP_range kh n L hL', List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1

theorem parentsM_bytes (k : ℕ) (level : Array Digest) (hs : level.size = 2 ^ (k + 1)) :
    (parentsM (permId π) level (2 ^ k)).run.toList.map Digest.toBytes =
      levelUpP (kDet π) (level.toList.map Digest.toBytes) := by
  rw [levelUpP_range (kDet π) (2 ^ k) _ (by simp [hs, pow_succ']), parentsM_run, Array.toList_map,
    Array.toList_range, List.map_map]
  refine List.map_congr_left fun j _ ↦ ?_
  simp only [Function.comp_apply, getD_map_toBytes, toBytes_toList]
  rfl

theorem levelsM_bytes : ∀ (k : ℕ) (level : Array Digest), level.size = 2 ^ k →
    ((levelsM (permId π) k level).run.map fun a ↦ a.toList.map Digest.toBytes) =
      levelsP (kDet π) k (level.toList.map Digest.toBytes)
  | 0, _, _ => rfl
  | k + 1, level, hs => by
    rw [levelsM_succ_run, List.map_cons, levelsP,
      levelsM_bytes k _ (parentsM_size π level (2 ^ k)), parentsM_bytes π k level hs]

/-- **(c) The statement's tree is the skeleton's**: its levels, read as bytes, are `levelsP` of
Keccak-256 over `π` on the leaves' digests. -/
theorem tree_levels (d : ℕ) (word : Compile.Word) :
    treeBytes π d word =
      levelsP (kDet π) d ((List.range (2 ^ d)).map fun i ↦ kDet π ((word i).flatMap kBytes)) := by
  rw [treeBytes_eq, treeLevels, levelsM_bytes π d _ (leafDigestsM_size π d word)]
  congr 1
  simp only [leafDigestsM, Array.idRun_mapM, Array.toList_map, Array.toList_range, List.map_map]
  rfl

/-- **(c) The roots agree.** -/
theorem tree_root (d : ℕ) (word : Compile.Word) :
    rootOf (levelsP (kDet π) d ((List.range (2 ^ d)).map fun i ↦ kDet π ((word i).flatMap kBytes))) =
      Digest.toBytes (buildTreeM (permId π) d word).run.root := by
  rw [← tree_levels, treeBytes_eq, buildTree_run]
  have hlen : (treeLevels π d word).length = d + 1 := levelsM_length π d _
  simp only [rootOf, Tree.root, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
    List.length_map, hlen, Nat.add_sub_cancel, List.getElem?_map, getD_toArray,
    List.getD_eq_getElem?_getD]
  rcases (treeLevels π d word)[d]? with _ | ⟨⟨l⟩⟩
  · simp [toBytes_default]
  · cases l <;> simp [toBytes_default]

end Tree

/-! ## (d) The multiproof's expansion -/

section Expand

variable (π : Equiv.Perm Eager.St)

/-- `pairUp` against `π`. -/
def pairUpP : List (ℕ × Digest) → List (ℕ × Digest)
  | (a, x) :: (_, y) :: rest => (a / 2, hashD π x y) :: pairUpP rest
  | _ => []

/-- `expandLevels` against `π`. -/
def expandLevelsP : ℕ → List (ℕ × Digest) → List Digest → List (List (ℕ × Digest))
  | 0, _, _ => []
  | h + 1, known, sibs =>
    (expandLevel known sibs).1 ::
      expandLevelsP h (pairUpP π (expandLevel known sibs).1) (expandLevel known sibs).2

/-- The row `expandMulti` reads for position `p`. -/
def rowAtP (sp : List ℕ) (rows : List (List UInt64)) (p : ℕ) : List K :=
  ((sp.zip rows).find? fun e ↦ e.1 = p).elim [] fun e ↦ e.2.map K.ofLane

theorem sim_permF (x : KeccakState) : simulateQ (permOnly π) (permF x) = permId π x := by
  simp only [permF, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
  rfl

theorem sim_keccak (m : List UInt8) :
    simulateQ (permOnly π) (keccak256With permF m) = keccak256With (permId π) m := by
  have h := Param.keccak256With_hom (simHom (permOnly π)) permF m
  simp only [simHom_app, sim_permF] at h
  exact h

theorem sim_mapM_list {α β : Type} (f : α → OracleComp PermSpec β) (l : List α) :
    simulateQ (permOnly π) (l.mapM f) = l.mapM fun a ↦ simulateQ (permOnly π) (f a) :=
  (simHom (permOnly π)).app_mapM_list f l

theorem sim_pairUp :
    ∀ L : List (ℕ × Digest), simulateQ (permOnly π) (pairUp L) = pure (pairUpP π L)
  | (a, x) :: (b, y) :: rest => by
    simp only [pairUp, simulateQ_bind, simulateQ_pure, sim_keccak, sim_pairUp rest, pairUpP]
    rfl
  | [] => by simp only [pairUp, simulateQ_pure, pairUpP]
  | [(a, x)] => by simp only [pairUp, simulateQ_pure, pairUpP]

theorem sim_expandLevels : ∀ (h : ℕ) (known : List (ℕ × Digest)) (sibs : List Digest),
    simulateQ (permOnly π) (expandLevels h known sibs) = pure (expandLevelsP π h known sibs)
  | 0, _, _ => by simp only [expandLevels, simulateQ_pure, expandLevelsP]
  | h + 1, known, sibs => by
    rcases hE : expandLevel known sibs with ⟨level, rest⟩
    simp only [expandLevels, hE, simulateQ_bind, simulateQ_pure, sim_pairUp, sim_expandLevels h,
      expandLevelsP, pure_bind]

/-- **`expandMulti` against `π`.** -/
theorem sim_expandMulti (sp : List ℕ) (rows : List (List UInt64)) (sibs : List Bytes32)
    (height : ℕ) (ps : List ℕ) :
    (simulateQ (permOnly π) (expandMulti (sp, rows, sibs) height ps)).run =
      ps.map fun q ↦ ⟨rowAtP sp rows q, (List.range height).map fun k ↦
        nodeAt ((expandLevelsP π height
          (sp.map fun p ↦ (p, (keccak256With (permId π) ((rowAtP sp rows p).flatMap kBytes)).run))
          (sibs.map digestOfBytes)).getD k []) ((q >>> k) ^^^ 1)⟩ := by
  simp only [expandMulti, simulateQ_bind, simulateQ_pure, sim_mapM_list, sim_keccak,
    sim_expandLevels, Id.run_bind, Id.run_pure, List.idRun_mapM]
  rfl

/-! ### Positions -/

theorem xor_one (p : ℕ) : p ^^^ 1 = if p % 2 = 0 then p + 1 else p - 1 := by
  split_ifs with h
  · exact Nat.xor_one_of_even (Nat.even_iff.mpr h)
  · exact Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))

theorem xor_one_xor_one (p : ℕ) : p ^^^ 1 ^^^ 1 = p := by
  have h1 := xor_one p
  have h2 := xor_one (p ^^^ 1)
  split_ifs at h1 h2 <;> omega

theorem xor_one_div_two (p : ℕ) : (p ^^^ 1) / 2 = p / 2 := by
  have h1 := xor_one p
  split_ifs at h1 <;> omega

theorem sibling_eq (i : ℕ) : sibling i = i ^^^ 1 := by
  rw [sibling, xor_one]

/-! ### One level -/

/-- The nodes `expandLevel` completes at a level: the active positions `A` and their siblings, with
the digests `n`, in `pruneLevel`'s order. -/
def comp (n : ℕ → Digest) : List ℕ → List (ℕ × Digest)
  | p :: q :: rest =>
    if q = p ^^^ 1 then (p, n p) :: (q, n q) :: comp n rest
    else withSibling p (n p) (n (p ^^^ 1)) ++ comp n (q :: rest)
  | [p] => withSibling p (n p) (n (p ^^^ 1))
  | [] => []

/-- **One level**: `expandLevel` of the active positions' true nodes and the siblings `pruneLevel`
sends completes them (`comp`) and leaves the siblings after. -/
theorem expandLevel_pruneLevel (n : ℕ → Digest) (lv : List Bytes32) (rest : List Digest) :
    ∀ A : List ℕ, (∀ p ∈ A, digestOfBytes (lv.getD (p ^^^ 1) default) = n (p ^^^ 1)) →
      expandLevel (A.map fun p ↦ (p, n p)) ((pruneLevel lv A).1.map digestOfBytes ++ rest) =
        (comp n A, rest)
  | [], _ => by simp only [List.map_nil, pruneLevel, List.nil_append, expandLevel, comp]
  | [p], h => by
    simp only [List.map_cons, List.map_nil, pruneLevel, List.cons_append, List.nil_append,
      expandLevel, comp]
    rw [h p (by simp)]
  | p :: q :: A, h => by
    by_cases hq : q = p ^^^ 1
    · have ih := expandLevel_pruneLevel n lv rest A (fun r hr ↦ h r (by simp [hr]))
      simp only [List.map_cons, pruneLevel, ite_eq_left hq, expandLevel, comp]
      rw [ih]
    · have ih := expandLevel_pruneLevel n lv rest (q :: A)
        (fun r hr ↦ h r (List.mem_cons_of_mem _ hr))
      simp only [List.map_cons] at ih
      simp only [List.map_cons, pruneLevel, ite_eq_right hq, expandLevel, comp, List.cons_append]
      rw [ih, h p (by simp)]

theorem pairUpP_withSibling (n : ℕ → Digest) (p : ℕ) (L : List (ℕ × Digest)) :
    pairUpP π (withSibling p (n p) (n (p ^^^ 1)) ++ L) =
      (p / 2, hashD π (n (2 * (p / 2))) (n (2 * (p / 2) + 1))) :: pairUpP π L := by
  have hx := xor_one p
  unfold withSibling
  split_ifs at hx ⊢ with he
  · simp only [List.cons_append, List.nil_append, pairUpP]
    rw [hx, show 2 * (p / 2) = p by omega]
  · simp only [List.cons_append, List.nil_append, pairUpP]
    rw [hx, show 2 * (p / 2) = p - 1 by omega, show (p - 1) / 2 = p / 2 by omega,
      show p - 1 + 1 = p by omega]

theorem mem_pruneLevel_snd (lv : List Bytes32) :
    ∀ (A : List ℕ) (x : ℕ), x ∈ (pruneLevel lv A).2 → ∃ p ∈ A, x = p / 2
  | [], x, hx => by simp [pruneLevel] at hx
  | [p], x, hx => by
    simp only [pruneLevel, List.mem_singleton] at hx
    exact ⟨p, by simp, hx⟩
  | p :: q :: A, x, hx => by
    by_cases hq : q = p ^^^ 1
    · simp only [pruneLevel, ite_eq_left hq, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨p, by simp, rfl⟩
      · obtain ⟨r, hr, rfl⟩ := mem_pruneLevel_snd lv A x hx
        exact ⟨r, by simp [hr], rfl⟩
    · simp only [pruneLevel, ite_eq_right hq, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨p, by simp, rfl⟩
      · obtain ⟨r, hr, rfl⟩ := mem_pruneLevel_snd lv (q :: A) x hx
        exact ⟨r, List.mem_cons_of_mem _ hr, rfl⟩

theorem div_two_mem_pruneLevel_snd (lv : List Bytes32) :
    ∀ (A : List ℕ) (p : ℕ), p ∈ A → p / 2 ∈ (pruneLevel lv A).2
  | [], p, hp => by simp at hp
  | [r], p, hp => by
    simp only [List.mem_singleton] at hp
    simp [pruneLevel, hp]
  | r :: q :: A, p, hp => by
    by_cases hq : q = r ^^^ 1
    · simp only [pruneLevel, ite_eq_left hq, List.mem_cons]
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Or.inl rfl
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Or.inl (by rw [hq, xor_one_div_two])
      · exact Or.inr (div_two_mem_pruneLevel_snd lv A p hp)
    · simp only [pruneLevel, ite_eq_right hq, List.mem_cons]
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Or.inl rfl
      · exact Or.inr (div_two_mem_pruneLevel_snd lv (q :: A) p hp)

theorem pairwise_pruneLevel_snd (lv : List Bytes32) :
    ∀ A : List ℕ, A.Pairwise (· < ·) → (pruneLevel lv A).2.Pairwise (· < ·)
  | [], _ => by simp [pruneLevel]
  | [p], _ => by simp [pruneLevel]
  | p :: q :: A, hA => by
    rw [List.pairwise_cons] at hA
    have hpq := hA.1 q (by simp)
    have hx := xor_one p
    have hqA := List.pairwise_cons.mp hA.2
    by_cases hq : q = p ^^^ 1
    · simp only [pruneLevel, ite_eq_left hq, List.pairwise_cons]
      refine ⟨fun x hx' ↦ ?_, pairwise_pruneLevel_snd lv A hqA.2⟩
      obtain ⟨r, hr, rfl⟩ := mem_pruneLevel_snd lv A x hx'
      have hqr := hqA.1 r hr
      split_ifs at hx <;> omega
    · simp only [pruneLevel, ite_eq_right hq, List.pairwise_cons]
      refine ⟨fun x hx' ↦ ?_, pairwise_pruneLevel_snd lv (q :: A) hA.2⟩
      obtain ⟨r, hr, rfl⟩ := mem_pruneLevel_snd lv (q :: A) x hx'
      rcases List.mem_cons.mp hr with rfl | hr'
      · split_ifs at hx <;> omega
      · have hqr := hqA.1 r hr'
        split_ifs at hx <;> omega

/-- **The parents of a completed level** are the next level's active positions, each with the hash
of its children. -/
theorem pairUpP_comp (n : ℕ → Digest) (lv : List Bytes32) :
    ∀ A : List ℕ, A.Pairwise (· < ·) →
    pairUpP π (comp n A) =
      (pruneLevel lv A).2.map fun r ↦ (r, hashD π (n (2 * r)) (n (2 * r + 1)))
  | [], _ => by simp [comp, pairUpP, pruneLevel]
  | [p], _ => by
    have h := pairUpP_withSibling π n p []
    simp only [List.append_nil] at h
    simp only [comp, pruneLevel, h, pairUpP, List.map_cons, List.map_nil]
  | p :: q :: A, hA => by
    rw [List.pairwise_cons] at hA
    have hpq := hA.1 q (by simp)
    by_cases hq : q = p ^^^ 1
    · have ih := pairUpP_comp n lv A (List.pairwise_cons.mp hA.2).2
      have hx := xor_one p
      have hev : p % 2 = 0 := by split_ifs at hx with h <;> omega
      have hq' : q = p + 1 := by rw [hq, hx, ite_eq_left hev]
      simp only [comp, ite_eq_left hq, pairUpP, pruneLevel, ih, List.map_cons]
      rw [show 2 * (p / 2) = p by omega, hq']
    · have ih := pairUpP_comp n lv (q :: A) hA.2
      simp only [comp, ite_eq_right hq, pairUpP_withSibling, ih, pruneLevel, List.map_cons]

theorem mem_withSibling {p : ℕ} {a b : Digest} {e : ℕ × Digest} (he : e ∈ withSibling p a b) :
    e = (p, a) ∨ e = (p ^^^ 1, b) := by
  unfold withSibling at he
  split_ifs at he <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at he <;> tauto

theorem fst_mem_withSibling (p : ℕ) (a b : Digest) :
    p ^^^ 1 ∈ (withSibling p a b).map Prod.fst := by
  unfold withSibling
  split_ifs <;> simp

theorem comp_snd (n : ℕ → Digest) : ∀ (A : List ℕ), ∀ e ∈ comp n A, e.2 = n e.1
  | [], e, he => by simp [comp] at he
  | [p], e, he => by
    simp only [comp] at he
    rcases mem_withSibling he with rfl | rfl <;> rfl
  | p :: q :: A, e, he => by
    by_cases hq : q = p ^^^ 1
    · simp only [comp, ite_eq_left hq, List.mem_cons] at he
      rcases he with rfl | rfl | he
      · rfl
      · rfl
      · exact comp_snd n A e he
    · simp only [comp, ite_eq_right hq, List.mem_append] at he
      rcases he with he | he
      · rcases mem_withSibling he with rfl | rfl <;> rfl
      · exact comp_snd n (q :: A) e he

theorem comp_fst (n : ℕ → Digest) :
    ∀ (A : List ℕ), ∀ p ∈ A, p ^^^ 1 ∈ (comp n A).map Prod.fst
  | [], p, hp => by simp at hp
  | [r], p, hp => by
    simp only [List.mem_singleton] at hp
    subst hp
    simp only [comp]
    exact fst_mem_withSibling _ _ _
  | r :: q :: A, p, hp => by
    by_cases hq : q = r ^^^ 1
    · simp only [comp, ite_eq_left hq, List.map_cons, List.mem_cons]
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Or.inr (Or.inl hq.symm)
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Or.inl (by rw [hq, xor_one_xor_one])
      · exact Or.inr (Or.inr (comp_fst n A p hp))
    · simp only [comp, ite_eq_right hq, List.map_append, List.mem_append]
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Or.inl (fst_mem_withSibling _ _ _)
      · exact Or.inr (comp_fst n (q :: A) p hp)

/-- A key's first entry, when every entry's value is `g` of its key. -/
theorem find_key {β : Type} (L : List (ℕ × β)) (g : ℕ → β) (hL : ∀ e ∈ L, e.2 = g e.1)
    (x : ℕ) (hx : x ∈ L.map Prod.fst) :
    ∃ e, (L.find? fun e ↦ e.1 = x) = some e ∧ e.2 = g x := by
  rcases h : L.find? (fun e ↦ e.1 = x) with _ | e
  · rw [List.find?_eq_none] at h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact absurd (by simp) (h e he)
  · have hmem := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    simp only [decide_eq_true_eq] at hp
    exact ⟨e, h, by rw [hL e hmem, hp]⟩

theorem nodeAt_eq (n : ℕ → Digest) (L : List (ℕ × Digest)) (hL : ∀ e ∈ L, e.2 = n e.1)
    (x : ℕ) (hx : x ∈ L.map Prod.fst) : nodeAt L x = n x := by
  obtain ⟨e, he, h2⟩ := find_key L n hL x hx
  simp only [nodeAt, he, Option.map_some, Option.getD_some, h2]

/-! ### All levels -/

/-- **The expansion's levels hold the true siblings**: for a tree `T` (level `k + 1` the hashes of
level `k`'s pairs) whose levels as bytes are `lvs`, the expansion of `prune lvs A` from the active
positions' true leaves has, at level `k`, the true sibling of every active position's ancestor. -/
theorem expandLevelsP_spec (h : ℕ) : ∀ (T : ℕ → ℕ → Digest) (lvs : List (List Bytes32))
    (A : List ℕ), A.Pairwise (· < ·) → (∀ p ∈ A, p < 2 ^ h) → lvs.length = h + 1 →
    (∀ k i, digestOfBytes ((lvs.getD k []).getD i default) = T k i) →
    (∀ k < h, ∀ i < 2 ^ (h - k - 1), T (k + 1) i = hashD π (T k (2 * i)) (T k (2 * i + 1))) →
    ∀ p ∈ A, ∀ k < h,
      nodeAt ((expandLevelsP π h (A.map fun p ↦ (p, T 0 p))
        ((prune lvs A).map digestOfBytes)).getD k []) ((p / 2 ^ k) ^^^ 1) = T k ((p / 2 ^ k) ^^^ 1)
  := by
  induction h with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ k hk
    exact absurd hk (Nat.not_lt_zero k)
  | succ h ih =>
    intro T lvs A hA hAlt hlen hlv hT p hp k hk
    obtain ⟨lv0, lv1, lvs'', rfl⟩ : ∃ lv0 lv1 lvs'', lvs = lv0 :: lv1 :: lvs'' := by
      rcases lvs with _ | ⟨lv0, _ | ⟨lv1, lvs''⟩⟩
      · simp at hlen
      · simp at hlen
      · exact ⟨lv0, lv1, lvs'', rfl⟩
    have hA' := pairwise_pruneLevel_snd lv0 A hA
    have hnd : (pruneLevel lv0 A).2.dedup = (pruneLevel lv0 A).2 :=
      List.dedup_eq_self.mpr (hA'.imp ne_of_lt)
    have hprune : prune (lv0 :: lv1 :: lvs'') A =
        (pruneLevel lv0 A).1 ++ prune (lv1 :: lvs'') (pruneLevel lv0 A).2 := by
      rw [prune, hnd]
    have hE := expandLevel_pruneLevel (T 0) lv0 ((prune (lv1 :: lvs'') (pruneLevel lv0 A).2).map
      digestOfBytes) A (fun r _ ↦ by simpa using hlv 0 (r ^^^ 1))
    have hup : pairUpP π (comp (T 0) A) = (pruneLevel lv0 A).2.map fun r ↦ (r, T 1 r) := by
      rw [pairUpP_comp π (T 0) lv0 A hA]
      refine List.map_congr_left fun r hr ↦ ?_
      obtain ⟨q, hq, rfl⟩ := mem_pruneLevel_snd lv0 A r hr
      have hqlt := hAlt q hq
      have hb : q / 2 < 2 ^ (h + 1 - 0 - 1) := by
        rw [pow_succ] at hqlt
        simp only [Nat.sub_zero, Nat.add_sub_cancel]
        omega
      rw [hT 0 (Nat.succ_pos h) (q / 2) hb]
    rw [hprune, List.map_append, expandLevelsP, hE]
    dsimp only
    rw [hup]
    rcases k with _ | k
    · simp only [List.getD_cons_zero, pow_zero, Nat.div_one]
      exact nodeAt_eq (T 0) _ (comp_snd (T 0) A) _ (comp_fst (T 0) A p hp)
    · rw [List.getD_cons_succ, show p / 2 ^ (k + 1) = p / 2 / 2 ^ k by
        rw [Nat.div_div_eq_div_mul, pow_succ']]
      exact ih (fun k ↦ T (k + 1)) (lv1 :: lvs'') (pruneLevel lv0 A).2 hA'
        (fun r hr ↦ by
          obtain ⟨q, hq, rfl⟩ := mem_pruneLevel_snd lv0 A r hr
          have := hAlt q hq
          rw [pow_succ] at this
          omega)
        (by simpa using hlen)
        (fun k i ↦ by simpa using hlv (k + 1) i)
        (fun k hk i hi ↦ hT (k + 1) (by omega) i (by
          rw [show h + 1 - (k + 1) - 1 = h - k - 1 by omega]; exact hi))
        (p / 2) (div_two_mem_pruneLevel_snd lv0 A p hp) k (by omega)

/-! ### The openings -/

theorem zip_map_self {β : Type} (g : ℕ → β) :
    ∀ l : List ℕ, l.zip (l.map g) = l.map fun p ↦ (p, g p)
  | [] => rfl
  | a :: l => by simp [zip_map_self g l]

theorem sortedUnique_pairwise (ps : List ℕ) : (sortedUnique ps).Pairwise (· < ·) := by
  unfold sortedUnique
  have h1 : (ps.mergeSort (· ≤ ·)).Pairwise (· ≤ ·) := by
    have := List.pairwise_mergeSort (le := fun a b : ℕ ↦ decide (a ≤ b))
      (fun a b c h1 h2 ↦ by simp only [decide_eq_true_eq] at *; omega)
      (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) ps
    simpa using this
  have h2 := h1.sublist (List.dedup_sublist _)
  have h3 := List.nodup_dedup (ps.mergeSort (· ≤ ·))
  exact (h2.and h3).imp fun h ↦ lt_of_le_of_ne h.1 h.2

theorem mem_sortedUnique {ps : List ℕ} {p : ℕ} : p ∈ sortedUnique ps ↔ p ∈ ps := by
  simp only [sortedUnique, List.mem_dedup, List.mem_mergeSort]

theorem rowAtP_eq (sp : List ℕ) (word : Compile.Word) (p : ℕ) (hp : p ∈ sp) :
    rowAtP sp (sp.map fun p ↦ (word p).map K.lane) p = word p := by
  obtain ⟨e, he, h2⟩ := find_key (sp.zip (sp.map fun p ↦ (word p).map K.lane))
    (fun p ↦ (word p).map K.lane)
    (by rw [zip_map_self]; intro e he; simp at he; obtain ⟨a, _, rfl⟩ := he; rfl)
    p (by rw [zip_map_self, List.map_map]; simpa using hp)
  have hid : ∀ l : List K, l.map (fun x ↦ K.ofLane (K.lane x)) = l := fun l ↦ by
    induction l with
    | nil => rfl
    | cons a l ih => simp only [List.map_cons, ih]; rfl
  simp only [rowAtP, he, Option.elim_some, h2, List.map_map, Function.comp_def, hid]

theorem treeLevels_length (d : ℕ) (word : Compile.Word) : (treeLevels π d word).length = d + 1 :=
  levelsM_length π d _

theorem treeLevels_leaf (d : ℕ) (word : Compile.Word) (p : ℕ) (hp : p < 2 ^ d) :
    ((treeLevels π d word).getD 0 #[]).getD p default =
      (keccak256With (permId π) ((word p).flatMap kBytes)).run := by
  rw [treeLevels, levelsM_getD_zero, leafDigestsM_getD π d word p hp]

theorem treeLevels_parent (d : ℕ) (word : Compile.Word) (k : ℕ) (hk : k < d) (i : ℕ)
    (hi : i < 2 ^ (d - k - 1)) :
    ((treeLevels π d word).getD (k + 1) #[]).getD i default =
      hashD π (((treeLevels π d word).getD k #[]).getD (2 * i) default)
        (((treeLevels π d word).getD k #[]).getD (2 * i + 1) default) := by
  rw [treeLevels, levelsM_getD_succ π d _ k hk, parentsM_getD π _ _ i hi]

/-- The statement's opening at a position of the tree. -/
theorem opening_eq (d : ℕ) (word : Compile.Word) (q : ℕ) (hq : q < 2 ^ d) :
    (buildTreeM (permId π) d word).run.opening q =
      ⟨word q, (List.range d).map fun k ↦
        ((treeLevels π d word).getD k #[]).getD ((q / 2 ^ k) ^^^ 1) default⟩ := by
  rw [buildTree_run]
  simp only [Tree.opening, Nat.mod_eq_of_lt hq, sibling_eq, getD_toArray]

/-- **(d) `fmt`'s expansion gives the statement's openings**: from the multiproof the skeleton
sends for the queried positions `ps` (the sorted distinct positions, their rows as words, `prune` of
the tree's levels as bytes), `expandMulti` against `π` outputs, at every queried position, the
statement's tree's opening. -/
theorem expandMulti_eq (d : ℕ) (word : Compile.Word) (ps : List ℕ)
    (hps : ∀ p ∈ ps, p < 2 ^ d) :
    (simulateQ (permOnly π) (expandMulti (sortedUnique ps,
        (sortedUnique ps).map (fun p ↦ (word p).map K.lane),
        prune (treeBytes π d word) (sortedUnique ps)) d ps)).run =
      ps.map (buildTreeM (permId π) d word).run.opening := by
  have hspl : ∀ p ∈ sortedUnique ps, p < 2 ^ d := fun p hp ↦ hps p (mem_sortedUnique.mp hp)
  have hleaves : ((sortedUnique ps).map fun p ↦ (p, (keccak256With (permId π)
      ((rowAtP (sortedUnique ps) ((sortedUnique ps).map fun p ↦ (word p).map K.lane) p).flatMap
        kBytes)).run)) =
      (sortedUnique ps).map fun p ↦ (p, ((treeLevels π d word).getD 0 #[]).getD p default) := by
    refine List.map_congr_left fun p hp ↦ ?_
    rw [rowAtP_eq _ word p hp, treeLevels_leaf π d word p (hspl p hp)]
  rw [sim_expandMulti, hleaves, treeBytes_eq]
  refine List.map_congr_left fun q hq ↦ ?_
  rw [opening_eq π d word q (hps q hq), rowAtP_eq _ word q (mem_sortedUnique.mpr hq)]
  congr 1
  refine List.map_congr_left fun k hk ↦ ?_
  rw [List.mem_range] at hk
  rw [Nat.shiftRight_eq_div_pow]
  exact expandLevelsP_spec π d (fun k i ↦ ((treeLevels π d word).getD k #[]).getD i default)
    ((treeLevels π d word).map fun a ↦ a.toList.map Digest.toBytes) (sortedUnique ps)
    (sortedUnique_pairwise ps) hspl
    (by rw [List.length_map, treeLevels_length])
    (fun k i ↦ by exact getD_bytes _ k i)
    (fun k hk i hi ↦ treeLevels_parent π d word k hk i hi)
    q (mem_sortedUnique.mpr hq) k hk

/-- **(d) with the skeleton's levels** (`levelsP` of `kDet π` on the leaves, by (c)). -/
theorem expandMulti_eq_levelsP (d : ℕ) (word : Compile.Word) (ps : List ℕ)
    (hps : ∀ p ∈ ps, p < 2 ^ d) :
    (simulateQ (permOnly π) (expandMulti (sortedUnique ps,
        (sortedUnique ps).map (fun p ↦ (word p).map K.lane),
        prune (levelsP (kDet π) d
            ((List.range (2 ^ d)).map fun i ↦ kDet π ((word i).flatMap kBytes)))
          (sortedUnique ps)) d ps)).run =
      ps.map (buildTreeM (permId π) d word).run.opening := by
  rw [← tree_levels]
  exact expandMulti_eq π d word ps hps

end Expand

end PcsQuotient.EndToEnd.Merkle

/-- info: 'PcsQuotient.EndToEnd.Merkle.digestOfBytes_toBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PcsQuotient.EndToEnd.Merkle.digestOfBytes_toBytes

/-- info: 'PcsQuotient.EndToEnd.Merkle.runDet_levels' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms PcsQuotient.EndToEnd.Merkle.runDet_levels

/-- info: 'PcsQuotient.EndToEnd.Merkle.tree_levels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PcsQuotient.EndToEnd.Merkle.tree_levels

/-- info: 'PcsQuotient.EndToEnd.Merkle.tree_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PcsQuotient.EndToEnd.Merkle.tree_root

/-- info: 'PcsQuotient.EndToEnd.Merkle.expandMulti_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PcsQuotient.EndToEnd.Merkle.expandMulti_eq

/-- info: 'PcsQuotient.EndToEnd.Merkle.expandMulti_eq_levelsP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PcsQuotient.EndToEnd.Merkle.expandMulti_eq_levelsP
