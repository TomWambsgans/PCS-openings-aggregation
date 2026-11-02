-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the block cost `hashBlocks` and the weight calculus `Common.QueryCostAtMost`;
-- the cost calculus of the verifier's programs (`Prog.Costs`, `costs_verifyStackedOpening`,
-- `ladder_cost`, `costHeight`, `whirBound`); the widths of WHIR's commitments (`WidthsLE`,
-- `widthsLE_verifyWhir`, `ladder_folds`). The weighted bounds of the prover's runner and of the
-- verifier's run are adapted from mumbai's query counts (`isTotalQueryBound_proveFromM`,
-- `Compile/Rom/Prover.lean`; `allQ_run`, `allQ_openAll`, `Rpm/Cost.lean`).
import E2ECompleteness.HashLen
import LeanVM.Protocol.Rpm.Cost
import LeanVM.Protocol.Verifier.Cost

/-!
# The block count of the deployed staged run

**`hcost_deployed`**: the deployed staged run (`stagedRun`, `Staging.lean`) makes at most `2^48`
block calls (`hashBlocks`: a Keccak-256 of `n` bytes costs `⌊n / 136⌋ + 1`, a Keccak-f[1600] one),
the third field of `Staged.Holds`, the hypothesis `hcost` of `completeness_deployed_cost_rej` and
`completeness_deployed_final`.

mumbai's route for leanVM (a count of queries times `2^32` blocks per query) is too coarse here: the
WHIR prover's count is `40481` quarter-queries times the prover's factor `2^27 + 2 · fuel + 2`
(`isTotalQueryBound_proveFromM`), about `2^43` per opening. The cost is weighted instead:

* **Every hash is short.** The tables' Merkle leaves are `64` words (`512` bytes, `4` blocks),
  WHIR's at most `192` words (`1536` bytes, `12` blocks: `WordsLE` for the honest script
  `openingScript`, from `ladder_folds`; `WidthsLE` for the verifier's program), the nodes `64`
  bytes, the chain's inputs at most `192` bytes, the openings' IVs at most `1564` bytes (points of
  at most `cellVars logRows + 6` coordinates, `claimsAt_len`).
* **The prover's runner** (`cost_runFromWithHash`): a program of cost `n` quarters
  (`Prog.Costs`) at height `h` costs at most `n · (13 · 2^h + 2 · fuel + 2)` blocks
  (`blockFactor`): a commitment, two quarters, builds a tree of at most `13 · 2^h` blocks; a proof
  of work, five quarters, at most `2 · fuel + 2` permutations.
* **The verifier's run** (`cost_runWithHash`): at most `3 · n` blocks, an opening of `k` positions
  costing `k · (12 + height)` blocks of the `3 · 4 · k · (1 + 26)` its quarters allow.
* **The stages** (`cost_stagedRunG`, generic in the setup, circuit and cells): the setup's, index,
  witness and quotient trees (`5 · 2^(μ - 5)` blocks each, `treeCost`), the label and the chain's
  four hashes, the reduction's six hashes (seven blocks) for the prover and for the verifier, the
  three openings proved (`proverCost`) and verified (`verifierCost`). Instantiated at the deployed
  sizes (`cellVars 22 = 24`, `fuel = 2^25`); nothing of the deployed circuit is evaluated.

The total is `114 098 677 826 653 < 2^47` blocks, nearly all of it the three WHIR provers'
`3 · 40481 · (14 · 2^26 + 2)`.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Rpm (hashBlocks)
open LeanVM.Prover (Tree Script)
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript

set_option autoImplicit false

namespace E2ECompleteness

namespace Cost

/-- At most `n` block calls. -/
abbrev QC {α : Type} (X : OracleComp KeccakCalls α) (n : ℕ) : Prop :=
  Common.QueryCostAtMost X hashBlocks n

/-! ## The calculus -/

theorem qc_pure {α : Type} (a : α) (n : ℕ) : QC (pure a : OracleComp KeccakCalls α) n := trivial

theorem QC.mono {α : Type} {X : OracleComp KeccakCalls α} {a b : ℕ} (h : QC X a) (hab : a ≤ b) :
    QC X b :=
  Common.QueryCostAtMost.mono h hab

theorem QC.bind {α β : Type} {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β}
    {a b : ℕ} (hX : QC X a) (hf : ∀ x, QC (f x) b) : QC (X >>= f) (a + b) :=
  Common.QueryCostAtMost.bind hX hf

theorem QC.bind_le {α β : Type} {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β}
    {a b c : ℕ} (hX : QC X a) (hf : ∀ x, QC (f x) b) (h : a + b ≤ c) : QC (X >>= f) c :=
  (hX.bind hf).mono h

theorem QC.map {α β : Type} {X : OracleComp KeccakCalls α} (f : α → β) {a : ℕ} (hX : QC X a) :
    QC (f <$> X) a :=
  Common.isWeightBound_map f hX

theorem qc_F (s : KeccakState) : QC (callKeccakF1600 s) 1 :=
  Common.isWeightBound_query hashBlocks (Sum.inr s)

theorem qc_H (x : Bytes) : QC (callKeccak256 x) (x.length / 136 + 1) :=
  Common.isWeightBound_query hashBlocks (Sum.inl x)

/-- A hash of at most `136 · k - 1` bytes costs at most `k` blocks. -/
theorem qc_H_le {x : Bytes} {k : ℕ} (hx : x.length < 136 * k) : QC (callKeccak256 x) k :=
  (qc_H x).mono (by omega)

/-! ## The sponge -/

theorem qc_duplex (sp : Sponge) : QC (duplex callKeccakF1600 sp) 1 :=
  ((qc_F _).bind fun _ ↦ qc_pure _ 0).mono le_rfl

theorem qc_absorb (sp : Sponge) (x : E) (tag : ℕ) :
    QC (Compile.absorb callKeccakF1600 sp x tag) 1 := by
  unfold Compile.absorb
  split
  · exact (qc_duplex sp).bind_le (fun _ ↦ qc_pure _ 0) le_rfl
  · exact (qc_pure _ 1).bind_le (fun _ ↦ qc_pure _ 0) le_rfl

theorem qc_squeeze (sp : Sponge) : QC (squeeze callKeccakF1600 sp) 1 :=
  (qc_duplex sp).bind_le (fun _ ↦ qc_pure _ 0) le_rfl

theorem qc_powStepM (sp : Sponge) (n : E) : QC (LeanVM.Prover.powStepM callKeccakF1600 sp n) 2 :=
  (qc_absorb _ _ _).bind_le (fun _ ↦ qc_squeeze _) le_rfl

theorem qc_searchM (bits : ℕ) (sp : Sponge) :
    ∀ (count n : ℕ), QC (LeanVM.Prover.searchM callKeccakF1600 bits sp n count) (2 * count)
  | 0, _ => trivial
  | count + 1, n => by
    simp only [LeanVM.Prover.searchM]
    refine (qc_powStepM _ _).bind_le (fun r ↦ ?_) (show 2 + 2 * count ≤ 2 * (count + 1) by omega)
    split
    · exact qc_pure _ _
    · exact qc_searchM bits sp count (n + 1)

theorem qc_findNonceM (bits : ℕ) (sp : Sponge) (fuel : ℕ) :
    QC (LeanVM.Prover.findNonceM callKeccakF1600 bits sp fuel) (2 * fuel) := by
  unfold LeanVM.Prover.findNonceM
  split
  · exact qc_pure _ _
  · exact qc_searchM _ _ _ _

/-! ## Merkle trees -/

theorem qc_listMapM {β γ : Type} (f : β → OracleComp KeccakCalls γ) (c : ℕ)
    (hf : ∀ a, QC (f a) c) : ∀ l : List β, QC (l.mapM f) (l.length * c)
  | [] => by rw [List.mapM_nil]; exact qc_pure _ _
  | a :: l => by
    rw [List.mapM_cons, List.length_cons]
    exact (hf a).bind_le (fun _ ↦ (qc_listMapM f c hf l).bind_le (fun _ ↦ qc_pure _ 0) le_rfl)
      (by rw [Nat.succ_mul]; omega)

theorem qc_arrayMapM {β γ : Type} (f : β → OracleComp KeccakCalls γ) (c : ℕ)
    (hf : ∀ a, QC (f a) c) (xs : Array β) : QC (xs.mapM f) (xs.size * c) := by
  rw [Array.mapM_eq_mapM_toList, ← Array.length_toList]
  exact (qc_listMapM f c hf _).map _

theorem qc_parents (level : Array Digest) (n : ℕ) :
    QC (LeanVM.Prover.parentsWithHash callKeccak256 level n) n := by
  unfold LeanVM.Prover.parentsWithHash
  refine (qc_arrayMapM _ 1 (fun j ↦ qc_H_le ?_) _).mono (by simp)
  rw [List.length_append, length_digestBytes, length_digestBytes]
  omega

theorem qc_levels : ∀ (k : ℕ) (level : Array Digest),
    QC (LeanVM.Prover.levelsWithHash callKeccak256 k level) (2 ^ k)
  | 0, _ => qc_pure _ _
  | k + 1, level => by
    simp only [LeanVM.Prover.levelsWithHash]
    exact (qc_parents _ _).bind_le (fun _ ↦ (qc_levels k _).bind_le (fun _ ↦ qc_pure _ 0)
      le_rfl) (by rw [pow_succ]; omega)

/-- **A Merkle tree** of rows of fewer than `136 · c` bytes: `2^height` leaves of at most `c`
blocks, fewer than `2^height` nodes of one. -/
theorem qc_buildTree (height : ℕ) (word : Word) (c : ℕ)
    (hw : ∀ p, 8 * (word p).length < 136 * c) :
    QC (LeanVM.Prover.buildTreeWithHash callKeccak256 height word) ((c + 1) * 2 ^ height) := by
  unfold LeanVM.Prover.buildTreeWithHash LeanVM.Prover.leafDigestsWithHash
  refine (qc_arrayMapM _ c (fun i ↦ qc_H_le ?_) _).bind_le (fun _ ↦ (qc_levels _ _).bind_le
    (fun _ ↦ qc_pure _ 0) le_rfl) (by rw [Array.size_range]; ring_nf; omega)
  rw [length_flatMap_kBytes]
  exact hw i

/-- A table's tree: `2^(μ − 5)` leaves of `64` words (`4` blocks) and its nodes. -/
theorem qc_commitWithH (μ : ℕ) (stack : Array K) :
    QC (commitWithH callKeccak256 μ stack) (5 * 2 ^ (μ - 6 + 1)) :=
  qc_buildTree _ _ 4 fun p ↦ by rw [length_stackWordFast]; omega

/-! ## The honest script commits rows of at most `192` words -/

/-- Every matrix the script commits has rows of at most `W` words. -/
def WordsLE (W : ℕ) {β : Type} : Script β → Prop
  | .ret _ => True
  | .send _ k => WordsLE W k
  | .sample k => ∀ c, WordsLE W (k c)
  | .grind k => WordsLE W k
  | .commit w k => (∀ p, (w p).length ≤ W) ∧ WordsLE W k
  | .query k => ∀ rows, WordsLE W (k rows)

namespace WordsLE

variable {W : ℕ} {β γ : Type}

theorem bind {x : Script β} {f : β → Script γ} (hx : WordsLE W x) (hf : ∀ a, WordsLE W (f a)) :
    WordsLE W (x >>= f) := by
  show WordsLE W (x.bind f)
  induction x with
  | ret a => exact hf a
  | send y k ih => exact ih hx
  | sample k ih => exact fun c ↦ ih c (hx c)
  | grind k ih => exact ih hx
  | commit w k ih => exact ⟨hx.1, ih hx.2⟩
  | query k ih => exact fun rows ↦ ih rows (hx rows)

theorem ret' (a : β) : WordsLE W (pure a : Script β) := trivial

theorem sendE (x : E) : WordsLE W (Script.sendE x) := trivial

theorem sendList : ∀ xs : List E, WordsLE W (Script.sendList xs)
  | [] => trivial
  | _ :: xs => sendList xs

theorem sampleE : WordsLE W Script.sampleE := fun _ ↦ trivial

theorem sampleN : ∀ n : ℕ, WordsLE W (Script.sampleN n)
  | 0 => trivial
  | n + 1 => bind sampleE fun _ ↦ bind (sampleN n) fun _ ↦ trivial

theorem grindS : WordsLE W Script.grindS := trivial

theorem queryS : WordsLE W Script.queryS := fun _ ↦ trivial

theorem commitS {w : Word} (hw : ∀ p, (w p).length ≤ W) : WordsLE W (Script.commitS w) :=
  ⟨hw, trivial⟩

end WordsLE

theorem wordsLE_roundA {W : ℕ} (claim : E) (Wt g : Array E) :
    WordsLE W (LeanVM.Prover.roundA claim Wt g) :=
  WordsLE.bind (WordsLE.sendE _) fun _ ↦ WordsLE.bind (WordsLE.sendList _) fun _ ↦ trivial

theorem wordsLE_foldRoundsA {W : ℕ} :
    ∀ (n : ℕ) (s : WhirState) (lf : List E) (Wt gt : Array E),
      WordsLE W (LeanVM.Prover.foldRoundsA n s lf Wt gt)
  | 0, _, _, _, _ => trivial
  | n + 1, s, lf, Wt, gt => by
    simp only [LeanVM.Prover.foldRoundsA]
    exact WordsLE.bind WordsLE.sampleE fun _ ↦ WordsLE.bind (wordsLE_roundA _ _ _) fun _ ↦
      wordsLE_foldRoundsA n _ _ _ _

theorem wordsLE_tailRoundsA {W : ℕ} :
    ∀ (n : ℕ) (quad : List E) (Wt gt : Array E),
      WordsLE W (LeanVM.Prover.tailRoundsA n quad Wt gt)
  | 0, _, _, _ => trivial
  | n + 1, quad, Wt, gt => by
    simp only [LeanVM.Prover.tailRoundsA]
    refine WordsLE.bind WordsLE.sampleE fun c ↦ ?_
    split
    · trivial
    · exact WordsLE.bind (wordsLE_roundA _ _ _) fun _ ↦ wordsLE_tailRoundsA n _ _ _

theorem wordsLE_sampleQueriesS {W : ℕ} (depth : ℕ) :
    ∀ (fuel remaining : ℕ), WordsLE W (LeanVM.Prover.sampleQueriesS depth fuel remaining)
  | 0, _ => trivial
  | fuel + 1, remaining => by
    simp only [LeanVM.Prover.sampleQueriesS]
    split
    · trivial
    · exact WordsLE.bind WordsLE.sampleE fun _ ↦
        WordsLE.bind (wordsLE_sampleQueriesS depth fuel _) fun _ ↦ trivial

theorem length_levelWordFast (κ k R : ℕ) (g : Array E) (p : ℕ) :
    (LeanVM.Prover.levelWordFast κ k R g p).length = 3 * 2 ^ k := by
  unfold LeanVM.Prover.levelWordFast LeanVM.Prover.levelWordFast.levelWordOf
  split
  · simp [List.length_flatMap, mul_comm]
  · simp [LeanVM.Protocol.Whir.Complete.levelWord, LeanVM.Protocol.Whir.Complete.laneCodes,
      LeanVM.Protocol.Whir.Complete.limbsOf, List.length_flatMap, Function.comp_def,
      List.sum_replicate, mul_comm]

/-- **The WHIR levels commit rows of at most `192` words** when every level folds at most `6`
variables (`3 · 2^fold` words a row). -/
theorem wordsLE_levelsA (μ : ℕ) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState) (Wt gt : Array E),
      (∀ l ∈ levels, l.fold ≤ 6) → WordsLE 192 (LeanVM.Prover.levelsA μ index levels s Wt gt) := by
  intro levels
  induction levels with
  | nil => intros; trivial
  | cons level rest ih =>
    intro index s Wt gt hf
    cases rest with
    | nil =>
      rw [LeanVM.Prover.levelsA]
      refine WordsLE.bind (wordsLE_foldRoundsA _ _ _ _ _) fun ⟨s', lf, Wt', g'⟩ ↦ ?_
      dsimp only
      refine WordsLE.bind (WordsLE.sendList _) fun _ ↦
        WordsLE.bind (WordsLE.ret' _) fun ⟨r, pd, tb⟩ ↦ ?_
      dsimp only
      refine WordsLE.bind WordsLE.grindS fun _ ↦ ?_
      refine WordsLE.bind (wordsLE_sampleQueriesS _ _ _) fun _ ↦ ?_
      refine WordsLE.bind WordsLE.sampleE fun _ ↦ ?_
      refine WordsLE.bind WordsLE.queryS fun _ ↦ ?_
      exact WordsLE.bind (wordsLE_roundA _ _ _) fun _ ↦ wordsLE_tailRoundsA _ _ _ _
    | cons next rest =>
      have hn : next.fold ≤ 6 := hf next (by simp)
      rw [LeanVM.Prover.levelsA]
      refine WordsLE.bind (wordsLE_foldRoundsA _ _ _ _ _) fun ⟨s', lf, Wt', g'⟩ ↦ ?_
      dsimp only
      refine WordsLE.bind (WordsLE.commitS fun p ↦ ?_) fun _ ↦ ?_
      · rw [length_levelWordFast]
        have : 2 ^ next.fold ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hn
        omega
      refine WordsLE.bind (WordsLE.sampleN _) fun _ ↦ WordsLE.bind (WordsLE.sendE _) fun _ ↦
        WordsLE.bind (wordsLE_roundA _ _ _) fun _ ↦ WordsLE.bind (WordsLE.ret' _)
          fun ⟨r, pd, tb⟩ ↦ ?_
      dsimp only
      refine WordsLE.bind WordsLE.grindS fun _ ↦ ?_
      refine WordsLE.bind (wordsLE_sampleQueriesS _ _ _) fun _ ↦ ?_
      refine WordsLE.bind WordsLE.sampleE fun _ ↦ ?_
      refine WordsLE.bind WordsLE.queryS fun _ ↦ ?_
      exact WordsLE.bind (wordsLE_roundA _ _ _) fun _ ↦
        ih _ _ _ _ fun l hl ↦ hf l (List.mem_cons_of_mem _ hl)

/-- **The honest opening script commits rows of at most `192` words** (`ladder_folds`). -/
theorem wordsLE_openingScript (L : PcsQuotient.Layout) (stack : Array K)
    (claims : List PcsQuotient.Claim) : WordsLE 192 (openingScript L stack claims) := by
  unfold openingScript
  refine WordsLE.bind WordsLE.sampleE fun c ↦ ?_
  split
  · trivial
  · rename_i config hc
    exact WordsLE.bind (wordsLE_roundA _ _ _) fun _ ↦
      wordsLE_levelsA _ _ _ _ _ _ (LeanVM.Rpm.ladder_folds _ _ _ hc)

/-! ## The prover's runner -/

/-- The runner's current node commits rows of at most `W` words. -/
def OWordsLE (W : ℕ) {β : Type} : Option (Script β) → Prop
  | none => True
  | some S => WordsLE W S

section OWords

variable {W : ℕ} {β : Type}

theorem oWordsLE_afterSend {S : Option (Script β)} (h : OWordsLE W S) :
    OWordsLE W (Script.afterSend S) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> trivial

theorem oWordsLE_afterSample (c : E) {S : Option (Script β)} (h : OWordsLE W S) :
    OWordsLE W (Script.afterSample c S) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> first | trivial | exact h c

theorem oWordsLE_afterGrind {S : Option (Script β)} (h : OWordsLE W S) :
    OWordsLE W (Script.afterGrind S) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> trivial

theorem oWordsLE_afterCommit {S : Option (Script β)} (h : OWordsLE W S) :
    OWordsLE W (Script.afterCommit S) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> first | trivial | exact h.2

theorem oWordsLE_afterQuery (rows : List (List K)) {S : Option (Script β)} (h : OWordsLE W S) :
    OWordsLE W (Script.afterQuery rows S) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> first | trivial | exact h rows

theorem length_wordOf_le {S : Option (Script β)} (h : OWordsLE W S) (p : ℕ) :
    (Script.wordOf S p).length ≤ W := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> first | exact Nat.zero_le _ | exact h.1 p

end OWords

/-- **The prover's factor**: what one quarter of the program's cost costs the prover, in blocks.
A commitment (two quarters) builds a tree of at most `13 · 2^height` blocks and absorbs its root;
a proof of work (five quarters) searches `fuel` nonces, two permutations each, then steps once. -/
def blockFactor (height fuel : ℕ) : ℕ := 13 * 2 ^ height + 2 * fuel + 2

/-- **The prover's runner**, against a program of cost `n` quarters at height `height`, from a
script whose commitments have rows of at most `192` words, makes at most
`n · blockFactor height fuel` block calls (mumbai's `isTotalQueryBound_proveFromM`, weighted). -/
theorem cost_runFromWithHash (fuel height : ℕ) {α β : Type} :
    ∀ (P : Prog α) (S : Option (Script β)) (sp : Sponge) (cs : List Tree) (n : ℕ)
      (Q : α → Prop), P.Costs height n Q → OWordsLE 192 S →
      QC (LeanVM.Prover.runFromWithHash callKeccak256 callKeccakF1600 fuel P S sp cs)
        (n * blockFactor height fuel) := by
  intro P
  have hF : 1 ≤ blockFactor height fuel := by unfold blockFactor; omega
  induction P with
  | ret a => intros; exact qc_pure _ _
  | fail => intros; exact qc_pure _ _
  | read k ih =>
    intro S sp cs n Q hp hS
    simp only [LeanVM.Prover.runFromWithHash]
    refine (qc_absorb _ _ _).bind_le (fun sp' ↦ (ih _ _ _ cs (n - 1) Q (hp.2 _)
      (oWordsLE_afterSend hS)).bind_le (fun _ ↦ qc_pure _ 0) le_rfl) ?_
    have h1 := hp.1
    generalize blockFactor height fuel = F at *
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.succ_mul]
    omega
  | sample k ih =>
    intro S sp cs n Q hp hS
    simp only [LeanVM.Prover.runFromWithHash]
    refine (qc_squeeze _).bind_le (fun r ↦ ih _ _ _ cs (n - 4) Q (hp.2 _)
      (oWordsLE_afterSample _ hS)) ?_
    have h1 := hp.1
    generalize blockFactor height fuel = F at *
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 4 := ⟨n - 4, by omega⟩
    rw [Nat.add_sub_cancel, Nat.add_mul]
    omega
  | grind bits k ih =>
    intro S sp cs n Q hp hS
    simp only [LeanVM.Prover.runFromWithHash]
    refine (qc_findNonceM _ _ _).bind_le (b := 2 + ((n - 5) * blockFactor height fuel + 0))
      (fun o ↦ ?_) ?_
    · split
      · exact qc_pure _ _
      · exact (qc_powStepM _ _).bind_le (fun r ↦ (ih _ _ cs (n - 5) Q hp.2
          (oWordsLE_afterGrind hS)).bind_le (fun _ ↦ qc_pure _ 0) le_rfl) le_rfl
    · have h1 := hp.1
      have hfuel : 2 * fuel + 2 ≤ blockFactor height fuel := by unfold blockFactor; omega
      generalize blockFactor height fuel = F at *
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 5 := ⟨n - 5, by omega⟩
      rw [Nat.add_sub_cancel, Nat.add_mul]
      omega
  | commit ht w k ih =>
    intro S sp cs n Q hp hS
    simp only [LeanVM.Prover.runFromWithHash]
    refine (qc_buildTree ht _ 12 fun p ↦ ?_).bind_le (b := 1 + (1 + ((n - 2) *
      blockFactor height fuel + 0))) (fun tree ↦ (qc_absorb _ _ _).bind_le (fun _ ↦
        (qc_absorb _ _ _).bind_le (fun _ ↦ (ih _ _ _ (n - 2) Q hp.2.2
          (oWordsLE_afterCommit hS)).bind_le (fun _ ↦ qc_pure _ 0) le_rfl) le_rfl) le_rfl) ?_
    · have := length_wordOf_le hS p
      omega
    · have h1 := hp.2.1
      have h2 : 2 ^ ht ≤ 2 ^ height := Nat.pow_le_pow_right (by norm_num) hp.1
      have htree : 13 * 2 ^ height + 2 ≤ blockFactor height fuel := by unfold blockFactor; omega
      generalize blockFactor height fuel = F at *
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
      rw [Nat.add_sub_cancel, Nat.add_mul n' 2]
      omega
  | query i ps k ih =>
    intro S sp cs n Q hp hS
    simp only [LeanVM.Prover.runFromWithHash]
    split
    · exact qc_pure _ _
    · exact (ih _ _ _ cs (n - Prog.openCost height ps.length) Q (hp.2 _)
        (oWordsLE_afterQuery _ hS)).bind_le (fun _ ↦ qc_pure _ 0)
          (by rw [Nat.add_zero]; exact Nat.mul_le_mul_right _ (Nat.sub_le _ _))

/-! ## The verifier's run -/

theorem qc_climb : ∀ (node : Digest) (q : ℕ) (ss : List Digest),
    QC (climbWithHash callKeccak256 node q ss) ss.length
  | _, _, [] => qc_pure _ _
  | node, q, s :: ss => by
    simp only [climbWithHash, List.length_cons]
    have hn (a b : Digest) : QC (callKeccak256 (digestBytes a ++ digestBytes b)) 1 :=
      qc_H_le (by rw [List.length_append, length_digestBytes, length_digestBytes]; omega)
    rw [Nat.add_comm]
    split <;> exact (hn _ _).bind fun _ ↦ qc_climb _ _ ss

/-- One opening: a leaf of at most `192` words (`12` blocks) and its path. -/
theorem qc_openOne (root : Digest) (height width q : ℕ) (o : Compile.Opening)
    (hw : width ≤ 192) :
    QC (openOneWithHash callKeccak256 root height width q o) (12 + height) := by
  unfold openOneWithHash
  split
  · rename_i h
    refine (qc_H_le (k := 12) ?_).bind_le (fun _ ↦ (qc_climb _ _ _).bind_le
      (fun _ ↦ qc_pure _ 0) le_rfl) (by rw [h.2]; omega)
    rw [length_flatMap_kBytes, h.1]
    omega
  · exact qc_pure _ _

theorem qc_openAll (root : Digest) (height width : ℕ) (hw : width ≤ 192) :
    ∀ (ps : List ℕ) (os : List Compile.Opening),
      QC (openAllWithHash callKeccak256 root height width ps os) (ps.length * (12 + height))
  | [], _ => qc_pure _ _
  | _ :: _, [] => qc_pure _ _
  | q :: qs, o :: os => by
    simp only [openAllWithHash, List.length_cons]
    refine (qc_openOne root height width q o hw).bind_le (b := qs.length * (12 + height))
      (fun b ↦ ?_) (by rw [Nat.succ_mul]; omega)
    split
    · exact (qc_openAll root height width hw qs os).bind_le (fun _ ↦ qc_pure _ 0) le_rfl
    · exact qc_pure _ _

/-- **The verifier's run**, of a program of cost `n` quarters at height `height` whose
commitments have width at most `192`, from roots of height at most `12 · height` and width at
most `192`, makes at most `3 · n` block calls: a quarter costs at most `3` blocks (an absorption
`1` of its `1`, an opening of `k` positions `k · (12 + 12 · height)` of its
`4 · k · (1 + height)`). -/
theorem cost_runWithHash (height : ℕ) {α : Type} :
    ∀ (P : Prog α) (s : ProgState) (n : ℕ) (Q : α → Prop), P.Costs height n Q →
      LeanVM.Rpm.WidthsLE LeanVM.Rpm.maxWidth P →
      (∀ r ∈ s.roots, r.2.1 ≤ 12 * height ∧ r.2.2 ≤ 192) →
      QC (runWithHash callKeccak256 callKeccakF1600 P s) (3 * n)
  | .ret _, _, _, _, _, _, _ => qc_pure _ _
  | .fail, _, _, _, _, _, _ => qc_pure _ _
  | .read k, s, n, Q, hp, hW, hr => by
    simp only [runWithHash]
    split
    · exact qc_pure _ _
    · exact (qc_absorb _ _ _).bind_le (fun sp ↦ cost_runWithHash height _ _ (n - 1) Q (hp.2 _)
        (hW _) hr) (by have := hp.1; omega)
  | .sample k, s, n, Q, hp, hW, hr => by
    simp only [runWithHash]
    refine (qc_squeeze _).bind_le (b := 3 * (n - 4)) (fun r ↦ ?_) (by have := hp.1; omega)
    obtain ⟨c, sp⟩ := r
    exact cost_runWithHash height _ _ (n - 4) Q (hp.2 _) (hW _) hr
  | .grind bits k, s, n, Q, hp, hW, hr => by
    simp only [runWithHash]
    split
    · exact qc_pure _ _
    · refine (qc_absorb _ _ _).bind_le (fun sp ↦ (qc_squeeze _).bind_le (b := 3 * (n - 5))
        (fun r ↦ ?_) le_rfl) (by have := hp.1; omega)
      obtain ⟨c, sp'⟩ := r
      dsimp only
      split
      · exact cost_runWithHash height _ _ (n - 5) Q hp.2 hW hr
      · exact qc_pure _ _
  | .commit ht w k, s, n, Q, hp, hW, hr => by
    simp only [runWithHash]
    split
    · refine (qc_absorb _ _ _).bind_le (fun sp ↦ (qc_absorb _ _ _).bind_le (b := 3 * (n - 2))
        (fun sp' ↦ ?_) le_rfl) (by have := hp.2.1; omega)
      split
      · refine cost_runWithHash height _ _ (n - 2) Q hp.2.2 hW.2 fun r hr' ↦ ?_
        rcases List.mem_append.mp hr' with h | h
        · exact hr r h
        · simp only [List.mem_singleton] at h
          subst h
          exact ⟨by have := hp.1; dsimp only; omega, hW.1⟩
      · exact qc_pure _ _
    · exact qc_pure _ _
  | .query i ps k, s, n, Q, hp, hW, hr => by
    simp only [runWithHash]
    split
    · exact qc_pure _ _
    · next root h' w hi =>
      have hrw := hr _ (List.mem_of_getElem? hi)
      refine (qc_openAll root h' w hrw.2 ps s.openings).bind_le
        (b := 3 * (n - Prog.openCost height ps.length)) (fun o ↦ ?_) ?_
      · split
        · exact cost_runWithHash height _ _ _ Q (hp.2 _) (hW _) hr
        · exact qc_pure _ _
      · have h1 := hp.1
        have hm : ps.length * h' ≤ ps.length * (12 * height) := Nat.mul_le_mul_left _ hrw.1
        have e1 : ps.length * (12 + h') = 12 * ps.length + ps.length * h' := by ring
        have e2 : ps.length * (12 * height) = 12 * (ps.length * height) := by ring
        have e3 : Prog.openCost height ps.length = 4 * ps.length + 4 * (ps.length * height) := by
          unfold Prog.openCost; ring
        rw [e1]
        rw [e2] at hm
        rw [e3] at h1 ⊢
        omega

/-- The stacked opening's cost: the batching challenge and WHIR, at height `26` (mumbai's
`costs_verifyStackedOpening` with `ladder_cost`). -/
theorem costs_vso (logN R : ℕ) (claims : List StackClaim) :
    Prog.Costs costHeight (verifyStackedOpening logN R claims) (4 + (2 + whirBound))
      fun _ ↦ True :=
  costs_verifyStackedOpening (height := costHeight) logN R claims whirBound fun levels h ↦
    ⟨(ladder_cost _ _ levels h).1, (ladder_cost _ _ levels h).2.2.1,
      (ladder_cost _ _ levels h).2.2.2⟩

/-- The stacked opening's commitments have width at most `192` (mumbai's
`widthsLE_verifyWhir`). -/
theorem widthsLE_vso (logN R : ℕ) (claims : List StackClaim) :
    LeanVM.Rpm.WidthsLE LeanVM.Rpm.maxWidth (verifyStackedOpening logN R claims) := by
  rw [verifyStackedOpening_eq_target]
  exact LeanVM.Rpm.WidthsLE.seq (LeanVM.Rpm.WidthsLE.of_moves (g := fun _ ↦ True)
    LeanVM.Protocol.EndToEnd.Sound.MovesOK.sampleE) fun _ ↦ LeanVM.Rpm.widthsLE_verifyWhir _ _ _ _

/-! ## The openings' IVs -/

theorem length_u64Bytes (n : ℕ) : (u64Bytes n).length = 8 := by
  simp [u64Bytes, LeanVM.Rpm.wordBytes_len]

/-- `opening::verify`'s prefix: `76` bytes. -/
theorem length_openingPre (L : PcsQuotient.Layout) :
    (openingLabel ++ u64Bytes openingVersion ++ digestBytes L.id ++ u64Bytes L.logN ++
      u64Bytes logInvRate).length = 76 := by
  have h20 : openingLabel.length = 20 := by decide +kernel
  simp only [List.length_append, length_u64Bytes, length_digestBytes, h20]

theorem length_flatMap_eBytes (l : List E) : (l.flatMap eBytes).length = 24 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    simp only [eBytes, kBytes, List.length_append, LeanVM.Rpm.wordBytes_len]
    ring

theorem length_claimBytes_le (v : ℕ) :
    ∀ claims : List PcsQuotient.Claim, (∀ c ∈ claims, c.point.length ≤ v) →
      (claimBytes claims).length ≤ 24 * (claims.length * (v + 1))
  | [], _ => by simp [claimBytes]
  | c :: cs, h => by
    have ih := length_claimBytes_le v cs fun c' hc' ↦ h c' (List.mem_cons_of_mem _ hc')
    have hc := h c List.mem_cons_self
    simp only [claimBytes, List.flatMap_cons, List.length_append, length_flatMap_eBytes,
      List.length_cons, List.length_nil] at ih ⊢
    nlinarith

/-- The opening's sponge: the IV's hash, of the prefix and the claims, and one permutation. -/
theorem qc_openingSpongeWithH (L : PcsQuotient.Layout) (claims : List PcsQuotient.Claim) (v B : ℕ)
    (hv : ∀ c ∈ claims, c.point.length ≤ v) (hB : 76 + 24 * (claims.length * (v + 1)) < 136 * B) :
    QC (openingSpongeWithH callKeccak256 callKeccakF1600 L claims) (B + 1) := by
  unfold openingSpongeWithH
  refine (qc_H_le (k := B) ?_).bind_le (fun iv ↦ (qc_F _).bind_le (fun _ ↦ qc_pure _ 0) le_rfl)
    le_rfl
  rw [List.length_append, length_openingPre]
  have := length_claimBytes_le v claims hv
  omega

/-- The verifier's cost of one opening, besides its IV. -/
def vOpen : ℕ := 3 + 3 * (4 + (2 + whirBound))

/-- **The verifier's opening**: its IV (at most `B` blocks), its seed's permutation, the root's two
absorptions and the run of the stacked opening, from the root at its height. -/
theorem cost_openingWithH (L : PcsQuotient.Layout) (root : Digest)
    (claims : List PcsQuotient.Claim) (proof : Compile.Proof)
    (hL : L.logN - laneFold + logInvRate ≤ 12 * costHeight) (B : ℕ)
    (hB : 76 + 24 * (claims.length * (L.vars + 1)) < 136 * B) :
    QC (openingWithH callKeccak256 callKeccakF1600 L root claims proof) (B + vOpen) := by
  unfold openingWithH
  split
  · rename_i hc
    have hv : ∀ c ∈ claims, c.point.length ≤ L.vars := fun c hc' ↦ by
      have := hc.2
      rw [List.all_eq_true] at this
      exact le_of_eq (of_decide_eq_true (this c hc'))
    split
    · refine (qc_openingSpongeWithH L claims L.vars B hv hB).bind_le (fun sp ↦
        (qc_absorb _ _ _).bind_le (fun sp ↦ (qc_absorb _ _ _).bind_le
          (b := 3 * (4 + (2 + whirBound))) (fun sp ↦ ?_) le_rfl) le_rfl) (by unfold vOpen; omega)
      split
      · split
        · refine (cost_runWithHash costHeight _ _ _ _ (costs_vso _ _ _) (widthsLE_vso _ _ _)
            ?_).bind_le (b := 0) (fun z ↦ ?_) (by omega)
          · intro r hr
            simp only [List.mem_singleton] at hr
            subst hr
            exact ⟨hL, show 2 ^ laneFold ≤ 192 by decide⟩
          · split <;> exact qc_pure _ _
        · exact qc_pure _ _
      · exact qc_pure _ _
    · exact qc_pure _ _
  · exact qc_pure _ _

/-! ## The reduction -/

/-- The claims' points have at most `m + 6` coordinates. -/
def ClaimsLen (m : ℕ) (cl : Claims) : Prop :=
  cl.witness.point.length ≤ m + 6 ∧ cl.wiring.point.length ≤ m + 6 ∧
    cl.quotient.point.length ≤ m + 6 ∧ cl.sum.point.length ≤ m + 6

/-- What the reduction may return: claims whose points have at most `m + 6` coordinates. -/
def RedOK (logRows : ℕ) (o : Option Reduced) : Prop :=
  ∀ r, o = some r → ClaimsLen (cellVars logRows) r.claims

/-- **The claims' points**: the witness claim's `m + 1` coordinates, the wiring's `m`, the
quotient's and the sum's `m + 6`. -/
theorem claimsAt_len {logRows : ℕ} {stmt : Statement} {α β γ t ρ : E} {a : Vector E 4} {next : E}
    {cl : Claims} (h : claimsAt logRows stmt α β γ t ρ a next = some cl) :
    ClaimsLen (cellVars logRows) cl := by
  unfold claimsAt at h
  extract_lets m w wAt theta cell x y c v gate b gamma2 gammas outside publicWeight target tau
    rows d dNext product copies denominators at h
  by_cases hd : (denominators.any fun x ↦ decide (x = 0)) = true
  · simp [hd] at h
  simp only [hd] at h
  rename_i inv u copyInverse rowsInverse middle wiringScale quotientScale rho2 opened identities
  obtain rfl := (Option.some.inj h).symm
  have hu : u.length = m + 2 := by simp [u]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [sumPoint, hu, m]
  omega

theorem redOK_none (logRows : ℕ) : RedOK logRows none := fun _ h ↦ by cases h

theorem redOK_map {logRows : ℕ} {stmt : Statement} {α β γ t ρ : E} {a : Vector E 4} {next : E}
    (wr qr : Digest) :
    RedOK logRows ((claimsAt logRows stmt α β γ t ρ a next).map
      fun claims ↦ (⟨wr, qr, claims⟩ : Reduced)) := by
  intro r hr
  rcases hc : claimsAt logRows stmt α β γ t ρ a next with _ | cl
  · rw [hc] at hr
    cases hr
  · rw [hc] at hr
    cases hr
    exact claimsAt_len hc

theorem length_flatMap_scalarBytes (l : List E) :
    (l.flatMap scalarBytes).length = 32 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, ih, length_scalarBytes, List.length_cons]
    ring

theorem foldl_absorb (l : List E) (c : Chain) :
    l.foldl Chain.absorb c = ⟨c.state, c.pending ++ l⟩ := by
  induction l generalizing c with
  | nil => simp
  | cons a l ih => simp [ih, Chain.absorb]

/-- **The reduction's transcript**, then a continuation charged only at what the reduction may
return: the label (`112` bytes), the four challenges after at most two scalars, and `ρ` after
the five values (`192` bytes, two blocks). -/
theorem qc_reduceWithH_bind {β : Type} (logRows : ℕ) (ir : Digest) (stmt : Statement)
    (p : ReductionProof) (f : Option Reduced → OracleComp KeccakCalls β) (b : ℕ)
    (hf : ∀ o, RedOK logRows o → QC (f o) b) :
    QC (reduceWithH callKeccak256 logRows ir stmt p >>= f) (7 + b) := by
  by_cases hs : Supported logRows
  · simp only [reduceWithH, hs, not_true_eq_false, ↓reduceIte, startWithH, squeezeWithH,
      bind_assoc, pure_bind]
    refine (qc_H_le (k := 1) ?_).bind_le (b := 6 + b) (fun s₀ ↦ ?_) (by omega)
    · rw [length_label]; omega
    split
    · rw [pure_bind]
      exact (hf none (redOK_none _)).mono (by omega)
    simp only [bind_assoc]
    refine (qc_H_le (k := 1) ?_).bind_le (b := 5 + b) (fun s₁ ↦ ?_) (by omega)
    · simp [Chain.absorb, length_digestBytes, length_scalarBytes]
    refine (qc_H_le (k := 1) ?_).bind_le (b := 4 + b) (fun s₂ ↦ ?_) (by omega)
    · simp [length_digestBytes]
    refine (qc_H_le (k := 1) ?_).bind_le (b := 3 + b) (fun s₃ ↦ ?_) (by omega)
    · simp [length_digestBytes]
    split
    · rw [pure_bind]
      exact (hf none (redOK_none _)).mono (by omega)
    simp only [bind_assoc, pure_bind]
    refine (qc_H_le (k := 1) ?_).bind_le (b := 2 + b) (fun s₄ ↦ ?_) (by omega)
    · simp [Chain.absorb, length_digestBytes, length_scalarBytes]
    refine (qc_H_le (k := 2) ?_).bind_le (b := b) (fun s₅ ↦ ?_) (by omega)
    · simp only [foldl_absorb, Chain.absorb, List.nil_append, List.length_append,
        length_digestBytes, length_flatMap_scalarBytes, Vector.length_toList, List.length_cons,
        List.length_nil]
      omega
    exact hf _ (redOK_map _ _)
  · simp only [reduceWithH, hs, not_false_eq_true, ↓reduceIte, pure_bind]
    exact (hf none (redOK_none _)).mono (by omega)

/-! ## The openings -/

/-- **The prover's opening**: its IV (at most `B` blocks), its seed's permutation, the root's two
absorptions, and the runner on the stacked opening at height `26` from the honest script. -/
theorem cost_proveOpeningWithH (fuel : ℕ) (L : PcsQuotient.Layout) (tree : Tree)
    (stack : Array K) (claims : List PcsQuotient.Claim) (v B : ℕ)
    (hv : ∀ c ∈ claims, c.point.length ≤ v) (hB : 76 + 24 * (claims.length * (v + 1)) < 136 * B) :
    QC (proveOpeningWithH callKeccak256 callKeccakF1600 fuel L tree stack claims)
      (B + 3 + (4 + (2 + whirBound)) * blockFactor costHeight fuel) := by
  unfold proveOpeningWithH
  split
  refine (qc_openingSpongeWithH L claims v B hv hB).bind_le (fun sp ↦ (qc_absorb _ _ _).bind_le
    (fun sp ↦ (qc_absorb _ _ _).bind_le (fun sp ↦ (cost_runFromWithHash fuel costHeight _ _ sp
      [tree] _ _ (costs_vso _ _ _) (wordsLE_openingScript L stack claims)).bind_le
        (fun _ ↦ qc_pure _ 0) le_rfl) le_rfl) le_rfl) (by omega)

/-- The prover's cost of the reduction and the three openings. -/
def proverCost (fuel : ℕ) : ℕ :=
  7 + 3 * (12 + 3 + (4 + (2 + whirBound)) * blockFactor costHeight fuel)

/-- **The prover's last stretch**: the reduction, then the three openings, their IVs at most
`12` blocks (points of at most `cellVars logRows + 6 ≤ 30` coordinates). -/
theorem cost_proverTail (circuit : Circuit) (hr : cellVars circuit.logRows ≤ 24) (fuel : ℕ)
    (stmt : Statement) (a : AuxA) (bq : Tree × Array K) (t : E) :
    QC (proverTail circuit fuel stmt a bq t) (proverCost fuel) := by
  unfold proverTail proverCost
  refine qc_reduceWithH_bind _ _ _ _ _ _ fun o ho ↦ ?_
  split
  · exact qc_pure _ _
  · rename_i r
    obtain ⟨h1, -, h3, h4⟩ := ho r rfl
    have hB (cs : List PcsQuotient.Claim) (hj : cs.length ≤ 2) :
        76 + 24 * (cs.length * (cellVars circuit.logRows + 6 + 1)) < 136 * 12 := by
      have : cs.length * (cellVars circuit.logRows + 6 + 1) ≤ 2 * 31 :=
        Nat.mul_le_mul hj (by omega)
      omega
    refine (cost_proveOpeningWithH _ _ _ _ _ (cellVars circuit.logRows + 6) 12 ?_ ?_).bind_le
      (b := 2 * (12 + 3 + (4 + (2 + whirBound)) * blockFactor costHeight fuel)) (fun o₁ ↦ ?_)
      (by omega)
    · intro c hc
      simp only [List.mem_singleton] at hc
      subst hc
      exact h1
    · exact hB _ (by simp)
    split
    · refine (cost_proveOpeningWithH _ _ _ _ _ (cellVars circuit.logRows + 6) 12 ?_ ?_).bind_le
          (b := 12 + 3 + (4 + (2 + whirBound)) * blockFactor costHeight fuel) (fun o₂ ↦ ?_)
          (by omega)
      · intro c hc
        simp only [List.mem_singleton] at hc
        subst hc
        exact (ho r rfl).2.1
      · exact hB _ (by simp)
      split
      · refine (cost_proveOpeningWithH _ _ _ _ _ (cellVars circuit.logRows + 6) 12 ?_ ?_).bind_le
          (b := 0) (fun o₃ ↦ ?_) (by omega)
        · intro c hc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl
          · exact h3
          · exact h4
        · exact hB _ (by simp)
        split <;> exact qc_pure _ _
      · exact qc_pure _ _
    · exact qc_pure _ _

theorem witnessLayout_vars (r : ℕ) : (witnessLayout r).vars = cellVars r + 1 := rfl
theorem witnessLayout_logN (r : ℕ) : (witnessLayout r).logN = cellVars r + 1 := rfl
theorem wiringLayout_vars (r : ℕ) : (wiringLayout r).vars = cellVars r := rfl
theorem wiringLayout_logN (r : ℕ) : (wiringLayout r).logN = cellVars r := rfl
theorem quotientLayout_vars (r : ℕ) : (quotientLayout r).vars = cellVars r + 6 := rfl
theorem quotientLayout_logN (r : ℕ) : (quotientLayout r).logN = cellVars r + 4 := rfl

/-- The verifier's cost of the reduction and the three openings. -/
def verifierCost : ℕ := 7 + 3 * (12 + vOpen)

/-- **The verifier**: the reduction, then the three openings, their IVs at most `12` blocks and
their roots of height at most `cellVars logRows - 1 ≤ 23`. -/
theorem cost_verifyWithH (logRows : ℕ) (hr : cellVars logRows ≤ 24) (ir : Digest)
    (stmt : Statement) (proof : PcsQuotient.Proof) :
    QC (verifyWithH callKeccak256 callKeccakF1600 logRows ir stmt proof) verifierCost := by
  unfold verifyWithH verifierCost
  have hh : costHeight = 26 := rfl
  refine qc_reduceWithH_bind _ _ _ _ _ _ fun o _ ↦ ?_
  split
  · exact qc_pure _ _
  · refine (cost_openingWithH _ _ _ _ ?_ 12 ?_).bind_le (b := 2 * (12 + vOpen)) (fun b₁ ↦ ?_)
      (by omega)
    · rw [witnessLayout_logN, hh, laneFold, logInvRate]; omega
    · rw [witnessLayout_vars, List.length_singleton]; omega
    split
    · exact qc_pure _ _
    · refine (cost_openingWithH _ _ _ _ ?_ 12 ?_).bind_le (b := 12 + vOpen) (fun b₂ ↦ ?_)
        (by omega)
      · rw [wiringLayout_logN, hh, laneFold, logInvRate]; omega
      · rw [wiringLayout_vars, List.length_singleton]; omega
      split
      · exact qc_pure _ _
      · refine cost_openingWithH _ _ _ _ ?_ 12 ?_
        · rw [quotientLayout_logN, hh, laneFold, logInvRate]; omega
        · rw [quotientLayout_vars]; simp only [List.length_cons, List.length_nil]; omega

/-! ## The stages -/

/-- The block cost of a table's tree on `2^μ` words. -/
def treeCost (μ : ℕ) : ℕ := 5 * 2 ^ (μ - 6 + 1)

/-- **Stage A**: the setup, the index and witness trees, the label's hash. -/
theorem cost_stageAG (setup : OracleComp KeccakCalls Digest) (Cs : ℕ) (hs : QC setup Cs)
    (circuit : Circuit) (cells : Array K) (masks : Masks) (witnessPad : Padding)
    (stmt : Statement) :
    QC (stageAG setup circuit cells masks witnessPad stmt)
      (Cs + (treeCost (cellVars circuit.logRows) + (treeCost (cellVars circuit.logRows + 1) +
        (1 + 0)))) := by
  unfold stageAG
  exact hs.bind fun _ ↦ (qc_commitWithH _ _).bind fun _ ↦ (qc_commitWithH _ _).bind fun _ ↦
    (qc_H_le (k := 1) (by rw [length_label]; omega)).bind fun _ ↦ qc_pure _ 0

/-- **Stage B**: the quotient table's tree. -/
theorem cost_stageBG (circuit : Circuit) (cells : Array K) (quotientPad : Padding) (a : AuxA)
    (s₁ s₂ s₃ : Digest) :
    QC (stageBG circuit cells quotientPad a s₁ s₂ s₃)
      (treeCost (cellVars circuit.logRows + 4) + 0) := by
  unfold stageBG
  exact (qc_commitWithH _ _).bind fun _ ↦ qc_pure _ 0

/-- **Stage C**: the prover's last stretch, then the verifier. -/
theorem cost_stageCG (circuit : Circuit) (hr : cellVars circuit.logRows ≤ 24) (fuel vLogRows : ℕ)
    (hv : cellVars vLogRows ≤ 24) (stmt : Statement) (a : AuxA) (bq : Tree × Array K)
    (s₁ s₂ s₃ s₄ : Digest) :
    QC (stageCG circuit fuel vLogRows stmt a bq s₁ s₂ s₃ s₄) (proverCost fuel + verifierCost) := by
  unfold stageCG
  refine (cost_proverTail circuit hr fuel stmt a bq _).bind fun o ↦ ?_
  split
  · exact qc_pure _ _
  · exact cost_verifyWithH _ hv _ _ _

/-- **The chain's shape**: the stages, and the chain's four hashes (`96` and `32` bytes). -/
theorem cost_staged {α β γ : Type} (chal : Digest → E)
    (A : OracleComp KeccakCalls (α × Digest × (E × E)))
    (B : α → Digest → Digest → Digest → OracleComp KeccakCalls (β × (E × E)))
    (C : α → β → Digest → Digest → Digest → Digest → OracleComp KeccakCalls γ) (a b c : ℕ)
    (hA : QC A a) (hB : ∀ x s₁ s₂ s₃, QC (B x s₁ s₂ s₃) b)
    (hC : ∀ x y s₁ s₂ s₃ s₄, QC (C x y s₁ s₂ s₃ s₄) c) :
    QC (staged chal A B C) (a + (1 + (1 + (1 + (b + (1 + (c + 0))))))) := by
  unfold staged
  have h96 (s : Digest) (r : E × E) : QC (callKeccak256 (chainIn s r)) 1 :=
    qc_H_le (by rw [length_chainIn]; omega)
  have h32 (s : Digest) : QC (callKeccak256 (digestBytes s)) 1 :=
    qc_H_le (by rw [length_digestBytes]; omega)
  exact hA.bind fun x ↦ (h96 _ _).bind fun s₁ ↦ (h32 _).bind fun s₂ ↦ (h32 _).bind fun s₃ ↦
    (hB _ _ _ _).bind fun y ↦ (h96 _ _).bind fun s₄ ↦ (hC _ _ _ _ _ _).bind fun _ ↦ qc_pure _ 0

/-- **The staged run, for any setup, circuit and cells**: the setup's cost, the index, witness
and quotient trees, the chain's six hashes, the prover's reduction and openings, and the
verifier. -/
theorem cost_stagedRunG (setup : OracleComp KeccakCalls Digest) (Cs : ℕ) (hs : QC setup Cs)
    (circuit : Circuit) (hr : cellVars circuit.logRows ≤ 24) (cells : Array K) (masks : Masks)
    (witnessPad quotientPad : Padding) (fuel vLogRows : ℕ) (hv : cellVars vLogRows ≤ 24)
    (stmt : Statement) :
    QC (stagedRunG setup circuit cells masks witnessPad quotientPad fuel vLogRows stmt)
      (Cs + treeCost (cellVars circuit.logRows) + treeCost (cellVars circuit.logRows + 1) +
        treeCost (cellVars circuit.logRows + 4) + 6 + proverCost fuel + verifierCost) := by
  unfold stagedRunG
  refine (cost_staged _ _ _ _ _ _ _ (cost_stageAG setup Cs hs circuit cells masks witnessPad stmt)
    (fun a s₁ s₂ s₃ ↦ cost_stageBG circuit cells quotientPad a s₁ s₂ s₃)
    (fun a bq s₁ s₂ s₃ s₄ ↦ cost_stageCG circuit hr fuel vLogRows hv stmt a bq s₁ s₂ s₃ s₄)).mono ?_
  omega

/-! ## The deployed staged run -/

/-- The setup: the index tree on `2^24` words. -/
theorem cost_setupWithH : QC (setupWithH callKeccak256) (treeCost 24) := by
  unfold setupWithH
  exact (qc_commitWithH _ _).bind_le (fun _ ↦ qc_pure _ 0) (by rfl)

end Cost

open Cost in
/-- **The deployed staged run makes at most `2^48` block calls** (fewer than `2^47`): the third
field of `Staged.Holds`, the hypothesis `hcost` of `completeness_deployed_cost_rej` and
`completeness_deployed_final`. The circuit's size is read off its record (`rfl`); nothing of the
deployed circuit is evaluated. -/
theorem hcost_deployed :
    ∀ stmt w coins, Common.QueryCostAtMost (stagedRun stmt w coins) hashBlocks (2 ^ 48) := by
  intro stmt w coins
  have hm : (membership logRows).logRows = 22 := rfl
  refine (cost_stagedRunG _ _ cost_setupWithH (membership logRows) (by rw [hm]; decide)
    (cellsOf w) coins.1 coins.2.1 coins.2.2 nonceFuel logRows (by decide) stmt).mono ?_
  rw [hm]
  norm_num [treeCost, proverCost, verifierCost, vOpen, blockFactor, whirBound, costHeight,
    nonceFuel, cellVars]

end E2ECompleteness

/-- info: 'E2ECompleteness.hcost_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.hcost_deployed
