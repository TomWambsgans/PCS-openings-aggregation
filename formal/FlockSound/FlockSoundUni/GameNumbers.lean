-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The numbers are `formal/UniStatement`'s
-- (`reference`, `workloads`, `layoutsOf`, `layoutWords`, `programIv`); the hypotheses they discharge are
-- `formal/UniSound`'s (`UniShapes`, `LayoutVarsSmall`, `UniIv`, `fsLayer_of_bridges`'s `hnQ`, `hnv`).
import UniSound.FsCouple
import FlockSoundUni.PendingShape

/-!
# The deployment's numbers

The Fiat–Shamir layer (`UniSound.fsLayer_of_bridges`) and the end theorem
(`uniKnowledgeSoundness_flock`) take numeric facts about the deployment as hypotheses. Here they are
proved for the reference deployment (`UniStatement.reference`, 1,000 signatures), and the layout facts
for every measured workload but `xmss32`:

* **`UniShapes`** (the five layout words name `24 … 28` variables) and **`LayoutVarsSmall`**: at the
  reference, `C1`, `C2` and the setup have `27`, `27` and `24` variables (`layoutVars_reference`), and
  `A0`, `B0` have `28` (`matrixVars`), so the five words name `[27, 27, 24, 28, 28]`
  (`wv_reference`; `uniShapes_reference`, `layoutVarsSmall_reference`). The measured workloads'
  stacks have `[22, 24, 24]`, `[24, 25, 24]`, `[26, 27, 24]`, `[27, 27, 24]`, `[27, 28, 24]`,
  `[28, 28, 24]` variables (`layoutVars_workloads`): `xmss128`, `xmss400`, `xmss1000`, `xmss1290` and
  `xmss2000` satisfy both facts (`uniShapes_workloads`); **`xmss32` does not**: its `C1` has `22`
  variables (`not_uniShapes_xmss32`), below the large WHIR shapes' `24`, so a deployment at that shape
  needs a WHIR shape this proof does not have.
* **`UniIv`** for the reference program IV (`32` bytes): `uniIv_of`.
* **`hnQ`**: the main line's chain makes `41 + 2κ + V` queries (`nQ_flock`, for every number of values
  at `t`), at most `2^10` for `2κ + V ≤ 983` (`hnQ_flock`; `κ ≤ 32`, `V ≤ 64` in `hnQ_flock'`; `86` at
  the reference). **`hnv`**: every round reads at most `2^30` scalars, for every `κ` and `V`
  (`hnv_flock`; Flock's rounds at most `64`, the values at `t` at most `122`, `valsCount_le`, an upper
  bound: which fingerprints are sent depends on `E` coefficients, so `valsCount` is not evaluated).
* **At the reference**: `κ = 18` (`hκ_reference`), `V = 27` (`varsOf_reference`). Beyond the five facts:
  Flock's round errors are at most `(15 + κ)/|E|` (`err_flock_le`, so `hFl_flock`), and with them
  `fsLayer_reference` (the Fiat–Shamir layer from the three bridge facts) and
  `uniKnowledgeSoundness_reference` (the end theorem with `hκ`, `LayoutVarsSmall`, `hFl` and the
  Fiat–Shamir layer's numbers discharged).

**How the stacks' variables are computed** without evaluating a layout in the kernel (`List.mergeSort`
is well-founded recursion, and `E`'s arithmetic and equality do not reduce there): a stack's variables
are `max (log2Ceil (max W 2)) 15` of the words `W` its columns fill (`stackLayout_vars`; the sort only
permutes the pieces). `C1`'s and the setup's words are a closed sum of the shape's numbers (`c1Cols`,
`setupCols`; `102,891,520` and `10,485,760` at the reference). `C2`'s are `6 · 2^h + 3`, the
constraint quotient's chunks and each used heap block's leaf quotient's chunks (`c2Words`,
`heap_blocks_words`: the heap's sort permutes the used blocks, the unused ones have no quotient). A
table's leaf degree reads its flushes' degrees (`tableDegrees`), which test `E` coefficients against
zero; they are bounded instead, below by `1 + #flushes` (every tuple has degree at least `1`) and
above by the degrees of the monomials alone (`tupleDegreeU`, no coefficient read), and a leaf
quotient's words by their least and greatest over that range (`leafLo`, `leafHi`; `c2Lo`, `c2Hi`).
Every closed number is then a small `decide +kernel` (the heights, the widths, the counters, the
chunks, the bounds; each well under a second); `layoutsOf`, `layoutWords` and `Shape.heap` are never
evaluated, and `layoutWords` stays irreducible here. At every measured shape `C2`'s bounds fall in one
interval `(2^(k−1), 2^k]`, so its variables are exact: at the reference `93,388,803 ≤ W ≤ 109,117,443`
(`c2Lo`, `c2Hi`; the upper bound is the words themselves by `#eval`).
-/

namespace FlockSound.Uni

open UniSound UniStatement LeanVM.Parameters Compose

attribute [local irreducible] UniStatement.layoutWords UniStatement.setupStack
  UniStatement.flockMatrixStack

/-! ## A stack's variables are its words' -/

/-- The words a column fills: `2^vars`, three times for an `E`-valued column. -/
def colWords (x : Column × ℕ × Bool) : ℕ := (if x.2.2 then 3 else 1) * 2 ^ x.2.1

/-- The words a list of columns fills. -/
def colsWords (cols : List (Column × ℕ × Bool)) : ℕ := (cols.map colWords).sum

/-- A stack's variables from its words (`StackLayout::new`): `⌈log₂ max(W, 2)⌉`, at least `15`. -/
def stackVarsOf (W : ℕ) : ℕ := max (log2Ceil (max W 2)) 15

theorem foldl_snd_add {α β : Type} (F : β × ℕ → α → β × ℕ) (w : α → ℕ)
    (hF : ∀ acc x, (F acc x).2 = acc.2 + w x) :
    ∀ (l : List α) (acc : β × ℕ), (l.foldl F acc).2 = acc.2 + (l.map w).sum
  | [], acc => by simp
  | x :: l, acc => by
    rw [List.foldl_cons, foldl_snd_add F w hF l, hF, List.map_cons, List.sum_cons]
    omega

theorem sum_pieces (cols : List (Column × ℕ × Bool)) :
    ((cols.flatMap fun (column, vars, eValued) ↦
      (List.range (if eValued then 3 else 1)).map fun limb ↦ (column, limb, vars)).map
        fun x : Column × ℕ × ℕ ↦ 2 ^ x.2.2).sum = colsWords cols := by
  induction cols with
  | nil => rfl
  | cons x cols ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih]
    obtain ⟨c, v, e⟩ := x
    simp only [List.map_map, Function.comp_def, colsWords, colWords, List.map_cons, List.sum_cons]
    cases e
    · simp
    · simp [List.map_const']
      omega

/-- **A stack's variables are its words'** (`StackLayout.new`): the sort permutes the pieces. -/
theorem stackLayout_vars (cols : List (Column × ℕ × Bool)) :
    (StackLayout.new cols).vars = stackVarsOf (colsWords cols) := by
  unfold StackLayout.new stackVarsOf
  simp only []
  rw [foldl_snd_add _ (fun x : Column × ℕ × ℕ ↦ 2 ^ x.2.2) (fun _ _ ↦ rfl)]
  rw [((List.mergeSort_perm _ _).map _).sum_eq, sum_pieces]
  simp

/-! ## `log2Ceil` -/

theorem log2Ceil_le_iff (W k : ℕ) : log2Ceil W ≤ k ↔ W ≤ 2 ^ k := by
  unfold log2Ceil
  have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  split_ifs with h
  · simp only [Nat.zero_le, true_iff]
    omega
  · have hl := Nat.log2_lt (n := W - 1) (k := k) (by omega)
    generalize 2 ^ k = P at hl hp ⊢
    generalize Nat.log2 (W - 1) = L at hl
    omega

theorem log2Ceil_mono {a b : ℕ} (h : a ≤ b) : log2Ceil a ≤ log2Ceil b :=
  (log2Ceil_le_iff a _).mpr (h.trans ((log2Ceil_le_iff b _).mp le_rfl))

theorem stackVarsOf_mono {a b : ℕ} (h : a ≤ b) : stackVarsOf a ≤ stackVarsOf b :=
  max_le_max (log2Ceil_mono (max_le_max h le_rfl)) le_rfl

/-! ## The three stacks' columns -/

/-- `C1`'s columns (`layouts`): `q_flock`, every table's columns and `z_T`, the memory's four
columns, the bytecode's final counts. -/
def c1Cols (shape : Shape) : List (Column × ℕ × Bool) :=
  [(.qflock, shape.heights.getD opBlake2s 0 + 8, false)] ++
    tables.flatMap (fun t ↦
      let h := shape.heights.getD t.opcode 0
      (List.range t.width).map (fun c ↦ (Column.table t.opcode c, h, false)) ++
        [(.inverse t.opcode, h, false)]) ++
    (List.range 4).map (fun k ↦ (Column.memory k, shape.logMemory, false)) ++
    [(.bytecodeFinal, shape.logBytecode, false)]

/-- The setup's columns (`layouts`): the bytecode's tuples, the addresses. -/
def setupCols (shape : Shape) : List (Column × ℕ × Bool) :=
  [(.bytecodeTuple, shape.logBytecode + 4, false), (.address, shape.logMemory, false)]

theorem layoutOf_c1 (s : Shape) : layoutOf (layoutsOf s) .c1 = StackLayout.new (c1Cols s) := rfl

theorem layoutOf_c2 (s : Shape) : layoutOf (layoutsOf s) .c2 = StackLayout.new s.c2Columns := rfl

theorem layoutOf_setup (s : Shape) : layoutOf (layoutsOf s) .setup = StackLayout.new (setupCols s) := rfl

theorem varsOf_layoutsOf (s : Shape) :
    varsOf (layoutsOf s) = max (max (max 0 (layoutOf (layoutsOf s) .c1).vars)
      (layoutOf (layoutsOf s) .c2).vars) (layoutOf (layoutsOf s) .setup).vars := rfl

/-! ## Sums -/

theorem sum_map_le {α : Type} (f g : α → ℕ) : ∀ (l : List α), (∀ x ∈ l, f x ≤ g x) →
    (l.map f).sum ≤ (l.map g).sum
  | [], _ => le_rfl
  | x :: l, h => by
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    exact Nat.add_le_add (h x (List.mem_cons_self ..))
      (sum_map_le f g l fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem length_le_sum_map {α : Type} (f : α → ℕ) : ∀ (l : List α), (∀ x ∈ l, 1 ≤ f x) →
    l.length ≤ (l.map f).sum
  | [], _ => le_rfl
  | x :: l, h => by
    rw [List.map_cons, List.sum_cons, List.length_cons]
    have := h x (List.mem_cons_self ..)
    have := length_le_sum_map f l fun y hy => h y (List.mem_cons_of_mem _ hy)
    omega

theorem colsWords_append (a b : List (Column × ℕ × Bool)) :
    colsWords (a ++ b) = colsWords a + colsWords b := by
  simp [colsWords]

theorem colsWords_flatMap {α : Type} (f : α → List (Column × ℕ × Bool)) :
    ∀ (l : List α), colsWords (l.flatMap f) = (l.map fun x ↦ colsWords (f x)).sum
  | [] => rfl
  | x :: l => by
    rw [List.flatMap_cons, colsWords_append, colsWords_flatMap f l, List.map_cons, List.sum_cons]

theorem sum_map_zip_fst {α β : Type} (f : α → ℕ) (l : List α) (m : List β) (h : l.length ≤ m.length) :
    ((l.zip m).map fun x ↦ f x.1).sum = (l.map f).sum := by
  rw [show (fun x : α × β ↦ f x.1) = f ∘ Prod.fst from rfl, ← List.map_map, List.map_fst_zip h]

/-! ## `C2`'s words -/

/-- The words of a quotient's chunks of `count` coefficients: `Σ 2^(e_k)` (`chunks`). -/
def chunkWords (count : ℕ) : ℕ := ((UniStatement.chunks count).map (2 ^ ·)).sum

/-- **A heap block's leaf quotient's words** (`E`-valued chunks), by its leaves and variables; none for
an unused block. -/
def leafWords (b : Leaves × ℕ) : ℕ :=
  match Shape.leafDegree ⟨b.1, b.2, 0⟩ with
  | none => 0
  | some d => 3 * chunkWords (d + 1)

theorem colsWords_chunks (l : List ℕ) (g : ℕ × ℕ → Column × ℕ × Bool) (hg : ∀ x, colWords (g x) = 3 * 2 ^ x.1) :
    colsWords ((l.zip (List.range l.length)).map g) = 3 * (l.map (2 ^ ·)).sum := by
  unfold colsWords
  rw [List.map_map, show colWords ∘ g = fun x ↦ 3 * 2 ^ x.1 from funext hg,
    sum_map_zip_fst (fun e ↦ 3 * 2 ^ e) l _ (by simp)]
  induction l with
  | nil => rfl
  | cons e l ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih]
    ring

/-- **`C2`'s words**: the heap and the tree quotient (`E`-valued, `2^h` each, and one), the constraint
quotient's chunks, each heap block's leaf quotient's. -/
theorem c2Words (s : Shape) : colsWords s.c2Columns =
    6 * 2 ^ s.heap.h + 3 + 3 * chunkWords (s.constraintDegree + 1) +
      (s.heap.blocks.map fun b ↦ leafWords (b.leaves, b.r)).sum := by
  unfold Shape.c2Columns
  simp only []
  rw [colsWords_append, colsWords_append, colsWords_chunks _ _ (fun x ↦ by rcases x with ⟨e, c⟩; rfl),
    colsWords_flatMap]
  refine congrArg₂ (· + ·) ?_ ?_
  · simp only [colsWords, colWords, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ite_true,
      pow_zero, chunkWords]
    ring
  · rw [← sum_map_zip_fst (fun b : Block ↦ leafWords (b.leaves, b.r)) s.heap.blocks
      (List.range s.heap.blocks.length) (by simp)]
    refine congrArg List.sum (List.map_congr_left fun x _ ↦ ?_)
    rcases x with ⟨block, index⟩
    show colsWords _ = leafWords (block.leaves, block.r)
    unfold leafWords
    rw [show Shape.leafDegree ⟨block.leaves, block.r, 0⟩ = Shape.leafDegree block from rfl]
    simp only []
    cases Shape.leafDegree block with
    | none => rfl
    | some d =>
      simp only []
      rw [colsWords_chunks _ _ (fun x ↦ by rcases x with ⟨e, c⟩; rfl)]
      rfl

/-! ## The heap -/

/-- The heap's used blocks (`HeapLayout::new`), unsorted: the memory, the bytecode, the tables. -/
def usedOf (s : Shape) : List (Leaves × ℕ) :=
  [(.memory, s.logMemory), (.bytecode, s.logBytecode)] ++
    (List.range s.heights.length).map fun t ↦ (.table t, s.heights.getD t 0)

/-- The heap's variables (`HeapLayout::new`): `⌈log₂ Σ 2^r⌉ + 1` over the used blocks. -/
def heapH (s : Shape) : ℕ := log2Ceil ((usedOf s).map fun x ↦ 2 ^ x.2).sum + 1

theorem heap_h (s : Shape) : s.heap.h = heapH s := by
  unfold Shape.heap HeapLayout.new heapH
  simp only []
  rw [((List.mergeSort_perm _ _).map _).sum_eq]
  rfl

theorem foldl_blocks_map (base : ℕ) : ∀ (l : List (Leaves × ℕ)) (acc : Array Block × ℕ),
    (l.foldl (fun (acc : Array Block × ℕ) (x : Leaves × ℕ) =>
      (acc.1.push ⟨x.1, x.2, base + acc.2⟩, acc.2 + 2 ^ x.2)) acc).1.toList.map
        (fun b ↦ (b.leaves, b.r)) = acc.1.toList.map (fun b ↦ (b.leaves, b.r)) ++ l
  | [], acc => by simp
  | x :: l, acc => by
    rw [List.foldl_cons, foldl_blocks_map base l]
    simp

/-- **The heap's blocks' leaf quotients are the used blocks'** (the sort permutes them; the unused
blocks have none). -/
theorem heap_blocks_words (s : Shape) :
    (s.heap.blocks.map fun b ↦ leafWords (b.leaves, b.r)).sum = ((usedOf s).map leafWords).sum := by
  unfold Shape.heap HeapLayout.new
  simp only []
  rw [List.map_append, List.sum_append]
  have hu : ∀ base offset, ((unusedBlocks base offset).map fun b ↦ leafWords (b.leaves, b.r)).sum = 0 := by
    intro base offset
    refine List.sum_eq_zero fun x hx ↦ ?_
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    rw [unusedBlocks_unused _ _ b hb]
    rfl
  rw [hu, Nat.add_zero, show (fun b : Block ↦ leafWords (b.leaves, b.r)) =
    leafWords ∘ (fun b ↦ (b.leaves, b.r)) from rfl, ← List.map_map, foldl_blocks_map]
  simp only [List.map_nil, List.nil_append]
  exact ((List.mergeSort_perm _ _).map _).sum_eq

/-! ## The tables' degrees, bounded without reading a coefficient -/

/-- **A tuple's degree from its monomials alone** (`tuple_degree` without the zero test): at least
`tupleDegree`. -/
def tupleDegreeU (tuple : List Form) : ℕ :=
  max 1 (tuple.foldl (fun d form ↦ form.foldl (fun d x ↦ max d x.1.length) d) 0)

theorem foldl_mono {α : Type} (f g : ℕ → α → ℕ) (h : ∀ d d' x, d ≤ d' → f d x ≤ g d' x) :
    ∀ (l : List α) (d d' : ℕ), d ≤ d' → l.foldl f d ≤ l.foldl g d'
  | [], _, _, hd => hd
  | x :: l, d, d', hd => by
    rw [List.foldl_cons, List.foldl_cons]
    exact foldl_mono f g h l _ _ (h d d' x hd)

theorem tupleDegree_le (tuple : List Form) : tupleDegree tuple ≤ tupleDegreeU tuple := by
  unfold tupleDegree tupleDegreeU
  refine max_le_max le_rfl (foldl_mono _ _ (fun d d' form hd ↦ ?_) _ _ _ le_rfl)
  refine foldl_mono _ _ (fun e e' x he ↦ ?_) _ _ _ hd
  rcases x with ⟨m, c⟩
  simp only []
  split_ifs
  · exact he.trans (le_max_left _ _)
  · exact max_le_max he le_rfl

theorem one_le_tupleDegree (tuple : List Form) : 1 ≤ tupleDegree tuple := le_max_left _ _

theorem foldl_pairs (f g : List Form → ℕ) : ∀ (l : List (List Form × List Form)) (a b : ℕ),
    l.foldl (fun (acc : ℕ × ℕ) (x : List Form × List Form) ↦ (acc.1 + f x.1, acc.2 + g x.2)) (a, b) =
      (a + (l.map fun x ↦ f x.1).sum, b + (l.map fun x ↦ g x.2).sum)
  | [], a, b => by simp
  | x :: l, a, b => by
    rw [List.foldl_cons, foldl_pairs f g l, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    simp only [Prod.mk.injEq]
    omega

theorem tableDegrees_eq (T : Table) : tableDegrees T =
    (1 + ((T.flushes.pull.zip T.flushes.push).map fun x ↦ tupleDegree x.1).sum,
      0 + ((T.flushes.pull.zip T.flushes.push).map fun x ↦ tupleDegree x.2).sum) :=
  foldl_pairs tupleDegree tupleDegree _ 1 0

/-- A table's least leaf degree over `n − 1`: `1 + #flushes` (every tuple has degree at least `1`). -/
def degLo (T : Table) : ℕ := 1 + (T.flushes.pull.zip T.flushes.push).length

/-- A table's greatest leaf degree over `n − 1`: its flushes' degrees from the monomials alone. -/
def degHi (T : Table) : ℕ :=
  max (1 + ((T.flushes.pull.zip T.flushes.push).map fun x ↦ tupleDegreeU x.1).sum)
    ((T.flushes.pull.zip T.flushes.push).map fun x ↦ tupleDegreeU x.2).sum

theorem degLo_le (T : Table) : degLo T ≤ max (tableDegrees T).1 (tableDegrees T).2 := by
  rw [tableDegrees_eq]
  have := length_le_sum_map (fun x : List Form × List Form ↦ tupleDegree x.1)
    (T.flushes.pull.zip T.flushes.push) fun x _ ↦ one_le_tupleDegree x.1
  unfold degLo
  exact (Nat.add_le_add_left this 1).trans (le_max_left _ _)

theorem le_degHi (T : Table) : max (tableDegrees T).1 (tableDegrees T).2 ≤ degHi T := by
  rw [tableDegrees_eq]
  unfold degHi
  show max (1 + _) (0 + _) ≤ _
  rw [Nat.zero_add]
  exact max_le_max (Nat.add_le_add_left (sum_map_le _ _ _ fun x _ ↦ tupleDegree_le x.1) _)
    (sum_map_le _ _ _ fun x _ ↦ tupleDegree_le x.2)

/-! ## The leaf quotients' words, bounded -/

/-- A table block's leaf quotient's words at `r` variables for the degree `m` over `n − 1`
(`Shape.leafDegree`). -/
def tableLeafWords (r m : ℕ) : ℕ :=
  3 * chunkWords (UniStatement.degree (m * (2 ^ r - 1) + (2 ^ r - Shape.leastRows r)) (2 ^ r) + 1)

theorem leafWords_table (t r : ℕ) : leafWords (.table t, r) =
    tableLeafWords r (max (tableDegrees (UniStatement.tables.getD t default)).1
      (tableDegrees (UniStatement.tables.getD t default)).2) := rfl

/-- The least of `f` on `[lo, hi]`. -/
def rangeMin (f : ℕ → ℕ) (lo hi : ℕ) : ℕ := ((List.range' lo (hi + 1 - lo)).map f).foldl min (f lo)

/-- The greatest of `f` on `[lo, hi]`. -/
def rangeMax (f : ℕ → ℕ) (lo hi : ℕ) : ℕ := ((List.range' lo (hi + 1 - lo)).map f).foldl max 0

theorem foldl_min_le : ∀ (l : List ℕ) (a x : ℕ), x ∈ l → l.foldl min a ≤ x
  | [], _, _, h => by simp at h
  | y :: l, a, x, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · have : ∀ (l : List ℕ) (b : ℕ), l.foldl min b ≤ b := by
        intro l
        induction l with
        | nil => intro b; exact le_rfl
        | cons z l ih => intro b; exact (ih _).trans (min_le_left _ _)
      exact (this _ _).trans (min_le_right _ _)
    · exact foldl_min_le l _ x h

theorem le_foldl_max : ∀ (l : List ℕ) (a x : ℕ), x ∈ l → x ≤ l.foldl max a
  | [], _, _, h => by simp at h
  | y :: l, a, x, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · have : ∀ (l : List ℕ) (b : ℕ), b ≤ l.foldl max b := by
        intro l
        induction l with
        | nil => intro b; exact le_rfl
        | cons z l ih => intro b; exact (le_max_left _ _).trans (ih _)
      exact (le_max_right _ _).trans (this _ _)
    · exact le_foldl_max l _ x h

theorem mem_range_map (f : ℕ → ℕ) {lo hi m : ℕ} (h1 : lo ≤ m) (h2 : m ≤ hi) :
    f m ∈ (List.range' lo (hi + 1 - lo)).map f :=
  List.mem_map.mpr ⟨m, List.mem_range'_1.mpr ⟨h1, by omega⟩, rfl⟩

theorem rangeMin_le (f : ℕ → ℕ) {lo hi m : ℕ} (h1 : lo ≤ m) (h2 : m ≤ hi) : rangeMin f lo hi ≤ f m :=
  foldl_min_le _ _ _ (mem_range_map f h1 h2)

theorem le_rangeMax (f : ℕ → ℕ) {lo hi m : ℕ} (h1 : lo ≤ m) (h2 : m ≤ hi) : f m ≤ rangeMax f lo hi :=
  le_foldl_max _ _ _ (mem_range_map f h1 h2)

/-- **A lower bound of a used block's leaf quotient's words**: a table's least over its degrees'
range, else the words. -/
def leafLo (b : Leaves × ℕ) : ℕ :=
  match b.1 with
  | .table t => rangeMin (tableLeafWords b.2) (degLo (UniStatement.tables.getD t default))
      (degHi (UniStatement.tables.getD t default))
  | _ => leafWords b

/-- **An upper bound of a used block's leaf quotient's words**: a table's greatest over its degrees'
range, else the words. -/
def leafHi (b : Leaves × ℕ) : ℕ :=
  match b.1 with
  | .table t => rangeMax (tableLeafWords b.2) (degLo (UniStatement.tables.getD t default))
      (degHi (UniStatement.tables.getD t default))
  | _ => leafWords b

theorem leafLo_le (b : Leaves × ℕ) : leafLo b ≤ leafWords b := by
  rcases b with ⟨l, r⟩
  cases l with
  | table t =>
    show rangeMin _ _ _ ≤ _
    rw [leafWords_table]
    exact rangeMin_le _ (degLo_le _) (le_degHi _)
  | memory => exact le_rfl
  | bytecode => exact le_rfl
  | unused => exact le_rfl

theorem le_leafHi (b : Leaves × ℕ) : leafWords b ≤ leafHi b := by
  rcases b with ⟨l, r⟩
  cases l with
  | table t =>
    show _ ≤ rangeMax _ _ _
    rw [leafWords_table]
    exact le_rangeMax _ (degLo_le _) (le_degHi _)
  | memory => exact le_rfl
  | bytecode => exact le_rfl
  | unused => exact le_rfl

/-- **A lower bound of `C2`'s words**, computable from the shape's numbers. -/
def c2Lo (s : Shape) : ℕ :=
  6 * 2 ^ heapH s + 3 + 3 * chunkWords (s.constraintDegree + 1) + ((usedOf s).map leafLo).sum

/-- **An upper bound of `C2`'s words**, computable from the shape's numbers. -/
def c2Hi (s : Shape) : ℕ :=
  6 * 2 ^ heapH s + 3 + 3 * chunkWords (s.constraintDegree + 1) + ((usedOf s).map leafHi).sum

theorem c2Lo_le (s : Shape) : c2Lo s ≤ colsWords s.c2Columns := by
  rw [c2Words, heap_blocks_words, heap_h]
  exact Nat.add_le_add_left (sum_map_le _ _ _ fun b _ ↦ leafLo_le b) _

theorem le_c2Hi (s : Shape) : colsWords s.c2Columns ≤ c2Hi s := by
  rw [c2Words, heap_blocks_words, heap_h]
  exact Nat.add_le_add_left (sum_map_le _ _ _ fun b _ ↦ le_leafHi b) _

/-! ## The three stacks' variables, bounded by closed numbers -/

/-- **A lower bound of a stack's variables**, computable: `C1`'s and the setup's exact, `C2`'s from
`c2Lo`. -/
def varsLo (s : Shape) : Commitment → ℕ
  | .c1 => stackVarsOf (colsWords (c1Cols s))
  | .c2 => stackVarsOf (c2Lo s)
  | .setup => stackVarsOf (colsWords (setupCols s))

/-- **An upper bound of a stack's variables**, computable: `C1`'s and the setup's exact, `C2`'s from
`c2Hi`. -/
def varsHi (s : Shape) : Commitment → ℕ
  | .c1 => stackVarsOf (colsWords (c1Cols s))
  | .c2 => stackVarsOf (c2Hi s)
  | .setup => stackVarsOf (colsWords (setupCols s))

theorem varsLo_le (s : Shape) (c : Commitment) : varsLo s c ≤ (layoutOf (layoutsOf s) c).vars := by
  cases c
  · rw [layoutOf_c1, stackLayout_vars]
    exact le_rfl
  · rw [layoutOf_c2, stackLayout_vars]
    exact stackVarsOf_mono (c2Lo_le s)
  · rw [layoutOf_setup, stackLayout_vars]
    exact le_rfl

theorem le_varsHi (s : Shape) (c : Commitment) : (layoutOf (layoutsOf s) c).vars ≤ varsHi s c := by
  cases c
  · rw [layoutOf_c1, stackLayout_vars]
    exact le_rfl
  · rw [layoutOf_c2, stackLayout_vars]
    exact stackVarsOf_mono (le_c2Hi s)
  · rw [layoutOf_setup, stackLayout_vars]
    exact le_rfl

theorem varsLo_c1 (s : Shape) : varsLo s .c1 = varsHi s .c1 := rfl

theorem varsLo_setup (s : Shape) : varsLo s .setup = varsHi s .setup := rfl

/-- **A stack's variables, when the bounds meet.** -/
theorem layoutVars_eq (s : Shape) (c : Commitment) (h : varsLo s c = varsHi s c) :
    (layoutOf (layoutsOf s) c).vars = varsLo s c :=
  le_antisymm (h ▸ le_varsHi s c) (varsLo_le s c)

/-! ## `UniShapes` and `LayoutVarsSmall` from the bounds -/

/-- **The shape check**: every stack's bounds inside `24 … 28`. -/
def shapeOK (s : Shape) : Bool := commitments.all fun c ↦ 24 ≤ varsLo s c && varsHi s c ≤ 28

theorem layoutVars_of_shapeOK (s : Shape) (h : shapeOK s = true) (c : Commitment) :
    24 ≤ (layoutOf (layoutsOf s) c).vars ∧ (layoutOf (layoutsOf s) c).vars ≤ 28 := by
  have hc : (24 ≤ varsLo s c && varsHi s c ≤ 28) = true :=
    List.all_eq_true.mp h c (by cases c <;> simp [commitments])
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  exact ⟨hc.1.trans (varsLo_le s c), (le_varsHi s c).trans hc.2⟩

theorem matrixVars_eq : matrixVars = 28 := rfl

/-- **`UniShapes` from the stacks' variables** (`C1`, `C2`, the setup in `24 … 28`; `A0`, `B0` have
`28`). -/
theorem uniShapes_of (D : Deployment)
    (h : ∀ c, 24 ≤ (layoutOf (layoutsOf D.shape) c).vars ∧ (layoutOf (layoutsOf D.shape) c).vars ≤ 28) :
    UniShapes D ∧ LayoutVarsSmall D := by
  have hsmall : LayoutVarsSmall D := fun c ↦ by have := (h c).2; omega
  have hk : ∀ k < 5, 24 ≤ wv D k ∧ wv D k ≤ 28 := by
    intro k hk
    interval_cases k
    · show 24 ≤ wv D (wordIndex .c1) ∧ wv D (wordIndex .c1) ≤ 28
      unfold wv
      rw [claimVars D hsmall .c1]
      exact h .c1
    · show 24 ≤ wv D (wordIndex .c2) ∧ wv D (wordIndex .c2) ≤ 28
      unfold wv
      rw [claimVars D hsmall .c2]
      exact h .c2
    · show 24 ≤ wv D (wordIndex .setup) ∧ wv D (wordIndex .setup) ≤ 28
      unfold wv
      rw [claimVars D hsmall .setup]
      exact h .setup
    · unfold wv
      rw [(matrixWordVars D.shape).1, matrixVars_eq]
      decide
    · unfold wv
      rw [(matrixWordVars D.shape).2, matrixVars_eq]
      decide
  exact ⟨⟨fun k hk' ↦ (hk k hk').1, fun k hk' ↦ (hk k hk').2⟩, hsmall⟩

/-- **`UniShapes` and `LayoutVarsSmall` from the shape check.** -/
theorem uniShapes_of_shapeOK (D : Deployment) (h : shapeOK D.shape = true) :
    UniShapes D ∧ LayoutVarsSmall D :=
  uniShapes_of D (layoutVars_of_shapeOK D.shape h)

/-! ## The reference shape -/

/-- The reference's heights: `⌈log₂ rows⌉` of `183266, 195439, 223851, 137591, 80937, 202025`. -/
theorem reference_heights : reference.heights = [18, 18, 18, 18, 17, 18] := by decide +kernel

/-- **`κ` at the reference**: BLAKE2S's height, `⌈log₂ 202025⌉ = 18`. -/
theorem hκ_reference (D : Deployment) (hD : D.shape = reference) :
    D.shape.heights.getD opBlake2s 0 = 18 := by
  rw [hD, reference_heights]
  rfl

/-- `C1`'s words at the reference: `2^26 + 102.5 · 2^18 + 4 · 2^21 + 2^19`. -/
theorem c1Words_reference : colsWords (c1Cols reference) = 102891520 := by decide +kernel

/-- The setup's words at the reference: `2^23 + 2^21`. -/
theorem setupWords_reference : colsWords (setupCols reference) = 10485760 := by decide +kernel

/-- `C2`'s words at the reference: between `93,388,803` and `109,117,443` (`c2Lo`, `c2Hi`), inside
`(2^26, 2^27]` (`#eval`: `109,117,443`). -/
theorem c2Words_reference :
    93388803 ≤ colsWords reference.c2Columns ∧ colsWords reference.c2Columns ≤ 109117443 := by
  have h : c2Lo reference = 93388803 ∧ c2Hi reference = 109117443 := by decide +kernel
  exact ⟨h.1 ▸ c2Lo_le _, h.2 ▸ le_c2Hi _⟩

theorem varsBounds_reference : (commitments.map fun c ↦ (varsLo reference c, varsHi reference c)) =
    [(27, 27), (27, 27), (24, 24)] := by decide +kernel

/-- **The reference's stacks' variables**: `C1` `27`, `C2` `27`, the setup `24`. -/
theorem layoutVars_reference : (layoutOf (layoutsOf reference) .c1).vars = 27 ∧
    (layoutOf (layoutsOf reference) .c2).vars = 27 ∧ (layoutOf (layoutsOf reference) .setup).vars = 24 := by
  have h := varsBounds_reference
  simp only [commitments, List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq] at h
  refine ⟨?_, ?_, ?_⟩
  · rw [layoutVars_eq _ _ (h.1.1.trans h.1.2.symm), h.1.1]
  · rw [layoutVars_eq _ _ (h.2.1.1.trans h.2.1.2.symm), h.2.1.1]
  · rw [layoutVars_eq _ _ (h.2.2.1.1.trans h.2.2.1.2.symm), h.2.2.1.1]

/-- **The batch's variables at the reference**: `V = 27`. -/
theorem varsOf_reference : varsOf (layoutsOf reference) = 27 := by
  rw [varsOf_layoutsOf, layoutVars_reference.1, layoutVars_reference.2.1, layoutVars_reference.2.2]
  rfl

theorem varsOf_reference_le (D : Deployment) (hD : D.shape = reference) :
    varsOf (layoutsOf D.shape) ≤ 28 := by
  rw [hD, varsOf_reference]
  decide

/-- **`UniShapes` at the reference.** -/
theorem uniShapes_reference (D : Deployment) (hD : D.shape = reference) : UniShapes D :=
  (uniShapes_of D fun c ↦ by
    rw [hD]
    obtain ⟨h1, h2, h3⟩ := layoutVars_reference
    cases c
    · rw [h1]; decide
    · rw [h2]; decide
    · rw [h3]; decide).1

/-- **`LayoutVarsSmall` at the reference.** -/
theorem layoutVarsSmall_reference (D : Deployment) (hD : D.shape = reference) : LayoutVarsSmall D := by
  intro c
  rw [hD]
  obtain ⟨h1, h2, h3⟩ := layoutVars_reference
  cases c
  · rw [h1]; decide
  · rw [h2]; decide
  · rw [h3]; decide

/-- **The reference's five layout words name `[27, 27, 24, 28, 28]` variables.** -/
theorem wv_reference (D : Deployment) (hD : D.shape = reference) :
    wv D 0 = 27 ∧ wv D 1 = 27 ∧ wv D 2 = 24 ∧ wv D 3 = 28 ∧ wv D 4 = 28 := by
  have hsmall := layoutVarsSmall_reference D hD
  obtain ⟨h1, h2, h3⟩ := layoutVars_reference
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show wv D (wordIndex .c1) = 27
    unfold wv
    rw [claimVars D hsmall .c1, hD, h1]
  · show wv D (wordIndex .c2) = 27
    unfold wv
    rw [claimVars D hsmall .c2, hD, h2]
  · show wv D (wordIndex .setup) = 24
    unfold wv
    rw [claimVars D hsmall .setup, hD, h3]
  · exact (matrixWordVars D.shape).1
  · exact (matrixWordVars D.shape).2

/-! ## The measured workloads -/

/-- **The measured workloads' stacks' variables** (`C1`, `C2`, the setup), each pinned by its
bounds. -/
theorem layoutVars_workloads :
    workloads.map (fun w ↦ commitments.map fun c ↦ (layoutOf (layoutsOf w.2.2) c).vars) =
      [[22, 24, 24], [24, 25, 24], [26, 27, 24], [27, 27, 24], [27, 28, 24], [28, 28, 24]] := by
  have hmeet : ∀ w ∈ workloads, ∀ c ∈ commitments, varsLo w.2.2 c = varsHi w.2.2 c := by decide +kernel
  have hvals : workloads.map (fun w ↦ commitments.map fun c ↦ varsLo w.2.2 c) =
      [[22, 24, 24], [24, 25, 24], [26, 27, 24], [27, 27, 24], [27, 28, 24], [28, 28, 24]] := by
    decide +kernel
  rw [← hvals]
  exact List.map_congr_left fun w hw ↦ List.map_congr_left fun c hc ↦ layoutVars_eq _ _ (hmeet w hw c hc)

/-- **`UniShapes` and `LayoutVarsSmall` for the measured workloads but `xmss32`**: `xmss128`,
`xmss400`, `xmss1000` (the reference), `xmss1290`, `xmss2000`. -/
theorem uniShapes_workloads (w : String × ℕ × Shape) (hw : w ∈ workloads.tail) (D : Deployment)
    (hD : D.shape = w.2.2) : UniShapes D ∧ LayoutVarsSmall D := by
  have h : ∀ w ∈ workloads.tail, shapeOK w.2.2 = true := by decide +kernel
  exact uniShapes_of_shapeOK D (hD ▸ h w hw)

/-- The first measured workload, `xmss32`: 32 signatures, memory `2^16`. -/
theorem workloads_head :
    workloads.head? = some ("xmss32", 32, shapeOf 16 [6060, 6490, 11768, 4703, 2699, 6489]) := rfl

/-- **`UniShapes` fails at `xmss32`**: its `C1` has `22` variables (`2^21` words of `q_flock` and
`3,796,992` in all), below the large WHIR shapes' `24`. -/
theorem not_uniShapes_xmss32 (D : Deployment) (hD : D.shape = shapeOf 16 [6060, 6490, 11768, 4703, 2699, 6489]) :
    ¬ UniShapes D := by
  intro hs
  have h1 : (layoutOf (layoutsOf (shapeOf 16 [6060, 6490, 11768, 4703, 2699, 6489])) .c1).vars = 22 := by
    have h : varsLo (shapeOf 16 [6060, 6490, 11768, 4703, 2699, 6489]) .c1 = 22 := by decide +kernel
    rw [layoutVars_eq _ _ (varsLo_c1 _), h]
  have h0 := hs.lo 0 (by decide)
  have hw : wv D 0 = 22 := by
    show layoutWordVars ((layoutWords D.shape).getD (wordIndex .c1) []) = 22
    rw [layoutWords_word, layoutWordVars_layoutWord _ _ _ _ (by rw [hD, h1]; decide), hD, h1]
  omega

/-! ## The program's IV -/

theorem programIv_length : programIv.length = 32 := rfl

/-- **`UniIv` for the reference program IV** (`32` bytes). -/
theorem uniIv_of (D : Deployment) (h : D.programIv = programIv) : UniIv D :=
  ⟨by rw [h, programIv_length]; decide, by rw [h, programIv_length]; decide⟩

/-! ## The chain's queries and the rounds' sizes (`hnQ`, `hnv`) -/

theorem nSteps_append : ∀ a b : List Compose.RoundSpec,
    Compose.nSteps (a ++ b) = Compose.nSteps a + Compose.nSteps b
  | [], b => by simp [Compose.nSteps]
  | s :: a, b => by
    simp only [List.cons_append, Compose.nSteps, nSteps_append a b]
    omega

theorem nSteps_replicate (s : Compose.RoundSpec) :
    ∀ n, Compose.nSteps (List.replicate n s) = n * (s.ns + 1)
  | 0 => by simp [Compose.nSteps]
  | n + 1 => by
    rw [List.replicate_succ, Compose.nSteps, nSteps_replicate s n]
    ring

/-- Flock's rounds take `31 + 2κ` steps. -/
theorem nSteps_flockRounds (κ : ℕ) : Compose.nSteps (flockRounds κ) = 31 + 2 * κ := by
  simp only [flockRounds, nSteps_append, nSteps_replicate, Compose.nSteps]
  ring

theorem uRounds_flock (κ nV V : ℕ) :
    uRounds (flockSoundInstance κ) nV V = uniRounds (flockRounds κ) nV V := rfl

/-- **The main line's chain makes `41 + 2κ + V` queries**: the label, `C1` and `α, β, γ` (`6`),
Flock's `31 + 2κ`, `C2` and `t` (`1`), the values and `ρ, λ` (`2`), the batch's `V` rounds. -/
theorem nQ_flock (κ nV V : ℕ) : (uSpec (flockSoundInstance κ) nV V).K.nQ = 41 + 2 * κ + V := by
  show Compose.nSteps (uniRounds (flockRounds κ) nV V) + 1 = _
  simp only [uniRounds, nSteps_append, nSteps_replicate, nSteps_flockRounds, Compose.nSteps]
  ring

/-- **`hnQ`**: at most `2^10` queries when `2κ + V ≤ 983`. -/
theorem hnQ_flock (κ nV V : ℕ) (h : 2 * κ + V ≤ 983) : (uSpec (flockSoundInstance κ) nV V).K.nQ ≤ 2 ^ 10 := by
  rw [nQ_flock]
  omega

/-- **`hnQ`** for `κ ≤ 32` and `V ≤ 64` (the reference: `κ = 18`, `V = 27`, `86` queries). -/
theorem hnQ_flock' (κ nV V : ℕ) (hκ : κ ≤ 32) (hV : V ≤ 64) :
    (uSpec (flockSoundInstance κ) nV V).K.nQ ≤ 2 ^ 10 :=
  hnQ_flock κ nV V (by omega)

theorem flushReads_le (weights : Array E) (sent : Array (Option E)) (x : List Form × List Form) :
    flushReads weights sent x ≤ 2 := by
  unfold flushReads
  split_ifs <;> omega

/-- A table's values at `t` at most: its sent columns, and two fingerprints per flush. -/
def readsHi (t : Table) : ℕ := (sentColumns t).length + 2 * (t.flushes.pull.zip t.flushes.push).length

theorem tableReads_le (t : Table) : tableReads t ≤ readsHi t := by
  unfold tableReads readsHi
  have := sum_map_le (flushReads #[] (sentPat t)) (fun _ ↦ 2) (t.flushes.pull.zip t.flushes.push)
    fun x _ ↦ flushReads_le _ _ x
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at this
  omega

/-- **The values at `t` are at most `122`** (the tables' sent columns and fingerprints, and seven). -/
theorem valsCount_le : valsCount ≤ 122 := by
  have h : (UniStatement.tables.map readsHi).sum = 115 := by decide +kernel
  have := sum_map_le tableReads readsHi UniStatement.tables fun t _ ↦ tableReads_le t
  show (UniStatement.tables.map tableReads).sum + 7 ≤ 122
  omega

/-- **`hnv`** for any number of values at `t` up to `2^30`: Flock's rounds read at most `64`
scalars. -/
theorem hnv_flock' (κ nV V : ℕ) (hnV : nV ≤ 2 ^ 30) :
    ∀ r ∈ uRounds (flockSoundInstance κ) nV V, r.nv ≤ 2 ^ 30 := by
  intro r hr
  rw [uRounds_flock] at hr
  simp only [uniRounds, flockRounds, List.mem_append, List.mem_cons, List.mem_replicate,
    List.not_mem_nil, or_false] at hr
  rcases hr with ((h | (((((h | h) | ⟨_, h⟩) | h) | ⟨_, h⟩) | h)) | (h | h)) | ⟨_, h⟩ <;> subst h <;>
    dsimp only <;> omega

/-- **`hnv`**: every round of the main line reads at most `2^30` scalars (Flock's at most `64`, the
values at `t` at most `122`), for every `κ` and `V`. -/
theorem hnv_flock (κ V : ℕ) : ∀ r ∈ uRounds (flockSoundInstance κ) valsCount V, r.nv ≤ 2 ^ 30 :=
  hnv_flock' κ valsCount V (valsCount_le.trans (by decide))

/-! ## Flock's rounds' errors (`hFl`) -/

open scoped ENNReal in
/-- **Flock's round errors are at most `(15 + κ)/|E|`**: `roundErr κ j` on its `23 + κ` rounds, and
`1/|E|` (`dBound`'s default) past them. -/
theorem err_flock_le (κ j : ℕ) :
    (flockSoundInstance κ).err j ≤ ((15 + κ : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  by_cases hj : j < 23 + κ
  · rw [flockSoundInstance_err κ j hj]
    refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
    unfold roundErr
    split_ifs <;> omega
  · show ((∑ i ∈ Finset.range ((((flockRounds κ)[j]?).map (·.ns)).getD 0 + 1), dBound κ j i : ℕ) :
        ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) ≤ _
    rw [List.getElem?_eq_none (by rw [flockRounds_length]; omega)]
    refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
    simp only [Option.map_none, Option.getD_none, Nat.zero_add, Finset.sum_range_one]
    unfold dBound
    split_ifs <;> omega

open scoped ENNReal in
/-- **`hFl`**: every Flock round's error is at most `2^32/|E|`, for `κ ≤ 2^32 − 15`. -/
theorem hFl_flock (κ : ℕ) (hκ : κ ≤ 2 ^ 32 - 15) :
    ∀ j, (flockSoundInstance κ).err j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := fun j ↦
  (err_flock_le κ j).trans (ENNReal.div_le_div_right (Nat.cast_le.mpr (by omega)) _)

/-! ## The Fiat–Shamir layer with the numbers in place -/

/-- **The Fiat–Shamir layer of the main line from the three bridge facts**, for `κ ≤ 32`, `V ≤ 64`,
the shapes and the IV (`fsLayer_of_bridges` with `hnQ_flock'`, `hnv_flock`). -/
theorem fsLayer_flock (D : Deployment) (κ V : ℕ) (hκ : κ ≤ 32) (hV : V ≤ 64)
    (C : UniCode D (flockSoundInstance κ) valsCount V) (hs : UniShapes D) (hI : UniIv D)
    (hS : UniSetupBridge D hs) (hVb : UniVerifierBridge D (flockSoundInstance κ) valsCount V C hs)
    (hX : UniExtractBridge D (flockSoundInstance κ) valsCount V hs) :
    FsLayer D (flockSoundInstance κ) valsCount V C :=
  fsLayer_of_bridges D _ valsCount V C hs (hnQ_flock' κ valsCount V hκ hV) (hnv_flock κ V) hI hS hVb hX

/-- **The Fiat–Shamir layer at the reference deployment from the three bridge facts**: `κ = 18`,
`V = varsOf (layoutsOf D.shape) = 27`, the shapes `uniShapes_reference`, the IV `uniIv_of`. -/
theorem fsLayer_reference (D : Deployment) (hD : D.shape = reference) (hIv : D.programIv = programIv)
    (C : UniCode D (flockSoundInstance 18) valsCount (varsOf (layoutsOf D.shape)))
    (hS : UniSetupBridge D (uniShapes_reference D hD))
    (hVb : UniVerifierBridge D (flockSoundInstance 18) valsCount (varsOf (layoutsOf D.shape)) C
      (uniShapes_reference D hD))
    (hX : UniExtractBridge D (flockSoundInstance 18) valsCount (varsOf (layoutsOf D.shape))
      (uniShapes_reference D hD)) :
    FsLayer D (flockSoundInstance 18) valsCount (varsOf (layoutsOf D.shape)) C :=
  fsLayer_flock D 18 _ (by decide) (by rw [hD, varsOf_reference]; decide) C _ (uniIv_of D hIv) hS hVb hX

/-! ## The end theorem at the reference -/

open scoped ENNReal in
/-- **Knowledge soundness at the reference deployment, its numbers in place**
(`uniKnowledgeSoundness_flock` at `κ = 18`): `hκ` (`hκ_reference`), `LayoutVarsSmall`
(`layoutVarsSmall_reference`), Flock's errors (`hFl_flock`), and the Fiat–Shamir layer from the three
bridge facts (`fsLayer_of_bridges` with `uniShapes_reference`, `hnQ_flock'`, `hnv_flock'`, `uniIv_of`).
What is left: the bus model and the identity model's rest (`B`, `J`, their numbers `hB`, `hdeg`,
`hrel`, the batch `hprod`, `htarget`), `WeightMle`, and the three bridges. -/
theorem uniKnowledgeSoundness_reference {D : Deployment} (hD : D.shape = reference)
    (hIv : D.programIv = programIv) (B : BusModel D 18) (J : UniIdsRest D (flockSoundInstance 18) B)
    (hnV : J.nV = valsCount) (hV : J.V = varsOf (layoutsOf D.shape))
    (hprod : ∀ s c1 ch fd c2 t vals rho lam,
      J.prod s c1 ch fd c2 t vals rho lam = batchProd D (flockSoundInstance 18) s c1 ch fd c2 t vals rho lam)
    (htarget : ∀ s c1 ch fd c2 t vals rho lam,
      J.target s c1 ch fd c2 t vals rho lam = batchTargetOf D (flockSoundInstance 18) s ch fd t vals rho lam)
    (hW : WeightMle D (flockSoundInstance 18))
    (hS : UniSetupBridge D (uniShapes_reference D hD))
    (hVb : UniVerifierBridge D (flockSoundInstance 18) J.nV J.V
      (uniCodeAt D (flockSoundInstance 18) (hκ_reference D hD) J.nV J.V hnV hV) (uniShapes_reference D hD))
    (hX : UniExtractBridge D (flockSoundInstance 18) J.nV J.V (uniShapes_reference D hD))
    (hB : 4 * B.N + B.ncv ≤ 2 ^ 32) (hdeg : J.degSum ≤ 2 ^ 32) (hrel : J.nRel + 2 ≤ 2 ^ 32) :
    UniKnowledgeSoundness D (uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 :=
  uniKnowledgeSoundness_flock 18 (hκ_reference D hD) B J hnV hV hprod htarget hW
    (layoutVarsSmall_reference D hD)
    (fsLayer_of_bridges D _ J.nV J.V _ (uniShapes_reference D hD)
      (hnQ_flock' 18 J.nV J.V (by decide) (by rw [hV, hD, varsOf_reference]; decide))
      (hnv_flock' 18 J.nV J.V (by rw [hnV]; exact valsCount_le.trans (by decide))) (uniIv_of D hIv) hS hVb hX)
    hB (hFl_flock 18 (by decide)) hdeg hrel

end FlockSound.Uni

/-- info: 'FlockSound.Uni.stackLayout_vars' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.stackLayout_vars

/-- info: 'FlockSound.Uni.c2Words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.c2Words

/-- info: 'FlockSound.Uni.heap_blocks_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.heap_blocks_words

/-- info: 'FlockSound.Uni.tupleDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.tupleDegree_le

/-- info: 'FlockSound.Uni.c2Lo_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.c2Lo_le

/-- info: 'FlockSound.Uni.le_c2Hi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.le_c2Hi

/-- info: 'FlockSound.Uni.varsLo_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.varsLo_le

/-- info: 'FlockSound.Uni.le_varsHi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.le_varsHi

/-- info: 'FlockSound.Uni.layoutVars_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.layoutVars_eq

/-- info: 'FlockSound.Uni.uniShapes_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.uniShapes_of

/-- info: 'FlockSound.Uni.uniShapes_of_shapeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.uniShapes_of_shapeOK

/-- info: 'FlockSound.Uni.hκ_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.hκ_reference

/-- info: 'FlockSound.Uni.c2Words_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.c2Words_reference

/-- info: 'FlockSound.Uni.layoutVars_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.layoutVars_reference

/-- info: 'FlockSound.Uni.varsOf_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.varsOf_reference

/-- info: 'FlockSound.Uni.varsOf_reference_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.varsOf_reference_le

/-- info: 'FlockSound.Uni.uniShapes_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.uniShapes_reference

/-- info: 'FlockSound.Uni.layoutVarsSmall_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.layoutVarsSmall_reference

/-- info: 'FlockSound.Uni.wv_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.wv_reference

/-- info: 'FlockSound.Uni.layoutVars_workloads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.layoutVars_workloads

/-- info: 'FlockSound.Uni.uniShapes_workloads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.uniShapes_workloads

/-- info: 'FlockSound.Uni.not_uniShapes_xmss32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.not_uniShapes_xmss32

/-- info: 'FlockSound.Uni.uniIv_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.uniIv_of

/-- info: 'FlockSound.Uni.nQ_flock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.nQ_flock

/-- info: 'FlockSound.Uni.hnQ_flock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.hnQ_flock

/-- info: 'FlockSound.Uni.hnQ_flock'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.hnQ_flock'

/-- info: 'FlockSound.Uni.valsCount_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.valsCount_le

/-- info: 'FlockSound.Uni.hnv_flock'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.hnv_flock'

/-- info: 'FlockSound.Uni.hnv_flock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.hnv_flock

/-- info: 'FlockSound.Uni.err_flock_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.err_flock_le

/-- info: 'FlockSound.Uni.hFl_flock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.hFl_flock

/-- info: 'FlockSound.Uni.fsLayer_flock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.fsLayer_flock

/-- info: 'FlockSound.Uni.fsLayer_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.fsLayer_reference

/-- info: 'FlockSound.Uni.uniKnowledgeSoundness_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.uniKnowledgeSoundness_reference
