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
  (`wv_reference`). Of the measured workloads, `xmss128`, `xmss400`, `xmss1000`, `xmss1290` and
  `xmss2000` satisfy both (`uniShapes_workloads`); **`xmss32` does not**: its `C1` has `22` variables
  (`not_uniShapes_xmss32`), below the large WHIR shapes' `24`.
* **`UniIv`** for the reference program IV (`32` bytes): `uniIv_of`.
* **`hnQ`**: the main line's chain makes `41 + 2κ + V` queries (`nQ_flock`), at most `2^10` for
  `2κ + V ≤ 983` (`hnQ_flock`; `κ ≤ 32`, `V ≤ 64` in `hnQ_flock'`); **`hnv`**: every round reads at
  most `2^30` scalars, for every `κ` and `V` (`hnv_flock`; the values at `t` are at most `122`,
  `valsCount_le`).
* **At the reference**: `κ = 18` (`hκ_reference`), `V = 27` (`varsOf_reference`), and the
  Fiat–Shamir layer from the three bridge facts alone (`fsLayer_reference`).

**How the stacks' variables are computed** without evaluating a layout in the kernel (`List.mergeSort`
is well-founded recursion, and `E`'s arithmetic does not reduce there): a stack's variables are
`max (log2Ceil (max W 2)) 15` of the words `W` its columns fill (`stackLayout_vars`; the sort only
permutes the pieces). `C1`'s and the setup's words are a closed sum of the shape's numbers
(`c1Cols`, `setupCols`). `C2`'s are `6 · 2^h + 3`, the constraint quotient's chunks and each used heap
block's leaf quotient's chunks (`c2Words`, `heap_blocks_words`: the heap's sort permutes the used
blocks, the unused ones have no quotient). A table's leaf degree reads its flushes' degrees
(`tableDegrees`), which test `E` coefficients against zero; they are bounded instead, below by
`1 + #flushes` (every tuple has degree at least `1`) and above by the degrees of the monomials alone
(`tupleDegreeU`, no coefficient read), and the leaf quotient's words are bounded by their least and
greatest over that range (`leafLo`, `leafHi`, `c2Lo`, `c2Hi`). Every closed number is then a small
`decide +kernel` (the heights, the widths, the chunks, the bounds); `layoutsOf`, `layoutWords`,
`Shape.heap` are never evaluated whole. At the reference the bounds give `2^26 < c2Lo ≤ c2Hi ≤ 2^27`,
so `C2`'s `27` is exact (its words are `109,117,443`).
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

end FlockSound.Uni
