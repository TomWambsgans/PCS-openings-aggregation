/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.

Every public layout `Layout::new` builds (`crates/quotient/src/opening.rs:120-142`) from a list of
`(table, height)` chunks is valid, by one generic proof over the chunks.
-/
import WhirBridge.Hidden

/-!
# Public layouts of any shape

A univariate leanVM PIOP commits public stacks (no hiding is needed): its tables, the bus's
product-tree column, the quotient, a setup commitment of fixed columns, `2^24 ..= 2^28` words each.
`Layout::new(vars, log_chunk, log_n, chunks)` (`Layout.new`) lays any of them out: the committed
table has `vars` variables and is cut in chunks of `2^log_chunk` entries; each listed chunk
`(table, height)` = `(chunk, len)` puts its leading `len` entries on `⌈len / 2^ℓ⌉` lanes
(`ℓ = log_n − 6`), one block of `2^ℓ` entries per lane, in the order listed.

* `NewOK`: what `Layout::new` asserts of its arguments (`ℓ ≤ log_chunk ≤ vars`, every chunk index
  below `2^(vars − log_chunk)`, every height at most `2^log_chunk`, at most `64` lanes in all), and
  `6 ≤ log_n`; decidable on the chunks' numbers alone (`Σ ⌈len / 2^ℓ⌉ ≤ 64`, never a stack).
* `Layout.new_valid`: **under `NewOK`, `Layout.new vars log_chunk log_n chunks` is `Layout.Valid`**,
  for every list of chunks: the hypothesis of `opening_sound`, `Layout.holds_iff`,
  `Layout.openingDoom_iff` and `Layout.joint_of_not_doom`. The proof is generic: a block of chunk `c`
  is `c · 2^(log_chunk − ℓ) + j` for `j < ⌈len / 2^ℓ⌉ ≤ 2^(log_chunk − ℓ)`
  (`mem_newBlocks`), so below `2^(vars − ℓ)`, and the lanes number `Σ ⌈len / 2^ℓ⌉`
  (`newBlocks_length`).
* `newBlocks_nodup`: with distinct chunk indices the blocks are distinct, so each table entry is
  read from one lane (`Blocks.table_eq_lane`); an entry whose block no lane holds reads `0`
  (`Blocks.table_eq_zero`), and `mem_newBlocks_iff` says which: **the table a public stack stands for
  is the stack's lanes on the listed chunks' first `⌈len / 2^ℓ⌉ · 2^ℓ` entries and zero elsewhere**
  (`Layout.new_table_eq_zero`). The entries of a chunk past its height `len` but inside its last
  lane are read back from the stack, as `Table::read` does; the opening does not force them to
  zero.
-/

namespace WhirBridge

open LeanVM.Parameters LeanVM.Protocol Finset

/-- `⌈len / 2^ℓ⌉` (`len.div_ceil(1 << log_lane)`, `opening.rs:127`): the lanes a chunk's leading
`len` entries take. -/
def lanesOf (logLane len : ℕ) : ℕ := (len + 2 ^ logLane - 1) / 2 ^ logLane

/-- **What `Layout::new` asserts** (`opening.rs:121-133`), and `6 ≤ log_n`: lanes no longer than a
chunk, chunks no longer than the table, every chunk index inside the table, every height inside its
chunk, at most `64` lanes. (The Rust's further assertion of at least one lane is not needed.) -/
structure NewOK (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ)) : Prop where
  six_le : laneFold ≤ logN
  lane_le : logN - laneFold ≤ logChunk
  chunk_le : logChunk ≤ vars
  chunk_lt : ∀ c ∈ chunks, c.1 < 2 ^ (vars - logChunk)
  len_le : ∀ c ∈ chunks, c.2 ≤ 2 ^ logChunk
  lanes_le : (chunks.map fun c ↦ lanesOf (logN - laneFold) c.2).sum ≤ 2 ^ laneFold

theorem newOK_iff {vars logChunk logN : ℕ} {chunks : List (ℕ × ℕ)} :
    NewOK vars logChunk logN chunks ↔
      laneFold ≤ logN ∧ logN - laneFold ≤ logChunk ∧ logChunk ≤ vars ∧
        (∀ c ∈ chunks, c.1 < 2 ^ (vars - logChunk)) ∧ (∀ c ∈ chunks, c.2 ≤ 2 ^ logChunk) ∧
        (chunks.map fun c ↦ lanesOf (logN - laneFold) c.2).sum ≤ 2 ^ laneFold :=
  ⟨fun ⟨a, b, c, d, e, f⟩ ↦ ⟨a, b, c, d, e, f⟩, fun ⟨a, b, c, d, e, f⟩ ↦ ⟨a, b, c, d, e, f⟩⟩

/-- `NewOK` is decided on the chunks' numbers (`decide`). -/
instance {vars logChunk logN : ℕ} {chunks : List (ℕ × ℕ)} :
    Decidable (NewOK vars logChunk logN chunks) :=
  decidable_of_iff _ newOK_iff.symm

/-! ## Arithmetic -/

theorem lanesOf_le {ℓ lc len : ℕ} (hℓ : ℓ ≤ lc) (hlen : len ≤ 2 ^ lc) :
    lanesOf ℓ len ≤ 2 ^ (lc - ℓ) := by
  have hpos : 0 < 2 ^ ℓ := Nat.two_pow_pos ℓ
  have hmul : 2 ^ (lc - ℓ) * 2 ^ ℓ = 2 ^ lc := by
    rw [← pow_add, Nat.sub_add_cancel hℓ]
  refine Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hpos).2 ?_)
  rw [Nat.succ_mul, hmul]
  omega

/-- A block `c << k | j` with `j < 2^k` is `c · 2^k + j`. -/
theorem shiftLeft_or_eq {c j k : ℕ} (hj : j < 2 ^ k) : c <<< k ||| j = c * 2 ^ k + j := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt hj, Nat.shiftLeft_eq]

theorem block_div {c j k : ℕ} (hj : j < 2 ^ k) : (c * 2 ^ k + j) / 2 ^ k = c := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hj, zero_add]

theorem block_mod {c j k : ℕ} (hj : j < 2 ^ k) : (c * 2 ^ k + j) % 2 ^ k = j := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-! ## The blocks -/

section Blocks

variable {vars logChunk logN : ℕ} {chunks : List (ℕ × ℕ)}

/-- **The lanes `Layout::new` lists** number `Σ ⌈len / 2^ℓ⌉`. -/
theorem newBlocks_length (logChunk logN : ℕ) (chunks : List (ℕ × ℕ)) :
    (Layout.newBlocks logChunk logN chunks).length =
      (chunks.map fun c ↦ lanesOf (logN - laneFold) c.2).sum := by
  simp only [Layout.newBlocks, List.length_flatMap, List.length_map, List.length_range]
  rfl

/-- **The blocks of a chunk**: under `NewOK`, `b` is a listed block iff it is
`c · 2^(log_chunk − ℓ) + j` for a listed chunk `c` and `j < ⌈len / 2^ℓ⌉`. -/
theorem mem_newBlocks (h : NewOK vars logChunk logN chunks) (b : ℕ) :
    b ∈ Layout.newBlocks logChunk logN chunks ↔
      ∃ c ∈ chunks, ∃ j < lanesOf (logN - laneFold) c.2,
        b = c.1 * 2 ^ (logChunk - (logN - laneFold)) + j := by
  simp only [Layout.newBlocks, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨c, hc, j, hj, rfl⟩
    have hj' : j < 2 ^ (logChunk - (logN - laneFold)) :=
      lt_of_lt_of_le hj (lanesOf_le h.lane_le (h.len_le c hc))
    exact ⟨c, hc, j, hj, shiftLeft_or_eq hj'⟩
  · rintro ⟨c, hc, j, hj, rfl⟩
    have hj' : j < 2 ^ (logChunk - (logN - laneFold)) :=
      lt_of_lt_of_le hj (lanesOf_le h.lane_le (h.len_le c hc))
    exact ⟨c, hc, j, hj, shiftLeft_or_eq hj'⟩

/-- Every listed block is inside the table: below `2^(vars − ℓ)`. -/
theorem newBlocks_lt (h : NewOK vars logChunk logN chunks) :
    ∀ b ∈ Layout.newBlocks logChunk logN chunks, b < 2 ^ (vars - (logN - laneFold)) := by
  intro b hb
  obtain ⟨c, hc, j, hj, rfl⟩ := (mem_newBlocks h b).1 hb
  have hj' : j < 2 ^ (logChunk - (logN - laneFold)) :=
    lt_of_lt_of_le hj (lanesOf_le h.lane_le (h.len_le c hc))
  have hpow : 2 ^ (vars - logChunk) * 2 ^ (logChunk - (logN - laneFold)) =
      2 ^ (vars - (logN - laneFold)) := by
    rw [← pow_add]
    congr 1
    have := h.lane_le
    have := h.chunk_le
    omega
  calc c.1 * 2 ^ (logChunk - (logN - laneFold)) + j
      < (c.1 + 1) * 2 ^ (logChunk - (logN - laneFold)) := by rw [Nat.succ_mul]; omega
    _ ≤ 2 ^ (vars - logChunk) * 2 ^ (logChunk - (logN - laneFold)) :=
        Nat.mul_le_mul_right _ (h.chunk_lt c hc)
    _ = 2 ^ (vars - (logN - laneFold)) := hpow

/-- **Distinct chunks give distinct blocks.** -/
theorem newBlocks_nodup (h : NewOK vars logChunk logN chunks)
    (hd : (chunks.map Prod.fst).Nodup) : (Layout.newBlocks logChunk logN chunks).Nodup := by
  set k := logChunk - (logN - laneFold)
  have hlt : ∀ c ∈ chunks, ∀ j, j < lanesOf (logN - laneFold) c.2 → j < 2 ^ k :=
    fun c hc j hj ↦ lt_of_lt_of_le hj (lanesOf_le h.lane_le (h.len_le c hc))
  rw [Layout.newBlocks, List.nodup_flatMap]
  refine ⟨fun c hc ↦ ?_, ?_⟩
  · refine List.Nodup.map_on (fun x hx y hy hxy ↦ ?_) List.nodup_range
    have hx' := hlt c hc x (List.mem_range.1 hx)
    have hy' := hlt c hc y (List.mem_range.1 hy)
    rw [shiftLeft_or_eq hx', shiftLeft_or_eq hy'] at hxy
    omega
  · have hp : chunks.Pairwise fun a b ↦ a.1 ≠ b.1 := List.pairwise_map.1 hd
    refine hp.imp_of_mem fun {a b} ha hb hne ↦ ?_
    intro x hxa hxb
    simp only [List.mem_map, List.mem_range] at hxa hxb
    obtain ⟨i, hi, rfl⟩ := hxa
    obtain ⟨j, hj, hij⟩ := hxb
    have hi' := hlt a ha i hi
    have hj' := hlt b hb j hj
    rw [shiftLeft_or_eq hi', shiftLeft_or_eq hj'] at hij
    have := congrArg (· / 2 ^ k) hij
    simp only [block_div hi', block_div hj'] at this
    exact hne this.symm

end Blocks

/-! ## The layout -/

section Layout

variable {vars logChunk logN : ℕ} {chunks : List (ℕ × ℕ)}

/-- `Layout::new`'s layout reads back its listed blocks. -/
theorem Layout.new_toBlocks (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ)) :
    (Layout.new vars logChunk logN chunks).toBlocks =
      ⟨vars, logN, Layout.newBlocks logChunk logN chunks⟩ := by
  simp only [Layout.toBlocks, Layout.new, List.map_map]
  congr 1
  conv_rhs => rw [← List.map_id (Layout.newBlocks logChunk logN chunks)]
  rfl

/-- `Layout::new`'s layouts are public: no piece, every lane a block. -/
theorem Layout.new_isPublic (vars logChunk logN : ℕ) (chunks : List (ℕ × ℕ)) :
    (Layout.new vars logChunk logN chunks).IsPublic := by
  refine ⟨rfl, fun l hl ↦ ?_⟩
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hl
  exact ⟨b, rfl⟩

/-- Under `NewOK` its blocks are a valid public stacking. -/
theorem Layout.new_toBlocks_valid (h : NewOK vars logChunk logN chunks) :
    (Layout.new vars logChunk logN chunks).toBlocks.Valid := by
  rw [Layout.new_toBlocks]
  refine ⟨h.six_le, ?_, ?_, ?_⟩
  · show logN - laneFold ≤ vars
    exact h.lane_le.trans h.chunk_le
  · show (Layout.newBlocks logChunk logN chunks).length ≤ 2 ^ laneFold
    rw [newBlocks_length]
    exact h.lanes_le
  · exact newBlocks_lt h

/-- **Every public layout of `(table, height)` chunks that `Layout::new` accepts is valid**: one
lemma for every shape the PIOP picks. -/
theorem Layout.new_valid (h : NewOK vars logChunk logN chunks) :
    (Layout.new vars logChunk logN chunks).Valid :=
  Or.inl ⟨Layout.new_isPublic _ _ _ _, Layout.new_toBlocks_valid h⟩

/-- The layout's stack and lanes. -/
theorem Layout.new_logN : (Layout.new vars logChunk logN chunks).logN = logN := rfl

theorem Layout.new_vars : (Layout.new vars logChunk logN chunks).vars = vars := rfl

theorem Layout.new_lanes_length :
    (Layout.new vars logChunk logN chunks).lanes.length =
      (chunks.map fun c ↦ lanesOf (logN - laneFold) c.2).sum := by
  simp only [Layout.new, List.length_map]
  exact newBlocks_length _ _ _

end Layout

/-! ## The table read back -/

/-- **An entry whose block a lane holds is that lane's entry**, for distinct blocks. -/
theorem Blocks.table_eq_lane (L : Blocks) (hd : L.blocks.Nodup) (q : Column L.logN) {t l : ℕ}
    (hl : l < L.lanes) (hb : L.blocks.getD l 0 = t / 2 ^ L.logLane) :
    L.table q t = q.values.getD (t % 2 ^ L.logLane + 2 ^ L.logLane * l) 0 := by
  rw [Blocks.table, Finset.sum_eq_single_of_mem l (mem_range.2 hl), if_pos hb]
  intro l' hl' hne
  rw [if_neg]
  intro hb'
  have hl'' : l' < L.blocks.length := mem_range.1 hl'
  have hl''' : l < L.blocks.length := hl
  rw [← hb, List.getD_eq_getElem _ _ hl'', List.getD_eq_getElem _ _ hl'''] at hb'
  exact hne ((hd.getElem_inj_iff).1 hb')

/-- **An entry whose block no lane holds reads `0`.** -/
theorem Blocks.table_eq_zero (L : Blocks) (q : Column L.logN) {t : ℕ}
    (hb : t / 2 ^ L.logLane ∉ L.blocks) : L.table q t = 0 := by
  refine Finset.sum_eq_zero fun l hl ↦ if_neg fun h ↦ hb ?_
  rw [← h, List.getD_eq_getElem _ _ (mem_range.1 hl)]
  exact List.getElem_mem _

/-- **Which entries a public layout of chunks reads from its lanes**: entry `t` (in chunk
`t / 2^log_chunk`, at `t mod 2^log_chunk` in it) is on a lane iff its chunk is listed with a height
whose lanes cover it, `(t mod 2^log_chunk) / 2^ℓ < ⌈len / 2^ℓ⌉`. -/
theorem mem_newBlocks_iff {vars logChunk logN : ℕ} {chunks : List (ℕ × ℕ)}
    (h : NewOK vars logChunk logN chunks) (t : ℕ) :
    t / 2 ^ (logN - laneFold) ∈ Layout.newBlocks logChunk logN chunks ↔
      ∃ c ∈ chunks, t / 2 ^ logChunk = c.1 ∧
        t % 2 ^ logChunk / 2 ^ (logN - laneFold) < lanesOf (logN - laneFold) c.2 := by
  have hlen := h.len_le
  have hℓ := h.lane_le
  rw [mem_newBlocks h]
  generalize logN - laneFold = ℓ at *
  generalize hk : logChunk - ℓ = k
  have hlc : logChunk = k + ℓ := by omega
  have hlanes : ∀ c ∈ chunks, lanesOf ℓ c.2 ≤ 2 ^ k :=
    fun c hc ↦ hk ▸ lanesOf_le hℓ (hlen c hc)
  -- `t = 2^logChunk · a + 2^ℓ · j + o`, `j < 2^k`, `o < 2^ℓ`
  have hdiv : t / 2 ^ ℓ = t / 2 ^ logChunk * 2 ^ k + t % 2 ^ logChunk / 2 ^ ℓ := by
    have e0 : 2 ^ logChunk = 2 ^ k * 2 ^ ℓ := by rw [← pow_add, ← hlc]
    have e : 2 ^ logChunk * (t / 2 ^ logChunk) = 2 ^ ℓ * (t / 2 ^ logChunk * 2 ^ k) := by
      rw [e0]; ring
    calc t / 2 ^ ℓ = (2 ^ logChunk * (t / 2 ^ logChunk) + t % 2 ^ logChunk) / 2 ^ ℓ := by
          rw [Nat.div_add_mod]
      _ = (2 ^ ℓ * (t / 2 ^ logChunk * 2 ^ k) + t % 2 ^ logChunk) / 2 ^ ℓ := by rw [e]
      _ = t / 2 ^ logChunk * 2 ^ k + t % 2 ^ logChunk / 2 ^ ℓ :=
          Nat.mul_add_div (Nat.two_pow_pos ℓ) _ _
  have hj : t % 2 ^ logChunk / 2 ^ ℓ < 2 ^ k := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos ℓ), ← pow_add, ← hlc]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [hdiv]
  constructor
  · rintro ⟨c, hc, j, hjc, he⟩
    have hj' : j < 2 ^ k := lt_of_lt_of_le hjc (hlanes c hc)
    have h1 := congrArg (· / 2 ^ k) he
    have h2 := congrArg (· % 2 ^ k) he
    simp only [block_div hj, block_div hj', block_mod hj, block_mod hj'] at h1 h2
    exact ⟨c, hc, h1, by rw [h2]; exact hjc⟩
  · rintro ⟨c, hc, ha, hjc⟩
    exact ⟨c, hc, _, hjc, by rw [ha]⟩

/-- **The table a public layout of chunks stands for is zero off its lanes**: an entry of an
unlisted chunk, or of a listed one past the lanes its height takes, reads `0`, whatever the stack. -/
theorem Layout.new_table_eq_zero {vars logChunk logN : ℕ} {chunks : List (ℕ × ℕ)}
    (h : NewOK vars logChunk logN chunks) (q : Column logN) {t : ℕ}
    (ht : ∀ c ∈ chunks, t / 2 ^ logChunk = c.1 →
      lanesOf (logN - laneFold) c.2 ≤ t % 2 ^ logChunk / 2 ^ (logN - laneFold)) :
    (Layout.new vars logChunk logN chunks).table q t = 0 := by
  have hb : t / 2 ^ (logN - laneFold) ∉ Layout.newBlocks logChunk logN chunks := by
    rw [mem_newBlocks_iff h]
    rintro ⟨c, hc, ha, hlt⟩
    exact absurd (ht c hc ha) (not_le.2 hlt)
  simp only [Layout.table, Layout.new]
  have := Blocks.table_eq_zero (Layout.new vars logChunk logN chunks).toBlocks q
    (t := t) (by rw [Layout.new_toBlocks]; exact hb)
  exact this

end WhirBridge
