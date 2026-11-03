-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Follows `formal/UniComplete/UniComplete/Whir.lean` (the
-- plain layouts) and `formal/EndToEnd/Completeness/E2ECompleteness/ProverStack.lean` (`wiring_stackClaims_hold`) for π2's
-- public layouts of chunks (`crates/leanvm_rec/src/pi2/prover.rs`'s `layouts`, `quotient::opening::Layout::new`); uses
-- `formal/WhirBridge` (`Layout.new_valid`, `Layout.holds_iff`, `Blocks.table_eq_lane`, `admissible_large`) and leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0) through
-- `E2ECompleteness.ProverOpening` (`openingWithH_proveOpeningWithH`, `exists_failed_pow_opening`).
import RecCompose.Layers
import UniComplete.Whir
import WhirBridge.LargeLayout

/-!
# Honest WHIR openings at π2's layouts

π2 opens its three commitments (`W`, `Q`, the setup) on the public layouts of chunks `layoutsOf m`
(`PcsQuotient.Layout.ofChunks`, the Rust's `Layout::new`): at `m = 24`, `W` on `2^24` words (one chunk of `2^24`),
`Q` on `2^28` (fifteen chunks of `2^24`, `quotient_chunks`), the setup on `2^25` (two chunks). Here, for **every** public
layout of chunks that `Layout::new` accepts (`WhirBridge.NewOK`, distinct chunks), at a pure Keccak-256 `H` and
permutation `F`:

* **`ofChunks_lanes`, `layoutTr_ofChunks`**: the Statement's `ofChunks` is F2's `Layout.new` (the block
  `c · 2^(lc − ℓ) + j` is `c <<< (lc − ℓ) ||| j`, `j` below the chunk's lanes);
* **`table_new_eq`**: the table F2's layout reads off WHIR's column of a stack (`colOf`) is the Statement's
  `readEntry` of the stack (one lane per block, the blocks distinct, zero where no lane holds the entry);
* **`ofChunks_stackClaims_hold`**: a claim that holds of the stack under the layout (`RecCompose.ClaimOn`: the table's
  multilinear extension, the first coordinate the lowest bit) is every stack claim of its opening in WHIR's semantics
  (`Layout.holds_iff` at `Layout.new_valid`), and every stack claim's weight is multilinear;
* **`ofChunks_open_honest`**: every proof `proveOpeningWithH` makes of true claims on the stack's commitment is accepted
  by `openingWithH` against the commitment's root (`openingWithH_proveOpeningWithH`), for `log_n ≤ 64` and a WHIR
  shape admissible at rate `1/2`; **`ofChunks_fails_only_at_pow`**: if it makes none, a `17`-bit proof of work failed
  for every nonce below `fuel`.
* **At π2's layouts** (`pi2Layout`: `W`, `Q`, the setup at `m = 24`): `NewOK` by decision on the chunks' numbers,
  admissibility by `WhirBridge.admissible_large` (`24`, `28`, `25` variables): **`pi2Open_honest`**,
  **`pi2OpeningWith_honest`** (the Statement's `openingWith`, `commitWith`, `proveOpeningWith` over `F`, as the
  contract's `PCS_OPEN` runs them), **`pi2Open_fails_only_at_pow`**.

No stack is evaluated: the stacks are arbitrary; only the layouts' numbers are decided by the kernel.
-/

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover
open LeanVM.Protocol.EndToEnd (boolPoint)
open LeanVM.Protocol.Verifier (eqEval)
open Finset

set_option autoImplicit false

namespace RecCompose.Pi2W

/-! ## `ofChunks` is F2's `Layout.new` -/

theorem flatMap_congr' {α β : Type} : ∀ (l : List α) {f g : α → List β}, (∀ a ∈ l, f a = g a) →
    l.flatMap f = l.flatMap g
  | [], _, _, _ => rfl
  | a :: l, u, v, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      flatMap_congr' l fun b hb ↦ h b (List.mem_cons_of_mem _ hb)]

section Chunks

variable {vars lc logN : ℕ} {chunks : List (ℕ × ℕ)}

/-- **The Statement's lanes are F2's blocks**, under `Layout::new`'s assertions. -/
theorem ofChunks_lanes (h : WhirBridge.NewOK vars lc logN chunks) :
    (PcsQuotient.Layout.ofChunks vars lc logN chunks).lanes =
      (WhirBridge.Layout.newBlocks lc logN chunks).map PcsQuotient.Lane.block := by
  simp only [PcsQuotient.Layout.ofChunks, WhirBridge.Layout.newBlocks, List.map_flatMap, List.map_map]
  refine flatMap_congr' _ fun c hc ↦ ?_
  have hle := WhirBridge.lanesOf_le h.lane_le (h.len_le c hc)
  refine List.map_congr_left fun j hj ↦ ?_
  have hj' : j < 2 ^ (lc - (logN - WhirBridge.laneFold)) :=
    lt_of_lt_of_le (List.mem_range.1 hj) hle
  simp only [Function.comp_apply]
  rw [WhirBridge.shiftLeft_or_eq hj']
  rfl

/-- **`ofChunks` is F2's `Layout.new`**, under `Layout::new`'s assertions. -/
theorem layoutTr_ofChunks (h : WhirBridge.NewOK vars lc logN chunks) :
    Bridge.layoutTr (PcsQuotient.Layout.ofChunks vars lc logN chunks) =
      WhirBridge.Layout.new vars lc logN chunks := by
  unfold Bridge.layoutTr
  rw [ofChunks_lanes h, List.map_map]
  rfl

/-- `ofChunks` is public. -/
theorem ofChunks_logPiece : (PcsQuotient.Layout.ofChunks vars lc logN chunks).logPiece = none := rfl

theorem ofChunks_logN : (PcsQuotient.Layout.ofChunks vars lc logN chunks).logN = logN := rfl

theorem ofChunks_vars : (PcsQuotient.Layout.ofChunks vars lc logN chunks).vars = vars := rfl

theorem ofChunks_logLane :
    (PcsQuotient.Layout.ofChunks vars lc logN chunks).logLane = logN - WhirBridge.laneFold := rfl

/-! ## The table read back -/

theorem findIdx_block_some {bs : List ℕ} (hd : bs.Nodup) {l : ℕ} (hl : l < bs.length) :
    (bs.map PcsQuotient.Lane.block).findIdx? (· = .block bs[l]) = some l := by
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨by simpa using hl, by simp, fun j hj ↦ ?_⟩
  have hj' : j < bs.length := lt_trans hj hl
  simp only [List.getElem_map, PcsQuotient.Lane.block.injEq, decide_eq_true_eq]
  intro he
  exact absurd ((hd.getElem_inj_iff).1 he) (Nat.ne_of_lt hj)

theorem findIdx_block_none {bs : List ℕ} {b : ℕ} (hb : b ∉ bs) :
    (bs.map PcsQuotient.Lane.block).findIdx? (· = .block b) = none := by
  rw [List.findIdx?_eq_none_iff]
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
  simp only [PcsQuotient.Lane.block.injEq, decide_eq_false_iff_not]
  rintro rfl
  exact hb ha

/-- **The table F2's layout reads off a stack's column is the Statement's `readEntry`**, for distinct chunks. -/
theorem table_new_eq (h : WhirBridge.NewOK vars lc logN chunks) (hd : (chunks.map Prod.fst).Nodup)
    (stack : Array K) (t : ℕ) :
    (WhirBridge.Layout.new vars lc logN chunks).table (E2ECompleteness.colOf logN stack) t =
      (PcsQuotient.Layout.ofChunks vars lc logN chunks).readEntry (fun j ↦ stack.getD j 0) t := by
  have hnd := WhirBridge.newBlocks_nodup h hd
  have hB : (WhirBridge.Layout.new vars lc logN chunks).toBlocks.blocks =
      WhirBridge.Layout.newBlocks lc logN chunks := by
    rw [WhirBridge.Layout.new_toBlocks]
  have hℓ : (WhirBridge.Layout.new vars lc logN chunks).toBlocks.logLane = logN - WhirBridge.laneFold := by
    rw [WhirBridge.Layout.new_toBlocks]; rfl
  have hlen : (WhirBridge.Layout.newBlocks lc logN chunks).length ≤ 2 ^ WhirBridge.laneFold := by
    rw [WhirBridge.newBlocks_length]; exact h.lanes_le
  have htab : (WhirBridge.Layout.new vars lc logN chunks).table (E2ECompleteness.colOf logN stack) t =
      (WhirBridge.Layout.new vars lc logN chunks).toBlocks.table (E2ECompleteness.colOf logN stack) t := rfl
  have hlt : ∀ l, l < (WhirBridge.Layout.newBlocks lc logN chunks).length →
      t % 2 ^ (logN - WhirBridge.laneFold) + 2 ^ (logN - WhirBridge.laneFold) * l < 2 ^ logN := by
    intro l hl
    have hm := Nat.mod_lt t (Nat.two_pow_pos (logN - WhirBridge.laneFold))
    have hl64 : l < 2 ^ WhirBridge.laneFold := lt_of_lt_of_le hl hlen
    have hpow : 2 ^ (logN - WhirBridge.laneFold) * 2 ^ WhirBridge.laneFold = 2 ^ logN := by
      rw [← pow_add, Nat.sub_add_cancel h.six_le]
    calc t % 2 ^ (logN - WhirBridge.laneFold) + 2 ^ (logN - WhirBridge.laneFold) * l
        < 2 ^ (logN - WhirBridge.laneFold) * (l + 1) := by rw [Nat.mul_succ]; omega
      _ ≤ 2 ^ (logN - WhirBridge.laneFold) * 2 ^ WhirBridge.laneFold := Nat.mul_le_mul_left _ hl64
      _ = 2 ^ logN := hpow
  have hcol : ∀ x < 2 ^ logN, (E2ECompleteness.colOf logN stack).values.getD x 0 = stack.getD x 0 := by
    intro x hx
    simp [E2ECompleteness.colOf, Vector.getD, hx]
  refine htab.trans ?_
  unfold PcsQuotient.Layout.readEntry
  simp only [ofChunks_logPiece]
  split
  · rename_i l hfind
    rw [List.findIdx?_eq_some_iff_getElem] at hfind
    obtain ⟨hl0, hp, -⟩ := hfind
    have hl : l < (WhirBridge.Layout.newBlocks lc logN chunks).length := by
      have := hl0; rw [ofChunks_lanes h, List.length_map] at this; exact this
    have hlb : (WhirBridge.Layout.newBlocks lc logN chunks)[l] = t / 2 ^ (logN - WhirBridge.laneFold) := by
      have e : (PcsQuotient.Layout.ofChunks vars lc logN chunks).lanes[l] =
          PcsQuotient.Lane.block (WhirBridge.Layout.newBlocks lc logN chunks)[l] := by
        simp only [ofChunks_lanes h, List.getElem_map]
      simp only [decide_eq_true_eq, e, PcsQuotient.Lane.block.injEq] at hp
      exact hp
    refine (WhirBridge.Blocks.table_eq_lane (WhirBridge.Layout.new vars lc logN chunks).toBlocks
      (by rw [hB]; exact hnd) (E2ECompleteness.colOf logN stack) (l := l)
      (by show l < (WhirBridge.Layout.new vars lc logN chunks).toBlocks.blocks.length; rw [hB]; exact hl)
      (by rw [hB, hℓ, List.getD_eq_getElem _ _ hl, hlb])).trans ?_
    rw [hℓ]
    refine Eq.trans (hcol _ (hlt l hl)) ?_
    show stack.getD _ 0 = stack.getD (l * 2 ^ (logN - WhirBridge.laneFold) + t % 2 ^ (logN - WhirBridge.laneFold)) 0
    congr 1
    ring
  · rename_i hfind
    refine WhirBridge.Blocks.table_eq_zero _ _ ?_
    rw [hB, hℓ]
    intro hb
    obtain ⟨l, hl, hlb⟩ := List.getElem_of_mem hb
    rw [List.findIdx?_eq_none_iff] at hfind
    have hmem : PcsQuotient.Lane.block (WhirBridge.Layout.newBlocks lc logN chunks)[l] ∈
        (PcsQuotient.Layout.ofChunks vars lc logN chunks).lanes := by
      rw [ofChunks_lanes h]
      exact List.mem_map_of_mem (List.getElem_mem hl)
    have := hfind _ hmem
    simp only [decide_eq_false_iff_not, PcsQuotient.Lane.block.injEq] at this
    exact this hlb

/-! ## The stack claims -/

/-- **The claims that hold of the stack are its opening's stack claims, in WHIR's semantics.** -/
theorem ofChunks_stackClaims_hold (h : WhirBridge.NewOK vars lc logN chunks) (hd : (chunks.map Prod.fst).Nodup)
    (stack : Array K) (claims : List PcsQuotient.Claim)
    (hcl : ∀ c ∈ claims, c.point.length = vars ∧
      ClaimOn (PcsQuotient.Layout.ofChunks vars lc logN chunks) (fun j ↦ stack.getD j 0) (c.point, c.value)) :
    ∀ sc ∈ PcsQuotient.stackClaims (PcsQuotient.Layout.ofChunks vars lc logN chunks) claims,
      EndToEnd.StackClaim.Holds logN sc (E2ECompleteness.colOf logN stack) := by
  have hOK : Bridge.LayoutOK (PcsQuotient.Layout.ofChunks vars lc logN chunks) := Or.inl rfl
  have hval := WhirBridge.Layout.new_valid h
  intro sc hsc
  rw [Bridge.stackClaims_eq _ hOK claims, layoutTr_ofChunks h] at hsc
  rcases List.mem_append.1 hsc with hm | hm
  · obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hm
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
    refine ((WhirBridge.Layout.new vars lc logN chunks).holds_iff hval (Bridge.claimTr c) (hcl c hc).1 _).2 ?_
    refine Eq.trans ?_ (hcl c hc).2
    unfold WhirBridge.Layout.tableEval
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [table_new_eq h hd stack t, Bridge.eqBits_eq, WhirBridge.eqBits_eq_boolPoint, mul_comm]
    rw [show (Bridge.claimTr c).point = c.point from rfl, (hcl c hc).1]
    rfl
  · change sc ∈ (WhirBridge.Layout.new vars lc logN chunks).extra at hm
    rw [WhirBridge.Layout.extra_of_none rfl] at hm
    exact absurd hm List.not_mem_nil

/-- **Every stack claim of a public layout has a multilinear weight** (F2's multiaffine weights). -/
theorem ofChunks_multilinear (claims : List PcsQuotient.Claim) :
    ∀ sc ∈ PcsQuotient.stackClaims (PcsQuotient.Layout.ofChunks vars lc logN chunks) claims,
      EndToEnd.IsMultilinearFn logN sc.1 := by
  intro sc hsc
  rw [Bridge.stackClaims_eq _ (Or.inl rfl) claims] at hsc
  exact Completeness.isMultilinearFn_of_isMultiaffine
    ((Bridge.layoutTr (PcsQuotient.Layout.ofChunks vars lc logN chunks)).stacking.isMultiaffine_claims
      (claims.map Bridge.claimTr) sc hsc)

/-- **A public layout of chunks has the weight table's shape**, for `log_n ≤ 64`. -/
theorem weightShape_ofChunks (h : WhirBridge.NewOK vars lc logN chunks) (h64 : logN ≤ 64) :
    E2ECompleteness.WeightShape (PcsQuotient.Layout.ofChunks vars lc logN chunks) := by
  refine ⟨h.six_le, h64, ?_, ?_, fun s hs ↦ by simp [ofChunks_logPiece] at hs⟩
  · rw [ofChunks_lanes h, List.length_map, WhirBridge.newBlocks_length]
    exact h.lanes_le
  · show logN - WhirBridge.laneFold ≤ vars
    exact h.lane_le.trans h.chunk_le

/-! ## The honest openings -/

/-- **An honest opening at a public layout of chunks is accepted**: every proof `proveOpeningWithH` makes of true
claims on the stack's commitment is accepted against the commitment's root. -/
theorem ofChunks_open_honest (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ)
    (h : WhirBridge.NewOK vars lc logN chunks) (hd : (chunks.map Prod.fst).Nodup) (h64 : logN ≤ 64)
    (hw : Whir.Admissible logN PcsQuotient.logInvRate) (stack : Array K) (claims : List PcsQuotient.Claim)
    (hne : claims ≠ [])
    (hcl : ∀ c ∈ claims, c.point.length = vars ∧
      ClaimOn (PcsQuotient.Layout.ofChunks vars lc logN chunks) (fun j ↦ stack.getD j 0) (c.point, c.value))
    {π : Compile.Proof}
    (hπ : E2ECompleteness.proveOpeningWithH (m := Id) H F fuel (PcsQuotient.Layout.ofChunks vars lc logN chunks)
      (E2ECompleteness.commitWithH (m := Id) H logN stack) stack claims = some π) :
    E2ECompleteness.openingWithH (m := Id) H F (PcsQuotient.Layout.ofChunks vars lc logN chunks)
      (E2ECompleteness.commitWithH (m := Id) H logN stack).root claims π = true :=
  E2ECompleteness.openingWithH_proveOpeningWithH H F fuel _ (weightShape_ofChunks h h64) hw stack claims hne
    (fun c hc ↦ (hcl c hc).1) (ofChunks_stackClaims_hold h hd stack claims hcl) (ofChunks_multilinear claims) hπ

/-- **The prover fails only at a proof of work**, at a public layout of chunks. -/
theorem ofChunks_fails_only_at_pow (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ)
    (h : WhirBridge.NewOK vars lc logN chunks) (h64 : logN ≤ 64) (hw : Whir.Admissible logN PcsQuotient.logInvRate)
    (stack : Array K) (claims : List PcsQuotient.Claim) (hlen : ∀ c ∈ claims, c.point.length = vars)
    (hn : E2ECompleteness.proveOpeningWithH (m := Id) H F fuel (PcsQuotient.Layout.ofChunks vars lc logN chunks)
      (E2ECompleteness.commitWithH (m := Id) H logN stack) stack claims = none) :
    ∃ hist k sp, (Whir.Complete.openingProgram logN PcsQuotient.logInvRate
        (PcsQuotient.stackClaims (PcsQuotient.Layout.ofChunks vars lc logN chunks) claims)).after hist =
          some (.grind Whir.queryGrindingBits k) ∧
      ∀ n < fuel, powOk Whir.queryGrindingBits (Compile.nonceOf n)
        (Compile.powStep F sp (Compile.nonceOf n)).1 = false :=
  E2ECompleteness.exists_failed_pow_opening H F fuel _ (weightShape_ofChunks h h64) hw stack claims hlen hn

end Chunks

/-! ## π2's layouts -/

/-- **π2's three layouts at `m = 24`** (`prover::layouts(24)`): `W`, `Q`, the setup. -/
theorem layoutsOf_24 : RecStatement.layoutsOf 24 =
    (PcsQuotient.Layout.ofChunks 24 24 24 [(0, 2 ^ 24)],
      PcsQuotient.Layout.ofChunks 29 24 28 (RecStatement.quotientChunks 24),
      PcsQuotient.Layout.ofChunks 25 24 25 [(0, 2 ^ 24), (1, 2 ^ 24)]) := rfl

theorem newOK_w : WhirBridge.NewOK 24 24 24 [(0, 2 ^ 24)] := by decide +kernel

theorem newOK_q : WhirBridge.NewOK 29 24 28 (RecStatement.quotientChunks 24) := by decide +kernel

theorem newOK_s : WhirBridge.NewOK 25 24 25 [(0, 2 ^ 24), (1, 2 ^ 24)] := by decide +kernel

theorem nodup_w : ([(0, 2 ^ 24)].map Prod.fst : List ℕ).Nodup := by decide +kernel

theorem nodup_q : ((RecStatement.quotientChunks 24).map Prod.fst).Nodup := by decide +kernel

theorem nodup_s : ([(0, 2 ^ 24), (1, 2 ^ 24)].map Prod.fst : List ℕ).Nodup := by decide +kernel

/-- **A π2 layout**: `vars`, chunk size, stack size and chunks that `Layout::new` accepts, distinct chunks, a stack
of `2^24 … 2^28` words. -/
structure Pi2Layout (L : PcsQuotient.Layout) : Prop where
  ex : ∃ vars lc logN chunks, L = PcsQuotient.Layout.ofChunks vars lc logN chunks ∧
    WhirBridge.NewOK vars lc logN chunks ∧ (chunks.map Prod.fst).Nodup ∧ 24 ≤ logN ∧ logN ≤ 28

theorem pi2Layout_w : Pi2Layout (RecStatement.layoutsOf 24).1 := by
  rw [layoutsOf_24]
  exact ⟨⟨24, 24, 24, _, rfl, newOK_w, nodup_w, le_rfl, by norm_num⟩⟩

theorem pi2Layout_q : Pi2Layout (RecStatement.layoutsOf 24).2.1 := by
  rw [layoutsOf_24]
  exact ⟨⟨29, 24, 28, _, rfl, newOK_q, nodup_q, by norm_num, le_rfl⟩⟩

theorem pi2Layout_s : Pi2Layout (RecStatement.layoutsOf 24).2.2 := by
  rw [layoutsOf_24]
  exact ⟨⟨25, 24, 25, _, rfl, newOK_s, nodup_s, by norm_num, by norm_num⟩⟩

/-- **The honest opening at π2's layouts is accepted** (pure `H`, `F`). -/
theorem pi2Open_honest (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ) {L : PcsQuotient.Layout}
    (hL : Pi2Layout L) (stack : Array K) (claims : List PcsQuotient.Claim) (hne : claims ≠ [])
    (hcl : ∀ c ∈ claims, c.point.length = L.vars ∧ ClaimOn L (fun j ↦ stack.getD j 0) (c.point, c.value))
    {π : Compile.Proof}
    (hπ : E2ECompleteness.proveOpeningWithH (m := Id) H F fuel L
      (E2ECompleteness.commitWithH (m := Id) H L.logN stack) stack claims = some π) :
    E2ECompleteness.openingWithH (m := Id) H F L (E2ECompleteness.commitWithH (m := Id) H L.logN stack).root
      claims π = true := by
  obtain ⟨⟨vars, lc, logN, chunks, rfl, hok, hd, h24, h28⟩⟩ := hL
  exact ofChunks_open_honest H F fuel hok hd (by omega) (WhirBridge.admissible_large h24 h28) stack claims hne hcl hπ

/-- **`PCS_OPEN` accepts π2's honest openings**: the Statement's `openingWith` over `F` (Keccak-256 the sponge over
`F`) accepts every proof the Statement's `proveOpeningWith` makes of true claims on the stack's `commitWith`. -/
theorem pi2OpeningWith_honest (F : KeccakState → KeccakState) (fuel : ℕ) {L : PcsQuotient.Layout}
    (hL : Pi2Layout L) (stack : Array K) (claims : List PcsQuotient.Claim) (hne : claims ≠ [])
    (hcl : ∀ c ∈ claims, c.point.length = L.vars ∧ ClaimOn L (fun j ↦ stack.getD j 0) (c.point, c.value))
    {π : Compile.Proof}
    (hπ : PcsQuotient.proveOpeningWith (m := Id) (fun s ↦ pure (F s)) fuel L
      (PcsQuotient.commitWith (m := Id) (fun s ↦ pure (F s)) L.logN stack) stack claims = some π) :
    PcsQuotient.openingWith (m := Id) (fun s ↦ pure (F s)) L
      (PcsQuotient.commitWith (m := Id) (fun s ↦ pure (F s)) L.logN stack).root claims π = true := by
  rw [E2ECompleteness.proveOpeningWith_eqH, E2ECompleteness.commitWith_eqH] at hπ
  rw [E2ECompleteness.commitWith_eqH, E2ECompleteness.openingWith_eqH]
  exact pi2Open_honest _ F fuel hL stack claims hne hcl hπ

/-- **π2's opening prover fails only at a proof of work.** -/
theorem pi2Open_fails_only_at_pow (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ)
    {L : PcsQuotient.Layout} (hL : Pi2Layout L) (stack : Array K) (claims : List PcsQuotient.Claim)
    (hlen : ∀ c ∈ claims, c.point.length = L.vars)
    (hn : E2ECompleteness.proveOpeningWithH (m := Id) H F fuel L
      (E2ECompleteness.commitWithH (m := Id) H L.logN stack) stack claims = none) :
    ∃ hist k sp, (Whir.Complete.openingProgram L.logN PcsQuotient.logInvRate
        (PcsQuotient.stackClaims L claims)).after hist = some (.grind Whir.queryGrindingBits k) ∧
      ∀ n < fuel, powOk Whir.queryGrindingBits (Compile.nonceOf n)
        (Compile.powStep F sp (Compile.nonceOf n)).1 = false := by
  obtain ⟨⟨vars, lc, logN, chunks, rfl, hok, hd, h24, h28⟩⟩ := hL
  exact ofChunks_fails_only_at_pow H F fuel hok (by omega) (WhirBridge.admissible_large h24 h28) stack claims hlen hn

end RecCompose.Pi2W

/-! ## Axioms -/

/-- info: 'RecCompose.Pi2W.table_new_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RecCompose.Pi2W.table_new_eq

/-- info: 'RecCompose.Pi2W.ofChunks_stackClaims_hold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RecCompose.Pi2W.ofChunks_stackClaims_hold

/-- info: 'RecCompose.Pi2W.pi2Open_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RecCompose.Pi2W.pi2Open_honest

/-- info: 'RecCompose.Pi2W.pi2OpeningWith_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RecCompose.Pi2W.pi2OpeningWith_honest

/-- info: 'RecCompose.Pi2W.pi2Open_fails_only_at_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RecCompose.Pi2W.pi2Open_fails_only_at_pow
