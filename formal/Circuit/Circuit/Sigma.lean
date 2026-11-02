/-
Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-/
import Circuit.Final
import Circuit.Wiring

/-!
# The deployed σ

`membership.sigma`, the wiring `finish` builds (and the Rust's, `CircuitTest/Dump.lean`), is a
permutation of the `4 · 2^22` cells (`membership_sigma_lt`, `membership_sigma_inj`), and every
`X`, `Y`, `C` cell is on the cycle of what it reads (`membership_sigma_reads`): the `V` cell
`4 r' + 3` of the row `r'` it reads, or the constant's anchor, cell `4 · 320` (bit 0 of word 5) for
the zero and `4 · 256` (bit 0 of word 4) for the one.
-/

namespace PcsCircuit

attribute [local irreducible] runB IsRow Below Valid membership

/-- The cell whose cycle carries what a cell reads. -/
def anchorN : Src → Nat
  | .zero => 4 * 320
  | .one => 4 * 256
  | .row r => 4 * r + 3

theorem finish_sigma' (b : Builder) (pub : Nat → Nat → Src) (L : Nat) :
    (b.finish L pub).sigma = wiring (b.finish L pub).rows := rfl

theorem finish_sigma (b : Builder) (pub : Nat → Nat → Src) :
    (b.finish logRows pub).sigma = wiring (b.finish logRows pub).rows := finish_sigma' b pub logRows

theorem membership_sigma : membership.sigma = wiring membership.rows := by
  obtain ⟨y, root, bf, he, -⟩ := membership_spec
  rw [he]; exact finish_sigma _ _

theorem ranked_slot {rk : Nat} {s : Src} (h : Ranked rk s) : slot s < 2 ^ logRows + 2 := by
  cases s with
  | zero => simp [slot]
  | one => simp [slot]
  | row r => unfold Ranked at h; show 2 + r < 2 ^ logRows + 2; omega

theorem membership_hsrc : ∀ r < membership.rows.size,
    slot (membership.rows.getD r .idle).x < membership.rows.size + 2 ∧
    slot (membership.rows.getD r .idle).y < membership.rows.size + 2 ∧
    slot (membership.rows.getD r .idle).c < membership.rows.size + 2 := by
  intro r hr
  rw [membership_rows_size] at hr ⊢
  by_cases hin : r ∈ membership.inputs
  · obtain ⟨-, -, hrow⟩ := membership_input_row r hin
    rw [hrow]; show 2 + r < 2 ^ logRows + 2 ∧ 2 + r < 2 ^ logRows + 2 ∧ 2 + r < 2 ^ logRows + 2; omega
  · obtain ⟨hx, hy, hc⟩ := membership_order r hr hin
    exact ⟨ranked_slot hx, ranked_slot hy, ranked_slot hc⟩

theorem membership_sigma_perm :
    (∀ c < 4 * 2 ^ logRows, membership.sigma.getD c 0 < 4 * 2 ^ logRows) ∧
    (∀ c < 4 * 2 ^ logRows, ∀ d < 4 * 2 ^ logRows, membership.sigma.getD c 0 = membership.sigma.getD d 0 → c = d) ∧
    (∀ c < 4 * 2 ^ logRows, ∀ d < 4 * 2 ^ logRows, slotOfCell membership.rows c = slotOfCell membership.rows d →
      ∃ k, iter (fun x => membership.sigma.getD x 0) k c = d) := by
  have h := wiring_perm membership.rows membership_hsrc
  rw [membership_rows_size, ← membership_sigma] at h
  exact h

/-- **σ maps the cells among themselves.** -/
theorem membership_sigma_lt (c : Nat) (hc : c < 4 * 2 ^ logRows) : membership.sigma.getD c 0 < 4 * 2 ^ logRows :=
  membership_sigma_perm.1 c hc

/-- **σ is injective on the cells.** -/
theorem membership_sigma_inj (c d : Nat) (hc : c < 4 * 2 ^ logRows) (hd : d < 4 * 2 ^ logRows)
    (h : membership.sigma.getD c 0 = membership.sigma.getD d 0) : c = d :=
  membership_sigma_perm.2.1 c hc d hd h

theorem slotOfCell_read (rows : Array Row) (r k : Nat) (hk : k < 3) :
    slotOfCell rows (4 * r + k) =
      slot (if k = 0 then (rows.getD r .idle).x else if k = 1 then (rows.getD r .idle).y
        else (rows.getD r .idle).c) := by
  unfold slotOfCell
  have e1 : (4 * r + k) / 4 = r := by omega
  have e2 : (4 * r + k) % 4 = k := by omega
  rw [e1, e2]
  by_cases h0 : k = 0
  · simp [h0]
  · by_cases h1 : k = 1
    · simp [h1]
    · rw [if_neg h0, if_neg h1, if_pos (by omega), if_neg h0, if_neg h1]

theorem slotOfCell_out (rows : Array Row) (r : Nat) : slotOfCell rows (4 * r + 3) = 2 + r := by
  unfold slotOfCell
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1; omega

/-- **Every reading cell is on the cycle of what it reads.** -/
theorem membership_sigma_reads (r k : Nat) (hr : r < 2 ^ logRows) (hk : k < 3) :
    ∃ m, iter (fun x => membership.sigma.getD x 0) m (4 * r + k) =
      anchorN (if k = 0 then (membership.rows.getD r .idle).x else if k = 1 then (membership.rows.getD r .idle).y
        else (membership.rows.getD r .idle).c) := by
  have hsrc := membership_hsrc r (by rw [membership_rows_size]; exact hr)
  rw [membership_rows_size] at hsrc
  refine membership_sigma_perm.2.2 _ (by omega) _ ?_ ?_
  · generalize hs : (if k = 0 then (membership.rows.getD r .idle).x else if k = 1 then (membership.rows.getD r .idle).y
      else (membership.rows.getD r .idle).c) = s
    have hsl : slot s < 2 ^ logRows + 2 := by
      rw [← hs]; split
      · exact hsrc.1
      · split
        · exact hsrc.2.1
        · exact hsrc.2.2
    cases s with
    | zero => show 4 * 320 < 4 * 2 ^ logRows; unfold logRows; omega
    | one => show 4 * 256 < 4 * 2 ^ logRows; unfold logRows; omega
    | row r' =>
      have : 2 + r' < 2 ^ logRows + 2 := hsl
      show 4 * r' + 3 < 4 * 2 ^ logRows; omega
  · rw [slotOfCell_read _ _ _ hk]
    generalize (if k = 0 then (membership.rows.getD r .idle).x else if k = 1 then (membership.rows.getD r .idle).y
      else (membership.rows.getD r .idle).c) = s
    cases s with
    | zero =>
      have := membership_word5 0 (by decide)
      unfold pubSrcN at this
      simp only [Nat.zero_mod, if_true, Nat.zero_div, Nat.add_zero] at this
      unfold anchorN
      rw [show 4 * 320 = 4 * (64 * 5) + 0 by rfl, slotOfCell_read _ _ _ (by decide)]
      simp only [if_true]
      rw [this]
    | one =>
      have := membership_word4_one
      unfold pubSrcN at this
      simp only [Nat.zero_mod, if_true, Nat.zero_div, Nat.add_zero] at this
      unfold anchorN
      rw [show 4 * 256 = 4 * (64 * 4) + 0 by rfl, slotOfCell_read _ _ _ (by decide)]
      simp only [if_true]
      rw [this]
    | row r' => unfold anchorN; rw [slotOfCell_out]; rfl

end PcsCircuit
