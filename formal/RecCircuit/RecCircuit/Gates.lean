-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecCircuit.PolySem

/-!
# The units' values on a satisfied circuit

From `gate_val` and the formulas' semantics: a constant is its `κ`, a free bit is a bit (`b = b²` in the field `K`),
a copy is its bit, an XOR is the sum. A checked D16v Keccak-f instance satisfies `D16Rel` (`keccak_rel`), so on bits
its output is `keccakF` of its input (`keccak_out`, from `KeccakMath.d16_keccakF`).
-/

namespace RecCircuit

open Primitives PcsCircuit.Builder

namespace Ctx

variable (X : Ctx)

/-- **What the theorems assume of a witness**: the view checked, the dense `κ` the circuit's, the circuit satisfied. -/
structure Good (w : ℕ → K) : Prop where
  view : X.viewOk = true
  kd : X.kd = denseKappa X.C
  sat : X.C.Satisfied w

variable {X} {w : ℕ → K}

theorem Good.gate (G : X.Good w) {v : ℕ} {p : Poly} {k : K} {cells : List (ℕ × ℕ)} (h : X.gate v p k cells = true) :
    X.val w v = p.eval (X.cellVal w cells) + k := X.gate_val G.view G.kd G.sat h

theorem cellVal_cons_self (c u : ℕ) (rest : List (ℕ × ℕ)) : X.cellVal w ((c, u) :: rest) c = X.val w u := by
  simp [cellVal]

theorem cellVal_cons_ne {c c' : ℕ} (u : ℕ) (rest : List (ℕ × ℕ)) (h : c' ≠ c) :
    X.cellVal w ((c, u) :: rest) c' = X.cellVal w rest c' := by
  have : (c' == c) = false := by simpa using h
  simp [cellVal, List.lookup_cons, this]

theorem cellVal_append_left {l₁ l₂ : List (ℕ × ℕ)} {c : ℕ} (h : (l₁.lookup c).isSome) :
    X.cellVal w (l₁ ++ l₂) c = X.cellVal w l₁ c := by
  unfold cellVal
  rw [List.lookup_append]
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp h
  rw [hu]; rfl

theorem cellVal_append_right {l₁ l₂ : List (ℕ × ℕ)} {c : ℕ} (h : l₁.lookup c = none) :
    X.cellVal w (l₁ ++ l₂) c = X.cellVal w l₂ c := by
  unfold cellVal
  rw [List.lookup_append, h]; rfl

theorem lookup_range_map (g : ℕ → ℕ) (b : ℕ) :
    ∀ (n y : ℕ), y < n → ((List.range n).map fun i => (b + i, g i)).lookup (b + y) = some (g y)
  | 0, y, h => absurd h (Nat.not_lt_zero _)
  | n + 1, y, h => by
    rw [List.range_succ, List.map_append, List.lookup_append]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · rw [lookup_range_map g b n y h]; rfl
    · have : ((List.range y).map fun i => (b + i, g i)).lookup (b + y) = none := by
        rw [List.lookup_eq_none_iff]
        intro p hp
        simp only [List.mem_map, List.mem_range] at hp
        obtain ⟨i, hi, rfl⟩ := hp
        simp; omega
      rw [this]; simp

theorem lookup_range_map_none (g : ℕ → ℕ) (b n c : ℕ) (h : c < b ∨ b + n ≤ c) :
    ((List.range n).map fun i => (b + i, g i)).lookup c = none := by
  rw [List.lookup_eq_none_iff]
  intro p hp
  simp only [List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  simp; omega

/-! ## Units -/

theorem const_val (G : X.Good w) {v : ℕ} {k : K} (h : X.constOk v k = true) : X.val w v = k := by
  rw [G.gate h, eval_spare, zero_add]

theorem bit_sq (G : X.Good w) {v : ℕ} (h : X.bitOk v = true) : X.val w v = X.val w v * X.val w v := by
  have e := G.gate h
  rw [eval_sq, add_zero, cellVal_cons_self] at e
  exact e

/-- In the field `K`, `b = b²` makes `b` a bit. -/
theorem isBit_of_sq {x : K} (h : x = x * x) : x = 0 ∨ x = 1 := by
  have : x * (x - 1) = 0 := by linear_combination -h
  rcases mul_eq_zero.mp this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

theorem bit_isBit (G : X.Good w) {v : ℕ} (h : X.bitOk v = true) : X.val w v = 0 ∨ X.val w v = 1 :=
  isBit_of_sq (bit_sq G h)

theorem copy_val (G : X.Good w) {v c : ℕ} (h : X.copyOk v c = true) : X.val w c = X.val w v := by
  simp only [copyOk, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [G.gate h.2, eval_copy, add_zero, cellVal_cons_self]

theorem xor_val (G : X.Good w) {x a b : ℕ} (h : X.xorOk x a b = true) : X.val w x = X.val w a + X.val w b := by
  rw [G.gate h, eval_xor, add_zero, cellVal_cons_self, cellVal_cons_ne _ _ (by omega), cellVal_cons_self]

/-! ## D16v's Keccak-f -/

/-- The χ row's cells: cell `x'` holds θ's lane input, cell `5 + x'` its D. -/
theorem chiCells_lookup (a d : Array Val) (y z x : ℕ) (hx : x < 5) :
    (chiCells a d y z).lookup x = some (a.getD (64 * piInv (x + 5 * y) + (z + 64 - rho (piInv (x + 5 * y))) % 64) NONE) ∧
    (chiCells a d y z).lookup (5 + x) =
      some (d.getD (64 * (piInv (x + 5 * y) % 5) + (z + 64 - rho (piInv (x + 5 * y))) % 64) NONE) := by
  interval_cases x <;> simp [chiCells, List.range_succ, List.lookup_cons]

theorem chiCells_lookup_10 (a d : Array Val) (y z x : ℕ) : (chiCells a d y z).lookup (10 + x) = none := by
  simp only [chiCells, List.lookup_eq_none_iff, List.mem_flatMap, List.mem_range]
  intro p hp
  obtain ⟨i, hi, hp⟩ := hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> simp <;> omega

/-- `χ`'s gate on the row's cells: `chiOut` of θ's outputs there. -/
theorem chi_cells_eval (a d : Array Val) (y z x : ℕ) (hx : x < 5) :
    (Builder.chiB x).build.eval (X.cellVal w (chiCells a d y z)) =
      chiOut (fun x' => chiIn (fun l z => X.val w (a.getD (64 * l + z) NONE))
        (fun x z => X.val w (d.getD (64 * x + z) NONE)) x' y z) x := by
  have e := fun x' (h : x' < 5) => chiCells_lookup a d y z x' h
  have hc : ∀ x' < 5, X.cellVal w (chiCells a d y z) x' + X.cellVal w (chiCells a d y z) (5 + x') =
      chiIn (fun l z => X.val w (a.getD (64 * l + z) NONE)) (fun x z => X.val w (d.getD (64 * x + z) NONE)) x' y z := by
    intro x' h
    simp only [cellVal, (e x' h).1, (e x' h).2, Option.getD_some, chiIn]
  rw [chiB_eval, hc x hx, hc _ (Nat.mod_lt _ (by norm_num)), hc _ (Nat.mod_lt _ (by norm_num)), chiOut]

/-- The values of a Keccak-f trace, as `D16Rel`'s functions. -/
def KeccakT.A (X : Ctx) (w : ℕ → K) (t : KeccakT) (j l z : ℕ) : K := X.val w ((t.a.getD j #[]).getD (64 * l + z) NONE)
def KeccakT.Cf (X : Ctx) (w : ℕ → K) (t : KeccakT) (j x z : ℕ) : K := X.val w ((t.c.getD j #[]).getD (64 * x + z) NONE)
def KeccakT.Df (X : Ctx) (w : ℕ → K) (t : KeccakT) (j x z : ℕ) : K := X.val w ((t.d.getD j #[]).getD (64 * x + z) NONE)

theorem keccakOk_parts {t : KeccakT} (h : X.keccakOk t = true) :
    (∀ u < 320, 5 ≤ X.role ((t.c.getD 0 #[]).getD u NONE) ∧
      X.gate ((t.c.getD 0 #[]).getD u NONE) (sumPolyL (X.role ((t.c.getD 0 #[]).getD u NONE) - 5)) 0
      ((List.range 5).map fun y => (X.role ((t.c.getD 0 #[]).getD u NONE) - 5 + y,
        (t.a.getD 0 #[]).getD (64 * (u / 64 + 5 * y) + u % 64) NONE)) = true) ∧
    (∀ j < 24, ∀ u < 320, X.gate ((t.d.getD j #[]).getD u NONE) (xorPolyL (X.role ((t.d.getD j #[]).getD u NONE))) 0
      [(X.role ((t.d.getD j #[]).getD u NONE), (t.c.getD j #[]).getD (64 * ((u / 64 + 4) % 5) + u % 64) NONE),
       (X.role ((t.d.getD j #[]).getD u NONE) + 1,
        (t.c.getD j #[]).getD (64 * ((u / 64 + 1) % 5) + (u % 64 + 63) % 64) NONE)] = true) ∧
    (∀ j < 24, ∀ y < 5, ∀ u < 320,
      X.gate ((t.a.getD (j + 1) #[]).getD (64 * (u / 64 + 5 * y) + u % 64) NONE) (Builder.chiB (u / 64)).build
        (if u / 64 == 0 then (if y == 0 then rcBit j (u % 64) else 0) else 0)
        (chiCells (t.a.getD j #[]) (t.d.getD j #[]) y (u % 64)) = true ∧
      (if y == 0 then X.gate (((t.p.getD j #[]).getD 0 #[]).getD u NONE) (Builder.chiB (u / 64)).build
          (if u / 64 == 0 then (if y == 0 then rcBit j (u % 64) else 0) else 0)
          (chiCells (t.a.getD j #[]) (t.d.getD j #[]) y (u % 64))
       else X.gate (((t.p.getD j #[]).getD y #[]).getD u NONE) ((Builder.chiB (u / 64)).addLinear (10 + u / 64) 1).build 0
          (chiCells (t.a.getD j #[]) (t.d.getD j #[]) y (u % 64) ++
            [(10 + u / 64, ((t.p.getD j #[]).getD (y - 1) #[]).getD u NONE)])) = true) ∧
    (∀ j < 23, ∀ u < 320, (t.c.getD (j + 1) #[]).getD u NONE = ((t.p.getD j #[]).getD 4 #[]).getD u NONE) := by
  unfold keccakOk at h
  beta_reduce at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := (Bool.and_eq_true _ _ ▸ h : _ ∧ _) |>.imp_left
    (fun h => (Bool.and_eq_true _ _ ▸ h : _ ∧ _) |>.imp_left (fun h => (Bool.and_eq_true _ _ ▸ h : _ ∧ _)))
  refine ⟨fun u hu => ?_, fun j hj u hu => ?_, fun j hj y hy u hu => ?_, fun j hj u hu => ?_⟩
  · have := allBelow_spec h0 u hu
    exact (Bool.and_eq_true _ _ ▸ this : _ ∧ _).imp_left (fun h => of_decide_eq_true h)
  · exact allBelow_spec (allBelow_spec h1 j hj) u hu
  · have := allBelow_spec (allBelow_spec (allBelow_spec h2 j hj) y hy) u hu
    exact (Bool.and_eq_true _ _ ▸ this : _ ∧ _)
  · have := allBelow_spec (allBelow_spec h3 j hj) u hu
    exact of_decide_eq_true (by simpa using this)

/-- **A checked Keccak-f instance satisfies D16v's relations.** -/
theorem keccak_rel (G : X.Good w) {t : KeccakT} (h : X.keccakOk t = true) :
    D16Rel (KeccakT.A X w t) (KeccakT.Cf X w t) (KeccakT.Df X w t) := by
  obtain ⟨h0, hd, hchi, hc⟩ := keccakOk_parts h
  -- The χ rows' values.
  have chiA : ∀ j < 24, ∀ x < 5, ∀ y < 5, ∀ z < 64, KeccakT.A X w t (j + 1) (x + 5 * y) z =
      chiOut (fun x' => chiIn (KeccakT.A X w t j) (KeccakT.Df X w t j) x' y z) x +
        (if x = 0 ∧ y = 0 then rcBit j z else 0) := by
    intro j hj x hx y hy z hz
    have hu : 64 * x + z < 320 := by omega
    have := (hchi j hj y hy (64 * x + z) hu).1
    have e1 : (64 * x + z) / 64 = x := by omega
    have e2 : (64 * x + z) % 64 = z := by omega
    rw [e1, e2] at this
    rw [KeccakT.A, G.gate this, chi_cells_eval _ _ _ _ _ hx]
    have hk : (if (x == 0) = true then (if (y == 0) = true then rcBit j z else 0) else 0) =
        (if x = 0 ∧ y = 0 then rcBit j z else 0) := by
      by_cases h0 : x = 0 <;> by_cases h1 : y = 0 <;> simp [h0, h1]
    rw [hk]; rfl
  -- The partial sums: `P_0 = A_(j+1)[x]`, `P_y = A_(j+1)[x + 5y] + P_(y−1)`.
  have hP : ∀ j < 24, ∀ x < 5, ∀ z < 64, ∀ y < 5,
      X.val w (((t.p.getD j #[]).getD y #[]).getD (64 * x + z) NONE) =
        (List.range (y + 1)).foldl (fun acc y' => acc + KeccakT.A X w t (j + 1) (x + 5 * y') z) 0 := by
    intro j hj x hx z hz y
    induction y with
    | zero =>
      intro _
      have hu : 64 * x + z < 320 := by omega
      have h2 := (hchi j hj 0 (by norm_num) (64 * x + z) hu)
      have e1 : (64 * x + z) / 64 = x := by omega
      have e2 : (64 * x + z) % 64 = z := by omega
      rw [e1, e2] at h2
      simp only [beq_self_eq_true, ite_true] at h2
      rw [G.gate h2.2, List.range_one, List.foldl_cons, List.foldl_nil, zero_add, KeccakT.A, G.gate h2.1]
    | succ y ih =>
      intro hy
      have hu : 64 * x + z < 320 := by omega
      have h2 := (hchi j hj (y + 1) hy (64 * x + z) hu)
      have e1 : (64 * x + z) / 64 = x := by omega
      have e2 : (64 * x + z) % 64 = z := by omega
      rw [e1, e2] at h2
      have hne : (y + 1 == 0) = false := by simp
      simp only [hne, Bool.false_eq_true, ite_false, ite_self, Nat.add_sub_cancel] at h2
      rw [G.gate h2.2, chiB_addLinear_eval, add_zero, List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil, ← ih (by omega), KeccakT.A, G.gate h2.1, add_zero]
      have hl := chiCells_lookup_10 (t.a.getD j #[]) (t.d.getD j #[]) (y + 1) z x
      rw [cellVal_append_right hl, cellVal_cons_self]
      have hev : (Builder.chiB x).build.eval
            (X.cellVal w (chiCells (t.a.getD j #[]) (t.d.getD j #[]) (y + 1) z ++ [(10 + x, ((t.p.getD j #[]).getD y #[]).getD (64 * x + z) NONE)])) =
          (Builder.chiB x).build.eval (X.cellVal w (chiCells (t.a.getD j #[]) (t.d.getD j #[]) (y + 1) z)) := by
        rw [chiB_eval, chiB_eval]
        have hs : ∀ c < 10, X.cellVal w (chiCells (t.a.getD j #[]) (t.d.getD j #[]) (y + 1) z ++
            [(10 + x, ((t.p.getD j #[]).getD y #[]).getD (64 * x + z) NONE)]) c =
            X.cellVal w (chiCells (t.a.getD j #[]) (t.d.getD j #[]) (y + 1) z) c := by
          intro c hc
          apply cellVal_append_left
          rcases Nat.lt_or_ge c 5 with h5 | h5
          · rw [(chiCells_lookup _ _ _ _ c h5).1]; rfl
          · have := (chiCells_lookup (t.a.getD j #[]) (t.d.getD j #[]) (y + 1) z (c - 5) (by omega)).2
            rw [show 5 + (c - 5) = c by omega] at this
            rw [this]; rfl
        have m1 : (x + 1) % 5 < 5 := Nat.mod_lt _ (by norm_num)
        have m2 : (x + 2) % 5 < 5 := Nat.mod_lt _ (by norm_num)
        rw [hs x (by omega), hs (5 + x) (by omega), hs _ (by omega), hs (5 + (x + 2) % 5) (by omega),
          hs _ (by omega), hs (5 + (x + 1) % 5) (by omega)]
      rw [hev]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- C_0: kprep's column sums.
    intro x hx z hz
    have hu : 64 * x + z < 320 := by omega
    obtain ⟨h5, hg⟩ := h0 (64 * x + z) hu
    have e1 : (64 * x + z) / 64 = x := by omega
    have e2 : (64 * x + z) % 64 = z := by omega
    rw [e1, e2] at hg
    rw [KeccakT.Cf, G.gate hg, eval_sum, add_zero]
    have L := fun y (h : y < 5) => lookup_range_map (fun y => (t.a.getD 0 #[]).getD (64 * (x + 5 * y) + z) NONE)
      (X.role ((t.c.getD 0 #[]).getD (64 * x + z) NONE) - 5) 5 y h
    have L0 := L 0 (by norm_num)
    rw [Nat.add_zero] at L0
    simp only [cellVal]
    rw [L0, L 1 (by norm_num), L 2 (by norm_num), L 3 (by norm_num), L 4 (by norm_num)]
    simp [colSum, KeccakT.A]
  · -- C_(j+1) = P_(j, 4), the column parity of A_(j+1).
    intro j hj x hx z hz
    have hu : 64 * x + z < 320 := by omega
    rw [KeccakT.Cf, hc j hj (64 * x + z) hu, hP j (by omega) x hx z hz 4 (by norm_num)]
    simp [List.range_succ, colSum]
  · -- D units.
    intro j hj x hx z hz
    have hu : 64 * x + z < 320 := by omega
    have hg := hd j hj (64 * x + z) hu
    have e1 : (64 * x + z) / 64 = x := by omega
    have e2 : (64 * x + z) % 64 = z := by omega
    rw [e1, e2] at hg
    rw [KeccakT.Df, G.gate hg, eval_xor, add_zero, cellVal_cons_self, cellVal_cons_ne _ _ (by omega),
      cellVal_cons_self]
    rfl
  · exact chiA

/-- **A checked Keccak-f instance computes Keccak-f[1600] on bits.** -/
theorem keccak_out (G : X.Good w) {t : KeccakT} (h : X.keccakOk t = true) (s : PcsCircuit.Bits)
    (hs : ∀ l < 25, ∀ z < 64, KeccakT.A X w t 0 l z = ofBool (s l z)) :
    ∀ l < 25, ∀ z < 64, KeccakT.A X w t 24 l z = ofBool (PcsCircuit.KeccakBits.keccakF s l z) :=
  d16_keccakF (keccak_rel G h) s hs

end Ctx

end RecCircuit
