-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Uses `formal/Lv42` (leanerVM `mumbai` f0393df4,
-- MIT OR Apache-2.0): `tupleOf`, `tuplesOn`, `busView` (`Protocol/LeanIsa/Bus.lean`), `toM3_flushes_eq`
-- (leanerVM's `Protocol/ToClean/ComponentPolynomial.lean`); `nameDir`, `nameSep`, `nameView`, `tuplesOn_eq` and
-- `flushesEval_eq` restate `LeanIsa/Bus.lean`'s private `nameDir`, `nameSep`, `nameView`, `tuplesOn_eq` and
-- `tuplesOn_opcode_row`.
import UniComplete.Honest
import UniComplete.Domain
import Lv42.Protocol.LeanIsa.Read
import Lv42.Protocol.LeanIsa.Bus
import Lv42.Protocol.LeanIsa.Complete
import Lv42.Arithmetization.Completeness.Satisfied

/-!
# The mapping's toolkit (milestone 4): constants, forms, tuples

The honest trace (`honestTrace`) is Lv42's stack placed in the univariate PIOP's order; its properties
(`TraceHonest`) are read off Lv42's relation (`M3Honest`). This file holds what every part of that reading uses:

* **The constants** (`gen_eq`, `gpow_eq`, `sepMem_eq`, `sepBytecode_eq`, `ofBits_four`): `layout.rs`'s `E`-constants
  are `K`'s generator's powers, `GEN = ofK g`, `gpow i = (ofK g)^i` (`epow` is square and multiply,
  `epow_eq`), `SEP_MEM = ofK g`, `SEP_BYTECODE = (ofK g)^2`, `K.ofBits 4 = g^2` (the setup's slot `0`); Lv42's
  separators are `gpow 0, 1, 2` of `K` (`channelSep`).
* **Forms at a row** (`formE_*`, `tupleAt_eq`): a form's value is the sum of its terms (`formE_eq_sum`), so the
  `Form` builders of `layout.rs` (`addAt`, `addScaled`, `add`, `sum`, `term`, `col`, `prod`, `constant`) evaluate
  term by term, whatever order the map keeps; a tuple of at most sixteen forms is their values then zeros.
* **Lv42's tuples in `E`** (`phi`, `phi_tupleOf`): a sixteen-slot `K`-tuple, limb by limb in `E`; injective
  (`phi_injective`), so it carries Lv42's balance (a permutation of `K`-tuples) to the PIOP's (of `E`-lists).
* **A table's flushes at a row** (`flushesEval_eq`): Lv42's flush polynomials of an opcode table, evaluated at a
  row and filtered by side, are the tuples its Clean component emits there (`tuplesOn`), which depend only on the
  channels' names and the messages (`tuplesOn_eq`, `nameView`).
-/

namespace UniComplete.Mapping

open UniStatement LeanVM.Parameters

/-! ### The constants -/

theorem ofKZero : ofK 0 = 0 := map_zero (algebraMap K E)

theorem ofKOne : ofK 1 = 1 := map_one (algebraMap K E)

theorem ofKPow (a : K) (n : ℕ) : ofK (a ^ n) = ofK a ^ n := map_pow (algebraMap K E) a n

/-- Square and multiply computes the power: `epowAux fuel base out n = out · base^n` while `n < 2^fuel`. -/
theorem epowAux_eq : ∀ (fuel : ℕ) (base out : E) (n : ℕ), n < 2 ^ fuel →
    epowAux fuel base out n = out * base ^ n
  | 0, base, out, n, h => by
    have : n = 0 := by simpa using h
    subst this
    simp [epowAux]
  | fuel + 1, base, out, n, h => by
    rw [epowAux]
    by_cases h0 : n = 0
    · subst h0
      simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h0),
        epowAux_eq fuel _ _ _ (by rw [pow_succ] at h; omega)]
      conv_rhs => rw [← Nat.div_add_mod n 2, pow_add, pow_mul, sq]
      rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
      · simp [h2]
      · simp only [h2, ite_true, pow_one]
        ring

/-- **`E::pow` is the power.** -/
theorem epow_eq (x : E) (n : ℕ) : epow x n = x ^ n := by
  rw [epow, epowAux_eq _ _ _ _ Nat.lt_log2_self, one_mul]

/-- `GEN = E(2)` is `g` in `E`. -/
theorem gen_eq : UniStatement.gen = ofK g := by decide +kernel

/-- **`gpow i = GEN^i`** is `(ofK g)^i`. -/
theorem gpow_eq (n : ℕ) : UniStatement.gpow n = ofK g ^ n := by
  rw [UniStatement.gpow, epow_eq, gen_eq]

/-- `SEP_MEM = g`. -/
theorem sepMem_eq : sepMem = ofK g := gen_eq

/-- `K.ofBits 4` is `g^2`. -/
theorem ofBits_four : K.ofBits 4 = g ^ 2 := by decide +kernel

/-- `SEP_BYTECODE = g^2`. -/
theorem sepBytecode_eq : sepBytecode = ofK g ^ 2 := by
  rw [← ofKPow]
  decide +kernel

/-- `SEP_STATE = 1`. -/
theorem sepState_eq : sepState = 1 := rfl

/-! ### Forms at a row -/

/-- A monomial's value at a row. -/
def monoE (mono : List ℕ) (col : ℕ → E) : E := mono.foldl (fun p j ↦ p * col j) 1

theorem foldl_add_shift {α : Type} (F : α → E) :
    ∀ (l : List α) (a : E), l.foldl (fun acc x ↦ acc + F x) a = a + (l.map F).sum
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, foldl_add_shift F l, List.map_cons, List.sum_cons]
    ring

/-- **A form's value is the sum of its terms.** -/
theorem formE_eq_sum (f : Form) (col : ℕ → E) :
    formE f col = (f.map fun x ↦ x.2 * monoE x.1 col).sum := by
  show f.foldl (fun acc x ↦ acc + x.2 * monoE x.1 col) 0 = _
  rw [foldl_add_shift, zero_add]

theorem formE_nil (col : ℕ → E) : formE [] col = 0 := rfl

theorem formE_addAt (col : ℕ → E) (mono : List ℕ) (c : E) :
    ∀ f : Form, formE (f.addAt mono c) col = formE f col + c * monoE mono col
  | [] => by simp [Form.addAt, formE_eq_sum]
  | (k, v) :: rest => by
    rw [Form.addAt]
    split_ifs with h1
    · have hk : k = mono := by simpa using h1
      subst hk
      simp only [formE_eq_sum, List.map_cons, List.sum_cons]
      ring
    · simp only [formE_eq_sum, List.map_cons, List.sum_cons]
      ring
    · have ih := formE_addAt col mono c rest
      simp only [formE_eq_sum, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      ring

theorem formE_addScaled (col : ℕ → E) (w : E) :
    ∀ (other f : Form), formE (f.addScaled other w) col = formE f col + w * formE other col
  | [], f => by simp [Form.addScaled, formE_nil]
  | (m, c) :: rest, f => by
    have ih := formE_addScaled col w rest (f.addAt m (w * c))
    simp only [Form.addScaled, List.foldl_cons] at ih ⊢
    rw [ih, formE_addAt]
    simp only [formE_eq_sum, List.map_cons, List.sum_cons]
    ring

theorem formE_add (col : ℕ → E) (f f' : Form) : formE (f.add f') col = formE f col + formE f' col := by
  rw [Form.add, formE_addScaled, one_mul]

theorem formE_term (col : ℕ → E) (mono : List ℕ) (c : E) :
    formE (Form.term mono c) col = c * monoE mono col := by
  simp [Form.term, formE_eq_sum]

theorem formE_constant (col : ℕ → E) (v : E) : formE (constant v) col = v := by
  simp [constant, formE_term, monoE]

theorem formE_col (col' : ℕ → E) (i e : ℕ) : formE (col i e) col' = ofK g ^ e * col' i := by
  simp [UniStatement.col, formE_term, monoE, gpow_eq]

theorem formE_prod (col' : ℕ → E) (a b e : ℕ) :
    formE (prod a b e) col' = ofK g ^ e * (col' (min a b) * col' (max a b)) := by
  simp [UniStatement.prod, formE_term, monoE, gpow_eq]

/-- A product of two columns in order. -/
theorem formE_prod_le (col' : ℕ → E) (a b e : ℕ) (h : a ≤ b) :
    formE (prod a b e) col' = ofK g ^ e * (col' a * col' b) := by
  rw [formE_prod, min_eq_left h, max_eq_right h]

theorem formE_sum_go (col : ℕ → E) :
    ∀ (forms : List Form) (f : Form), formE (forms.foldl Form.add f) col =
      formE f col + (forms.map (formE · col)).sum
  | [], f => by simp
  | x :: l, f => by
    rw [List.foldl_cons, formE_sum_go col l, formE_add, List.map_cons, List.sum_cons]
    ring

theorem formE_sum (col : ℕ → E) (forms : List Form) :
    formE (Form.sum forms) col = (forms.map (formE · col)).sum := by
  rw [Form.sum, formE_sum_go, formE_nil, zero_add]

/-- **A tuple of at most sixteen forms**: their values, then zeros. -/
theorem tupleAt_eq (tuple : List Form) (col : ℕ → E) (h : tuple.length ≤ 16) :
    tupleAt tuple col = tuple.map (formE · col) ++ List.replicate (16 - tuple.length) 0 := by
  apply List.ext_getElem (by simp [tupleAt]; omega)
  intro n h1 h2
  simp only [tupleAt, List.length_map, List.length_range] at h1
  simp only [tupleAt, List.getElem_map, List.getElem_range]
  by_cases hn : n < tuple.length
  · rw [List.getElem_append_left (by simpa using hn)]
    simp [List.getElem?_eq_getElem hn]
  · rw [List.getElem_append_right (by simpa using hn)]
    simp [List.getElem?_eq_none (by omega : tuple.length ≤ n), formE_nil]

/-! ### Lv42's tuples in `E` -/

/-- **A sixteen-slot `K`-tuple in `E`**, slot by slot. -/
def phi (v : Vector K 16) : List E := v.toList.map ofK

theorem phi_injective : Function.Injective phi := by
  intro a b h
  have h' : a.toList = b.toList := List.map_injective_iff.mpr ofK_injective h
  exact Vector.toList_inj.mp h'

open Lv42.Protocol.LeanIsa in
/-- A message's tuple in `E`: the separator, the message, then zeros. -/
theorem phi_tupleOf (σ : K) (m : Array K) (h : m.size ≤ 15) :
    phi (tupleOf σ m) = ofK σ :: m.toList.map ofK ++ List.replicate (15 - m.size) 0 := by
  apply List.ext_getElem (by simp [phi]; omega)
  intro n h1 h2
  simp only [phi, List.length_map, Vector.length_toList] at h1
  simp only [phi, List.getElem_map, Vector.getElem_toList, tupleOf, Vector.getElem_ofFn]
  rcases n with _ | n
  · simp
  · simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, List.cons_append,
      List.getElem_cons_succ]
    by_cases hn : n < m.size
    · rw [List.getElem_append_left (by simpa using hn)]
      simp [Array.getElem?_eq_getElem hn]
    · rw [List.getElem_append_right (by simpa using hn)]
      simp [Array.getElem?_eq_none (by omega : m.size ≤ n)]

/-! ### A table's flushes at a row -/

open Lv42.Protocol Lv42.Protocol.LeanIsa Lv42.Arithmetization LeanVM.Protocol

/-- The direction of the channel named `n` (`channelDir`'s reading). -/
def nameDir (n : String) : Direction :=
  if n = StatePull.name ∨ n = MemPull.name ∨ n = BytecodePull.name then .pull else .push

/-- The separator of the channel named `n` (`channelSep`'s reading). -/
def nameSep (n : String) : K :=
  if n = StatePull.name ∨ n = StatePush.name then gpow 0
  else if n = MemPull.name ∨ n = MemPush.name then gpow 1
  else if n = BytecodePull.name ∨ n = BytecodePush.name then gpow 2
  else 0

/-- The side and tuple of a message on the channel named `p.1`. -/
def nameView (p : String × Array K) : Side × Vector K 16 :=
  (sideOf (nameDir p.1), tupleOf (nameSep p.1) p.2)

/-- **The tuples of interactions depend only on their channels' names and messages.** -/
theorem tuplesOn_eq (l : List (Interaction K)) (side : Side) :
    tuplesOn l side = ((((l.map fun i ↦ (i.channel.name, i.msg)).map nameView).filter
      fun v ↦ decide (v.1 = side)).map (·.2)) := by
  rw [tuplesOn, List.map_map]
  rfl

/-- How the bus views the six channels' messages. -/
theorem nameView_statePush (m : Array K) : nameView (StatePush.name, m) = (.push, tupleOf (gpow 0) m) := rfl
theorem nameView_statePull (m : Array K) : nameView (StatePull.name, m) = (.pull, tupleOf (gpow 0) m) := rfl
theorem nameView_memPush (m : Array K) : nameView (MemPush.name, m) = (.push, tupleOf (gpow 1) m) := rfl
theorem nameView_memPull (m : Array K) : nameView (MemPull.name, m) = (.pull, tupleOf (gpow 1) m) := rfl
theorem nameView_bytecodePush (m : Array K) :
    nameView (BytecodePush.name, m) = (.push, tupleOf (gpow 2) m) := rfl
theorem nameView_bytecodePull (m : Array K) :
    nameView (BytecodePull.name, m) = (.pull, tupleOf (gpow 2) m) := rfl

theorem filter_map_side {n : ℕ} (L : List (Direction × Vector (CPoly.CMvPolynomial n K) 16))
    (r : Fin n → K) (side : Side) :
    ((L.map fun f ↦ (sideOf f.1, f.2)).filter fun f ↦ decide (f.1 = side)).map
        (fun f ↦ f.2.map fun P ↦ P.eval r) =
      ((L.map fun f ↦ (sideOf f.1, f.2.map fun P ↦ P.eval r)).filter fun v ↦ decide (v.1 = side)).map
        (·.2) := by
  induction L with
  | nil => rfl
  | cons f L ih =>
    by_cases h : sideOf f.1 = side
    · simp [h, ih]
    · simp [h, ih]

/-- **Lv42's flushes of opcode table `j` at a row** (filtered by side, evaluated) are the tuples its
component emits on that row, on that side. -/
theorem flushesEval_eq (j : Fin 6) (r : Fin (width (opIdx j)) → K) (data : ProverData K) (side : Side) :
    ((flushes (opIdx j)).filter fun f ↦ decide (f.1 = side)).map (fun f ↦ f.2.map fun P ↦ P.eval r) =
      tuplesOn ((opcodeComponent j).operations.interactionValues
        (Environment.fromArray (Array.ofFn r) data)) side := by
  have h := toM3_flushes_eq (opcodeComponent j) channelSep channelDir counted r data
  have hv : (((opcodeComponent j).operations.interactionValues
      (Environment.fromArray (Array.ofFn r) data)).map busView) =
      ((opcodeTable j).flushes.map fun f ↦ (sideOf f.1, f.2.map (·.eval r))) := by
    have := congrArg (List.map fun p : Direction × Vector K 16 ↦ (sideOf p.1, p.2)) h
    simp only [List.map_map] at this
    exact this.symm
  rw [tuplesOn, hv]
  exact filter_map_side (opcodeTable j).flushes r side

/-- A row of Lv42's table, as the PIOP's columns read it (`0` past the width). -/
def rowE {n : ℕ} (r : Fin n → K) (c : ℕ) : E := if h : c < n then ofK (r ⟨c, h⟩) else 0

end UniComplete.Mapping
