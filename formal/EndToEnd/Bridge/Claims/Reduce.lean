-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import PcsQuotient.Reduction
import Compose.Reduce
import Bridge.Opening
import Field.F192

/-!
# The statement's claims are `Compose.Reduce.reduce`'s

`PcsQuotient.claimsAt` (`formal/Statement/PcsQuotient/Reduction.lean`) and `Compose.Reduce.reduce`
(`formal/Compose/Compose/Reduce.lean`) are two line-by-line transcriptions of
`quotient::protocol::reduce` after its transcript. **`claimsAt_eq_reduce`**: at `2^22` rows they are
equal, for every statement, challenges and values, with `reduce`'s constants the statement's own
(`statementConsts`: the statement's Cantor basis `betaAt` and rows' polynomial `rowVanishing 24`),
the statement read as its 64 bytes `y ‖ root` (`stmtHalves`), and the claims converted
(`reducedTr`, `PcsQuotient.Claim` from F2's `Claim`). Proved for general arguments, without
evaluating any constant: the two transcriptions differ only in form —

* `w_k` as a list built by a fold (`w_foldl`) against the recursive `wChain`;
* the coordinates' constants as an array built by a fold against the recursive `coordinates`
  (`coordinates_getD`, the same recurrence);
* `2^j` against `1 <<< j` (`coordinateWeight_eq`), mumbai's `y` against the statement's `ey`;
* `Statement::halves` by big-endian words (`beWord`) against `halfValue` (`half_fst_eq`,
  `half_snd_eq`);
* the target by Horner's rule over `statementWords` against its expanded form;
* each denominator inverted (default `1` past the list) against `inverses` (default `0`), on the
  indices read.
-/

namespace Bridge

open LeanVM.Parameters PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript

/-! ## The constants and the conversion -/

/-- The statement's rows' polynomial at `2^22` rows, its `k`-th coefficient. -/
def statementTau (k : ℕ) : K := (rowVanishing 24).getD k 0

/-- **`reduce`'s constants as the statement computes them**: its Cantor basis and its rows'
polynomial at `2^22` rows (`m = 24` cell variables). -/
def statementConsts : Compose.Reduce.Consts :=
  ⟨betaAt, statementTau⟩

@[simp] theorem statementConsts_beta : statementConsts.beta = betaAt := rfl

@[simp] theorem statementConsts_tau : statementConsts.tau = statementTau := rfl

/-- An F2 claim as the statement's (the inverse of `claimTr`). -/
def claimOfW (c : WhirBridge.Claim) : PcsQuotient.Claim := ⟨c.point, c.value⟩

@[simp] theorem claimTr_claimOfW (c : WhirBridge.Claim) : claimTr (claimOfW c) = c := rfl

@[simp] theorem claimOfW_claimTr (c : PcsQuotient.Claim) : claimOfW (claimTr c) = c := rfl

/-- **`reduce`'s four claims as the statement's `Claims`.** -/
def reducedTr (r : Compose.Reduce.Reduced) : PcsQuotient.Claims :=
  ⟨claimOfW r.witness, claimOfW r.wiring, claimOfW r.quotient, claimOfW r.sum⟩

@[simp] theorem claimTr_reducedTr_witness (r : Compose.Reduce.Reduced) :
    claimTr (reducedTr r).witness = r.witness := rfl

@[simp] theorem claimTr_reducedTr_wiring (r : Compose.Reduce.Reduced) :
    claimTr (reducedTr r).wiring = r.wiring := rfl

@[simp] theorem claimTr_reducedTr_quotient (r : Compose.Reduce.Reduced) :
    claimTr (reducedTr r).quotient = r.quotient := rfl

@[simp] theorem claimTr_reducedTr_sum (r : Compose.Reduce.Reduced) :
    claimTr (reducedTr r).sum = r.sum := rfl

/-! ## Lists and folds -/

namespace ClaimsBridge

theorem foldl_congr_mem {α β : Type} (f g : β → α → β) :
    ∀ (l : List α), (∀ x ∈ l, ∀ b, f b x = g b x) → ∀ b, l.foldl f b = l.foldl g b
  | [], _, _ => rfl
  | x :: l, h, b => by
    rw [List.foldl_cons, List.foldl_cons, h x (List.mem_cons_self ..) b]
    exact foldl_congr_mem f g l (fun y hy ↦ h y (List.mem_cons_of_mem _ hy)) _

theorem getD_map_range {α : Type} (f : ℕ → α) {n k : ℕ} (hk : k < n) (d : α) :
    ((List.range n).map f).getD k d = f k := by
  simp [List.getD_eq_getElem?_getD, hk]

/-- The statement's `w` list is `wChain`'s values. -/
theorem w_foldl (t : E) (n : ℕ) :
    (List.range n).foldl (fun ws (_ : ℕ) ↦ ws ++ [ws.getLastD t * ws.getLastD t + ws.getLastD t])
      [t] = (List.range (n + 1)).map (Compose.Reduce.wChain t) := by
  induction n with
  | zero => simp [Compose.Reduce.wChain]
  | succ n ih =>
    have hlast : ((List.range (n + 1)).map (Compose.Reduce.wChain t)).getLastD t =
        Compose.Reduce.wChain t n := by
      rw [List.range_succ, List.map_append, List.map_singleton, List.getLastD_concat]
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil, hlast,
      List.range_succ (n := n + 1), List.map_append, List.map_singleton]
    rfl

/-! ## The coordinates' constants -/

/-- The statement's fold building `coordinates`. -/
def coordStep (b : Array K) (d : ℕ) : Array K :=
  if d = 0 then b.push 1
  else b.push ((List.range d).foldl (fun acc e ↦ acc + betaAt (e + 1) * b.getD (d - 1 - e) 0) 0)

theorem foldl_add_range (g : ℕ → K) (n : ℕ) (a : K) :
    (List.range n).foldl (fun acc e ↦ acc + g e) a = a + ∑ e : Fin n, g e := by
  rw [List.range_eq_range', Compose.Reduce.foldl_range'_add, Fin.sum_univ_eq_sum_range]
  simp

/-- **The statement's coordinates' constants are `Compose.Reduce.coordinates`'s**: the same
recurrence, `b[0] = 1`, `b[d + 1] = Σ_{e ≤ d} β_{e + 1} b[d − e]`. -/
theorem coordStep_spec (count : ℕ) :
    ((List.range count).foldl coordStep #[]).size = count ∧
      ∀ i < count, ((List.range count).foldl coordStep #[]).getD i 0 =
        Compose.Reduce.coordinates betaAt i := by
  induction count with
  | zero => simp
  | succ n ih =>
    obtain ⟨hs, hv⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set A := (List.range n).foldl coordStep #[] with hA
    have hpush : ∀ v : K, (A.push v).size = n + 1 ∧
        ∀ i < n + 1, (A.push v).getD i 0 = if i < n then A.getD i 0 else v := by
      intro v
      refine ⟨by simp [hs], fun i hi ↦ ?_⟩
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, hs]
      split_ifs with h1 h2 h2
      · omega
      · subst h1; simp
      · rfl
      · omega
    unfold coordStep
    split_ifs with h0
    · subst h0
      refine ⟨(hpush 1).1, fun i hi ↦ ?_⟩
      rw [(hpush 1).2 i hi, if_neg (by omega), show i = 0 by omega]
      simp [Compose.Reduce.coordinates]
    · refine ⟨(hpush _).1, fun i hi ↦ ?_⟩
      rw [(hpush _).2 i hi]
      split_ifs with hin
      · exact hv i hin
      · have hi' : i = n := by omega
        subst hi'
        obtain ⟨d, rfl⟩ : ∃ d, i = d + 1 := ⟨i - 1, by omega⟩
        rw [foldl_add_range, zero_add, Compose.Reduce.coordinates]
        refine Finset.sum_congr rfl fun e _ ↦ ?_
        rw [show d + 1 - 1 - (e : ℕ) = d - e by omega, hv _ (by omega)]

theorem coordinates_eq_foldl (count : ℕ) :
    PcsQuotient.Domain.coordinates count = ((List.range count).foldl coordStep #[]).toList := rfl

/-- **`b_i`, `i < 11`**, is `Compose.Reduce.coordinates`'s. -/
theorem coordinates_getD (i : ℕ) (hi : i < 11) :
    (PcsQuotient.Domain.coordinates region).getD i 0 = Compose.Reduce.coordinates betaAt i := by
  rw [show region = 11 from rfl, coordinates_eq_foldl, ← (coordStep_spec 11).2 i hi]
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]

/-! ## The coordinate weights -/

theorem bitWeight_eq (j : ℕ) : PcsQuotient.bitWeight j = Compose.Reduce.bitWeight j := by
  simp only [PcsQuotient.bitWeight, Compose.Reduce.bitWeight, Nat.one_shiftLeft]

/-- **`coordinate_weight(k)`** is the same in both transcriptions. -/
theorem coordinateWeight_eq (k : ℕ) :
    PcsQuotient.coordinateWeight k = Compose.Reduce.coordinateWeight k := by
  simp only [PcsQuotient.coordinateWeight, Compose.Reduce.coordinateWeight, bitWeight_eq,
    Nat.one_shiftLeft]

/-! ## The extension -/

/-- The statement's `y` is mumbai's. -/
theorem ey_eq_y : ey = y := Primitives.F192.Y_eq_gen

theorem extension_eq : PcsQuotient.extension = Compose.Reduce.extension := by
  simp only [PcsQuotient.extension, Compose.Reduce.extension, ey_eq_y]

theorem sumPoint_eq : PcsQuotient.sumPoint 22 = Compose.Reduce.sumPoint 24 := by
  simp only [PcsQuotient.sumPoint, Compose.Reduce.sumPoint, extension_eq]
  rfl

/-! ## `Statement::halves` -/

/-- The big-endian value of `n` bytes of `l` from `s`. -/
def beN (l : List UInt8) (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => beN l s n * 256 + (l.getD (s + n) 0).toNat

theorem beN_lt (l : List UInt8) (s : ℕ) : ∀ n, beN l s n < 256 ^ n
  | 0 => by simp [beN]
  | n + 1 => by
    have := beN_lt l s n
    have hb := (l.getD (s + n) 0).toNat_lt
    rw [beN, pow_succ]
    omega

theorem beN_add (l : List UInt8) (s n : ℕ) : ∀ m, beN l s (n + m) = beN l s n * 256 ^ m + beN l (s + n) m
  | 0 => by simp [beN]
  | m + 1 => by
    rw [← Nat.add_assoc, beN, beN_add l s n m, beN, pow_succ, Nat.add_assoc s n m]
    ring

theorem beN_sum (l : List UInt8) (s : ℕ) : ∀ n,
    beN l s n = ∑ t ∈ Finset.range n, (l.getD (s + t) 0).toNat * 256 ^ (n - 1 - t)
  | 0 => by simp [beN]
  | n + 1 => by
    rw [beN, beN_sum l s n, Finset.sum_range_succ, Finset.sum_mul,
      show n + 1 - 1 - n = 0 by omega, pow_zero, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    have ht' := Finset.mem_range.mp ht
    rw [mul_assoc, ← pow_succ, show n - 1 - t + 1 = n + 1 - 1 - t by omega]

/-- The statement's `beWord` reads `beN` of eight bytes. -/
theorem beWordAux_toNat (l : List UInt8) (s : ℕ) : ∀ n ≤ 8,
    ((List.range n).foldl (fun (acc : UInt64) k ↦ (acc <<< 8) ||| (l.getD (s + k) 0).toUInt64) 0).toNat =
      beN l s n
  | 0, _ => by simp [beN]
  | n + 1, hn => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, beN,
      ← beWordAux_toNat l s n (by omega)]
    generalize hx : (List.range n).foldl
      (fun (acc : UInt64) k ↦ (acc <<< 8) ||| (l.getD (s + k) 0).toUInt64) 0 = x
    have hxlt : x.toNat < 256 ^ n := by
      rw [← hx, beWordAux_toNat l s n (by omega)]
      exact beN_lt l s n
    have hb := (l.getD (s + n) 0).toNat_lt
    have hpow : 256 ^ n ≤ 256 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h8 : (8 : UInt64).toNat % 64 = 8 := rfl
    have hx56 : x.toNat < 72057594037927936 := lt_of_lt_of_le hxlt (by simpa using hpow)
    have hlt : x.toNat <<< 8 < 2 ^ 64 := by rw [Nat.shiftLeft_eq]; norm_num; omega
    have hb8 : (l.getD (s + n) 0).toUInt64.toNat < 2 ^ 8 := by
      rw [UInt8.toNat_toUInt64]; exact hb
    rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, h8, Nat.mod_eq_of_lt hlt,
      ← Nat.shiftLeft_add_eq_or_of_lt hb8, Nat.shiftLeft_eq, UInt8.toNat_toUInt64]

theorem beWord_toNat (l : List UInt8) (s : ℕ) : (beWord l s).toNat = beN l s 8 :=
  beWordAux_toNat l s 8 le_rfl

theorem ofLane_eq_ofBits (w : UInt64) (n : ℕ) (h : w.toNat = n % 2 ^ 64) :
    K.ofLane w = K.ofBits n := by
  unfold K.ofLane K.ofBits
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, ← h]
  rfl

/-- `halfValue` of a vector's bytes is `beN` of sixteen bytes. -/
theorem halfValue_eq (b : Vector UInt8 32) (h : Fin 2) :
    QuotientSecurity.halfValue (fun i ↦ b.get i) h = beN b.toList (16 * h) 16 := by
  rw [beN_sum, QuotientSecurity.halfValue]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  have ht' := Finset.mem_range.mp ht
  have hlt : 16 * (h : ℕ) + t < 32 := by omega
  rw [QuotientSecurity.byteAt, dif_pos hlt, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa using hlt), Option.getD_some, Vector.getElem_toList,
    show 16 - 1 - t = 15 - t by omega]
  rfl

theorem halfValue_split (b : Vector UInt8 32) (h : Fin 2) :
    QuotientSecurity.halfValue (fun i ↦ b.get i) h =
      beN b.toList (16 * h) 8 * 2 ^ 64 + beN b.toList (16 * h + 8) 8 := by
  rw [halfValue_eq, show (16 : ℕ) = 8 + 8 from rfl, beN_add]
  norm_num

theorem half_lo (b : Vector UInt8 32) (h : Fin 2) :
    K.ofLane (beWord b.toList (16 * h + 8)) =
      K.ofBits (QuotientSecurity.halfValue (fun i ↦ b.get i) h % 2 ^ 64) := by
  apply ofLane_eq_ofBits
  have hB : beN b.toList (16 * h + 8) 8 < 2 ^ 64 := by simpa using beN_lt b.toList (16 * h + 8) 8
  rw [beWord_toNat, halfValue_split, Nat.mod_mod]
  generalize beN b.toList (16 * h) 8 = A at *
  generalize beN b.toList (16 * h + 8) 8 = B at *
  rw [show A * 2 ^ 64 + B = B + A * 2 ^ 64 from Nat.add_comm _ _, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hB]

theorem half_hi (b : Vector UInt8 32) (h : Fin 2) :
    K.ofLane (beWord b.toList (16 * h)) =
      K.ofBits (QuotientSecurity.halfValue (fun i ↦ b.get i) h >>> 64) := by
  apply ofLane_eq_ofBits
  have hlo := beN_lt b.toList (16 * h + 8) 8
  have hhi := beN_lt b.toList (16 * h) 8
  have hB : beN b.toList (16 * h + 8) 8 < 2 ^ 64 := by simpa using hlo
  have hA : beN b.toList (16 * h) 8 < 2 ^ 64 := by simpa using hhi
  rw [beWord_toNat, halfValue_split, Nat.shiftRight_eq_div_pow]
  generalize beN b.toList (16 * h) 8 = A at *
  generalize beN b.toList (16 * h + 8) 8 = B at *
  rw [show A * 2 ^ 64 + B = B + A * 2 ^ 64 from Nat.add_comm _ _,
    Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hB, Nat.zero_add,
    Nat.mod_eq_of_lt hA]

/-- **One of `Statement::halves`** is `stmtHalf`'s. -/
theorem halves_eq (b : Vector UInt8 32) :
    PcsQuotient.halves b = (Compose.Reduce.stmtHalf (fun i ↦ b.get i) 0,
      Compose.Reduce.stmtHalf (fun i ↦ b.get i) 1) := by
  have l0 := half_lo b 0
  have h0 := half_hi b 0
  have l1 := half_lo b 1
  have h1 := half_hi b 1
  simp only [Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.zero_add, Nat.mul_one] at l0 h0 l1 h1
  simp only [PcsQuotient.halves, Compose.Reduce.stmtHalf, Nat.mul_zero, Nat.zero_add, Nat.mul_one,
    l0, h0, l1, h1]

/-- **`Statement::halves`** of the statement are `stmtHalves` of its 64 bytes. -/
theorem statement_halves (stmt : Statement) (k : Fin 4) :
    (Statement.halves stmt).getD k 0 = Compose.Reduce.stmtHalves (stmt.y ++ stmt.root) k := by
  have hy : Compose.Reduce.yOf (stmt.y ++ stmt.root) = fun i ↦ stmt.y.get i := by
    funext i
    simp [Compose.Reduce.yOf, Vector.get_eq_getElem, Vector.getElem_append_left i.2]
  have hr : Compose.Reduce.rootOf (stmt.y ++ stmt.root) = fun i ↦ stmt.root.get i := by
    funext i
    simp only [Compose.Reduce.rootOf, Vector.get_eq_getElem]
    rw [Vector.getElem_append_right (by omega) (Nat.le_add_right 32 (i : ℕ))]
    simp
  fin_cases k <;>
    simp [Statement.halves, Compose.Reduce.stmtHalves, hy, hr, halves_eq]

theorem take_drop_map_range {α : Type} (g : ℕ → α) :
    (((List.range 26).map g).drop 2).take 23 = (List.range' 2 23).map g := by
  rw [← List.map_drop, ← List.map_take]
  rfl

theorem take_map_range {α : Type} (g : ℕ → α) :
    ((List.range 26).map g).take 24 = (List.range 24).map g := by
  rw [← List.map_take]
  rfl

end ClaimsBridge

/-! ## The claims -/

open ClaimsBridge in
set_option maxHeartbeats 4000000 in
/-- **The statement's claims are `Compose.Reduce.reduce`'s** at `2^22` rows: for every statement,
challenges and values, `claimsAt 22` is `reduce` with the statement's constants (`statementConsts`)
on the statement's 64 bytes, its claims converted (`reducedTr`). -/
theorem claimsAt_eq_reduce (stmt : Statement) (α β γ t ρ : E) (a : Vector E 4) (next : E) :
    claimsAt 22 stmt α β γ t ρ a next =
      (Compose.Reduce.reduce statementConsts 24 (Compose.Reduce.stmtHalves (stmt.y ++ stmt.root))
        α β γ t (fun i ↦ a.get i) next ρ).map reducedTr := by
  set A : Fin 4 → E := fun i ↦ a.get i with hA
  set S := Compose.Reduce.stmtHalves (stmt.y ++ stmt.root) with hS
  have hA0 : A 0 = a[0] := rfl
  have hA1 : A 1 = a[1] := rfl
  have hA2 : A 2 = a[2] := rfl
  have hA3 : A 3 = a[3] := rfl
  unfold claimsAt
  lift_lets
  extract_lets m w wAt theta cell x y c v gate b gamma2 gammas outside publicWeight target tau rows
    d dNext product copies denominators inv u copyInverse rowsInverse middle wiringScale
    quotientScale rho2 opened identities
  have hm : m = 24 := rfl
  have hw : w = (List.range 26).map (Compose.Reduce.wChain t) := by
    simp only [w, hm]
    exact w_foldl t 25
  have hwAt : ∀ k < 26, wAt k = Compose.Reduce.wChain t k := fun k hk ↦ by
    simp only [wAt, hw, getD_map_range _ hk]
  have hcell : ∀ (sh : K) (second : Bool), cell sh second = Compose.Reduce.cell t A sh second := by
    intro sh second
    simp only [cell, Compose.Reduce.cell, hwAt 1 (by norm_num), hA0, hA1, hA2, hA3]
  have hx : x = Compose.Reduce.rowCells statementConsts t A 0 := hcell 0 false
  have hy : y = Compose.Reduce.rowCells statementConsts t A 1 := hcell 1 false
  have hc : c = Compose.Reduce.rowCells statementConsts t A 2 := hcell theta true
  have hv : v = Compose.Reduce.rowCells statementConsts t A 3 := hcell (theta + 1) true
  have hgate : gate = Compose.Reduce.gate4 (Compose.Reduce.rowCells statementConsts t A) := by
    simp only [gate, Compose.Reduce.gate4, hx, hy, hc, hv]
  have hpub : publicWeight = Compose.Reduce.publicWeight statementConsts 24 γ t := by
    simp only [publicWeight, Compose.Reduce.publicWeight, outside, Compose.Reduce.foldRange, hm]
    rw [show PcsQuotient.region = 11 from rfl, show Compose.Reduce.region = 11 from rfl,
      List.range_eq_range', foldl_congr_mem _ (fun acc k ↦ acc * (1 + Compose.Reduce.wChain t k))
        (List.range' 11 (24 - 11)) (fun k hk acc ↦ by rw [hwAt k (by simp at hk; omega)])]
    refine foldl_congr_mem _ _ _ (fun k hk acc ↦ ?_) _
    have hk' : k < 11 := by simp at hk; omega
    have hcoord : List.foldl (fun s j ↦ s + ofK (b.getD (j - k) 0) * wAt j) (wAt k)
        (List.range' (k + 1) (11 - (k + 1))) = Compose.Reduce.coordinate statementConsts t k := by
      rw [Compose.Reduce.coordinate, Compose.Reduce.foldRange, hwAt k (by omega)]
      refine foldl_congr_mem _ _ _ (fun j hj s ↦ ?_) _
      have hj' : j < 11 := by simp at hj; omega
      rw [hwAt j (by omega), coordinates_getD (j - k) (by omega), statementConsts_beta]
    rw [hcoord, Compose.Reduce.slope, ← coordinateWeight_eq]
    cases PcsQuotient.coordinateWeight k <;> rfl
  have htarget : target = Compose.Reduce.target S γ := by
    have h0 := statement_halves stmt 0
    have h1 := statement_halves stmt 1
    have h2 := statement_halves stmt 2
    have h3 := statement_halves stmt 3
    simp only [Statement.halves, Fin.val_zero, Fin.val_one, Fin.val_two, List.getD_cons_zero,
      List.getD_cons_succ] at h0 h1 h2 h3
    simp only [target, statementWords, Statement.halves, List.cons_append, List.nil_append,
      List.foldr_cons, List.foldr_nil, Compose.Reduce.target]
    rw [h0, h1, h2]
    have h3' : (PcsQuotient.halves stmt.root).2 = S 3 := h3
    rw [h3']
    ring
  have hrows : rows = Compose.Reduce.rows statementConsts 24 t := by
    simp only [rows, tau, Compose.Reduce.rows, Compose.Reduce.foldRange, hm, List.range_eq_range']
    refine foldl_congr_mem _ _ _ (fun k hk acc ↦ ?_) _
    rw [hwAt k (by simp at hk; omega), statementConsts_tau, statementTau]
  have hproduct : product = Compose.Reduce.product statementConsts α β t A next := by
    simp only [product, d, dNext, hx, Compose.Reduce.product]
  have hden : denominators = Compose.Reduce.denominators statementConsts 24 α β t A next := by
    simp only [denominators, hw, List.map_map, hm, hwAt 24 (by norm_num), hproduct, hrows,
      Compose.Reduce.denominators, Function.comp_def]
  have hlen : (Compose.Reduce.denominators statementConsts 24 α β t A next).length = 28 := by
    simp [Compose.Reduce.denominators]
  have hinv : ∀ k < 28, inv k = Compose.Reduce.inverses statementConsts 24 α β t A next k := fun k hk ↦ by
    simp only [inv, hden, Compose.Reduce.inverses, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (hlen ▸ hk : k < _), Option.getD_some]
  have hu : u = (List.range 26).map
      (fun k ↦ Compose.Reduce.wChain t k * Compose.Reduce.inverses statementConsts 24 α β t A next k) := by
    simp only [u, hm]
    refine List.map_congr_left fun k hk ↦ ?_
    have hk' : k < 26 := List.mem_range.mp hk
    rw [hwAt k hk', hinv k (by omega)]
  have hmiddle : middle = Compose.Reduce.middle statementConsts 24 α β t A next := by
    simp only [middle, hm, Compose.Reduce.middle, Compose.Reduce.foldRange, hinv 2 (by norm_num)]
    refine foldl_congr_mem _ _ _ (fun k hk acc ↦ ?_) _
    rw [hinv k (by simp at hk; omega)]
  have hany : (denominators.any fun x ↦ decide (x = 0)) = true ↔
      (Compose.Reduce.denominators statementConsts 24 α β t A next).prod = 0 := by
    rw [hden, List.any_eq_true, List.prod_eq_zero_iff]
    simp
  unfold Compose.Reduce.reduce
  by_cases h0 : (Compose.Reduce.denominators statementConsts 24 α β t A next).prod = 0
  · rw [if_pos (hany.mpr h0), if_pos h0]
    rfl
  · rw [if_neg (fun h ↦ h0 (hany.mp h)), if_neg h0, Option.map_some]
    refine congrArg some ?_
    simp only [reducedTr, claimOfW, Compose.Reduce.claimsOf]
    simp only [hu, hm, wiringScale, quotientScale, copyInverse, rowsInverse, opened, rho2,
      identities, copies, product, d, dNext, hmiddle, Compose.Reduce.middle, hx, hpub, hrows,
      hgate, htarget, extension_eq, sumPoint_eq, hinv 24 (by norm_num), hinv 25 (by norm_num),
      hinv 26 (by norm_num), hinv 27 (by norm_num), hinv 0 (by norm_num), hinv 1 (by norm_num),
      hwAt 24 (by norm_num), Nat.cast_one, hA0, hA1, hA2, hA3, take_drop_map_range,
      take_map_range, Nat.reduceAdd, Nat.reduceSub]

end Bridge

/-- info: 'Bridge.claimsAt_eq_reduce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.claimsAt_eq_reduce
