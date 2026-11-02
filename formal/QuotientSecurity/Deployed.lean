-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Statement
import Circuit.Final

/-!
# The deployed circuit in the end theorems

`formal/Circuit` transcribes `quotient::circuit::membership` (`PcsCircuit.membership`: its rows,
inputs and σ, checked against the Rust by `CircuitTest/Dump.lean`) and proves what its rows
compute. This file reads it as a `ChiCircuit` and plugs it into `soundness_circuit_bits`:

* `deployed`: the circuit, row `r` reading what row `r` of `membership` reads, ranked as the Rust
  test ranks it (`PcsCircuit.rank`: the public rows last), its inputs `membership`'s
  (`membership_input_row`, `membership_order`);
* `deployed_laid`: the anchors of the constants (words 4 and 5), so `wiringOf deployed` lays it
  (`laid_wiringOf`);
* `deployed_public`: for every computation `v` of `deployed`, its public bits are the bits of
  `y = H(x ‖ 0x11^32)` and of the root of the path, `x`, the siblings and the directions being
  `v`'s input bits (`secretOf v`), `H` leanerVM's Keccak-256;
* `Instance.soundness_membership`: the end theorem for the deployed circuit.

`membership` is a closed term of `2^22` rows that neither the elaborator nor the kernel may
unfold: everything is proved for a circuit `c` meeting the facts `formal/Circuit/Final.lean`
proves of `membership` (`toChi` and the lemmas after it), then instantiated.
-/

set_option maxRecDepth 10000

namespace QuotientSecurity

open PcsCircuit (membership publicRows logRows)

/-- A source of a circuit of `PcsCircuit` as a source of a circuit on `Fin (2^22)` (a row past
`2^22`, which no row of `membership` reads, would read zero). -/
def ofSrc : PcsCircuit.Src → Src (Fin (2 ^ 22))
  | .zero => .zero
  | .one => .one
  | .row r => if h : r < 2 ^ 22 then .row ⟨r, h⟩ else .zero

theorem ofSrc_eq_row {s : PcsCircuit.Src} {r' : Fin (2 ^ 22)} (h : ofSrc s = .row r') :
    s = .row r' := by
  cases s with
  | zero => cases h
  | one => cases h
  | row r =>
    change (if h : r < 2 ^ 22 then Src.row ⟨r, h⟩ else Src.zero) = Src.row r' at h
    by_cases hr : r < 2 ^ 22
    · rw [dif_pos hr] at h; cases h; rfl
    · rw [dif_neg hr] at h; cases h

theorem ranked_lt {s : PcsCircuit.Src} {rk : ℕ} (hs : PcsCircuit.Ranked rk s) (r' : Fin (2 ^ 22))
    (h : ofSrc s = .row r') : PcsCircuit.rank r' < rk := by
  rw [ofSrc_eq_row h] at hs
  exact hs.2

/-- A computation on `Fin (2^22)` as one on row numbers, `false` past the rows. -/
def natVal (v : Fin (2 ^ 22) → Bool) (r : ℕ) : Bool := if h : r < 2 ^ 22 then v ⟨r, h⟩ else false

theorem bval_ofSrc (v : Fin (2 ^ 22) → Bool) (s : PcsCircuit.Src) :
    (ofSrc s).bval v = PcsCircuit.read (natVal v) s := by
  cases s with
  | zero => rfl
  | one => rfl
  | row r =>
    show Src.bval v (if h : r < 2 ^ 22 then Src.row ⟨r, h⟩ else Src.zero) = natVal v r
    by_cases h : r < 2 ^ 22
    · rw [dif_pos h]; unfold natVal; rw [dif_pos h]; rfl
    · rw [dif_neg h]; unfold natVal; rw [dif_neg h]; rfl

/-- 32 bytes of a list. -/
def bytes32 (l : List UInt8) : Fin 32 → UInt8 := fun i => l.getD i 0

/-! ## A circuit of `PcsCircuit` as a `ChiCircuit` -/

section Generic

variable (c : PcsCircuit.Circuit)

/-- The input rows read their own outputs (`membership_input_row`). -/
def InputRows : Prop := ∀ r ∈ c.inputs, r < 2 ^ logRows ∧ publicRows ≤ r ∧
  c.rows.getD r .idle = ⟨.row r, .row r, .row r⟩

/-- Every other row reads lower ranks (`membership_order`). -/
def Ordered : Prop := ∀ r < 2 ^ logRows, r ∉ c.inputs →
  PcsCircuit.Ranked (PcsCircuit.rank r) (c.rows.getD r .idle).x ∧
  PcsCircuit.Ranked (PcsCircuit.rank r) (c.rows.getD r .idle).y ∧
  PcsCircuit.Ranked (PcsCircuit.rank r) (c.rows.getD r .idle).c

/-- **The circuit `c` as a loop-free χ circuit**: row `r` reads what row `r` of `c` reads, the
inputs are `c`'s, ranked by `PcsCircuit.rank`. -/
def toChi (hI : InputRows c) (hO : Ordered c) : ChiCircuit (Fin (2 ^ 22)) where
  x r := ofSrc (c.rows.getD r .idle).x
  y r := ofSrc (c.rows.getD r .idle).y
  c r := ofSrc (c.rows.getD r .idle).c
  rank r := PcsCircuit.rank r
  isInput r := (r : ℕ) ∈ c.inputs
  hInput r h := by
    obtain ⟨-, -, hrow⟩ := hI r h
    rw [hrow]
    have hr : (r : ℕ) < 2 ^ 22 := r.isLt
    simp [ofSrc, hr]
  hOrder r h r' hs := by
    obtain ⟨hx, hy, hc⟩ := hO r r.isLt h
    rcases hs with hs | hs | hs
    · exact ranked_lt hx r' hs
    · exact ranked_lt hy r' hs
    · exact ranked_lt hc r' hs

variable {c}

theorem toChi_pubSrc (hI : InputRows c) (hO : Ordered c) (J : Fin 8) (j : Fin 128) :
    (toChi c hI hO).pubSrc J j = ofSrc (PcsCircuit.pubSrcN c J j) := by
  unfold ChiCircuit.pubSrc PcsCircuit.pubSrcN
  by_cases h : (j : ℕ) % 2 = 0
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h]; rfl

theorem circuitSat_toChi (hI : InputRows c) (hO : Ordered c) (hsize : c.rows.size = 2 ^ logRows)
    (v : Fin (2 ^ 22) → Bool) (hv : (toChi c hI hO).SatisfiesBits v) :
    PcsCircuit.CircuitSat c (natVal v) := by
  intro r hr
  rw [hsize] at hr
  have hr' : r < 2 ^ 22 := hr
  have e : natVal v r = v ⟨r, hr'⟩ := dif_pos hr'
  rw [e, hv ⟨r, hr'⟩]
  show chiBits ((ofSrc (c.rows.getD r .idle).x).bval v) ((ofSrc (c.rows.getD r .idle).y).bval v)
    ((ofSrc (c.rows.getD r .idle).c).bval v) = _
  rw [bval_ofSrc, bval_ofSrc, bval_ofSrc]
  rfl

/-- The public bits of `c` are the statement's (`membership_public`). -/
def PublicIsStatement (c : PcsCircuit.Circuit) : Prop :=
  ∀ v : ℕ → Bool, PcsCircuit.CircuitSat c v → ∀ s : PcsCircuit.Secret, s.WellFormed →
    PcsCircuit.SecretInputs s v c.inputs → ∀ J j : ℕ, J < 4 → j < 128 →
    PcsCircuit.read v (PcsCircuit.pubSrcN c J j) =
      ((if J < 2 then s.y else s.root).getD (16 * (J % 2) + 15 - j / 8) 0).toNat.testBit (j % 8)

/-- The secret whose bits are the input bits of `v`. -/
def secretOfC (c : PcsCircuit.Circuit) (v : Fin (2 ^ 22) → Bool) : PcsCircuit.Secret :=
  PcsCircuit.secretOfBits fun k => natVal v (c.inputs.getD k 0)

theorem toChi_public (hI : InputRows c) (hO : Ordered c) (hsize : c.rows.size = 2 ^ logRows)
    (hP : PublicIsStatement c) (v : Fin (2 ^ 22) → Bool) (hv : (toChi c hI hO).SatisfiesBits v)
    (J : Fin 4) (j : Fin 128) :
    (toChi c hI hO).pubBit v (Fin.castLE (by norm_num) J) j =
      statementBit (bytes32 (secretOfC c v).y) (bytes32 (secretOfC c v).root) J j := by
  have hp := hP (natVal v) (circuitSat_toChi hI hO hsize v hv) (secretOfC c v)
    (PcsCircuit.secretOfBits_wellFormed _) (PcsCircuit.secretInputs_ofBits _ _) J j J.isLt j.isLt
  unfold ChiCircuit.pubBit
  rw [toChi_pubSrc, bval_ofSrc]
  simp only [Fin.coe_castLE]
  rw [hp]
  unfold statementBit byteAt bytes32
  have hi : 16 * ((J : ℕ) % 2) + 15 - (j : ℕ) / 8 < 32 := by have := J.isLt; have := j.isLt; omega
  rw [dif_pos hi]
  by_cases h2 : (J : ℕ) < 2
  · rw [if_pos h2, if_pos h2]
  · rw [if_neg h2, if_neg h2]

end Generic

/-! ## The deployed circuit -/

/-- **The deployed circuit** (`quotient::circuit::membership`) as a loop-free χ circuit: row `r`
reads what row `r` of `membership` reads, the inputs are `membership`'s, the ranks the Rust
test's (`r`, the public rows `2^22 + r`). -/
def deployed : ChiCircuit (Fin (2 ^ 22)) :=
  toChi membership PcsCircuit.membership_input_row PcsCircuit.membership_order

/-- The secret whose bits are the input bits of the computation `v` of `deployed`: `x`, then each
level's sibling and direction (`membership_inputs` inverted). -/
def secretOf (v : Fin (2 ^ 22) → Bool) : PcsCircuit.Secret := secretOfC membership v

theorem deployed_pubSrc (J : Fin 8) (j : Fin 128) :
    deployed.pubSrc J j = ofSrc (PcsCircuit.pubSrcN membership J j) := toChi_pubSrc _ _ J j

/-- **The constants' anchors**: word 5 reads the zero, bit 0 of word 4 the one, its other bits
the zero; and words 6, 7 the zero. -/
theorem deployed_word5 (j : Fin 128) : deployed.pubSrc 5 j = .zero := by
  rw [deployed_pubSrc]; exact congrArg ofSrc (PcsCircuit.membership_word5 j j.isLt)

theorem deployed_word4_one : deployed.pubSrc 4 0 = .one := by
  rw [deployed_pubSrc]; exact congrArg ofSrc PcsCircuit.membership_word4_one

theorem deployed_word4 (j : Fin 128) (hj : j ≠ 0) : deployed.pubSrc 4 j = .zero := by
  rw [deployed_pubSrc]
  exact congrArg ofSrc (PcsCircuit.membership_word4 j (fun h => hj (Fin.ext h)) j.isLt)

theorem deployed_word6 (j : Fin 128) : deployed.pubSrc 6 j = .zero := by
  rw [deployed_pubSrc]; exact congrArg ofSrc (PcsCircuit.membership_high 6 j (by decide) (by decide) j.isLt)

theorem deployed_word7 (j : Fin 128) : deployed.pubSrc 7 j = .zero := by
  rw [deployed_pubSrc]; exact congrArg ofSrc (PcsCircuit.membership_high 7 j (by decide) (by decide) j.isLt)

/-- **`wiringOf deployed` lays the deployed circuit.** -/
theorem deployed_laid : Laid (wiringOf deployed) deployed :=
  laid_wiringOf deployed deployed_word5 deployed_word4_one deployed_word4

/-- **The deployed circuit computes the statement.** For every computation `v` of `deployed`,
bit `j` of public word `J < 4` is bit `j` of the statement word (`statementBit`,
`circuit::public_words`): the halves of `y = H(x ‖ 0x11^32)` and of the root of the path from
`H(x ‖ 0x22^32)`, the secret being `v`'s input bits (`secretOf`). -/
theorem deployed_public (v : Fin (2 ^ 22) → Bool) (hv : deployed.SatisfiesBits v) (J : Fin 4)
    (j : Fin 128) :
    deployed.pubBit v (Fin.castLE (by norm_num) J) j =
      statementBit (bytes32 (secretOf v).y) (bytes32 (secretOf v).root) J j :=
  toChi_public _ _ PcsCircuit.membership_rows_size PcsCircuit.membership_public v hv J j

/-! ## The end theorem for the deployed circuit -/

/-- Bytes are determined by their bits as `statementBit` reads them. -/
theorem bytes_eq_of_statementBit {y root y' root' : Fin 32 → UInt8}
    (h : ∀ (J : Fin 4) (j : Fin 128), statementBit y root J j = statementBit y' root' J j) :
    y = y' ∧ root = root' := by
  have key : ∀ (b b' : Fin 32 → UInt8), (∀ (hh : ℕ) (j : Fin 128), hh < 2 →
      (byteAt b (16 * hh + 15 - j / 8)).testBit (j % 8) = (byteAt b' (16 * hh + 15 - j / 8)).testBit (j % 8)) →
      b = b' := by
    intro b b' h2
    funext i
    have hi := i.isLt
    apply UInt8.toNat_inj.mp
    apply Nat.eq_of_testBit_eq
    intro t
    by_cases ht : t < 8
    · have := h2 (i / 16) ⟨8 * (15 - i % 16) + t, by omega⟩ (by omega)
      have e1 : 16 * ((i : ℕ) / 16) + 15 - (8 * (15 - (i : ℕ) % 16) + t) / 8 = i := by omega
      have e2 : (8 * (15 - (i : ℕ) % 16) + t) % 8 = t := by omega
      simp only [e1, e2] at this
      unfold byteAt at this
      simpa [hi] using this
    · have h8 : 2 ^ 8 ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (UInt8.toNat_lt _) h8),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (UInt8.toNat_lt _) h8)]
  refine ⟨key y y' fun hh j hlt => ?_, key root root' fun hh j hlt => ?_⟩
  · have := h ⟨hh, by omega⟩ j
    unfold statementBit at this
    simp only [show hh < 2 from hlt, if_true, Nat.mod_eq_of_lt hlt] at this
    exact this
  · have := h ⟨hh + 2, by omega⟩ j
    unfold statementBit at this
    have e : (hh + 2) % 2 = hh := by omega
    simp only [show ¬ hh + 2 < 2 by omega, if_false, e] at this
    exact this

/-- The proof's cells hold a computation of the deployed circuit whose input bits are a secret
hashing to `(y, root)`: `y = H(x ‖ 0x11^32)` and the path from `H(x ‖ 0x22^32)` ends at `root`. -/
def ProvesMembership {F : Type*} [Field F] (w : (Fin (22 + 2) → Bool) → F)
    (y root : Fin 32 → UInt8) : Prop :=
  ∃ v, deployed.Computes w v ∧ bytes32 (secretOf v).y = y ∧ bytes32 (secretOf v).root = root

theorem ProvesBits.membership {F : Type*} [Field F] {w : (Fin (22 + 2) → Bool) → F}
    {y root : Fin 32 → UInt8} (h : deployed.ProvesBits w y root) : ProvesMembership w y root := by
  obtain ⟨v, hv, hbits⟩ := h
  obtain ⟨hy, hr⟩ := bytes_eq_of_statementBit fun J j => (deployed_public v hv.1 J j).symm.trans (hbits J j)
  exact ⟨v, hv, hy, hr⟩

open OracleSpec OracleComp

namespace Instance

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable (I : Instance F)

/-- **Knowledge soundness of the deployed membership proof.** Over a field of `2^192` elements,
for an instance laying the deployed circuit (`Laid I.wiring deployed`, e.g. `I.wiring =
wiringOf deployed`, `deployed_laid`), with `coordinate_weight`'s weights for bit weights
independent over `GF(2)`: for every adversary making at most `Q` oracle queries, the probability
that the verdict is true for the statement of some `(y, root)` while the proof's cells are not a
computation of `deployed` whose input bits are a secret `s` with `H(s.x ‖ 0x11^32) = y` and the
Merkle path of `s` from `H(s.x ‖ 0x22^32)` ending at `root` (`ProvesMembership`), is at most
`(Q + 3) / 2^128`. -/
theorem soundness_membership (hq : Fintype.card F = 2 ^ 192) {x Y : F}
    (hind : BitWeightsIndependent x Y) (hc : I.c = coordWeight x Y) (hC : Laid I.wiring deployed)
    (adv : I.Adversary) (Q : ℕ) (hQ : IsTotalQueryBound adv Q) :
    Pr{let r ← (simulateQ randomOracle (experiment adv)).run' ∅}[
        r.2 = true ∧ ∃ y root, r.1.stmt = statementWords x Y y root ∧
          ¬ ProvesMembership (I.cellsOf r.1.g.1) y root]
      ≤ (Q + 3 : ENNReal) / 2 ^ 128 :=
  le_trans (prEvent_mono _ _ _ fun r hr => by
    obtain ⟨y, root, hs, hn⟩ := hr.2
    exact ⟨hr.1, y, root, hs, fun h => hn (ProvesBits.membership h)⟩)
    (I.soundness_circuit_bits hq deployed hind hc hC adv Q hQ)

end Instance

end QuotientSecurity
