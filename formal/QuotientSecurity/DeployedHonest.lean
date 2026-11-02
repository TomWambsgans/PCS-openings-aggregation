-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Deployed

/-!
# The deployed circuit's honest computation

`Deployed.lean` is soundness's side of F0: every computation of `deployed` is Keccak-256 membership
of the secret its input bits hold. This file is completeness's side: for every secret there is
one, the circuit evaluated on the secret's input bits, and the deployed σ copies it.

* `ChiCircuit.eval`: a loop-free χ circuit evaluated on input bits, row by row in rank order
  (`evalN`, `n` rounds; a row of rank `k` is final from round `k + 1`, `evalN_stable`). It
  satisfies every gate (`eval_satisfies`) and holds the given bits at the inputs (`eval_input`):
  an input row's gate is `chiBits v v v = v`, any other row's the gate on lower ranks. By
  `bits_determined` it is the only such assignment.
* `deployedAssign s`: `deployed` evaluated on `membership_inputs(s)` (`Secret.inputs`, the
  Rust's order: `x`'s bits, then each level's sibling and direction), input `k` (row
  `membership.inputs[k]`) holding bit `k` (`inputsOf`). Its input bits are the secret's
  (`deployedAssign_secretInputs`), so, for a well-formed secret, its public bits are the bits of
  `y = H(x ‖ 0x11^32)` and of the root of the path (`deployedAssign_public`, from
  `membership_public`: the forward direction of Keccak correctness is soundness's lemma applied to
  this computation), and its cells prove membership (`deployedAssign_provesMembership`).
* `deployedAssign_eq_outputs`: **it is the Rust's `Circuit::outputs`** on `membership_inputs(s)`
  (`Circuit.outputs`, differentially tested against the Rust by `CircuitTest/Dump.lean`): its first
  loop writes the inputs (`inputsArray_spec`), its second sets each row to its gate, the rows in
  rank order (from `512` on, then the public rows), so every row it reads is final by then
  (`foldl_outStep`, `ReadsDone`); hence `Circuit.outputs` satisfies every gate (`outputs_satisfies`).
* `deployedSigma_cellSrc`: **the deployed σ keeps what each cell carries** (the source it reads,
  or its row for a `V` cell), so it copies every cell of a computation onto cells holding the
  same bit. From the construction of `finish`'s σ (`wiring_slot`: σ is the cyclic successor in
  the list of its slot's cells, `Circuit/Wiring.lean`'s `JoinInv`), and the slot of a source
  determining the source (`slot_injective`). Soundness needed only that every reading cell is on
  its source's cycle (`Laid`); completeness needs that no cycle mixes two sources.

As in `Deployed.lean`, everything is proved for a circuit `c` of `PcsCircuit` and then instantiated
with `membership`, whose projections are never unfolded.
-/

set_option maxRecDepth 10000

namespace PcsCircuit

attribute [local irreducible] membership

/-- **σ of `finish` keeps the slots**: the successor of cell `c` joined the same slot as `c`. -/
theorem wiring_slot (rows : Array Row)
    (hsrc : ∀ r < rows.size, slot (rows.getD r .idle).x < rows.size + 2 ∧
      slot (rows.getD r .idle).y < rows.size + 2 ∧ slot (rows.getD r .idle).c < rows.size + 2)
    (c : Nat) (hc : c < 4 * rows.size) :
    slotOfCell rows ((wiring rows).getD c 0) = slotOfCell rows c := by
  obtain ⟨st, hst, hinv⟩ := wiring_inv rows hsrc
  rw [← hst]
  have hP := joins_oneSlot rows rows.size
  have hB := joins_bounds rows rows.size hsrc
  have hS : slotOfCell rows c < rows.size + 2 := (hB _ (mem_joins rows rows.size c hc)).1
  have h1 := cyc_mem (hinv.cyc _ hS) (mem_cellsOf_of_mem (mem_joins rows rows.size c hc))
  have hlt : st.sigma.getD c 0 < 4 * rows.size := (hB _ (mem_cellsOf h1)).2
  exact slot_unique hP (mem_joins rows rows.size _ hlt) (mem_cellsOf h1)

/-- The slot of a source determines it. -/
theorem slot_injective : Function.Injective slot := by
  intro a b h
  cases a <;> cases b <;> simp only [slot] at h <;> first | rfl | omega | (congr 1; omega)

/-- What cell `n` carries: what it reads (`X`, `Y`, `C`), or its row (`V`). -/
def carried (rows : Array Row) (n : Nat) : Src :=
  if n % 4 = 0 then (rows.getD (n / 4) .idle).x else if n % 4 = 1 then (rows.getD (n / 4) .idle).y
  else if n % 4 = 2 then (rows.getD (n / 4) .idle).c else .row (n / 4)

theorem slot_carried (rows : Array Row) (n : Nat) : slot (carried rows n) = slotOfCell rows n := by
  unfold carried slotOfCell
  split_ifs <;> rfl

/-- `membership`'s σ keeps the slots. -/
theorem membership_sigma_slot (c : Nat) (hc : c < 4 * 2 ^ logRows) :
    slotOfCell membership.rows (membership.sigma.getD c 0) = slotOfCell membership.rows c := by
  have h := wiring_slot membership.rows membership_hsrc c (by rw [membership_rows_size]; exact hc)
  rwa [← membership_sigma] at h

/-- `membership`'s inputs are distinct rows. -/
theorem membership_inputs_nodup : membership.inputs.toList.Nodup := by
  obtain ⟨y, root, bf, he, hwf, -⟩ := membership_spec
  rw [he, finish_inputs]
  exact hwf.sorted.imp (fun h => Nat.ne_of_lt h)

/-- `membership` has `256 + 257 · 32` inputs. -/
theorem membership_inputs_size : membership.inputs.size = 256 + 257 * depth := by
  obtain ⟨y, root, bf, he, -, -, hs, -⟩ := membership_spec
  rw [he, finish_inputs, hs]

/-! ## `membership_inputs` -/

theorem length_flatMap_range {α : Type} (f : Nat → List α) (L : Nat) (hf : ∀ i, (f i).length = L) :
    ∀ n, ((List.range n).flatMap f).length = L * n
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, length_flatMap_range f L hf n]
    simp [hf, Nat.mul_succ]

theorem getD_flatMap_range {α : Type} (f : Nat → List α) (L : Nat) (hf : ∀ i, (f i).length = L)
    (d : α) : ∀ n i j, i < n → j < L → ((List.range n).flatMap f).getD (L * i + j) d = (f i).getD j d
  | 0, i, _, hi, _ => absurd hi (Nat.not_lt_zero i)
  | n + 1, i, j, hi, hj => by
    rw [List.range_succ, List.flatMap_append]
    have hlen := length_flatMap_range f L hf n
    by_cases h : i < n
    · have hlt : L * i + j < L * n := by
        calc L * i + j < L * i + L := by omega
          _ = L * (i + 1) := by ring
          _ ≤ L * n := Nat.mul_le_mul_left _ h
      rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hlt)]
      exact getD_flatMap_range f L hf d n i j h hj
    · have hi' : i = n := by omega
      subst hi'
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen, Nat.add_sub_cancel_left]
      simp

theorem bytesBits_length (b : List UInt8) : (bytesBits b).length = 256 := by simp [bytesBits]

theorem bytesBits_getD (b : List UInt8) (k : Nat) (hk : k < 256) :
    (bytesBits b).getD k false = bitOf b k := by
  simp [bytesBits, bitOf, List.getD_eq_getElem?_getD, List.getElem?_range hk]

/-- `membership_inputs`: bit `k < 256` is `x`'s bit `k`. -/
theorem Secret.inputs_x (s : Secret) (k : Nat) (hk : k < 256) :
    s.inputs.getD k false = bitOf s.x k := by
  rw [Secret.inputs, toArray_getD, List.getD_append _ _ _ _ (by rw [bytesBits_length]; exact hk),
    bytesBits_getD _ _ hk]

theorem Secret.inputs_level (s : Secret) (i j : Nat) (hi : i < depth) (hj : j < 257) :
    s.inputs.getD (256 + 257 * i + j) false =
      (bytesBits (s.siblings.getD i []) ++ [s.directions.testBit i]).getD j false := by
  rw [Secret.inputs, toArray_getD, List.getD_append_right _ _ _ _ (by rw [bytesBits_length]; omega),
    bytesBits_length, show 256 + 257 * i + j - 256 = 257 * i + j by omega]
  exact getD_flatMap_range _ 257 (fun i => by simp [bytesBits_length]) false depth i j hi hj

/-- `membership_inputs`: level `i`'s sibling bit `j`. -/
theorem Secret.inputs_sibling (s : Secret) (i j : Nat) (hi : i < depth) (hj : j < 256) :
    s.inputs.getD (256 + 257 * i + j) false = bitOf (s.siblings.getD i []) j := by
  rw [s.inputs_level i j hi (by omega), List.getD_append _ _ _ _ (by rw [bytesBits_length]; exact hj),
    bytesBits_getD _ _ hj]

/-- `membership_inputs`: level `i`'s direction. -/
theorem Secret.inputs_direction (s : Secret) (i : Nat) (hi : i < depth) :
    s.inputs.getD (256 + 257 * i + 256) false = s.directions.testBit i := by
  rw [s.inputs_level i 256 hi (by omega),
    List.getD_append_right _ _ _ _ (by simp [bytesBits_length]), bytesBits_length]
  simp

end PcsCircuit

namespace QuotientSecurity

open PcsCircuit (membership publicRows logRows)

-- `membership` is a closed term of `2^22` rows: never unfold it.
attribute [local irreducible] PcsCircuit.membership

/-! ## A loop-free circuit evaluated on its input bits -/

section Eval

open Classical

variable {ρ : Type*}

/-- **`n` rounds of evaluation** of `C` on the input bits `inp`: round `n + 1` sets every row that
is not an input to the gate on the bits of round `n`. -/
noncomputable def ChiCircuit.evalN (C : ChiCircuit ρ) (inp : ρ → Bool) : ℕ → ρ → Bool
  | 0 => inp
  | n + 1 => fun r => if C.isInput r then inp r else
      chiBits ((C.x r).bval (C.evalN inp n)) ((C.y r).bval (C.evalN inp n))
        ((C.c r).bval (C.evalN inp n))

/-- **The circuit evaluated on its input bits**: a row of rank `k` after `k + 1` rounds. -/
noncomputable def ChiCircuit.eval (C : ChiCircuit ρ) (inp : ρ → Bool) (r : ρ) : Bool :=
  C.evalN inp (C.rank r + 1) r

theorem ChiCircuit.evalN_succ (C : ChiCircuit ρ) (inp : ρ → Bool) (n : ℕ) (r : ρ) :
    C.evalN inp (n + 1) r = if C.isInput r then inp r else
      chiBits ((C.x r).bval (C.evalN inp n)) ((C.y r).bval (C.evalN inp n))
        ((C.c r).bval (C.evalN inp n)) := rfl

/-- A row of rank `k` is final from round `k + 1` on. -/
theorem ChiCircuit.evalN_stable (C : ChiCircuit ρ) (inp : ρ → Bool) :
    ∀ (r : ρ) (n : ℕ), C.rank r < n → C.evalN inp n r = C.eval inp r := by
  intro r
  induction hk : C.rank r using Nat.strong_induction_on generalizing r with
  | _ k ih =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    unfold ChiCircuit.eval
    rw [hk, C.evalN_succ, C.evalN_succ]
    by_cases hi : C.isInput r
    · rw [if_pos hi, if_pos hi]
    · rw [if_neg hi, if_neg hi]
      have hsrc : ∀ s : Src ρ, (∀ r', s = .row r' → C.rank r' < C.rank r) →
          s.bval (C.evalN inp n) = s.bval (C.evalN inp k) := by
        intro s hs
        cases s with
        | zero => rfl
        | one => rfl
        | row r' =>
          have h' : C.rank r' < k := by have := hs r' rfl; omega
          show C.evalN inp n r' = C.evalN inp k r'
          rw [ih _ h' r' rfl n (by omega), ih _ h' r' rfl k h']
      rw [hsrc (C.x r) fun r' h => C.hOrder r hi r' (Or.inl h),
        hsrc (C.y r) fun r' h => C.hOrder r hi r' (Or.inr (Or.inl h)),
        hsrc (C.c r) fun r' h => C.hOrder r hi r' (Or.inr (Or.inr h))]

/-- **The evaluation holds the input bits at the inputs.** -/
theorem ChiCircuit.eval_input (C : ChiCircuit ρ) (inp : ρ → Bool) (r : ρ) (h : C.isInput r) :
    C.eval inp r = inp r := by
  unfold ChiCircuit.eval
  rw [C.evalN_succ, if_pos h]

/-- **The evaluation satisfies every gate**: an input row's gate is `chiBits v v v = v`, any other
row's is how it was computed, from rows of lower rank, final by then. -/
theorem ChiCircuit.eval_satisfies (C : ChiCircuit ρ) (inp : ρ → Bool) :
    C.SatisfiesBits (C.eval inp) := by
  intro r
  by_cases hi : C.isInput r
  · obtain ⟨hx, hy, hc⟩ := C.hInput r hi
    rw [hx, hy, hc]
    show C.eval inp r = chiBits (C.eval inp r) (C.eval inp r) (C.eval inp r)
    cases C.eval inp r <;> rfl
  · have hsrc : ∀ s : Src ρ, (∀ r', s = .row r' → C.rank r' < C.rank r) →
        s.bval (C.evalN inp (C.rank r)) = s.bval (C.eval inp) := by
      intro s hs
      cases s with
      | zero => rfl
      | one => rfl
      | row r' => exact C.evalN_stable inp r' _ (hs r' rfl)
    show C.evalN inp (C.rank r + 1) r = _
    rw [C.evalN_succ, if_neg hi, hsrc (C.x r) fun r' h => C.hOrder r hi r' (Or.inl h),
      hsrc (C.y r) fun r' h => C.hOrder r hi r' (Or.inr (Or.inl h)),
      hsrc (C.c r) fun r' h => C.hOrder r hi r' (Or.inr (Or.inr h))]

/-- **It is the computation with those input bits**: any computation of `C` holding them is it. -/
theorem ChiCircuit.eq_eval (C : ChiCircuit ρ) (inp : ρ → Bool) (v : ρ → Bool)
    (hv : C.SatisfiesBits v) (hin : ∀ r, C.isInput r → v r = inp r) : v = C.eval inp :=
  C.bits_determined v _ hv (C.eval_satisfies inp) fun r h => (hin r h).trans (C.eval_input inp r h).symm

end Eval

/-! ## A circuit of `PcsCircuit` on given input bits -/

section Generic

variable {c : PcsCircuit.Circuit}

/-- **Input bits by input number**: row `c.inputs[k]` holds `bits k`. -/
def inputsOf (c : PcsCircuit.Circuit) (bits : ℕ → Bool) (r : Fin (2 ^ 22)) : Bool :=
  bits (List.idxOf (r : ℕ) c.inputs.toList)

theorem toChi_isInput (hI : InputRows c) (hO : Ordered c) (r : Fin (2 ^ 22)) :
    (toChi c hI hO).isInput r ↔ (r : ℕ) ∈ c.inputs := Iff.rfl

/-- **Input `k` of the evaluation holds `bits k`.** -/
theorem toChi_eval_input (hI : InputRows c) (hO : Ordered c) (hnd : c.inputs.toList.Nodup)
    (bits : ℕ → Bool) (k : ℕ) (hk : k < c.inputs.size) :
    natVal ((toChi c hI hO).eval (inputsOf c bits)) (c.inputs.getD k 0) = bits k := by
  have hmem : c.inputs.getD k 0 ∈ c.inputs := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some]
    exact Array.getElem_mem hk
  have hr : c.inputs.getD k 0 < 2 ^ 22 := (hI _ hmem).1
  unfold natVal
  rw [dif_pos hr, ChiCircuit.eval_input _ _ _ ((toChi_isInput hI hO _).mpr hmem)]
  unfold inputsOf
  have e : c.inputs.getD k 0 = c.inputs.toList[k]'(by simpa using hk) := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some,
      Array.getElem_toList]
  show bits (List.idxOf (c.inputs.getD k 0) c.inputs.toList) = bits k
  rw [e, List.Nodup.idxOf_getElem hnd]

/-- **The evaluation on a secret's input bits holds the secret** (`SecretInputs`), when the inputs
are `256 + 257 · 32` distinct rows. -/
theorem toChi_secretInputs (hI : InputRows c) (hO : Ordered c) (hnd : c.inputs.toList.Nodup)
    (hsize : c.inputs.size = 256 + 257 * PcsCircuit.depth) (s : PcsCircuit.Secret) :
    PcsCircuit.SecretInputs s (natVal ((toChi c hI hO).eval (inputsOf c fun k => s.inputs.getD k false)))
      c.inputs := by
  refine ⟨fun k hk => ?_, fun i hi => ⟨fun j hj => ?_, ?_⟩⟩
  · rw [toChi_eval_input hI hO hnd _ k (by rw [hsize]; omega), s.inputs_x k hk]
  · have hi' : i < 32 := hi
    rw [toChi_eval_input hI hO hnd _ _ (by rw [hsize]; unfold PcsCircuit.depth; omega),
      s.inputs_sibling i j hi hj]
  · have hi' : i < 32 := hi
    rw [toChi_eval_input hI hO hnd _ _ (by rw [hsize]; unfold PcsCircuit.depth; omega),
      s.inputs_direction i hi]

/-- **The public bits of a computation of `c` holding a well-formed secret are the statement's.** -/
theorem toChi_public_of (hI : InputRows c) (hO : Ordered c) (hsize : c.rows.size = 2 ^ logRows)
    (hP : PublicIsStatement c) (v : Fin (2 ^ 22) → Bool) (hv : (toChi c hI hO).SatisfiesBits v)
    (s : PcsCircuit.Secret) (hs : s.WellFormed) (hin : PcsCircuit.SecretInputs s (natVal v) c.inputs)
    (J : Fin 4) (j : Fin 128) :
    (toChi c hI hO).pubBit v (Fin.castLE (by norm_num) J) j =
      statementBit (bytes32 s.y) (bytes32 s.root) J j := by
  have hp := hP (natVal v) (circuitSat_toChi hI hO hsize v hv) s hs hin J j J.isLt j.isLt
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

/-- What cell `n` carries in `toChi c`: `carried`'s source. -/
theorem toChi_cellSrc_cellOf (hI : InputRows c) (hO : Ordered c) {n : ℕ} (hn : n < 2 ^ (22 + 2)) :
    (toChi c hI hO).cellSrc (cellOf n) = ofSrc (PcsCircuit.carried c.rows n) := by
  have hr : n / 4 < 2 ^ 22 := by
    have : (2 : ℕ) ^ (22 + 2) = 4 * 2 ^ 22 := by norm_num
    omega
  have e : cellOf n = rowCell ⟨n / 4, hr⟩ ⟨n % 4, Nat.mod_lt _ (by norm_num)⟩ := by
    rw [rowCell_eq_cellOf]
    congr 1
    show n = 4 * (n / 4) + n % 4
    omega
  rw [e, ChiCircuit.cellSrc_rowCell]
  unfold PcsCircuit.carried
  rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h | h | h | h
  · have hk : (⟨n % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) = 0 := Fin.ext h
    rw [hk, if_pos h]
    rfl
  · have hk : (⟨n % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) = 1 := Fin.ext h
    rw [hk, if_neg (by omega), if_pos h]
    rfl
  · have hk : (⟨n % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) = 2 := Fin.ext h
    rw [hk, if_neg (by omega), if_neg (by omega), if_pos h]
    rfl
  · have hk : (⟨n % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) = 3 := Fin.ext h
    rw [hk, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    show (Src.row ⟨n / 4, hr⟩ : Src (Fin (2 ^ 22))) =
      (if h : n / 4 < 2 ^ 22 then Src.row ⟨n / 4, h⟩ else Src.zero)
    rw [dif_pos hr]

end Generic

/-! ## `Circuit.outputs`, the Rust's evaluation -/

section Outputs

variable {c : PcsCircuit.Circuit}

/-- The first loop of `Circuit.outputs`: input `k`'s bit written at row `c.inputs[k]`. -/
def inputsArray (c : PcsCircuit.Circuit) (bits : Array Bool) : Array Bool :=
  (List.range c.inputs.size).foldl (fun v k => v.set! (c.inputs.getD k 0) (bits.getD k false))
    (Array.replicate c.rows.size false)

/-- A step of its second loop: row `r` set to its gate on the array. -/
def outStep (c : PcsCircuit.Circuit) (v : Array Bool) (r : ℕ) : Array Bool :=
  v.set! r (PcsCircuit.gateBits (PcsCircuit.readBit v (c.rows.getD r .idle).x)
    (PcsCircuit.readBit v (c.rows.getD r .idle).y) (PcsCircuit.readBit v (c.rows.getD r .idle).c))

/-- `Circuit.outputs`: the inputs written, then the rows from `512` on in order, then the public
rows. -/
theorem outputs_eq (bits : Array Bool) : c.outputs bits =
    (List.range' publicRows (c.rows.size - publicRows) ++ List.range publicRows).foldl (outStep c)
      (inputsArray c bits) := rfl

/-- Row `r` of `c` reads row `r'`. -/
def RowReads (c : PcsCircuit.Circuit) (r r' : ℕ) : Prop :=
  (c.rows.getD r .idle).x = .row r' ∨ (c.rows.getD r .idle).y = .row r' ∨
    (c.rows.getD r .idle).c = .row r'

/-- Each row of `L`, when its turn comes, is a row of `c` all of whose reads are done (in `T`, then
in `T` and the rows before it). -/
def ReadsDone (c : PcsCircuit.Circuit) : (ℕ → Prop) → List ℕ → Prop
  | _, [] => True
  | T, r :: L => (r < c.rows.size ∧ ∀ r', RowReads c r r' → T r') ∧
      ReadsDone c (fun x => T x ∨ x = r) L

theorem readsDone_mono : ∀ (L : List ℕ) (T T' : ℕ → Prop), (∀ x, T x → T' x) →
    ReadsDone c T L → ReadsDone c T' L
  | [], _, _, _, _ => trivial
  | _ :: L, _, _, h, ⟨⟨hr, hrd⟩, hL⟩ => ⟨⟨hr, fun r' h' => h _ (hrd r' h')⟩,
      readsDone_mono L _ _ (fun x hx => hx.imp_left (h x)) hL⟩

theorem readsDone_append : ∀ (L1 L2 : List ℕ) (T : ℕ → Prop), ReadsDone c T L1 →
    ReadsDone c (fun x => T x ∨ x ∈ L1) L2 → ReadsDone c T (L1 ++ L2)
  | [], L2, _, _, h2 => readsDone_mono L2 _ _ (fun x hx => hx.resolve_right List.not_mem_nil) h2
  | _ :: L1, L2, _, ⟨h0, h1⟩, h2 => ⟨h0, readsDone_append L1 L2 _ h1
      (readsDone_mono L2 _ _ (fun x hx => by
        rcases hx with hx | hx
        · exact Or.inl (Or.inl hx)
        · rcases List.mem_cons.mp hx with hx | hx
          · exact Or.inl (Or.inr hx)
          · exact Or.inr hx) h2)⟩

theorem readsDone_range' : ∀ (n a : ℕ) (T : ℕ → Prop),
    (∀ r, a ≤ r → r < a + n →
      r < c.rows.size ∧ ∀ r', RowReads c r r' → T r' ∨ (a ≤ r' ∧ r' < r)) →
    ReadsDone c T (List.range' a n)
  | 0, _, _, _ => trivial
  | n + 1, a, T, h => by
    rw [List.range'_succ]
    obtain ⟨hr, hrd⟩ := h a le_rfl (by omega)
    refine ⟨⟨hr, fun r' h' => (hrd r' h').resolve_right (by omega)⟩,
      readsDone_range' n (a + 1) _ fun r h1 h2 => ?_⟩
    obtain ⟨hr, hrd⟩ := h r (by omega) (by omega)
    refine ⟨hr, fun r' h' => ?_⟩
    rcases hrd r' h' with h' | ⟨h1', h2'⟩
    · exact Or.inl (Or.inl h')
    · by_cases e : r' = a
      · exact Or.inl (Or.inr e)
      · exact Or.inr ⟨by omega, h2'⟩

/-- **The second loop computes `ev`** when `ev` satisfies every gate: a row whose reads hold `ev`
gets its gate on them, `ev`'s bit. -/
theorem foldl_outStep (ev : ℕ → Bool)
    (hev : ∀ r < c.rows.size, ev r = (c.rows.getD r .idle).eval ev) :
    ∀ (L : List ℕ) (T : ℕ → Prop) (a : Array Bool), a.size = c.rows.size →
      (∀ r, T r → a.getD r false = ev r) → ReadsDone c T L →
      (L.foldl (outStep c) a).size = c.rows.size ∧
        ∀ r, (T r ∨ r ∈ L) → (L.foldl (outStep c) a).getD r false = ev r
  | [], T, a, ha, hT, _ => ⟨ha, fun r h => h.elim (hT r) (fun h => absurd h List.not_mem_nil)⟩
  | r :: L, T, a, ha, hT, ⟨⟨hr, hrd⟩, hL⟩ => by
    have hread : ∀ s : PcsCircuit.Src, (∀ r', s = .row r' → RowReads c r r') →
        PcsCircuit.readBit a s = PcsCircuit.read ev s := by
      intro s hs
      cases s with
      | zero => rfl
      | one => rfl
      | row r' => exact hT r' (hrd r' (hs r' rfl))
    have hsize : (outStep c a r).size = c.rows.size := by
      unfold outStep; rw [PcsCircuit.size_set!, ha]
    have hT' : ∀ x, (T x ∨ x = r) → (outStep c a r).getD x false = ev x := by
      intro x hx
      unfold outStep
      rw [PcsCircuit.getD_set!]
      by_cases hxr : x = r
      · rw [hxr, if_pos ⟨rfl, by rw [ha]; exact hr⟩,
          hread (c.rows.getD r .idle).x (fun r' h => Or.inl h),
          hread (c.rows.getD r .idle).y (fun r' h => Or.inr (Or.inl h)),
          hread (c.rows.getD r .idle).c (fun r' h => Or.inr (Or.inr h))]
        exact (hev r hr).symm
      · rw [if_neg (fun h => hxr h.1.symm)]
        exact hT x (hx.resolve_right hxr)
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := foldl_outStep ev hev L _ (outStep c a r) hsize hT' hL
    refine ⟨h1, fun x hx => h2 x ?_⟩
    rcases hx with hx | hx
    · exact Or.inl (Or.inl hx)
    · rcases List.mem_cons.mp hx with hx | hx
      · exact Or.inl (Or.inr hx)
      · exact Or.inr hx

theorem inputs_getD_toList (a : Array ℕ) (k : ℕ) (hk : k < a.size) :
    a.getD k 0 = a.toList[k]'(by simpa using hk) := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some,
    Array.getElem_toList]

/-- **The first loop writes input `k`'s bit at its row**, the rows being distinct. -/
theorem inputsArray_spec (hnd : c.inputs.toList.Nodup) (hlt : ∀ r ∈ c.inputs, r < c.rows.size)
    (bits : Array Bool) : (inputsArray c bits).size = c.rows.size ∧
      ∀ k < c.inputs.size,
        (inputsArray c bits).getD (c.inputs.getD k 0) false = bits.getD k false := by
  have key : ∀ j, j ≤ c.inputs.size →
      ((List.range j).foldl (fun v k => v.set! (c.inputs.getD k 0) (bits.getD k false))
        (Array.replicate c.rows.size false)).size = c.rows.size ∧
      ∀ k < j, ((List.range j).foldl (fun v k => v.set! (c.inputs.getD k 0) (bits.getD k false))
        (Array.replicate c.rows.size false)).getD (c.inputs.getD k 0) false =
          bits.getD k false := by
    intro j
    induction j with
    | zero => intro _; exact ⟨by simp, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hmem : c.inputs.getD j 0 ∈ c.inputs := by
        rw [inputs_getD_toList _ _ (by omega)]
        exact Array.mem_def.mpr (List.getElem_mem _)
      refine ⟨by rw [PcsCircuit.size_set!, h1], fun k hk => ?_⟩
      rw [PcsCircuit.getD_set!]
      by_cases hkj : k = j
      · rw [hkj, if_pos ⟨rfl, by rw [h1]; exact hlt _ hmem⟩]
      · rw [if_neg (fun h => hkj ?_)]
        · exact h2 k (by omega)
        · have e := h.1
          rw [inputs_getD_toList _ _ (by omega), inputs_getD_toList _ _ (by omega)] at e
          exact ((List.Nodup.getElem_inj_iff hnd).mp e).symm
  exact key c.inputs.size le_rfl

theorem rowReads_input (hI : InputRows c) {r r' : ℕ} (hin : r ∈ c.inputs) (h : RowReads c r r') :
    r' = r := by
  obtain ⟨-, -, hrow⟩ := hI r hin
  unfold RowReads at h
  rw [hrow] at h
  rcases h with h | h | h <;> exact (PcsCircuit.Src.row.inj h).symm

theorem rowReads_ranked (hO : Ordered c) {r r' : ℕ} (hr : r < 2 ^ logRows) (hin : r ∉ c.inputs)
    (h : RowReads c r r') : r' < 2 ^ logRows ∧ PcsCircuit.rank r' < PcsCircuit.rank r := by
  obtain ⟨hx, hy, hc⟩ := hO r hr hin
  rcases h with h | h | h
  · rw [h] at hx; exact hx
  · rw [h] at hy; exact hy
  · rw [h] at hc; exact hc

/-- **`Circuit.outputs` is the evaluation**: for a circuit of `2^22` rows whose inputs are distinct
rows reading themselves and whose other rows read lower ranks, the Rust's `outputs` on the input
bits `bits` is the circuit evaluated on them. So it satisfies every gate. -/
theorem toChi_eval_eq_outputs (hI : InputRows c) (hO : Ordered c)
    (hsize : c.rows.size = 2 ^ logRows) (hnd : c.inputs.toList.Nodup) (bits : Array Bool)
    (r : Fin (2 ^ 22)) :
    (toChi c hI hO).eval (inputsOf c fun k => bits.getD k false) r =
      (c.outputs bits).getD r false := by
  have hN : c.rows.size = 4194304 := by rw [hsize]; rfl
  have hev := circuitSat_toChi hI hO hsize _
    (ChiCircuit.eval_satisfies _ (inputsOf c fun k => bits.getD k false))
  obtain ⟨ha1, ha2⟩ := inputsArray_spec hnd (fun r hr => hsize ▸ (hI r hr).1) bits
  have hT : ∀ x, x ∈ c.inputs → (inputsArray c bits).getD x false =
      natVal ((toChi c hI hO).eval (inputsOf c fun k => bits.getD k false)) x := by
    intro x hx
    obtain ⟨k, hk, hkx⟩ := Array.mem_iff_getElem.mp hx
    have e : c.inputs.getD k 0 = x := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some, hkx]
    rw [← e, ha2 k hk, toChi_eval_input hI hO hnd _ k hk]
  have hrd : ReadsDone c (· ∈ c.inputs)
      (List.range' publicRows (c.rows.size - publicRows) ++ List.range publicRows) := by
    refine readsDone_append _ _ _ (readsDone_range' _ _ _ fun r h1 h2 => ?_) ?_
    · rw [hN] at h2
      simp only [publicRows] at h1 h2 ⊢
      have hr : r < 2 ^ logRows := by simp only [logRows, Nat.reducePow]; omega
      refine ⟨by rw [hN]; omega, fun r' h' => ?_⟩
      by_cases hin : r ∈ c.inputs
      · exact Or.inl (rowReads_input hI hin h' ▸ hin)
      · obtain ⟨-, hrk⟩ := rowReads_ranked hO hr hin h'
        refine Or.inr ?_
        unfold PcsCircuit.rank at hrk
        rw [if_neg (show ¬ r < publicRows by unfold publicRows; omega)] at hrk
        by_cases h3 : r' < publicRows
        · rw [if_pos h3] at hrk
          simp only [publicRows, logRows, Nat.reducePow] at hrk h3; omega
        · rw [if_neg h3] at hrk
          simp only [publicRows] at h3; omega
    · rw [List.range_eq_range']
      refine readsDone_range' _ _ _ fun r _ h2 => ?_
      simp only [publicRows] at h2
      have hr : r < 2 ^ logRows := by simp only [logRows, Nat.reducePow]; omega
      have hin : r ∉ c.inputs := fun h => by
        have := (hI r h).2.1; simp only [publicRows] at this; omega
      refine ⟨by rw [hN]; omega, fun r' h' => ?_⟩
      obtain ⟨hr', hrk⟩ := rowReads_ranked hO hr hin h'
      simp only [logRows, Nat.reducePow] at hr'
      unfold PcsCircuit.rank at hrk
      by_cases h5 : 512 ≤ r'
      · refine Or.inl (Or.inr (List.mem_range'_1.mpr ⟨?_, ?_⟩)) <;>
          simp only [publicRows, hN] <;> omega
      · refine Or.inr ⟨Nat.zero_le _, ?_⟩
        rw [if_pos (show r' < publicRows by unfold publicRows; omega),
          if_pos (show r < publicRows by unfold publicRows; omega)] at hrk
        omega
  obtain ⟨-, hfin⟩ := foldl_outStep _ hev _ _ _ ha1 hT hrd
  rw [outputs_eq, hfin r ?_]
  · unfold natVal
    rw [dif_pos r.isLt]
  · refine Or.inr (List.mem_append.mpr ?_)
    have hr := r.isLt
    simp only [Nat.reducePow] at hr
    by_cases h5 : publicRows ≤ (r : ℕ)
    · refine Or.inl (List.mem_range'_1.mpr ⟨h5, ?_⟩)
      rw [hN]; simp only [publicRows] at h5 ⊢; omega
    · exact Or.inr (List.mem_range.mpr (by simp only [publicRows] at h5 ⊢; omega))

end Outputs

/-! ## The deployed circuit -/

/-- **The honest assignment**: `deployed` evaluated on `membership_inputs(s)`, input `k` holding
bit `k` of `Secret.inputs`. -/
noncomputable def deployedAssign (s : PcsCircuit.Secret) : Fin (2 ^ 22) → Bool :=
  deployed.eval (inputsOf membership fun k => s.inputs.getD k false)

/-- **It satisfies every gate of the deployed circuit.** -/
theorem deployedAssign_satisfies (s : PcsCircuit.Secret) : deployed.SatisfiesBits (deployedAssign s) :=
  ChiCircuit.eval_satisfies _ _

/-- **Its input bits are the secret's**, in `membership_inputs`' order. -/
theorem deployedAssign_secretInputs (s : PcsCircuit.Secret) :
    PcsCircuit.SecretInputs s (natVal (deployedAssign s)) membership.inputs :=
  toChi_secretInputs _ _ PcsCircuit.membership_inputs_nodup PcsCircuit.membership_inputs_size s

/-- **Input `k` holds bit `k` of `membership_inputs(s)`.** -/
theorem deployedAssign_input (s : PcsCircuit.Secret) (k : ℕ) (hk : k < membership.inputs.size) :
    natVal (deployedAssign s) (membership.inputs.getD k 0) = s.inputs.getD k false :=
  toChi_eval_input _ _ PcsCircuit.membership_inputs_nodup _ k hk

/-- **Keccak correctness, forward**: for a well-formed secret (`x` and the siblings `32` bytes),
bit `j` of public word `J < 4` of the honest assignment is bit `j` of the statement word: the
halves of `y = H(x ‖ 0x11^32)` and of the root of the path from `H(x ‖ 0x22^32)`. -/
theorem deployedAssign_public (s : PcsCircuit.Secret) (hs : s.WellFormed) (J : Fin 4) (j : Fin 128) :
    deployed.pubBit (deployedAssign s) (Fin.castLE (by norm_num) J) j =
      statementBit (bytes32 s.y) (bytes32 s.root) J j :=
  toChi_public_of _ _ PcsCircuit.membership_rows_size PcsCircuit.membership_public _
    (deployedAssign_satisfies s) s hs (deployedAssign_secretInputs s) J j

/-- **The honest cells prove membership** of the secret's statement, in soundness's terms
(`ProvesMembership`): they hold a computation of `deployed` whose input bits are a secret hashing
to `(y, root)`. -/
theorem deployedAssign_provesMembership {F : Type} [Field F] [DecidableEq F] [CharP F 2] (s : PcsCircuit.Secret)
    (hs : s.WellFormed) :
    ProvesMembership (deployed.cellsOfBits (deployedAssign s) : (Fin (22 + 2) → Bool) → F)
      (bytes32 s.y) (bytes32 s.root) :=
  ProvesBits.membership ⟨deployedAssign s, deployed.cellsOfBits_computes _ (deployedAssign_satisfies s),
    deployedAssign_public s hs⟩

/-- What cell `n` carries in `deployed`. -/
theorem deployed_cellSrc_cellOf {n : ℕ} (hn : n < 2 ^ (22 + 2)) :
    deployed.cellSrc (cellOf n) = ofSrc (PcsCircuit.carried membership.rows n) :=
  toChi_cellSrc_cellOf _ _ hn

/-- **The deployed σ keeps what each cell carries**: a cell and its successor read the same
source (or are the `V` cell of a row and a cell reading it). So a computation's cells, each
holding the bit of what it carries, are copied by σ. -/
theorem deployedSigma_cellSrc (z : Fin (22 + 2) → Bool) :
    deployed.cellSrc (deployedSigma z) = deployed.cellSrc z := by
  obtain ⟨n, hn, rfl⟩ := exists_cellOf z
  have hn' : n < 4 * 2 ^ logRows := four_mul_rows ▸ hn
  have hσ : membership.sigma.getD n 0 < 2 ^ (22 + 2) :=
    four_mul_rows ▸ PcsCircuit.membership_sigma_lt n hn'
  rw [deployedSigma_cellOf hn, deployed_cellSrc_cellOf hσ, deployed_cellSrc_cellOf hn]
  congr 1
  apply PcsCircuit.slot_injective
  rw [PcsCircuit.slot_carried, PcsCircuit.slot_carried, PcsCircuit.membership_sigma_slot n hn']

/-- **The honest assignment is the Rust's `Circuit::outputs`** on `membership_inputs(s)`
(`Circuit.outputs`, which `CircuitTest/Dump.lean` compares with the Rust's). -/
theorem deployedAssign_eq_outputs (s : PcsCircuit.Secret) (r : Fin (2 ^ 22)) :
    deployedAssign s r = (membership.outputs s.inputs).getD r false :=
  toChi_eval_eq_outputs _ _ PcsCircuit.membership_rows_size PcsCircuit.membership_inputs_nodup _ r

/-- **`Circuit.outputs` satisfies every gate of the deployed circuit.** -/
theorem outputs_satisfies (s : PcsCircuit.Secret) :
    deployed.SatisfiesBits fun r => (membership.outputs s.inputs).getD r false := by
  have h : (fun r : Fin (2 ^ 22) => (membership.outputs s.inputs).getD r false) =
      deployedAssign s := funext fun r => (deployedAssign_eq_outputs s r).symm
  rw [h]
  exact deployedAssign_satisfies s

end QuotientSecurity
