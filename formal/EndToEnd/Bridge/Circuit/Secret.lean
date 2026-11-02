-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import Bridge.Circuit
import QuotientSecurity.Deployed

/-!
# The secret the input bits spell, and the relation

The statement reads a secret off the membership circuit's input bits (`PcsQuotient.secretOfInputs`:
`x`'s `256` bits, then each level's `256` sibling bits and its direction bit, a byte's bits low
first); F0b reads the same secret off them (`PcsCircuit.secretOfBits`, and
`QuotientSecurity.secretOf v`, the input bits of the computation `v`). **`secretMatches`**: if
F0b's secret of `v` hashes to the statement's `y` and root (natively, Keccak-256 both sides), the
statement's secret of the input rows' bits of `v` satisfies the statement's `Relation`
(`Bridge.SecretMatches` of `Bridge/Extractor.lean`). On the way: `secretOfInputs_x`,
`secretOfInputs_siblings`, `secretOfInputs_directions` (the two byte layouts agree on the first
`8480` bits), `statement_secretOfInputs` (the statement a secret proves, natively, is F0b's
`Secret.y` and `Secret.root`).
-/

namespace Bridge.Circuit

/-! ## Bytes from bits -/

theorem byte_fold (f : ℕ → Bool) :
    (List.range 8).foldl (fun acc k => if f k then acc ||| ((1 : UInt8) <<< k.toUInt8) else acc) 0 =
      PcsCircuit.byteOfBits f := by
  unfold PcsCircuit.byteOfBits
  rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil]
  generalize f 0 = b0
  generalize f 1 = b1
  generalize f 2 = b2
  generalize f 3 = b3
  generalize f 4 = b4
  generalize f 5 = b5
  generalize f 6 = b6
  generalize f 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide

theorem byteOfBits_congr {f g : ℕ → Bool} (h : ∀ t < 8, f t = g t) :
    PcsCircuit.byteOfBits f = PcsCircuit.byteOfBits g := by
  unfold PcsCircuit.byteOfBits
  congr 2
  exact List.map_congr_left fun t ht => h t (List.mem_range.mp ht)

theorem bytesOfBits_congr {f g : ℕ → Bool} (h : ∀ t < 256, f t = g t) :
    PcsCircuit.bytesOfBits f = PcsCircuit.bytesOfBits g := by
  unfold PcsCircuit.bytesOfBits
  exact List.map_congr_left fun p hp => byteOfBits_congr fun t ht => h _ (by
    have := List.mem_range.mp hp; omega)

/-- The statement's `32` bytes from bit `from_` on are F0b's. -/
theorem qbytes_toList (bits : List Bool) (from_ : ℕ) :
    (Vector.ofFn fun j : Fin 32 => (List.range 8).foldl (fun acc k =>
        if bits.getD (from_ + 8 * j.val + k) false then acc ||| ((1 : UInt8) <<< k.toUInt8) else acc)
        0).toList =
      PcsCircuit.bytesOfBits fun t => bits.getD (from_ + t) false := by
  unfold PcsCircuit.bytesOfBits
  apply List.ext_getElem (by simp)
  intro p h1 h2
  simp only [Vector.getElem_toList, Vector.getElem_ofFn, List.getElem_map, List.getElem_range]
  rw [byte_fold]
  exact byteOfBits_congr fun t _ => by rw [Nat.add_assoc]

/-! ## The statement's secret of bits -/

theorem secretOfInputs_x (bits : List Bool) :
    (PcsQuotient.secretOfInputs bits).x.toList = PcsCircuit.bytesOfBits fun t => bits.getD t false := by
  have := qbytes_toList bits 0
  simp only [Nat.zero_add] at this
  rw [← this]
  rfl

theorem secretOfInputs_siblings (bits : List Bool) (i : Fin PcsQuotient.depth) :
    (PcsQuotient.secretOfInputs bits).siblings[i].toList =
      PcsCircuit.bytesOfBits fun t => bits.getD (256 + 257 * i.val + t) false := by
  rw [← qbytes_toList bits (256 + 257 * i.val)]
  simp [PcsQuotient.secretOfInputs]

theorem secretOfInputs_directions (bits : List Bool) (i : Fin PcsQuotient.depth) :
    (PcsQuotient.secretOfInputs bits).directions[i] = bits.getD (256 + 257 * i.val + 256) false := by
  simp [PcsQuotient.secretOfInputs]

/-! ## Native hashing on both sides -/

theorem pair_toList (l r : PcsQuotient.Bytes32) :
    (PcsQuotient.pair l r).toList = PcsCircuit.H (l.toList ++ r.toList) := by
  simp [PcsQuotient.pair, PcsCircuit.H, LeanVM.Protocol.Digest.toBytes]

theorem finRange_map_val (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem foldl_sim {α β γ : Type} (R : β → γ → Prop) (f : β → α → β) (g : γ → α → γ) :
    ∀ (l : List α) (a : β) (b : γ), R a b → (∀ x ∈ l, ∀ a b, R a b → R (f a x) (g b x)) →
      R (l.foldl f a) (l.foldl g b)
  | [], _, _, h, _ => h
  | x :: l, a, b, h, hs =>
    foldl_sim R f g l _ _ (hs x (List.mem_cons_self ..) a b h)
      fun y hy => hs y (List.mem_cons_of_mem _ hy)

/-- **The statement a secret proves**, natively: `y` and the root are F0b's `Secret.y` and
`Secret.root` of a secret with the same `x`, siblings and directions. -/
theorem statement_secretOfInputs (w : PcsQuotient.Secret) (s : PcsCircuit.Secret)
    (hx : w.x.toList = s.x) (hs : ∀ i : Fin PcsQuotient.depth, w.siblings[i].toList = s.siblings.getD i [])
    (hd : ∀ i : Fin PcsQuotient.depth, w.directions[i] = s.directions.testBit i) :
    w.statement.y.toList = s.y ∧ w.statement.root.toList = s.root := by
  refine ⟨?_, ?_⟩
  · simp only [PcsQuotient.Secret.statement, pair_toList, hx, Vector.toList_replicate]
    rfl
  · simp only [PcsQuotient.Secret.statement, PcsQuotient.Secret.root, PcsCircuit.Secret.root]
    rw [← finRange_map_val, List.foldl_map]
    refine foldl_sim (fun (n : PcsQuotient.Bytes32) (m : List UInt8) => n.toList = m) _ _ _ _ _ ?_
      fun i _ a b hab => ?_
    · simp only [PcsQuotient.Secret.leaf, pair_toList, hx, Vector.toList_replicate]
      rfl
    · simp only [PcsCircuit.Secret.up]
      rw [← hd i, ← hs i]
      split <;> simp only [pair_toList, hab]

/-! ## The secret of the input rows' bits -/

attribute [local irreducible] PcsQuotient.membership PcsCircuit.membership

theorem getD_map_bits (l : List ℕ) (f : ℕ → Bool) (k : ℕ) (hk : k < l.length) :
    (l.map f).getD k false = f (l.getD k 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem pc_inputs_size : PcsCircuit.membership.inputs.size = 256 + 257 * PcsCircuit.depth := by
  obtain ⟨y, root, bf, he, -, -, hsz, -⟩ := PcsCircuit.membership_spec
  rw [he, PcsCircuit.finish_inputs]
  exact hsz

theorem secretOfBits_x (B : ℕ → Bool) : (PcsCircuit.secretOfBits B).x = PcsCircuit.bytesOfBits B := rfl

theorem secretOfBits_siblings (B : ℕ → Bool) (i : Fin PcsQuotient.depth) :
    (PcsCircuit.secretOfBits B).siblings.getD i [] =
      PcsCircuit.bytesOfBits fun j => B (256 + 257 * i.val + j) := by
  simp only [PcsCircuit.secretOfBits, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (show (i : ℕ) < PcsCircuit.depth from i.isLt), Option.map_some,
    Option.getD_some]

theorem secretOfBits_directions (B : ℕ → Bool) (i : Fin PcsQuotient.depth) :
    (PcsCircuit.secretOfBits B).directions.testBit i = B (256 + 257 * i.val + 256) := by
  simp only [PcsCircuit.secretOfBits]
  rw [PcsCircuit.bitsToNat_testBit]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (show (i : ℕ) < PcsCircuit.depth from i.isLt), Option.map_some,
    Option.getD_some]

/-- **The statement's secret of bits is F0b's** on the first `8480` bits (`256 + 32 · 257`, all
the circuit's inputs): the same `x`, siblings and directions. -/
theorem secretOfInputs_fields (bits : List Bool) (B : ℕ → Bool)
    (hB : ∀ k < 8480, bits.getD k false = B k) :
    (PcsQuotient.secretOfInputs bits).x.toList = (PcsCircuit.secretOfBits B).x ∧
      (∀ i : Fin PcsQuotient.depth, (PcsQuotient.secretOfInputs bits).siblings[i].toList =
        (PcsCircuit.secretOfBits B).siblings.getD i []) ∧
      ∀ i : Fin PcsQuotient.depth, (PcsQuotient.secretOfInputs bits).directions[i] =
        (PcsCircuit.secretOfBits B).directions.testBit i := by
  refine ⟨?_, fun i => ?_, fun i => ?_⟩
  · rw [secretOfInputs_x, secretOfBits_x]
    exact bytesOfBits_congr fun t ht => hB t (by omega)
  · rw [secretOfInputs_siblings, secretOfBits_siblings]
    exact bytesOfBits_congr fun t ht => hB _ (by have : (i : ℕ) < 32 := i.isLt; omega)
  · rw [secretOfInputs_directions, secretOfBits_directions]
    exact hB _ (by have : (i : ℕ) < 32 := i.isLt; omega)

theorem secretOf_eq (v : Fin (2 ^ 22) → Bool) : QuotientSecurity.secretOf v =
    PcsCircuit.secretOfBits fun k => QuotientSecurity.natVal v (PcsCircuit.membership.inputs.getD k 0) :=
  rfl

/-- The input rows' bits of `v`, read as the statement reads them (`inputBitsOfStack`), are F0b's
`secretOf`'s on the first `8480`. -/
theorem inputBits_getD (v : Fin (2 ^ 22) → Bool) (k : ℕ) (hk : k < 8480) :
    ((PcsQuotient.membership 22).inputs.toList.map (QuotientSecurity.natVal v)).getD k false =
      QuotientSecurity.natVal v (PcsCircuit.membership.inputs.getD k 0) := by
  have hsz := pc_inputs_size
  have hdepth : PcsCircuit.depth = 32 := rfl
  rw [hdepth] at hsz
  rw [membership_inputs, getD_map_bits _ _ _ (by simp; omega)]
  simp only [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-- **The secret matches** (`Bridge.SecretMatches`): if F0b's secret of the computation `v` hashes
to the statement's `y` and root, the statement's secret of the input rows' bits of `v` is a witness
of the statement. -/
theorem secretMatches : ∀ (stmt : PcsQuotient.Statement) (v : Fin (2 ^ 22) → Bool),
    QuotientSecurity.bytes32 (QuotientSecurity.secretOf v).y = (fun i => stmt.y.get i) →
    QuotientSecurity.bytes32 (QuotientSecurity.secretOf v).root = (fun i => stmt.root.get i) →
      PcsQuotient.Relation stmt (PcsQuotient.secretOfInputs
        ((PcsQuotient.membership 22).inputs.toList.map (QuotientSecurity.natVal v))) := by
  intro stmt v hy hr
  obtain ⟨hx, hs, hd⟩ := secretOfInputs_fields _ _ (inputBits_getD v)
  rw [← secretOf_eq] at hx hs hd
  obtain ⟨ey, er⟩ := statement_secretOfInputs _ _ hx hs hd
  have key : ∀ (a b : PcsQuotient.Bytes32) (l : List UInt8), a.toList = l →
      QuotientSecurity.bytes32 l = (fun i => b.get i) → a = b := by
    intro a b l hal hl
    apply Vector.ext
    intro i hi
    have := congrFun hl ⟨i, hi⟩
    simp only [QuotientSecurity.bytes32, ← hal] at this
    rw [List.getD_eq_getElem?_getD, Vector.getElem?_toList, Vector.getElem?_eq_getElem hi,
      Option.getD_some] at this
    rw [this]
    rfl
  show PcsQuotient.Secret.statement _ = stmt
  obtain ⟨sy, sr⟩ := stmt
  have h1 := key _ sy _ ey hy
  have h2 := key _ sr _ er hr
  cases h : PcsQuotient.Secret.statement (PcsQuotient.secretOfInputs
    ((PcsQuotient.membership 22).inputs.toList.map (QuotientSecurity.natVal v)))
  rw [h] at h1 h2
  simp only at h1 h2
  rw [h1, h2]

end Bridge.Circuit
