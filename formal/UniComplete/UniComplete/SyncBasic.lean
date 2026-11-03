-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.Prover
import UniComplete.VerifierH

/-!
# The prover and the verifier in step: the channels' synchronisation and its primitives

The honest prover writes the stream (`Wr`, `Basic.lean`); the verifier reads it (`Chan`, `Transcript.lean`).
Here, at a pure Keccak-256 `H : List UInt8 → Digest` (the monad `Id`, the hash `pure ∘ H`), the verifier reads back
what the prover wrote and draws the same challenges.

* **`Synced w c`**: the channel's cursor is the writer's stream size, its sponge (`absorbed`, `state`) and its
  challenges are the writer's, and its data starts with the writer's stream.
* **Bytes**: `beWordAt` reads back `be64` (`beWordAt_of`, through `toNat`: the big-endian fold of the first `j`
  bytes is the word divided by `2^(8(8 − j))`); a scalar's limbs (`eNew_limbs`); a root's halves without their top
  limbs (`rootRead`, `= halves` when the top limbs are zero, as `digestScalars` makes them); a 4-byte integer below
  `2^32` (`integerWire_fold`).
* **`Reads v B a zs`**: the verifier action `v` reads the bytes `B` at the cursor, returns `a` and collects `zs`
  (whatever else the channel holds). `takeBytes`, `nextScalar`, `nextScalars`, `nextRoot`, `nextInteger 4`,
  `requireZero` are readers; readers compose (`Reads.bind`, `Reads.forIn`: a loop whose every pass reads).
* **`Writes p w b B`**: the prover action `p` from `w` returns `b`, only appending `B` (`sendBytes`, …;
  `Writes.bind`, `Writes.forIn`).
* **`Steps v p pos w a b pos' w' zs`**, the workhorse: the verifier may *trail* the prover (bytes written, not yet
  read): from the verifier at `pos` with `w`'s sponge, `p` from `w` returns `b` at `w'` (only appending) and `v`
  returns `a`, collects `zs` and ends at `pos'` with `w'`'s sponge, on any data covering `w'`'s stream.
  `Steps.bind` (both sides), `Steps.vbind` (a verifier-only first step, `Reads`), `Steps.pbind` (a prover-only first
  step, `Writes`), `Steps.sample` (the challenge: both at the end of the stream, the same input bytes),
  `Steps.samples`.
* **`Syncs v p w a zs`** (the interface the other layers state their hypotheses in): `Steps` from a synchronised
  channel to a synchronised channel (`Synced` both sides): `Syncs.bind`, and the primitives: `nextScalar`/
  `sendScalar`, `nextScalars`/`sendScalars`, `nextRoot`/`sendRoot`, `nextInteger 4`/`sendInteger n 4`,
  `sampleH`/`sampleW`, `samplesH`/`samplesW`, `requireZero`; `finish` succeeds when the data is the writer's
  stream (`finish_synced`).
* **The two steps stated as hypotheses** (proved elsewhere; `SyncVerifier.lean` takes them): `FlockSyncs` (Flock's
  prover against `Flock.verifyDeferredH`: the verifier returns the prover's point, end and pending matrices, collects
  nothing) and `BatchSyncs` (the batching sumcheck's prover, `batchProver`, against `batchH`: the verifier returns
  the prover's point claims, `pointOpening`, and its matrices' claim, and collects one value, `terminal w`).

Decisions:

* `Synced`'s data condition is a prefix (`w.stream.toList <+: c.data.toList`): the verifier runs on the final
  stream, of which every stream the writer had is a prefix.
* A synchronised channel is determined by its data and its collected values (`Synced.eq_chanAt`), so the step
  lemmas are equations on `chanAt D pos w Z` (data `D`, cursor `pos`, `w`'s sponge, collected `Z`), which compose
  by rewriting.
* `zs` (the values collected) is a list, appended to the channel's `zeros`: the end statement reads the collected
  values off the steps.
* No `bv_decide`, no `native_decide`: the byte round trips go through `UInt64.toNat` (`Nat.shiftLeft_add_eq_or_of_lt`).
-/

namespace UniComplete

open UniStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-! ## Bytes -/

section Bytes

/-- Byte `k < 8` of `be64 w`. -/
theorem be64_getD (w : UInt64) {k : ℕ} (hk : k < 8) :
    (be64 w).getD k 0 = (w >>> (8 * (7 - k)).toUInt64).toUInt8 := by
  simp [be64, List.getD_eq_getElem?_getD, hk]

/-- Byte `k < 8` of `be64 w`, as a number: the word's base-256 digit `7 − k`. -/
theorem be64_byte_toNat (w : UInt64) {k : ℕ} (hk : k < 8) :
    ((w >>> (8 * (7 - k)).toUInt64).toUInt8).toNat = w.toNat / 2 ^ (8 * (7 - k)) % 256 := by
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, UInt64.toNat_ofNat']
  have h1 : 8 * (7 - k) % 2 ^ 64 = 8 * (7 - k) := Nat.mod_eq_of_lt (by omega)
  have h2 : 8 * (7 - k) % 64 = 8 * (7 - k) := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2]

/-- The big-endian fold of `be64 w`'s first `j` bytes is `w / 2^(8 (8 − j))`. -/
theorem be64_fold_toNat (w : UInt64) : ∀ j ≤ 8,
    ((List.range j).foldl (fun (acc : UInt64) k ↦ (acc <<< 8) ||| ((w >>> (8 * (7 - k)).toUInt64).toUInt8).toUInt64)
      (0 : UInt64)).toNat = w.toNat / 2 ^ (8 * (8 - j))
  | 0, _ => by
    have hw := w.toNat_lt
    simp only [List.range_zero, List.foldl_nil, UInt64.toNat_zero]
    exact (Nat.div_eq_of_lt hw).symm
  | j + 1, hj => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, UInt64.toNat_or,
      UInt64.toNat_shiftLeft, be64_fold_toNat w j (by omega), UInt8.toNat_toUInt64,
      be64_byte_toNat w (by omega)]
    have h8 : (8 : UInt64).toNat % 64 = 8 := rfl
    rw [h8]
    set m := w.toNat / 2 ^ (8 * (7 - j)) with hm
    have hpow : 2 ^ (8 * (8 - j)) = 2 ^ (8 * (7 - j)) * 2 ^ 8 := by
      rw [← pow_add]; congr 1; omega
    have hq : w.toNat / 2 ^ (8 * (8 - j)) = m / 2 ^ 8 := by
      rw [hpow, ← Nat.div_div_eq_div_mul]
    have hlast : w.toNat / 2 ^ (8 * (8 - (j + 1))) = m := by
      rw [hm]; congr 2; omega
    rw [hq, hlast]
    have hmw : m ≤ w.toNat := Nat.div_le_self _ _
    have hw := w.toNat_lt
    have hsl : (m / 2 ^ 8) <<< 8 = m / 2 ^ 8 * 2 ^ 8 := Nat.shiftLeft_eq _ _
    have hle : m / 2 ^ 8 * 2 ^ 8 ≤ m := Nat.div_mul_le_self _ _
    rw [hsl, Nat.mod_eq_of_lt (by omega), ← hsl,
      ← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by norm_num)), hsl]
    exact Nat.div_add_mod' m (2 ^ 8)

/-- The big-endian fold of `be64 w` is `w`. -/
theorem be64_fold (w : UInt64) :
    (List.range 8).foldl (fun (acc : UInt64) k ↦ (acc <<< 8) ||| ((w >>> (8 * (7 - k)).toUInt64).toUInt8).toUInt64)
      (0 : UInt64) = w := by
  apply UInt64.toNat_inj.mp
  rw [be64_fold_toNat w 8 le_rfl]
  simp

/-- **`beWordAt` reads back `be64`**: if the array holds `be64 w` at `s`, the word at `s` is `w`. -/
theorem beWordAt_of {a : Array UInt8} {pre post : List UInt8} {w : UInt64}
    (h : a.toList = pre ++ be64 w ++ post) : beWordAt a pre.length = w := by
  unfold beWordAt
  rw [List.foldl_ext _ (fun (acc : UInt64) k ↦ (acc <<< 8) ||| ((w >>> (8 * (7 - k)).toUInt64).toUInt8).toUInt64)]
  · exact be64_fold w
  · intro acc k hk
    have hk8 : k < 8 := List.mem_range.mp hk
    congr 2
    have e1 : (pre ++ (be64 w ++ post))[pre.length + k]? = (be64 w ++ post)[k]? := by
      rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    have e2 : (be64 w ++ post)[k]? = (be64 w)[k]? := List.getElem?_append_left (by simp [be64, hk8])
    rw [← be64_getD w hk8, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, h, List.append_assoc, e1, e2,
      List.getD_eq_getElem?_getD]

/-- `beWordAt` at `0` of a list starting with `be64 w`. -/
theorem beWordAt_zero_of {a : Array UInt8} {post : List UInt8} {w : UInt64}
    (h : a.toList = be64 w ++ post) : beWordAt a 0 = w :=
  beWordAt_of (pre := []) (by simpa using h)

/-- A scalar's limbs, as `next_scalar` rebuilds it. -/
theorem eNew_limbs (x : E) : eNew (x.limb 0).lane (x.limb 1).lane (x.limb 2).lane = x := ofLimbs_limb x

@[simp] theorem length_be64 (w : UInt64) : (be64 w).length = 8 := by simp [be64]

@[simp] theorem length_scalarWire (x : E) : (scalarWire x).length = 24 := by simp [scalarWire]

@[simp] theorem length_rootWord (halves : E × E) : (rootWord halves).length = 32 := by simp [rootWord]

@[simp] theorem length_integerWire (n bytes : ℕ) : (integerWire n bytes).length = bytes := by
  simp [integerWire]

/-- The scalar `next_scalar` reads from `scalarWire x`. -/
theorem scalarWire_read (x : E) :
    eNew (beWordAt (scalarWire x).toArray 16) (beWordAt (scalarWire x).toArray 8)
      (beWordAt (scalarWire x).toArray 0) = x := by
  have h0 : beWordAt (scalarWire x).toArray 0 = (x.limb 2).lane :=
    beWordAt_zero_of (post := be64 (x.limb 1).lane ++ be64 (x.limb 0).lane) (by simp [scalarWire])
  have h8 : beWordAt (scalarWire x).toArray 8 = (x.limb 1).lane := by
    have := beWordAt_of (a := (scalarWire x).toArray) (pre := be64 (x.limb 2).lane)
      (post := be64 (x.limb 0).lane) (w := (x.limb 1).lane) (by simp [scalarWire])
    simpa using this
  have h16 : beWordAt (scalarWire x).toArray 16 = (x.limb 0).lane := by
    have := beWordAt_of (a := (scalarWire x).toArray) (pre := be64 (x.limb 2).lane ++ be64 (x.limb 1).lane)
      (post := []) (w := (x.limb 0).lane) (by simp [scalarWire])
    simpa using this
  rw [h0, h8, h16, eNew_limbs]

/-- **The root `next_root` reads** from `rootWord halves`: each half without its top limb (a root's halves, as
`digestScalars` makes them, have none: `rootRead_of`). -/
def rootRead (halves : E × E) : E × E :=
  (eNew (halves.1.limb 0).lane (halves.1.limb 1).lane 0, eNew (halves.2.limb 0).lane (halves.2.limb 1).lane 0)

/-- Halves without top limbs are read back as they are. -/
theorem rootRead_of {halves : E × E} (h1 : halves.1.limb 2 = 0) (h2 : halves.2.limb 2 = 0) :
    rootRead halves = halves := by
  have e1 : eNew (halves.1.limb 0).lane (halves.1.limb 1).lane 0 = halves.1 := by
    have := eNew_limbs halves.1
    rw [h1] at this
    exact this
  have e2 : eNew (halves.2.limb 0).lane (halves.2.limb 1).lane 0 = halves.2 := by
    have := eNew_limbs halves.2
    rw [h2] at this
    exact this
  simp only [rootRead, e1, e2]

/-- The four words `next_root` reads from `rootWord halves`. -/
theorem rootWord_read (halves : E × E) :
    (eNew (beWordAt ((rootWord halves).toArray.extract 0 16) 8) (beWordAt ((rootWord halves).toArray.extract 0 16) 0) 0,
      eNew (beWordAt ((rootWord halves).toArray.extract 16 32) 8)
        (beWordAt ((rootWord halves).toArray.extract 16 32) 0) 0) = rootRead halves := by
  have hsplit : rootWord halves = (be64 (halves.1.limb 1).lane ++ be64 (halves.1.limb 0).lane) ++
      (be64 (halves.2.limb 1).lane ++ be64 (halves.2.limb 0).lane) := by
    simp only [rootWord, List.append_assoc]
  have hlo : ((rootWord halves).toArray.extract 0 16).toList =
      be64 (halves.1.limb 1).lane ++ be64 (halves.1.limb 0).lane := by
    rw [Array.toList_extract, List.extract_eq_take_drop, List.drop_zero, List.toList_toArray, hsplit]
    exact List.take_left' (by simp)
  have hhi : ((rootWord halves).toArray.extract 16 32).toList =
      be64 (halves.2.limb 1).lane ++ be64 (halves.2.limb 0).lane := by
    rw [Array.toList_extract, List.extract_eq_take_drop, List.toList_toArray, hsplit,
      List.drop_left' (by simp)]
    exact List.take_of_length_le (by simp)
  have a0 := beWordAt_zero_of (a := (rootWord halves).toArray.extract 0 16) (post := be64 (halves.1.limb 0).lane) hlo
  have a8 := beWordAt_of (a := (rootWord halves).toArray.extract 0 16) (pre := be64 (halves.1.limb 1).lane)
    (post := []) (w := (halves.1.limb 0).lane) (by simpa using hlo)
  have b0 := beWordAt_zero_of (a := (rootWord halves).toArray.extract 16 32) (post := be64 (halves.2.limb 0).lane) hhi
  have b8 := beWordAt_of (a := (rootWord halves).toArray.extract 16 32) (pre := be64 (halves.2.limb 1).lane)
    (post := []) (w := (halves.2.limb 0).lane) (by simpa using hhi)
  simp only [length_be64] at a8 b8
  rw [a0, a8, b0, b8]
  rfl

/-- The big-endian fold of a 4-byte `integerWire`, below `2^32`, is the integer. -/
theorem integerWire_fold {n : ℕ} (hn : n < 2 ^ 32) :
    (integerWire n 4).toArray.foldl (fun acc x ↦ acc * 256 + x.toNat) 0 = n := by
  simp only [integerWire, List.foldl_toArray', List.range_succ, List.range_zero, List.nil_append, List.map_append,
    List.map_cons, List.map_nil, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.toUInt8,
    UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  norm_num
  omega

end Bytes

/-! ## Readers -/

/-- **A reader**: `v` reads the bytes `B` at the cursor, returns `a` and collects `zs`: from any channel whose
data holds `B` at its cursor, the cursor moves past `B` and `zs` is appended to the collected values, nothing else
changed. -/
def Reads {α : Type} (v : ChanM Id α) (B : List UInt8) (a : α) (zs : List E) : Prop :=
  ∀ c : Chan, c.cursor ≤ c.data.size → B <+: c.data.toList.drop c.cursor →
    v.run.run c = (.ok a, { c with cursor := c.cursor + B.length, zeros := c.zeros ++ zs.toArray })

/-- **A channel action's run after a bind**: the first action's, then the continuation's from its channel. -/
theorem chan_run_bind {α β : Type} (v : ChanM Id α) (f : α → ChanM Id β) (c : Chan) :
    (v >>= f).run.run c = match (v.run.run c).1 with
      | .ok a => (f a).run.run (v.run.run c).2
      | .error e => (.error e, (v.run.run c).2) := by
  rw [ExceptT.run_bind, StateT.run_bind]
  generalize v.run.run c = p
  rcases p with ⟨r, c'⟩
  cases r <;> rfl

/-- A channel action's run after a map. -/
theorem chan_run_map {α β : Type} (v : ChanM Id α) (f : α → β) (c : Chan) :
    (f <$> v).run.run c = match (v.run.run c).1 with
      | .ok a => (.ok (f a), (v.run.run c).2)
      | .error e => (.error e, (v.run.run c).2) := by
  rw [ExceptT.run_map, StateT.run_map]
  generalize v.run.run c = p
  rcases p with ⟨r, c'⟩
  cases r <;> rfl

/-- A pure channel action. -/
theorem chan_run_pure {α : Type} (a : α) (c : Chan) : (Pure.pure a : ChanM Id α).run.run c = (.ok a, c) := rfl

theorem chan_run_get (c : Chan) : (get : ChanM Id Chan).run.run c = (.ok c, c) := rfl

theorem chan_run_set (c c' : Chan) : (set c' : ChanM Id PUnit).run.run c = (.ok ⟨⟩, c') := rfl

theorem chan_run_modify (f : Chan → Chan) (c : Chan) : (modify f : ChanM Id PUnit).run.run c = (.ok ⟨⟩, f c) := rfl

theorem chan_run_throw {α : Type} (e : UniError) (c : Chan) :
    (throw e : ChanM Id α).run.run c = (.error e, c) := rfl

theorem chan_run_ite {α : Type} (p : Prop) [Decidable p] (x y : ChanM Id α) (c : Chan) :
    (if p then x else y).run.run c = if p then x.run.run c else y.run.run c := by
  split <;> rfl

namespace Reads

variable {α β : Type}

theorem pure (a : α) : Reads (Pure.pure a : ChanM Id α) [] a [] := by
  intro c _ _
  rw [chan_run_pure]
  simp

theorem bind {v : ChanM Id α} {f : α → ChanM Id β} {B1 B2 : List UInt8} {a : α} {b : β} {zs1 zs2 : List E}
    (h1 : Reads v B1 a zs1) (h2 : Reads (f a) B2 b zs2) : Reads (v >>= f) (B1 ++ B2) b (zs1 ++ zs2) := by
  intro c hcur hc
  have hc1 : B1 <+: c.data.toList.drop c.cursor := (List.prefix_append B1 B2).trans hc
  have hlen := hc.length_le
  simp only [List.length_append, List.length_drop, Array.length_toList] at hlen
  have hc2 : B2 <+: c.data.toList.drop (c.cursor + B1.length) := by
    obtain ⟨t, ht⟩ := hc
    refine ⟨t, ?_⟩
    rw [← List.drop_drop, ← ht, List.append_assoc, List.drop_left]
  have e1 := h1 c hcur hc1
  have e2 := h2 { c with cursor := c.cursor + B1.length, zeros := c.zeros ++ zs1.toArray } (by simp; omega) hc2
  rw [chan_run_bind, e1]
  dsimp only
  rw [e2]
  simp [Nat.add_assoc, Array.append_assoc]

/-- A reader followed by a pure map. -/
theorem bind_pure {v : ChanM Id α} {f : α → β} {B : List UInt8} {a : α} {zs : List E} (h : Reads v B a zs) :
    Reads (v >>= fun x ↦ Pure.pure (f x)) B (f a) zs := by
  simpa using h.bind (f := fun x ↦ Pure.pure (f x)) (Reads.pure (f a))

theorem congr {v : ChanM Id α} {B B' : List UInt8} {a a' : α} {zs zs' : List E} (h : Reads v B a zs)
    (hB : B = B') (ha : a = a') (hz : zs = zs') : Reads v B' a' zs' := by
  subst hB ha hz; exact h

end Reads

/-- `take::<N>` reads its bytes. -/
theorem takeBytes_reads (B : List UInt8) : Reads (takeBytes (m := Id) B.length) B B.toArray [] := by
  intro c hcur hc
  have hle : c.cursor + B.length ≤ c.data.size := by
    have := hc.length_le
    simp only [List.length_drop, Array.length_toList] at this
    omega
  have hex : c.data.extract c.cursor (c.cursor + B.length) = B.toArray := by
    apply Array.toList_inj.mp
    rw [Array.toList_extract, List.extract_eq_take_drop, Nat.add_sub_cancel_left, List.toList_toArray]
    exact (List.prefix_iff_eq_take.mp hc).symm
  simp only [takeBytes, chan_run_bind, chan_run_get, hle, ite_true, chan_run_set, hex, chan_run_pure]
  simp

/-- **`next_scalar` reads `scalarWire x`**. -/
theorem nextScalar_reads (x : E) : Reads (nextScalar (m := Id)) (scalarWire x) x [] := by
  have h := (takeBytes_reads (scalarWire x)).bind_pure
    (f := fun b ↦ eNew (beWordAt b 16) (beWordAt b 8) (beWordAt b 0))
  rw [scalarWire_read, length_scalarWire] at h
  exact h

/-- **`next_root` reads `rootWord halves`**, and returns the halves without their top limbs. -/
theorem nextRoot_reads (halves : E × E) : Reads (nextRoot (m := Id)) (rootWord halves) (rootRead halves) [] := by
  have hl1 : ((rootWord halves).take 16).length = 16 := by simp
  have hl2 : ((rootWord halves).drop 16).length = 16 := by simp
  have r1 := takeBytes_reads ((rootWord halves).take 16)
  have r2 := takeBytes_reads ((rootWord halves).drop 16)
  rw [hl1] at r1
  rw [hl2] at r2
  have hread := rootWord_read halves
  have ex1 : (rootWord halves).toArray.extract 0 16 = ((rootWord halves).take 16).toArray := by
    apply Array.toList_inj.mp
    rw [Array.toList_extract, List.extract_eq_take_drop, List.drop_zero, List.toList_toArray, List.toList_toArray]
  have ex2 : (rootWord halves).toArray.extract 16 32 = ((rootWord halves).drop 16).toArray := by
    apply Array.toList_inj.mp
    rw [Array.toList_extract, List.extract_eq_take_drop, List.toList_toArray, List.toList_toArray]
    exact List.take_of_length_le (by simp)
  rw [ex1, ex2] at hread
  exact Reads.congr (r1.bind (r2.bind_pure (f := fun hi ↦
      (eNew (beWordAt ((rootWord halves).take 16).toArray 8) (beWordAt ((rootWord halves).take 16).toArray 0) 0,
        eNew (beWordAt hi 8) (beWordAt hi 0) 0)))) (List.take_append_drop _ _) hread (by simp)

/-- **`next_integer(4)` reads `integerWire n 4`** for `n < 2^32`. -/
theorem nextInteger_reads {n : ℕ} (hn : n < 2 ^ 32) : Reads (nextInteger (m := Id) 4) (integerWire n 4) n [] := by
  have h := (takeBytes_reads (integerWire n 4)).bind_pure (f := fun b ↦ b.foldl (fun acc x ↦ acc * 256 + x.toNat) 0)
  rw [integerWire_fold hn, length_integerWire] at h
  exact h

/-- `require_zero(x)` reads nothing and collects `x`. -/
theorem requireZero_reads (x : E) : Reads (requireZero (m := Id) x) [] () [x] := by
  intro c _ _
  simp [requireZero]
  rfl

/-- **A loop whose every pass reads**: pass `x` from state `s` reads `bytes s x`, collects `zs s x` and yields
`step s x`. -/
def loopBytes {β γ : Type} (step : β → γ → β) (bytes : β → γ → List UInt8) : List γ → β → List UInt8
  | [], _ => []
  | x :: xs, s => bytes s x ++ loopBytes step bytes xs (step s x)

/-- The values a loop whose every pass reads collects. -/
def loopZeros {β γ : Type} (step : β → γ → β) (zs : β → γ → List E) : List γ → β → List E
  | [], _ => []
  | x :: xs, s => zs s x ++ loopZeros step zs xs (step s x)

theorem Reads.forIn {β γ : Type} (step : β → γ → β) (bytes : β → γ → List UInt8) (zs : β → γ → List E)
    (body : γ → β → ChanM Id (ForInStep β)) :
    ∀ (xs : List γ), (∀ x ∈ xs, ∀ s, Reads (body x s) (bytes s x) (.yield (step s x)) (zs s x)) →
    ∀ s, Reads (ForIn.forIn xs s body) (loopBytes step bytes xs s) (xs.foldl step s) (loopZeros step zs xs s)
  | [], _, s => by
    simpa [loopBytes, loopZeros] using Reads.pure (α := β) s
  | x :: xs, h, s => by
    rw [List.forIn_cons]
    have h1 := h x List.mem_cons_self s
    have h2 := Reads.forIn step bytes zs body xs (fun y hy ↦ h y (List.mem_cons_of_mem x hy)) (step s x)
    exact h1.bind (f := fun r ↦ match r with
      | ForInStep.done b => Pure.pure b
      | ForInStep.yield b => ForIn.forIn xs b body) h2

theorem loopBytes_const {β γ : Type} (step : β → γ → β) (g : γ → List UInt8) :
    ∀ (xs : List γ) (s : β), loopBytes step (fun _ x ↦ g x) xs s = xs.flatMap g
  | [], _ => rfl
  | x :: xs, s => by simp [loopBytes, loopBytes_const step g xs]

theorem loopZeros_nil {β γ : Type} (step : β → γ → β) :
    ∀ (xs : List γ) (s : β), loopZeros step (fun _ _ ↦ []) xs s = []
  | [], _ => rfl
  | x :: xs, s => by simp [loopZeros, loopZeros_nil step xs]

theorem foldl_push_map {α γ : Type} (g : γ → α) :
    ∀ (xs : List γ) (acc : Array α), xs.foldl (fun s x ↦ s.push (g x)) acc = acc ++ (xs.map g).toArray
  | [], acc => by simp
  | x :: xs, acc => by
    rw [List.foldl_cons, foldl_push_map g xs]
    apply Array.toList_inj.mp
    simp

theorem range'_map_getD {α : Type} (xs : List α) (d : α) : (List.range' 0 xs.length).map (fun i ↦ xs.getD i d) = xs := by
  rw [← List.range_eq_range']
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- **`next_scalars(n)` reads `n` scalars**, `scalarWire` each. -/
theorem nextScalars_reads (xs : List E) :
    Reads (nextScalars (m := Id) xs.length) (xs.flatMap scalarWire) xs [] := by
  unfold nextScalars
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one]
  have hloop := Reads.forIn (fun (s : Array E) (i : ℕ) ↦ s.push (xs.getD i 0)) (fun _ i ↦ scalarWire (xs.getD i 0))
    (fun _ _ ↦ []) (fun _ (s : Array E) ↦ do
      let x ← nextScalar (m := Id)
      Pure.pure (ForInStep.yield (s.push x))) (List.range' 0 xs.length)
    (fun i _ s ↦ (nextScalar_reads (xs.getD i 0)).bind_pure (f := fun x ↦ ForInStep.yield (s.push x))) #[]
  have hb : (List.range' 0 xs.length).flatMap (fun i ↦ scalarWire (xs.getD i 0)) = xs.flatMap scalarWire := by
    simpa [List.flatMap_map] using congrArg (List.flatMap scalarWire) (range'_map_getD xs 0)
  rw [loopBytes_const, loopZeros_nil, foldl_push_map, range'_map_getD, hb] at hloop
  exact Reads.congr (hloop.bind_pure (f := Array.toList)) rfl (by simp) rfl

/-! ## Writers -/

/-- The writer after appending `B`. -/
abbrev Wr.append (w : Wr) (B : List UInt8) : Wr := { w with stream := w.stream ++ B.toArray }

/-- **A writer**: the prover action `p` from `w` returns `b` and only appends `B` to the stream. -/
def Writes {β : Type} (p : WrM Id β) (w : Wr) (b : β) (B : List UInt8) : Prop :=
  p.run w = (b, w.append B)

theorem Wr.append_append (w : Wr) (B1 B2 : List UInt8) : (w.append B1).append B2 = w.append (B1 ++ B2) := by
  simp [Wr.append, Array.append_assoc]

theorem Wr.append_nil (w : Wr) : w.append [] = w := by simp [Wr.append]

/-- A prover action's run after a bind. -/
theorem wr_run_bind {β γ : Type} (p : WrM Id β) (g : β → WrM Id γ) (w : Wr) :
    (p >>= g).run w = (g (p.run w).1).run (p.run w).2 := rfl

theorem wr_run_pure {β : Type} (b : β) (w : Wr) : (Pure.pure b : WrM Id β).run w = (b, w) := rfl

namespace Writes

variable {β γ : Type}

theorem pure (b : β) (w : Wr) : Writes (Pure.pure b : WrM Id β) w b [] := by
  show (b, w) = (b, w.append [])
  rw [Wr.append_nil]

theorem bind {p : WrM Id β} {g : β → WrM Id γ} {w : Wr} {b : β} {c : γ} {B1 B2 : List UInt8}
    (h1 : Writes p w b B1) (h2 : Writes (g b) (w.append B1) c B2) : Writes (p >>= g) w c (B1 ++ B2) := by
  unfold Writes at *
  rw [wr_run_bind, h1]
  dsimp only
  rw [h2, Wr.append_append]

theorem congr {p : WrM Id β} {w : Wr} {b b' : β} {B B' : List UInt8} (h : Writes p w b B) (hb : b = b')
    (hB : B = B') : Writes p w b' B' := by
  subst hb hB; exact h

end Writes

/-- **A loop whose every pass writes** (on the prover's side): pass `x` from state `s` at any writer appends
`bytes s x` and yields `step s x`. -/
theorem Writes.forIn {β γ : Type} (step : β → γ → β) (bytes : β → γ → List UInt8)
    (body : γ → β → WrM Id (ForInStep β)) :
    ∀ (xs : List γ), (∀ x ∈ xs, ∀ s w, Writes (body x s) w (.yield (step s x)) (bytes s x)) →
    ∀ s w, Writes (ForIn.forIn xs s body) w (xs.foldl step s) (loopBytes step bytes xs s)
  | [], _, s, w => by
    simpa [loopBytes] using Writes.pure (β := β) s w
  | x :: xs, h, s, w => by
    rw [List.forIn_cons]
    have h1 := h x List.mem_cons_self s w
    have h2 := Writes.forIn step bytes body xs (fun y hy ↦ h y (List.mem_cons_of_mem x hy)) (step s x)
      (w.append (bytes s x))
    exact h1.bind (g := fun r ↦ match r with
      | ForInStep.done b => Pure.pure b
      | ForInStep.yield b => ForIn.forIn xs b body) h2

theorem sendBytes_writes (B : List UInt8) (w : Wr) : Writes (sendBytes (m := Id) B) w () B := rfl

theorem sendScalar_writes (x : E) (w : Wr) : Writes (sendScalar (m := Id) x) w () (scalarWire x) := rfl

theorem sendScalars_writes (xs : List E) (w : Wr) : Writes (sendScalars (m := Id) xs) w () (xs.flatMap scalarWire) :=
  rfl

theorem sendRoot_writes (halves : E × E) (w : Wr) : Writes (sendRoot (m := Id) halves) w () (rootWord halves) := rfl

theorem sendInteger_writes (n bytes : ℕ) (w : Wr) : Writes (sendInteger (m := Id) n bytes) w () (integerWire n bytes) :=
  rfl

/-! ## The prover's challenge -/

section Sample

variable (H : List UInt8 → Digest)

/-- **The prover's challenge** at the writer `w` (`sampleW` at `pure ∘ H`): the challenge, and the writer after it
(everything written absorbed, the new state, the challenge recorded). -/
def Wr.sampled (w : Wr) : E × Wr :=
  let state := H (digestBytes w.state ++ (w.stream.extract w.absorbed w.stream.size).toList)
  let x := PcsQuotient.Transcript.challengeOf state
  (x, { w with absorbed := w.stream.size, state := state, challenges := w.challenges.push x })

theorem sampleW_run (w : Wr) : (sampleW (m := Id) (pure ∘ H)).run w = Wr.sampled H w := rfl

/-- A challenge leaves the stream as it is. -/
@[simp] theorem Wr.sampled_stream (w : Wr) : (Wr.sampled H w).2.stream = w.stream := rfl

end Sample

/-! ## The channel trailing the writer: `Steps` -/

/-- **The verifier's channel** on data `D` at `pos`, with the writer `w`'s sponge (`absorbed`, `state`) and
challenges, `Z` collected. -/
def chanAt (D : Array UInt8) (pos : ℕ) (w : Wr) (Z : Array E) : Chan := ⟨D, pos, w.absorbed, w.state, w.challenges, Z⟩

/-- Writing leaves the sponge as it is. -/
theorem chanAt_append (D : Array UInt8) (pos : ℕ) (w : Wr) (B : List UInt8) (Z : Array E) :
    chanAt D pos (w.append B) Z = chanAt D pos w Z := rfl

/-- The channel from the seed is the one at `0` of the writer from the seed. -/
theorem chan_start_eq (seed : Digest) (D : Array UInt8) : Chan.start seed D = chanAt D 0 (Wr.start seed) #[] := rfl

/-- **The verifier `v` and the prover `p` in step**, the verifier possibly trailing: `p` from `w` returns `b` at
`w'`, only appending to the stream; on any data `D` covering `w'`'s stream, `v` from `pos` with `w`'s sponge
returns `a`, collects `zs` and ends at `pos'` with `w'`'s sponge. -/
def Steps {α β : Type} (v : ChanM Id α) (p : WrM Id β) (pos : ℕ) (w : Wr) (a : α) (b : β) (pos' : ℕ) (w' : Wr)
    (zs : List E) : Prop :=
  p.run w = (b, w') ∧ w.stream.toList <+: w'.stream.toList ∧
  ∀ (D : Array UInt8) (Z : Array E), w'.stream.toList <+: D.toList →
    v.run.run (chanAt D pos w Z) = (.ok a, chanAt D pos' w' (Z ++ zs.toArray))

namespace Steps

variable {α β γ δ : Type}

/-- Both sides one after the other. -/
theorem bind {v : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id β} {g : β → WrM Id δ} {pos pos1 pos2 : ℕ}
    {w w1 w2 : Wr} {a : α} {b : β} {c : γ} {d : δ} {zs1 zs2 : List E}
    (h1 : Steps v p pos w a b pos1 w1 zs1) (h2 : Steps (f a) (g b) pos1 w1 c d pos2 w2 zs2) :
    Steps (v >>= f) (p >>= g) pos w c d pos2 w2 (zs1 ++ zs2) := by
  obtain ⟨p1, m1, e1⟩ := h1
  obtain ⟨p2, m2, e2⟩ := h2
  refine ⟨?_, m1.trans m2, fun D Z hD ↦ ?_⟩
  · rw [wr_run_bind, p1]
    exact p2
  · rw [chan_run_bind, e1 D Z (m2.trans hD)]
    dsimp only
    rw [e2 D _ hD]
    simp [Array.append_assoc]

/-- Nothing on either side. -/
theorem pure (a : α) (b : β) (pos : ℕ) (w : Wr) :
    Steps (Pure.pure a : ChanM Id α) (Pure.pure b : WrM Id β) pos w a b pos w [] := by
  refine ⟨rfl, List.prefix_refl _, fun D Z _ ↦ ?_⟩
  rw [chan_run_pure]
  simp

/-- **A verifier-only first step**: `v` reads bytes the writer has already written (at `pos`, not past its
stream); the prover's program runs on. -/
theorem vbind {v : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id δ} {pos pos2 : ℕ} {w w2 : Wr} {B : List UInt8}
    {a : α} {c : γ} {d : δ} {zs1 zs2 : List E}
    (h1 : Reads v B a zs1) (hpos : pos ≤ w.stream.size) (hB : B <+: w.stream.toList.drop pos)
    (h2 : Steps (f a) p (pos + B.length) w c d pos2 w2 zs2) :
    Steps (v >>= f) p pos w c d pos2 w2 (zs1 ++ zs2) := by
  obtain ⟨p2, m2, e2⟩ := h2
  refine ⟨p2, m2, fun D Z hD ↦ ?_⟩
  have hD' : w.stream.toList <+: D.toList := m2.trans hD
  have hsize : pos ≤ D.size := by
    have := hD'.length_le
    simp only [Array.length_toList] at this
    omega
  have hBD : B <+: D.toList.drop pos := by
    obtain ⟨t, ht⟩ := hD'
    rw [← ht, List.drop_append_of_le_length (by simpa using hpos)]
    exact hB.trans (List.prefix_append _ _)
  rw [chan_run_bind, h1 (chanAt D pos w Z) hsize hBD]
  dsimp only
  have e := e2 D (Z ++ zs1.toArray) hD
  rw [show chanAt D pos w Z = ⟨D, pos, w.absorbed, w.state, w.challenges, Z⟩ from rfl] at *
  simpa [chanAt, Array.append_assoc] using e

/-- **A prover-only first step**: `p` appends `B`; the verifier trails. -/
theorem pbind {v : ChanM Id α} {p : WrM Id β} {g : β → WrM Id δ} {pos pos2 : ℕ} {w w2 : Wr} {B : List UInt8}
    {b : β} {c : α} {d : δ} {zs : List E}
    (h1 : Writes p w b B) (h2 : Steps v (g b) pos (w.append B) c d pos2 w2 zs) :
    Steps v (p >>= g) pos w c d pos2 w2 zs := by
  obtain ⟨p2, m2, e2⟩ := h2
  refine ⟨?_, (List.prefix_append w.stream.toList B).trans (by simpa using m2), fun D Z hD ↦ ?_⟩
  · rw [wr_run_bind, h1]
    exact p2
  · rw [← chanAt_append D pos w B]
    exact e2 D Z hD

/-- The verifier's result mapped. -/
theorem map_v {v : ChanM Id α} {f : α → γ} {p : WrM Id β} {pos pos' : ℕ} {w w' : Wr} {a : α} {b : β}
    {zs : List E} (h : Steps v p pos w a b pos' w' zs) :
    Steps (v >>= fun x ↦ Pure.pure (f x)) p pos w (f a) b pos' w' zs := by
  obtain ⟨p1, m1, e1⟩ := h
  refine ⟨p1, m1, fun D Z hD ↦ ?_⟩
  rw [chan_run_bind, e1 D Z hD]
  rfl

/-- The prover's result mapped. -/
theorem map_p {v : ChanM Id α} {p : WrM Id β} {g : β → δ} {pos pos' : ℕ} {w w' : Wr} {a : α} {b : β}
    {zs : List E} (h : Steps v p pos w a b pos' w' zs) :
    Steps v (p >>= fun x ↦ Pure.pure (g x)) pos w a (g b) pos' w' zs := by
  obtain ⟨p1, m1, e1⟩ := h
  refine ⟨?_, m1, e1⟩
  rw [wr_run_bind, p1]
  rfl

theorem congr {v : ChanM Id α} {p : WrM Id β} {pos pos' : ℕ} {w w' : Wr} {a a' : α} {b b' : β}
    {zs zs' : List E} (h : Steps v p pos w a b pos' w' zs) (ha : a = a') (hb : b = b') (hz : zs = zs') :
    Steps v p pos w a' b' pos' w' zs' := by
  subst ha hb hz; exact h

/-- **The challenge**: both at the end of the stream (the verifier has read all the prover wrote), the same input
bytes, the same challenge, the same writer and channel after it. -/
theorem sample (H : List UInt8 → Digest) (w : Wr) :
    Steps (sampleH (m := Id) (Pure.pure ∘ H)) (sampleW (m := Id) (Pure.pure ∘ H)) w.stream.size w
      (Wr.sampled H w).1 (Wr.sampled H w).1 w.stream.size (Wr.sampled H w).2 [] := by
  refine ⟨sampleW_run H w, List.prefix_refl _, fun D Z hD ↦ ?_⟩
  have hex : D.extract w.absorbed w.stream.size = w.stream.extract w.absorbed w.stream.size := by
    apply Array.toList_inj.mp
    obtain ⟨t, ht⟩ := hD
    simp only [Wr.sampled_stream] at ht
    rw [Array.toList_extract, Array.toList_extract, ← ht, List.extract_eq_take_drop, List.extract_eq_take_drop]
    by_cases hab : w.absorbed ≤ w.stream.toList.length
    · have hl : (List.drop w.absorbed w.stream.toList).length = w.stream.size - w.absorbed := by simp
      rw [List.drop_append_of_le_length hab, List.take_left' hl, List.take_of_length_le (le_of_eq hl)]
    · have h0 : w.stream.size - w.absorbed = 0 := by simp at hab; omega
      rw [h0, List.take_zero, List.take_zero]
  have e : (sampleH (m := Id) (Pure.pure ∘ H)).run.run (chanAt D w.stream.size w Z) =
      (.ok (PcsQuotient.Transcript.challengeOf
          (H (digestBytes w.state ++ (D.extract w.absorbed w.stream.size).toList))),
        ⟨D, w.stream.size, w.stream.size, H (digestBytes w.state ++ (D.extract w.absorbed w.stream.size).toList),
          w.challenges.push (PcsQuotient.Transcript.challengeOf
            (H (digestBytes w.state ++ (D.extract w.absorbed w.stream.size).toList))), Z⟩) := rfl
  rw [e, hex, show ([] : List E).toArray = #[] from rfl, Array.append_empty]
  rfl

/-- **A reader on bytes already written**, the prover idle. -/
theorem reads {v : ChanM Id α} {pos : ℕ} {w : Wr} {B : List UInt8} {a : α} {zs : List E}
    (h : Reads v B a zs) (hpos : pos ≤ w.stream.size) (hB : B <+: w.stream.toList.drop pos) :
    Steps v (Pure.pure () : WrM Id Unit) pos w a () (pos + B.length) w zs := by
  have := vbind (f := fun x ↦ (Pure.pure x : ChanM Id α)) h hpos hB (Steps.pure a () (pos + B.length) w)
  simpa using this

/-- **A reader against the writer of its bytes**, both from the end of the stream. -/
theorem readWrite {v : ChanM Id α} {p : WrM Id β} {w : Wr} {B : List UInt8} {a : α} {b : β} {zs : List E}
    (h1 : Reads v B a zs) (h2 : Writes p w b B) :
    Steps v p w.stream.size w a b (w.append B).stream.size (w.append B) zs := by
  refine ⟨h2, by simp, fun D Z hD ↦ ?_⟩
  have hD' : w.stream.toList ++ B <+: D.toList := by simpa using hD
  have hsize : w.stream.size ≤ D.size := by
    have := hD'.length_le
    simp only [List.length_append, Array.length_toList] at this
    omega
  have hBD : B <+: D.toList.drop w.stream.size := by
    obtain ⟨t, ht⟩ := hD'
    rw [← ht, List.append_assoc, show w.stream.size = w.stream.toList.length by simp, List.drop_left]
    exact List.prefix_append _ _
  rw [h1 (chanAt D w.stream.size w Z) hsize hBD]
  simp [chanAt]

end Steps

/-- The loop body of `samples(n)` (`samplesH`'s). -/
def samplesBody (H : List UInt8 → Digest) (_ : ℕ) (out : Array E) : ChanM Id (ForInStep (Array E)) := do
  let x ← sampleH (m := Id) (Pure.pure ∘ H)
  Pure.pure (ForInStep.yield (out.push x))

/-- `samples(n)` against `n` of the prover's challenges, as a loop from any start and accumulator. -/
theorem samples_loop_steps (H : List UInt8 → Digest) :
    ∀ (n s : ℕ) (acc : Array E) (w : Wr),
      Steps (ForIn.forIn (List.range' s n) acc (samplesBody H))
        (samplesW (m := Id) (Pure.pure ∘ H) n) w.stream.size w
        (acc ++ ((samplesW (m := Id) (Pure.pure ∘ H) n).run w).1.toArray)
        ((samplesW (m := Id) (Pure.pure ∘ H) n).run w).1 w.stream.size
        ((samplesW (m := Id) (Pure.pure ∘ H) n).run w).2 []
  | 0, s, acc, w => by
    have e : ForIn.forIn (List.range' s 0) acc (samplesBody H) = (Pure.pure acc : ChanM Id (Array E)) := rfl
    rw [e]
    have e0 : ((samplesW (m := Id) (Pure.pure ∘ H) 0).run w).1 = [] := rfl
    exact Steps.congr (Steps.pure (α := Array E) acc ([] : List E) w.stream.size w) (by rw [e0]; simp) rfl rfl
  | n + 1, s, acc, w => by
    rw [List.range'_succ, List.forIn_cons]
    have h1 := (Steps.sample H w).map_v (f := fun x ↦ ForInStep.yield (acc.push x))
    have h2 := samples_loop_steps H n (s + 1) (acc.push (Wr.sampled H w).1) (Wr.sampled H w).2
    have h3 := h2.map_p (g := fun rest ↦ (Wr.sampled H w).1 :: rest)
    have h := Steps.bind (f := fun r ↦ match r with
      | ForInStep.done b => Pure.pure b
      | ForInStep.yield b => ForIn.forIn (List.range' (s + 1) n) b (samplesBody H))
      (g := fun x ↦ samplesW (m := Id) (Pure.pure ∘ H) n >>= fun r ↦ Pure.pure (x :: r)) h1 h3
    have e : samplesW (m := Id) (Pure.pure ∘ H) (n + 1) = (sampleW (m := Id) (Pure.pure ∘ H) >>= fun x ↦
        samplesW (m := Id) (Pure.pure ∘ H) n >>= fun r ↦ Pure.pure (x :: r)) := rfl
    rw [e]
    simp only [wr_run_bind, sampleW_run, wr_run_pure]
    refine Steps.congr h ?_ rfl rfl
    apply Array.toList_inj.mp
    simp

/-- **`samples(n)` draws the prover's `n` challenges** (`samplesW`). -/
theorem Steps.samples (H : List UInt8 → Digest) (n : ℕ) (w : Wr) :
    Steps (samplesH (m := Id) (Pure.pure ∘ H) n) (samplesW (m := Id) (Pure.pure ∘ H) n) w.stream.size w
      ((samplesW (m := Id) (Pure.pure ∘ H) n).run w).1 ((samplesW (m := Id) (Pure.pure ∘ H) n).run w).1
      w.stream.size ((samplesW (m := Id) (Pure.pure ∘ H) n).run w).2 [] := by
  have h := (samples_loop_steps H n 0 #[] w).map_v (f := Array.toList)
  have h' := h.map_p (g := id)
  have e1 : samplesH (m := Id) (Pure.pure ∘ H) n = (ForIn.forIn (List.range' 0 n) #[] (samplesBody H) >>=
      fun x ↦ Pure.pure x.toList) := by
    unfold samplesH
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
      Nat.div_one]
    rfl
  have e2 : (samplesW (m := Id) (Pure.pure ∘ H) n >>= fun x ↦ Pure.pure (id x)) =
      samplesW (m := Id) (Pure.pure ∘ H) n := by
    simp
  rw [e1]
  rw [e2] at h'
  exact Steps.congr h' (by simp) rfl rfl

/-- Challenges leave the stream as it is. -/
theorem samplesW_stream (H : List UInt8 → Digest) :
    ∀ (n : ℕ) (w : Wr), ((samplesW (m := Id) (Pure.pure ∘ H) n).run w).2.stream = w.stream
  | 0, _ => rfl
  | n + 1, w => by
    have e : samplesW (m := Id) (Pure.pure ∘ H) (n + 1) = (sampleW (m := Id) (Pure.pure ∘ H) >>= fun x ↦
        samplesW (m := Id) (Pure.pure ∘ H) n >>= fun r ↦ Pure.pure (x :: r)) := rfl
    rw [e, wr_run_bind, sampleW_run, wr_run_bind, wr_run_pure]
    exact samplesW_stream H n _

/-- The verifier's end position, rewritten. -/
theorem Steps.pos_congr {α β : Type} {v : ChanM Id α} {p : WrM Id β} {pos pos' pos'' : ℕ} {w w' : Wr} {a : α}
    {b : β} {zs : List E} (h : Steps v p pos w a b pos' w' zs) (e : pos' = pos'') : Steps v p pos w a b pos'' w' zs := by
  subst e; exact h

/-- **The run from the seed**: steps from the start of the stream, on the data the prover wrote. -/
theorem Steps.run_start {α β : Type} {v : ChanM Id α} {p : WrM Id β} {seed : Digest} {a : α} {b : β} {pos' : ℕ}
    {w' : Wr} {zs : List E} (h : Steps v p 0 (Wr.start seed) a b pos' w' zs) :
    v.run.run (Chan.start seed w'.stream) = (.ok a, chanAt w'.stream pos' w' zs.toArray) := by
  rw [chan_start_eq, h.2.2 w'.stream #[] (List.prefix_refl _)]
  simp

/-- **`finish`** at the end of the data succeeds. -/
theorem finish_chanAt (D : Array UInt8) (w : Wr) (Z : Array E) :
    (finish (m := Id)).run.run (chanAt D D.size w Z) = (.ok (), chanAt D D.size w Z) := by
  simp only [finish, chan_run_bind, chan_run_get]
  simp [chanAt]
  rfl

/-! ## Synchronised channels: `Synced` and `Syncs` -/

/-- **The channel is synchronised with the writer**: the same cursor (the stream's size), the same sponge
(`absorbed`, `state`), the same challenges, and the channel's data starts with the writer's stream. -/
structure Synced (w : Wr) (c : Chan) : Prop where
  cursor : c.cursor = w.stream.size
  absorbed : c.absorbed = w.absorbed
  state : c.state = w.state
  challenges : c.challenges = w.challenges
  data : w.stream.toList <+: c.data.toList

/-- A synchronised channel is the one at the end of the writer's stream, on its data, with its collected values. -/
theorem Synced.eq_chanAt {w : Wr} {c : Chan} (h : Synced w c) : c = chanAt c.data w.stream.size w c.zeros := by
  obtain ⟨d, cu, ab, st, ch, z⟩ := c
  obtain ⟨h1, h2, h3, h4, _⟩ := h
  simp only at h1 h2 h3 h4
  subst h1 h2 h3 h4
  rfl

theorem synced_chanAt {w : Wr} {D : Array UInt8} (Z : Array E) (h : w.stream.toList <+: D.toList) :
    Synced w (chanAt D w.stream.size w Z) := ⟨rfl, rfl, rfl, rfl, h⟩

/-- **The verifier action `v` and the prover action `p` synchronise from the writer `w`**: `p` only appends to the
stream, and from any channel synchronised with `w` whose data covers what `p` writes, `v` returns `a`, collects
`zs`, and ends synchronised with `p`'s writer, its data the same. -/
def Syncs {α β : Type} (v : ChanM Id α) (p : WrM Id β) (w : Wr) (a : α) (zs : List E) : Prop :=
  w.stream.toList <+: (p.run w).2.stream.toList ∧
  ∀ c : Chan, Synced w c → (p.run w).2.stream.toList <+: c.data.toList →
    ∃ c' : Chan, v.run.run c = (.ok a, c') ∧ Synced (p.run w).2 c' ∧ c'.data = c.data ∧
      c'.zeros = c.zeros ++ zs.toArray

section Syncs

variable {α β γ δ : Type}

theorem Syncs.steps {v : ChanM Id α} {p : WrM Id β} {w : Wr} {a : α} {zs : List E} (h : Syncs v p w a zs) :
    Steps v p w.stream.size w a (p.run w).1 (p.run w).2.stream.size (p.run w).2 zs := by
  refine ⟨rfl, h.1, fun D Z hD ↦ ?_⟩
  obtain ⟨c', e, hs, hd, hz⟩ := h.2 (chanAt D w.stream.size w Z) (synced_chanAt Z (h.1.trans hD)) hD
  rw [e, hs.eq_chanAt, hd, hz]
  rfl

theorem Steps.syncs {v : ChanM Id α} {p : WrM Id β} {w w' : Wr} {a : α} {b : β} {zs : List E}
    (h : Steps v p w.stream.size w a b w'.stream.size w' zs) : Syncs v p w a zs := by
  obtain ⟨p1, m1, e1⟩ := h
  unfold Syncs
  rw [p1]
  refine ⟨m1, fun c hc hD ↦ ⟨chanAt c.data w'.stream.size w' (c.zeros ++ zs.toArray), ?_, synced_chanAt _ hD,
    rfl, rfl⟩⟩
  have e := e1 c.data c.zeros hD
  rwa [← hc.eq_chanAt] at e

/-- **The bind lemma**: synchronising actions compose. -/
theorem Syncs.bind {v : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id β} {g : β → WrM Id δ} {w : Wr} {a : α}
    {c : γ} {zs1 zs2 : List E} (h1 : Syncs v p w a zs1) (h2 : Syncs (f a) (g (p.run w).1) (p.run w).2 c zs2) :
    Syncs (v >>= f) (p >>= g) w c (zs1 ++ zs2) :=
  (Steps.bind h1.steps h2.steps).syncs

/-- **`next_scalar` reads the scalar sent.** -/
theorem syncs_scalar (x : E) (w : Wr) : Syncs (nextScalar (m := Id)) (sendScalar (m := Id) x) w x [] :=
  (Steps.readWrite (nextScalar_reads x) (sendScalar_writes x w)).syncs

/-- **`next_scalars(n)` reads the `n` scalars sent.** -/
theorem syncs_scalars (xs : List E) (w : Wr) :
    Syncs (nextScalars (m := Id) xs.length) (sendScalars (m := Id) xs) w xs [] :=
  (Steps.readWrite (nextScalars_reads xs) (sendScalars_writes xs w)).syncs

/-- **`next_root` reads the root sent**, its halves without top limbs (`rootRead`; the halves themselves when
they have none, `rootRead_of`). -/
theorem syncs_root (halves : E × E) (w : Wr) :
    Syncs (nextRoot (m := Id)) (sendRoot (m := Id) halves) w (rootRead halves) [] :=
  (Steps.readWrite (nextRoot_reads halves) (sendRoot_writes halves w)).syncs

/-- **`next_integer(4)` reads the count sent**, below `2^32`. -/
theorem syncs_integer {n : ℕ} (hn : n < 2 ^ 32) (w : Wr) :
    Syncs (nextInteger (m := Id) 4) (sendInteger (m := Id) n 4) w n [] :=
  (Steps.readWrite (nextInteger_reads hn) (sendInteger_writes n 4 w)).syncs

/-- **The same challenge** (`sampleH`, `sampleW` at `pure ∘ H`). -/
theorem syncs_sample (H : List UInt8 → Digest) (w : Wr) :
    Syncs (sampleH (m := Id) (Pure.pure ∘ H)) (sampleW (m := Id) (Pure.pure ∘ H)) w (Wr.sampled H w).1 [] :=
  (Steps.sample H w).syncs

/-- **The same challenges** (`samplesH`, `samplesW`). -/
theorem syncs_samples (H : List UInt8 → Digest) (n : ℕ) (w : Wr) :
    Syncs (samplesH (m := Id) (Pure.pure ∘ H) n) (samplesW (m := Id) (Pure.pure ∘ H) n) w
      ((samplesW (m := Id) (Pure.pure ∘ H) n).run w).1 [] :=
  ((Steps.samples H n w).pos_congr (by rw [samplesW_stream])).syncs

/-- **`require_zero` only collects.** -/
theorem syncs_requireZero (x : E) (w : Wr) :
    Syncs (requireZero (m := Id) x) (Pure.pure () : WrM Id Unit) w () [x] :=
  (Steps.reads (requireZero_reads x) le_rfl (List.nil_prefix)).syncs

/-- **`finish` succeeds** when the data is exactly the writer's stream. -/
theorem finish_synced {w : Wr} {c : Chan} (h : Synced w c) (hd : c.data = w.stream) :
    (finish (m := Id)).run.run c = (.ok (), c) := by
  rw [h.eq_chanAt]
  have hs : w.stream.size = c.data.size := by rw [hd]
  rw [hs]
  exact finish_chanAt _ _ _

end Syncs

/-! ## The two steps stated as hypotheses: Flock and the batching sumcheck

The main synchronisation (`SyncVerifier.lean`) takes these two steps as hypotheses, proved elsewhere: Flock's
prover against `Flock.verifyDeferredH`, and the batching sumcheck's prover against `batchH`. -/

/-- **Flock's prover synchronises with `Flock.verifyDeferredH`** at `log_n` variables, the variant, on `q_flock`'s
words `q`: from any writer, the verifier reads Flock's messages, draws its challenges, collects nothing, and returns
`q_flock`'s point, the end (`some`: the main line sends the slices) and the pending matrices as the prover's output
carries them. -/
def FlockSyncs (H : List UInt8 → Digest) (flock : FlockProver Id) (logN : ℕ) (variant : Flock.Variant)
    (q : Array K) : Prop :=
  ∀ w : Wr, Syncs (Flock.verifyDeferredH (m := Id) (Pure.pure ∘ H) logN variant) (flock logN variant q) w
    (((flock logN variant q).run w).1.point, some ((flock logN variant q).run w).1.end_,
      ((flock logN variant q).run w).1.pending) []

section BatchProver

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- **The batching sumcheck's prover** (`proveStreamWith`'s step 9, as a function): `λ`, the rounds
(`batchRounds`) on the combined claims' dense weights (`denseWeight`, with the ring map) and the stacks (`stackOf`),
Flock's pending tables, then each stack's value at its part of the point, then (Flock's matrices pending) `a`, `b`
at the matrices' point; the point claims in the combined claims' order and the matrices' claim. -/
def batchProver (combined : List (Commitment × Combined)) (stackLayouts : List (Commitment × StackLayout))
    (stackOf : Commitment → Array K) (ringMap : Option (List E)) (tables : Option PendingTables)
    (pending : Option (Flock.Pending × List E)) :
    WrM m (List (Commitment × List E × E) × Option Flock.MatrixClaim) := do
  let lambda ← sampleW H
  let vars := (stackLayouts.map (·.2.vars)).foldl max 0
  let st : BatchState := ⟨combined.map (fun (c, claim) ↦ denseWeight claim (layoutIn stackLayouts c) ringMap),
    combined.map (fun (c, _) ↦ (stackOf c).map ofK), tables, 0, []⟩
  let r ← batchRounds H lambda vars st
  let claims : List (Commitment × List E × E) := combined.map fun (c, _) ↦
    let pt := r.take (layoutIn stackLayouts c).vars
    (c, pt, multilinearEval ((stackOf c).toList.map ofK) pt)
  sendScalars (claims.map (·.2.2))
  let matrices ← match pending with
    | some (p, _) => do
      let mc := p.matrixClaim r 0 0
      let ma := multilinearEval ((flockMatrixStack true).toList.map ofK) mc.point
      let mb := multilinearEval ((flockMatrixStack false).toList.map ofK) mc.point
      sendScalars [ma, mb]
      pure (some (p.matrixClaim r ma mb))
    | none => pure none
  return (claims, matrices)

end BatchProver

/-- A prover's point claim as the verifier's opening: `.point pt v none` (no bit-slice claim on the main line). -/
def pointOpening (claim : Commitment × List E × E) : Commitment × Opening := (claim.1, .point claim.2.1 claim.2.2 none)

/-- **The batching sumcheck's prover synchronises with `batchH`** (no bit-slice claim): from any writer, the
verifier reads the rounds, the stacks' values and `a`, `b`, draws `λ` and the rounds' challenges, returns the
prover's point claims (`pointOpening`, in order) and its matrices' claim, and collects one value, the batch's
terminal `terminal w` (a function of the writer at `λ`, which fixes every challenge of the batch; zero for an
honest trace, the algebra's part). It holds for pending matrices with the slices (`Pending.hasSlices`, the main
line's: `flock_hasSlices`, `SyncVerifier.lean`) or none (`Blake2s.omitted`); without the slices `batchH` returns
the bit-slice combination on `C1`'s opening instead. -/
def BatchSyncs (H : List UInt8 → Digest) (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E))
    (tables : Option PendingTables) (pending : Option (Flock.Pending × List E)) (terminal : Wr → E) : Prop :=
  ∀ w : Wr, Syncs (batchH (m := Id) (Pure.pure ∘ H) combined stackLayouts none ringMap pending)
    (batchProver (m := Id) (Pure.pure ∘ H) combined stackLayouts stackOf ringMap tables pending) w
    ((((batchProver (m := Id) (Pure.pure ∘ H) combined stackLayouts stackOf ringMap tables pending).run w).1.1.map
        pointOpening),
      ((batchProver (m := Id) (Pure.pure ∘ H) combined stackLayouts stackOf ringMap tables pending).run w).1.2)
    [terminal w]

end UniComplete

/-- info: 'UniComplete.Syncs.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.Syncs.bind

/-- info: 'UniComplete.syncs_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.syncs_scalar

/-- info: 'UniComplete.syncs_scalars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.syncs_scalars

/-- info: 'UniComplete.syncs_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.syncs_root

/-- info: 'UniComplete.syncs_integer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.syncs_integer

/-- info: 'UniComplete.syncs_samples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.syncs_samples

/-- info: 'UniComplete.syncs_requireZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.syncs_requireZero

/-- info: 'UniComplete.finish_synced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniComplete.finish_synced
