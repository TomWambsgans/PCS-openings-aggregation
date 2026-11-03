-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniComplete.SyncTable
import UniComplete.DomainCount

namespace UniComplete

open UniStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-! ## More steps -/

namespace Steps

variable {α β γ δ : Type}

/-- **A verifier-only read at a known place of the writer's stream**: the stream is `P ++ B ++ Q`, the verifier at
`P`'s end reads `B`. -/
theorem vread {v : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id δ} {pos2 : ℕ} {w w2 : Wr}
    {P B Q : List UInt8} {a : α} {c : γ} {d : δ} {zs1 zs2 : List E}
    (h1 : Reads v B a zs1) (hw : w.stream.toList = P ++ (B ++ Q))
    (h2 : Steps (f a) p (P.length + B.length) w c d pos2 w2 zs2) :
    Steps (v >>= f) p P.length w c d pos2 w2 (zs1 ++ zs2) := by
  refine vbind h1 ?_ ?_ h2
  · have := congrArg List.length hw
    simp only [List.length_append, Array.length_toList] at this
    omega
  · rw [hw, List.drop_left]
    exact List.prefix_append _ _

/-- **A verifier-only read of the last bytes written**: the writer is `w.append B`, the verifier at `w`'s end. -/
theorem vreadEnd {v : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id δ} {pos2 : ℕ} {w w2 : Wr} {B : List UInt8}
    {a : α} {c : γ} {d : δ} {zs1 zs2 : List E} (h1 : Reads v B a zs1)
    (h2 : Steps (f a) p (w.stream.size + B.length) (w.append B) c d pos2 w2 zs2) :
    Steps (v >>= f) p w.stream.size (w.append B) c d pos2 w2 (zs1 ++ zs2) :=
  vread (P := w.stream.toList) (Q := []) h1 (by simp) h2

/-- **A verifier-only read, the bytes left after `pos` known**: they start with `B`, the read's; the continuation
knows the rest. -/
theorem vreadD {v : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id δ} {pos pos2 : ℕ} {w w2 : Wr} {B R : List UInt8}
    {a : α} {c : γ} {d : δ} {zs1 zs2 : List E} (h1 : Reads v B a zs1) (hpos : pos ≤ w.stream.size)
    (hd : w.stream.toList.drop pos = B ++ R)
    (h2 : w.stream.toList.drop (pos + B.length) = R → Steps (f a) p (pos + B.length) w c d pos2 w2 zs2) :
    Steps (v >>= f) p pos w c d pos2 w2 (zs1 ++ zs2) := by
  refine vbind h1 hpos (by rw [hd]; exact List.prefix_append _ _) (h2 ?_)
  rw [← List.drop_drop, hd, List.drop_left]

/-- **The next scalar**, the scalars left after `pos` known. -/
theorem vscalarD {f : E → ChanM Id γ} {p : WrM Id δ} {pos pos2 : ℕ} {w w2 : Wr} {x : E} {xs : List E} {c : γ}
    {d : δ} {zs : List E} (hd : w.stream.toList.drop pos = (x :: xs).flatMap scalarWire)
    (h2 : w.stream.toList.drop (pos + 24) = xs.flatMap scalarWire → Steps (f x) p (pos + 24) w c d pos2 w2 zs) :
    Steps (nextScalar (m := Id) >>= f) p pos w c d pos2 w2 zs := by
  have hpos : pos ≤ w.stream.size := by
    by_contra hlt
    have h0 : w.stream.toList.drop pos = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [h0, List.flatMap_cons] at hd
    have := congrArg List.length hd
    simp at this
    omega
  have h := vreadD (nextScalar_reads x) hpos (by rw [hd, List.flatMap_cons]) (by simpa using h2)
  simpa using h

/-- The verifier's start position, rewritten. -/
theorem pos_start {v : ChanM Id α} {p : WrM Id β} {pos pos0 pos' : ℕ} {w w' : Wr} {a : α} {b : β} {zs : List E}
    (e : pos = pos0) (h : Steps v p pos0 w a b pos' w' zs) : Steps v p pos w a b pos' w' zs := by
  subst e; exact h

/-- **A commitment on the prover's side** (`StateT.lift` in `Id`): no byte written. -/
theorem plift {v : ChanM Id α} {x : Id β} {g : β → WrM Id δ} {pos pos2 : ℕ} {w w2 : Wr} {c : α} {d : δ}
    {zs : List E} (h : Steps v (g x) pos w c d pos2 w2 zs) :
    Steps v ((StateT.lift x : WrM Id β) >>= g) pos w c d pos2 w2 zs := h

/-- The prover's result mapped (`f <$> p`). -/
theorem pmap {v : ChanM Id α} {p : WrM Id β} {g : β → δ} {pos pos' : ℕ} {w w' : Wr} {a : α} {b : β}
    {zs : List E} (h : Steps v p pos w a b pos' w' zs) : Steps v (g <$> p) pos w a (g b) pos' w' zs := by
  obtain ⟨p1, m1, e1⟩ := h
  refine ⟨?_, m1, e1⟩
  show (g (p.run w).1, (p.run w).2) = _
  rw [p1]

/-- `get` on the prover's side. -/
theorem pget {v : ChanM Id α} {g : Wr → WrM Id δ} {pos pos2 : ℕ} {w w2 : Wr} {c : α} {d : δ} {zs : List E}
    (h : Steps v (g w) pos w c d pos2 w2 zs) : Steps v ((get : WrM Id Wr) >>= g) pos w c d pos2 w2 zs := h

/-- Both sides one after the other, the first from the end of the stream (`pos` rewritten to it). -/
theorem bind_pos {v : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id β} {g : β → WrM Id δ} {pos pos1 pos2 : ℕ}
    {w w1 w2 : Wr} {a : α} {b : β} {c : γ} {d : δ} {zs1 zs2 : List E} (e : pos = w.stream.size)
    (h1 : Steps v p w.stream.size w a b pos1 w1 zs1) (h2 : Steps (f a) (g b) pos1 w1 c d pos2 w2 zs2) :
    Steps (v >>= f) (p >>= g) pos w c d pos2 w2 (zs1 ++ zs2) := by
  subst e; exact h1.bind h2

/-- A pure first action on the verifier's side. -/
theorem vpure {f : α → ChanM Id γ} {p : WrM Id δ} {x : α} {pos pos2 : ℕ} {w w2 : Wr} {c : γ} {d : δ}
    {zs : List E} (h : Steps (f x) p pos w c d pos2 w2 zs) : Steps ((Pure.pure x : ChanM Id α) >>= f) p pos w c d pos2 w2 zs :=
  h

/-- The verifier's two pure ends, as one. -/
theorem vite {b : Bool} {R1 R2 : α} {p : WrM Id δ} {pos pos' : ℕ} {w w' : Wr} {d : δ} {zs : List E}
    (h : Steps (Pure.pure (if b = true then R1 else R2) : ChanM Id α) p pos w (if b = true then R1 else R2) d pos' w'
      zs) :
    Steps (if b = true then (Pure.pure R1 : ChanM Id α) else Pure.pure R2) p pos w (if b = true then R1 else R2) d
      pos' w' zs := by
  cases b
  · exact h
  · exact h

/-- The prover's program, rewritten. -/
theorem prog_eq {v : ChanM Id α} {p p' : WrM Id β} {pos pos' : ℕ} {w w' : Wr} {a : α} {b : β} {zs : List E}
    (e : p = p') (h : Steps v p' pos w a b pos' w' zs) : Steps v p pos w a b pos' w' zs := by
  subst e; exact h

/-- The verifier's first action, rewritten. -/
theorem bind_veq {v v' : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id β} {g : β → WrM Id δ} {pos pos1 pos2 : ℕ}
    {w w1 w2 : Wr} {a : α} {b : β} {c : γ} {d : δ} {zs1 zs2 : List E} (e : v = v')
    (h1 : Steps v' p pos w a b pos1 w1 zs1) (h2 : Steps (f a) (g b) pos1 w1 c d pos2 w2 zs2) :
    Steps (v >>= f) (p >>= g) pos w c d pos2 w2 (zs1 ++ zs2) := by
  subst e; exact h1.bind h2

end Steps

/-! ## Steps with their ends unnamed -/

/-- **`Steps` with its ends unnamed**: some result, prover result, end position, writer and collected values,
satisfying `K`. -/
def StepsE {α β : Type} (v : ChanM Id α) (p : WrM Id β) (pos : ℕ) (w : Wr)
    (K : α → β → ℕ → Wr → List E → Prop) : Prop :=
  ∃ a b pos' w' zs, Steps v p pos w a b pos' w' zs ∧ K a b pos' w' zs

namespace StepsE

variable {α β γ δ : Type}

theorem pure {a : α} {b : β} {pos : ℕ} {w : Wr} {K : α → β → ℕ → Wr → List E → Prop} (h : K a b pos w []) :
    StepsE (Pure.pure a : ChanM Id α) (Pure.pure b : WrM Id β) pos w K :=
  ⟨a, b, pos, w, [], Steps.pure a b pos w, h⟩

theorem bind_pos {v : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id β} {g : β → WrM Id δ} {pos pos1 : ℕ}
    {w w1 : Wr} {a : α} {b : β} {zs1 : List E} {K : γ → δ → ℕ → Wr → List E → Prop} (e : pos = w.stream.size)
    (h1 : Steps v p w.stream.size w a b pos1 w1 zs1)
    (h2 : StepsE (f a) (g b) pos1 w1 (fun c d p2 w2 z2 ↦ K c d p2 w2 (zs1 ++ z2))) :
    StepsE (v >>= f) (p >>= g) pos w K := by
  obtain ⟨c, d, p2, w2, z2, hs, hq⟩ := h2
  exact ⟨c, d, p2, w2, zs1 ++ z2, Steps.bind_pos e h1 hs, hq⟩

theorem bind_veq {v v' : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id β} {g : β → WrM Id δ} {pos pos1 : ℕ}
    {w w1 : Wr} {a : α} {b : β} {zs1 : List E} {K : γ → δ → ℕ → Wr → List E → Prop} (e : v = v')
    (h1 : Steps v' p pos w a b pos1 w1 zs1)
    (h2 : StepsE (f a) (g b) pos1 w1 (fun c d p2 w2 z2 ↦ K c d p2 w2 (zs1 ++ z2))) :
    StepsE (v >>= f) (p >>= g) pos w K := by
  obtain ⟨c, d, p2, w2, z2, hs, hq⟩ := h2
  exact ⟨c, d, p2, w2, zs1 ++ z2, Steps.bind_veq e h1 hs, hq⟩

theorem vread {v : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id δ} {w : Wr} {P B Q : List UInt8} {a : α}
    {zs1 : List E} {K : γ → δ → ℕ → Wr → List E → Prop} (h1 : Reads v B a zs1) (hw : w.stream.toList = P ++ (B ++ Q))
    (h2 : StepsE (f a) p (P.length + B.length) w (fun c d p2 w2 z2 ↦ K c d p2 w2 (zs1 ++ z2))) :
    StepsE (v >>= f) p P.length w K := by
  obtain ⟨c, d, p2, w2, z2, hs, hq⟩ := h2
  exact ⟨c, d, p2, w2, zs1 ++ z2, Steps.vread h1 hw hs, hq⟩

theorem vreadEnd {v : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id δ} {w : Wr} {B : List UInt8} {a : α}
    {zs1 : List E} {K : γ → δ → ℕ → Wr → List E → Prop} (h1 : Reads v B a zs1)
    (h2 : StepsE (f a) p (w.stream.size + B.length) (w.append B) (fun c d p2 w2 z2 ↦ K c d p2 w2 (zs1 ++ z2))) :
    StepsE (v >>= f) p w.stream.size (w.append B) K := by
  obtain ⟨c, d, p2, w2, z2, hs, hq⟩ := h2
  exact ⟨c, d, p2, w2, zs1 ++ z2, Steps.vreadEnd h1 hs, hq⟩

theorem vreadD {v : ChanM Id α} {f : α → ChanM Id γ} {p : WrM Id δ} {pos : ℕ} {w : Wr} {B R : List UInt8} {a : α}
    {zs1 : List E} {K : γ → δ → ℕ → Wr → List E → Prop} (h1 : Reads v B a zs1) (hpos : pos ≤ w.stream.size)
    (hd : w.stream.toList.drop pos = B ++ R)
    (h2 : w.stream.toList.drop (pos + B.length) = R →
      StepsE (f a) p (pos + B.length) w (fun c d p2 w2 z2 ↦ K c d p2 w2 (zs1 ++ z2))) :
    StepsE (v >>= f) p pos w K := by
  have hd' : w.stream.toList.drop (pos + B.length) = R := by rw [← List.drop_drop, hd, List.drop_left]
  obtain ⟨c, d, p2, w2, z2, hs, hq⟩ := h2 hd'
  exact ⟨c, d, p2, w2, zs1 ++ z2, Steps.vreadD h1 hpos hd (fun _ ↦ hs), hq⟩

theorem vscalarD {f : E → ChanM Id γ} {p : WrM Id δ} {pos : ℕ} {w : Wr} {x : E} {xs : List E}
    {K : γ → δ → ℕ → Wr → List E → Prop} (hd : w.stream.toList.drop pos = (x :: xs).flatMap scalarWire)
    (h2 : w.stream.toList.drop (pos + 24) = xs.flatMap scalarWire → StepsE (f x) p (pos + 24) w K) :
    StepsE (nextScalar (m := Id) >>= f) p pos w K := by
  have hd' : w.stream.toList.drop (pos + 24) = xs.flatMap scalarWire := by
    rw [← List.drop_drop, hd, List.flatMap_cons, show 24 = (scalarWire x).length by simp, List.drop_left]
  obtain ⟨c, d, p2, w2, z2, hs, hq⟩ := h2 hd'
  exact ⟨c, d, p2, w2, z2, Steps.vscalarD hd (fun _ ↦ hs), hq⟩

theorem pos_start {v : ChanM Id α} {p : WrM Id β} {pos pos0 : ℕ} {w : Wr} {K : α → β → ℕ → Wr → List E → Prop}
    (e : pos = pos0) (h : StepsE v p pos0 w K) : StepsE v p pos w K := by
  subst e; exact h

theorem pbind {v : ChanM Id α} {p : WrM Id β} {g : β → WrM Id δ} {pos : ℕ} {w : Wr} {B : List UInt8} {b : β}
    {K : α → δ → ℕ → Wr → List E → Prop} (h1 : Writes p w b B) (h2 : StepsE v (g b) pos (w.append B) K) :
    StepsE v (p >>= g) pos w K := by
  obtain ⟨c, d, p2, w2, z2, hs, hq⟩ := h2
  exact ⟨c, d, p2, w2, z2, Steps.pbind h1 hs, hq⟩

theorem plift {v : ChanM Id α} {x : Id β} {g : β → WrM Id δ} {pos : ℕ} {w : Wr}
    {K : α → δ → ℕ → Wr → List E → Prop} (h : StepsE v (g x) pos w K) :
    StepsE v ((StateT.lift x : WrM Id β) >>= g) pos w K := h

theorem pget {v : ChanM Id α} {g : Wr → WrM Id δ} {pos : ℕ} {w : Wr} {K : α → δ → ℕ → Wr → List E → Prop}
    (h : StepsE v (g w) pos w K) : StepsE v ((get : WrM Id Wr) >>= g) pos w K := h

theorem vpure {f : α → ChanM Id γ} {p : WrM Id δ} {x : α} {pos : ℕ} {w : Wr} {K : γ → δ → ℕ → Wr → List E → Prop}
    (h : StepsE (f x) p pos w K) : StepsE ((Pure.pure x : ChanM Id α) >>= f) p pos w K := h

theorem prog_eq {v : ChanM Id α} {p p' : WrM Id β} {pos : ℕ} {w : Wr} {K : α → β → ℕ → Wr → List E → Prop}
    (e : p = p') (h : StepsE v p' pos w K) : StepsE v p pos w K := by
  subst e; exact h

theorem vite {b : Bool} {R1 R2 : α} {p : WrM Id δ} {pos : ℕ} {w : Wr} {K : α → δ → ℕ → Wr → List E → Prop}
    (h : StepsE (Pure.pure (if b = true then R1 else R2) : ChanM Id α) p pos w K) :
    StepsE (if b = true then (Pure.pure R1 : ChanM Id α) else Pure.pure R2) p pos w K := by
  cases b
  · exact h
  · exact h

end StepsE

/-- The rows loop writes the counts (`proveStreamWith`, step 0). -/
theorem rows_writes (rows : List ℕ) (body : ℕ → PUnit → WrM Id (ForInStep PUnit))
    (hbody : ∀ n s, body n s = (sendInteger (m := Id) n 4 >>= fun _ ↦ Pure.pure (ForInStep.yield PUnit.unit)))
    (w : Wr) : Writes (ForIn.forIn rows PUnit.unit body) w PUnit.unit (rows.flatMap fun n ↦ integerWire n 4) := by
  have h := Writes.forIn (fun _ _ ↦ PUnit.unit) (fun _ n ↦ integerWire n 4) body rows (fun n _ s w ↦ by
    rw [hbody]
    exact ((sendInteger_writes n 4 w).bind (g := fun _ ↦ Pure.pure (ForInStep.yield PUnit.unit))
      (Writes.pure _ _)).congr rfl (List.append_nil _)) PUnit.unit w
  rw [loopBytes_const] at h
  exact h

/-! ## Flock's end is a ring switch's -/

theorem err_ne_ok {α : Type} {e : UniError} {a : α} {c c' : Chan} :
    ((.error e, c) : Except UniError α × Chan) ≠ (.ok a, c') := by
  intro h; cases h

/-- `ringEndH` ends with a ring switch's map and target. -/
theorem ringEndH_ring (H : List UInt8 → Digest) (variant : Flock.Variant) (s : List E) (c : Chan) (e : Flock.End)
    (c' : Chan) (h : (Flock.ringEndH (m := Id) (Pure.pure ∘ H) variant s).run.run c = (.ok e, c')) :
    ∃ map target, e = .ring map target := by
  unfold Flock.ringEndH at h
  rw [chan_run_bind] at h
  generalize (samplesH (m := Id) (Pure.pure ∘ H) UniStatement.Flock.ringMapShifts.length).run.run c = r at h
  rcases r with ⟨r, c1⟩
  cases r with
  | error err => exact absurd h err_ne_ok
  | ok map =>
    cases h
    exact ⟨_, _, rfl⟩

/-- **`Flock.verifyDeferredH`'s end, when there is one, is a ring switch's.** -/
theorem verifyDeferredH_end (H : List UInt8 → Digest) (logN : ℕ) (variant : Flock.Variant) (c : Chan)
    {pt : List E} {e : Flock.End} {pd : Flock.Pending} {c' : Chan}
    (h : (Flock.verifyDeferredH (m := Id) (Pure.pure ∘ H) logN variant).run.run c = (.ok (pt, some e, pd), c')) :
    ∃ map target, e = .ring map target := by
  unfold Flock.verifyDeferredH at h
  rw [chan_run_bind] at h
  generalize (Flock.frontH (m := Id) (Pure.pure ∘ H) logN variant).run.run c = r at h
  rcases r with ⟨r, c1⟩
  cases r with
  | error err => exact absurd h err_ne_ok
  | ok fr =>
    dsimp only at h
    cases hs : fr.slices with
    | none =>
      rw [hs] at h
      cases h
    | some s =>
      rw [hs] at h
      dsimp only at h
      rw [chan_run_bind, chan_run_map] at h
      generalize hr : (Flock.ringEndH (m := Id) (Pure.pure ∘ H) variant s).run.run c1 = r2 at h
      rcases r2 with ⟨r2, c2⟩
      cases r2 with
      | error err => exact absurd h err_ne_ok
      | ok e' =>
        cases h
        exact ringEndH_ring H variant s c1 _ _ hr

/-! ## The values at `t`, as `atTOf` sends them -/

section AtT

variable (tr : Trace) (c2 : C2Data) (alphas : List E) (beta t : E)

/-- The digits at `t` (`reduceWith`'s `w`). -/
def wOf : List E := digits t (max tr.shape.heap.h (tr.shape.constraintVars + 4) + 2)

/-- The memory's column `k` at `t`. -/
def memAtT (k : ℕ) : E :=
  evalB ((bCoefficients tr.shape.logMemory (tr.memory.getD k #[])).map ofK) tr.shape.logMemory (wOf tr t)

/-- The addresses at `t`. -/
def addressAtT : E :=
  evalB ((bCoefficients tr.shape.logMemory (addressColumn tr.shape.logMemory)).map ofK) tr.shape.logMemory (wOf tr t)

/-- The memory's pull fingerprint at `t`. -/
def memoryPullAtT : E :=
  memoryFp (eqKernel alphas) beta (addressAtT tr t) (memAtT tr t 3) ((List.range 3).map (memAtT tr t))

/-- The bytecode's final counts at `t`. -/
def bytecodeFinalAtT : E :=
  evalB ((bCoefficients tr.shape.logBytecode tr.bytecodeFinal).map ofK) tr.shape.logBytecode (wOf tr t)

/-- The bytecode's pull fingerprint at `t`. -/
def bytecodePullAtT : E :=
  bytecodeFp (eqKernel alphas) beta fun s ↦ if s = 2 then bytecodeFinalAtT tr t else
    evalB ((bCoefficients tr.shape.logBytecode (tr.slots.getD s #[])).map ofK) tr.shape.logBytecode (wOf tr t)

/-- `T(t)`. -/
def heapAtT : E := evalB c2.heapB tr.shape.heap.h (wOf tr t)

/-- `Q_W(t)`. -/
def constraintAtT : E :=
  ((c2.constraintChunks.zip c2.constraintSizes).foldl (fun (acc : E × E) (x : Array E × ℕ) ↦
    (acc.1 + acc.2 * evalB x.1 x.2 (wOf tr t), acc.2 * (wOf tr t).getD x.2 0)) (0, 1)).1

/-- **The values after the tables'**: the memory's three, the bytecode's two, `T(t)`, `Q_W(t)`. -/
def tailAtT : List E :=
  [memAtT tr t 3, addressAtT tr t, memoryPullAtT tr alphas beta t, bytecodeFinalAtT tr t,
    bytecodePullAtT tr alphas beta t, heapAtT tr c2 t, constraintAtT tr c2 t]

/-- **What the prover sends at `t`**: every table's values (`tvals`), then `tailAtT`. -/
theorem atTOf_values (gamma : E) (fo : Option FlockOut) :
    (atTOf tr c2 alphas beta gamma t fo).values =
      tables.flatMap (tvals tr (eqKernel alphas) beta (wOf tr t)) ++ tailAtT tr c2 alphas beta t := by
  unfold atTOf
  dsimp only
  rw [atTLoop_eq tr (eqKernel alphas) beta (wOf tr t) _ ?hb]
  case hb => intro _ _; rfl
  rw [pure_bind]
  have hL := atTFold_fst tr (eqKernel alphas) beta (wOf tr t) tables (#[], #[], #[])
  rcases fo with _ | out
  · dsimp only
    rw [hL]
    simp [tailAtT, memAtT, addressAtT, memoryPullAtT, bytecodeFinalAtT, bytecodePullAtT, heapAtT, constraintAtT, wOf]
    rfl
  · dsimp only
    rcases out.end_ with ⟨map, target⟩ | ⟨ws, value⟩
    all_goals
      dsimp only
      rw [hL]
      simp [tailAtT, memAtT, addressAtT, memoryPullAtT, bytecodeFinalAtT, bytecodePullAtT, heapAtT, constraintAtT, wOf]
      rfl

/-- **The pending matrices `atTOf` leaves**: Flock's, with `q_flock`'s point. -/
theorem atTOf_pending (gamma : E) (fo : Option FlockOut) :
    (atTOf tr c2 alphas beta gamma t fo).pending = fo.map fun out ↦ (out.pending, out.point) := by
  unfold atTOf
  dsimp only
  rw [atTLoop_eq tr (eqKernel alphas) beta (wOf tr t) _ ?hb]
  case hb => intro _ _; rfl
  rw [pure_bind]
  rcases fo with _ | out
  · rfl
  · dsimp only
    rcases out.end_ with ⟨map, target⟩ | ⟨ws, value⟩ <;> rfl

/-- **The ring map `atTOf` leaves**, Flock's end a ring switch's. -/
theorem atTOf_ringMap (gamma : E) (fo : FlockOut) {map : List E} {target : E} (h : fo.end_ = .ring map target) :
    (atTOf tr c2 alphas beta gamma t (some fo)).ringMap = some map := by
  unfold atTOf
  dsimp only
  rw [atTLoop_eq tr (eqKernel alphas) beta (wOf tr t) _ ?hb]
  case hb => intro _ _; rfl
  rw [pure_bind, h]
  rfl

/-- Without Flock, no ring map. -/
theorem atTOf_ringMap_none (gamma : E) : (atTOf tr c2 alphas beta gamma t none).ringMap = none := by
  unfold atTOf
  dsimp only
  rw [atTLoop_eq tr (eqKernel alphas) beta (wOf tr t) _ ?hb]
  case hb => intro _ _; rfl
  rfl

end AtT

/-- The active rows' vanishing polynomials from the counts' bits the verifier reads are the prover's. -/
theorem countBits_zip_map (w : List E) : ∀ (rows heights : List ℕ), rows.length = heights.length →
    ((countBitsOf rows heights).zip heights).map (fun x ↦ activeVanishingFromBits w x.1 x.2) =
      (rows.zip heights).map (fun x ↦
        activeVanishingFromBits w ((List.range (x.2 + 1)).map fun b ↦ intBits x.1 b 1) x.2)
  | [], [], _ => rfl
  | n :: rows, r :: heights, h => by
    simp only [countBitsOf, List.zipWith_cons_cons, List.zip_cons_cons, List.map_cons]
    rw [← countBitsOf, countBits_zip_map w rows heights (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-! ## The prover's state when the batching sumcheck starts -/

/-- **The prover's state when the batching sumcheck starts** (`proveStreamWith`, steps 0–8): `C1`'s stack and
commitment, `α β γ`, Flock's output, `C2`'s data and commitment, `t`, the values and relations at `t`, `ρ`, the
combined claims, the stacks' layouts, the setup's stack. -/
structure FrontOut where
  stack1 : Array K
  committed1 : Committed
  alphas : List E
  beta : E
  gamma : E
  flockOut : Option FlockOut
  c2 : C2Data
  committed2 : Committed
  t : E
  atT : AtT
  rho : E
  combined : List (Commitment × Combined)
  stackLayouts : List (Commitment × StackLayout)
  stack3 : Array K

/-- Three stacks as a function of the commitment. -/
def stacksOf (s1 s2 s3 : Array K) : Commitment → Array K := fun c ↦
  match c with
  | .c1 => s1
  | .c2 => s2
  | .setup => s3

/-- The three stacks (`proveStreamWith`'s `stackOf`). -/
def FrontOut.stackOf (F : FrontOut) : Commitment → Array K := stacksOf F.stack1 F.c2.stack F.stack3

section Front

variable (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed) (flock : FlockProver Id)

/-- **The prover's run up to `ρ`** (`proveStreamWith`'s steps 0–8, at `Id` with `pure ∘ H`), from the writer `w0`:
its state, and the writer when the batching sumcheck starts. -/
def frontOf (blake2s : Blake2s) (tr : Trace) (w0 : Wr) : FrontOut × Wr :=
  let shape := tr.shape
  let w1 := w0.append (tr.rows.flatMap fun n ↦ integerWire n 4)
  let stack1 := c1Stack tr
  let committed1 : Committed := commit .c1 (c1Layout shape).vars stack1
  let w2 := w1.append (rootWord committed1.halves)
  let alphas := ((samplesW (m := Id) (Pure.pure ∘ H) 4).run w2).1
  let w3 := ((samplesW (m := Id) (Pure.pure ∘ H) 4).run w2).2
  let beta := (Wr.sampled H w3).1
  let w4 := (Wr.sampled H w3).2
  let gamma := (Wr.sampled H w4).1
  let w5 := (Wr.sampled H w4).2
  let logN := blake2sR1csLogSize + shape.heights.getD opBlake2s 0
  let flockOut : Option FlockOut := match blake2s with
    | .flock variant => some ((flock logN variant tr.qflock).run w5).1
    | .omitted => none
  let w6 := match blake2s with
    | .flock variant => ((flock logN variant tr.qflock).run w5).2
    | .omitted => w5
  let c2 := c2DataOf tr (eqKernel alphas) beta gamma
  let committed2 : Committed := commit .c2 (((layoutsOf shape).lookup .c2).getD default).vars c2.stack
  let w7 := w6.append (rootWord committed2.halves)
  let t := (Wr.sampled H w7).1
  let w8 := (Wr.sampled H w7).2
  let a := atTOf tr c2 alphas beta gamma t flockOut
  let w9 := w8.append (a.values.flatMap scalarWire)
  let rho := (Wr.sampled H w9).1
  let w10 := (Wr.sampled H w9).2
  let combined := commitments.filterMap fun c ↦ (combine a.relations c rho).map (c, ·)
  let stackLayouts := layouts shape a.c2Columns
  (⟨stack1, committed1, alphas, beta, gamma, flockOut, c2, committed2, t, a, rho, combined, stackLayouts,
    setupStackOf tr⟩, w10)

/-- **The batching sumcheck's hypothesis at the prover's state** (`BatchSyncs` at `frontOf`'s): the combined claims,
the layouts, the stacks, the ring map, Flock's tables, the pending matrices. -/
def BatchSyncsAt (blake2s : Blake2s) (tr : Trace) (seed : Digest) (terminal : Wr → E) : Prop :=
  BatchSyncs H (frontOf H commit flock blake2s tr (Wr.start seed)).1.combined
    (frontOf H commit flock blake2s tr (Wr.start seed)).1.stackLayouts
    (frontOf H commit flock blake2s tr (Wr.start seed)).1.stackOf
    (frontOf H commit flock blake2s tr (Wr.start seed)).1.atT.ringMap
    ((frontOf H commit flock blake2s tr (Wr.start seed)).1.flockOut.map (·.tables))
    (frontOf H commit flock blake2s tr (Wr.start seed)).1.atT.pending terminal

end Front

set_option maxHeartbeats 4000000 in
theorem reduce_steps (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed)
    (flock : FlockProver Id) (tr : Trace) (seed : Digest) (hvalid : tr.shape.validate true = true)
    (hlen : tr.rows.length = tr.shape.heights.length) (h32 : ∀ n ∈ tr.rows, n < 2 ^ 32)
    (hflock : FlockSyncs H flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) flockMain tr.qflock)
    (terminal : Wr → E) (hbatch : BatchSyncsAt H commit flock (.flock flockMain) tr seed terminal) :
    StepsE (reduceWithH (m := Id) (Pure.pure ∘ H) tr.shape (publicWordsOf tr.publicInput) (.flock flockMain) .point)
      (proveStreamWith (m := Id) (Pure.pure ∘ H) commit flock (.flock flockMain) tr) 0 (Wr.start seed)
      (fun R out posF wF zs ↦ posF = wF.stream.size ∧ out.stream = wF.stream ∧
        R.openings = out.claims.map pointOpening ∧ R.matrices = out.matrices ∧
        R.roots = (rootRead out.c1.2.halves, rootRead out.c2.2.halves) ∧
        zs = countChecks tr.rows tr.shape.heights ++
          [terminal (frontOf H commit flock (.flock flockMain) tr (Wr.start seed)).2]) := by
  have hb : (Blake2s.flock flockMain != Blake2s.omitted) = true := by decide
  unfold reduceWithH proveStreamWith
  simp only [hb, hvalid, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  apply StepsE.pbind (rows_writes tr.rows _ (fun _ _ ↦ rfl) _)
  apply StepsE.plift
  apply StepsE.pbind (sendRoot_writes _ _)
  apply StepsE.vread (P := []) (Q := rootWord (commit .c1 (c1Layout tr.shape).vars (c1Stack tr)).halves)
    (countBits_reads hlen h32)
  · simp [Wr.start]
  apply StepsE.pos_start (pos0 := (tr.rows.flatMap fun n ↦ integerWire n 4).length) (by simp)
  apply StepsE.vread (Q := []) (nextRoot_reads (commit .c1 (c1Layout tr.shape).vars (c1Stack tr)).halves)
  · simp [Wr.start]
  apply StepsE.bind_pos (h1 := Steps.samples H 4 _)
  case e => simp [Wr.start]
  set w2 := ((Wr.start seed).append (tr.rows.flatMap fun n ↦ integerWire n 4)).append
    (rootWord (commit .c1 (c1Layout tr.shape).vars (c1Stack tr)).halves) with hw2
  set alphas := ((samplesW (m := Id) (Pure.pure ∘ H) 4).run w2).1 with halphas
  set w3 := ((samplesW (m := Id) (Pure.pure ∘ H) 4).run w2).2 with hw3
  apply StepsE.bind_pos (h1 := Steps.sample H w3)
  case e => rw [hw3, samplesW_stream]
  set beta := (Wr.sampled H w3).1 with hbeta
  set w4 := (Wr.sampled H w3).2 with hw4
  apply StepsE.bind_pos (h1 := Steps.sample H w4)
  case e => rfl
  set gamma := (Wr.sampled H w4).1 with hgamma
  set w5 := (Wr.sampled H w4).2 with hw5
  apply StepsE.bind_pos (h1 := Steps.pmap (g := some) (hflock w5).steps)
  case e => rfl
  set fo := ((flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) flockMain tr.qflock).run w5).1 with hfo
  set w6 := ((flock (blake2sR1csLogSize + tr.shape.heights.getD opBlake2s 0) flockMain tr.qflock).run w5).2 with hw6
  apply StepsE.vpure
  apply StepsE.plift
  apply StepsE.pbind (sendRoot_writes _ _)
  apply StepsE.vreadEnd (nextRoot_reads _)
  set c2 := c2DataOf tr (eqKernel alphas) beta gamma with hc2
  set committed2 := commit .c2 (((layoutsOf tr.shape).lookup .c2).getD default).vars c2.stack with hcm2
  apply StepsE.bind_pos (h1 := Steps.sample H _)
  case e => simp
  set w7 := w6.append (rootWord committed2.halves) with hw7
  set t := (Wr.sampled H w7).1 with ht
  set w8 := (Wr.sampled H w7).2 with hw8
  set a := atTOf tr c2 alphas beta gamma t (some fo) with ha
  have hvals := atTOf_values tr c2 alphas beta t gamma (some fo)
  apply StepsE.pbind (sendScalars_writes _ _)
  apply StepsE.vreadD (R := (tailAtT tr c2 alphas beta t).flatMap scalarWire)
    (tablesLoop_reads tr (eqKernel alphas) beta (wOf tr t) _ ?hb tables (#[], #[]))
  case hb => intro _ _; rfl
  case hpos => simp [hw8, ha, hvals]
  case hd => simp [hw8, ha, hvals, List.flatMap_append]
  intro hd0
  unfold tailAtT at hd0
  apply StepsE.vscalarD hd0; intro hd1
  apply StepsE.vscalarD hd1; intro hd2
  apply StepsE.vscalarD hd2; intro hd3
  apply StepsE.vscalarD hd3; intro hd4
  apply StepsE.vscalarD hd4; intro hd5
  apply StepsE.vscalarD hd5; intro hd6
  apply StepsE.vscalarD hd6; intro _
  obtain ⟨map, target, hend⟩ : ∃ map target, fo.end_ = .ring map target :=
    verifyDeferredH_end H _ _ _ (((hflock w5).steps).2.2 w6.stream #[] (List.prefix_refl _))
  have hcond : (flockMain.slices == Flock.Slices.tower && ClaimsMode.point == ClaimsMode.point) = true := by decide
  simp only [hend, hcond, ↓reduceIte]
  apply StepsE.bind_pos (h1 := Steps.sample H _)
  case e => simp [hw8, ha, hvals, tailAtT, List.flatMap_append]; omega
  set w9 := w8.append (a.values.flatMap scalarWire) with hw9
  set rho := (Wr.sampled H w9).1 with hrho
  set w10 := (Wr.sampled H w9).2 with hw10
  have hpend : a.pending = some (fo.pending, fo.point) := atTOf_pending tr c2 alphas beta t gamma (some fo)
  have hring : a.ringMap = some map := atTOf_ringMap tr c2 alphas beta t gamma fo hend
  simp only [hpend, hring]
  have hB := hbatch w10
  generalize hF : (frontOf H commit flock (.flock flockMain) tr (Wr.start seed)).1 = F at hB
  have hFp : F.atT.pending = some (fo.pending, fo.point) := by rw [← hF]; exact hpend
  have hFr : F.atT.ringMap = some map := by rw [← hF]; exact hring
  have hFc : F.combined = commitments.filterMap (fun c ↦ (combine a.relations c rho).map (c, ·)) := by
    rw [← hF]; rfl
  have hFl : F.stackLayouts = layouts tr.shape a.c2Columns := by rw [← hF]; rfl
  have hFs : F.stackOf = stacksOf (c1Stack tr) c2.stack (setupStackOf tr) := by rw [← hF]; rfl
  have hFt : F.flockOut.map (·.tables) = some fo.tables := by rw [← hF]; rfl
  rw [hFp, hFr, hFc, hFl, hFs, hFt] at hB
  apply StepsE.prog_eq (p' := batchProver (Pure.pure ∘ H)
    (commitments.filterMap fun c ↦ (combine a.relations c rho).map (c, ·)) (layouts tr.shape a.c2Columns)
    (stacksOf (c1Stack tr) c2.stack (setupStackOf tr)) (some map) (some fo.tables) (some (fo.pending, fo.point)) >>=
      fun cm ↦ (get : WrM Id Wr) >>= fun c ↦ Pure.pure ⟨c.stream, (c1Stack tr, commit .c1 (c1Layout tr.shape).vars
        (c1Stack tr)), (c2.stack, committed2), setupStackOf tr, cm.1, cm.2,
        commitments.filterMap fun c ↦ (combine a.relations c rho).map (c, ·), c2.heapVals⟩)
  case e =>
    simp only [batchProver, bind_assoc, pure_bind]
    rfl
  apply StepsE.bind_veq (h1 := hB.steps)
  case e =>
    congr 1
    · congr 1
      funext c
      congr 2
      rw [ha, countBits_zip_map _ _ _ hlen]
      unfold atTOf
      dsimp only
      rw [atTLoop_eq tr (eqKernel alphas) beta (wOf tr t) _ ?hb]
      case hb => intro _ _; rfl
      rw [pure_bind, hend, atTFold_snd]
      rfl
    · congr 1
      rw [ha, countBits_zip_map _ _ _ hlen]
      unfold atTOf
      dsimp only
      rw [atTLoop_eq tr (eqKernel alphas) beta (wOf tr t) _ ?hb]
      case hb => intro _ _; rfl
      rw [pure_bind, hend, atTFold_snd]
      rfl
  apply StepsE.pget
  apply StepsE.vite
  apply StepsE.pure
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · split <;> rfl
  · split
    · rfl
    · exact (Option.not_isSome_iff_eq_none.mp (by assumption)).symm
  · split <;> rfl
  · simp only [List.nil_append, List.append_nil]
    rfl

end UniComplete
