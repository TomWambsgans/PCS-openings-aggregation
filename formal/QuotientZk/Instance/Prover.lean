-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The claims' bytes are `opening::iv`'s (`crates/quotient/src/opening.rs`: each coordinate's limbs
-- `c0, c1, c2`, little-endian); a leaf's bytes are the full-width image `whir.rs` hashes (the absent
-- lanes' zeros, then the committed lanes from the last, each word little-endian).
import QuotientZk.Instance.Openings

/-!
# The deployed prover as the joint model

**The prover** (`Pb R`, read through `DRpm.ofBytes`): its randomness is the masks and the two
tables' paddings (`Rand`); its secret tables' leaves are the bytes of their stacks' codeword rows
(`rowBytes`: `whir.rs`'s 64-word leaf image) at the novel basis's point of the leaf (`codeAt`), the
quotient table after `α, β, γ` (`cK 1 = 3`); its opened positions are `slotsW`, `slotsQ`; its
messages, after `k` challenges, are **the claims** at the openings' starts (`k = 5, 128, 242`,
`opening::iv`'s bytes of the verifier's claims) followed by **`R k h (avail k v)`**: any public
function `R` (the renderer) of the step, the answers so far and the part of the joint view
`v = jv (chOf h) s` that has been drawn for by then (`avail`: the five values after `t`, a lane
round after its challenges, the folded table after the six lane folds, the opened rows after the
position draws). The deployed renderer is WHIR's honest prover (`whir.rs`, `recursive_prover`): the
five values, the lane rounds, then everything after the first fold from the folded table `f¹` and
the challenges, the opened rows; the statement holds for every `R`.

**The link** (`link`): `LinkV`'s fields, proved:

* `hview` (`view_eq`): the view is `out σ` of the joint view, by **causality** (`avail_jv_take`:
  what `avail k` keeps of the joint view depends only on the first `k` answers; `laneRounds_congr`);
* `rows₁`, `rows₂`, `inj₁`, `inj₂`: the leaves are the injective `rowBytes` of the stacks' rows;
* `free₁`, `free₁₂`, `free₂`, `free₂₂`: (Q) for the unopened rows, from the novel basis's degrees
  (`free_one`, `free_two`), at most `225 + 2 ≤ 247` points.

**`FSFresh`'s conditions** (`fsFresh_deployed_bits`): `hlong_Pb` (leaves of `512 > 192` bytes),
`hcK_Pb`, `hrow₀_Pb` (the first witness leaf keeps `2^-2368`: its row is free entries,
`hidden_hδ`), `claimsAt_W`, `claimsAt_σ`, `claimsAt_Q` (the claims' first coordinate is `ρ`, then
`t/(1+t)`, read off the chain states `4` and `3`), `hcw_deployed` (`2^-191`: `t ↦ t/(1+t)` is at most
2-to-1), `hn_Pb`.
-/

open OracleComp OracleSpec Polynomial Module QuotientSecurity QuotientSecurity.Hiding QuotientRpm
open QuotientZk.Joint
open QuotientZk.Deployed (Inp Out Msg Item Tbl Pos KSt)
open LeanVM.Protocol.KeccakHash (wordBytes)
open scoped ENNReal

namespace QuotientZk.Instance

set_option linter.unusedSectionVars false

/-! ## Bytes -/

/-- A scalar's bytes (`opening::iv`): its limbs `c0, c1, c2`, little-endian. -/
def scalarLE (x : Limbs) : List UInt8 := wordBytes x.1 ++ wordBytes x.2.1 ++ wordBytes x.2.2

theorem length_scalarLE (x : Limbs) : (scalarLE x).length = 24 := by
  simp [scalarLE, LeanVM.Rpm.wordBytes_len]

theorem scalarLE_injective : Function.Injective scalarLE := by
  rintro ⟨a0, a1, a2⟩ ⟨b0, b1, b2⟩ h
  simp only [scalarLE, List.append_assoc] at h
  have h0 := congrArg LeanVM.Rpm.bytesLane h
  rw [LeanVM.Rpm.bytesLane_wordBytes_append, LeanVM.Rpm.bytesLane_wordBytes_append] at h0
  subst h0
  have h' := List.append_cancel_left h
  have h1 := congrArg LeanVM.Rpm.bytesLane h'
  rw [LeanVM.Rpm.bytesLane_wordBytes_append, LeanVM.Rpm.bytesLane_wordBytes_append] at h1
  subst h1
  have h'' := List.append_cancel_left h'
  have h2 := congrArg LeanVM.Rpm.bytesLane h''
  rw [← List.append_nil (wordBytes a2), ← List.append_nil (wordBytes b2),
    LeanVM.Rpm.bytesLane_wordBytes_append, LeanVM.Rpm.bytesLane_wordBytes_append] at h2
  subst h2
  rfl

theorem length_flatMap_wordBytes : ∀ l : List UInt64, (l.flatMap wordBytes).length = 8 * l.length
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, LeanVM.Rpm.wordBytes_len,
      length_flatMap_wordBytes l, List.length_cons]
    ring

theorem flatMap_wordBytes_injective : Function.Injective (fun l : List UInt64 => l.flatMap wordBytes)
  | [], [], _ => rfl
  | [], b :: l, h => by
    have := congrArg List.length h
    simp only [List.flatMap_nil, List.length_nil, length_flatMap_wordBytes, List.length_cons] at this
    omega
  | a :: l, [], h => by
    have := congrArg List.length h
    simp only [List.flatMap_nil, List.length_nil, length_flatMap_wordBytes, List.length_cons] at this
    omega
  | a :: l, b :: l', h => by
    simp only [List.flatMap_cons] at h
    have hab := congrArg LeanVM.Rpm.bytesLane h
    rw [LeanVM.Rpm.bytesLane_wordBytes_append, LeanVM.Rpm.bytesLane_wordBytes_append] at hab
    subst hab
    rw [flatMap_wordBytes_injective (List.append_cancel_left h)]

section Field

variable {K E : Type} [Field K] [Field E] [Algebra K E] (rep : Rep K E)

/-- **A leaf's bytes** (`whir.rs`): the 64-word image, the absent lanes' zeros first, then the
committed lanes from the last to the first, each word little-endian. -/
def rowBytes {n : ℕ} (row : Fin n → K) : List UInt8 :=
  (List.replicate (64 - n) 0 ++ (List.ofFn fun l => rep.toWord (row l)).reverse).flatMap wordBytes

theorem rowBytes_injective {n : ℕ} : Function.Injective (rowBytes rep (n := n)) := by
  intro r r' h
  have h1 := List.append_cancel_left (flatMap_wordBytes_injective h)
  have h2 := List.reverse_injective h1
  funext l
  exact rep.toWord_injective (congrFun (List.ofFn_injective h2) l)

theorem length_rowBytes {n : ℕ} (hn : n ≤ 64) (row : Fin n → K) : (rowBytes rep row).length = 512 := by
  rw [rowBytes, length_flatMap_wordBytes, List.length_append, List.length_replicate,
    List.length_reverse, List.length_ofFn]
  omega

/-- A coordinate list's bytes. -/
def scalarsLE (l : List E) : List UInt8 := l.flatMap fun x => scalarLE (rep.limbs x)

/-- The novel basis at the point of position `x`: the coefficient vector of a codeword row. -/
noncomputable def codeAt (ℓ x : ℕ) : Fin (2 ^ ℓ) → K := fun y => (novel rep.w.v ℓ y).eval (rep.w.word x)

end Field

/-! ## The prover -/

section Prover

variable {K E : Type} [Field K] [Field E] [Algebra K E] [DecidableEq E] [CharP E 2] [Fintype E]
  (rep : Rep K E) (P₀ : Params E) (gK : Fin 4 → K[X]) (van : K[X]) (stmt : Fin P₀.words → E)
  (Y : E) (TW : (Fin 4 → Fin 3 → K) → ιW → YW → K)
  (TQ : E × E × E → (Fin 4 → Fin 3 → K) → ιQ → YQ → K)

/-- The joint view: the five values, the wiring opening (public: nothing), the two level-0
views. -/
abbrev JV (K E : Type) [Field K] := Vals E × Unit × L0View E ιW YW (Fin 224) K ×
  L0View E ιQ YQ (Fin 225) K

/-- The prover's randomness. -/
abbrev RandD (K : Type) := Rand K ιW YW ιQ YQ

/-- **The renderer**: what the prover sends besides the claims, a public function of the step, the
answers so far and the available part of the joint view. -/
abbrev Renderer (K E : Type) [Field K] := ℕ → List Out → JV K E → Msg

/-- The witness table as the model has it (it reads no challenge), the quotient table (it reads
`α, β, γ`). -/
def T₁ : DChal E → (Fin 4 → Fin 3 → K) → ιW → YW → K := fun _ m => TW m
def T₂ : DChal E → (Fin 4 → Fin 3 → K) → ιQ → YQ → K := fun c m => TQ c.1.1.1 m

/-- **The joint view** of the deployed protocol. -/
noncomputable def jv (c : DChal E) (s : RandD K) : JV K E :=
  (modelV P₀ gK van (fun _ => ()) (T₁ TW) (T₂ TQ) (openW rep Y) (openQ rep P₀ Y)).view c s

theorem jv_red (c : DChal E) (s : RandD K) :
    (jv rep P₀ gK van Y TW TQ c s).1 = redMsgs P₀ gK van c.1.1.2 s.1 := rfl

/-- The witness opening's level-0 view in the joint view. -/
theorem jv_W (c : DChal E) (s : RandD K) :
    (jv rep P₀ gK van Y TW TQ c s).2.2.1 = Gadget.levelMap (Lw.toGadget okW) Lw.pos
      (Lw.claimW fun _ => pointW c) ![1, Y, Y ^ 2] (Gadget.powers 1 (lam₁ c)) (phi₁ c)
      (novelEnc rep.w Lw.logLane (slotFn 20 224 (drawsW c)))
      ((Lw.toGadget okW).stackD (TW s.1) + (Lw.toGadget okW).stackR s.2.1) := rfl

/-- The quotient opening's. -/
theorem jv_Q (c : DChal E) (s : RandD K) :
    (jv rep P₀ gK van Y TW TQ c s).2.2.2 = Gadget.levelMap (Lq.toGadget okQ) Lq.pos
      (Lq.claimW ![pointQ P₀ Y c (redMsgs P₀ gK van c.1.1.2 s.1), pointS Y]) ![1, Y, Y ^ 2]
      (Gadget.powers 2 (lam₂ c)) (phi₂ c) (novelEnc rep.w Lq.logLane (slotFn 23 225 (drawsQ c)))
      ((Lq.toGadget okQ).stackD (TQ c.1.1.1 s.1) + (Lq.toGadget okQ).stackR s.2.2) := rfl

/-- What has been drawn for after `k` challenges: in an opening starting at step `st`, its lane
round `j` after `st + 1 + j`, its folded table after `st + 7`, its opened rows after `pe`. -/
def availL0 {ι Y Q : Type} (st pe k : ℕ) (lv : L0View E ι Y Q K) : L0View E ι Y Q K :=
  (fun j => if st + 1 + (j : ℕ) ≤ k then lv.1 j else 0, if st + 7 ≤ k then lv.2.1 else 0,
    if pe ≤ k then lv.2.2 else 0)

/-- **The available part of the joint view** after `k` challenges. -/
def avail (k : ℕ) (v : JV K E) : JV K E :=
  (if 4 ≤ k then v.1 else 0, v.2.1, availL0 5 56 k v.2.2.1, availL0 242 300 k v.2.2.2)

/-- **The claims' bytes** at the openings' starts (`opening::iv`): the verifier's claims
(`modelWitness`, `modelWiring`, `modelQuotient` and `modelSum`), points then values. -/
noncomputable def claimMsg (k : ℕ) (c : DChal E) (v : Vals E) : List Item :=
  if k = 5 then [.bytes (scalarsLE rep (Implementation.modelWitness c.1.1.2 c.1.2 v.1))]
  else if k = 128 then [.bytes (scalarsLE rep (Implementation.modelWiring c.1.1.2 v.2))]
  else if k = 242 then [.bytes (scalarsLE rep
    (Implementation.modelQuotient P₀ c.1.1.1.1 c.1.1.1.2.1 c.1.1.1.2.2 c.1.1.2 c.1.2 v.2 Y v.1 ++
      Implementation.modelSum P₀ stmt c.1.1.1.2.2 Y))]
  else []

/-- **The message after `k` challenges**, from public data and the available joint view. -/
noncomputable def msgPub (R : Renderer K E) (k : ℕ) (h : List Out) (va : JV K E) : Msg :=
  claimMsg rep P₀ stmt Y k (chOf rep.limbs h) va.1 ++ R k h va

/-- The prover's message after the answers `h`. -/
noncomputable def PbMsg (R : Renderer K E) (s : RandD K) (h : List Out) : Msg :=
  msgPub rep P₀ stmt Y R h.length h (avail h.length (jv rep P₀ gK van Y TW TQ (chOf rep.limbs h) s))

/-- The witness table is committed first, the quotient table after `α, β, γ`. -/
def PbcK (k : Tbl) : ℕ := if (k : ℕ) = 0 then 0 else 3

/-- A secret leaf's bytes. -/
noncomputable def PbRow (s : RandD K) (h : List Out) (k : Tbl) (x : Pos) : List UInt8 :=
  if (k : ℕ) = 0 then
    rowBytes rep (Deployed.rowAt (codeAt rep Lw.logLane x)
      (stackV₁ (T₁ TW) (openW rep Y).L (chOf rep.limbs h) s))
  else
    rowBytes rep (Deployed.rowAt (codeAt rep Lq.logLane x)
      (stackV₂ (T₂ TQ) (openQ rep P₀ Y).L (chOf rep.limbs h) s))

/-- The opened positions. -/
def PbOpened (σ : List Out) (k : Tbl) (x : Pos) : Bool :=
  if (k : ℕ) = 0 then decide ((x : ℕ) ∈ slotsW (chOf rep.limbs σ))
  else decide ((x : ℕ) ∈ slotsQ (chOf rep.limbs σ))

/-- **The deployed prover**, its leaves byte strings. -/
noncomputable def Pb (R : Renderer K E) : Proto (RandD K) (List UInt8) Out Msg Tbl Pos where
  n := nRaw
  msgFn := PbMsg rep P₀ gK van stmt Y TW TQ R
  cK := PbcK
  rowFn := PbRow rep P₀ Y TW TQ
  opened := PbOpened (E := E) rep

theorem ofBytes_opened {S : Type} (P : Proto S (List UInt8) Out Msg Tbl Pos) :
    (DRpm.ofBytes P).opened = P.opened := rfl

theorem Pb_opened (R : Renderer K E) :
    (Pb rep P₀ gK van stmt Y TW TQ R).opened = PbOpened (E := E) rep := rfl
theorem Pb_rowFn (R : Renderer K E) :
    (Pb rep P₀ gK van stmt Y TW TQ R).rowFn = PbRow rep P₀ Y TW TQ := rfl
theorem Pb_cK (R : Renderer K E) : (Pb rep P₀ gK van stmt Y TW TQ R).cK = PbcK := rfl
theorem Pb_msgFn (R : Renderer K E) :
    (Pb rep P₀ gK van stmt Y TW TQ R).msgFn = PbMsg rep P₀ gK van stmt Y TW TQ R := rfl
theorem Pb_n (R : Renderer K E) : (Pb rep P₀ gK van stmt Y TW TQ R).n = nRaw := rfl

theorem PbOpened_zero (σ : List Out) (x : Pos) :
    PbOpened (E := E) rep σ 0 x = decide ((x : ℕ) ∈ slotsW (chOf rep.limbs σ)) := by
  unfold PbOpened
  exact if_pos rfl

theorem PbOpened_one (σ : List Out) (x : Pos) :
    PbOpened (E := E) rep σ 1 x = decide ((x : ℕ) ∈ slotsQ (chOf rep.limbs σ)) := by
  unfold PbOpened
  exact if_neg (by decide)

theorem PbcK_zero : PbcK 0 = 0 := by unfold PbcK; exact if_pos rfl
theorem PbcK_one : PbcK 1 = 3 := by unfold PbcK; exact if_neg (by decide)

theorem PbRow_zero (s : RandD K) (h : List Out) (x : Pos) :
    PbRow rep P₀ Y TW TQ s h 0 x = rowBytes rep (Deployed.rowAt (codeAt rep Lw.logLane x)
      (stackV₁ (T₁ TW) (openW rep Y).L (chOf rep.limbs h) s)) := by
  unfold PbRow
  exact if_pos rfl

theorem PbRow_one (s : RandD K) (h : List Out) (x : Pos) :
    PbRow rep P₀ Y TW TQ s h 1 x = rowBytes rep (Deployed.rowAt (codeAt rep Lq.logLane x)
      (stackV₂ (T₂ TQ) (openQ rep P₀ Y).L (chOf rep.limbs h) s)) := by
  unfold PbRow
  exact if_neg (by decide)

theorem stackV₁_eq (c : DChal E) (s : RandD K) :
    stackV₁ (T₁ TW) (openW rep Y).L c s =
      (Lw.toGadget okW).stackD (TW s.1) + (Lw.toGadget okW).stackR s.2.1 := rfl

theorem stackV₂_eq (c : DChal E) (s : RandD K) :
    stackV₂ (T₂ TQ) (openQ rep P₀ Y).L c s =
      (Lq.toGadget okQ).stackD (TQ c.1.1.1 s.1) + (Lq.toGadget okQ).stackR s.2.2 := rfl

/-- An opened row, from the joint view. -/
def outRow (σ : List Out) (v : JV K E) (k : Tbl) (x : Pos) : Inp :=
  if (k : ℕ) = 0 then .inl (rowBytes rep (v.2.2.1.2.2 (slotOf 20 224 (drawsW (chOf rep.limbs σ)) x)))
  else .inl (rowBytes rep (v.2.2.2.2.2 (slotOf 23 225 (drawsQ (chOf rep.limbs σ)) x)))

theorem outRow_zero (σ : List Out) (v : JV K E) (x : Pos) :
    outRow rep σ v 0 x = .inl (rowBytes rep (v.2.2.1.2.2 (slotOf 20 224 (drawsW (chOf rep.limbs σ)) x))) := by
  unfold outRow
  exact if_pos rfl

theorem outRow_one (σ : List Out) (v : JV K E) (x : Pos) :
    outRow rep σ v 1 x = .inl (rowBytes rep (v.2.2.2.2.2 (slotOf 23 225 (drawsQ (chOf rep.limbs σ)) x))) := by
  unfold outRow
  exact if_neg (by decide)

theorem jv_W_rows (c : DChal E) (s : RandD K) :
    (jv rep P₀ gK van Y TW TQ c s).2.2.1.2.2 =
      rowsMap (novelEnc rep.w Lw.logLane (slotFn 20 224 (drawsW c)))
        ((Lw.toGadget okW).stackD (TW s.1) + (Lw.toGadget okW).stackR s.2.1) := by
  rw [jv_W]
  rfl

theorem jv_Q_rows (c : DChal E) (s : RandD K) :
    (jv rep P₀ gK van Y TW TQ c s).2.2.2.2.2 =
      rowsMap (novelEnc rep.w Lq.logLane (slotFn 23 225 (drawsQ c)))
        ((Lq.toGadget okQ).stackD (TQ c.1.1.1 s.1) + (Lq.toGadget okQ).stackR s.2.2) := by
  rw [jv_Q]
  rfl

theorem rowsMap_eq_rowAt {ι Yt Q : Type} [Fintype ι] [Fintype Yt] (enc : Q → Yt → K)
    (T : ι → Yt → K) (q : Q) : rowsMap enc T q = Deployed.rowAt (enc q) T := rfl

/-- **The view from the joint view** (public). -/
noncomputable def out (R : Renderer K E) (σ : List Out) (v : JV K E) : View Msg Inp Tbl Pos where
  msg c := msgPub rep P₀ stmt Y R (min c σ.length) (σ.take c) (avail (min c σ.length) v)
  row k x := if (DRpm.ofBytes (Pb rep P₀ gK van stmt Y TW TQ R)).opened σ k x then
    outRow rep σ v k x else default

/-! ### Causality -/

theorem laneRounds_congr {Yt : Type} [Fintype Yt] :
    ∀ (k : ℕ) (φ φ' : Fin k → E) (w t : LTable E Yt k) (j : Fin k),
      (∀ i : Fin k, (i : ℕ) < j → φ i = φ' i) → laneRounds k φ w t j = laneRounds k φ' w t j
  | 0, _, _, _, _, j, _ => j.elim0
  | k + 1, φ, φ', w, t, ⟨j, hj⟩, h => by
    cases j with
    | zero => rfl
    | succ j =>
      have e : (⟨j + 1, hj⟩ : Fin (k + 1)) = Fin.succ ⟨j, by omega⟩ := rfl
      rw [e]
      simp only [laneRounds, Fin.cons_succ]
      have h0 : φ 0 = φ' 0 := h 0 (by simp)
      rw [h0]
      refine laneRounds_congr k _ _ _ _ _ fun i hi => h i.succ ?_
      simp only [Fin.val_succ]
      simp only at hi
      omega

theorem availL0_levelMap_congr {ι Yt Q : Type} [Fintype ι] [DecidableEq ι] [Fintype Yt]
    [DecidableEq Yt] [Fintype Q] [DecidableEq Q] (L : GadgetLayout ι Yt)
    (pos : ι → (Fin 6 → Bool)) {m : ℕ} (Wc Wc' : Fin m → ι → Yt → E) (β : Fin 3 → E)
    (lam lam' : E) (φ φ' : Fin 6 → E) (enc enc' : Q → Yt → K) (T : ι → Yt → K) (st pe k : ℕ)
    (hW : st + 1 ≤ k → Wc = Wc' ∧ lam = lam') (hφ : ∀ i : Fin 6, st + 2 + (i : ℕ) ≤ k → φ i = φ' i)
    (henc : pe ≤ k → enc = enc') :
    availL0 st pe k (Gadget.levelMap L pos Wc β (Gadget.powers m lam) φ enc T) =
      availL0 st pe k (Gadget.levelMap L pos Wc' β (Gadget.powers m lam') φ' enc' T) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext j
    show (if st + 1 + (j : ℕ) ≤ k then _ else 0) = (if st + 1 + (j : ℕ) ≤ k then _ else 0)
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := hW (by omega)
      exact laneRounds_congr 6 φ φ' _ _ j fun i hi => hφ i (by omega)
    · rfl
  · show (if st + 7 ≤ k then foldMap (HiddenLayout.foldW pos φ) T else 0) =
      (if st + 7 ≤ k then foldMap (HiddenLayout.foldW pos φ') T else 0)
    split_ifs with h
    · have : φ = φ' := funext fun i => hφ i (by have := i.isLt; omega)
      rw [this]
    · rfl
  · show (if pe ≤ k then rowsMap enc T else 0) = (if pe ≤ k then rowsMap enc' T else 0)
    split_ifs with h
    · rw [henc h]
    · rfl

theorem drawsW_take (σ : List Out) {k : ℕ} (hk : 56 ≤ k) :
    drawsW (chOf rep.limbs (σ.take k)) = drawsW (chOf rep.limbs σ) := by
  unfold drawsW
  congr 1
  funext i
  rw [chOf_take_gW rep.limbs σ _ (by have := i.isLt; simp only; omega)]

theorem drawsQ_take (σ : List Out) {k : ℕ} (hk : 300 ≤ k) :
    drawsQ (chOf rep.limbs (σ.take k)) = drawsQ (chOf rep.limbs σ) := by
  unfold drawsQ
  congr 1
  funext i
  rw [chOf_take_gQ rep.limbs σ _ (by have := i.isLt; simp only; omega)]

theorem pointW_congr {c c' : DChal E} (h : c.1 = c'.1) : pointW c = pointW c' := by
  unfold pointW; rw [h]

theorem pointQ_congr {c c' : DChal E} (h : c.1 = c'.1) (v : Vals E) :
    pointQ P₀ Y c v = pointQ P₀ Y c' v := by
  unfold pointQ; rw [h]

theorem avail_red_take (σ : List Out) (s : RandD K) (k : ℕ) :
    (if 4 ≤ k then (jv rep P₀ gK van Y TW TQ (chOf rep.limbs (σ.take k)) s).1 else 0) =
      (if 4 ≤ k then (jv rep P₀ gK van Y TW TQ (chOf rep.limbs σ) s).1 else 0) := by
  rw [jv_red, jv_red]
  split_ifs with h
  · rw [chOf_take_t rep.limbs σ h]
  · rfl

theorem avail_W_take (σ : List Out) (s : RandD K) (k : ℕ) :
    availL0 5 56 k (jv rep P₀ gK van Y TW TQ (chOf rep.limbs (σ.take k)) s).2.2.1 =
      availL0 5 56 k (jv rep P₀ gK van Y TW TQ (chOf rep.limbs σ) s).2.2.1 := by
  rw [jv_W, jv_W]
  refine availL0_levelMap_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun h => ⟨?_, ?_⟩)
    (fun i hi => chOf_take_phi₁ rep.limbs σ i (by omega)) (fun h => ?_)
  · rw [pointW_congr (chOf_take_fst rep.limbs σ (by omega))]
  · exact chOf_take_lam₁ rep.limbs σ (by omega)
  · rw [drawsW_take rep σ h]

theorem availL0_low {ι Yt Q : Type} {k : ℕ} (hk : k < 243) (lv lv' : L0View E ι Yt Q K) :
    availL0 242 300 k lv = availL0 242 300 k lv' := by
  refine Prod.ext (funext fun j => ?_) (Prod.ext ?_ ?_)
  · show (if 242 + 1 + (j : ℕ) ≤ k then _ else 0) = (if 242 + 1 + (j : ℕ) ≤ k then _ else 0)
    rw [if_neg (by omega), if_neg (by omega)]
  · show (if 242 + 7 ≤ k then _ else 0) = (if 242 + 7 ≤ k then _ else 0)
    rw [if_neg (by omega), if_neg (by omega)]
  · show (if 300 ≤ k then _ else 0) = (if 300 ≤ k then _ else 0)
    rw [if_neg (by omega), if_neg (by omega)]

theorem avail_Q_take (σ : List Out) (s : RandD K) (k : ℕ) :
    availL0 242 300 k (jv rep P₀ gK van Y TW TQ (chOf rep.limbs (σ.take k)) s).2.2.2 =
      availL0 242 300 k (jv rep P₀ gK van Y TW TQ (chOf rep.limbs σ) s).2.2.2 := by
  by_cases hk : 243 ≤ k
  · rw [jv_Q, jv_Q]
    have hfst := chOf_take_fst rep.limbs σ (k := k) (by omega)
    have h1 : (chOf rep.limbs (σ.take k)).1.1.1 = (chOf rep.limbs σ).1.1.1 := by rw [hfst]
    have h2 : (chOf rep.limbs (σ.take k)).1.1.2 = (chOf rep.limbs σ).1.1.2 := by rw [hfst]
    rw [h1, h2]
    refine availL0_levelMap_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun h => ⟨?_, ?_⟩)
      (fun i hi => chOf_take_phi₂ rep.limbs σ i (by omega)) (fun h => ?_)
    · rw [pointQ_congr P₀ Y hfst]
    · exact chOf_take_lam₂ rep.limbs σ (by omega)
    · rw [drawsQ_take rep σ h]
  · exact availL0_low (by omega) _ _

theorem avail_eq (k : ℕ) (v : JV K E) :
    avail k v = (if 4 ≤ k then v.1 else 0, (), availL0 5 56 k v.2.2.1, availL0 242 300 k v.2.2.2) :=
  rfl

/-- **Causality**: what is available after `k` challenges depends only on the first `k`
answers. -/
theorem avail_jv_take (σ : List Out) (s : RandD K) (k : ℕ) :
    avail k (jv rep P₀ gK van Y TW TQ (chOf rep.limbs (σ.take k)) s) =
      avail k (jv rep P₀ gK van Y TW TQ (chOf rep.limbs σ) s) := by
  rw [avail_eq, avail_eq, avail_red_take, avail_W_take, avail_Q_take]

theorem take_min_length (σ : List Out) (c : ℕ) : σ.take (min c σ.length) = σ.take c := by
  rcases le_total c σ.length with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, List.take_of_length_le le_rfl, List.take_of_length_le h]

/-- **The view is a function of the joint view** (`LinkV.hview`). -/
theorem view_eq (R : Renderer K E) (s : RandD K) (σ : List Out) :
    (DRpm.ofBytes (Pb rep P₀ gK van stmt Y TW TQ R)).view s σ =
      out rep P₀ gK van stmt Y TW TQ R σ (jv rep P₀ gK van Y TW TQ (chOf rep.limbs σ) s) := by
  unfold Proto.view out
  congr 1
  · funext c
    show (Pb rep P₀ gK van stmt Y TW TQ R).msgFn s (σ.take c) = _
    rw [Pb_msgFn]
    show msgPub rep P₀ stmt Y R (σ.take c).length (σ.take c)
      (avail (σ.take c).length (jv rep P₀ gK van Y TW TQ (chOf rep.limbs (σ.take c)) s)) = _
    rw [List.length_take, ← take_min_length σ c, avail_jv_take, take_min_length]
  · funext k x
    split_ifs with h
    · show Sum.inl ((Pb rep P₀ gK van stmt Y TW TQ R).rowFn s
        (σ.take ((Pb rep P₀ gK van stmt Y TW TQ R).cK k)) k x) = outRow rep σ _ k x
      rw [ofBytes_opened, Pb_opened] at h
      rw [Pb_rowFn, Pb_cK]
      obtain rfl | rfl : k = 0 ∨ k = 1 := by fin_cases k <;> simp
      · have hx : (x : ℕ) ∈ slotsW (chOf rep.limbs σ) := by
          rw [PbOpened_zero] at h
          exact of_decide_eq_true h
        rw [PbRow_zero, stackV₁_eq, outRow_zero, jv_W_rows, rowsMap_eq_rowAt]
        have e : novelEnc rep.w Lw.logLane (slotFn 20 224 (drawsW (chOf rep.limbs σ)))
            (slotOf 20 224 (drawsW (chOf rep.limbs σ)) x) = codeAt rep Lw.logLane x := by
          funext y
          simp only [novelEnc, codeAt]
          rw [slotFn_slotOf _ _ _ hx]
        rw [e]
      · have hx : (x : ℕ) ∈ slotsQ (chOf rep.limbs σ) := by
          rw [PbOpened_one] at h
          exact of_decide_eq_true h
        rw [PbcK_one, PbRow_one, stackV₂_eq, chOf_take_abc rep.limbs σ le_rfl, outRow_one,
          jv_Q_rows, rowsMap_eq_rowAt]
        have e : novelEnc rep.w Lq.logLane (slotFn 23 225 (drawsQ (chOf rep.limbs σ)))
            (slotOf 23 225 (drawsQ (chOf rep.limbs σ)) x) = codeAt rep Lq.logLane x := by
          funext y
          simp only [novelEnc, codeAt]
          rw [slotFn_slotOf _ _ _ hx]
        rw [e]
    · rfl

/-! ### Free vectors -/

variable [CharP K 2]

theorem novel_deg (ℓ : ℕ) (hℓ : ℓ ≤ 64) (y : Fin (2 ^ ℓ)) :
    (novel rep.w.v ℓ y).natDegree = y ∧ novel rep.w.v ℓ y ≠ 0 :=
  novel_natDegree rep.w hℓ y.isLt

/-- An unopened position's vector. -/
theorem free_one {ℓ q : ℕ} (hℓ8 : 8 ≤ ℓ) (hℓ : ℓ ≤ 63) (pos : Fin q → ℕ)
    (hpos : ∀ i, pos i < 2 ^ 64) (hinj : Function.Injective pos) (hq : q < 247) (x : ℕ)
    (hx : x < 2 ^ 64) (hxQ : ∀ i, pos i ≠ x) :
    ∃ u, FreeVec (firstFree ℓ) (novelEnc rep.w ℓ pos) u ∧ ∑ y, codeAt rep ℓ x y * u y = 1 := by
  have hm : 247 ≤ 2 ^ ℓ :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hℓ8 : 2 ^ 8 ≤ 2 ^ ℓ)
  have hpt : Function.Injective fun i => rep.w.word (pos i) := fun i j h =>
    hinj (rep.w.word_inj _ _ (hpos i) (hpos j) h)
  obtain ⟨u, hu, hu0, hu1⟩ := exists_unopened_vector (m := 247) hm (fun y : Fin (2 ^ ℓ) =>
    novel rep.w.v ℓ y) (fun y => (novel_deg rep ℓ (by omega) y).1)
    (fun y => (novel_deg rep ℓ (by omega) y).2) _ hpt (by simpa using hq) (rep.w.word x)
    (fun i h => hxQ i (rep.w.word_inj _ _ (hpos i) hx h))
  refine ⟨u, ⟨fun y hy => hu y (by simpa [firstFree] using hy), hu0⟩, hu1⟩

/-- Two unopened positions' vector: `1` at the first, `0` at the second. -/
theorem free_two {ℓ q : ℕ} (hℓ8 : 8 ≤ ℓ) (hℓ : ℓ ≤ 63) (pos : Fin q → ℕ)
    (hpos : ∀ i, pos i < 2 ^ 64) (hinj : Function.Injective pos) (hq : q + 2 ≤ 247) (x x' : ℕ)
    (hx : x < 2 ^ 64) (hx' : x' < 2 ^ 64) (hxQ : ∀ i, pos i ≠ x) (hxQ' : ∀ i, pos i ≠ x')
    (hxx : x ≠ x') :
    ∃ u, FreeVec (firstFree ℓ) (novelEnc rep.w ℓ pos) u ∧ ∑ y, codeAt rep ℓ x y * u y = 1 ∧
      ∑ y, codeAt rep ℓ x' y * u y = 0 := by
  classical
  have hm : 247 ≤ 2 ^ ℓ :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hℓ8 : 2 ^ 8 ≤ 2 ^ ℓ)
  set pt' : Option (Option (Fin q)) → K := fun o =>
    o.elim (rep.w.word x) fun o' => o'.elim (rep.w.word x') fun i => rep.w.word (pos i)
  have hw : ∀ a b, a < 2 ^ 64 → b < 2 ^ 64 → a ≠ b → rep.w.word a ≠ rep.w.word b :=
    fun a b ha hb hab h => hab (rep.w.word_inj _ _ ha hb h)
  have hpt' : Function.Injective pt' := by
    intro o o' h
    rcases o with _ | _ | i <;> rcases o' with _ | _ | j <;> simp only [pt', Option.elim] at h
    · rfl
    · exact absurd h (hw _ _ hx hx' hxx)
    · exact absurd h (hw _ _ hx (hpos j) (fun e => hxQ j e.symm))
    · exact absurd h.symm (hw _ _ hx hx' hxx)
    · rfl
    · exact absurd h (hw _ _ hx' (hpos j) (fun e => hxQ' j e.symm))
    · exact absurd h (hw _ _ (hpos i) hx (hxQ i))
    · exact absurd h (hw _ _ (hpos i) hx' (hxQ' i))
    · rw [hinj (rep.w.word_inj _ _ (hpos i) (hpos j) h)]
  have hQ' : Fintype.card (Option (Option (Fin q))) ≤ 247 := by
    simp only [Fintype.card_option, Fintype.card_fin]; omega
  obtain ⟨z, hz⟩ := firstEval_surjective_of_degrees hm (fun y : Fin (2 ^ ℓ) => novel rep.w.v ℓ y)
    (fun y => (novel_deg rep ℓ (by omega) y).1) (fun y => (novel_deg rep ℓ (by omega) y).2) pt'
    hpt' hQ' (fun o => o.elim 1 fun _ => 0)
  set u : Fin (2 ^ ℓ) → K := fun y => if (y : ℕ) < 247 then z y else 0
  have hsum : ∀ o, ∑ y : Fin (2 ^ ℓ), (novel rep.w.v ℓ y).eval (pt' o) * u y =
      o.elim 1 fun _ => 0 := by
    intro o
    rw [← congrFun hz o]
    show _ = ∑ y ∈ Finset.univ.filter fun y : Fin (2 ^ ℓ) => (y : ℕ) < 247,
      (novel rep.w.v ℓ y).eval (pt' o) * z y
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [u]
    split_ifs <;> simp
  refine ⟨u, ⟨fun y hy => ?_, fun i => ?_⟩, ?_, ?_⟩
  · simp only [firstFree, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp [u, hy]
  · simpa [pt', novelEnc] using hsum (some (some i))
  · simpa [pt', codeAt] using hsum none
  · simpa [pt', codeAt] using hsum (some none)

/-! ### The link -/

variable [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K] [SampleableType E]

theorem slotFn_lt64 {b q : ℕ} (ds : List Limbs) (hq : 2 * q + 1 ≤ 2 ^ b) (hb : b ≤ 64) (i : Fin q) :
    slotFn b q ds i < 2 ^ 64 :=
  lt_of_lt_of_le (slotFn_lt ds hq i) (Nat.pow_le_pow_right (by norm_num) hb)

theorem pos_lt64 (x : Pos) : (x : ℕ) < 2 ^ 64 := lt_trans x.isLt (by norm_num)

theorem slotFn_ne {b q : ℕ} (ds : List Limbs) {x : ℕ} (hx : x ∉ slotsOf b q ds) (i : Fin q) :
    slotFn b q ds i ≠ x := fun h => hx (h ▸ slotFn_mem b q ds i)

theorem notW_of_opened {R : Renderer K E} {σ : List Out} {x : Pos}
    (h : (DRpm.ofBytes (Pb rep P₀ gK van stmt Y TW TQ R)).opened σ 0 x = false) :
    (x : ℕ) ∉ slotsW (chOf rep.limbs σ) := by
  rw [ofBytes_opened, Pb_opened, PbOpened_zero] at h
  exact of_decide_eq_false h

theorem notQ_of_opened {R : Renderer K E} {σ : List Out} {x : Pos}
    (h : (DRpm.ofBytes (Pb rep P₀ gK van stmt Y TW TQ R)).opened σ 1 x = false) :
    (x : ℕ) ∉ slotsQ (chOf rep.limbs σ) := by
  rw [ofBytes_opened, Pb_opened, PbOpened_one] at h
  exact of_decide_eq_false h

/-- **The deployed prover is the joint model `modelV`.** -/
noncomputable def link (R : Renderer K E) :
    LinkV (DRpm.ofBytes (Pb rep P₀ gK van stmt Y TW TQ R)) P₀ gK van (fun _ => ())
      (T₁ TW) (T₂ TQ) (openW rep Y) (openQ rep P₀ Y) where
  chOf := chOf rep.limbs
  out := out rep P₀ gK van stmt Y TW TQ R
  hview s σ := view_eq rep P₀ gK van stmt Y TW TQ R s σ
  enc₁ row := .inl (rowBytes rep row)
  enc₂ row := .inl (rowBytes rep row)
  inj₁ _ _ h := rowBytes_injective rep (Sum.inl_injective h)
  inj₂ _ _ h := rowBytes_injective rep (Sum.inl_injective h)
  code₁ _ x := codeAt rep Lw.logLane x
  code₂ _ x := codeAt rep Lq.logLane x
  rows₁ s σ x _ := by
    show Sum.inl ((Pb rep P₀ gK van stmt Y TW TQ R).rowFn s
      (σ.take ((Pb rep P₀ gK van stmt Y TW TQ R).cK 0)) 0 x) = _
    rw [Pb_rowFn, PbRow_zero, stackV₁_eq, stackV₁_eq]
  rows₂ s σ x _ := by
    show Sum.inl ((Pb rep P₀ gK van stmt Y TW TQ R).rowFn s
      (σ.take ((Pb rep P₀ gK van stmt Y TW TQ R).cK 1)) 1 x) = _
    rw [Pb_rowFn, Pb_cK, PbcK_one, PbRow_one, stackV₂_eq, stackV₂_eq,
      chOf_take_abc rep.limbs σ le_rfl]
  free₁ σ x hx := by
    have hx' : (x : ℕ) ∉ slotsW (chOf rep.limbs σ) := notW_of_opened rep P₀ gK van stmt Y TW TQ hx
    obtain ⟨u, hu, h1⟩ := free_one rep (ℓ := Lw.logLane) (by rw [logLane_W]; norm_num)
      (by rw [logLane_W]; norm_num) _ (slotFn_lt64 _ (by norm_num) (by norm_num))
      (slotFn_injective _ _ _) (by norm_num) x (pos_lt64 x) (slotFn_ne _ hx')
    exact ⟨u, fun _ => hu, h1⟩
  free₁₂ σ x x' hx hx' hxx := by
    have h1 : (x : ℕ) ∉ slotsW (chOf rep.limbs σ) := notW_of_opened rep P₀ gK van stmt Y TW TQ hx
    have h2 : (x' : ℕ) ∉ slotsW (chOf rep.limbs σ) := (notW_of_opened rep P₀ gK van stmt Y TW TQ hx')
    obtain ⟨u, hu, e1, e2⟩ := free_two rep (ℓ := Lw.logLane) (by rw [logLane_W]; norm_num)
      (by rw [logLane_W]; norm_num) _ (slotFn_lt64 _ (by norm_num) (by norm_num))
      (slotFn_injective _ _ _) (by norm_num) x x' (pos_lt64 x) (pos_lt64 x') (slotFn_ne _ h1)
      (slotFn_ne _ h2) (fun h => hxx (Fin.ext h))
    exact ⟨u, fun _ => hu, e1, e2⟩
  free₂ σ x hx := by
    have hx' : (x : ℕ) ∉ slotsQ (chOf rep.limbs σ) := notQ_of_opened rep P₀ gK van stmt Y TW TQ hx
    obtain ⟨u, hu, h1⟩ := free_one rep (ℓ := Lq.logLane) (by rw [logLane_Q]; norm_num)
      (by rw [logLane_Q]; norm_num) _ (slotFn_lt64 _ (by norm_num) (by norm_num))
      (slotFn_injective _ _ _) (by norm_num) x (pos_lt64 x) (slotFn_ne _ hx')
    exact ⟨u, fun _ => hu, h1⟩
  free₂₂ σ x x' hx hx' hxx := by
    have h1 : (x : ℕ) ∉ slotsQ (chOf rep.limbs σ) := notQ_of_opened rep P₀ gK van stmt Y TW TQ hx
    have h2 : (x' : ℕ) ∉ slotsQ (chOf rep.limbs σ) := notQ_of_opened rep P₀ gK van stmt Y TW TQ hx'
    obtain ⟨u, hu, e1, e2⟩ := free_two rep (ℓ := Lq.logLane) (by rw [logLane_Q]; norm_num)
      (by rw [logLane_Q]; norm_num) _ (slotFn_lt64 _ (by norm_num) (by norm_num))
      (slotFn_injective _ _ _) (by norm_num) x x' (pos_lt64 x) (pos_lt64 x') (slotFn_ne _ h1)
      (slotFn_ne _ h2) (fun h => hxx (Fin.ext h))
    exact ⟨u, fun _ => hu, e1, e2⟩

end Prover

end QuotientZk.Instance
