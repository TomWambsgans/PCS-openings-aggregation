-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): `common`'s duplex discipline (`Common.Duplex`, `Common.Admissible`) and its
-- lanes lemmas (`LeanVM.Rpm.keccakNF_of_keep`, `LeanVM.Rpm.toRpm_zero`).
import QuotientZk.RpmJoint

/-!
# The deployed prover follows the duplex discipline; its rows are byte strings

`zk_rpm_deployed`, `zk_rpm_deployed_bits` and `zk_rpm_deployed_joint` (`RpmJoint.lean`) assume two
facts about the deployed prover that this file proves.

* **`hduplex`** (`DuplexDiscipline P (Deployed.skel sh)`): every call of `F` the prover makes absorbs
  a non-final block into the zero state or into an earlier answer of `F`, keeping the capacity
  (`Common.Duplex`). On the skeleton (`Deployed.Disc`): `Wp` is the weakest precondition of the
  discipline on lanes (a permutation call's input keeps lanes `16 .. 24` of the zero state or of an
  earlier answer, `AdmL`), with its bind law; the Merkle trees, the reduction's chain and the
  messages make no permutation call (`Silent`); the duplex's state (`Dx.st`) is always an earlier
  answer (the seed, a draw, a fifth absorbed scalar, a grinding try), and its input keeps lanes
  `16 .. 24` of it (`keeps_input`; the seed's input is zero there, `keeps_seedInput`); so every
  opening, and the skeleton, is disciplined for **every shape** (`ok_opening`, `ok_skel`; the
  deployed shape is not unfolded, so its `2^20`-leaf ranges are never evaluated). On the prover
  (`dw_implHF`): run by the two-oracle prover, a skeleton disciplined on lanes is disciplined on
  bytes, a lane input keeping lanes `16 .. 24` being a byte state keeping the capacity and byte
  `135` (`LeanVM.Rpm.keccakNF_of_keep`), when the leaf rows are byte strings (a leaf is then a
  Keccak-256 query, not a call of `F`). **`duplexDiscipline_skel`**.
* **`hrow`**: the deployed prover hashes a leaf's bytes; a prover with byte rows is `ofBytes Pb`
  for `Pb : Proto _ (List UInt8) _ _ _ _` (`rowFn_ofBytes`), and every prover satisfying `hrow` is
  one (`exists_ofBytes`).

**`zk_rpm_deployed_bits'`**, **`zk_rpm_deployed_joint'`**: the end statements for `ofBytes Pb`,
without `hrow` and `hduplex`.
-/

open OracleComp OracleSpec
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec Proof)
open scoped ENNReal

namespace QuotientZk.Deployed.Disc

set_option linter.unusedSectionVars false

/-! ## The discipline on lanes, on the skeleton -/

/-- Lanes `16 .. 24` of `x` (the last rate lane and the capacity) are those of `z`. -/
def Keeps (x z : KSt) : Prop := ∀ i : Fin 25, 16 ≤ i.val → x[i] = z[i]

/-- A permutation input admissible after the answers `H`: it keeps lanes `16 .. 24` of the zero
state or of an earlier answer. -/
def AdmL (H : List KSt) (x : KSt) : Prop :=
  Keeps x (Vector.replicate 25 0) ∨ ∃ z ∈ H, Keeps x z

/-- **The weakest precondition of the discipline** on the skeleton's operations: every permutation
call (`pub` or `chal` of a state) admissible after the answers so far (`H`, newest first), and `Q`
of the result and the answers at the end. -/
def Wp {α : Type} : OracleComp DSpec α → List KSt → (α → List KSt → Prop) → Prop
  | .pure a, H, Q => Q a H
  | .liftBind (.pub (.inr x)) k, H, Q => AdmL H x ∧ ∀ u, Wp (k u) ((u : Out).2 :: H) Q
  | .liftBind (.chal (.inr x)) k, H, Q => AdmL H x ∧ ∀ u, Wp (k u) ((u : Out).2 :: H) Q
  | .liftBind _ k, H, Q => ∀ u, Wp (k u) H Q

section Calculus

variable {α β : Type}

theorem wp_pure (a : α) (H : List KSt) (Q : α → List KSt → Prop) :
    Wp (pure a : OracleComp DSpec α) H Q ↔ Q a H := Iff.rfl

theorem wp_query_pubF (x : KSt) (k : Out → OracleComp DSpec α) (H : List KSt)
    (Q : α → List KSt → Prop) :
    Wp (liftM (DSpec.query (.pub (.inr x))) >>= k) H Q ↔ AdmL H x ∧ ∀ u : Out, Wp (k u) (u.2 :: H) Q :=
  Iff.rfl

theorem wp_query_chalF (x : KSt) (k : Out → OracleComp DSpec α) (H : List KSt)
    (Q : α → List KSt → Prop) :
    Wp (liftM (DSpec.query (.chal (.inr x))) >>= k) H Q ↔ AdmL H x ∧ ∀ u : Out, Wp (k u) (u.2 :: H) Q :=
  Iff.rfl

theorem wp_query_other (op : Op Inp Tbl Pos) (h₁ : ∀ x, op ≠ .pub (.inr x))
    (h₂ : ∀ x, op ≠ .chal (.inr x)) (k : DSpec.Range op → OracleComp DSpec α) (H : List KSt)
    (Q : α → List KSt → Prop) :
    Wp (liftM (DSpec.query op) >>= k) H Q ↔ ∀ u, Wp (k u) H Q := by
  rcases op with (m | x) | _ | ⟨t, x⟩ | (m | x)
  · exact Iff.rfl
  · exact absurd rfl (h₁ x)
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · exact absurd rfl (h₂ x)

/-- **The bind law.** -/
theorem wp_bind (oa : OracleComp DSpec α) (f : α → OracleComp DSpec β) :
    ∀ (H : List KSt) (Q : β → List KSt → Prop),
      Wp (oa >>= f) H Q ↔ Wp oa H (fun a H' ↦ Wp (f a) H' Q) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro H Q; rw [pure_bind]; rfl
  | query_bind op k ih =>
    intro H Q
    rw [bind_assoc]
    rcases op with (m | x) | _ | ⟨t, x⟩ | (m | x)
    · rw [wp_query_other _ (by simp) (by simp), wp_query_other _ (by simp) (by simp)]
      exact forall_congr' fun u ↦ ih u H Q
    · rw [wp_query_pubF, wp_query_pubF]
      exact and_congr Iff.rfl (forall_congr' fun u ↦ ih u _ Q)
    · rw [wp_query_other _ (by simp) (by simp), wp_query_other _ (by simp) (by simp)]
      exact forall_congr' fun u ↦ ih u H Q
    · rw [wp_query_other _ (by simp) (by simp), wp_query_other _ (by simp) (by simp)]
      exact forall_congr' fun u ↦ ih u H Q
    · rw [wp_query_other _ (by simp) (by simp), wp_query_other _ (by simp) (by simp)]
      exact forall_congr' fun u ↦ ih u H Q
    · rw [wp_query_chalF, wp_query_chalF]
      exact and_congr Iff.rfl (forall_congr' fun u ↦ ih u _ Q)

theorem wp_bind_of {oa : OracleComp DSpec α} {f : α → OracleComp DSpec β} {H : List KSt}
    {Q : β → List KSt → Prop} (h : Wp oa H (fun a H' ↦ Wp (f a) H' Q)) : Wp (oa >>= f) H Q :=
  (wp_bind oa f H Q).2 h

theorem wp_mono (oa : OracleComp DSpec α) :
    ∀ (H : List KSt) (Q Q' : α → List KSt → Prop), Wp oa H Q → (∀ a H', Q a H' → Q' a H') →
      Wp oa H Q' := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro H Q Q' h hQ; exact hQ a H h
  | query_bind op k ih =>
    intro H Q Q' h hQ
    rcases op with (m | x) | _ | ⟨t, x⟩ | (m | x)
    · rw [wp_query_other _ (by simp) (by simp)] at h ⊢
      exact fun u ↦ ih u H Q Q' (h u) hQ
    · rw [wp_query_pubF] at h ⊢
      exact ⟨h.1, fun u ↦ ih u _ Q Q' (h.2 u) hQ⟩
    · rw [wp_query_other _ (by simp) (by simp)] at h ⊢
      exact fun u ↦ ih u H Q Q' (h u) hQ
    · rw [wp_query_other _ (by simp) (by simp)] at h ⊢
      exact fun u ↦ ih u H Q Q' (h u) hQ
    · rw [wp_query_other _ (by simp) (by simp)] at h ⊢
      exact fun u ↦ ih u H Q Q' (h u) hQ
    · rw [wp_query_chalF] at h ⊢
      exact ⟨h.1, fun u ↦ ih u _ Q Q' (h.2 u) hQ⟩

/-- **A disciplined computation**: from any answers `H`, every postcondition holding of every
result and answers holds. -/
def Ok (oa : OracleComp DSpec α) : Prop :=
  ∀ (H : List KSt) (Q : α → List KSt → Prop), (∀ a H', Q a H') → Wp oa H Q

/-- **A silent computation** (no permutation call): every postcondition holding of every result at
`H` holds. -/
def Silent (oa : OracleComp DSpec α) : Prop :=
  ∀ (H : List KSt) (Q : α → List KSt → Prop), (∀ a, Q a H) → Wp oa H Q

theorem Silent.ok {oa : OracleComp DSpec α} (h : Silent oa) : Ok oa :=
  fun H Q hQ ↦ h H Q fun a ↦ hQ a H

theorem silent_pure (a : α) : Silent (pure a : OracleComp DSpec α) := fun _ _ h ↦ h a

theorem Silent.bind {oa : OracleComp DSpec α} {f : α → OracleComp DSpec β} (h : Silent oa)
    (hf : ∀ a, Silent (f a)) : Silent (oa >>= f) :=
  fun H Q hQ ↦ wp_bind_of (h H _ fun a ↦ hf a H Q hQ)

theorem Ok.bind {oa : OracleComp DSpec α} {f : α → OracleComp DSpec β} (h : Ok oa)
    (hf : ∀ a, Ok (f a)) : Ok (oa >>= f) :=
  fun H Q hQ ↦ wp_bind_of (h H _ fun a H' ↦ hf a H' Q hQ)

theorem silent_map {oa : OracleComp DSpec α} (f : α → β) (h : Silent oa) : Silent (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact h.bind fun a ↦ silent_pure _

theorem silent_mapM {γ : Type} (f : γ → OracleComp DSpec α) (hf : ∀ c, Silent (f c)) :
    ∀ l : List γ, Silent (l.mapM f)
  | [] => by rw [List.mapM_nil]; exact silent_pure _
  | c :: l => by
    rw [List.mapM_cons]
    exact (hf c).bind fun a ↦ (silent_mapM f hf l).bind fun _ ↦ silent_pure _

end Calculus

/-! ## The operations -/

section Ops

variable {α : Type}

theorem wp_hashH (m : List UInt8) (H : List KSt) (Q : QuotientRpm.Bytes32 → List KSt → Prop) :
    Wp (hashH m) H Q ↔ ∀ a : Out, Q a.1 H := Iff.rfl

theorem wp_chalH (m : List UInt8) (H : List KSt) (Q : QuotientRpm.Bytes32 → List KSt → Prop) :
    Wp (chalH m) H Q ↔ ∀ a : Out, Q a.1 H := Iff.rfl

theorem wp_perm (x : KSt) (H : List KSt) (Q : KSt → List KSt → Prop) :
    Wp (perm x) H Q ↔ AdmL H x ∧ ∀ a : Out, Q a.2 (a.2 :: H) := Iff.rfl

theorem wp_chalF (x : KSt) (H : List KSt) (Q : KSt → List KSt → Prop) :
    Wp (chalF x) H Q ↔ AdmL H x ∧ ∀ a : Out, Q a.2 (a.2 :: H) := Iff.rfl

theorem silent_hashH (m : List UInt8) : Silent (hashH m) := fun _ _ h a ↦ h a.1

theorem silent_chalH (m : List UInt8) : Silent (chalH m) := fun _ _ h a ↦ h a.1

theorem silent_leafH (k : Tbl) (x : ℕ) : Silent (leafH k x) := fun _ _ h a ↦ h a.1

theorem silent_getMsg : Silent getMsg := fun _ _ h m ↦ h m

theorem silent_levelUp : ∀ l : List QuotientRpm.Bytes32, Silent (levelUp l)
  | a :: b :: rest => by
    rw [levelUp]
    exact (silent_hashH _).bind fun h ↦ (silent_levelUp rest).bind fun t ↦ silent_pure _
  | [] => silent_pure (α := List QuotientRpm.Bytes32) []
  | [_] => silent_pure (α := List QuotientRpm.Bytes32) []

theorem silent_levels : ∀ (d : ℕ) (l : List QuotientRpm.Bytes32), Silent (levels d l)
  | 0, l => by rw [levels]; exact silent_pure _
  | d + 1, l => by
    rw [levels]
    exact (silent_levelUp l).bind fun up ↦ (silent_levels d up).bind fun _ ↦ silent_pure _

theorem silent_tree₀ (sh : OpenShape) : Silent (tree₀ sh) := by
  unfold tree₀
  dsimp only
  split
  · exact (silent_mapM _ (fun x ↦ silent_leafH _ x) _).bind fun _ ↦ silent_levels _ _
  · exact (silent_mapM _ silent_hashH _).bind fun _ ↦ silent_levels _ _

end Ops

/-! ## The duplex: its state is always an earlier answer -/

section Duplex

theorem sub_cons (a : KSt) (H : List KSt) : H ⊆ a :: H := fun _ h ↦ List.mem_cons_of_mem _ h

theorem mem_cons (a : KSt) (H : List KSt) : a ∈ a :: H := List.mem_cons.2 (Or.inl rfl)

/-- The permutation's input keeps lanes `16 .. 24` of the duplex's state. -/
theorem keeps_input (d : Dx) : Keeps d.input d.st := by
  intro i hi
  have h : ¬ (i : ℕ) < 16 := by omega
  simp only [Dx.input, Fin.getElem_fin, Vector.getElem_ofFn, h, ↓reduceIte]

theorem admL_input {H : List KSt} {d : Dx} (hd : d.st ∈ H) : AdmL H d.input :=
  Or.inr ⟨d.st, hd, keeps_input d⟩

/-- The seed's input is zero in lanes `4 .. 24`. -/
theorem keeps_seedInput (iv : QuotientRpm.Bytes32) :
    Keeps (seedInput iv) (Vector.replicate 25 0) := by
  intro i hi
  have h : ¬ (i : ℕ) < 4 := by omega
  simp only [seedInput, Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_replicate, h,
    ↓reduceIte]

theorem wp_absorb (d : Dx) (x : QuotientRpm.Limbs) (tag : UInt64) {H : List KSt}
    {Q : Dx → List KSt → Prop} (hd : d.st ∈ H) (hQ : ∀ d' H', H ⊆ H' → d'.st ∈ H' → Q d' H') :
    Wp (d.absorb x tag) H Q := by
  unfold Dx.absorb
  split
  · refine wp_bind_of ((wp_perm _ _ _).2 ⟨admL_input hd, fun a ↦ ?_⟩)
    exact hQ _ _ (sub_cons _ _) (mem_cons _ _)
  · exact hQ _ _ (List.Subset.refl _) hd

theorem wp_absorbAll : ∀ (xs : List QuotientRpm.Limbs) (d : Dx) {H : List KSt}
    {Q : Dx → List KSt → Prop}, d.st ∈ H → (∀ d' H', H ⊆ H' → d'.st ∈ H' → Q d' H') →
    Wp (d.absorbAll xs) H Q
  | [], d, H, _, hd, hQ => hQ d H (List.Subset.refl _) hd
  | x :: xs, d, _, Q, hd, hQ => by
    rw [Dx.absorbAll]
    refine wp_bind_of (wp_absorb d x _ hd fun d' H' h₁ h₂ ↦ ?_)
    exact wp_absorbAll xs d' h₂ fun d'' H'' h₃ h₄ ↦ hQ d'' H'' (List.Subset.trans h₁ h₃) h₄

theorem wp_draw (d : Dx) {H : List KSt} {Q : QuotientRpm.Limbs × Dx → List KSt → Prop}
    (hd : d.st ∈ H) (hQ : ∀ c d' H', H ⊆ H' → d'.st ∈ H' → Q (c, d') H') : Wp d.draw H Q := by
  unfold Dx.draw
  refine wp_bind_of ((wp_chalF _ _ _).2 ⟨admL_input hd, fun _ ↦ ?_⟩)
  exact hQ _ _ _ (sub_cons _ _) (mem_cons _ _)

theorem wp_seed (iv : QuotientRpm.Bytes32) {H : List KSt} {Q : Dx → List KSt → Prop}
    (hQ : ∀ d' H', H ⊆ H' → d'.st ∈ H' → Q d' H') : Wp (seed iv) H Q := by
  unfold seed
  refine wp_bind_of ((wp_perm _ _ _).2 ⟨Or.inl (keeps_seedInput iv), fun _ ↦ ?_⟩)
  exact hQ _ _ (sub_cons _ _) (mem_cons _ _)

theorem wp_tryNonce (d : Dx) (n : UInt64) {H : List KSt} {Q : Bool × Dx → List KSt → Prop}
    (hd : d.st ∈ H) (hQ : ∀ b d' H', H ⊆ H' → d'.st ∈ H' → Q (b, d') H') :
    Wp (tryNonce d n) H Q := by
  unfold tryNonce
  refine wp_bind_of (wp_absorb d _ _ hd fun d₁ H₁ h₁ h₂ ↦ ?_)
  refine wp_bind_of ((wp_perm _ _ _).2 ⟨admL_input h₂, fun _ ↦ ?_⟩)
  exact hQ _ _ _ (List.Subset.trans h₁ (sub_cons _ _)) (mem_cons _ _)

theorem wp_grind (d : Dx) : ∀ (fuel : ℕ) (n : UInt64) {H : List KSt}
    {Q : UInt64 × Dx → List KSt → Prop}, d.st ∈ H →
    (∀ m d' H', H ⊆ H' → d'.st ∈ H' → Q (m, d') H') → Wp (grind d fuel n) H Q
  | 0, n, H, _, hd, hQ => hQ n d H (List.Subset.refl _) hd
  | fuel + 1, n, _, Q, hd, hQ => by
    rw [grind]
    refine wp_bind_of (wp_tryNonce d n hd fun b d' H' h₁ h₂ ↦ ?_)
    cases b
    · exact wp_grind d fuel (n + 1) (h₁ hd) fun m d'' H'' h₃ h₄ ↦
        hQ m d'' H'' (List.Subset.trans h₁ h₃) h₄
    · exact hQ n d' H' h₁ h₂

theorem wp_sendK (o : OSt) (k : ℕ) {H : List KSt} {Q : OSt → List KSt → Prop}
    (hd : o.dx.st ∈ H) (hQ : ∀ o' H', H ⊆ H' → o'.dx.st ∈ H' → Q o' H') :
    Wp (sendK o k) H Q := by
  unfold sendK
  split
  refine wp_bind_of (wp_absorbAll _ _ hd fun _ H' h₁ h₂ ↦ ?_)
  exact hQ _ H' h₁ h₂

theorem wp_drawO (o : OSt) {H : List KSt} {Q : QuotientRpm.Limbs × OSt → List KSt → Prop}
    (hd : o.dx.st ∈ H) (hQ : ∀ c o' H', H ⊆ H' → o'.dx.st ∈ H' → Q (c, o') H') :
    Wp (drawO o) H Q := by
  unfold drawO
  refine wp_bind_of (wp_draw _ hd fun _ _ H' h₁ h₂ ↦ ?_)
  refine wp_bind_of (silent_getMsg H' _ fun _ ↦ ?_)
  exact hQ _ _ H' h₁ h₂

theorem wp_rounds : ∀ (o : OSt) (k : ℕ) {H : List KSt} {Q : OSt → List KSt → Prop},
    o.dx.st ∈ H → (∀ o' H', H ⊆ H' → o'.dx.st ∈ H' → Q o' H') → Wp (rounds o k) H Q
  | o, 0, H, _, hd, hQ => hQ o H (List.Subset.refl _) hd
  | o, k + 1, _, Q, hd, hQ => by
    rw [rounds]
    refine wp_bind_of (wp_drawO o hd fun _ o₁ _ h₁ h₂ ↦ ?_)
    refine wp_bind_of (wp_sendK o₁ 2 h₂ fun o₂ _ h₃ h₄ ↦ ?_)
    exact wp_rounds o₂ k h₄ fun o₃ H₃ h₅ h₆ ↦
      hQ o₃ H₃ (List.Subset.trans h₁ (List.Subset.trans h₃ h₅)) h₆

theorem wp_drawMany : ∀ (o : OSt) (m : ℕ) {H : List KSt}
    {Q : List QuotientRpm.Limbs × OSt → List KSt → Prop}, o.dx.st ∈ H →
    (∀ cs o' H', H ⊆ H' → o'.dx.st ∈ H' → Q (cs, o') H') → Wp (drawMany o m) H Q
  | o, 0, H, _, hd, hQ => hQ [] o H (List.Subset.refl _) hd
  | o, m + 1, _, Q, hd, hQ => by
    rw [drawMany]
    refine wp_bind_of (wp_drawO o hd fun c o₁ _ h₁ h₂ ↦ ?_)
    refine wp_bind_of (wp_drawMany o₁ m h₂ fun cs o₂ H₂ h₃ h₄ ↦ ?_)
    exact hQ (c :: cs) o₂ H₂ (List.Subset.trans h₁ h₃) h₄

theorem wp_commitNext (o : OSt) (depth : ℕ) {H : List KSt} {Q : OSt → List KSt → Prop}
    (hd : o.dx.st ∈ H) (hQ : ∀ o' H', H ⊆ H' → o'.dx.st ∈ H' → Q o' H') :
    Wp (commitNext o depth) H Q := by
  unfold commitNext
  split
  refine wp_bind_of (silent_mapM _ (fun _ ↦ silent_hashH _) _ H _ fun leaves ↦ ?_)
  refine wp_bind_of (silent_levels _ _ H _ fun lv ↦ ?_)
  refine wp_bind_of (wp_absorbAll _ _ hd fun _ H' h₁ h₂ ↦ ?_)
  exact hQ _ H' h₁ h₂

theorem wp_ood (o : OSt) (m : ℕ) {H : List KSt} {Q : OSt → List KSt → Prop}
    (hd : o.dx.st ∈ H) (hQ : ∀ o' H', H ⊆ H' → o'.dx.st ∈ H' → Q o' H') :
    Wp (ood o m) H Q := by
  unfold ood
  refine wp_bind_of (wp_drawMany o m hd fun _ o₁ _ h₁ h₂ ↦ ?_)
  exact wp_sendK o₁ 3 h₂ fun o₂ H₂ h₃ h₄ ↦ hQ o₂ H₂ (List.Subset.trans h₁ h₃) h₄

theorem wp_queryPhase (o : OSt) (lvl q : ℕ) {H : List KSt} {Q : OSt → List KSt → Prop}
    (hd : o.dx.st ∈ H) (hQ : ∀ o' H', H ⊆ H' → o'.dx.st ∈ H' → Q o' H') :
    Wp (queryPhase o lvl q) H Q := by
  unfold queryPhase
  refine wp_bind_of (wp_grind _ _ _ hd fun nonce d₁ H₁ h₁ h₂ ↦ ?_)
  refine wp_bind_of (wp_drawMany _ _ h₂ fun cs o₂ H₂ h₃ h₄ ↦ ?_)
  refine wp_bind_of (wp_drawO _ h₄ fun _ o₃ H₃ h₅ h₆ ↦ ?_)
  exact wp_sendK _ 2 h₆ fun o₄ H₄ h₇ h₈ ↦
    hQ o₄ H₄ (List.Subset.trans h₁ (List.Subset.trans h₃ (List.Subset.trans h₅ h₇))) h₈

theorem wp_middle : ∀ (o : OSt) (lvl : ℕ) (ls : List (ℕ × ℕ × ℕ)) (qs : List ℕ) {H : List KSt}
    {Q : OSt → List KSt → Prop}, o.dx.st ∈ H →
    (∀ o' H', H ⊆ H' → o'.dx.st ∈ H' → Q o' H') → Wp (middle o lvl ls qs) H Q
  | o, lvl, [], qs, H, _, hd, hQ => by
    rw [middle]; exact hQ o H (List.Subset.refl _) hd
  | o, lvl, ⟨folds, depth, oodN⟩ :: rest, q :: qs, _, Q, hd, hQ => by
    rw [middle]
    refine wp_bind_of (wp_rounds o folds hd fun o₁ _ h₁ h₂ ↦ ?_)
    refine wp_bind_of (wp_commitNext o₁ depth h₂ fun o₂ _ h₃ h₄ ↦ ?_)
    refine wp_bind_of (wp_ood o₂ oodN h₄ fun o₃ _ h₅ h₆ ↦ ?_)
    refine wp_bind_of (wp_queryPhase o₃ lvl q h₆ fun o₄ _ h₇ h₈ ↦ ?_)
    exact wp_middle o₄ (lvl + 1) rest qs h₈ fun o₅ H₅ h₉ h₁₀ ↦
      hQ o₅ H₅ (List.Subset.trans h₁ (List.Subset.trans h₃ (List.Subset.trans h₅
        (List.Subset.trans h₇ h₉)))) h₁₀
  | o, lvl, ⟨folds, depth, oodN⟩ :: rest, [], H, _, hd, hQ => by
    rw [middle]; exact hQ o H (List.Subset.refl _) hd

/-- **An opening is disciplined**: its seed is a permutation of an input zero in lanes `4 .. 24`,
and every later permutation call absorbs into the duplex's state, an earlier answer. -/
theorem ok_opening (sh : OpenShape) (lv₀ : List (List QuotientRpm.Bytes32)) :
    Ok (opening sh lv₀) := by
  intro H Q hQ
  unfold opening
  refine wp_bind_of (silent_getMsg H _ fun m ↦ ?_)
  split
  refine wp_bind_of (silent_hashH _ H _ fun iv ↦ ?_)
  refine wp_bind_of (wp_seed iv fun d₁ H₁ _ h₁ ↦ ?_)
  refine wp_bind_of (wp_absorbAll _ _ h₁ fun d₂ H₂ _ h₂ ↦ ?_)
  refine wp_bind_of (wp_drawO _ h₂ fun _ o₃ H₃ _ h₃ ↦ ?_)
  refine wp_bind_of (wp_sendK _ 2 h₃ fun o₄ H₄ _ h₄ ↦ ?_)
  refine wp_bind_of (wp_rounds _ 6 h₄ fun o₅ H₅ _ h₅ ↦ ?_)
  refine wp_bind_of (wp_commitNext _ _ h₅ fun o₆ H₆ _ h₆ ↦ ?_)
  refine wp_bind_of (wp_ood _ _ h₆ fun o₇ H₇ _ h₇ ↦ ?_)
  refine wp_bind_of (wp_queryPhase _ _ _ h₇ fun o₈ H₈ _ h₈ ↦ ?_)
  refine wp_bind_of (wp_middle _ _ _ _ h₈ fun o₉ H₉ _ h₉ ↦ ?_)
  refine wp_bind_of (wp_rounds _ _ h₉ fun o₁₀ H₁₀ _ h₁₀ ↦ ?_)
  refine wp_bind_of (wp_sendK _ _ h₁₀ fun o₁₁ H₁₁ _ h₁₁ ↦ ?_)
  refine wp_bind_of (wp_queryPhase _ _ _ h₁₁ fun o₁₂ H₁₂ _ h₁₂ ↦ ?_)
  refine wp_bind_of (wp_rounds _ _ h₁₂ fun o₁₃ H₁₃ _ h₁₃ ↦ ?_)
  refine wp_bind_of (wp_drawO _ h₁₃ fun _ _ _ _ _ ↦ ?_)
  exact hQ _ _

/-- **The deployed skeleton is disciplined**, for every shape. -/
theorem ok_skel (sh : Shape) : Ok (skel sh) := by
  unfold skel
  refine (silent_tree₀ _).ok.bind fun _ ↦ (silent_hashH _).ok.bind fun _ ↦
    (silent_chalH _).ok.bind fun _ ↦ (silent_chalH _).ok.bind fun _ ↦
    (silent_chalH _).ok.bind fun _ ↦ (silent_tree₀ _).ok.bind fun _ ↦
    (silent_chalH _).ok.bind fun _ ↦ silent_getMsg.ok.bind fun m ↦ ?_
  split
  exact (silent_chalH _).ok.bind fun _ ↦ (silent_tree₀ _).ok.bind fun _ ↦
    (ok_opening _ _).bind fun _ ↦ (ok_opening _ _).bind fun _ ↦ (ok_opening _ _).bind fun _ ↦
    (silent_pure _).ok

end Duplex

end QuotientZk.Deployed.Disc

/-! ## From the skeleton to the prover's calls of `F` -/

namespace QuotientZk.DRpm

open Common LeanVM.Rpm

set_option linter.unusedSectionVars false

section Transfer

/-- **The weakest precondition of `Common.Duplex`** for a computation with coins, `H` and `F`:
every direct call admissible after the answers so far, and `Q` at the end. -/
def DW {α : Type} : OracleComp (unifSpec + HF) α → List KState → (α → List KState → Prop) → Prop
  | .pure a, h, Q => Q a h
  | .liftBind (.inr (.inr x)) k, h, Q =>
      Admissible KState.zero keccakNF h x ∧ ∀ y, DW (k y) (y :: h) Q
  | .liftBind _ k, h, Q => ∀ u, DW (k u) h Q

variable {α β : Type}

theorem dw_query_coin (n : ℕ) (k : Fin (n + 1) → OracleComp (unifSpec + HF) α) (h : List KState)
    (Q : α → List KState → Prop) :
    DW (liftM ((unifSpec + HF).query (.inl n)) >>= k) h Q ↔ ∀ u, DW (k u) h Q := Iff.rfl

theorem dw_query_H (m : List UInt8) (k : DigestBytes → OracleComp (unifSpec + HF) α)
    (h : List KState) (Q : α → List KState → Prop) :
    DW (liftM ((unifSpec + HF).query (.inr (.inl m))) >>= k) h Q ↔ ∀ u, DW (k u) h Q := Iff.rfl

theorem dw_query_F (x : KState) (k : KState → OracleComp (unifSpec + HF) α) (h : List KState)
    (Q : α → List KState → Prop) :
    DW (liftM ((unifSpec + HF).query (.inr (.inr x))) >>= k) h Q ↔
      Admissible KState.zero keccakNF h x ∧ ∀ y, DW (k y) (y :: h) Q := Iff.rfl

theorem dw_bind (oa : OracleComp (unifSpec + HF) α) (f : α → OracleComp (unifSpec + HF) β) :
    ∀ (h : List KState) (Q : β → List KState → Prop),
      DW (oa >>= f) h Q ↔ DW oa h (fun a h' ↦ DW (f a) h' Q) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro h Q; rw [pure_bind]; rfl
  | query_bind t k ih =>
    intro h Q
    rw [bind_assoc]
    rcases t with n | m | x
    · rw [dw_query_coin, dw_query_coin]; exact forall_congr' fun u ↦ ih u h Q
    · rw [dw_query_H, dw_query_H]; exact forall_congr' fun u ↦ ih u h Q
    · rw [dw_query_F, dw_query_F]; exact and_congr Iff.rfl (forall_congr' fun u ↦ ih u _ Q)

theorem dw_map (f : α → β) (oa : OracleComp (unifSpec + HF) α) (h : List KState)
    (Q : β → List KState → Prop) : DW (f <$> oa) h Q ↔ DW oa h (fun a h' ↦ Q (f a) h') := by
  rw [map_eq_bind_pure_comp, dw_bind]
  rfl

/-- With the trivial postcondition, `DW` is the duplex discipline. -/
theorem duplex_of_dw (oa : OracleComp (unifSpec + HF) α) :
    ∀ h, DW oa h (fun _ _ ↦ True) → Duplex KState.zero keccakNF oa h := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro _ _; trivial
  | query_bind t k ih =>
    intro h hd
    rcases t with n | m | x
    · exact fun u ↦ ih u h (hd u)
    · exact fun u ↦ ih u h (hd u)
    · exact ⟨hd.1, fun y ↦ ih y _ (hd.2 y)⟩

/-- Coins make no direct call. -/
theorem dw_coins (p : ProbComp α) :
    ∀ (h : List KState) (Q : α → List KState → Prop), (∀ a, Q a h) →
      DW (liftM p : OracleComp (unifSpec + HF) α) h Q := by
  change ∀ h Q, (∀ a, Q a h) → DW (OracleComp.liftComp p _) h Q
  induction p using OracleComp.inductionOn with
  | pure a => intro h Q hQ; exact hQ a
  | query_bind n k ih =>
    intro h Q hQ
    rw [OracleComp.liftComp_bind, OracleComp.liftComp_query]
    simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
    change DW (liftM ((unifSpec + HF).query (.inl n)) >>= _) h Q
    exact fun u ↦ ih u h Q hQ

theorem dw_coin2 (γ : Type) [SampleableType γ] (h : List KState) (Q : γ → List KState → Prop)
    (hQ : ∀ a, Q a h) : DW (coin2 γ) h Q :=
  dw_coins _ h Q hQ

theorem dw_hH2 (m : List UInt8) (h : List KState) (Q : DigestBytes → List KState → Prop) :
    DW (hH2 m) h Q ↔ ∀ d, Q d h := Iff.rfl

theorem dw_hF2 (x : KSt) (h : List KState) (Q : KSt → List KState → Prop) :
    DW (hF2 x) h Q ↔ Admissible KState.zero keccakNF h (stateEquiv x) ∧
      ∀ y, Q (stateEquiv.symm y) (y :: h) := by
  rw [hF2, dw_map]
  rfl

/-- A Keccak-256 query of the prover, completed from its table or its coins. -/
theorem dw_hashJ_inl (m : List UInt8) (J : JTab) {h : List KState}
    {Q : Out × JTab → List KState → Prop} (hQ : ∀ d j J', Q ((d, j), J') h) :
    DW ((hashJ hH2 hF2 (coin2 KSt) (coin2 DigestBytes) (.inl m)).run J) h Q := by
  simp only [hashJ, StateT.run]
  rw [dw_bind]
  refine (dw_hH2 m h _).2 fun d ↦ ?_
  split
  · exact hQ _ _ _
  · rw [dw_bind]
    refine @dw_coin2 _ _ h _ fun j ↦ ?_
    exact hQ d j _

/-- A permutation call of the prover: a direct call of `F` on the bytes, completed from its table
or its coins. -/
theorem dw_hashJ_inr (x : KSt) (J : JTab) {h : List KState} {Q : Out × JTab → List KState → Prop}
    (hx : Admissible KState.zero keccakNF h (stateEquiv x))
    (hQ : ∀ y d J', Q ((d, stateEquiv.symm y), J') (y :: h)) :
    DW ((hashJ hH2 hF2 (coin2 KSt) (coin2 DigestBytes) (.inr x)).run J) h Q := by
  simp only [hashJ, StateT.run]
  rw [dw_bind]
  refine (dw_hF2 x h _).2 ⟨hx, fun y ↦ ?_⟩
  split
  · exact hQ _ _ _
  · rw [dw_bind]
    refine @dw_coin2 _ _ _ _ fun j ↦ ?_
    exact hQ y j _

/-- **An input admissible on lanes is admissible on bytes**: keeping lanes `16 .. 24` keeps the
capacity and byte `135` (`LeanVM.Rpm.keccakNF_of_keep`); the zero lanes are the zero state. -/
theorem admissible_of_admL {H : List KSt} {x : KSt} (hx : Deployed.Disc.AdmL H x) :
    Admissible KState.zero keccakNF (H.map stateEquiv) (stateEquiv x) := by
  rcases hx with hx | ⟨z, hz, hx⟩
  · left
    have h := keccakNF_of_keep x _ hx
    rw [toRpm_zero] at h
    exact h
  · right
    exact ⟨stateEquiv z, List.mem_map_of_mem hz, keccakNF_of_keep x z hx⟩

variable {S : Type} (P : Proto S Inp Out Msg Tbl Pos)

/-- **The transfer**: a skeleton disciplined on lanes, run by the prover of the two-oracle model
whose leaf rows are byte strings, is disciplined on bytes, its answers read through
`stateEquiv`. -/
theorem dw_implHF (hrow : ∀ s h k x, ∃ m, P.rowFn s h k x = .inl m) (s : S) {α : Type}
    (oa : OracleComp DSpec α) :
    ∀ (H : List KSt) (st : List Out × JTab), Deployed.Disc.Wp oa H (fun _ _ ↦ True) →
      DW ((simulateQ (implHF P s) oa).run st) (H.map stateEquiv) (fun _ _ ↦ True) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro H st _; trivial
  | query_bind op k ih =>
    intro H st hw
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rw [dw_bind]
    rcases op with (m | x) | _ | ⟨t, x⟩ | (m | x)
    · rw [Deployed.Disc.wp_query_other _ (by simp) (by simp)] at hw
      refine (dw_map _ _ _ _).2 (dw_hashJ_inl m st.2 fun d j J' ↦ ?_)
      exact ih _ H _ (hw _)
    · rw [Deployed.Disc.wp_query_pubF] at hw
      refine (dw_map _ _ _ _).2 (dw_hashJ_inr x st.2 (admissible_of_admL hw.1) fun y d J' ↦ ?_)
      rw [show y :: H.map stateEquiv = (stateEquiv.symm y :: H).map stateEquiv by
        rw [List.map_cons, Equiv.apply_symm_apply]]
      exact ih _ _ _ (hw.2 _)
    · rw [Deployed.Disc.wp_query_other _ (by simp) (by simp)] at hw
      exact ih _ H st (hw _)
    · rw [Deployed.Disc.wp_query_other _ (by simp) (by simp)] at hw
      obtain ⟨mrow, hm⟩ := hrow s (st.1.take (P.cK t)) t x
      by_cases hk : st.1.length < P.cK t
      · have e : (implHF P s (.leaf t x)).run st = pure (default, st) := by
          show (if _ then _ else _) = _
          simp only [hk, ↓reduceIte]
        rw [e]
        exact ih _ H st (hw _)
      · have e : (implHF P s (.leaf t x)).run st = (fun z ↦ (z.1, (st.1, z.2))) <$>
            (hashJ hH2 hF2 (coin2 KSt) (coin2 DigestBytes) (.inl mrow)).run st.2 := by
          show (if _ then _ else _) = _
          simp only [hk, ↓reduceIte, hm]
        rw [e]
        refine (dw_map _ _ _ _).2 (dw_hashJ_inl mrow st.2 fun d j J' ↦ ?_)
        exact ih _ H _ (hw _)
    · rw [Deployed.Disc.wp_query_other _ (by simp) (by simp)] at hw
      refine (dw_map _ _ _ _).2 (dw_hashJ_inl m st.2 fun d j J' ↦ ?_)
      exact ih _ H _ (hw _)
    · rw [Deployed.Disc.wp_query_chalF] at hw
      refine (dw_map _ _ _ _).2 (dw_hashJ_inr x st.2 (admissible_of_admL hw.1) fun y d J' ↦ ?_)
      rw [show y :: H.map stateEquiv = (stateEquiv.symm y :: H).map stateEquiv by
        rw [List.map_cons, Equiv.apply_symm_apply]]
      exact ih _ _ _ (hw.2 _)

/-- A skeleton disciplined on lanes from no answer gives a prover following the duplex
discipline. -/
theorem duplexDiscipline_of_wp (hrow : ∀ s h k x, ∃ m, P.rowFn s h k x = .inl m)
    (skel : OracleComp DSpec Proof) (h : Deployed.Disc.Wp skel [] (fun _ _ ↦ True)) :
    DuplexDiscipline P skel := by
  intro s
  refine duplex_of_dw _ _ ?_
  unfold proverJ
  rw [StateT.run'_eq, dw_map]
  exact dw_implHF P hrow s skel [] _ h

/-- **The deployed prover follows the duplex discipline** (`hduplex` of `zk_rpm_deployed` and its
corollaries), for every shape, when its leaf rows are byte strings: each permutation call absorbs
into the zero state (an opening's seed: the IV in lanes `0 .. 3`) or into the duplex's state, an
earlier answer, keeping lanes `16 .. 24`. -/
theorem duplexDiscipline_skel (hrow : ∀ s h k x, ∃ m, P.rowFn s h k x = .inl m)
    (sh : Deployed.Shape) : DuplexDiscipline P (Deployed.skel sh) :=
  duplexDiscipline_of_wp P hrow _ (Deployed.Disc.ok_skel sh [] _ fun _ _ ↦ trivial)

end Transfer

/-! ## A prover whose leaf rows are byte strings -/

/-- **A prover whose leaf rows are byte strings**, its rows read as Keccak-256's inputs (`inl`): the
deployed prover hashes a leaf's bytes (`pcs::merkle`, `Deployed.leafH`). -/
def ofBytes {S : Type} (P : Proto S (List UInt8) Out Msg Tbl Pos) : Proto S Inp Out Msg Tbl Pos where
  n := P.n
  msgFn := P.msgFn
  cK := P.cK
  rowFn s h k x := .inl (P.rowFn s h k x)
  opened := P.opened

/-- Its rows are byte strings (`hrow`). -/
theorem rowFn_ofBytes {S : Type} (P : Proto S (List UInt8) Out Msg Tbl Pos) :
    ∀ s h k x, ∃ m, (ofBytes P).rowFn s h k x = .inl m :=
  fun _ _ _ _ ↦ ⟨_, rfl⟩

/-- Every prover whose rows are byte strings is one: stating the theorems for `ofBytes` loses no
generality over `hrow`. -/
theorem exists_ofBytes {S : Type} (P : Proto S Inp Out Msg Tbl Pos)
    (hrow : ∀ s h k x, ∃ m, P.rowFn s h k x = .inl m) :
    ∃ Pb : Proto S (List UInt8) Out Msg Tbl Pos, P = ofBytes Pb := by
  refine ⟨⟨P.n, P.msgFn, P.cK, fun s h k x ↦ (hrow s h k x).choose, P.opened⟩, ?_⟩
  cases P with
  | mk n msgFn cK rowFn opened =>
    simp only [ofBytes, Proto.mk.injEq, true_and, and_true]
    funext s h k x
    exact (hrow s h k x).choose_spec

/-! ## The end statements without `hrow` and `hduplex` -/

section Deployed

variable {S : Type} [SampleableType S]

/-- **`zk_rpm_deployed_bits` without `hrow` and `hduplex`**: for a prover whose leaf rows are byte
strings (`ofBytes Pb`), at `2^22` rows, `δ = δ₂ = 2^-2368`, at most `2^127` queries of the
distinguisher: advantage at most `εFS + εhv + 2^-2200 + Q² / 2^508`. -/
theorem zk_rpm_deployed_bits' (stmt : Deployed.Statement) (idW idσ idQ : QuotientRpm.Bytes32)
    (rows : List (List UInt8)) (hrows : rows.length = 2 ^ 19) (sh : Deployed.Shape)
    (hsh : sh = Deployed.deployedShape stmt idW idσ idQ rows)
    (Pb : Proto S (List UInt8) Out Msg Tbl Pos)
    (simV : List Out → ProbComp (View Msg Inp Tbl Pos)) (good : List Out → Prop)
    (εFS εhv : ℝ≥0∞) (QD Q : ℕ) (hQD : QD ≤ 2 ^ 127)
    (hFS : Deployed.FSFresh (ofBytes Pb) (Deployed.skel sh) [] εFS)
    (hHV : Deployed.JointHVZK (ofBytes Pb) simV good εhv)
    (hfac : ∀ σ k x, (ofBytes Pb).opened σ k x = false → ∀ y,
      Nonempty (Deployed.Factors (ofBytes Pb) σ (fun s => (ofBytes Pb).rows s σ k x = y)
        ((2 : ℝ≥0∞) ^ 2368)⁻¹))
    (hfac₂ : ∀ σ k x k' x', (ofBytes Pb).opened σ k x = false →
      (ofBytes Pb).opened σ k' x' = false → (k, x) ≠ (k', x') →
      Nonempty (Deployed.Factors (ofBytes Pb) σ
        (fun s => (ofBytes Pb).rows s σ k x = (ofBytes Pb).rows s σ k' x') ((2 : ℝ≥0∞) ^ 2368)⁻¹))
    (D : Proof → OracleComp (permutationOracleSpec KSt) Bool)
    (hD : ∀ π, IsTotalQueryBound (D π) QD)
    (hQ : ∀ s, QueryCostAtMost (zkGameRpmD (ofBytes Pb) (Deployed.skel sh) D s)
      permutationCallCost Q) :
    Close (realGameRpmD (ofBytes Pb) (Deployed.skel sh) D)
      (simGameRpmD (ofBytes Pb) simV (Deployed.skel sh) D)
      (εFS + εhv + ((2 : ℝ≥0∞) ^ 2200)⁻¹ + (Q ^ 2 : ℝ≥0∞) / 2 ^ 508) :=
  zk_rpm_deployed_bits stmt idW idσ idQ rows hrows sh hsh (ofBytes Pb) simV good εFS εhv QD Q hQD
    hFS hHV hfac hfac₂ (rowFn_ofBytes Pb) (duplexDiscipline_skel _ (rowFn_ofBytes Pb) sh) D hD hQ

end Deployed

section Joint

open Polynomial Module QuotientSecurity QuotientSecurity.Hiding QuotientZk.Joint

variable {K E Γ₁ Γ₂ Γw W ι₁ Y₁ Q₁ O₁ ι₂ Y₂ Q₂ O₂ : Type} [Field K] [Field E] [Algebra K E]
  [DecidableEq E] [CharP E 2] [Fintype E]
  [Fintype ι₁] [DecidableEq ι₁] [Fintype Y₁] [DecidableEq Y₁] [Fintype Q₁] [DecidableEq Q₁]
  [Fintype ι₂] [DecidableEq ι₂] [Fintype Y₂] [DecidableEq Y₂] [Fintype Q₂] [DecidableEq Q₂]
  [Fintype K] [DecidableEq K] [FiniteDimensional K E] [SampleableType K] [SampleableType E]
  [SampleableType (ι₁ → Y₁ → K)] [SampleableType (ι₂ → Y₂ → K)]
  [SampleableType Γ₁] [Fintype Γ₁] [SampleableType Γ₂] [Fintype Γ₂] [SampleableType Γw]

/-- **`zk_rpm_deployed_joint` without `hrow` and `hduplex`**: for the deployed skeleton and a prover
whose leaf rows are byte strings (`ofBytes Pb`) and that is the joint model, every distinguisher of
at most `QD ≤ 2^127` queries of `π` and `π⁻¹`, the real game making at most `Q` permutation calls,
tells the real game from the simulated one with advantage at most
`εFS + 2^-165 + 2^-2200 + Q² / 2^508`. Remaining: `hFS`, the joint model's hypotheses, `hQ`. -/
theorem zk_rpm_deployed_joint' (stmtD : Deployed.Statement) (idW idσ idQ : QuotientRpm.Bytes32)
    (rowsW : List (List UInt8)) (hrows : rowsW.length = 2 ^ 19) (sh : Deployed.Shape)
    (hsh : sh = Deployed.deployedShape stmtD idW idσ idQ rowsW)
    (Pb : Proto (Rand K ι₁ Y₁ ι₂ Y₂) (List UInt8) Out Msg Tbl Pos)
    (εFS : ℝ≥0∞) (QD Q : ℕ) (hQD : QD ≤ 2 ^ 127)
    (hFS : Deployed.FSFresh (ofBytes Pb) (Deployed.skel sh) [] εFS)
    (h3 : finrank K E = 3) (P₀ : Params E) (hE : P₀.Exact) (stmt : Fin P₀.words → E)
    (gK : Fin 4 → K[X]) (van : K[X]) (hvan : ∀ x : P₀.T, aeval (rowPoly.eval (x : E)) van = 0)
    (hsat : P₀.Sat stmt (P₀.cells (committed gK van 0))) (hvan0 : van ≠ 0)
    (hq : Fintype.card E = 2 ^ 192) (hK : Fintype.card K = 2 ^ 64) (hN : P₀.nCells = 2 ^ 24)
    (hdeg : van.natDegree ≤ 2 ^ 22) (h40₁ : 40 ≤ Fintype.card ι₁) (h40₂ : 40 ≤ Fintype.card ι₂)
    (inK : E → Bool) (hinK : ∀ e, inK e = true ↔ e ∈ Set.range (algebraMap K E))
    (sigmaAt : E → E) (hsig : ∀ t, sigmaAt t = P₀.sigmaPoly.eval t)
    (wir : Chal E Γ₁ Γ₂ Γw → W)
    (S₁ : SecretOpening K E (Chal E Γ₁ Γ₂ Γw) ι₁ Y₁ Q₁ O₁)
    (S₂ : SecretOpening K E (Chal E Γ₁ Γ₂ Γw) ι₂ Y₂ Q₂ O₂)
    (hS₁ : S₁.Conditions) (hS₂ : S₂.Conditions)
    (T₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₁ → Y₁ → K)
    (T₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → Fin 3 → K) → ι₂ → Y₂ → K)
    (cl₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → Fin S₁.m → E)
    (cl₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → Fin S₂.m → E)
    (hT₁ : ∀ c, good P₀ gK van c → ∀ m, S₁.claims c (T₁ c m) = cl₁ c (redMsgs P₀ gK van c.1.1.2 m))
    (hT₂ : ∀ c, good P₀ gK van c → ∀ m, S₂.claims c (T₂ c m) = cl₂ c (redMsgs P₀ gK van c.1.1.2 m))
    (simT₁ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → ι₁ → Y₁ → K)
    (simT₂ : Chal E Γ₁ Γ₂ Γw → (Fin 4 → E) × E → ι₂ → Y₂ → K)
    (hsimT₁ : ∀ c, good P₀ gK van c → ∀ v, S₁.claims c (simT₁ c v) = cl₁ c v)
    (hsimT₂ : ∀ c, good P₀ gK van c → ∀ v, S₂.claims c (simT₂ c v) = cl₂ c v)
    (lk : Link (ofBytes Pb) P₀ gK van wir T₁ T₂ S₁ S₂)
    (hch : lk.chOf <$> uniformList Out Pb.n =ᵈ ($ᵗ (Chal E Γ₁ Γ₂ Γw)))
    (D : Proof → OracleComp (permutationOracleSpec KSt) Bool)
    (hD : ∀ π, IsTotalQueryBound (D π) QD)
    (hQ : ∀ s, QueryCostAtMost (zkGameRpmD (ofBytes Pb) (Deployed.skel sh) D s)
      permutationCallCost Q) :
    Close (realGameRpmD (ofBytes Pb) (Deployed.skel sh) D)
      (simGameRpmD (ofBytes Pb)
        (fun σ => lk.out σ <$> jointSim inK sigmaAt wir S₁ S₂ simT₁ simT₂ (lk.chOf σ))
        (Deployed.skel sh) D)
      (εFS + 1 / 2 ^ 165 + ((2 : ℝ≥0∞) ^ 2200)⁻¹ + (Q ^ 2 : ℝ≥0∞) / 2 ^ 508) :=
  zk_rpm_deployed_joint stmtD idW idσ idQ rowsW hrows sh hsh (ofBytes Pb) εFS QD Q hQD hFS h3 P₀ hE
    stmt gK van hvan hsat hvan0 hq hK hN hdeg h40₁ h40₂ inK hinK sigmaAt hsig wir S₁ S₂ hS₁ hS₂
    T₁ T₂ cl₁ cl₂ hT₁ hT₂ simT₁ simT₂ hsimT₁ hsimT₂ lk hch (rowFn_ofBytes Pb)
    (duplexDiscipline_skel _ (rowFn_ofBytes Pb) sh) D hD hQ

end Joint

end QuotientZk.DRpm

/-- info: 'QuotientZk.Deployed.Disc.ok_skel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.Deployed.Disc.ok_skel

/--
info: 'QuotientZk.DRpm.duplexDiscipline_skel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms QuotientZk.DRpm.duplexDiscipline_skel

/-- info: 'QuotientZk.DRpm.exists_ofBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuotientZk.DRpm.exists_ofBytes

/--
info: 'QuotientZk.DRpm.zk_rpm_deployed_bits'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms QuotientZk.DRpm.zk_rpm_deployed_bits'

/--
info: 'QuotientZk.DRpm.zk_rpm_deployed_joint'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms QuotientZk.DRpm.zk_rpm_deployed_joint'
