-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): `common`'s weight calculus (`Common.QueryCostAtMost`; Keccak-256 over `π`
-- costs `⌊n / 136⌋ + 1` calls, `Common.isWeightBound_keccakK_bind`; coins cost nothing,
-- `Common.isWeightBound_liftM_probComp`) and mumbai's honest WHIR script (`levelsA`, `roundA`, ...,
-- `LeanVM.Rpm.ladder_folds`); the bound on its committed rows (`WordsLE`, `OWordsLE`) is
-- `EndToEnd/Completeness/E2ECompleteness/Cost.lean`'s, copied: that library imports leanerVM's
-- `LeanVM.Protocol.ExperimentBridge`, whose `LeanDa.instFintypeK` then wins over the `Fintype K`
-- the deployed joint model was built with, and elaborating `(deployedJD R stmt w).P` exceeds the
-- maximum recursion depth (a file importing both needs `attribute [-instance] LeanDa.instFintypeK`).
import ZK.Final
import ZK.ProverBridgeRender
import LeanVM.Protocol.Rpm.Cost

/-!
# The prover's permutation budget

`zeroKnowledge_deployed_final` (`ZK/Final.lean`) assumes `hprover`: the statement's prover in the
skeleton model, `proverJ` over Keccak-256 over `π` and the duplex's calls of `π`, makes at most `Qp`
calls of `π`. The skeleton hashes what the renderer sends (`commitNext` hashes the rows of a
commitment, `opening` the claims' bytes of an IV), so `Qp` depends on the renderer's rows.

* **The skeleton's hashes** (`Wp`, `fine_skel`, `fine_skelSetup`): a weakest precondition over the skeleton's
  operations, every Keccak-256 input at most `L` bytes on every path where every message has rows
  of at most `Lr` bytes and claims' bytes of at most `Lb` (`MsgOK`): the trees' nodes (`64` bytes),
  the chain's inputs (at most `192`), a commitment's rows (`Lr`), an IV (its prefix and `Lb`), the
  public rows.
* **The transfer** (`cost_proverJ`): a skeleton of at most `N` operations whose hashes are at most
  `L` bytes, run by `proverJ` with messages passing `MsgOK` and leaves of at most `L` bytes, makes
  at most `N · (⌊L / 136⌋ + 1)` calls of `π` (a coin costs nothing).
* **The deployed prover's messages** (`msgOK_PbMsg`): the claims' bytes (`claimMsg`: `26`, `25`,
  `62` scalars, at most `1488` bytes), and for **WHIR's honest prover as the renderer**
  (`msgOK_whirRenderer`) rows of at most `192` words (`1536` bytes: `WordsLE` of mumbai's script,
  `hybridScript`'s lane rounds and level tail, kept along the drive `evRun`); the secret leaves are
  `512` bytes (`length_rowBytes`).
* **`hprover_of_renderer`**, **`hprover_whir`**: `hprover` at `Qp = (2^24 + 2^70) · 12` (an IV of
  `76 + 1488 = 1564` bytes is `12` blocks; the skeleton makes at most `2^24 + 2^70` operations,
  `skelSetup_queryBound`), given the wiring codeword's rows of at most `1564` bytes.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace QuotientZk.Deployed.Budget

set_option linter.unusedSectionVars false

/-! ## Messages and the weakest precondition -/

/-- An item's hashed lengths: a commitment's rows at most `Lr` bytes, claims' bytes at most `Lb`. -/
def ItemOK (Lr Lb : ℕ) : Item → Prop
  | .rows l => ∀ r ∈ l, r.length ≤ Lr
  | .bytes b => b.length ≤ Lb
  | .scalars _ => True
  | .opened _ => True

/-- A message's items pass `ItemOK`. -/
def MsgOK (Lr Lb : ℕ) (m : Msg) : Prop := ∀ it ∈ m, ItemOK Lr Lb it

section Msgs

variable {Lr Lb : ℕ}

theorem msgOK_nil : MsgOK Lr Lb [] := fun _ h ↦ absurd h List.not_mem_nil

theorem MsgOK.append {a b : Msg} (ha : MsgOK Lr Lb a) (hb : MsgOK Lr Lb b) :
    MsgOK Lr Lb (a ++ b) := fun it hit ↦ (List.mem_append.mp hit).elim (ha it) (hb it)

theorem msgOK_singleton {it : Item} (h : ItemOK Lr Lb it) : MsgOK Lr Lb [it] := fun _ hit ↦ by
  rw [List.mem_singleton] at hit
  exact hit ▸ h

theorem MsgOK.sub {a b : Msg} (hb : MsgOK Lr Lb b) (h : a ⊆ b) : MsgOK Lr Lb a :=
  fun it hit ↦ hb it (h hit)

end Msgs

section Wp

variable (mok : Msg → Prop) (L : ℕ)

/-- **The weakest precondition of short hashes**: every Keccak-256 input (`pub` or `chal` of bytes)
at most `L` bytes, and `Q` of the result, on every path whose messages pass `mok`. -/
def Wp {α : Type} : OracleComp DSpec α → (α → Prop) → Prop
  | .pure a, Q => Q a
  | .liftBind (.pub (.inl m)) k, Q => m.length ≤ L ∧ ∀ u, Wp (k u) Q
  | .liftBind (.chal (.inl m)) k, Q => m.length ≤ L ∧ ∀ u, Wp (k u) Q
  | .liftBind .msg k, Q => ∀ u, mok u → Wp (k u) Q
  | .liftBind _ k, Q => ∀ u, Wp (k u) Q

variable {α β : Type}

theorem wp_pure (a : α) (Q : α → Prop) : Wp mok L (pure a : OracleComp DSpec α) Q ↔ Q a :=
  Iff.rfl

theorem wp_pubH (m : List UInt8) (k : Out → OracleComp DSpec α) (Q : α → Prop) :
    Wp mok L (liftM (DSpec.query (.pub (.inl m))) >>= k) Q ↔
      m.length ≤ L ∧ ∀ u : Out, Wp mok L (k u) Q := Iff.rfl

theorem wp_chalH (m : List UInt8) (k : Out → OracleComp DSpec α) (Q : α → Prop) :
    Wp mok L (liftM (DSpec.query (.chal (.inl m))) >>= k) Q ↔
      m.length ≤ L ∧ ∀ u : Out, Wp mok L (k u) Q := Iff.rfl

theorem wp_pubF (x : KSt) (k : Out → OracleComp DSpec α) (Q : α → Prop) :
    Wp mok L (liftM (DSpec.query (.pub (.inr x))) >>= k) Q ↔ ∀ u : Out, Wp mok L (k u) Q :=
  Iff.rfl

theorem wp_chalF (x : KSt) (k : Out → OracleComp DSpec α) (Q : α → Prop) :
    Wp mok L (liftM (DSpec.query (.chal (.inr x))) >>= k) Q ↔ ∀ u : Out, Wp mok L (k u) Q :=
  Iff.rfl

theorem wp_msg (k : Msg → OracleComp DSpec α) (Q : α → Prop) :
    Wp mok L (liftM (DSpec.query .msg) >>= k) Q ↔ ∀ u : Msg, mok u → Wp mok L (k u) Q :=
  Iff.rfl

theorem wp_leaf (t : Tbl) (x : Pos) (k : Out → OracleComp DSpec α) (Q : α → Prop) :
    Wp mok L (liftM (DSpec.query (.leaf t x)) >>= k) Q ↔ ∀ u : Out, Wp mok L (k u) Q :=
  Iff.rfl

/-- **The bind law.** -/
theorem wp_bind (oa : OracleComp DSpec α) (f : α → OracleComp DSpec β) :
    ∀ Q : β → Prop, Wp mok L (oa >>= f) Q ↔ Wp mok L oa (fun a ↦ Wp mok L (f a) Q) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro Q; rw [pure_bind]; rfl
  | query_bind op k ih =>
    intro Q
    rw [bind_assoc]
    rcases op with (m | x) | _ | ⟨t, x⟩ | (m | x)
    · rw [wp_pubH, wp_pubH]
      exact and_congr Iff.rfl (forall_congr' fun u ↦ ih u Q)
    · rw [wp_pubF, wp_pubF]
      exact forall_congr' fun u ↦ ih u Q
    · rw [wp_msg, wp_msg]
      exact forall_congr' fun u ↦ imp_congr_right fun _ ↦ ih u Q
    · rw [wp_leaf, wp_leaf]
      exact forall_congr' fun u ↦ ih u Q
    · rw [wp_chalH, wp_chalH]
      exact and_congr Iff.rfl (forall_congr' fun u ↦ ih u Q)
    · rw [wp_chalF, wp_chalF]
      exact forall_congr' fun u ↦ ih u Q

theorem wp_mono (oa : OracleComp DSpec α) :
    ∀ (Q Q' : α → Prop), Wp mok L oa Q → (∀ a, Q a → Q' a) → Wp mok L oa Q' := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro Q Q' h hQ; exact hQ a h
  | query_bind op k ih =>
    intro Q Q' h hQ
    rcases op with (m | x) | _ | ⟨t, x⟩ | (m | x)
    · rw [wp_pubH] at h ⊢
      exact ⟨h.1, fun u ↦ ih u Q Q' (h.2 u) hQ⟩
    · rw [wp_pubF] at h ⊢
      exact fun u ↦ ih u Q Q' (h u) hQ
    · rw [wp_msg] at h ⊢
      exact fun u hu ↦ ih u Q Q' (h u hu) hQ
    · rw [wp_leaf] at h ⊢
      exact fun u ↦ ih u Q Q' (h u) hQ
    · rw [wp_chalH] at h ⊢
      exact ⟨h.1, fun u ↦ ih u Q Q' (h.2 u) hQ⟩
    · rw [wp_chalF] at h ⊢
      exact fun u ↦ ih u Q Q' (h u) hQ

variable {mok L}

/-- Sequencing: `oa` establishes `P`, from which `f` establishes `Q`. -/
theorem wp_seq {oa : OracleComp DSpec α} {f : α → OracleComp DSpec β} {P : α → Prop}
    {Q : β → Prop} (h : Wp mok L oa P) (hf : ∀ a, P a → Wp mok L (f a) Q) :
    Wp mok L (oa >>= f) Q :=
  (wp_bind mok L oa f Q).2 (wp_mono mok L oa P _ h hf)

variable (mok L)

/-- **Short hashes, whatever the result**. -/
def Fine (oa : OracleComp DSpec α) : Prop := ∀ Q : α → Prop, (∀ a, Q a) → Wp mok L oa Q

variable {mok L}

theorem fine_pure (a : α) : Fine mok L (pure a : OracleComp DSpec α) := fun _ h ↦ h a

theorem Fine.wp {oa : OracleComp DSpec α} (h : Fine mok L oa) {f : α → OracleComp DSpec β}
    {Q : β → Prop} (hf : ∀ a, Wp mok L (f a) Q) : Wp mok L (oa >>= f) Q :=
  (wp_bind mok L oa f Q).2 (h _ hf)

theorem Fine.bind {oa : OracleComp DSpec α} {f : α → OracleComp DSpec β} (h : Fine mok L oa)
    (hf : ∀ a, Fine mok L (f a)) : Fine mok L (oa >>= f) :=
  fun Q hQ ↦ h.wp fun a ↦ hf a Q hQ

theorem Fine.wp_self {oa : OracleComp DSpec α} (h : Fine mok L oa) : Wp mok L oa fun _ ↦ True :=
  h _ fun _ ↦ trivial

theorem fine_mapM {γ : Type} (f : γ → OracleComp DSpec α) :
    ∀ l : List γ, (∀ c ∈ l, Fine mok L (f c)) → Fine mok L (l.mapM f)
  | [], _ => by rw [List.mapM_nil]; exact fine_pure _
  | c :: l, hf => by
    rw [List.mapM_cons]
    exact (hf c List.mem_cons_self).bind fun a ↦
      (fine_mapM f l fun c' hc' ↦ hf c' (List.mem_cons_of_mem _ hc')).bind fun _ ↦ fine_pure _

end Wp

/-! ## The skeleton's operations -/

section Ops

variable {mok : Msg → Prop} {L : ℕ} {α : Type}

theorem fine_hashH {m : List UInt8} (h : m.length ≤ L) : Fine mok L (hashH m) :=
  fun _ hQ ↦ ⟨h, fun _ ↦ hQ _⟩

theorem fine_chalH {m : List UInt8} (h : m.length ≤ L) : Fine mok L (chalH m) :=
  fun _ hQ ↦ ⟨h, fun _ ↦ hQ _⟩

theorem fine_perm (x : KSt) : Fine mok L (perm x) := fun _ hQ _ ↦ hQ _

theorem fine_chalF (x : KSt) : Fine mok L (chalF x) := fun _ hQ _ ↦ hQ _

theorem fine_leafH (k : Tbl) (x : ℕ) : Fine mok L (leafH k x) := fun _ hQ _ ↦ hQ _

theorem wp_getMsg (Q : Msg → Prop) : Wp mok L getMsg Q ↔ ∀ m, mok m → Q m := Iff.rfl

theorem fine_levelUp (hL : 64 ≤ L) : ∀ l : List QuotientRpm.Bytes32, Fine mok L (levelUp l)
  | a :: b :: rest => by
    rw [levelUp]
    exact (fine_hashH (by rw [List.length_append, Vector.length_toList, Vector.length_toList]; omega)).bind
      fun _ ↦ (fine_levelUp hL rest).bind fun _ ↦ fine_pure _
  | [] => fine_pure (α := List QuotientRpm.Bytes32) []
  | [_] => fine_pure (α := List QuotientRpm.Bytes32) []

theorem fine_levels (hL : 64 ≤ L) :
    ∀ (d : ℕ) (l : List QuotientRpm.Bytes32), Fine mok L (levels d l)
  | 0, l => by rw [levels]; exact fine_pure _
  | d + 1, l => by
    rw [levels]
    exact (fine_levelUp hL l).bind fun up ↦ (fine_levels hL d up).bind fun _ ↦ fine_pure _

/-- **An opening's shape hashes short inputs**: its IV's prefix and claims' bytes at most `L`
bytes, its public rows too. -/
def OpenOK (Lb L : ℕ) (sh : OpenShape) : Prop :=
  sh.ivPrefix.length + Lb ≤ L ∧ ∀ r ∈ sh.pubRows, r.length ≤ L

theorem fine_tree₀ (hL : 64 ≤ L) (sh : OpenShape) (hpub : ∀ r ∈ sh.pubRows, r.length ≤ L) :
    Fine mok L (tree₀ sh) := by
  unfold tree₀
  dsimp only
  split
  · exact (fine_mapM _ _ fun _ _ ↦ fine_leafH _ _).bind fun _ ↦ fine_levels hL _ _
  · exact (fine_mapM _ _ fun r hr ↦ fine_hashH (hpub r hr)).bind fun _ ↦ fine_levels hL _ _

theorem fine_absorb (d : Dx) (x : QuotientRpm.Limbs) (tag : UInt64) :
    Fine mok L (d.absorb x tag) := by
  unfold Dx.absorb
  split
  · exact (fine_perm _).bind fun _ ↦ fine_pure _
  · exact fine_pure _

theorem fine_absorbAll : ∀ (d : Dx) (xs : List QuotientRpm.Limbs), Fine mok L (d.absorbAll xs)
  | d, [] => by rw [Dx.absorbAll]; exact fine_pure _
  | d, x :: xs => by
    rw [Dx.absorbAll]
    exact (fine_absorb d x _).bind fun d' ↦ fine_absorbAll d' xs

theorem fine_draw (d : Dx) : Fine mok L d.draw := (fine_chalF _).bind fun _ ↦ fine_pure _

theorem fine_seed (iv : QuotientRpm.Bytes32) : Fine mok L (seed iv) :=
  (fine_perm _).bind fun _ ↦ fine_pure _

theorem fine_tryNonce (d : Dx) (n : UInt64) : Fine mok L (tryNonce d n) :=
  (fine_absorb _ _ _).bind fun _ ↦ (fine_perm _).bind fun _ ↦ fine_pure _

theorem fine_grind : ∀ (fuel : ℕ) (d : Dx) (n : UInt64), Fine mok L (grind d fuel n)
  | 0, d, n => by rw [grind]; exact fine_pure _
  | fuel + 1, d, n => by
    rw [grind]
    refine (fine_tryNonce d n).bind fun r ↦ ?_
    obtain ⟨b, d'⟩ := r
    dsimp only
    split
    · exact fine_pure _
    · exact fine_grind fuel d (n + 1)

end Ops

/-! ## The openings -/

section Openings

variable {Lr Lb L : ℕ}

/-- The opening's state passes: its pending items do. -/
abbrev OK (Lr Lb : ℕ) (o : OSt) : Prop := MsgOK Lr Lb o.items

theorem takeScalars_sub : ∀ (items : Msg) (k : ℕ), (takeScalars items k).2 ⊆ items
  | [], _ => List.Subset.refl _
  | .scalars _ :: _, _ => List.subset_cons_self _ _
  | .rows _ :: _, _ => List.Subset.refl _
  | .opened _ :: _, _ => List.Subset.refl _
  | .bytes _ :: _, _ => List.Subset.refl _

theorem length_takeScalars : ∀ (items : Msg) (k : ℕ), (takeScalars items k).1.length = k
  | [], k => List.length_replicate
  | .scalars l :: _, k => by
    show ((l ++ List.replicate k (0, 0, 0)).take k).length = k
    rw [List.length_take, List.length_append, List.length_replicate]
    omega
  | .rows _ :: _, k => List.length_replicate
  | .opened _ :: _, k => List.length_replicate
  | .bytes _ :: _, k => List.length_replicate

theorem takeRows_sub : ∀ items : Msg, (takeRows items).2 ⊆ items
  | [] => List.Subset.refl _
  | .scalars _ :: _ => List.Subset.refl _
  | .rows _ :: _ => List.subset_cons_self _ _
  | .opened _ :: _ => List.Subset.refl _
  | .bytes _ :: _ => List.Subset.refl _

theorem takeRows_fst : ∀ items : Msg, MsgOK Lr Lb items → ∀ r ∈ (takeRows items).1, r.length ≤ Lr
  | [], _ => fun _ h ↦ absurd h List.not_mem_nil
  | .scalars _ :: _, _ => fun _ h ↦ absurd h List.not_mem_nil
  | .rows l :: _, hm => hm (.rows l) List.mem_cons_self
  | .opened _ :: _, _ => fun _ h ↦ absurd h List.not_mem_nil
  | .bytes _ :: _, _ => fun _ h ↦ absurd h List.not_mem_nil

theorem takeOpened_sub : ∀ items : Msg, (takeOpened items).2 ⊆ items
  | [] => List.Subset.refl _
  | .scalars _ :: _ => List.Subset.refl _
  | .rows _ :: _ => List.Subset.refl _
  | .opened _ :: _ => List.subset_cons_self _ _
  | .bytes _ :: _ => List.Subset.refl _

theorem wp_sendK (o : OSt) (h : OK Lr Lb o) (k : ℕ) : Wp (MsgOK Lr Lb) L (sendK o k) (OK Lr Lb) := by
  unfold sendK
  have hsub := takeScalars_sub o.items k
  generalize takeScalars o.items k = p at hsub ⊢
  obtain ⟨xs, items⟩ := p
  exact (fine_absorbAll _ _).wp fun _ ↦ (wp_pure _ _ _ _).2 (h.sub hsub)

theorem wp_drawO (o : OSt) : Wp (MsgOK Lr Lb) L (drawO o) (fun r ↦ OK Lr Lb r.2) := by
  unfold drawO
  refine (fine_draw _).wp fun p ↦ ?_
  obtain ⟨c, dx⟩ := p
  exact wp_seq ((wp_getMsg _).2 fun m hm ↦ hm) fun m hm ↦ (wp_pure _ _ _ _).2 hm

theorem wp_rounds : ∀ (k : ℕ) (o : OSt), OK Lr Lb o → Wp (MsgOK Lr Lb) L (rounds o k) (OK Lr Lb)
  | 0, o, h => by rw [rounds]; exact h
  | k + 1, o, h => by
    rw [rounds]
    refine wp_seq (wp_drawO o) fun r hr ↦ ?_
    obtain ⟨_, o'⟩ := r
    exact wp_seq (wp_sendK o' hr 2) fun o'' h'' ↦ wp_rounds k o'' h''

theorem wp_drawMany : ∀ (m : ℕ) (o : OSt), OK Lr Lb o →
    Wp (MsgOK Lr Lb) L (drawMany o m) (fun r ↦ OK Lr Lb r.2)
  | 0, o, h => by rw [drawMany]; exact h
  | m + 1, o, h => by
    rw [drawMany]
    refine wp_seq (wp_drawO o) fun r hr ↦ ?_
    obtain ⟨c, o'⟩ := r
    exact wp_seq (wp_drawMany m o' hr) fun r' hr' ↦ by
      obtain ⟨cs, o''⟩ := r'
      exact hr'

theorem length_getD_le {rows : List (List UInt8)} (h : ∀ r ∈ rows, r.length ≤ Lr) (i : ℕ) :
    (rows.getD i []).length ≤ Lr := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : rows[i]? with
  | none => exact Nat.zero_le _
  | some r => exact h r (List.mem_of_getElem? hi)

theorem wp_commitNext (hL : 64 ≤ L) (hr : Lr ≤ L) (o : OSt) (h : OK Lr Lb o) (depth : ℕ) :
    Wp (MsgOK Lr Lb) L (commitNext o depth) (OK Lr Lb) := by
  unfold commitNext
  have hsub := takeRows_sub o.items
  have hrows := takeRows_fst o.items h
  generalize takeRows o.items = p at hsub hrows ⊢
  obtain ⟨rows, items⟩ := p
  refine (fine_mapM _ _ fun i _ ↦ fine_hashH ((length_getD_le hrows i).trans hr)).wp fun _ ↦ ?_
  refine (fine_levels hL _ _).wp fun _ ↦ ?_
  exact (fine_absorbAll _ _).wp fun _ ↦ (wp_pure _ _ _ _).2 (h.sub hsub)

theorem wp_ood (o : OSt) (h : OK Lr Lb o) (m : ℕ) : Wp (MsgOK Lr Lb) L (ood o m) (OK Lr Lb) := by
  unfold ood
  refine wp_seq (wp_drawMany m o h) fun r hr ↦ ?_
  obtain ⟨_, o'⟩ := r
  exact wp_sendK o' hr 3

theorem wp_queryPhase (o : OSt) (h : OK Lr Lb o) (lvl q : ℕ) :
    Wp (MsgOK Lr Lb) L (queryPhase o lvl q) (OK Lr Lb) := by
  unfold queryPhase
  refine (fine_grind _ _ _).wp fun p ↦ ?_
  obtain ⟨nonce, dx⟩ := p
  refine wp_seq (wp_drawMany _ _ h) fun r hr ↦ ?_
  obtain ⟨cs, o'⟩ := r
  refine wp_seq (wp_drawO o') fun r' hr' ↦ ?_
  obtain ⟨_, o''⟩ := r'
  have hsub := takeOpened_sub o''.items
  dsimp only
  generalize takeOpened o''.items = p at hsub ⊢
  obtain ⟨opened, items⟩ := p
  exact wp_sendK _ (hr'.sub hsub) 2

theorem wp_middle (hL : 64 ≤ L) (hr : Lr ≤ L) :
    ∀ (levels : List (ℕ × ℕ × ℕ)) (o : OSt) (lvl : ℕ) (qs : List ℕ), OK Lr Lb o →
      Wp (MsgOK Lr Lb) L (middle o lvl levels qs) (OK Lr Lb)
  | [], o, lvl, qs, h => by rw [middle]; exact h
  | (folds, depth, oodN) :: rest, o, lvl, q :: qs, h => by
    rw [middle]
    refine wp_seq (wp_rounds folds o h) fun o₁ h₁ ↦ ?_
    refine wp_seq (wp_commitNext hL hr o₁ h₁ depth) fun o₂ h₂ ↦ ?_
    refine wp_seq (wp_ood o₂ h₂ oodN) fun o₃ h₃ ↦ ?_
    refine wp_seq (wp_queryPhase o₃ h₃ lvl q) fun o₄ h₄ ↦ ?_
    exact wp_middle hL hr rest o₄ (lvl + 1) qs h₄
  | _ :: _, o, lvl, [], h => by rw [middle]; exact h

/-- **An opening hashes short inputs**, on every path whose messages pass. -/
theorem fine_opening (hL : 64 ≤ L) (hr : Lr ≤ L) (sh : OpenShape) (hsh : OpenOK Lb L sh)
    (lv₀ : List (List QuotientRpm.Bytes32)) : Fine (MsgOK Lr Lb) L (opening sh lv₀) := by
  intro Q hQ
  unfold opening
  refine wp_seq ((wp_getMsg _).2 fun m hm ↦ hm) fun m hm ↦ ?_
  have hiv := hsh.1
  rcases m with _ | ⟨it, rest⟩
  all_goals try cases it
  all_goals dsimp only
  all_goals refine (fine_hashH (by
    rw [List.length_append]
    first
      | (have h₂ := hm _ List.mem_cons_self; simp only [ItemOK] at h₂; omega)
      | (simp only [List.length_nil]; omega))).wp fun iv ↦ ?_
  all_goals
    refine (fine_seed _).wp fun dx ↦ ?_
    refine (fine_absorbAll _ _).wp fun dx' ↦ ?_
    refine wp_seq (wp_drawO (Lr := Lr) (Lb := Lb) _) fun r hr₀ ↦ ?_
    obtain ⟨_, o₁⟩ := r
    refine wp_seq (wp_sendK o₁ hr₀ 2) fun o₂ h₂ ↦ ?_
    refine wp_seq (wp_rounds 6 o₂ h₂) fun o₃ h₃ ↦ ?_
    refine wp_seq (wp_commitNext hL hr o₃ h₃ _) fun o₄ h₄ ↦ ?_
    refine wp_seq (wp_ood o₄ h₄ _) fun o₅ h₅ ↦ ?_
    refine wp_seq (wp_queryPhase o₅ h₅ 0 _) fun o₆ h₆ ↦ ?_
    refine wp_seq (wp_middle hL hr _ o₆ 1 _ h₆) fun o₇ h₇ ↦ ?_
    refine wp_seq (wp_rounds _ o₇ h₇) fun o₈ h₈ ↦ ?_
    refine wp_seq (wp_sendK o₈ h₈ _) fun o₉ h₉ ↦ ?_
    refine wp_seq (wp_queryPhase o₉ h₉ _ _) fun o₁₀ h₁₀ ↦ ?_
    refine wp_seq (wp_rounds _ o₁₀ h₁₀) fun o₁₁ h₁₁ ↦ ?_
    refine wp_seq (wp_drawO o₁₁) fun r' _ ↦ ?_
    obtain ⟨_, o₁₂⟩ := r'
    exact hQ _

end Openings

/-! ## The skeleton -/

section Skeleton

variable {Lr Lb L : ℕ}

theorem length_flatMap_scalarWord (l : List QuotientRpm.Limbs) :
    (l.flatMap QuotientRpm.scalarWord).length = 32 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, QuotientRpm.length_scalarWord, ih,
      List.length_cons]
    ring

/-- **The skeleton hashes short inputs**: its three openings' shapes pass, the chain's inputs
(at most `192` bytes) and the nodes fit. -/
theorem fine_skel (hL : 192 ≤ L) (hr : Lr ≤ L) (sh : Shape) (hW : OpenOK Lb L sh.witness)
    (hσ : OpenOK Lb L sh.wiring) (hQ : OpenOK Lb L sh.quotient) :
    Fine (MsgOK Lr Lb) L (skel sh) := by
  have h64 : 64 ≤ L := by omega
  unfold skel
  refine (fine_tree₀ h64 _ hW.2).bind fun lvW ↦ ?_
  refine (fine_hashH ?_).bind fun st₀ ↦ ?_
  · simp only [List.length_append, Vector.length_toList, kcTag, List.length_cons, List.length_nil]
    omega
  refine (fine_chalH ?_).bind fun st₁ ↦ ?_
  · rw [List.length_append, Vector.length_toList, QuotientRpm.length_rootWords]; omega
  refine (fine_chalH ?_).bind fun st₂ ↦ ?_
  · rw [Vector.length_toList]; omega
  refine (fine_chalH ?_).bind fun st₃ ↦ ?_
  · rw [Vector.length_toList]; omega
  refine (fine_tree₀ h64 _ hQ.2).bind fun lvQ ↦ ?_
  refine (fine_chalH ?_).bind fun st₄ ↦ ?_
  · rw [List.length_append, Vector.length_toList, QuotientRpm.length_rootWords]; omega
  intro Q hQ'
  refine wp_seq ((wp_getMsg _).2 fun m hm ↦ hm) fun m _ ↦ ?_
  have hlen := length_takeScalars m 5
  generalize takeScalars m 5 = p at hlen ⊢
  obtain ⟨vals, _⟩ := p
  refine (fine_chalH ?_).wp fun _ ↦ ?_
  · rw [List.length_append, Vector.length_toList, length_flatMap_scalarWord, hlen]; omega
  refine (fine_tree₀ h64 _ hσ.2).wp fun lvσ ↦ ?_
  refine (fine_opening h64 hr _ hW _).wp fun oW ↦ ?_
  refine (fine_opening h64 hr _ hσ _).wp fun oσ ↦ ?_
  exact (fine_opening h64 hr _ hQ _).wp fun oQ ↦ hQ' _

end Skeleton

/-! ## The deployed shapes -/

theorem length_ivPrefix (layoutId : QuotientRpm.Bytes32) (logN : ℕ) :
    (ivPrefix layoutId logN).length = 76 := by
  have h20 : "pcs-quotient-opening".toUTF8.toList.length = 20 := by decide +kernel
  simp only [ivPrefix, List.length_append, h20, LeanVM.Protocol.KeccakHash.wordBytes_length,
    Vector.length_toList]

theorem openOK_witnessShape (idW : QuotientRpm.Bytes32) : OpenOK 1488 1564 (witnessShape idW) :=
  ⟨by rw [witnessShape, length_ivPrefix], fun _ h ↦ absurd h List.not_mem_nil⟩

theorem openOK_quotientShape (idQ : QuotientRpm.Bytes32) :
    OpenOK 1488 1564 (quotientShape idQ) :=
  ⟨by rw [quotientShape, length_ivPrefix], fun _ h ↦ absurd h List.not_mem_nil⟩

theorem openOK_wiringShape (idσ : QuotientRpm.Bytes32) (rows : List (List UInt8))
    (hrows : ∀ r ∈ rows, r.length ≤ 1564) : OpenOK 1488 1564 (wiringShape idσ rows) :=
  ⟨by rw [wiringShape, length_ivPrefix], hrows⟩

/-! ## The prover's calls of `π` -/

open Common (QueryCostAtMost permutationCallCost keccak256OverPermutation queryPermutation
  DigestBytes)
open QuotientZk.DRpm (hashJ implJ proverJ coinR JTab)

section Transfer

/-- **Keccak-256 or a permutation call, with its completion**: `⌊n / 136⌋ + 1` calls of `π` for
`n` bytes, one for a state, the completion's coin nothing. -/
theorem cost_hashJ (t : Inp) (J : JTab) (c : ℕ) (hc : ∀ m, t = .inl m → m.length / 136 + 1 ≤ c)
    (h1 : 1 ≤ c) :
    QueryCostAtMost ((hashJ keccak256OverPermutation queryPermutation (coinR KSt)
      (coinR DigestBytes) t).run J) permutationCallCost c := by
  have hcoin : ∀ (α : Type) [SampleableType α],
      QueryCostAtMost (coinR α) permutationCallCost 0 :=
    fun α _ ↦ Common.isWeightBound_liftM_probComp _ (fun _ ↦ rfl) _
  rcases t with m | x
  · refine (Common.isWeightBound_keccakK_bind m (Q' := 0) fun d ↦ ?_).mono
      (by have := hc m rfl; omega)
    split
    · trivial
    · exact Common.QueryCostAtMost.mono
        (Common.QueryCostAtMost.bind (b := 0) (hcoin _) fun _ ↦ trivial) (by omega)
  · refine ((Common.isWeightBound_query permutationCallCost (.inr (.forward x))).bind (b := 0)
      fun y ↦ ?_).mono (by simp only [permutationCallCost]; omega)
    split
    · trivial
    · exact Common.QueryCostAtMost.mono
        (Common.QueryCostAtMost.bind (b := 0) (hcoin _) fun _ ↦ trivial) (by omega)

variable {S : Type} (P : Proto S Inp Out Msg Tbl Pos) (s : S)

/-- The prover's implementation, over Keccak-256 over `π`, `π` and the coins. -/
noncomputable abbrev implP :
    QueryImpl DSpec (StateT (List Out × JTab) (OracleComp Common.RandomPermutationOracles)) :=
  implJ P keccak256OverPermutation queryPermutation (coinR KSt) (coinR DigestBytes) s

theorem cost_implP_pub (t : Inp) (st : List Out × JTab) (c : ℕ)
    (hc : ∀ m, t = .inl m → m.length / 136 + 1 ≤ c) (h1 : 1 ≤ c) :
    QueryCostAtMost ((implP P s (.pub t)).run st) permutationCallCost c :=
  Common.isWeightBound_map _ (cost_hashJ t st.2 c hc h1)

theorem cost_implP_chal (t : Inp) (st : List Out × JTab) (c : ℕ)
    (hc : ∀ m, t = .inl m → m.length / 136 + 1 ≤ c) (h1 : 1 ≤ c) :
    QueryCostAtMost ((implP P s (.chal t)).run st) permutationCallCost c :=
  Common.isWeightBound_map _ (cost_hashJ t st.2 c hc h1)

theorem cost_implP_leaf (L : ℕ) (hrow : ∀ h k x, ∃ m, P.rowFn s h k x = .inl m ∧ m.length ≤ L)
    (t : Tbl) (x : Pos) (st : List Out × JTab) :
    QueryCostAtMost ((implP P s (.leaf t x)).run st) permutationCallCost (L / 136 + 1) := by
  show QueryCostAtMost (if st.1.length < P.cK t then pure (default, st) else _) _ _
  split
  · trivial
  · obtain ⟨m, hm, hlen⟩ := hrow (st.1.take (P.cK t)) t x
    refine Common.isWeightBound_map _ (cost_hashJ _ _ _ (fun m' hm' ↦ ?_) (by omega))
    rw [hm] at hm'
    cases hm'
    exact Nat.add_le_add_right (Nat.div_le_div_right hlen) _

/-- **The prover's run**: a computation of at most `N` operations whose Keccak-256 inputs are at
most `L` bytes on every path of passing messages, run by the prover whose messages pass and whose
leaves are at most `L` bytes, makes at most `N · (⌊L / 136⌋ + 1)` calls of `π`. -/
theorem cost_run_implP (L : ℕ) (mok : Msg → Prop) (hmsg : ∀ h, mok (P.msgFn s h))
    (hrow : ∀ h k x, ∃ m, P.rowFn s h k x = .inl m ∧ m.length ≤ L) {β : Type}
    (oa : OracleComp DSpec β) :
    ∀ (N : ℕ) (st : List Out × JTab), IsTotalQueryBound oa N → Wp mok L oa (fun _ ↦ True) →
      QueryCostAtMost ((simulateQ (implP P s) oa).run st) permutationCallCost
        (N * (L / 136 + 1)) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro _ _ _ _; trivial
  | query_bind op k ih =>
    intro N st hN hW
    rw [isTotalQueryBound_query_bind_iff] at hN
    obtain ⟨hN1, hNk⟩ := hN
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    have hNc : (L / 136 + 1) + (N - 1) * (L / 136 + 1) ≤ N * (L / 136 + 1) := by
      obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
      rw [Nat.add_sub_cancel, Nat.succ_mul, Nat.add_comm]
    have hlt : (N - 1) * (L / 136 + 1) ≤ N * (L / 136 + 1) :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    rcases op with (m | x) | _ | ⟨t, x⟩ | (m | x)
    · rw [wp_pubH] at hW
      refine ((cost_implP_pub P s _ st _ (fun m' hm' ↦ ?_) (by omega)).bind fun z ↦
        ih z.1 (N - 1) z.2 (hNk z.1) (hW.2 z.1)).mono hNc
      cases hm'
      exact Nat.add_le_add_right (Nat.div_le_div_right hW.1) _
    · rw [wp_pubF] at hW
      exact ((cost_implP_pub P s _ st _ (fun _ h ↦ by cases h) (by omega)).bind fun z ↦
        ih z.1 (N - 1) z.2 (hNk z.1) (hW z.1)).mono hNc
    · rw [wp_msg] at hW
      show QueryCostAtMost (pure (P.msgFn s st.1, st) >>= fun z ↦
        (simulateQ (implP P s) (k z.1)).run z.2) _ _
      rw [pure_bind]
      exact (ih _ (N - 1) st (hNk _) (hW _ (hmsg st.1))).mono hlt
    · rw [wp_leaf] at hW
      exact ((cost_implP_leaf P s L hrow t x st).bind fun z ↦
        ih z.1 (N - 1) z.2 (hNk z.1) (hW z.1)).mono hNc
    · rw [wp_chalH] at hW
      refine ((cost_implP_chal P s _ st _ (fun m' hm' ↦ ?_) (by omega)).bind fun z ↦
        ih z.1 (N - 1) z.2 (hNk z.1) (hW.2 z.1)).mono hNc
      cases hm'
      exact Nat.add_le_add_right (Nat.div_le_div_right hW.1) _
    · rw [wp_chalF] at hW
      exact ((cost_implP_chal P s _ st _ (fun _ h ↦ by cases h) (by omega)).bind fun z ↦
        ih z.1 (N - 1) z.2 (hNk z.1) (hW z.1)).mono hNc

/-- **The prover's calls of `π`**: a skeleton of at most `N` operations hashing at most `L` bytes,
run by a prover whose messages pass and whose leaves are at most `L` bytes. -/
theorem cost_proverJ (L : ℕ) (mok : Msg → Prop) (hmsg : ∀ h, mok (P.msgFn s h))
    (hrow : ∀ h k x, ∃ m, P.rowFn s h k x = .inl m ∧ m.length ≤ L) {β : Type}
    (skel : OracleComp DSpec β) (N : ℕ) (hN : IsTotalQueryBound skel N) (hW : Fine mok L skel) :
    QueryCostAtMost (proverJ P keccak256OverPermutation queryPermutation (coinR KSt)
      (coinR DigestBytes) s skel) permutationCallCost (N * (L / 136 + 1)) := by
  unfold proverJ
  rw [StateT.run'_eq]
  exact Common.isWeightBound_map _ (cost_run_implP P s L mok hmsg hrow skel N _ hN hW.wp_self)

end Transfer

end QuotientZk.Deployed.Budget

/-! ## The deployed prover's messages -/

namespace QuotientZk.Instance

set_option linter.unusedSectionVars false

open Polynomial QuotientSecurity QuotientSecurity.Hiding QuotientZk.Joint
open QuotientZk.Deployed (Out Msg Item Tbl Pos)
open QuotientZk.Deployed.Budget

section Claims

variable {K E : Type} [Field K] [Field E] [Algebra K E] [DecidableEq E] [CharP E 2] [Fintype E]
  (rep : Rep K E) (P₀ : Params E) (gK : Fin 4 → Polynomial K) (van : Polynomial K)
  (stmt : Fin P₀.words → E) (Y : E) (TW : (Fin 4 → Fin 3 → K) → ιW → YW → K)
  (TQ : E × E × E → (Fin 4 → Fin 3 → K) → ιQ → YQ → K)

omit [Algebra K E] [DecidableEq E] [CharP E 2] [Fintype E] in
theorem length_scalarsLE (l : List E) : (scalarsLE rep l).length = 24 * l.length := by
  unfold scalarsLE
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, length_scalarLE, ih, List.length_cons]
    ring

omit [Algebra K E] [CharP E 2] [Fintype E] in
/-- **The claims' bytes**: `26`, `25` and `62` scalars, at most `1488` bytes. -/
theorem msgOK_claimMsg (k : ℕ) (c : DChal E) (v : Vals E) :
    MsgOK 1536 1488 (claimMsg rep P₀ stmt Y k c v) := by
  unfold claimMsg
  split_ifs
  · refine msgOK_singleton (show (scalarsLE rep _).length ≤ 1488 from ?_)
    rw [length_scalarsLE]
    simp [Implementation.modelWitness]
  · refine msgOK_singleton (show (scalarsLE rep _).length ≤ 1488 from ?_)
    rw [length_scalarsLE]
    simp [Implementation.modelWiring]
  · refine msgOK_singleton (show (scalarsLE rep _).length ≤ 1488 from ?_)
    rw [length_scalarsLE]
    simp [Implementation.modelQuotient, Implementation.modelSum]
  · exact msgOK_nil

/-- **The deployed prover's messages pass** when its renderer's do. -/
theorem msgOK_PbMsg (R : Renderer K E) (hR : ∀ k h va, MsgOK 1536 1488 (R k h va)) (s : RandD K)
    (h : List Out) : MsgOK 1536 1488 (PbMsg rep P₀ gK van stmt Y TW TQ R s h) :=
  (msgOK_claimMsg rep P₀ stmt Y _ _ _).append (hR _ _ _)

omit [CharP E 2] [Fintype E] in
/-- **A secret leaf is `512` bytes.** -/
theorem length_PbRow (s : RandD K) (h : List Out) (k : Tbl) (x : Pos) :
    (PbRow rep P₀ Y TW TQ s h k x).length = 512 := by
  unfold PbRow
  split
  · exact length_rowBytes rep (by rw [lanes_W]; norm_num) _
  · exact length_rowBytes rep (by rw [lanes_Q]; norm_num) _

end Claims

end QuotientZk.Instance

/-! ## WHIR's honest prover as the renderer -/

namespace PcsQuotient.EndToEnd.Render

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Complete
open QuotientZk.Deployed (Out Msg Item)
open QuotientZk.Deployed.Budget

/-! ## The honest script commits rows of at most `192` words -/

/-- Every matrix the script commits has rows of at most `W` words. -/
def WordsLE (W : ℕ) {β : Type} : Script β → Prop
  | .ret _ => True
  | .send _ k => WordsLE W k
  | .sample k => ∀ c, WordsLE W (k c)
  | .grind k => WordsLE W k
  | .commit w k => (∀ p, (w p).length ≤ W) ∧ WordsLE W k
  | .query k => ∀ rows, WordsLE W (k rows)

namespace WordsLE

variable {W : ℕ} {β γ : Type}

theorem bind {x : Script β} {f : β → Script γ} (hx : WordsLE W x) (hf : ∀ a, WordsLE W (f a)) :
    WordsLE W (x >>= f) := by
  show WordsLE W (x.bind f)
  induction x with
  | ret a => exact hf a
  | send y k ih => exact ih hx
  | sample k ih => exact fun c ↦ ih c (hx c)
  | grind k ih => exact ih hx
  | commit w k ih => exact ⟨hx.1, ih hx.2⟩
  | query k ih => exact fun rows ↦ ih rows (hx rows)

theorem ret' (a : β) : WordsLE W (pure a : Script β) := trivial

theorem sendE (x : E) : WordsLE W (Script.sendE x) := trivial

theorem sendList : ∀ xs : List E, WordsLE W (Script.sendList xs)
  | [] => trivial
  | _ :: xs => sendList xs

theorem sampleE : WordsLE W Script.sampleE := fun _ ↦ trivial

theorem sampleN : ∀ n : ℕ, WordsLE W (Script.sampleN n)
  | 0 => trivial
  | n + 1 => bind sampleE fun _ ↦ bind (sampleN n) fun _ ↦ trivial

theorem grindS : WordsLE W Script.grindS := trivial

theorem queryS : WordsLE W Script.queryS := fun _ ↦ trivial

theorem commitS {w : Word} (hw : ∀ p, (w p).length ≤ W) : WordsLE W (Script.commitS w) :=
  ⟨hw, trivial⟩

end WordsLE

theorem wordsLE_roundA {W : ℕ} (claim : E) (Wt g : Array E) :
    WordsLE W (LeanVM.Prover.roundA claim Wt g) :=
  WordsLE.bind (WordsLE.sendE _) fun _ ↦ WordsLE.bind (WordsLE.sendList _) fun _ ↦ trivial

theorem wordsLE_foldRoundsA {W : ℕ} :
    ∀ (n : ℕ) (s : WhirState) (lf : List E) (Wt gt : Array E),
      WordsLE W (LeanVM.Prover.foldRoundsA n s lf Wt gt)
  | 0, _, _, _, _ => trivial
  | n + 1, s, lf, Wt, gt => by
    simp only [LeanVM.Prover.foldRoundsA]
    exact WordsLE.bind WordsLE.sampleE fun _ ↦ WordsLE.bind (wordsLE_roundA _ _ _) fun _ ↦
      wordsLE_foldRoundsA n _ _ _ _

theorem wordsLE_tailRoundsA {W : ℕ} :
    ∀ (n : ℕ) (quad : List E) (Wt gt : Array E),
      WordsLE W (LeanVM.Prover.tailRoundsA n quad Wt gt)
  | 0, _, _, _ => trivial
  | n + 1, quad, Wt, gt => by
    simp only [LeanVM.Prover.tailRoundsA]
    refine WordsLE.bind WordsLE.sampleE fun c ↦ ?_
    split
    · trivial
    · exact WordsLE.bind (wordsLE_roundA _ _ _) fun _ ↦ wordsLE_tailRoundsA n _ _ _

theorem wordsLE_sampleQueriesS {W : ℕ} (depth : ℕ) :
    ∀ (fuel remaining : ℕ), WordsLE W (LeanVM.Prover.sampleQueriesS depth fuel remaining)
  | 0, _ => trivial
  | fuel + 1, remaining => by
    simp only [LeanVM.Prover.sampleQueriesS]
    split
    · trivial
    · exact WordsLE.bind WordsLE.sampleE fun _ ↦
        WordsLE.bind (wordsLE_sampleQueriesS depth fuel _) fun _ ↦ trivial

theorem length_levelWordFast (κ k R : ℕ) (g : Array E) (p : ℕ) :
    (LeanVM.Prover.levelWordFast κ k R g p).length = 3 * 2 ^ k := by
  unfold LeanVM.Prover.levelWordFast LeanVM.Prover.levelWordFast.levelWordOf
  split
  · simp [List.length_flatMap, mul_comm]
  · simp [LeanVM.Protocol.Whir.Complete.levelWord, LeanVM.Protocol.Whir.Complete.laneCodes,
      LeanVM.Protocol.Whir.Complete.limbsOf, List.length_flatMap, Function.comp_def,
      List.sum_replicate, mul_comm]

/-- **The WHIR levels commit rows of at most `192` words** when every level folds at most `6`
variables (`3 · 2^fold` words a row). -/
theorem wordsLE_levelsA (μ : ℕ) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState) (Wt gt : Array E),
      (∀ l ∈ levels, l.fold ≤ 6) → WordsLE 192 (LeanVM.Prover.levelsA μ index levels s Wt gt) := by
  intro levels
  induction levels with
  | nil => intros; trivial
  | cons level rest ih =>
    intro index s Wt gt hf
    cases rest with
    | nil =>
      rw [LeanVM.Prover.levelsA]
      refine WordsLE.bind (wordsLE_foldRoundsA _ _ _ _ _) fun ⟨s', lf, Wt', g'⟩ ↦ ?_
      dsimp only
      refine WordsLE.bind (WordsLE.sendList _) fun _ ↦
        WordsLE.bind (WordsLE.ret' _) fun ⟨r, pd, tb⟩ ↦ ?_
      dsimp only
      refine WordsLE.bind WordsLE.grindS fun _ ↦ ?_
      refine WordsLE.bind (wordsLE_sampleQueriesS _ _ _) fun _ ↦ ?_
      refine WordsLE.bind WordsLE.sampleE fun _ ↦ ?_
      refine WordsLE.bind WordsLE.queryS fun _ ↦ ?_
      exact WordsLE.bind (wordsLE_roundA _ _ _) fun _ ↦ wordsLE_tailRoundsA _ _ _ _
    | cons next rest =>
      have hn : next.fold ≤ 6 := hf next (by simp)
      rw [LeanVM.Prover.levelsA]
      refine WordsLE.bind (wordsLE_foldRoundsA _ _ _ _ _) fun ⟨s', lf, Wt', g'⟩ ↦ ?_
      dsimp only
      refine WordsLE.bind (WordsLE.commitS fun p ↦ ?_) fun _ ↦ ?_
      · rw [length_levelWordFast]
        have : 2 ^ next.fold ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hn
        omega
      refine WordsLE.bind (WordsLE.sampleN _) fun _ ↦ WordsLE.bind (WordsLE.sendE _) fun _ ↦
        WordsLE.bind (wordsLE_roundA _ _ _) fun _ ↦ WordsLE.bind (WordsLE.ret' _)
          fun ⟨r, pd, tb⟩ ↦ ?_
      dsimp only
      refine WordsLE.bind WordsLE.grindS fun _ ↦ ?_
      refine WordsLE.bind (wordsLE_sampleQueriesS _ _ _) fun _ ↦ ?_
      refine WordsLE.bind WordsLE.sampleE fun _ ↦ ?_
      refine WordsLE.bind WordsLE.queryS fun _ ↦ ?_
      exact WordsLE.bind (wordsLE_roundA _ _ _) fun _ ↦
        ih _ _ _ _ fun l hl ↦ hf l (List.mem_cons_of_mem _ hl)

/-- **The honest opening script commits rows of at most `192` words** (`ladder_folds`). -/
theorem wordsLE_openingScript (L : PcsQuotient.Layout) (stack : Array K)
    (claims : List PcsQuotient.Claim) : WordsLE 192 (PcsQuotient.openingScript L stack claims) := by
  unfold PcsQuotient.openingScript
  refine WordsLE.bind WordsLE.sampleE fun c ↦ ?_
  split
  · trivial
  · rename_i config hc
    exact WordsLE.bind (wordsLE_roundA _ _ _) fun _ ↦
      wordsLE_levelsA _ _ _ _ _ _ (LeanVM.Rpm.ladder_folds _ _ _ hc)

/-! ## The prover's runner -/

/-- The runner's current node commits rows of at most `W` words. -/
def OWordsLE (W : ℕ) {β : Type} : Option (Script β) → Prop
  | none => True
  | some S => WordsLE W S

section OWords

variable {W : ℕ} {β : Type}

theorem oWordsLE_afterSend {S : Option (Script β)} (h : OWordsLE W S) :
    OWordsLE W (Script.afterSend S) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> trivial

theorem oWordsLE_afterSample (c : E) {S : Option (Script β)} (h : OWordsLE W S) :
    OWordsLE W (Script.afterSample c S) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> first | trivial | exact h c

theorem oWordsLE_afterGrind {S : Option (Script β)} (h : OWordsLE W S) :
    OWordsLE W (Script.afterGrind S) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> trivial

theorem oWordsLE_afterCommit {S : Option (Script β)} (h : OWordsLE W S) :
    OWordsLE W (Script.afterCommit S) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> first | trivial | exact h.2

theorem oWordsLE_afterQuery (rows : List (List K)) {S : Option (Script β)} (h : OWordsLE W S) :
    OWordsLE W (Script.afterQuery rows S) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> first | trivial | exact h rows

theorem length_wordOf_le {S : Option (Script β)} (h : OWordsLE W S) (p : ℕ) :
    (Script.wordOf S p).length ≤ W := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> first | exact Nat.zero_le _ | exact h.1 p

end OWords


theorem wordsLE_roundMsgA {W : ℕ} (claim : E) (m : E × E) : WordsLE W (roundMsgA claim m) :=
  WordsLE.bind (WordsLE.sendE _) fun _ ↦ WordsLE.bind (WordsLE.sendList _) fun _ ↦ trivial

theorem wordsLE_laneFoldsH {W : ℕ} (lane : ℕ → E × E) :
    ∀ (n j : ℕ) (s : WhirState) (lf : List E) (Wt : Array E),
      WordsLE W (laneFoldsH lane n j s lf Wt)
  | 0, _, _, _, _ => trivial
  | n + 1, j, s, lf, Wt => by
    rw [laneFoldsH]
    exact WordsLE.bind WordsLE.sampleE fun _ ↦ WordsLE.bind (wordsLE_roundMsgA _ _) fun _ ↦
      wordsLE_laneFoldsH lane n _ _ _ _

/-- **A level's tail commits rows of at most `192` words** (`wordsLE_levelsA`'s step). -/
theorem wordsLE_levelTailA (μ index : ℕ) (level : Whir.Level) (rest : List Whir.Level)
    (s : WhirState) (lf : List E) (Wt g : Array E) (hf : ∀ l ∈ rest, l.fold ≤ 6) :
    WordsLE 192 (levelTailA μ index level rest s lf Wt g) := by
  unfold levelTailA
  cases rest with
  | nil =>
    dsimp only
    refine WordsLE.bind (WordsLE.sendList _) fun _ ↦
      WordsLE.bind (WordsLE.ret' _) fun ⟨r, pd, tb⟩ ↦ ?_
    dsimp only
    refine WordsLE.bind WordsLE.grindS fun _ ↦ ?_
    refine WordsLE.bind (wordsLE_sampleQueriesS _ _ _) fun _ ↦ ?_
    refine WordsLE.bind WordsLE.sampleE fun _ ↦ ?_
    refine WordsLE.bind WordsLE.queryS fun _ ↦ ?_
    exact WordsLE.bind (wordsLE_roundA _ _ _) fun _ ↦
      wordsLE_tailRoundsA _ _ _ _
  | cons next rest =>
    have hn : next.fold ≤ 6 := hf next List.mem_cons_self
    dsimp only
    refine WordsLE.bind (WordsLE.commitS fun p ↦ ?_) fun _ ↦ ?_
    · rw [length_levelWordFast]
      have : 2 ^ next.fold ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hn
      omega
    refine WordsLE.bind (WordsLE.sampleN _) fun _ ↦ WordsLE.bind (WordsLE.sendE _) fun _ ↦
      WordsLE.bind (wordsLE_roundA _ _ _) fun _ ↦ WordsLE.bind (WordsLE.ret' _)
        fun ⟨r, pd, tb⟩ ↦ ?_
    dsimp only
    refine WordsLE.bind WordsLE.grindS fun _ ↦ ?_
    refine WordsLE.bind (wordsLE_sampleQueriesS _ _ _) fun _ ↦ ?_
    refine WordsLE.bind WordsLE.sampleE fun _ ↦ ?_
    refine WordsLE.bind WordsLE.queryS fun _ ↦ ?_
    exact WordsLE.bind (wordsLE_roundA _ _ _) fun _ ↦
      wordsLE_levelsA _ _ _ _ _ _ hf

/-- **The hybrid opening commits rows of at most `192` words.** -/
theorem wordsLE_hybridScript (L : PcsQuotient.Layout) (claims : List PcsQuotient.Claim)
    (lane : ℕ → E × E) (f1 : Array E) : WordsLE 192 (hybridScript L claims lane f1) := by
  unfold hybridScript
  refine WordsLE.bind WordsLE.sampleE fun c ↦ ?_
  split
  · trivial
  · trivial
  · rename_i level rest hc
    have hf := LeanVM.Rpm.ladder_folds _ _ _ hc
    refine WordsLE.bind (wordsLE_roundMsgA _ _) fun _ ↦ ?_
    refine WordsLE.bind (wordsLE_laneFoldsH _ _ _ _ _ _) fun r ↦ ?_
    obtain ⟨s, lf, Wt⟩ := r
    dsimp only
    refine WordsLE.bind WordsLE.sampleE fun _ ↦ ?_
    refine WordsLE.bind (wordsLE_roundA _ _ _) fun _ ↦ ?_
    exact wordsLE_levelTailA _ _ _ _ _ _ _ _ fun l hl ↦ hf l (List.mem_cons_of_mem _ hl)

theorem oWordsLE_sendsN : ∀ (n : ℕ) {S : Option (Script Unit)}, OWordsLE 192 S →
    OWordsLE 192 (sendsN n S).2
  | 0, _, h => h
  | n + 1, _, h => oWordsLE_sendsN n (oWordsLE_afterSend h)

theorem length_flatMap_kBytes (l : List K) : (l.flatMap kBytes).length = 8 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons, kBytes, wordBytes_length]
    ring

/-- The drive's state passes: the script commits rows of at most `192` words, the messages so far
and the current one pass. -/
def RunOK (Lb : ℕ) (st : RunSt) : Prop :=
  OWordsLE 192 st.script ∧ (∀ m ∈ st.done, MsgOK 1536 Lb m) ∧ MsgOK 1536 Lb st.acc

theorem runOK_end {Lb : ℕ} {st : RunSt} (h : RunOK Lb st) :
    ∀ m ∈ st.done ++ [st.acc], MsgOK 1536 Lb m := by
  intro m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact h.2.1 m hm
  · rw [List.mem_singleton] at hm
    exact hm ▸ h.2.2

/-- **The drive's messages pass.** -/
theorem evRun_ok {Lb : ℕ} : ∀ (evs : List Ev) (chs : List Out) (st : RunSt), RunOK Lb st →
    ∀ m ∈ evRun evs chs st, MsgOK 1536 Lb m
  | [], chs, st, h => by rw [evRun]; exact runOK_end h
  | .draw :: evs, [], st, h => by rw [evRun]; exact runOK_end h
  | .draw :: evs, o :: chs, st, h => by
    intro m hm
    refine evRun_ok evs chs _ ?_ m hm
    exact ⟨oWordsLE_afterSample _ h.1, runOK_end h, msgOK_nil⟩
  | .posDraw :: evs, [], st, h => by rw [evRun]; exact runOK_end h
  | .posDraw :: evs, o :: chs, st, h => by
    intro m hm
    refine evRun_ok evs chs _ ?_ m hm
    exact ⟨oWordsLE_afterSample _ h.1, runOK_end h, msgOK_nil⟩
  | .send k :: evs, chs, st, h => by
    intro m hm
    refine evRun_ok evs chs _ ?_ m hm
    exact ⟨oWordsLE_sendsN k h.1, h.2.1, h.2.2.append (msgOK_singleton trivial)⟩
  | .commit d :: evs, chs, st, h => by
    intro m hm
    refine evRun_ok evs chs _ ?_ m hm
    refine ⟨oWordsLE_afterCommit h.1, h.2.1,
      h.2.2.append (msgOK_singleton ?_)⟩
    intro r hr
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hr
    rw [length_flatMap_kBytes]
    have := length_wordOf_le h.1 i
    omega
  | .grind :: evs, chs, st, h => by
    intro m hm
    refine evRun_ok evs chs _ ?_ m hm
    exact ⟨oWordsLE_afterGrind h.1, h.2.1, h.2.2⟩
  | .opened lvl q b :: evs, chs, st, h => by
    intro m hm
    refine evRun_ok evs chs _ ?_ m hm
    exact ⟨oWordsLE_afterQuery _ h.1, h.2.1,
      h.2.2.append (msgOK_singleton trivial)⟩

theorem getLastD_ok {P : Msg → Prop} :
    ∀ (l : List Msg) (d : Msg), P d → (∀ m ∈ l, P m) → P (l.getLastD d)
  | [], d, hd, _ => by rw [List.getLastD_nil]; exact hd
  | a :: l, _, _, hl => by
    rw [List.getLastD_cons]
    exact getLastD_ok l a (hl a List.mem_cons_self) fun m hm ↦ hl m (List.mem_cons_of_mem _ hm)

/-- **An opening's message passes** when its script commits rows of at most `192` words. -/
theorem msgOK_openingMsg {Lb : ℕ} (sh : QuotientZk.Deployed.OpenShape) (S : Script Unit)
    (word0 : Word) (chs : List Out) (hS : WordsLE 192 S) :
    MsgOK 1536 Lb (openingMsg sh S word0 chs) :=
  getLastD_ok _ _ msgOK_nil (evRun_ok _ chs _ ⟨hS, fun _ h ↦ absurd h List.not_mem_nil, msgOK_nil⟩)

/-- **WHIR's honest prover sends rows of at most `1536` bytes** (`192` words) and no claims'
bytes. -/
theorem msgOK_whirRenderer {Lb : ℕ} (rep : QuotientZk.Instance.Rep K E) (stmt : Statement)
    (k : ℕ) (h : List Out) (va : QuotientZk.Instance.JV K E) :
    MsgOK 1536 Lb (whirRenderer rep stmt k h va) := by
  unfold whirRenderer
  split_ifs
  · exact msgOK_singleton trivial
  all_goals split
  all_goals first
    | exact msgOK_nil
    | exact msgOK_openingMsg _ _ _ _ (wordsLE_hybridScript _ _ _ _)
    | exact msgOK_openingMsg _ _ _ _ (wordsLE_openingScript _ _ _)

end PcsQuotient.EndToEnd.Render

/-! ## The budget -/

namespace PcsQuotient.EndToEnd

open OracleComp OracleSpec Common Polynomial QuotientSecurity
open QuotientZk.Joint QuotientZk.Instance
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt DSpec)
open QuotientZk.Deployed.Budget (Fine MsgOK fine_tree₀ fine_skel openOK_witnessShape
  openOK_wiringShape openOK_quotientShape cost_proverJ)
open LeanVM.Parameters Primitives

/-- **The statement's prover's skeleton hashes at most `1564` bytes** (an IV: `76 + 1488`) on every
path whose messages pass, given the wiring codeword's rows of at most `1564` bytes. -/
theorem fine_skelSetup (stmtBytes : Vector UInt8 64) (idW idσ idQ : QuotientRpm.Bytes32)
    (rowsW : List (List UInt8)) (hrowsW : ∀ r ∈ rowsW, r.length ≤ 1564) :
    Fine (MsgOK 1536 1488) 1564 (skelSetup stmtBytes idW idσ idQ rowsW) := by
  unfold skelSetup skelWith
  refine Fine.bind (fine_tree₀ (by norm_num) _ hrowsW) fun lv ↦ ?_
  refine fine_skel (by norm_num) (by norm_num) _ ?_ ?_ ?_
  · exact openOK_witnessShape idW
  · exact openOK_wiringShape idσ rowsW hrowsW
  · exact openOK_quotientShape idQ

/-- **`hprover` for any renderer whose messages pass**: the statement's prover makes at most
`(2^24 + 2^70) · 12` calls of `π` (at most `2^24 + 2^70` operations, `skelSetup_queryBound`, each a
Keccak-256 of at most `1564` bytes, `12` blocks, or one permutation call). -/
theorem hprover_of_renderer (R : QuotientZk.Instance.Renderer K E)
    (hR : ∀ k h va, MsgOK 1536 1488 (R k h va)) (stmtBytes : Statement → Vector UInt8 64)
    (idW idσ idQ : QuotientRpm.Bytes32) (rowsW : List (List UInt8))
    (hrows : rowsW.length = 2 ^ 19) (hrowsW : ∀ r ∈ rowsW, r.length ≤ 1564) :
    ∀ stmt w, Relation stmt w → ∀ s,
      QueryCostAtMost (QuotientZk.DRpm.proverJ (deployedJD R stmt w).P keccak256OverPermutation
        queryPermutation (QuotientZk.DRpm.coinR KSt) (QuotientZk.DRpm.coinR DigestBytes) s
        (skelSetup (stmtBytes stmt) idW idσ idQ rowsW)) permutationCallCost
        ((2 ^ 24 + 2 ^ 70) * 12) := by
  intro stmt w _ s
  have h := cost_proverJ (deployedJD R stmt w).P s 1564 (MsgOK 1536 1488)
    (fun h ↦ QuotientZk.Instance.msgOK_PbMsg deployedRep P₀D (gKD w) vanD (stmtWD stmt) F192.Y
      (TWD w) (TQD w) R hR s h)
    (fun h k x ↦ ⟨_, rfl, (QuotientZk.Instance.length_PbRow deployedRep P₀D F192.Y (TWD w)
      (TQD w) s h k x).trans_le (by norm_num)⟩)
    _ _ (skelSetup_queryBound (stmtBytes stmt) idW idσ idQ rowsW hrows)
    (fine_skelSetup (stmtBytes stmt) idW idσ idQ rowsW hrowsW)
  have e : (1564 : ℕ) / 136 + 1 = 12 := by norm_num
  rwa [e] at h

/-- **`hprover` of `zeroKnowledge_deployed_final` with WHIR's honest prover as the renderer**, at
`Qp = (2^24 + 2^70) · 12`, given the wiring codeword's rows of at most `1564` bytes (its `64`-word
leaf images are `512`). -/
theorem hprover_whir (stmtBytes : Statement → Vector UInt8 64) (idW idσ idQ : QuotientRpm.Bytes32)
    (rowsW : List (List UInt8)) (hrows : rowsW.length = 2 ^ 19)
    (hrowsW : ∀ r ∈ rowsW, r.length ≤ 1564) :
    ∀ stmt w, Relation stmt w → ∀ s,
      QueryCostAtMost (QuotientZk.DRpm.proverJ
          (deployedJD (Render.whirRenderer deployedRep stmt) stmt w).P keccak256OverPermutation
        queryPermutation (QuotientZk.DRpm.coinR KSt) (QuotientZk.DRpm.coinR DigestBytes) s
        (skelSetup (stmtBytes stmt) idW idσ idQ rowsW)) permutationCallCost
        ((2 ^ 24 + 2 ^ 70) * 12) :=
  fun stmt w hw ↦ hprover_of_renderer (Render.whirRenderer deployedRep stmt)
    (Render.msgOK_whirRenderer deployedRep stmt) stmtBytes idW idσ idQ rowsW hrows hrowsW stmt w hw

end PcsQuotient.EndToEnd

/-- info: 'PcsQuotient.EndToEnd.hprover_of_renderer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.hprover_of_renderer

/-- info: 'PcsQuotient.EndToEnd.hprover_whir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsQuotient.EndToEnd.hprover_whir
