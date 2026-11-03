-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The statement is `Fs.lean`'s `UniFinal`;
-- the verifier's batch is `formal/UniStatement`'s `batch` (`CodeBatch.lean`'s `batchPure`).
import UniSound.CodeLink
import UniSound.PendingLink
import UniSound.Final

/-!
# The last link (`UniFinal`): the batch's terminal check with true claims is the last state

**`uniFinal`**: for the identity model whose batch products are the verifier's (`batchProd`: the
`λ^k`-weighted products of each commitment's claim's weight, read on the cube, and its stack
zero-extended to the batch's variables, then `λ³` times the pending matrices' term `Gext · Llift`;
`batchTargetOf` its claimed sum), the verifier's checks on a completed transcript (the terminal
`sum + λ³ value ext + last = 0` collected) with true claims (`ClaimsHold`) make the sumcheck's last
claim the partial sum at its point (`SumState`).

The algebra is `terminal_sumState` (independent of the transcript): the sumcheck's decoded rounds
are `claimAfter`/`pointAfter` (`decodeSC_none`), the full point's partial sum is
`Σ_k λ^k fold(W_k) fold(C_k) + λ³ fold(Gext) fold(Llift)` (`ProdSum.T_full`), each stack's fold is
its point claim times the zero extension (`foldAll_stackExt`), the pending term's is the terminal
(`pendingTerminalLink`).

**Hypotheses** (named, beyond the identity model's batch being the verifier's):

* `WeightMle`: each claim's weight, at the batch's point, is the fold (multilinear extension) of
  its values on the cube. **Not true in every case**: `weightAt` reads a `q_flock` slot term's row on
  `8 + |point|` coordinates, and `combine` replaces a point by a longer one it is a prefix of; when
  the slot terms' point `y(t)` is a prefix of another `C1` point (`w(t)`'s first coordinates, Flock's
  slices' point: a polynomial coincidence in `t`), the row overlaps the selector's coordinates and
  the weight is not multilinear. Outside these `t` (and the ring-switch term's `towerWeightAt`),
  unproved here.
* `LayoutVarsSmall`: the stacks have fewer than `256` variables (a layout word's byte).
* `FlockPendingShaped`: Flock's pending reduction has its shape (`Pending.Shaped`) and the slices.
-/

namespace UniSound

open UniStatement LeanVM.Parameters LeanVM.Semantics Finset FlockSound.Uni

/-! ## The sumcheck's decoded rounds -/

theorem decodeMsg_none_two (c a b : E) : decodeMsg c none [a, b] = roundCoeffs c a b := by
  simp [decodeMsg, roundCoeffs, esum]

/-- The batch's rounds as `claimAfter` reads them. -/
def roundsOf (d : Done) : List (List E × List E) := d.map fun x => (x.1.2, x.2)

/-- **The batching sumcheck's decoded rounds** are `pointAfter`, `claimAfter`. -/
theorem decodeSC_none (c : E) : ∀ (d : Done), (∀ x ∈ d, x.1.2.length = 2) →
    decodeSC c (List.replicate d.length none) d = (pointAfter (roundsOf d), claimAfter c (roundsOf d))
  | [], _ => rfl
  | r :: d, h => by
    obtain ⟨a, b, hab⟩ : ∃ a b, r.1.2 = [a, b] := by
      have h2 := h r (List.mem_cons_self ..)
      match hr : r.1.2, h2 with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    simp only [List.length_cons, List.replicate_succ, decodeSC, roundsOf, List.map_cons, pointAfter,
      claimAfter, hab, decodeMsg_none_two, List.getD_cons_zero, List.getD_cons_succ]
    have ih := decodeSC_none (polyEval (roundCoeffs c a b) (r.2.headD 0)) d
      (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [ih]
    rfl

/-! ## The batch's products and their terminal -/

/-- **The batch's products** (`ProdSum`): for each combined claim `k`, `λ^k` times its weight read on
the cube's points and its stack zero-extended to the batch's variables; then `λ^n` times the
pending matrices' term `Gext · Llift`. -/
noncomputable def prodOf (cmb : List (Commitment × Combined)) (L : List (Commitment × StackLayout))
    (ringMap : Option (List E)) (p : Flock.Pending) (stk : Commitment → Stk) (lam : E) : ProdSum where
  vars := varsOf L
  n := cmb.length + 1
  coef k := lam ^ k
  A k u := if k < cmb.length then
      weightAt (cmb.getD k default).2 (layoutOf L (cmb.getD k default).1) (bitsE u (varsOf L)) ringMap
    else Pending.Gext p u
  B k u := if k < cmb.length then
      (if u < 2 ^ (layoutOf L (cmb.getD k default).1).vars then ofK (stk (cmb.getD k default).1 u) else 0)
    else Pending.Llift p u

/-- The batch's claimed sum: `Σ_k λ^k v_k + λ^n claim`. -/
def targetOf (cmb : List (Commitment × Combined)) (lam : E) (p : Flock.Pending) : E :=
  (batchTarget cmb lam).1 + (batchTarget cmb lam).2 * p.claim

theorem two_eq_zero_E : (2 : E) = 0 := CharTwo.two_eq_zero

theorem eq_of_add_eq_zero_char2 {a b : E} (h : a + b = 0) : b = a := by
  linear_combination h - a * two_eq_zero_E

/-- A stack zero-extended folds to its point claim times the zero extension. -/
theorem foldAll_stackExt (c : Stk) (R : ℕ) (r : List E) (hR : R ≤ r.length) :
    foldAll (fun u => if u < 2 ^ R then ofK (c u) else 0) r 0 =
      mleStk c R (r.take R) * cubeEq (r.drop R) (r.length - R) 0 := by
  rw [foldAll_ext r R hR (fun u => ofK (c u))]
  congr 1
  unfold mleStk
  rw [Fin.sum_univ_eq_sum_range (fun x => cubeEq (r.take R) R x * ofK (c x))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [cubeEq_take]

theorem layoutOf_vars_le (L : List (Commitment × StackLayout)) (c : Commitment) :
    (layoutOf L c).vars ≤ varsOf L := by
  unfold layoutOf varsOf
  cases h : L.find? (fun x => x.1 == c) with
  | none => exact Nat.zero_le _
  | some x =>
    have hx := List.mem_of_find?_eq_some h
    simp only [Option.map_some, Option.getD_some]
    have key : ∀ (l : List (Commitment × StackLayout)) (a : ℕ), x ∈ l →
        x.2.vars ≤ (l.map fun y => y.2.vars).foldl max a := by
      intro l
      induction l with
      | nil => intro a h; simp at h
      | cons y l ih =>
        intro a h
        simp only [List.map_cons, List.foldl_cons]
        rcases List.mem_cons.mp h with rfl | h
        · have : ∀ (l : List ℕ) (b : ℕ), b ≤ l.foldl max b := by
            intro l
            induction l with
            | nil => intro b; simp
            | cons z l ih' => intro b; exact (le_max_left b z).trans (ih' _)
          exact (le_max_right a x.2.vars).trans (this _ _)
        · exact ih _ h
    exact key L 0 hx

/-- **The batch's terminal check with true claims is the last state** (the algebra of `UniFinal`). -/
theorem terminal_sumState (cmb : List (Commitment × Combined)) (L : List (Commitment × StackLayout))
    (bitSlice : Option Combined) (ringMap : Option (List E)) (p : Flock.Pending) (fp : List E) (lam : E)
    (brs : Done) (tl : List E) (stk : Commitment → Stk)
    (hlen : cmb.length = 3) (htl : tl.length = 5) (hbrs : brs.length = varsOf L)
    (h2 : ∀ x ∈ brs, x.1.2.length = 2) (hsh : Pending.Shaped p) (hsl : p.hasSlices = true)
    (hR : p.rounds ≤ varsOf L)
    (hz : ∀ z ∈ (batchPure cmb L bitSlice ringMap p fp lam brs tl).1, z = 0)
    (hclaims : ∀ o ∈ (batchPure cmb L bitSlice ringMap p fp lam brs tl).2.1, ∀ pt v bs,
      o.2 = .point pt v bs → mleStk (stk o.1) (layoutOf L o.1).vars pt = v)
    (hmat : ∀ mc, (batchPure cmb L bitSlice ringMap p fp lam brs tl).2.2 = some mc → MatrixHolds mc)
    (hW : ∀ x ∈ cmb, foldAll (fun u => weightAt x.2 (layoutOf L x.1) (bitsE u (varsOf L)) ringMap)
      (pointAfter (roundsOf brs)) 0 = weightAt x.2 (layoutOf L x.1) (pointAfter (roundsOf brs)) ringMap) :
    SumState (prodOf cmb L ringMap p stk lam).oracle (targetOf cmb lam p) (roundsOf brs) := by
  have hsc := decodeSC_none ((batchTarget cmb lam).1 + (batchTarget cmb lam).2 * p.claim) brs h2
  rw [hbrs] at hsc
  have hrl : (pointAfter (roundsOf brs)).length = varsOf L := by
    rw [length_pointAfter]
    simp [roundsOf, hbrs]
  generalize hrdef : pointAfter (roundsOf brs) = r at hsc hrl hW
  obtain ⟨x1, x2, x3, rfl⟩ := List.length_eq_three.mp hlen
  rcases tl with _ | ⟨t0, _ | ⟨t1, _ | ⟨t2, _ | ⟨t3, _ | ⟨t4, _ | ⟨t5, tl'⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at htl <;> try omega
  simp only [batchPure, hsc, hsl, ite_true, batchFold, List.length_cons, List.length_nil,
    List.take_succ_cons, List.take_zero, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons,
    List.foldl_nil, List.getD_cons_succ, List.getD_cons_zero] at hz hclaims hmat
  have hcl := eq_of_add_eq_zero_char2 (hz _ (List.mem_singleton_self _))
  simp only [Array.toList_push, List.nil_append, List.cons_append,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hclaims
  obtain ⟨hc1, hc2, hc3⟩ := hclaims
  have hc1 := hc1 _ _ _ rfl
  have hc2 := hc2 _ _ _ rfl
  have hc3 := hc3 _ _ _ rfl
  have hpt := pendingTerminalLink p r t3 t4 hsh (by omega) (hmat _ rfl)
  have hv1 := layoutOf_vars_le L x1.1
  have hv2 := layoutOf_vars_le L x2.1
  have hv3 := layoutOf_vars_le L x3.1
  unfold SumState targetOf
  rw [hrdef, hcl]
  show _ = (prodOf [x1, x2, x3] L ringMap p stk lam).T r
  rw [ProdSum.T_full _ r hrl]
  simp only [prodOf, Finset.sum_range_succ, Finset.sum_range_zero, List.length_cons, List.length_nil,
    List.getD_cons_zero, List.getD_cons_succ, zero_add]
  simp only [show (0 : ℕ) < 3 from by decide, show (1 : ℕ) < 3 from by decide,
    show (2 : ℕ) < 3 from by decide, show ¬ (3 : ℕ) < 3 from by decide, ite_true, ite_false]
  rw [hW x1 (by simp), hW x2 (by simp), hW x3 (by simp), hpt,
    foldAll_stackExt _ _ r (by omega), foldAll_stackExt _ _ r (by omega), foldAll_stackExt _ _ r (by omega),
    hc1, hc2, hc3, ← hrl, extension_eq_cubeEq, extension_eq_cubeEq, extension_eq_cubeEq,
    extension_eq_cubeEq]
  ring

/-! ## Completed transcripts -/

theorem doneFits_append_split : ∀ (a b : List Compose.RoundSpec) (d : Done), DoneFits (a ++ b) d →
    ∃ d1 d2, d = d1 ++ d2 ∧ DoneFits a d1 ∧ DoneFits b d2
  | [], b, d, h => ⟨[], d, rfl, trivial, h⟩
  | s :: a, b, [], h => by simp [DoneFits] at h
  | s :: a, b, x :: d, h => by
    simp only [List.cons_append, DoneFits] at h
    obtain ⟨d1, d2, rfl, h1, h2⟩ := doneFits_append_split a b d h.2.2
    exact ⟨x :: d1, d2, rfl, ⟨h.1, h.2.1, h1⟩, h2⟩

theorem doneFits_length : ∀ (a : List Compose.RoundSpec) (d : Done), DoneFits a d → d.length = a.length
  | [], [], _ => rfl
  | _ :: a, _ :: d, h => by simp only [List.length_cons, doneFits_length a d h.2.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem doneFits_replicate_two : ∀ (n : ℕ) (d : Done), DoneFits (List.replicate n ⟨false, 2, 0⟩) d →
    ∀ x ∈ d, x.1.2.length = 2
  | 0, [], _ => by simp
  | n + 1, x :: d, h => by
    simp only [List.replicate_succ, DoneFits] at h
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h.1.2
    · exact doneFits_replicate_two n d h.2.2 y hy
  | 0, _ :: _, h => h.elim
  | _ + 1, [], h => h.elim

theorem doneFits_noRoot_eq : ∀ (rs : List Compose.RoundSpec) (d : Done), (∀ s ∈ rs, s.root = false) →
    DoneFits rs d → d.map (fun y => (((none : Option (E × E)), y.1.2), y.2)) = d
  | [], [], _, _ => rfl
  | s :: rs, y :: d, hr, h => by
    simp only [DoneFits] at h
    have hs : s.root = false := hr s (List.mem_cons_self ..)
    have hy : y.1.1 = none := by
      have h1 := h.1.1
      rw [hs] at h1
      exact Option.not_isSome_iff_eq_none.mp (by simp [h1])
    simp only [List.map_cons, doneFits_noRoot_eq rs d (fun s hs => hr s (List.mem_cons_of_mem _ hs)) h.2.2]
    rw [← hy]

/-! ## The layout words -/

/-- **The stacks have fewer than `256` variables** (a layout word carries them in one byte). -/
def LayoutVarsSmall (D : Deployment) : Prop := ∀ c, (layoutOf (layoutsOf D.shape) c).vars < 256

theorem layoutWordVars_layoutWord (s : Shape) (code vars placed : ℕ) (h : vars < 256) :
    layoutWordVars (layoutWord s code vars placed) = vars := by
  simp only [layoutWordVars, layoutWord, shapeBytes, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp), List.getElem?_append_right (by simp)]
  simp only [List.length_append, List.length_cons, List.length_map, List.length_range,
    List.length_replicate, List.length_nil]
  simp [Nat.mod_eq_of_lt h]

theorem layoutWords_word (s : Shape) (c : Commitment) :
    (layoutWords s).getD (wordIndex c) [] =
      layoutWord s (layoutCode c) (layoutOf (layoutsOf s) c).vars (layoutOf (layoutsOf s) c).words := by
  cases c <;> rfl

theorem claimVars (D : Deployment) (hsmall : LayoutVarsSmall D) (c : Commitment) :
    layoutWordVars ((layoutWords D.shape).getD (wordIndex c) []) = (layoutOf (layoutsOf D.shape) c).vars := by
  rw [layoutWords_word, layoutWordVars_layoutWord _ _ _ _ (hsmall c)]

theorem matrixWordVars (s : Shape) :
    layoutWordVars ((layoutWords s).getD 3 []) = matrixVars ∧
      layoutWordVars ((layoutWords s).getD 4 []) = matrixVars :=
  ⟨layoutWordVars_layoutWord _ _ _ _ (by decide), layoutWordVars_layoutWord _ _ _ _ (by decide)⟩

theorem varsOf_ge (s : Shape) : 15 ≤ varsOf (layoutsOf s) := by
  have h := layoutOf_vars_le (layoutsOf s) .c1
  have h1 : 15 ≤ (layoutOf (layoutsOf s) .c1).vars := by
    show 15 ≤ (StackLayout.new _).vars
    exact le_max_right _ _
  omega

/-! ## The identity model's batch, and the hypotheses -/

section Model

variable (D : Deployment) {κ : ℕ} (Fl : FlockSound κ)

/-- **The run's combined claims and ring map**, from the statement, round `0`'s challenges, Flock's
transcript, `t`, the values and `ρ` (`mainOut`'s). -/
def runClaims (s : USt) (ch : List E) (fd : Done) (t : E) (vals : List E) (rho : E) :
    List (Commitment × Combined) × Option (List E) :=
  ((commitments.filterMap fun c => (combine (flockClaim (mainRels D.shape (publicWordsOf s.1.toList)
      (countsBits D.shape.heights s.2) (ch.take 4) (ch.getD 4 0) (ch.getD 5 0) t vals).1
        (Fl.prog.out fd [])).1.toList c rho).map fun x => (c, x)),
    (flockClaim (mainRels D.shape (publicWordsOf s.1.toList) (countsBits D.shape.heights s.2) (ch.take 4)
      (ch.getD 4 0) (ch.getD 5 0) t vals).1 (Fl.prog.out fd [])).2.2)

/-- **The batch's products as the verifier states them** (the identity model's `prod`): `prodOf`
of the run's claims, the shape's layouts, the stacks `C1`, `C2`, the setup's. -/
noncomputable def batchProd (s : USt) (c1 : Stk) (ch : List E) (fd : Done) (c2 : Stk) (t : E)
    (vals : List E) (rho lam : E) : ProdSum :=
  prodOf (runClaims D Fl s ch fd t vals rho).1 (layoutsOf D.shape) (runClaims D Fl s ch fd t vals rho).2
    (Fl.prog.out fd []).2.2 (stackFor D c1 c2) lam

/-- **The batch's claimed sum** (the identity model's `target`). -/
def batchTargetOf (s : USt) (ch : List E) (fd : Done) (t : E) (vals : List E) (rho lam : E) : E :=
  targetOf (runClaims D Fl s ch fd t vals rho).1 lam (Fl.prog.out fd []).2.2

/-- **The weights are multilinear at the batch's point**: each run claim's weight there is the fold
of its values on the cube (`weightAt` the multilinear extension of the cube's weights). See the
module's docstring: false when a `q_flock` slot term's point is merged into a longer one. -/
def WeightMle : Prop :=
  ∀ (s : USt) (ch : List E) (fd : Done) (t : E) (vals : List E) (rho : E) (r : List E),
    r.length = varsOf (layoutsOf D.shape) → ∀ x ∈ (runClaims D Fl s ch fd t vals rho).1,
      foldAll (fun u => weightAt x.2 (layoutOf (layoutsOf D.shape) x.1)
          (bitsE u (varsOf (layoutsOf D.shape))) (runClaims D Fl s ch fd t vals rho).2) r 0 =
        weightAt x.2 (layoutOf (layoutsOf D.shape) x.1) r (runClaims D Fl s ch fd t vals rho).2

/-- **Flock's pending reduction has its shape** on every completed Flock transcript: the skip's
`2^k` weights, the 64 slices sent, its points inside `A0`'s variables, at most `15` rounds. -/
def FlockPendingShaped : Prop :=
  ∀ fd, DoneFits Fl.prog.rounds fd →
    Pending.Shaped (Fl.prog.out fd []).2.2 ∧ (Fl.prog.out fd []).2.2.hasSlices = true ∧
      (Fl.prog.out fd []).2.2.rounds ≤ 15

/-- `uniCode` at the identity model's numbers. -/
def uniCodeAt (hκ : D.shape.heights.getD opBlake2s 0 = κ) (nV V : ℕ) (hnV : nV = valsCount)
    (hV : V = varsOf (layoutsOf D.shape)) : UniCode D Fl nV V where
  prog := mainProg D Fl
  rounds_eq i r := by
    rw [hnV, hV, mainProg_rounds]
    rfl
  tail_eq _ _ := rfl
  link := (uniCode D Fl hκ).link

end Model

/-! ## The last link -/

theorem map_zipIdx_fst {α β : Type} (f : α → β) : ∀ (l : List α) (k : ℕ),
    (l.zipIdx k).map (fun x => f x.1) = l.map f
  | [], _ => rfl
  | x :: l, k => by simp only [List.zipIdx_cons, List.map_cons, map_zipIdx_fst f l (k + 1)]

theorem brOf_openedOf (nF : ℕ) (c1 c2 : Stk) (pre brs : Done) (h : pre.length = nF + 3) :
    brOf nF (openedOf nF c1 c2 (pre ++ brs)) = roundsOf brs := by
  unfold brOf openedOf roundsOf
  rw [List.zipIdx_append, List.map_append, List.drop_append_of_le_length (by simp; omega),
    List.drop_eq_nil_of_le (by simp; omega), List.nil_append]
  simp only [List.map_map, Function.comp_def]
  exact map_zipIdx_fst (fun y : UMsg × List E => (y.1.2, y.2)) brs _

/-- **The last link** (`UniFinal`), for the identity model whose batch is the verifier's. -/
theorem uniFinal (D : Deployment) {κ : ℕ} (Fl : FlockSound κ) (hκ : D.shape.heights.getD opBlake2s 0 = κ)
    (I : UniIds D Fl) (hnV : I.nV = valsCount) (hV : I.V = varsOf (layoutsOf D.shape))
    (hprod : ∀ s c1 ch fd c2 t vals rho lam,
      I.prod s c1 ch fd c2 t vals rho lam = batchProd D Fl s c1 ch fd c2 t vals rho lam)
    (htarget : ∀ s c1 ch fd c2 t vals rho lam,
      I.target s c1 ch fd c2 t vals rho lam = batchTargetOf D Fl s ch fd t vals rho lam)
    (hW : WeightMle D Fl) (hsmall : LayoutVarsSmall D) (hpend : FlockPendingShaped Fl) :
    UniFinal D Fl I (uniCodeAt D Fl hκ I.nV I.V hnV hV) := by
  intro s done tl c1 c2 hd htl hz hc
  change (mainProg D Fl s.1 s.2).ZerosVanish done tl at hz
  change ClaimsHold D ((mainProg D Fl s.1 s.2).out done tl) c1 c2 at hc
  rw [hnV, hV] at hd
  simp only [uniRounds] at hd
  obtain ⟨d012, brs, rfl, h012, hbr⟩ := doneFits_append_split _ _ _ hd
  obtain ⟨d01, d23, rfl, h01, h23⟩ := doneFits_append_split _ _ _ h012
  obtain ⟨d0, G, rfl, h0, hG⟩ := doneFits_append_split _ _ _ h01
  rcases d0 with _ | ⟨x0, _ | ⟨y0, d0⟩⟩ <;> simp only [DoneFits, and_false] at h0
  rcases d23 with _ | ⟨x2, _ | ⟨x3, _ | ⟨y3, d23⟩⟩⟩ <;> simp only [DoneFits, and_false] at h23
  have hGl : G.length = Fl.prog.rounds.length := doneFits_length _ _ hG
  have hbl : brs.length = varsOf (layoutsOf D.shape) := by simpa using doneFits_length _ _ hbr
  -- The opened transcript's reads.
  have hpre : ([x0] ++ G ++ [x2, x3]).length = Fl.prog.rounds.length + 3 := by simp [hGl]
  have hr0 : (rd (openedOf Fl.prog.rounds.length c1 c2 ([x0] ++ G ++ [x2, x3] ++ brs)) 0).2 = x0.2 := by
    rw [rd_openedOf _ _ _ _ 0 (by simp)]
    simp
  have hr2 : (rd (openedOf Fl.prog.rounds.length c1 c2 ([x0] ++ G ++ [x2, x3] ++ brs))
      (Fl.prog.rounds.length + 1)).2 = x2.2 := by
    rw [rd_openedOf _ _ _ _ _ (by simp [hGl])]
    simp [List.getElem_append_right, hGl]
  have hr3 : rd (openedOf Fl.prog.rounds.length c1 c2 ([x0] ++ G ++ [x2, x3] ++ brs))
      (Fl.prog.rounds.length + 2) = ((none, x3.1.2), x3.2) := by
    rw [rd_openedOf _ _ _ _ _ (by simp [hGl])]
    simp [List.getElem_append_right, hGl]
  have hfd : fdOf Fl.prog.rounds.length (openedOf Fl.prog.rounds.length c1 c2 ([x0] ++ G ++ [x2, x3] ++ brs)) =
      G := by
    rw [fdOf_openedOf]
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.drop_one, List.tail_cons]
    rw [List.take_left' hGl]
    exact doneFits_noRoot_eq _ _ Fl.rounds_root hG
  rw [hr0, hfd, hr2, hr3, brOf_openedOf _ _ _ _ _ hpre, hprod, htarget]
  simp only []
  -- The program's zeros and result at this transcript.
  have e : [x0] ++ G ++ [x2, x3] ++ brs = [x0] ++ G ++ [x2] ++ [x3] ++ brs := by simp
  rw [e] at hz hc
  have hz' := hz.2
  simp only [mainProg, decode_r0, decode_fd _ _ _ _ _ _ hGl, decode_r2 _ _ _ _ _ _ hGl,
    decode_r3 _ _ _ _ _ _ hGl, decode_brs _ _ _ _ _ _ hGl] at hz' hc
  simp only [mainOut, mainRels_c2] at hz' hc
  change ∀ z ∈ (batchPure (runClaims D Fl s x0.2 G (x2.2.headD 0) x3.1.2 (x3.2.headD 0)).1
    (layoutsOf D.shape) _ (runClaims D Fl s x0.2 G (x2.2.headD 0) x3.1.2 (x3.2.headD 0)).2
    (Fl.prog.out G []).2.2 (Fl.prog.out G []).1 (x3.2.getD 1 0) brs tl).1, z = 0 at hz'
  obtain ⟨hsh, hsl, hR⟩ := hpend G hG
  unfold batchProd batchTargetOf
  refine terminal_sumState _ (layoutsOf D.shape) _ _ _ _ _ brs tl (stackFor D c1 c2) ?_ htl hbl
    (doneFits_replicate_two _ _ hbr) hsh hsl (hR.trans (varsOf_ge _)) hz' ?_ ?_ ?_
  · exact mainCombined_length _ _ _ _ _ _ _ _ _ _
  · intro o ho pt v bs hob
    have h1 := hc.1 o ho pt v bs hob
    rwa [claimVars D hsmall] at h1
  · intro mc hmc
    have key : ∀ (o : Option Flock.MatrixClaim), o = some mc → (if o.isSome = true then o else none) = some mc := by
      intro o h
      subst h
      rfl
    have h1 := hc.2 mc (key _ hmc)
    rwa [(matrixWordVars D.shape).1, (matrixWordVars D.shape).2] at h1
  · exact hW s x0.2 G (x2.2.headD 0) x3.1.2 (x3.2.headD 0) _
      (by rw [length_pointAfter]; simp [roundsOf, hbl])

/-! ## The end theorem with the code-level links in place -/

open scoped ENNReal in
/-- **Knowledge soundness, the code-level links constructed** (`uniCodeAt`, `uniFinal`): the end
theorem `uniKnowledgeSoundness_bus` with `UniCode` and `UniFinal` discharged, for an identity model
whose numbers are the verifier's (`valsCount`, the batch's variables) and whose batch is the
verifier's (`batchProd`, `batchTargetOf`); under `WeightMle`, `LayoutVarsSmall`,
`FlockPendingShaped` and the end theorem's other hypotheses. -/
theorem uniKnowledgeSoundness_code {D : Deployment} {κ : ℕ} (hFlock : FlockSound κ)
    (hκ : D.shape.heights.getD opBlake2s 0 = κ) (B : BusModel D κ) (J : UniIdsRest D hFlock B)
    (hnV : J.nV = valsCount) (hV : J.V = varsOf (layoutsOf D.shape))
    (hprod : ∀ s c1 ch fd c2 t vals rho lam,
      J.prod s c1 ch fd c2 t vals rho lam = batchProd D hFlock s c1 ch fd c2 t vals rho lam)
    (htarget : ∀ s c1 ch fd c2 t vals rho lam,
      J.target s c1 ch fd c2 t vals rho lam = batchTargetOf D hFlock s ch fd t vals rho lam)
    (hW : WeightMle D hFlock) (hsmall : LayoutVarsSmall D) (hpend : FlockPendingShaped hFlock)
    (hFs : FsLayer D hFlock J.nV J.V (uniCodeAt D hFlock hκ J.nV J.V hnV hV))
    (hB : 4 * B.N + B.ncv ≤ 2 ^ 32)
    (hFl : ∀ j, hFlock.err j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hdeg : J.degSum ≤ 2 ^ 32) (hrel : J.nRel + 2 ≤ 2 ^ 32) :
    UniKnowledgeSoundness D (uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 :=
  uniKnowledgeSoundness_bus hFlock B J (uniCodeAt D hFlock hκ J.nV J.V hnV hV)
    (uniFinal D hFlock hκ (UniIds.ofBus hFlock B J) hnV hV hprod htarget hW hsmall hpend) hFs hB hFl hdeg
    hrel

end UniSound
