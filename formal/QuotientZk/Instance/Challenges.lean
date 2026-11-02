-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientZk.Instance.JointV

/-!
# The deployed prover's challenges

`skel` (`Deployed/Skeleton.lean`) asks `394` Fiat–Shamir queries at the deployed shape: the
reduction's five chain states (`α, β, γ, t, ρ`, `transcript.rs`), then the witness opening's `123`
draws, the wiring opening's `114`, the quotient opening's `152` (`openDraws`, counted from the
shape as `opening` draws: `λ`, the six lane-fold challenges, the first commitment's out-of-domain
coordinates, each query phase's position draws and batching challenge, the later levels' folds and
samples, the last rounds; `openDraws_witness`, …). The witness opening starts at step `5`, the
wiring opening at `128`, the quotient opening at `242`.

**The challenges** (`chOf`): from the `394` oracle answers (`Out = digest × state`), a chain
challenge is the low 192 bits of the digest (`QuotientRpm.Wire.chal`: `limbsE.symm ∘ stateLimbs`),
a duplex draw the state's lanes `0 .. 2` (`Dx.draw`). The joint model's `Chal` keeps the five chain
challenges, each secret opening's `λ` and six `φ`, and every other answer raw (`ΓW`, `Γσ`, `ΓQ`:
the openings' later draws, positions included). `eAll`: the answers are `Chal` and the parts of
the answers no challenge reads (`Rest`), an equivalence; so **`hch`**: uniform answers give uniform
challenges.

**Causality** (`chOf_take_*`): the challenges an answer prefix `σ.take k` decodes agree with
`σ`'s on every component drawn before step `k`.
-/

open OracleComp OracleSpec QuotientRpm
open QuotientZk.Deployed (Inp Out Msg Tbl Pos KSt OpenShape)
open QuotientZk.Joint

namespace QuotientZk.Instance

set_option linter.unusedSectionVars false

/-! ## The draws of an opening -/

/-- A query phase's draws on a commitment of depth `b` with `q` queries: the positions, then the
batching challenge (`queryPhase`). -/
def qpDraws (b q : ℕ) : ℕ := (q + 192 / max b 1 - 1) / (192 / max b 1) + 1

/-- The later levels' draws, the previous commitment of depth `b` (`middle`). -/
def midDraws : ℕ → List (ℕ × ℕ × ℕ) → List ℕ → ℕ
  | _, [], _ => 0
  | b, (folds, depth, oodN) :: rest, q :: qs => folds + oodN + qpDraws b q + midDraws depth rest qs
  | _, _ :: _, [] => 0

/-- The last commitment's depth. -/
def lastDepth : ℕ → List (ℕ × ℕ × ℕ) → ℕ
  | b, [] => b
  | _, (_, depth, _) :: rest => lastDepth depth rest

/-- **An opening's draws** (`opening`): `λ`, six lane folds, the first commitment's out-of-domain
coordinates, level 0's query phase, the later levels, the last rounds, the last level's query
phase, the residual's rounds and the final draw. -/
def openDraws (sh : OpenShape) : ℕ :=
  1 + 6 + sh.ood₀ + qpDraws sh.depth₀ (sh.queries.headD 0) +
    midDraws sh.depth₁ sh.levels (sh.queries.drop 1) + sh.lastFolds +
    qpDraws (lastDepth sh.depth₁ sh.levels) (sh.queries.getLastD 0) + (sh.residualVars - 1) + 1

theorem openDraws_witness (id : Bytes32) : openDraws (Deployed.witnessShape id) = 7 + 116 := by
  simp [openDraws, Deployed.witnessShape, qpDraws, midDraws, lastDepth]

theorem openDraws_wiring (id : Bytes32) (rows : List (List UInt8)) :
    openDraws (Deployed.wiringShape id rows) = 114 := by
  simp [openDraws, Deployed.wiringShape, qpDraws, midDraws, lastDepth]

theorem openDraws_quotient (id : Bytes32) : openDraws (Deployed.quotientShape id) = 7 + 145 := by
  simp [openDraws, Deployed.quotientShape, qpDraws, midDraws, lastDepth]

/-- Level 0's position draws: `qpDraws depth₀ q₀ - 1`, `25` for the witness table (`2^20` leaves,
`9` positions a draw, `224` queries), `29` for the quotient table (`2^23`, `8`, `225`). -/
theorem posDraws_witness : qpDraws 20 224 - 1 = 25 := by decide
theorem posDraws_quotient : qpDraws 23 225 - 1 = 29 := by decide

/-! ## The raw answers -/

/-- The witness opening's answers after `λ` and `φ`, the wiring opening's, the quotient
opening's. -/
abbrev ΓW := Fin 116 → Out
abbrev Γσ := Fin 114 → Out
abbrev ΓQ := Fin 145 → Out

/-- **The deployed challenges**: the joint model's `Chal`. -/
abbrev DChal (E : Type) := Chal E ΓW ΓQ Γσ

/-- The number of Fiat–Shamir steps: `5 + 123 + 114 + 152`. -/
abbrev nRaw : ℕ := 5 + (7 + (116 + (114 + (7 + 145))))

theorem nRaw_eq : nRaw = 394 := rfl

/-- What a chain answer keeps besides its challenge, and a draw. -/
abbrev RH := Vector UInt8 8 × KSt
abbrev RF := Bytes32 × (Fin 22 → UInt64)

/-- The parts of the answers no challenge reads. -/
abbrev Rest := (Fin 5 → RH) × (Fin 7 → RF) × (Fin 7 → RF)

variable {E : Type} (limbsE : E ≃ Limbs)

/-- A chain challenge: the low 192 bits of the state (`Wire.chal`). -/
def dH (o : Out) : E := limbsE.symm (stateLimbs o.1)

/-- A draw's limbs: the state's lanes `0 .. 2` (`Dx.draw`). -/
def drawLimbs (o : Out) : Limbs := (o.2[0], o.2[1], o.2[2])

/-- A duplex draw's challenge. -/
def dF (o : Out) : E := limbsE.symm (drawLimbs o)

/-- A chain answer: its challenge and the rest. -/
def eH : Out ≃ E × RH where
  toFun o := (dH limbsE o, ((stateEquiv o.1).1, o.2))
  invFun p := (stateEquiv.symm (p.2.1, limbsE p.1), p.2.2)
  left_inv o := by
    obtain ⟨b, x⟩ := o
    show (stateEquiv.symm ((stateEquiv b).1, limbsE (limbsE.symm (stateLimbs b))), x) = (b, x)
    rw [Equiv.apply_symm_apply, ← stateEquiv_snd, Prod.mk.eta, Equiv.symm_apply_apply]
  right_inv p := by
    obtain ⟨e, top, x⟩ := p
    show (limbsE.symm (stateLimbs (stateEquiv.symm (top, limbsE e))),
      ((stateEquiv (stateEquiv.symm (top, limbsE e))).1, x)) = (e, top, x)
    rw [← stateEquiv_snd, Equiv.apply_symm_apply]
    simp

/-- The limb `i` of a triple. -/
def limbAt (L : Limbs) (i : ℕ) : UInt64 := if i = 0 then L.1 else if i = 1 then L.2.1 else L.2.2

/-- A draw: its challenge and the rest. -/
def eF : Out ≃ E × RF where
  toFun o := (dF limbsE o, (o.1, fun i => o.2[(i : ℕ) + 3]))
  invFun p := (p.2.1, Vector.ofFn fun i : Fin 25 =>
    if h : (i : ℕ) < 3 then limbAt (limbsE p.1) i else p.2.2 ⟨(i : ℕ) - 3, by omega⟩)
  left_inv o := by
    obtain ⟨b, x⟩ := o
    refine Prod.ext rfl ?_
    apply Vector.ext
    intro i hi
    simp only [dF, drawLimbs, Equiv.apply_symm_apply, Vector.getElem_ofFn]
    split_ifs with h
    · interval_cases i <;> rfl
    · congr 1
      omega
  right_inv p := by
    obtain ⟨e, b, f⟩ := p
    refine Prod.ext ?_ (Prod.ext rfl ?_)
    · show limbsE.symm (drawLimbs (b, _)) = e
      simp only [drawLimbs, Vector.getElem_ofFn, limbAt]
      simp
    · funext i
      show (Vector.ofFn _)[(i : ℕ) + 3] = f i
      rw [Vector.getElem_ofFn]
      simp

/-- Five chain answers. -/
def e5 : (Fin 5 → E) ≃ ((E × E × E) × E) × E where
  toFun f := (((f 0, f 1, f 2), f 3), f 4)
  invFun p := ![p.1.1.1, p.1.1.2.1, p.1.1.2.2, p.1.2, p.2]
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

/-- The reduction's five answers. -/
def eRed : (Fin 5 → Out) ≃ (((E × E × E) × E) × E) × (Fin 5 → RH) :=
  (Equiv.piCongrRight fun _ => eH limbsE).trans
    ((Equiv.arrowProdEquivProdArrow _ _ _).trans (Equiv.prodCongr e5 (Equiv.refl _)))

/-- An opening's first seven draws: `λ` and the six lane-fold challenges. -/
def eOpen : (Fin 7 → Out) ≃ (E × (Fin 6 → E)) × (Fin 7 → RF) :=
  (Equiv.piCongrRight fun _ => eF limbsE).trans
    ((Equiv.arrowProdEquivProdArrow _ _ _).trans
      (Equiv.prodCongr (Fin.consEquiv fun _ => E).symm (Equiv.refl _)))

/-- The blocks put in the order of `Chal` and `Rest`. -/
def rearr : ((((E × E × E) × E) × E) × (Fin 5 → RH)) ×
    (((E × (Fin 6 → E)) × (Fin 7 → RF)) × (ΓW × (Γσ × (((E × (Fin 6 → E)) × (Fin 7 → RF)) × ΓQ))))
    ≃ DChal E × Rest where
  toFun x := ((x.1.1, ((x.2.1.1.1, x.2.2.1), x.2.1.1.2),
      ((x.2.2.2.2.1.1.1, x.2.2.2.2.2), x.2.2.2.2.1.1.2), x.2.2.2.1),
    (x.1.2, x.2.1.2, x.2.2.2.2.1.2))
  invFun y := ((y.1.1, y.2.1), (((y.1.2.1.1.1, y.1.2.1.2), y.2.2.1),
    (y.1.2.1.1.2, (y.1.2.2.2, ((y.1.2.2.1.1.1, y.1.2.2.1.2), y.2.2.2), y.1.2.2.1.1.2))))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The answers are the challenges and the rest.** -/
def eAll : (Fin nRaw → Out) ≃ DChal E × Rest :=
  ((Fin.appendEquiv 5 _).symm.trans (Equiv.prodCongr (eRed limbsE)
    ((Fin.appendEquiv 7 _).symm.trans (Equiv.prodCongr (eOpen limbsE)
      ((Fin.appendEquiv 116 _).symm.trans (Equiv.prodCongr (Equiv.refl _)
        ((Fin.appendEquiv 114 _).symm.trans (Equiv.prodCongr (Equiv.refl _)
          ((Fin.appendEquiv 7 145).symm.trans
            (Equiv.prodCongr (eOpen limbsE) (Equiv.refl _))))))))))).trans rearr

/-- The answers as a function, the default past the end. -/
def getRaw (σ : List Out) : Fin nRaw → Out := fun i => σ.getD i default

/-- **The challenges the oracle's answers give.** -/
def chOf (σ : List Out) : DChal E := (eAll limbsE (getRaw σ)).1

/-! ## What each challenge reads -/

theorem chOf_fst (σ : List Out) : (chOf limbsE σ).1 =
    ((((dH limbsE (σ.getD 0 default), dH limbsE (σ.getD 1 default),
      dH limbsE (σ.getD 2 default)), dH limbsE (σ.getD 3 default)),
      dH limbsE (σ.getD 4 default))) := rfl

theorem lam₁_chOf (σ : List Out) : lam₁ (chOf limbsE σ) = dF limbsE (σ.getD 5 default) := rfl

theorem phi₁_chOf (σ : List Out) (i : Fin 6) :
    phi₁ (chOf limbsE σ) i = dF limbsE (σ.getD (5 + ((i : ℕ) + 1)) default) := rfl

theorem gW_chOf (σ : List Out) (j : Fin 116) :
    (chOf limbsE σ).2.1.1.2 j = σ.getD (5 + (7 + (j : ℕ))) default := rfl

theorem lam₂_chOf (σ : List Out) :
    lam₂ (chOf limbsE σ) = dF limbsE (σ.getD (5 + (7 + (116 + (114 + 0)))) default) := rfl

theorem phi₂_chOf (σ : List Out) (i : Fin 6) :
    phi₂ (chOf limbsE σ) i =
      dF limbsE (σ.getD (5 + (7 + (116 + (114 + ((i : ℕ) + 1))))) default) := rfl

theorem gQ_chOf (σ : List Out) (j : Fin 145) :
    (chOf limbsE σ).2.2.1.1.2 j = σ.getD (5 + (7 + (116 + (114 + (7 + (j : ℕ)))))) default := rfl

/-! ## Causality -/

theorem getD_take_of_lt {α : Type} (σ : List α) (d : α) {i k : ℕ} (h : i < k) :
    (σ.take k).getD i d = σ.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos h]

theorem dH_take {σ : List Out} {i k : ℕ} (h : i < k) :
    dH limbsE ((σ.take k).getD i default) = dH limbsE (σ.getD i default) := by
  rw [getD_take_of_lt _ _ h]

theorem dF_take {σ : List Out} {i k : ℕ} (h : i < k) :
    dF limbsE ((σ.take k).getD i default) = dF limbsE (σ.getD i default) := by
  rw [getD_take_of_lt _ _ h]

/-- `α, β, γ` are drawn at steps `0 .. 2`. -/
theorem chOf_take_abc (σ : List Out) {k : ℕ} (hk : 3 ≤ k) :
    (chOf limbsE (σ.take k)).1.1.1 = (chOf limbsE σ).1.1.1 := by
  simp only [chOf_fst, dH_take limbsE (show 0 < k by omega), dH_take limbsE (show 1 < k by omega),
    dH_take limbsE (show 2 < k by omega)]

/-- `t` is drawn at step `3`. -/
theorem chOf_take_t (σ : List Out) {k : ℕ} (hk : 4 ≤ k) :
    (chOf limbsE (σ.take k)).1.1.2 = (chOf limbsE σ).1.1.2 := by
  simp only [chOf_fst, dH_take limbsE (show 3 < k by omega)]

/-- The reduction's challenges are drawn at steps `0 .. 4`. -/
theorem chOf_take_fst (σ : List Out) {k : ℕ} (hk : 5 ≤ k) :
    (chOf limbsE (σ.take k)).1 = (chOf limbsE σ).1 := by
  simp only [chOf_fst, dH_take limbsE (show 0 < k by omega), dH_take limbsE (show 1 < k by omega),
    dH_take limbsE (show 2 < k by omega), dH_take limbsE (show 3 < k by omega),
    dH_take limbsE (show 4 < k by omega)]

theorem chOf_take_lam₁ (σ : List Out) {k : ℕ} (hk : 6 ≤ k) :
    lam₁ (chOf limbsE (σ.take k)) = lam₁ (chOf limbsE σ) := by
  rw [lam₁_chOf, lam₁_chOf, dF_take limbsE (show 5 < k by omega)]

theorem chOf_take_phi₁ (σ : List Out) {k : ℕ} (i : Fin 6) (hk : 7 + (i : ℕ) ≤ k) :
    phi₁ (chOf limbsE (σ.take k)) i = phi₁ (chOf limbsE σ) i := by
  rw [phi₁_chOf, phi₁_chOf, dF_take limbsE (show 5 + ((i : ℕ) + 1) < k by omega)]

theorem chOf_take_gW (σ : List Out) {k : ℕ} (j : Fin 116) (hk : 13 + (j : ℕ) ≤ k) :
    (chOf limbsE (σ.take k)).2.1.1.2 j = (chOf limbsE σ).2.1.1.2 j := by
  rw [gW_chOf, gW_chOf, getD_take_of_lt _ _ (show 5 + (7 + (j : ℕ)) < k by omega)]

theorem chOf_take_lam₂ (σ : List Out) {k : ℕ} (hk : 243 ≤ k) :
    lam₂ (chOf limbsE (σ.take k)) = lam₂ (chOf limbsE σ) := by
  rw [lam₂_chOf, lam₂_chOf, dF_take limbsE (show 5 + (7 + (116 + (114 + 0))) < k by omega)]

theorem chOf_take_phi₂ (σ : List Out) {k : ℕ} (i : Fin 6) (hk : 244 + (i : ℕ) ≤ k) :
    phi₂ (chOf limbsE (σ.take k)) i = phi₂ (chOf limbsE σ) i := by
  rw [phi₂_chOf, phi₂_chOf,
    dF_take limbsE (show 5 + (7 + (116 + (114 + ((i : ℕ) + 1)))) < k by omega)]

theorem chOf_take_gQ (σ : List Out) {k : ℕ} (j : Fin 145) (hk : 250 + (j : ℕ) ≤ k) :
    (chOf limbsE (σ.take k)).2.2.1.1.2 j = (chOf limbsE σ).2.2.1.1.2 j := by
  rw [gQ_chOf, gQ_chOf, getD_take_of_lt _ _ (show 5 + (7 + (116 + (114 + (7 + (j : ℕ))))) < k by omega)]

/-! ## Uniform answers give uniform challenges -/

theorem uniformList_ofFn (O : Type) [SampleableType O] :
    ∀ n, uniformList O n =ᵈ (List.ofFn <$> ($ᵗ (Fin n → O)))
  | 0 => by
    have : (List.ofFn <$> ($ᵗ (Fin 0 → O)) : ProbComp (List O)) =
        ($ᵗ (Fin 0 → O)) >>= fun _ => pure [] := by
      rw [map_eq_bind_pure_comp]
      congr 1
    rw [this]
    exact (EvalDistEq.bind_const _ _).symm
  | n + 1 => by
    have hc : ($ᵗ (Fin (n + 1) → O)) =ᵈ
        (fun p : O × (Fin n → O) => (Fin.cons p.1 p.2 : Fin (n + 1) → O)) <$>
          ($ᵗ (O × (Fin n → O))) :=
      (SampleableType.map_uniformSample_evalDistEq_of_bijective
        (Fin.consEquiv fun _ : Fin (n + 1) => O).bijective).symm
    have key : ∀ u : O, ((fun l => u :: l) <$> uniformList O n) =ᵈ
        ((fun f => List.ofFn (Fin.cons u f : Fin (n + 1) → O)) <$> ($ᵗ (Fin n → O))) := by
      intro u
      have h := (uniformList_ofFn O n).map (fun l => u :: l)
      rw [Functor.map_map] at h
      have e : (fun a => u :: List.ofFn a : (Fin n → O) → List O) =
          fun f => List.ofFn (Fin.cons u f : Fin (n + 1) → O) := by
        funext f
        simp [List.ofFn_succ]
      rw [e] at h
      exact h
    calc uniformList O (n + 1)
        = ($ᵗ O) >>= fun u => (fun l => u :: l) <$> uniformList O n := by
          simp only [uniformList, map_eq_bind_pure_comp, Function.comp_def]
      _ =ᵈ ($ᵗ O) >>= fun u => (fun f => List.ofFn (Fin.cons u f : Fin (n + 1) → O)) <$>
          ($ᵗ (Fin n → O)) := EvalDistEq.bind_right _ key
      _ = List.ofFn <$> ((fun p : O × (Fin n → O) => (Fin.cons p.1 p.2 : Fin (n + 1) → O)) <$>
          ($ᵗ (O × (Fin n → O)))) := by
          rw [SampleableType.uniformSample_prod_eq_bind]
          simp only [map_bind, map_pure, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
            pure_bind]
      _ =ᵈ List.ofFn <$> ($ᵗ (Fin (n + 1) → O)) := hc.symm.map _

theorem getRaw_ofFn (f : Fin nRaw → Out) : getRaw (List.ofFn f) = f := by
  funext i
  show (List.ofFn f).getD i default = f i
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]

theorem fst_uniform {A B : Type} [SampleableType A] [SampleableType B] :
    (Prod.fst <$> ($ᵗ (A × B)) : ProbComp A) =ᵈ ($ᵗ A) := by
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [map_bind, map_pure]
  calc (($ᵗ A) >>= fun a => ($ᵗ B) >>= fun _ => (pure a : ProbComp A))
      =ᵈ (($ᵗ A) >>= fun a => (pure a : ProbComp A)) :=
        EvalDistEq.bind_right _ fun a => EvalDistEq.bind_const _ _
    _ = $ᵗ A := bind_pure _

variable [SampleableType E]

/-- **`hch`**: the challenges of uniform answers are uniform. -/
theorem chOf_uniform :
    chOf limbsE <$> uniformList Out nRaw =ᵈ ($ᵗ (DChal E)) := by
  have h1 := (uniformList_ofFn Out nRaw).map (chOf limbsE)
  rw [Functor.map_map] at h1
  have e : (fun f => chOf limbsE (List.ofFn f) : (Fin nRaw → Out) → DChal E) =
      fun f => (eAll limbsE f).1 := by
    funext f
    rw [chOf, getRaw_ofFn]
  have e2 : ((fun f => (eAll limbsE f).1) <$> ($ᵗ (Fin nRaw → Out)) : ProbComp (DChal E)) =
      Prod.fst <$> (eAll limbsE <$> ($ᵗ (Fin nRaw → Out))) := by
    rw [Functor.map_map]
  rw [e, e2] at h1
  exact h1.trans (((SampleableType.map_uniformSample_evalDistEq_of_bijective
    (eAll limbsE).bijective).map Prod.fst).trans fst_uniform)

end QuotientZk.Instance
