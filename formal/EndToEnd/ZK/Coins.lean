-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
-- The model (`RandomPermutationOracles`, `QueryCostAtMost`, `permutationCallCost`) is leanerVM's
-- (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0: `Statement/RandomPermutation.lean`).
import PcsQuotient.Security
import QuotientZk.RpmMain

/-!
# The distinguisher's coins

`PcsQuotient.ZeroKnowledge` quantifies over distinguishers with **coins** (`RandomPermutationOracles`
has `unifSpec` beside `π` and `π⁻¹`, and coins cost nothing), while `formal/QuotientZk`'s theorems are
for distinguishers of `π` and `π⁻¹` alone. This file removes the coins, for any two games of the
statement's shape: a first part `X` (the proof and the oracle's state), then the distinguisher run on
the proof by an oracle that answers coins as `unifSpec` does.

* **Coin bounds** (`CoinBound oa C N`): at most `C` coin queries on every path, each of range at most
  `N`. Every computation has some (`exists_coinBound`: it is a finite tree of finite branching).
* **A tape** (`tape M k`: `k` uniform values of `Fin (M + 1)`) answers a coin of range `n` by its next
  value modulo `n + 1` (`coinOf`), uniform when `n + 1` divides `M + 1` (`coinOf_uniform`).
  `derand M oa t` is `oa` with its coins read from the tape `t`: a computation of `π` and `π⁻¹` alone,
  with as many calls of them as `oa` (`derand_queryBound`).
* **`run_tape`**: run by an oracle that answers coins uniformly, `oa` is `derand M oa t` for a tape
  drawn first.
* **`close_of_coinFree`**: two games closer than `ε` for every coin-free distinguisher of at most `Q`
  calls are closer than `ε` for every distinguisher with coins of at most `Q` calls (the proofs both
  games can produce are finitely many, so one tape serves all of them).
* **`zeroKnowledgeWith_of_coinFree`**: `PcsQuotient.ZeroKnowledgeWith s₀ sim simOracle ζ` from the same
  bound for coin-free distinguishers (`ZeroKnowledgeCoinFreeWith`), for any simulator whose oracle
  forwards coins (`CoinsUniform`); `zeroKnowledge_of_coinFree` at the package's own `simulator`.
-/

open OracleComp OracleSpec Common
open scoped ENNReal

namespace PcsQuotient.EndToEnd

open QuotientZk (Close)

set_option linter.unusedSectionVars false

/-- `π` and `π⁻¹` alone. -/
abbrev PermSpec := permutationOracleSpec LeanVM.Semantics.KeccakState

/-- A distinguisher of `π` and `π⁻¹` as a computation of the model (no coins). -/
def liftPerm : QueryImpl PermSpec (OracleComp RandomPermutationOracles) :=
  fun q ↦ liftM (RandomPermutationOracles.query (.inr q))

theorem liftPerm_eq_permQuery : liftPerm = QuotientZk.permQuery := rfl

/-! ## Coin bounds -/

/-- A coin query needs budget left and a range at most `N`; a permutation call needs nothing. -/
def coinOK (N : ℕ) : RandomPermutationOracles.Domain → ℕ → Prop
  | .inl n, b => 0 < b ∧ n ≤ N
  | .inr _, _ => True

/-- A coin query costs one; a permutation call nothing. -/
def coinCost : RandomPermutationOracles.Domain → ℕ → ℕ
  | .inl _, b => b - 1
  | .inr _, b => b

/-- **`oa` asks at most `C` coins, each of range at most `N`, on every path.** -/
def CoinBound {α : Type} (oa : OracleComp RandomPermutationOracles α) (C N : ℕ) : Prop :=
  IsQueryBound oa C (coinOK N) coinCost

theorem CoinBound.mono {α : Type} {oa : OracleComp RandomPermutationOracles α} {C N C' N' : ℕ}
    (h : CoinBound oa C N) (hC : C ≤ C') (hN : N ≤ N') : CoinBound oa C' N' := by
  induction oa using OracleComp.inductionOn generalizing C C' with
  | pure _ => trivial
  | query_bind t k ih =>
    unfold CoinBound at h ⊢
    rw [isQueryBound_query_bind_iff] at h ⊢
    rcases t with n | q
    · simp only [coinOK, coinCost] at h ⊢
      exact ⟨⟨by omega, h.1.2.trans hN⟩, fun u ↦ ih u (h.2 u) (by omega)⟩
    · simp only [coinOK, coinCost] at h ⊢
      exact ⟨trivial, fun u ↦ ih u (h.2 u) hC⟩

/-- A function on a finite type is bounded. -/
theorem exists_bound {β : Type} [Finite β] (f : β → ℕ) : ∃ M, ∀ b, f b ≤ M := by
  obtain ⟨M, hM⟩ := (Set.finite_range f).bddAbove
  exact ⟨M, fun b ↦ hM (Set.mem_range_self b)⟩

/-- **Every computation has a coin bound**: it is a finite tree, each query of finitely many answers. -/
theorem exists_coinBound {α : Type} (oa : OracleComp RandomPermutationOracles α) :
    ∃ C N, CoinBound oa C N := by
  induction oa using OracleComp.inductionOn with
  | pure _ => exact ⟨0, 0, trivial⟩
  | query_bind t k ih =>
    choose C N h using ih
    have hfin : Finite (RandomPermutationOracles.Range t) := by
      rcases t with n | q
      · exact inferInstanceAs (Finite (Fin (n + 1)))
      · exact inferInstanceAs (Finite LeanVM.Semantics.KeccakState)
    obtain ⟨Cm, hCm⟩ := exists_bound C
    obtain ⟨Nm, hNm⟩ := exists_bound N
    rcases t with n | q
    · refine ⟨Cm + 1, max n Nm, ?_⟩
      unfold CoinBound
      rw [isQueryBound_query_bind_iff]
      simp only [coinOK, coinCost]
      refine ⟨⟨by omega, le_max_left _ _⟩, fun u ↦ (h u).mono ?_ ((hNm u).trans (le_max_right _ _))⟩
      have := hCm u
      omega
    · refine ⟨Cm, Nm, ?_⟩
      unfold CoinBound
      rw [isQueryBound_query_bind_iff]
      simp only [coinOK, coinCost]
      exact ⟨trivial, fun u ↦ (h u).mono (hCm u) (hNm u)⟩

/-! ## A coin from a tape value -/

/-- A coin of range `n` (a value of `Fin (n + 1)`) from a tape value: its residue. -/
def coinOf (M n : ℕ) (u : Fin (M + 1)) : Fin (n + 1) :=
  ⟨u.val % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

/-- A uniform pair of `Fin (q + 1) × Fin (n + 1)` read as one value of `Fin (M + 1)`. -/
def pairFin (M n q : ℕ) (hq : M + 1 = (n + 1) * (q + 1)) (x : Fin (q + 1) × Fin (n + 1)) :
    Fin (M + 1) :=
  ⟨x.2.val + (n + 1) * x.1.val, by
    have h1 := x.1.isLt
    have h2 := x.2.isLt
    rw [hq]
    nlinarith⟩

theorem pairFin_bijective (M n q : ℕ) (hq : M + 1 = (n + 1) * (q + 1)) :
    Function.Bijective (pairFin M n q hq) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun x y hxy ↦ ?_, ?_⟩
  · have h := congrArg Fin.val hxy
    simp only [pairFin] at h
    have hx2 := x.2.isLt
    have hy2 := y.2.isLt
    have hm : x.2.val = y.2.val := by
      have := congrArg (· % (n + 1)) h
      simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx2, Nat.mod_eq_of_lt hy2] using this
    have hd : x.1.val = y.1.val := by
      have := congrArg (· / (n + 1)) h
      rw [Nat.add_mul_div_left _ _ (Nat.succ_pos n), Nat.add_mul_div_left _ _ (Nat.succ_pos n),
        Nat.div_eq_of_lt hx2, Nat.div_eq_of_lt hy2] at this
      simpa using this
    exact Prod.ext (Fin.ext hd) (Fin.ext hm)
  · simp [Fintype.card_prod, Fintype.card_fin, hq, mul_comm]

theorem coinOf_pairFin (M n q : ℕ) (hq : M + 1 = (n + 1) * (q + 1))
    (x : Fin (q + 1) × Fin (n + 1)) : coinOf M n (pairFin M n q hq x) = x.2 := by
  apply Fin.ext
  simp [coinOf, pairFin, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt x.2.isLt]

theorem uniformFin_eq_sample (M : ℕ) : ($[0..M] : ProbComp (Fin (M + 1))) = $ᵗ (Fin (M + 1)) := rfl

/-- **A tape value's residue is a uniform coin**, when the coin's range divides the tape's. -/
theorem coinOf_uniform (M n : ℕ) (h : (n + 1) ∣ M + 1) :
    (coinOf M n <$> $[0..M]) =ᵈ ($[0..n] : ProbComp (Fin (n + 1))) := by
  obtain ⟨q₀, hq₀⟩ := h
  obtain ⟨q, rfl⟩ : ∃ q, q₀ = q + 1 := ⟨q₀ - 1, by
    rcases q₀ with _ | q₀
    · simp at hq₀
    · simp⟩
  have hb := SampleableType.map_uniformSample_evalDistEq_of_bijective
    (pairFin_bijective M n q hq₀)
  rw [uniformFin_eq_sample M, uniformFin_eq_sample n]
  calc coinOf M n <$> ($ᵗ (Fin (M + 1)))
      =ᵈ coinOf M n <$> (pairFin M n q hq₀ <$> ($ᵗ (Fin (q + 1) × Fin (n + 1)))) :=
        hb.symm.map _
    _ = Prod.snd <$> ($ᵗ (Fin (q + 1) × Fin (n + 1))) := by
        rw [Functor.map_map]
        congr 1
        funext x
        exact coinOf_pairFin M n q hq₀ x
    _ =ᵈ ($ᵗ (Fin (n + 1))) := by
        rw [SampleableType.uniformSample_prod_eq_bind]
        simp only [map_bind, map_pure]
        calc (($ᵗ (Fin (q + 1))) >>= fun _ ↦ ($ᵗ (Fin (n + 1))) >>= fun b ↦
              (pure b : ProbComp (Fin (n + 1))))
            =ᵈ (($ᵗ (Fin (n + 1))) >>= fun b ↦ (pure b : ProbComp (Fin (n + 1)))) :=
              QuotientZk.evalDistEq_bind_const _ _
          _ = $ᵗ (Fin (n + 1)) := bind_pure _

/-! ## The tape -/

/-- **A tape** of `k` uniform values of `Fin (M + 1)`. -/
def tape (M : ℕ) : ℕ → ProbComp (List (Fin (M + 1)))
  | 0 => pure []
  | k + 1 => do
    let u ← $[0..M]
    let l ← tape M k
    return u :: l

/-- Coins from the tape (its head, modulo the range), `π` and `π⁻¹` asked. -/
def tapeImpl (M : ℕ) :
    QueryImpl RandomPermutationOracles (StateT (List (Fin (M + 1))) (OracleComp PermSpec))
  | .inl n => fun t ↦ pure (coinOf M n t.headI, t.tail)
  | .inr q => fun t ↦ (fun a ↦ (a, t)) <$> (liftM (PermSpec.query q) : OracleComp PermSpec _)

/-- **`oa` with its coins read from the tape `t`**: a computation of `π` and `π⁻¹` alone. -/
def derand (M : ℕ) {α : Type} (oa : OracleComp RandomPermutationOracles α) (t : List (Fin (M + 1))) :
    OracleComp PermSpec α :=
  (simulateQ (tapeImpl M) oa).run' t

theorem derand_pure (M : ℕ) {α : Type} (a : α) (t : List (Fin (M + 1))) :
    derand M (pure a : OracleComp RandomPermutationOracles α) t = pure a := by
  simp [derand]

theorem derand_coin (M : ℕ) {α : Type} (n : ℕ) (k : Fin (n + 1) → OracleComp RandomPermutationOracles α)
    (t : List (Fin (M + 1))) :
    derand M (liftM (RandomPermutationOracles.query (.inl n)) >>= k) t = derand M (k (coinOf M n t.headI)) t.tail := by
  simp only [derand, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run'_eq, StateT.run_bind]
  rfl

theorem derand_perm (M : ℕ) {α : Type} (q : PermutationQuery LeanVM.Semantics.KeccakState)
    (k : LeanVM.Semantics.KeccakState → OracleComp RandomPermutationOracles α) (t : List (Fin (M + 1))) :
    derand M (liftM (RandomPermutationOracles.query (.inr q)) >>= k) t =
      (liftM (PermSpec.query q) : OracleComp PermSpec _) >>= fun a ↦ derand M (k a) t := by
  simp only [derand, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run'_eq, StateT.run_bind]
  simp only [map_bind, tapeImpl, StateT.run, bind_map_left]
  rfl

/-- **Derandomizing keeps the calls of `π` and `π⁻¹`.** -/
theorem derand_queryBound (M : ℕ) {α : Type} (oa : OracleComp RandomPermutationOracles α) :
    ∀ Q, QueryCostAtMost oa permutationCallCost Q → ∀ t, IsTotalQueryBound (derand M oa t) Q := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro Q _ t; rw [derand_pure]; trivial
  | query_bind t k ih =>
    intro Q hQ tp
    unfold QueryCostAtMost at hQ
    rw [isQueryBound_query_bind_iff] at hQ
    rcases t with n | q
    · rw [derand_coin]
      exact ih _ Q (hQ.2 (coinOf M n tp.headI)) _
    · rw [derand_perm, isTotalQueryBound_query_bind_iff]
      have h1 : 1 ≤ Q := hQ.1
      exact ⟨by omega, fun a ↦ ih a (Q - 1) (hQ.2 a) tp⟩

/-! ## Coins drawn first -/

section Run

variable {σ : Type} (impl : QueryImpl RandomPermutationOracles (StateT σ ProbComp))

/-- The permutation part of an implementation of the model. -/
def permPart : QueryImpl PermSpec (StateT σ ProbComp) := fun q ↦ impl (.inr q)

/-- An implementation answers coins as `unifSpec` does. -/
def CoinsUniform : Prop := ∀ n, impl (.inl n) = liftM ($[0..n])

theorem run_liftPerm {α : Type} (D : OracleComp PermSpec α) (s : σ) :
    (simulateQ impl (simulateQ liftPerm D)).run' s = (simulateQ (permPart impl) D).run' s := by
  congr 1
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext q
  simp [QueryImpl.apply_compose, liftPerm, permPart]

theorem tape_succ_bind (M k : ℕ) {β : Type} (f : List (Fin (M + 1)) → ProbComp β) :
    (tape M (k + 1) >>= f) = ($[0..M] >>= fun u ↦ tape M k >>= fun l ↦ f (u :: l)) := by
  simp [tape, bind_assoc]

/-- **The coins drawn first**: run by an oracle that answers coins uniformly, a computation of at most
`C ≤ k` coins of ranges dividing `M + 1` is its derandomization on a uniform tape of `k` values. -/
theorem run_tape (hc : CoinsUniform impl) (M N : ℕ) (hM : ∀ n ≤ N, (n + 1) ∣ M + 1) {α : Type}
    (oa : OracleComp RandomPermutationOracles α) :
    ∀ C, CoinBound oa C N → ∀ k, C ≤ k → ∀ s : σ,
      (simulateQ impl oa).run' s =ᵈ
        (tape M k >>= fun t ↦ (simulateQ (permPart impl) (derand M oa t)).run' s) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro C _ k _ s
    simp only [derand_pure, simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    exact (QuotientZk.evalDistEq_bind_const _ _).symm
  | query_bind t cont ih =>
    intro C hC k hk s
    unfold CoinBound at hC
    rw [isQueryBound_query_bind_iff] at hC
    rcases t with n | q
    · simp only [coinOK, coinCost] at hC
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [tape_succ_bind]
      simp only [derand_coin, List.headI_cons, List.tail_cons]
      have hl : (simulateQ impl (liftM (RandomPermutationOracles.query (.inl n)) >>= cont)).run' s =
          ($[0..n] >>= fun u ↦ (simulateQ impl (cont u)).run' s) := by
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run'_eq, StateT.run_bind, hc n]
        simp [map_bind]
      rw [hl]
      calc ($[0..n] >>= fun u ↦ (simulateQ impl (cont u)).run' s)
          =ᵈ ((coinOf M n <$> $[0..M]) >>= fun u ↦ (simulateQ impl (cont u)).run' s) :=
            EvalDistEq.bind_left (coinOf_uniform M n (hM n hC.1.2)).symm _
        _ = ($[0..M] >>= fun u ↦ (simulateQ impl (cont (coinOf M n u))).run' s) := by
            rw [bind_map_left]
        _ =ᵈ _ := EvalDistEq.bind_right _ fun u ↦
            ih (coinOf M n u) (C - 1) (hC.2 _) k' (by omega) s
    · simp only [coinOK, coinCost] at hC
      have hl : (simulateQ impl (liftM (RandomPermutationOracles.query (.inr q)) >>= cont)).run' s =
          ((impl (.inr q)).run s >>= fun z ↦ (simulateQ impl (cont z.1)).run' z.2) := by
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run'_eq, StateT.run_bind, map_bind]
      have hr : ∀ tp : List (Fin (M + 1)),
          (simulateQ (permPart impl) (derand M (liftM (RandomPermutationOracles.query (.inr q)) >>= cont) tp)).run' s =
            ((impl (.inr q)).run s >>= fun z ↦
              (simulateQ (permPart impl) (derand M (cont z.1) tp)).run' z.2) := by
        intro tp
        rw [derand_perm]
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run'_eq, StateT.run_bind, map_bind]
        rfl
      rw [hl]
      simp only [hr]
      refine EvalDistEq.trans ?_ (EvalDistEq.bind_bind_swap _ _ _).symm
      exact EvalDistEq.bind_right _ fun z ↦ ih z.1 C (hC.2 _) k hk z.2

end Run

/-! ## Closeness for every distinguisher from closeness for coin-free ones -/

section Close

variable {P σ₁ σ₂ : Type}

/-- `(n + 1)` divides `(N + 1)!` for `n ≤ N`. -/
theorem dvd_factorial_succ {N n : ℕ} (h : n ≤ N) : (n + 1) ∣ (N + 1).factorial :=
  Nat.dvd_factorial (Nat.succ_pos n) (by omega)

theorem factorial_succ_eq (N : ℕ) : (N + 1).factorial - 1 + 1 = (N + 1).factorial :=
  Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))

/-- **Closeness for distinguishers with coins.** Two games, each a first part (`X`, `Y`: a value
`z.1` handed to the distinguisher and the oracle's state `z.2`) then the distinguisher run by an
oracle (`impl₁`, `impl₂`) that answers coins uniformly: if they are `ε`-close for every coin-free
distinguisher of at most `Q` calls of `π` and `π⁻¹`, they are `ε`-close for every distinguisher of
at most `Q` such calls, coins free. -/
theorem close_of_coinFree (X : ProbComp (P × σ₁)) (Y : ProbComp (P × σ₂))
    (impl₁ : QueryImpl RandomPermutationOracles (StateT σ₁ ProbComp)) (impl₂ : QueryImpl RandomPermutationOracles (StateT σ₂ ProbComp))
    (hc₁ : CoinsUniform impl₁) (hc₂ : CoinsUniform impl₂) (ε : ℝ≥0∞) (Q : ℕ)
    (h : ∀ D₀ : P → OracleComp PermSpec Bool, (∀ p, IsTotalQueryBound (D₀ p) Q) →
      Close (X >>= fun z ↦ (simulateQ (permPart impl₁) (D₀ z.1)).run' z.2)
        (Y >>= fun z ↦ (simulateQ (permPart impl₂) (D₀ z.1)).run' z.2) ε)
    (D : P → OracleComp RandomPermutationOracles Bool) (hD : ∀ p, QueryCostAtMost (D p) permutationCallCost Q) :
    Close (X >>= fun z ↦ (simulateQ impl₁ (D z.1)).run' z.2)
      (Y >>= fun z ↦ (simulateQ impl₂ (D z.1)).run' z.2) ε := by
  classical
  -- the values the distinguisher can be handed: finitely many
  let Sx : Set P := Prod.fst '' support X
  let Sy : Set P := Prod.fst '' support Y
  have hfin : (Sx ∪ Sy).Finite :=
    ((support_finite X).image _).union ((support_finite Y).image _)
  let F := hfin.toFinset
  choose Cf Nf hCN using fun p ↦ exists_coinBound (D p)
  let C := F.sup Cf
  let N := F.sup Nf
  -- the distinguisher, off those values `false`
  let D' : P → OracleComp RandomPermutationOracles Bool := fun p ↦ if p ∈ Sx ∪ Sy then D p else pure false
  have hD'b : ∀ p, CoinBound (D' p) C N := by
    intro p
    by_cases hp : p ∈ Sx ∪ Sy
    · simp only [D', hp, ↓reduceIte]
      have hpF : p ∈ F := hfin.mem_toFinset.mpr hp
      exact (hCN p).mono (Finset.le_sup (f := Cf) hpF) (Finset.le_sup (f := Nf) hpF)
    · simp only [D', hp, ↓reduceIte]; trivial
  have hD'Q : ∀ p, QueryCostAtMost (D' p) permutationCallCost Q := by
    intro p
    by_cases hp : p ∈ Sx ∪ Sy
    · simp only [D', hp, ↓reduceIte]; exact hD p
    · simp only [D', hp, ↓reduceIte]; trivial
  let M := (N + 1).factorial - 1
  have hM : ∀ n ≤ N, (n + 1) ∣ M + 1 := fun n hn ↦ by
    simp only [M, factorial_succ_eq]; exact dvd_factorial_succ hn
  -- each game, `D` replaced by `D'`, its coins drawn first
  have hX : (X >>= fun z ↦ (simulateQ impl₁ (D z.1)).run' z.2) =ᵈ
      (tape M C >>= fun t ↦ X >>= fun z ↦
        (simulateQ (permPart impl₁) (derand M (D' z.1) t)).run' z.2) := by
    calc (X >>= fun z ↦ (simulateQ impl₁ (D z.1)).run' z.2)
        =ᵈ (X >>= fun z ↦ (simulateQ impl₁ (D' z.1)).run' z.2) := by
          refine EvalDistEq.bind_congr_of_support _ fun z hz ↦ ?_
          have : z.1 ∈ Sx ∪ Sy := Or.inl ⟨z, hz, rfl⟩
          simp only [D', this, ↓reduceIte]; exact EvalDistEq.rfl
      _ =ᵈ (X >>= fun z ↦ tape M C >>= fun t ↦
            (simulateQ (permPart impl₁) (derand M (D' z.1) t)).run' z.2) :=
          EvalDistEq.bind_right _ fun z ↦
            run_tape impl₁ hc₁ M N hM (D' z.1) C (hD'b _) C le_rfl z.2
      _ =ᵈ _ := EvalDistEq.bind_bind_swap _ _ _
  have hY : (Y >>= fun z ↦ (simulateQ impl₂ (D z.1)).run' z.2) =ᵈ
      (tape M C >>= fun t ↦ Y >>= fun z ↦
        (simulateQ (permPart impl₂) (derand M (D' z.1) t)).run' z.2) := by
    calc (Y >>= fun z ↦ (simulateQ impl₂ (D z.1)).run' z.2)
        =ᵈ (Y >>= fun z ↦ (simulateQ impl₂ (D' z.1)).run' z.2) := by
          refine EvalDistEq.bind_congr_of_support _ fun z hz ↦ ?_
          have : z.1 ∈ Sx ∪ Sy := Or.inr ⟨z, hz, rfl⟩
          simp only [D', this, ↓reduceIte]; exact EvalDistEq.rfl
      _ =ᵈ (Y >>= fun z ↦ tape M C >>= fun t ↦
            (simulateQ (permPart impl₂) (derand M (D' z.1) t)).run' z.2) :=
          EvalDistEq.bind_right _ fun z ↦
            run_tape impl₂ hc₂ M N hM (D' z.1) C (hD'b _) C le_rfl z.2
      _ =ᵈ _ := EvalDistEq.bind_bind_swap _ _ _
  have hmid := QuotientZk.Close.bind_const (tape M C) _ _ ε fun t ↦
    h (fun p ↦ derand M (D' p) t) fun p ↦ derand_queryBound M (D' p) Q (hD'Q p) t
  refine ((Close.of_evalDistEq hX).trans (hmid.trans (Close.of_evalDistEq hY.symm))).mono ?_
  simp

end Close

/-! ## The statement's experiments -/

/-- The real experiment's first part: the honest proof over the lazily sampled permutation, with
the permutation's edges after it. -/
noncomputable def realPrefix (stmt : Statement) (w : Secret) :
    ProbComp (Option Proof × PermutationEdges LeanVM.Semantics.KeccakState) :=
  (simulateQ lazyRandomPermutationOracles (do
    let coins ← sampleCoins
    prover queryPermutation stmt w coins)).run []

theorem realExperiment_eq (stmt : Statement) (w : Secret) (D : Distinguisher) :
    realExperiment stmt w D = (realPrefix stmt w >>= fun z ↦
      (simulateQ lazyRandomPermutationOracles (D z.1)).run' z.2) := by
  simp only [realExperiment, runWithRandomPermutation, realPrefix, bind_assoc, simulateQ_bind,
    StateT.run'_eq, StateT.run_bind, map_bind]

theorem idealExperimentWith_eq {S : Type} (s₀ : S) (sim : Statement → StateT S ProbComp (Option Proof))
    (simOracle : QueryImpl RandomPermutationOracles (StateT S ProbComp)) (stmt : Statement)
    (D : Distinguisher) :
    idealExperimentWith s₀ sim simOracle stmt D = ((sim stmt).run s₀ >>= fun z ↦
      (simulateQ simOracle (D z.1)).run' z.2) := by
  simp only [idealExperimentWith, StateT.run'_eq, StateT.run_bind, map_bind]

theorem coinsUniform_lazy : CoinsUniform lazyRandomPermutationOracles := fun _ ↦ rfl

theorem coinsUniform_simOracle : CoinsUniform Simulator.simOracle := fun _ ↦ rfl

/-- **Zero knowledge against coin-free distinguishers, for a simulator**: `ZeroKnowledgeWith`'s
statement for every distinguisher of `π` and `π⁻¹` alone (`liftPerm`), its calls bounded by
`IsTotalQueryBound`. -/
def ZeroKnowledgeCoinFreeWith {S : Type} (s₀ : S) (sim : Statement → StateT S ProbComp (Option Proof))
    (simOracle : QueryImpl RandomPermutationOracles (StateT S ProbComp)) (ζ : ℕ → ℝ≥0∞) : Prop :=
  ∀ (stmt : Statement) (w : Secret), Relation stmt w →
  ∀ (D : Option Proof → OracleComp PermSpec Bool) (Q : ℕ), (∀ proof, IsTotalQueryBound (D proof) Q) →
    Close (realExperiment stmt w fun proof ↦ simulateQ liftPerm (D proof))
      (idealExperimentWith s₀ sim simOracle stmt fun proof ↦ simulateQ liftPerm (D proof)) (ζ Q)

/-- **`ZeroKnowledgeWith` from coin-free distinguishers**: for a simulator whose oracle answers coins
uniformly, the coins of a distinguisher change nothing. -/
theorem zeroKnowledgeWith_of_coinFree {S : Type} (s₀ : S)
    (sim : Statement → StateT S ProbComp (Option Proof))
    (simOracle : QueryImpl RandomPermutationOracles (StateT S ProbComp))
    (hsim : CoinsUniform simOracle) (ζ : ℕ → ℝ≥0∞) (h : ZeroKnowledgeCoinFreeWith s₀ sim simOracle ζ) :
    ZeroKnowledgeWith s₀ sim simOracle ζ := by
  intro stmt w hw D Q hD
  have hc := close_of_coinFree (realPrefix stmt w) ((sim stmt).run s₀)
    lazyRandomPermutationOracles simOracle coinsUniform_lazy hsim
    (ζ Q) Q (fun D₀ hD₀ ↦ by
      have h' := h stmt w hw D₀ Q hD₀
      rw [realExperiment_eq, idealExperimentWith_eq] at h'
      simp only [run_liftPerm] at h'
      exact h') D hD
  rw [← realExperiment_eq, ← idealExperimentWith_eq] at hc
  exact hc

/-- **Zero knowledge against coin-free distinguishers** for this package's `simulator`. -/
def ZeroKnowledgeCoinFree (ζ : ℕ → ℝ≥0∞) : Prop :=
  ZeroKnowledgeCoinFreeWith (S := Simulator.SimState) {} simulator Simulator.simOracle ζ

/-- **`ZeroKnowledge` from coin-free distinguishers**: the coins of a distinguisher change nothing. -/
theorem zeroKnowledge_of_coinFree (ζ : ℕ → ℝ≥0∞) (h : ZeroKnowledgeCoinFree ζ) :
    ZeroKnowledge ζ :=
  zeroKnowledgeWith_of_coinFree _ _ _ coinsUniform_simOracle ζ h

end PcsQuotient.EndToEnd
