-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Hiding.Model
import QuotientSecurity.Hiding.Span

/-!
# The hidden layouts of `crates/quotient` (`opening::Layout::hidden`)

A hidden stack has lanes `ι` (at lane indices `pos l : Fin k → Bool`, `k = 6`, the bits of `l`) of
entries `Y` (`2^ℓ` of them). Its unknowns:

* **every lane's first piece** (`first`, the entries `0 .. 2^s`) is uniform;
* the **random lanes** (`isRand`) are uniform; one of them is the **share** lane;
* the **overflow** lane `ov` holds the table at the entries `held` (its pieces `1 .. H`), plus the
  share lane's value there (so the share lane is one share of the overflow lane's table there), and is
  uniform at the other entries;
* every other entry (the block lanes past their first piece, and the overflow lane at `held`) is the
  table's.

So the stack is `stackD d + stackR r`: the table's part and the randomness's part, both `K`-linear
(`stackD`, `stackR`), `r` uniform. A claim at a point weighs the stack by `Wc c l y`; in the design it
weighs nothing on the first pieces, on the random lanes but the share, on the overflow and share lanes
off `held`, and weighs the share lane as the overflow lane at `held` (in characteristic 2, `W + W = 0`,
which is all `hW4` asks). Then the randomness weighs nothing in any claim (`claims_stackR`).

`hidden_view_evalDistEq` is `HIDING.md`'s theorem for this layout: at challenges where three random
lanes other than the share have independent fold weights (condition (S)) and the randomness reaches
the lane rounds' 33 dimensions (condition (R), `RoundsReached`), two tables with the same claims give
identically distributed views, whatever is computed from them. `hidden_prEvent_le` averages over
uniform challenges: the views' statistical distance is at most the probability of (R) failing plus
`(|K|^2 + |K| + 2k + 2)/|E|`. `random_lane_patterns` checks the design's lanes (`1, 7, 13` for the
witness table, `1, 11, 21` for the quotient table) meet the hypothesis of the (S) bound.
-/

namespace QuotientSecurity.Hiding

open Finset OracleComp

set_option linter.unusedSectionVars false

variable {K E : Type} [Field K] [Field E] [Algebra K E]
variable {ι Y Q : Type} [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y] [Fintype Q]
  [DecidableEq Q]

/-- A hidden layout: which lanes are random, the overflow and share lanes, the first piece and the
entries where the overflow lane holds the table. -/
structure HiddenLayout (ι Y : Type) where
  isRand : ι → Prop
  [decRand : DecidablePred isRand]
  ov : ι
  share : ι
  first : Finset Y
  held : Finset Y
  rand_share : isRand share
  not_rand_ov : ¬ isRand ov
  held_first : Disjoint held first

attribute [instance] HiddenLayout.decRand

namespace HiddenLayout

variable (L : HiddenLayout ι Y)

theorem share_ne_ov : L.share ≠ L.ov := fun h => L.not_rand_ov (h ▸ L.rand_share)

/-- The stack's random entries (the share lane's at `held` also enter the overflow lane's). -/
def randPos (l : ι) (y : Y) : Prop := y ∈ L.first ∨ L.isRand l ∨ (l = L.ov ∧ y ∉ L.held)

instance (l : ι) (y : Y) : Decidable (L.randPos l y) := by
  unfold randPos
  infer_instance

/-- The randomness's part of the stack. -/
def stackR : (ι → Y → K) →ₗ[K] (ι → Y → K) where
  toFun r l y := (if L.randPos l y then r l y else 0) +
    (if l = L.ov ∧ y ∈ L.held then r L.share y else 0)
  map_add' r r' := by
    funext l y
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c r := by
    funext l y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- The table's part of the stack. -/
def stackD : (ι → Y → K) →ₗ[K] (ι → Y → K) where
  toFun d l y := if L.randPos l y then 0 else d l y
  map_add' d d' := by
    funext l y
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c d := by
    funext l y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- The randomness covers every stack that is zero past the first piece. -/
theorem onFirst_mem_range (T : ι → Y → K) (hT : OnFirst L.first T) :
    T ∈ LinearMap.range (L.stackR (K := K)) := by
  refine ⟨T, ?_⟩
  funext l y
  show (if L.randPos l y then T l y else 0) +
    (if l = L.ov ∧ y ∈ L.held then T L.share y else 0) = T l y
  by_cases hy : y ∈ L.first
  · have hheld : y ∉ L.held := Finset.disjoint_right.mp L.held_first hy
    simp [randPos, hy, hheld]
  · have h1 : T l y = 0 := hT l y hy
    have h2 : T L.share y = 0 := hT L.share y hy
    simp [h1, h2]

/-- A change at one entry on lanes that are random (but the share) is a change of the randomness. -/
theorem column_mem_range (y : Y) (k : ι → K) (hk : ∀ l, k l ≠ 0 → L.isRand l ∧ l ≠ L.share) :
    (fun l y' => if y' = y then k l else 0) ∈ LinearMap.range (L.stackR (K := K)) := by
  refine ⟨fun l y' => if y' = y then k l else 0, ?_⟩
  funext l y'
  show (if L.randPos l y' then (if y' = y then k l else 0) else 0) +
    (if l = L.ov ∧ y' ∈ L.held then (if y' = y then k L.share else 0) else 0)
      = if y' = y then k l else 0
  have hs : k L.share = 0 := by
    by_contra h
    exact (hk _ h).2 rfl
  by_cases hyy : y' = y
  · subst hyy
    by_cases hkl : k l = 0
    · simp [hkl, hs]
    · have hr : L.randPos l y' := Or.inr (Or.inl (hk l hkl).1)
      simp [hr, hs]
  · simp [hyy]

/-! ### Claims -/

/-- The claims, as weights on the stack. -/
def claimsMap {m : ℕ} (Wc : Fin m → ι → Y → E) : (ι → Y → K) →ₗ[K] (Fin m → E) where
  toFun T c := ∑ l, ∑ y, Wc c l y * algebraMap K E (T l y)
  map_add' T T' := by
    funext c
    simp [mul_add, sum_add_distrib]
  map_smul' a T := by
    funext c
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, mul_sum, Algebra.smul_def]
    refine sum_congr rfl fun l _ => sum_congr rfl fun y _ => ?_
    ring

/-- What the design's claims weigh: nothing on the first pieces, on the random lanes but the share,
on the overflow and share lanes off `held`; the share lane against the overflow lane at `held`. -/
structure WeightsFit {m : ℕ} (Wc : Fin m → ι → Y → E) : Prop where
  first : ∀ c l, ∀ y ∈ L.first, Wc c l y = 0
  rand : ∀ c l y, L.isRand l → l ≠ L.share → Wc c l y = 0
  off_held : ∀ c y, y ∉ L.held → Wc c L.ov y = 0 ∧ Wc c L.share y = 0
  share : ∀ c, ∀ y ∈ L.held, Wc c L.share y + Wc c L.ov y = 0

/-- **The randomness weighs nothing in the claims** (the share cancels against the overflow lane). -/
theorem claims_stackR {m : ℕ} (Wc : Fin m → ι → Y → E) (hW : L.WeightsFit Wc)
    (r : ι → Y → K) : claimsMap Wc (L.stackR r) = 0 := by
  funext c
  show ∑ l, ∑ y, Wc c l y * algebraMap K E ((if L.randPos l y then r l y else 0) +
    (if l = L.ov ∧ y ∈ L.held then r L.share y else 0)) = 0
  have hpt : ∀ l y, Wc c l y * algebraMap K E ((if L.randPos l y then r l y else 0) +
      (if l = L.ov ∧ y ∈ L.held then r L.share y else 0))
      = (if l = L.share then (if y ∈ L.held then Wc c L.share y * algebraMap K E (r L.share y)
            else 0) else 0) +
        (if l = L.ov then (if y ∈ L.held then Wc c L.ov y * algebraMap K E (r L.share y)
            else 0) else 0) := by
    intro l y
    have hso := L.share_ne_ov
    by_cases hy1 : y ∈ L.first
    · have hh : y ∉ L.held := Finset.disjoint_right.mp L.held_first hy1
      simp [hW.first c l y hy1, hh]
    by_cases hls : l = L.share
    · subst hls
      have hr : L.randPos L.share y := Or.inr (Or.inl L.rand_share)
      by_cases hh : y ∈ L.held
      · simp [hr, hh, hso]
      · simp [hr, hh, hso, (hW.off_held c y hh).2]
    by_cases hlo : l = L.ov
    · subst hlo
      by_cases hh : y ∈ L.held
      · have hr : ¬ L.randPos L.ov y := by
          simp [randPos, hy1, L.not_rand_ov, hh]
        simp [hr, hh, Ne.symm hso]
      · simp [hh, Ne.symm hso, (hW.off_held c y hh).1]
    by_cases hrl : L.isRand l
    · simp [hW.rand c l y hrl hls, hls, hlo]
    · have hr : ¬ L.randPos l y := by simp [randPos, hy1, hrl, hlo]
      simp [hr, hls, hlo]
  rw [sum_comm]
  refine sum_eq_zero fun y _ => ?_
  simp only [hpt, sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
  split_ifs with hh
  · rw [← add_mul, hW.share c y hh, zero_mul]
  · simp

/-! ### The lane rounds of the combined claim -/

variable {k : ℕ}

/-- The claims' combined weight `Σ_c λ_c W_c`, at the lane indices. -/
def combinedW {m : ℕ} (pos : ι → (Fin k → Bool)) (Wc : Fin m → ι → Y → E) (lam : Fin m → E) :
    LTable E Y k :=
  fun b y => ∑ l, if pos l = b then ∑ c, lam c * Wc c l y else 0

theorem ip_combinedW {m : ℕ} (pos : ι → (Fin k → Bool)) (hpos : Function.Injective pos)
    (Wc : Fin m → ι → Y → E) (lam : Fin m → E) (T : ι → Y → K) :
    ip (combinedW pos Wc lam) (lift pos T) = ∑ c, lam c * claimsMap (K := K) Wc T c := by
  simp only [ip, combinedW, lift, claimsMap, LinearMap.coe_mk, AddHom.coe_mk]
  have hpt : ∀ (b : Fin k → Bool) (y : Y),
      (∑ l, if pos l = b then ∑ c, lam c * Wc c l y else 0) *
        (∑ l, if pos l = b then algebraMap K E (T l y) else 0)
      = ∑ l, if pos l = b then (∑ c, lam c * Wc c l y) * algebraMap K E (T l y) else 0 := by
    intro b y
    by_cases hb : ∃ l, pos l = b
    · obtain ⟨l0, rfl⟩ := hb
      have hu : ∀ (f : ι → E), (∑ l, if pos l = pos l0 then f l else 0) = f l0 := by
        intro f
        rw [sum_eq_single l0]
        · simp
        · intro l _ hl
          simp [hpos.ne hl]
        · simp
      rw [hu, hu, hu]
    · push Not at hb
      simp [hb]
  simp only [hpt]
  have hcollapse : ∀ F : ι → Y → E,
      (∑ b : Fin k → Bool, ∑ y, ∑ l, if pos l = b then F l y else 0) = ∑ l, ∑ y, F l y := by
    intro F
    calc (∑ b : Fin k → Bool, ∑ y, ∑ l, if pos l = b then F l y else 0)
        = ∑ y, ∑ b : Fin k → Bool, ∑ l, if pos l = b then F l y else 0 := sum_comm
      _ = ∑ y, ∑ l, ∑ b : Fin k → Bool, if pos l = b then F l y else 0 :=
          sum_congr rfl fun y _ => sum_comm
      _ = ∑ l, ∑ y, ∑ b : Fin k → Bool, if pos l = b then F l y else 0 := sum_comm
      _ = ∑ l, ∑ y, F l y := sum_congr rfl fun l _ => sum_congr rfl fun y _ => by simp
  rw [hcollapse (fun l y => (∑ c, lam c * Wc c l y) * algebraMap K E (T l y))]
  calc ∑ l, ∑ y, (∑ c, lam c * Wc c l y) * algebraMap K E (T l y)
      = ∑ l, ∑ y, ∑ c, lam c * (Wc c l y * algebraMap K E (T l y)) := by
        refine sum_congr rfl fun l _ => sum_congr rfl fun y _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun c _ => ?_
        ring
    _ = ∑ l, ∑ c, ∑ y, lam c * (Wc c l y * algebraMap K E (T l y)) :=
        sum_congr rfl fun l _ => sum_comm
    _ = ∑ c, ∑ l, ∑ y, lam c * (Wc c l y * algebraMap K E (T l y)) := sum_comm
    _ = ∑ c, lam c * ∑ l, ∑ y, Wc c l y * algebraMap K E (T l y) := by
        refine sum_congr rfl fun c _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun l _ => ?_
        rw [mul_sum]

/-- The fold weights of the stack's lanes: `eq(φ, pos l)`. -/
def foldW (pos : ι → (Fin k → Bool)) (φ : Fin k → E) : ι → E := fun l => eqW φ (pos l)

/-- **Condition (R)**: through the lane rounds, the changes of the randomness that keep `f¹` span the
round values whose last running claim is unchanged. -/
def RoundsReached {m : ℕ} (pos : ι → (Fin k → Bool)) (Wc : Fin m → ι → Y → E) (lam : Fin m → E)
    (φ : Fin k → E) : Prop :=
  LinearMap.ker (lastMap (K := K) φ) ≤ Submodule.span K
    (roundsMap pos φ (combinedW pos Wc lam) ''
      kerMoves (foldW pos φ) L.first (LinearMap.range (L.stackR (K := K))))

/-- **Condition (S)**: three random lanes other than the share whose fold weights are independent. -/
def FoldSpans (pos : ι → (Fin k → Bool)) (φ : Fin k → E) : Prop :=
  ∃ r : Fin 3 → ι, (∀ i, L.isRand (r i) ∧ r i ≠ L.share) ∧
    LinearIndependent K fun i => foldW pos φ (r i)

/-- (S) lets the randomness at any entry past the first piece move `f¹` anywhere. -/
theorem foldSpans_moves [FiniteDimensional K E] (h3 : Module.finrank K E = 3)
    (pos : ι → (Fin k → Bool)) (φ : Fin k → E) (hS : L.FoldSpans (K := K) pos φ) :
    ∀ y ∉ L.first, ∀ e : E, ∃ ρ ∈ LinearMap.range (L.stackR (K := K)),
      OnColumn y ρ ∧ foldMap (foldW pos φ) ρ y = e := by
  classical
  obtain ⟨r, hr, hind⟩ := hS
  intro y _ e
  have htop : Submodule.span K (Set.range fun i => foldW pos φ (r i)) = ⊤ :=
    hind.span_eq_top_of_card_eq_finrank' (by simp [h3])
  have he : e ∈ Submodule.span K (Set.range fun i => foldW pos φ (r i)) := htop ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp he
  set kv : ι → K := fun l => ∑ i, if r i = l then c i else 0
  have hk : ∀ l, kv l ≠ 0 → L.isRand l ∧ l ≠ L.share := by
    intro l hl
    by_contra hno
    apply hl
    refine sum_eq_zero fun i _ => ?_
    have : r i ≠ l := fun h => hno (h ▸ hr i)
    simp [this]
  refine ⟨_, L.column_mem_range y kv hk, ?_, ?_⟩
  · intro l y' hy'
    simp [hy']
  · show ∑ l, foldW pos φ l * algebraMap K E (if y = y then kv l else 0) = e
    simp only [ite_true, kv, map_sum, mul_sum]
    rw [sum_comm, ← hc]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_eq_single (r i)]
    · simp [Algebra.smul_def, mul_comm]
    · intro l _ hl
      simp [Ne.symm hl]
    · simp

/-! ### The theorem for the hidden layouts -/

/-- **`HIDING.md`'s theorem.** At challenges `(λ, φ)` meeting (S) and (R), with the first piece's
codeword at the opened positions onto (Q), the opening's view up to the first fold of two tables
with the same claims, and anything computed from it, are identically distributed. -/
theorem hidden_view_evalDistEq [FiniteDimensional K E] (h3 : Module.finrank K E = 3)
    [SampleableType (ι → Y → K)] {m : ℕ} (pos : ι → (Fin k → Bool)) (hpos : Function.Injective pos)
    (Wc : Fin m → ι → Y → E) (hW : L.WeightsFit Wc) (enc : Q → Y → K)
    (hQ : Function.Surjective (firstEval enc L.first)) (lam : Fin m → E) (φ : Fin k → E)
    (hS : L.FoldSpans (K := K) pos φ) (hR : L.RoundsReached (K := K) pos Wc lam φ)
    {O : Type} (g : (Fin k → E × E) × (Y → E) × (Q → ι → K) → O) {d d' : ι → Y → K}
    (hd : claimsMap (K := K) Wc (L.stackD d) = claimsMap Wc (L.stackD d')) :
    (fun r => g (viewMap (roundsMap pos φ (combinedW pos Wc lam)) (foldW pos φ) enc
        (L.stackD d + L.stackR r))) <$> ($ᵗ (ι → Y → K))
      =ᵈ (fun r => g (viewMap (roundsMap pos φ (combinedW pos Wc lam)) (foldW pos φ) enc
        (L.stackD d' + L.stackR r))) <$> ($ᵗ (ι → Y → K)) := by
  have hWb : ∀ b, ∀ y ∈ L.first, combinedW pos Wc lam b y = 0 := by
    intro b y hy
    simp [combinedW, hW.first _ _ y hy]
  refine level0_view_evalDistEq (foldW pos φ) enc L.first (roundsMap pos φ (combinedW pos Wc lam))
    (claimsMap Wc) L.stackD L.stackR (LinearMap.ker (lastMap (K := K) φ))
    (fun T hT => L.onFirst_mem_range T hT)
    (fun T hT => roundsMap_eq_zero pos φ _ L.first hWb T hT)
    (L.claims_stackR Wc hW) hQ (L.foldSpans_moves h3 pos φ hS) ?_ hR hd g
  intro T hT hfold
  refine roundsMap_mem_ker pos φ _ L.first hWb T ?_ hfold
  rw [ip_combinedW pos hpos, hT]
  simp

/-- **Averaged over the challenges.** With `λ` from any uniform `γ` and `φ` uniform in `E^k`, the
two tables' experiments (challenges, then anything computed from the view) give every event
probabilities that differ by at most the probability of (S) or (R) failing. -/
theorem hidden_prEvent_le [FiniteDimensional K E] (h3 : Module.finrank K E = 3)
    [SampleableType (ι → Y → K)] {Γ : Type} [SampleableType Γ] [Fintype Γ] [Fintype E]
    [SampleableType E] {m : ℕ} (pos : ι → (Fin k → Bool)) (hpos : Function.Injective pos)
    (Wc : Fin m → ι → Y → E) (hW : L.WeightsFit Wc) (enc : Q → Y → K)
    (hQ : Function.Surjective (firstEval enc L.first)) (lam : Γ → Fin m → E)
    {O : Type} (g : Γ × (Fin k → E) → (Fin k → E × E) × (Y → E) × (Q → ι → K) → O)
    {d d' : ι → Y → K} (hd : claimsMap (K := K) Wc (L.stackD d) = claimsMap Wc (L.stackD d'))
    (S : (Γ × (Fin k → E)) × O → Prop) :
    let run := fun (x : ι → Y → K) (c : Γ × (Fin k → E)) =>
      (fun r => g c (viewMap (roundsMap pos c.2 (combinedW pos Wc (lam c.1))) (foldW pos c.2) enc
        (L.stackD x + L.stackR r))) <$> ($ᵗ (ι → Y → K))
    Pr{let o ← withChallenges (run d)}[S o]
      ≤ Pr{let o ← withChallenges (run d')}[S o]
        + Pr{let c ← $ᵗ (Γ × (Fin k → E))}[¬ (L.FoldSpans (K := K) pos c.2 ∧
            L.RoundsReached (K := K) pos Wc (lam c.1) c.2)] := by
  intro run
  refine prEvent_le_add_prEvent_bad (run d) (run d') _ (fun c hc => ?_) S
  exact L.hidden_view_evalDistEq h3 pos hpos Wc hW enc hQ (lam c.1) c.2 hc.1 hc.2 (g c) hd

end HiddenLayout

/-! ### The design's random lanes -/

/-- Lane `l`'s index: its six bits, bit `i` the variable `i`. -/
def laneBits (l : Fin 64) : Fin 6 → Bool := fun i => (l : ℕ).testBit i

/-- The witness table's random lanes `1, 7, 13` (and the quotient table's `1, 11, 21`) have the
coordinate pattern of `card_not_linearIndependent_le`, at `a = 1`, `b = 2`. -/
theorem random_lane_patterns :
    (laneBits 1 1 = laneBits 13 1 ∧ laneBits 7 1 = !laneBits 1 1 ∧ laneBits 1 2 ≠ laneBits 13 2) ∧
    (laneBits 1 1 = laneBits 21 1 ∧ laneBits 11 1 = !laneBits 1 1 ∧ laneBits 1 2 ≠ laneBits 21 2) := by
  decide

theorem laneBits_injective : Function.Injective laneBits := by
  decide

end QuotientSecurity.Hiding
