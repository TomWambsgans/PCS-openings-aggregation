-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import QuotientSecurity.Hiding.Gadget

/-!
# The hidden layouts with the gadget (`opening::Layout::hidden` since the gadget)

`crates/quotient/HIDING.md`, "The layout". A stack has lanes `ι` at lane indices `pos l` and
entries `Y`. Its unknowns:

* the entries `first` (every lane's first piece below the gadget, `0 .. D`) are uniform in every lane;
* the **gadget's entries** `gent p i` (pattern `p`, entry `i`) are uniform in every lane, but pattern
  `p < 2`'s second lane `pairB p` holds its first lane `pairA p`'s value there, and the overflow lane
  `ov` holds zero at pattern 2's;
* the **random lanes** (`isRand`) are uniform;
* the **overflow lane** holds the table at the entries `held`, and is uniform elsewhere;
* every other entry is the table's.

The stack is `stackD d + stackR r`, `r` uniform. The claims weigh the table's entries; the **gadget**
is one more claim, of value zero, with weight `gadgetW β` (`β i` on pattern `p`'s lanes at its entry
`i`), which `stackR` meets in characteristic 2 (a pair holds one value twice, the overflow lane zero).
-/

namespace QuotientSecurity.Hiding

open Finset

set_option linter.unusedSectionVars false

variable {K E : Type} [Field K] [Field E] [Algebra K E]
variable {ι Y : Type} [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y]

/-- A hidden layout with the gadget. -/
structure GadgetLayout (ι Y : Type) where
  isRand : ι → Prop
  [decRand : DecidablePred isRand]
  /-- The overflow lane (pattern 2's lane). -/
  ov : ι
  /-- The weightless random entries of every lane: the first piece below the gadget. -/
  first : Finset Y
  /-- The overflow lane's table entries. -/
  held : Finset Y
  /-- The gadget's entries: pattern `p`, entry `i`. -/
  gent : Fin 3 → Fin 3 → Y
  /-- Patterns 0 and 1: the lane holding the pair's value, and the lane copying it. -/
  pairA : Fin 2 → ι
  pairB : Fin 2 → ι
  gent_inj : ∀ p i p' i', gent p i = gent p' i' → p = p' ∧ i = i'
  gent_first : ∀ p i, gent p i ∉ first
  gent_held : ∀ p i, gent p i ∉ held
  held_first : Disjoint held first
  not_rand_ov : ¬ isRand ov
  not_rand_pairB : ∀ p, ¬ isRand (pairB p)
  pairB_ne_ov : ∀ p, pairB p ≠ ov
  pairA_ne_pairB : ∀ p, pairA p ≠ pairB p

attribute [instance] GadgetLayout.decRand

namespace GadgetLayout

variable (L : GadgetLayout ι Y)

/-- Entry `y` is one of pattern `p`'s. -/
def AtPat (p : Fin 3) (y : Y) : Prop := ∃ i, L.gent p i = y

instance (p : Fin 3) (y : Y) : Decidable (L.AtPat p y) := by
  unfold AtPat; infer_instance

/-- Entry `y` is one of the gadget's. -/
def AtGadget (y : Y) : Prop := ∃ p, L.AtPat p y

instance (y : Y) : Decidable (L.AtGadget y) := by
  unfold AtGadget; infer_instance

/-- The stack's random entries (before the gadget's copies and zeros). -/
def randPos (l : ι) (y : Y) : Prop :=
  y ∈ L.first ∨ L.AtGadget y ∨ L.isRand l ∨ (l = L.ov ∧ y ∉ L.held)

instance (l : ι) (y : Y) : Decidable (L.randPos l y) := by
  unfold randPos; infer_instance

/-- The lane whose random value entry `y` of lane `l` holds: a pair's second lane copies its first at
the pair's entries. -/
def copyOf (y : Y) (l : ι) : ι :=
  if L.AtPat 0 y ∧ l = L.pairB 0 then L.pairA 0
  else if L.AtPat 1 y ∧ l = L.pairB 1 then L.pairA 1 else l

/-- The overflow lane is zero at pattern 2's entries. -/
def ZeroAt (l : ι) (y : Y) : Prop := L.AtPat 2 y ∧ l = L.ov

instance (l : ι) (y : Y) : Decidable (L.ZeroAt l y) := by
  unfold ZeroAt; infer_instance

/-- The randomness's part of the stack. -/
def stackR : (ι → Y → K) →ₗ[K] (ι → Y → K) where
  toFun r l y := if L.randPos l y ∧ ¬ L.ZeroAt l y then r (L.copyOf y l) y else 0
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

/-- The gadget's weight: `β i` times pattern `p`'s lanes (by lane index) at its entry `i`. -/
def gadgetW (pos : ι → (Fin 6 → Bool)) (β : Fin 3 → E) : ι → Y → E := fun l y =>
  ∑ p : Fin 3, ∑ i : Fin 3, if L.gent p i = y then β i * patE p (pos l) else 0

/-- The weights a design's claims put: nothing on the first pieces, at the gadget's entries, on the
random lanes, nor on the overflow lane off `held`. -/
structure WeightsFit {m : ℕ} (Wc : Fin m → ι → Y → E) : Prop where
  first : ∀ c l, ∀ y ∈ L.first, Wc c l y = 0
  gadget : ∀ c l y, L.AtGadget y → Wc c l y = 0
  rand : ∀ c l y, L.isRand l → Wc c l y = 0
  off_held : ∀ c y, y ∉ L.held → Wc c L.ov y = 0

/-- The claims with the gadget as the last, of value zero. -/
def withGadget {m : ℕ} (Wc : Fin m → ι → Y → E) (G : ι → Y → E) : Fin (m + 1) → ι → Y → E :=
  Fin.snoc Wc G

/-- **Condition (R)** for a layout with the gadget: through the lane rounds, the changes of the
randomness that keep `f¹` span the round values whose last running claim is unchanged. -/
def RoundsReached {m : ℕ} (pos : ι → (Fin 6 → Bool)) (Wc : Fin m → ι → Y → E) (lam : Fin m → E)
    (φ : Fin 6 → E) : Prop :=
  LinearMap.ker (lastMap (K := K) φ) ≤ Submodule.span K
    (roundsMap pos φ (HiddenLayout.combinedW pos Wc lam) ''
      kerMoves (HiddenLayout.foldW pos φ) L.first (LinearMap.range (L.stackR (K := K))))

end GadgetLayout

end QuotientSecurity.Hiding
