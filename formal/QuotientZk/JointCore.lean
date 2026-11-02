-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.EvalDist.ProbabilityBounds

/-!
# Joint honest-verifier zero knowledge: the hybrid

The interactive protocol, at fixed challenges `c`, shows the honest verifier

* the reduction's messages `red c m` (the five field elements), a function of the **masks** `m`;
* the public wiring table's opening `wir c`;
* the two secret tables' openings `open₁ c (tab₁ c m) r₁`, `open₂ c (tab₂ c m) r₂`: the witness
  table and the quotient table, laid on their hidden stacks, are functions of the masks (and of the
  witness), and each opening has its own **padding** `rᵢ`, uniform and independent of the masks.

The prover's randomness is `(m, r₁, r₂)`, uniform (`Model.view`).

**The hybrid** (`Model.view_evalDistEq`). Fix the masks. Each opening hides its table given its
claims (`Hides`: two tables with the same claims give the same distribution of views, F3), and the
honest table has the claims of the simulator's table built from the reduction's messages (`hT₁`,
`hT₂`: both are the verifier's claims, which it computes from the five values). So each opening's
view may be replaced by the view of the simulator's table: the whole view is then a function of the
reduction's messages and fresh paddings, and the messages are simulated (`hred`, F1). The
openings reveal nothing of the masks or the witness beyond the claims, which the five values
already determine: this is what lets F1's zero knowledge, proved for ideal commitments, carry over.

**The simulator** (`simulate`) reads only public things: the challenges, the reduction's simulator
`simRed`, the public tables `simT₁`, `simT₂` it builds from the simulated messages, the honest
opening algorithms `open₁`, `open₂` (run on those tables with fresh paddings), and the wiring
opening. It is a plain definition (`#print axioms` in `Joint.lean`).
-/

open OracleComp

namespace QuotientZk.Joint

/-! ## The model -/

/-- The honest interactive protocol, as the joint argument sees it, at challenges `c : Ch`. -/
structure Model (Ch Mk R₁ R₂ V₀ W D₁ D₂ V₁ V₂ C₁ C₂ : Type) where
  /-- The reduction's messages (the five field elements), a function of the masks. -/
  red : Ch → Mk → V₀
  /-- The public wiring table's opening. -/
  wir : Ch → W
  /-- The witness table laid on its stack, a function of the masks (and of the witness). -/
  tab₁ : Ch → Mk → D₁
  /-- The quotient table laid on its stack. -/
  tab₂ : Ch → Mk → D₂
  /-- The honest opening of a table with its padding: the view it gives. -/
  open₁ : Ch → D₁ → R₁ → V₁
  open₂ : Ch → D₂ → R₂ → V₂
  /-- The claims an opening proves of a table. -/
  cl₁ : Ch → D₁ → C₁
  cl₂ : Ch → D₂ → C₂

variable {Ch Mk R₁ R₂ V₀ W D₁ D₂ V₁ V₂ C₁ C₂ : Type}

/-- **The honest view**: the reduction's messages, the wiring opening, the two secret openings, for
the prover's randomness `s = (masks, padding₁, padding₂)`. -/
def Model.view (M : Model Ch Mk R₁ R₂ V₀ W D₁ D₂ V₁ V₂ C₁ C₂) (c : Ch) (s : Mk × R₁ × R₂) :
    V₀ × W × V₁ × V₂ :=
  (M.red c s.1, M.wir c, M.open₁ c (M.tab₁ c s.1) s.2.1, M.open₂ c (M.tab₂ c s.1) s.2.2)

/-- **The simulator.** From the challenges only: the reduction's simulated messages `v`, then the
honest openings of the public tables `simT₁ c v`, `simT₂ c v` with fresh paddings, and the wiring
opening. -/
def simulate [SampleableType R₁] [SampleableType R₂] (wir : Ch → W)
    (open₁ : Ch → D₁ → R₁ → V₁) (open₂ : Ch → D₂ → R₂ → V₂) (simRed : Ch → ProbComp V₀)
    (simT₁ : Ch → V₀ → D₁) (simT₂ : Ch → V₀ → D₂) (c : Ch) : ProbComp (V₀ × W × V₁ × V₂) := do
  let v ← simRed c
  let r₁ ← $ᵗ R₁
  let r₂ ← $ᵗ R₂
  return (v, wir c, open₁ c (simT₁ c v) r₁, open₂ c (simT₂ c v) r₂)

/-- An opening **hides its table given its claims** at `c`: two tables with the same claims give
views with the same distribution, under a uniform padding. -/
def Hides {D R V C : Type} [SampleableType R] (op : Ch → D → R → V) (cl : Ch → D → C) (c : Ch) :
    Prop :=
  ∀ d d', cl c d = cl c d' → op c d <$> ($ᵗ R) =ᵈ op c d' <$> ($ᵗ R)

/-! ## The hybrid -/

/-- **Joint honest-verifier zero knowledge at one challenge.** If the reduction's messages are
simulated (`hred`), each opening hides its table given its claims (`hide₁`, `hide₂`), and the
simulator's tables have the honest tables' claims (`hT₁`, `hT₂`), then the whole honest view has
the simulator's distribution. -/
theorem view_evalDistEq [SampleableType Mk] [SampleableType R₁] [SampleableType R₂]
    (M : Model Ch Mk R₁ R₂ V₀ W D₁ D₂ V₁ V₂ C₁ C₂) (simRed : Ch → ProbComp V₀)
    (simT₁ : Ch → V₀ → D₁) (simT₂ : Ch → V₀ → D₂) (c : Ch)
    (hred : M.red c <$> ($ᵗ Mk) =ᵈ simRed c)
    (hide₁ : Hides M.open₁ M.cl₁ c) (hide₂ : Hides M.open₂ M.cl₂ c)
    (hT₁ : ∀ m, M.cl₁ c (simT₁ c (M.red c m)) = M.cl₁ c (M.tab₁ c m))
    (hT₂ : ∀ m, M.cl₂ c (simT₂ c (M.red c m)) = M.cl₂ c (M.tab₂ c m)) :
    M.view c <$> ($ᵗ (Mk × R₁ × R₂)) =ᵈ
      simulate M.wir M.open₁ M.open₂ simRed simT₁ simT₂ c := by
  -- the openings at messages `v` and tables `d₁`, `d₂`
  let G : V₀ → D₁ → D₂ → ProbComp (V₀ × W × V₁ × V₂) := fun v d₁ d₂ =>
    (M.open₁ c d₁ <$> ($ᵗ R₁)) >>= fun x₁ => (M.open₂ c d₂ <$> ($ᵗ R₂)) >>= fun x₂ =>
      pure (v, M.wir c, x₁, x₂)
  have hreal : M.view c <$> ($ᵗ (Mk × R₁ × R₂)) =
      ($ᵗ Mk) >>= fun m => G (M.red c m) (M.tab₁ c m) (M.tab₂ c m) := by
    rw [SampleableType.uniformSample_prod_eq_bind, SampleableType.uniformSample_prod_eq_bind]
    simp only [G, map_bind, map_pure, bind_assoc, pure_bind, bind_map_left, Model.view]
  have hsim : simulate M.wir M.open₁ M.open₂ simRed simT₁ simT₂ c =
      simRed c >>= fun v => G v (simT₁ c v) (simT₂ c v) := by
    simp only [simulate, G, bind_map_left]
  rw [hreal, hsim]
  calc (($ᵗ Mk) >>= fun m => G (M.red c m) (M.tab₁ c m) (M.tab₂ c m))
      =ᵈ (($ᵗ Mk) >>= fun m => G (M.red c m) (simT₁ c (M.red c m)) (simT₂ c (M.red c m))) :=
        EvalDistEq.bind_right _ fun m =>
          (hide₁ _ _ (hT₁ m).symm).bind fun _ => (hide₂ _ _ (hT₂ m).symm).bind fun _ =>
            EvalDistEq.rfl
    _ = ((M.red c <$> ($ᵗ Mk)) >>= fun v => G v (simT₁ c v) (simT₂ c v)) := by
        rw [bind_map_left]
    _ =ᵈ (simRed c >>= fun v => G v (simT₁ c v) (simT₂ c v)) := hred.bind_left _

/-! ## Bad challenges -/

/-- The union bound for a conjunction. -/
theorem prEvent_not_and_le {α : Type} (mx : ProbComp α) (p q : α → Prop) :
    Pr{let x ← mx}[¬ (p x ∧ q x)] ≤ Pr{let x ← mx}[¬ p x] + Pr{let x ← mx}[¬ q x] := by
  refine (prEvent_mono _ _ _ fun x h => ?_).trans (prEvent_or_le _ _ _)
  by_cases hp : p x
  · exact Or.inr fun hq => h ⟨hp, hq⟩
  · exact Or.inl hp

/-- The first coordinate of a uniform pair is uniform. -/
theorem prEvent_uniform_fst {A B : Type} [SampleableType A] [SampleableType B] (p : A → Prop) :
    Pr{let x ← $ᵗ (A × B)}[p x.1] = Pr{let a ← $ᵗ A}[p a] := by
  have h : (Prod.fst <$> ($ᵗ (A × B)) : ProbComp A) =ᵈ ($ᵗ A) := by
    rw [SampleableType.uniformSample_prod_eq_bind]
    simp only [map_bind, map_pure]
    calc (($ᵗ A) >>= fun a => ($ᵗ B) >>= fun _ => (pure a : ProbComp A))
        =ᵈ (($ᵗ A) >>= fun a => (pure a : ProbComp A)) :=
          EvalDistEq.bind_right _ fun a => EvalDistEq.bind_const _ _
      _ = $ᵗ A := bind_pure _
  rw [← h.prEvent_eq p, prEvent_map]

/-- The second coordinate of a uniform pair is uniform. -/
theorem prEvent_uniform_snd {A B : Type} [SampleableType A] [SampleableType B] (p : B → Prop) :
    Pr{let x ← $ᵗ (A × B)}[p x.2] = Pr{let b ← $ᵗ B}[p b] := by
  have h : (Prod.snd <$> ($ᵗ (A × B)) : ProbComp B) =ᵈ ($ᵗ B) := by
    rw [SampleableType.uniformSample_prod_eq_bind]
    simp only [map_bind, map_pure]
    calc (($ᵗ A) >>= fun _ => ($ᵗ B) >>= fun b => (pure b : ProbComp B))
        =ᵈ (($ᵗ B) >>= fun b => (pure b : ProbComp B)) := EvalDistEq.bind_const _ _
      _ = $ᵗ B := bind_pure _
  rw [← h.prEvent_eq p, prEvent_map]

end QuotientZk.Joint
