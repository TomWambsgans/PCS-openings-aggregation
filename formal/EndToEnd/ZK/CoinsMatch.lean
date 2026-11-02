-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import ZK.Real
import QuotientZk.Instance.Challenges

/-!
# The statement's prover's coins as uniform words

The statement's prover draws its coins (`sampleCoins`, `Security.lean`) as `12` words for the masks and
a word per position of each hidden table's padding, each word `UInt64.ofNat` of a uniform value below
`2^64`. **`sampleCoinsP_eq`**: they are `decodeCoins` of a uniform `CoinWords` (the three families of
words as functions of `Fin`), in distribution.

**`coinsMatch_of_bijective`**: so `CoinsMatch (decodeCoins ∘ e)` (`ZK/Real.lean`) for every bijection
`e` from the skeleton model's randomness to `CoinWords`: the statement's coins are the skeleton
model's uniform randomness read through `e`. For the deployed instance, `e` reads the masks and the two
paddings word by word, in the order the statement's prover lays them (`ProverBridge` fixes which `e`).
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters

namespace PcsQuotient.EndToEnd

set_option linter.unusedSectionVars false

/-- A uniform value below `2^64`, the model's coin for a word. -/
abbrev W64 := Fin (2 ^ 64 - 1 + 1)

/-- The word of a coin. -/
def wordOf (n : W64) : UInt64 := UInt64.ofNat n.val

/-- The statement's prover's word, as a `ProbComp`. -/
def coinWordP : ProbComp UInt64 := wordOf <$> $[0..2 ^ 64 - 1]

/-- `n` independent draws of `g`. -/
def repeatP {α : Type} (g : ProbComp α) : ℕ → ProbComp (List α)
  | 0 => pure []
  | n + 1 => do
    let u ← g
    let l ← repeatP g n
    return u :: l

/-! ## The coins as words -/

/-- The masks of twelve words. -/
def decodeMasks (w : List UInt64) : Masks := fun j i ↦ K.ofLane (w.getD (3 * j.val + i.val) 0)

/-- The padding of a table of layout `L` from its words. -/
def decodePadding (L : Layout) (w : List UInt64) : Padding :=
  let lane := 2 ^ L.logLane
  let words := w.toArray
  fun l i ↦ K.ofLane (words.getD (l * lane + i) 0)

/-- The number of padding words of a table of layout `L`. -/
def padWords (L : Layout) : ℕ := L.lanes.length * 2 ^ L.logLane

theorem simulateQ_mapM {α β : Type} (f : α → OracleComp RandomPermutationOracles β) :
    ∀ l : List α, simulateQ coinsImpl (l.mapM f) = l.mapM fun a ↦ simulateQ coinsImpl (f a)
  | [] => by simp
  | a :: l => by
    simp only [List.mapM_cons, simulateQ_bind, simulateQ_pure]
    exact bind_congr fun b ↦ by rw [simulateQ_mapM f l]

theorem mapM_const {α β : Type} (g : ProbComp β) :
    ∀ l : List α, (l.mapM fun _ ↦ g) = repeatP g l.length
  | [] => rfl
  | a :: l => by
    simp only [List.mapM_cons, List.length_cons, repeatP]
    exact bind_congr fun b ↦ by rw [mapM_const g l]

theorem simulateQ_coinWord : simulateQ coinsImpl coinWord = coinWordP := by
  unfold coinWord coinWordP wordOf
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, simulateQ_pure]
  rw [map_eq_bind_pure_comp]
  rfl

/-- **The coins, unfolded**: twelve words, then each layout's padding words. -/
theorem sampleCoins_words (L₁ L₂ : Layout) :
    simulateQ coinsImpl (do return (← sampleMasks, ← samplePadding L₁, ← samplePadding L₂)) =
      (do
        let w₁ ← repeatP coinWordP 12
        let w₂ ← repeatP coinWordP (padWords L₁)
        let w₃ ← repeatP coinWordP (padWords L₂)
        return (decodeMasks w₁, decodePadding L₁ w₂, decodePadding L₂ w₃)) := by
  unfold sampleMasks samplePadding
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_mapM, simulateQ_coinWord, mapM_const,
    List.length_range, bind_assoc, pure_bind]
  rfl

/-! ## Uniform words -/

theorem repeatP_map {α β : Type} (g : ProbComp α) (f : α → β) :
    ∀ n, repeatP (f <$> g) n = List.map f <$> repeatP g n
  | 0 => by simp [repeatP]
  | n + 1 => by
    simp only [repeatP, bind_map_left, map_bind, map_pure, List.map_cons]
    exact bind_congr fun u ↦ by rw [repeatP_map g f n, bind_map_left]

theorem repeatP_uniform (n : ℕ) :
    repeatP ($[0..2 ^ 64 - 1]) n = QuotientZk.uniformList W64 n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [repeatP, ih]; rfl

/-- **`n` coin words are uniform words**: `wordOf` of a uniform function of `Fin n`. -/
theorem repeatP_coinWord (n : ℕ) :
    repeatP coinWordP n =ᵈ (fun f : Fin n → W64 ↦ (List.ofFn f).map wordOf) <$> ($ᵗ (Fin n → W64)) := by
  rw [coinWordP, repeatP_map, repeatP_uniform]
  have h := (QuotientZk.Instance.uniformList_ofFn W64 n).map (List.map wordOf)
  rw [Functor.map_map] at h
  exact h

/-- The coins' words for layouts `L₁`, `L₂`: the masks', the first padding's, the second's. -/
abbrev CoinWordsL (L₁ L₂ : Layout) : Type :=
  (Fin 12 → W64) × (Fin (padWords L₁) → W64) × (Fin (padWords L₂) → W64)

/-- The coins of the words. -/
def decodeCoinsL (L₁ L₂ : Layout) (c : CoinWordsL L₁ L₂) : Masks × Padding × Padding :=
  (decodeMasks ((List.ofFn c.1).map wordOf), decodePadding L₁ ((List.ofFn c.2.1).map wordOf),
    decodePadding L₂ ((List.ofFn c.2.2).map wordOf))

/-- **The coins are `decodeCoinsL` of uniform words**, for any layouts. -/
theorem coins_eq (L₁ L₂ : Layout) :
    simulateQ coinsImpl (do return (← sampleMasks, ← samplePadding L₁, ← samplePadding L₂)) =ᵈ
      decodeCoinsL L₁ L₂ <$> ($ᵗ (CoinWordsL L₁ L₂)) := by
  rw [sampleCoins_words]
  have e : decodeCoinsL L₁ L₂ <$> ($ᵗ (CoinWordsL L₁ L₂)) =
      (($ᵗ (Fin 12 → W64)) >>= fun a ↦ ($ᵗ (Fin (padWords L₁) → W64)) >>= fun b ↦
        ($ᵗ (Fin (padWords L₂) → W64)) >>= fun c ↦ pure (decodeCoinsL L₁ L₂ (a, b, c))) := by
    rw [SampleableType.uniformSample_prod_eq_bind, SampleableType.uniformSample_prod_eq_bind]
    simp only [map_bind, map_pure, bind_assoc, pure_bind]
  rw [e]
  refine (EvalDistEq.bind_left (repeatP_coinWord 12) _).trans ?_
  rw [bind_map_left]
  refine EvalDistEq.bind_right _ fun a ↦ ?_
  refine (EvalDistEq.bind_left (repeatP_coinWord _) _).trans ?_
  rw [bind_map_left]
  refine EvalDistEq.bind_right _ fun b ↦ ?_
  refine (EvalDistEq.bind_left (repeatP_coinWord _) _).trans ?_
  rw [bind_map_left]
  exact EvalDistEq.rfl

/-- The coins' words of the deployed layouts. -/
abbrev CoinWords : Type := CoinWordsL (witnessLayout logRows) (quotientLayout logRows)

/-- **The coins of the words**, at the deployed layouts. -/
def decodeCoins : CoinWords → Masks × Padding × Padding :=
  decodeCoinsL (witnessLayout logRows) (quotientLayout logRows)

/-- **The statement's coins are `decodeCoins` of uniform words.** -/
theorem sampleCoinsP_eq : sampleCoinsP =ᵈ decodeCoins <$> ($ᵗ CoinWords) :=
  coins_eq (witnessLayout logRows) (quotientLayout logRows)

/-- **`CoinsMatch` for every bijection onto the words**: the statement's coins are the skeleton model's
uniform randomness read through a bijection `e` onto `CoinWords`, then decoded. -/
theorem coinsMatch_of_bijective {S : Type} [SampleableType S] (e : S → CoinWords)
    (he : Function.Bijective e) : CoinsMatch (decodeCoins ∘ e) := by
  unfold CoinsMatch
  have h2 := (SampleableType.map_uniformSample_evalDistEq_of_bijective he).map decodeCoins
  rw [Functor.map_map] at h2
  exact sampleCoinsP_eq.trans h2.symm

end PcsQuotient.EndToEnd
