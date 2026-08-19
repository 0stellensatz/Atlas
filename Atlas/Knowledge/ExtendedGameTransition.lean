import Mathlib
import Atlas.Knowledge.IsGameState
import Atlas.Knowledge.ShiftDepth
import Atlas.Knowledge.ShiftEStar

/-!
# transition kernel of the extended shooting game

The Markov structure of the source's extended shooting game, where an extra shooter fires
from `e_ρ^*`: the state carrier over `Atlas.Knowledge.IsGameState`'s extended variant, the
count of `e_ρ^*`-iterates crossed by a step, the per-kind transition weights of the source's
`P^*`, and the one-step kernel. The two kinds being exclusive—the proved
`Atlas.Knowledge.extendedGameState_kinds_exclusive`—the per-kind formula is selected by the
first-kind test alone. The Markov property is the recorded claim, and the path measure over
it is `Atlas.Knowledge.ExtendedGameMeasure`.

## Main definitions

* `ExtendedGameState` — the extended state carrier, with the discrete measurable structure.
* `extendedShotCount` — the source's `v_ρ (e_ρ^*, k₁, k₂)`: how many iterates of `e_ρ^*` a
  step crosses.
* `extendedGameTransition` — the per-kind weights of `P^*`.
* `extendedGameKernel` — the one-step kernel.

## Main statements

* `isMarkovKernel_extendedGameKernel` — the kernel is Markov at `1 < p` and `1 < q`. Claim
  recorded ahead of its proof.

## Implementation notes

The iterate count is a `Finset.card` over exponents up to the far endpoint, which suffices
because iterates grow at least linearly. The weight's second branch fires exactly on the
second kind for genuine states, the kinds being exclusive; on junk pairs that are states of
neither kind the branch value is junk the kernel never reads, its sum ranging over the state
carrier. The source explains the row mass one through a walker with two coins, the second
spent at each crossing of an `e_ρ^*`-iterate; the claim records exactly that mass statement,
and needs no relation between `p` and `q` beyond both exceeding one, the source's case being
`q = p^f`.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The **state carrier** of the extended shooting game
([Pagano 2022, §7, p.455][Pagano2022]). -/
def ExtendedGameState (ρ : Shift) (hρ : (Shift.T ρ).Finite) : Type :=
  {x : ℕ+ × ℕ // IsExtendedGameState ρ hρ x}

instance (ρ : Shift) (hρ : (Shift.T ρ).Finite) : Countable (ExtendedGameState ρ hρ) := by
  unfold ExtendedGameState
  infer_instance

instance (ρ : Shift) (hρ : (Shift.T ρ).Finite) : MeasurableSpace (ExtendedGameState ρ hρ) := ⊤

open Classical in
/-- The source's `v_ρ (e_ρ^*, k₁, k₂)`: the number of iterates of `e_ρ^*` lying in
`(k₁, k₂]`—how many chances the extra shooter gets along a step
([Pagano 2022, §7, p.455][Pagano2022]). -/
noncomputable def extendedShotCount (ρ : Shift) (hρ : (Shift.T ρ).Finite) (k₁ k₂ : ℕ+) : ℕ :=
  ((Finset.range ((k₂ : ℕ) + 1)).filter fun m =>
    k₁ < (⇑ρ)^[m] (Shift.e_star ρ hρ) ∧ (⇑ρ)^[m] (Shift.e_star ρ hρ) ≤ k₂).card

/-- The **transition weight** of the extended game, the source's `P^*`: toward a strictly
forward position, `(q - 1) / (q^{y₁ - x₁} p^{v_ρ (e_ρ^*, x₁, y₁)})` onto the first kind and
`(p - 1) / (q^{y₁ - x₁ - 1} p^{v_ρ (e_ρ^*, x₁, y₁)})` onto the second
([Pagano 2022, §7, p.456][Pagano2022]). -/
noncomputable def extendedGameTransition (ρ : Shift) (hρ : (Shift.T ρ).Finite) (p q : ℕ+)
    (x y : ℕ+ × ℕ) : ℝ≥0∞ :=
  if x.1 < y.1 then
    (if ρ.depth y.1 = y.2 then
      ((q : ℝ≥0∞) - 1) / ((q : ℝ≥0∞) ^ ((y.1 : ℕ) - (x.1 : ℕ)) *
        (p : ℝ≥0∞) ^ extendedShotCount ρ hρ x.1 y.1)
    else
      ((p : ℝ≥0∞) - 1) / ((q : ℝ≥0∞) ^ ((y.1 : ℕ) - (x.1 : ℕ) - 1) *
        (p : ℝ≥0∞) ^ extendedShotCount ρ hρ x.1 y.1))
  else 0

/-- The **one-step kernel** of the extended shooting game
([Pagano 2022, §7, p.456][Pagano2022]). -/
noncomputable def extendedGameKernel (ρ : Shift) (hρ : (Shift.T ρ).Finite) (p q : ℕ+) :
    Kernel (ExtendedGameState ρ hρ) (ExtendedGameState ρ hρ) where
  toFun := fun x => Measure.sum fun y : ExtendedGameState ρ hρ =>
    extendedGameTransition ρ hρ p q x.val y.val • Measure.dirac y
  measurable' := measurable_from_top

/-- The extended kernel is Markov at `1 < p` and `1 < q`: the source's walker spends its
second coin at each crossing of an `e_ρ^*`-iterate, and the row mass telescopes to one. Claim
recorded ahead of its proof ([Pagano 2022, §7, p.456][Pagano2022]). -/
theorem isMarkovKernel_extendedGameKernel (ρ : Shift) (hρ : (Shift.T ρ).Finite) (p q : ℕ+)
    (hp : 1 < p) (hq : 1 < q) :
    IsMarkovKernel (extendedGameKernel ρ hρ p q) := by
  sorry

end Atlas.Knowledge
