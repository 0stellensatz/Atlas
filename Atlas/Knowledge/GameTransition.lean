import Mathlib
import Atlas.Knowledge.IsGameState

/-!
# transition kernel of the shooting game

The Markov structure of the source's shooting game: the state carrier over
`Atlas.Knowledge.IsGameState`, the transition weight `(q - 1) / q^{y₁ - x₁}` toward every
strictly forward position, and the one-step kernel summing weighted Dirac masses. That the
kernel is Markov—each row a probability measure, the geometric series summing to one—is the
recorded claim; the path measure standing on it is `Atlas.Knowledge.GamePathMeasure`.

## Main definitions

* `GameState` — the state carrier: pairs consistent in the sense of
  `Atlas.Knowledge.IsGameState`, with the discrete measurable structure.
* `gameTransition` — the weight `(q - 1) / q^{y₁ - x₁}` toward strictly forward positions.
* `gameKernel` — the one-step kernel.

## Main statements

* `isMarkovKernel_gameKernel` — the kernel is Markov at `1 < q`. Claim recorded ahead of its
  proof.

## Implementation notes

The state space is countable and carries the top measurable structure, so the kernel's
measurability is free and every set the measures below meet is measurable. The weight is
stated on raw pairs and consulted by the kernel only on states, one per forward position, so
the row mass is `Σ_{k ≥ 1} (q - 1) / q^k`—the claim's content, true exactly at `1 < q`; at
`q = 1` every weight vanishes and the kernel is the zero kernel, which the claim's hypothesis
excludes as the source's `q = p^f` does.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The **state carrier** of the shooting game: pairs of a position and a shot length,
consistent in the sense of `Atlas.Knowledge.IsGameState`
([Pagano 2022, §7, p.455][Pagano2022]). -/
def GameState (ρ : Shift) : Type := {x : ℕ+ × ℕ // IsGameState ρ x}

instance (ρ : Shift) : Countable (GameState ρ) := by
  unfold GameState
  infer_instance

instance (ρ : Shift) : MeasurableSpace (GameState ρ) := ⊤

/-- The **transition weight** of the shooting game: `(q - 1) / q^{y₁ - x₁}` toward every
strictly forward position, `0` otherwise ([Pagano 2022, §7, p.455][Pagano2022]). -/
noncomputable def gameTransition (q : ℕ+) (x y : ℕ+ × ℕ) : ℝ≥0∞ :=
  if x.1 < y.1 then ((q : ℝ≥0∞) - 1) / (q : ℝ≥0∞) ^ ((y.1 : ℕ) - (x.1 : ℕ)) else 0

/-- The **one-step kernel** of the shooting game: from each state, the weighted sum of Dirac
masses over all states ([Pagano 2022, §7, p.455][Pagano2022]). -/
noncomputable def gameKernel (ρ : Shift) (q : ℕ+) : Kernel (GameState ρ) (GameState ρ) where
  toFun := fun x => Measure.sum fun y : GameState ρ =>
    gameTransition q x.val y.val • Measure.dirac y
  measurable' := measurable_from_top

/-- The kernel is Markov at `1 < q`: over each state the weights sum to one, the geometric
series `Σ_{k ≥ 1} (q - 1) / q^k`, there being exactly one state per forward position. Claim
recorded ahead of its proof ([Pagano 2022, §7, p.455][Pagano2022]). -/
theorem isMarkovKernel_gameKernel (ρ : Shift) (q : ℕ+) (hq : 1 < q) :
    IsMarkovKernel (gameKernel ρ q) := by
  sorry

end Atlas.Knowledge
