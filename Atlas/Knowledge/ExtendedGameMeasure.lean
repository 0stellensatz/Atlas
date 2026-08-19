import Mathlib
import Atlas.Knowledge.ExtendedGameJumpPair
import Atlas.Knowledge.ExtendedGameTransition
import Atlas.Knowledge.IsAdmissibleJumpPair
import Atlas.Knowledge.ShiftDepth
import Atlas.Knowledge.ShiftEPrime

/-!
# measure of the extended shooting game

The source's probability space of extended shooting games and the measure it induces on
extended jump sets: the path measure `μ^*_{q,r}` from the extended kernel
`Atlas.Knowledge.ExtendedGameTransition` by Ionescu–Tulcea, and the mass the pushforward
along `Atlas.Knowledge.ExtendedGameJumpPair` gives each extended jump pair—the measure the
mass formula of the source's §9 computes and its §8 equates with the Haar mass of
`Atlas.Knowledge.HaarGameMass`. At the start `e'_ρ` the pairs of positive mass are exactly
the admissible ones, which is the source's observation tying the game to
`Atlas.Knowledge.IsAdmissibleJumpPair`.

## Main definitions

* `extendedGameHistoryKernel` — the extended kernel read off the last coordinate.
* `extendedGamePathMeasure` — the measure `μ^*_{q,r}` on extended state paths.
* `extendedGameMass` — the mass of an extended jump pair under the pushforward.

## Main statements

* `extendedGameMass_pos_iff` — at the start `e'_ρ`, the pairs of positive mass are exactly
  the admissible ones. Claim recorded ahead of its proof.

## Implementation notes

As in `Atlas.Knowledge.GamePathMeasure`, the Markov instances the trajectory construction
asks for descend from the recorded claim
`Atlas.Knowledge.isMarkovKernel_extendedGameKernel` and enter as hypotheses. The initial
state is `(r, depth r)`, of the first kind—the source starts its extended games below
`e_ρ^*`, before the extra shooter's positions. The mass is the path measure of the
pair's fiber, an outer application that needs no measurability, though over the discrete
σ-algebra on states the fiber is in fact measurable; stating masses pointwise on graphs is
what the consuming claims evaluate anyway, the source equipping `Jump^*_ρ` with the discrete
σ-algebra.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The **history kernel** of the extended shooting game
([Pagano 2022, §7, pp.455–457][Pagano2022]). -/
noncomputable def extendedGameHistoryKernel (ρ : Shift) (hρ : (Shift.T ρ).Finite)
    (p q : ℕ+) (n : ℕ) :
    Kernel ((i : ↥(Finset.Iic n)) → ExtendedGameState ρ hρ) (ExtendedGameState ρ hρ) :=
  (extendedGameKernel ρ hρ p q).comap (fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply _)

/-- The **path measure** `μ^*_{q,r}` of the extended shooting game, started at
`(r, depth r)` ([Pagano 2022, §7, p.457][Pagano2022]). -/
noncomputable def extendedGamePathMeasure (ρ : Shift) (hρ : (Shift.T ρ).Finite)
    (p q : ℕ+) (r : ℕ+)
    [∀ n, IsMarkovKernel (extendedGameHistoryKernel ρ hρ p q n)] :
    Measure ((n : ℕ) → ExtendedGameState ρ hρ) :=
  Kernel.traj (extendedGameHistoryKernel ρ hρ p q) 0
    (fun _ => ⟨(r, ρ.depth r), Or.inl rfl⟩)

/-- The **mass of an extended jump pair** under the extended game: the path measure of its
fiber along the pair map—the pushforward measure on `Jump^*_ρ`, evaluated on graphs
([Pagano 2022, §7, p.457][Pagano2022]). -/
noncomputable def extendedGameMass (ρ : Shift) (hρ : (Shift.T ρ).Finite) (p q : ℕ+) (r : ℕ+)
    [∀ n, IsMarkovKernel (extendedGameHistoryKernel ρ hρ p q n)]
    (P : Finset (ℕ+ × ℕ+)) : ℝ≥0∞ :=
  extendedGamePathMeasure ρ hρ p q r
    {ω | extendedGameJumpPair ρ hρ (fun t => (ω t).val) = ↑P}

/-- At the start `e'_ρ` the pairs of positive mass are exactly the admissible ones: the
source's observation tying the extended game to admissibility. Claim recorded ahead of its
proof ([Pagano 2022, §7, p.457][Pagano2022]). -/
theorem extendedGameMass_pos_iff (ρ : Shift) (hρ : (Shift.T ρ).Finite) (p q : ℕ+)
    (hp : 1 < p) (hq : 1 < q)
    [∀ n, IsMarkovKernel (extendedGameHistoryKernel ρ hρ p q n)]
    {P : Finset (ℕ+ × ℕ+)} (hP : IsJumpPair ρ (Shift.T_star ρ hρ) P) :
    0 < extendedGameMass ρ hρ p q (Shift.e' hρ) P ↔ IsAdmissibleJumpPair ρ hρ P := by
  sorry

end Atlas.Knowledge
