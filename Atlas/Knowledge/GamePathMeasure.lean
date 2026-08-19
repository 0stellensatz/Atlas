import Mathlib
import Atlas.Knowledge.GameTransition
import Atlas.Knowledge.ShiftDepth

/-!
# path measure of the shooting game

The source's probability space of shooting games: the measure `μ_{q,r}` on the paths of
states, built from the one-step kernel `Atlas.Knowledge.GameTransition` by Mathlib's
Ionescu–Tulcea machinery, started at the rabbit's initial position with its depth as the first
shot length. The history kernels forget everything but the last state, which is the Markov
property of the source's process; their Markov instances descend from the recorded claim
`Atlas.Knowledge.isMarkovKernel_gameKernel` and enter the definition as a hypothesis, the
consumer device of the layer.

## Main definitions

* `gameHistoryKernel` — the one-step kernel read off the last coordinate of a history.
* `gamePathMeasure` — the measure `μ_{q,r}` on state paths, through `Kernel.traj`.

## Main statements

* `gamePathMeasure_strictMono` — almost every trajectory advances strictly: the rabbit only
  moves forward. Claim recorded ahead of its proof.

## Implementation notes

`ProbabilityTheory.Kernel.traj` asks each history kernel to be Markov as an instance, and the
instance's truth is the recorded claim, so the path measure carries the instance as a
hypothesis rather than deriving it—a definition may not stand on a recorded claim, and a
consumer discharges the hypothesis with `haveI` from the claim under `1 < q`. Started at time
`0`, the initial history is the single state `(r, depth r)`, the source's `x₀ = (r, v_ρ (r))`.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The **history kernel** of the shooting game: the one-step kernel consulted at the last
coordinate of a history, which is the Markov property of the source's process
([Pagano 2022, §7, pp.454–455][Pagano2022]). -/
noncomputable def gameHistoryKernel (ρ : Shift) (q : ℕ+) (n : ℕ) :
    Kernel ((i : ↥(Finset.Iic n)) → GameState ρ) (GameState ρ) :=
  (gameKernel ρ q).comap (fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply _)

/-- The **path measure** `μ_{q,r}` of the shooting game: the Ionescu–Tulcea measure of the
history kernels, started at `(r, depth r)`—the source's `x₀ = (r, v_ρ (r))`
([Pagano 2022, §7, pp.454–455][Pagano2022]). -/
noncomputable def gamePathMeasure (ρ : Shift) (q : ℕ+) (r : ℕ+)
    [∀ n, IsMarkovKernel (gameHistoryKernel ρ q n)] :
    Measure ((n : ℕ) → GameState ρ) :=
  Kernel.traj (gameHistoryKernel ρ q) 0 (fun _ => ⟨(r, ρ.depth r), rfl⟩)

/-- Almost every trajectory advances strictly: the transition weights vanish off the forward
positions, so the strictly increasing paths carry the whole measure. Claim recorded ahead of
its proof ([Pagano 2022, §7, p.455][Pagano2022]). -/
theorem gamePathMeasure_strictMono (ρ : Shift) (q : ℕ+) (r : ℕ+) (hq : 1 < q)
    [∀ n, IsMarkovKernel (gameHistoryKernel ρ q n)] :
    gamePathMeasure ρ q r {ω | StrictMono fun n => ((ω n).val.1 : ℕ+)} = 1 := by
  sorry

end Atlas.Knowledge
