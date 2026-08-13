import Mathlib
import Atlas.Knowledge.ClosedDerivedSeries

/-!
# m-step solvable group

A topological group is **`m`-step solvable** if the `m`-th term of its closed derived series
`Atlas.Knowledge.ClosedDerivedSeries` is trivial. For `m = 1` this is being abelian; taking the
closure at each step makes the condition the right one for profinite groups, where the maximal
`m`-step solvable quotient `Atlas.Knowledge.MStepSolvableQuotient` corresponds to the maximal
`m`-step solvable subextension `Atlas.Knowledge.MStepSolvableExtension` under the Galois
correspondence.

## Main definitions

* `IsMStepSolvable` — the `m`-th closed derived subgroup is trivial.

## Main statements

* `IsMStepSolvable.mono` — an `m`-step solvable group is `n`-step solvable for every `n ≥ m`,
  granted a Hausdorff hypothesis making `⊥` closed.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A topological group is **`m`-step solvable** if the `m`-th term of its closed derived series
is trivial ([Hyeon 2025, §2, p.8][Hyeon2025]). -/
def IsMStepSolvable (m : ℕ) : Prop :=
  closedDerivedSeries G m = ⊥

variable {G}

/-- An `m`-step solvable group is `n`-step solvable for every `n ≥ m`. Hausdorffness stands in
for profiniteness: it is what makes `⊥` closed, so that the series stays at `⊥` once it arrives
([Hyeon 2025, §2, p.8][Hyeon2025]). -/
theorem IsMStepSolvable.mono [T2Space G] {m n : ℕ} (h : IsMStepSolvable G m) (hmn : m ≤ n) :
    IsMStepSolvable G n := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ n hmn ih =>
    rw [IsMStepSolvable, closedDerivedSeries_succ, ih, Subgroup.commutator_bot_left]
    refine le_antisymm
      (Subgroup.topologicalClosure_minimal _ le_rfl ?_) (Subgroup.le_topologicalClosure _)
    simp

end Atlas.Knowledge
