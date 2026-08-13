import Mathlib
import Atlas.Knowledge.ClosedDerivedSeries

/-!
# maximal m-step solvable quotient

The **maximal `m`-step solvable quotient** `G^m` of a topological group: the quotient of `G` by
the `m`-th term of its closed derived series `Atlas.Knowledge.ClosedDerivedSeries`. For `m = 1`
this is Mathlib's `TopologicalAbelianization`. For `G` an absolute Galois group it is the Galois
group of the maximal `m`-step solvable extension `Atlas.Knowledge.MStepSolvableExtension`, and it
is the group both main anabelian theorems take as input.

## Main definitions

* `mStepSolvableQuotient` — the quotient group `G ⧸ closedDerivedSeries G m`, with its quotient
  topology.

## Implementation notes

The quotient map is Mathlib's own, `QuotientGroup.mk' (closedDerivedSeries G m)`, so no bespoke
projection is defined here. Maximality—every continuous morphism to an `m`-step solvable group
factors through `G^m`—is the universal property of that quotient map and is deferred until
something needs it stated.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The **maximal `m`-step solvable quotient** of a topological group: the quotient by the `m`-th
term of the closed derived series ([Hyeon 2025, §2, p.8][Hyeon2025]). -/
def mStepSolvableQuotient (m : ℕ) : Type _ :=
  G ⧸ closedDerivedSeries G m

namespace mStepSolvableQuotient

variable (m : ℕ)

instance : Group (mStepSolvableQuotient G m) :=
  inferInstanceAs (Group (G ⧸ closedDerivedSeries G m))

instance : TopologicalSpace (mStepSolvableQuotient G m) :=
  inferInstanceAs (TopologicalSpace (G ⧸ closedDerivedSeries G m))

instance : IsTopologicalGroup (mStepSolvableQuotient G m) :=
  inferInstanceAs (IsTopologicalGroup (G ⧸ closedDerivedSeries G m))

end mStepSolvableQuotient

end Atlas.Knowledge
