import Mathlib
import Atlas.Knowledge.ClosedDerivedSeries

/-!
# m-step solvable representation

A representation of a topological group is **`m`-step solvable** if it annihilates the `m`-th
term of the closed derived series `Atlas.Knowledge.ClosedDerivedSeries`—equivalently, if it
factors through the maximal `m`-step solvable quotient
`Atlas.Knowledge.MStepSolvableQuotient`. A `1`-step solvable representation is **abelian**.
These are the representations the source's Hodge–Tate analysis can see from `G_K^{m+1}` alone,
which is what its Section 5 is for.

## Main definitions

* `IsMStepSolvableRep` — `ρ` kills `closedDerivedSeries G m`.
* `IsAbelianRep` — the case `m = 1`.

## Implementation notes

The factoring through `G^m` is deferred until something needs it stated; the annihilation form
is the one the source works with. The coefficients are any commutative semiring: the source's
`ℓ`-adic setting is `Atlas.Knowledge.IsLadicRepresentation`, and the two predicates compose
without either knowing the other.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

variable {k G V : Type*} [CommSemiring k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommMonoid V] [Module k V]

/-- A representation of a topological group is **`m`-step solvable** if it annihilates the
`m`-th term of the closed derived series ([Hyeon 2025, Def. 5.2, p.19][Hyeon2025]). -/
def IsMStepSolvableRep (ρ : Representation k G V) (m : ℕ) : Prop :=
  ∀ g ∈ closedDerivedSeries G m, ρ g = 1

/-- A representation is **abelian** if it is `1`-step solvable
([Hyeon 2025, Def. 5.2, p.19][Hyeon2025]). -/
def IsAbelianRep (ρ : Representation k G V) : Prop :=
  IsMStepSolvableRep ρ 1

end Atlas.Knowledge
