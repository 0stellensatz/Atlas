import Mathlib

/-!
# prosolvable group

A topological group is **prosolvable** if each of its finite discrete quotients is solvable:
every open normal subgroup has solvable quotient. For a profinite group this says the group is
an inverse limit of finite solvable groups. The absolute Galois group of a
mixed-characteristic local field is prosolvable, which is the source of the vanishing
`⨅ m, closedDerivedSeries G m = ⊥` recorded in
`Atlas.Knowledge.AbsoluteGaloisProsolvability`.

## Main definitions

* `IsProsolvable` — every open normal subgroup has solvable quotient.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

/-- A topological group is **prosolvable** if the quotient by every open normal subgroup is
solvable ([Hyeon 2025, Rem. 2.4 (1), p.9][Hyeon2025]). -/
def IsProsolvable (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ N : OpenNormalSubgroup G, IsSolvable (G ⧸ N.toSubgroup)

end Atlas.Knowledge
