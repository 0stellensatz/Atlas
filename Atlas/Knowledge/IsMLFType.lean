import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.MStepSolvableQuotient

/-!
# group of MLF-type

A profinite group is of **MLF-type** if it is isomorphic, as a topological group, to the
absolute Galois group of some mixed-characteristic local field
`Atlas.Knowledge.IsMixedCharLocalField`; it is of **MLF^m-type** or **MLF^ab-type** if it is so
isomorphic to the maximal `m`-step solvable quotient `Atlas.Knowledge.MStepSolvableQuotient`,
respectively the abelianization, of such a Galois group. These are the unfiltered variants: the
source defines filtered companions in the same breath, whose filtration is the upper-numbering
ramification filtration and which therefore must wait for that vocabulary. Both anabelian main
theorems are statements about groups of these types, and the solvability degree
`Atlas.Knowledge.SolvabilityDegree` and the six invariants of
`Atlas.Knowledge.GroupResidueCharacteristic` and its companions are functions on them.

## Main definitions

* `IsMLFType` — topologically isomorphic to some `Field.absoluteGaloisGroup K`.
* `IsMLFmType` — topologically isomorphic to some `mStepSolvableQuotient` of one.
* `IsMLFabType` — the case `m = 1`, the source writing `G_K^ab` for `G_K^1`.

## Implementation notes

The source's "isomorphism of profinite groups" is a continuous group isomorphism, `≃ₜ*`; on
compact Hausdorff carriers the inverse is automatically continuous, so nothing is lost by
requiring it. The carrier `G` is asked to be only a topological group: profiniteness is not
hypothesized, since a group isomorphic to a `G_K` has it, and a group not so isomorphic is
merely not of MLF-type. The witness field ranges over a universe `u` of its own, so each
definition is universe-polymorphic in the witness; instantiating `u := 0` captures every
isomorphism class, the mixed-characteristic local fields being, up to isomorphism, the finite
extensions of the `ℚ_[p]`.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

universe u

variable (G : Type*) [Group G] [TopologicalSpace G]

/-- A topological group is of **MLF-type** if it is topologically isomorphic to the absolute
Galois group of some mixed-characteristic local field
([Hyeon 2025, Def. 2.2, p.8][Hyeon2025]). -/
def IsMLFType : Prop :=
  ∃ (K : Type u) (_ : Field K) (_ : ValuativeRel K) (_ : TopologicalSpace K)
    (_ : IsMixedCharLocalField K), Nonempty (G ≃ₜ* Field.absoluteGaloisGroup K)

/-- A topological group is of **MLF^m-type** if it is topologically isomorphic to the maximal
`m`-step solvable quotient of the absolute Galois group of some mixed-characteristic local
field ([Hyeon 2025, Def. 2.2, p.8][Hyeon2025]). -/
def IsMLFmType (m : ℕ) : Prop :=
  ∃ (K : Type u) (_ : Field K) (_ : ValuativeRel K) (_ : TopologicalSpace K)
    (_ : IsMixedCharLocalField K),
    Nonempty (G ≃ₜ* mStepSolvableQuotient (Field.absoluteGaloisGroup K) m)

/-- A topological group is of **MLF^ab-type** if it is topologically isomorphic to the
abelianized absolute Galois group of some mixed-characteristic local field—the case `m = 1` of
`Atlas.Knowledge.IsMLFmType`, the source writing `G_K^ab` for `G_K^1`
([Hyeon 2025, Def. 2.2, p.8][Hyeon2025]). -/
def IsMLFabType : Prop :=
  IsMLFmType.{u} G 1

end Atlas.Knowledge
