import Mathlib
import Atlas.Knowledge.FiniteCyclicSubextension
import Atlas.Knowledge.RelativeNormLaws

/-!
# finite unramified cyclic extension

A finite cyclic extension of a field finite over the base, bundled with the
assertion that it is unramified for a fixed degree datum: the coefficient
package of the unit-cohomology axiom. The one instance registered here is
the absolute finiteness of the upper field, through the tower; normality,
relative finiteness, and the canonical `Fintype` already reach the bundle
through the parent projection (#104).

## Main definitions

* `FiniteUnramifiedCyclicExtension` — a finite cyclic subextension carrying
  its unramifiedness.
* `FiniteUnramifiedCyclicExtension.toFiniteAbstractFieldExtension` — both
  finite endpoint bundles, forgetting the cyclic and unramified structure.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling and the
source's `@[implicit_reducible]` marker is dropped, as in
`Atlas.Knowledge.FiniteCyclicSubextension`; the source's normality,
relative-finiteness, and `Fintype` instances are not restated — instance
resolution reaches the parent's through the projection.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {D : DegreeData G}

/-- **A finite cyclic extension bundled with its unramifiedness for a fixed
degree datum** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean:103`]
[Yamaguchi2026]). -/
structure FiniteUnramifiedCyclicExtension
    (D : DegreeData G) (K : FiniteAbstractField G)
    extends FiniteCyclicSubextension K where
  /-- The underlying finite cyclic extension is unramified for `D`. -/
  unramified : toFiniteCyclicSubextension.IsUnramified D

namespace FiniteUnramifiedCyclicExtension

variable {K : FiniteAbstractField G}

/-- Forget cyclic and unramified structure while retaining both finite
endpoint fields and the relative finite quotient ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean:116`]
[Yamaguchi2026]). -/
noncomputable def toFiniteAbstractFieldExtension
    (E : FiniteUnramifiedCyclicExtension D K) :
    FiniteAbstractFieldExtension G :=
  E.toFiniteCyclicSubextension.toFiniteAbstractFieldExtension

/-- The unramified proof, transported to the canonical finite
field-extension bundle ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean:123`]
[Yamaguchi2026]). -/
theorem toFiniteAbstractFieldExtension_isUnramified
    (E : FiniteUnramifiedCyclicExtension D K) :
    E.toFiniteAbstractFieldExtension.IsUnramified D := by
  exact E.unramified

/-- The absolute quotient attached to a finite unramified cyclic extension
is finite ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean:139`]
[Yamaguchi2026]). -/
noncomputable instance (E : FiniteUnramifiedCyclicExtension D K) :
    Finite ((baseField G).toSubgroup ⧸
      E.field.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
  relativeTowerQuotientFinite (baseField G) K.field E.field E.below
    (le_baseField K.field)

end FiniteUnramifiedCyclicExtension

end

end Atlas.Knowledge
