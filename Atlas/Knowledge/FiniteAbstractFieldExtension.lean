import Mathlib
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteResidueAbstractExtension

/-!
# finite extension of abstract fields over the base

A finite extension between two fields that are themselves finite over the
distinguished base, with both endpoint certificates and the relative quotient
carried by the object. The canonical constructor derives finiteness of the
upper endpoint from the tower — the cardinal tower identity is the source of
truth — and both endpoints enrich to their residue data.

## Main definitions

* `FiniteAbstractFieldExtension` — the extension object, with
  `FiniteAbstractFieldExtension.ofInclusion` deriving the upper endpoint's
  finiteness from the tower.
* `FiniteAbstractFieldExtension.degree` /
  `FiniteAbstractFieldExtension.residueDegree` /
  `FiniteAbstractFieldExtension.ramificationIndex` — the positive invariants.
* `FiniteAbstractFieldExtension.toFiniteResidueAbstractExtension` — both
  endpoints enriched with their residue data.

## Main statements

* `FiniteAbstractFieldExtension.residueDegree_eq_degree_of_isUnramified` — the
  unramified degeneracy; proved.

## Implementation notes

The source marks `ofInclusion`, `toFiniteAbstractExtension`, and `IsUnramified`
`@[implicit_reducible]` — Lean core's instances-transparency attribute; dropped
here, restorable at the first consumer that unfolds through them.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **A finite extension of fields finite over the base**: both endpoint
finiteness proofs and the relative quotient belong to the object
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:1196`][Yamaguchi2026]). -/
structure FiniteAbstractFieldExtension (G : Type u)
    [Group G] [TopologicalSpace G] where
  /-- The top endpoint, finite over the distinguished base. -/
  field : FiniteAbstractField G
  /-- The base endpoint, finite over the distinguished base. -/
  base : FiniteAbstractField G
  /-- The top-field subgroup is contained in the base-field subgroup. -/
  below : field.field.toSubgroup ≤ base.field.toSubgroup
  /-- The relative extension quotient is finite. -/
  finiteQuotient :
    Finite
      (base.field.toSubgroup ⧸
        field.field.toSubgroup.subgroupOf base.field.toSubgroup)

namespace FiniteAbstractFieldExtension

/-- **Bundle a finite relative extension of a field finite over the base**:
finiteness of the upper field follows from the quotient tower
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:1216`][Yamaguchi2026]). -/
noncomputable def ofInclusion (field : ClosedSubgroup G)
    (base : FiniteAbstractField G)
    (below : field.toSubgroup ≤ base.field.toSubgroup)
    [finiteQuotient : Finite
      (base.field.toSubgroup ⧸
        field.toSubgroup.subgroupOf base.field.toSubgroup)] :
    FiniteAbstractFieldExtension G where
  field := {
    field := field
    finite := by
      apply Cardinal.lt_aleph0_iff_finite.mp
      let T : AbstractExtension.Tower G := {
        top := field
        middle := base.field
        base := baseField G
        top_le_middle := below
        middle_le_base := le_baseField base.field }
      change T.totalExtension.degreeCardinal < Cardinal.aleph0
      rw [← T.degreeCardinal_mul]
      apply Cardinal.mul_lt_aleph0
      · change Cardinal.mk
          (base.field.toSubgroup ⧸
            field.toSubgroup.subgroupOf base.field.toSubgroup) < Cardinal.aleph0
        exact Cardinal.lt_aleph0_of_finite _
      · change Cardinal.mk
          ((baseField G).toSubgroup ⧸
            base.field.toSubgroup.subgroupOf (baseField G).toSubgroup) <
          Cardinal.aleph0
        exact Cardinal.lt_aleph0_of_finite _ }
  base := base
  below := below
  finiteQuotient := finiteQuotient

/-- Forget endpoint finiteness over the base. -/
def toFiniteAbstractExtension (E : FiniteAbstractFieldExtension G) :
    FiniteAbstractExtension G where
  field := E.field.field
  base := E.base.field
  below := E.below
  finiteQuotient := E.finiteQuotient

/-- Structural unramifiedness of the relative extension. -/
def IsUnramified (E : FiniteAbstractFieldExtension G) (D : DegreeData G) :
    Prop :=
  E.toFiniteAbstractExtension.IsUnramified D

/-- Structural total ramification of the relative extension. -/
def IsTotallyRamified (E : FiniteAbstractFieldExtension G)
    (D : DegreeData G) : Prop :=
  E.toFiniteAbstractExtension.IsTotallyRamified D

/-- The positive relative degree. -/
noncomputable def degree (E : FiniteAbstractFieldExtension G) : ℕ+ :=
  E.toFiniteAbstractExtension.degree

/-- The positive relative residue degree. -/
noncomputable def residueDegree (E : FiniteAbstractFieldExtension G)
    (D : DegreeData G) : ℕ+ :=
  E.toFiniteAbstractExtension.residueDegree D

/-- The positive relative ramification index. -/
noncomputable def ramificationIndex (E : FiniteAbstractFieldExtension G)
    (D : DegreeData G) : ℕ+ :=
  E.toFiniteAbstractExtension.ramificationIndex D

/-- In an unramified extension the residue degree is the degree. -/
theorem residueDegree_eq_degree_of_isUnramified
    (E : FiniteAbstractFieldExtension G) (D : DegreeData G)
    (hE : E.IsUnramified D) :
    (E.residueDegree D : ℕ) = (E.degree : ℕ) :=
  E.toFiniteAbstractExtension.residueDegree_eq_degree_of_isUnramified D hE

/-- The extension supplies finiteness of its relative quotient. -/
instance (E : FiniteAbstractFieldExtension G) :
    Finite
      (E.base.field.toSubgroup ⧸
        E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup) :=
  E.finiteQuotient

/-- Enrich both endpoints with their residue data. -/
noncomputable def toFiniteResidueAbstractExtension
    (E : FiniteAbstractFieldExtension G) (D : DegreeData G) :
    FiniteResidueAbstractExtension D where
  field := E.field.toFiniteResidueAbstractField D
  base := E.base.toFiniteResidueAbstractField D
  below := E.below
  finiteQuotient := E.finiteQuotient

end FiniteAbstractFieldExtension

end Atlas.Knowledge
