import Mathlib
import Atlas.Knowledge.FiniteAbstractExtension
import Atlas.Knowledge.FiniteResidueAbstractField

/-!
# finite extension with residue data

A finite abstract extension whose endpoints both carry their finite absolute
residue quotients, together with the two boundary constructors that *derive*
the upper endpoint's residue finiteness — from the cardinal Frobenius
compatibility when only the relative residue quotient is finite, and from the
finite relative quotient when the whole extension is finite. The cardinal
identities are the source of truth; no natural-valued index enters.

## Main definitions

* `FiniteResidueAbstractField.ofRelativeInclusion` — ascend residue finiteness
  along a finite relative residue quotient.
* `FiniteResidueAbstractExtension` — the extension with residue-finite
  endpoints, `FiniteResidueAbstractExtension.ofInclusion` to build one, and the
  three positive invariants inherited through
  `FiniteResidueAbstractExtension.toFiniteAbstractExtension`.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] {D : DegreeData G}

namespace FiniteResidueAbstractField

/-- **Residue finiteness ascends along a finite relative residue quotient**:
if the base has finite absolute residue quotient and the relative residue
quotient is finite, so is the upper absolute residue quotient — by the cardinal
Frobenius compatibility
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:951`][Yamaguchi2026]). -/
noncomputable def ofRelativeInclusion (D : DegreeData G)
    (field : ClosedSubgroup G) (base : FiniteResidueAbstractField D)
    (below : field.toSubgroup ≤ base.field.toSubgroup)
    [finiteRelativeResidueQuotient : Finite
      (↥(base.field.toSubgroup.map D.degree.toMonoidHom) ⧸
        (field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
          (base.field.toSubgroup.map D.degree.toMonoidHom))] :
    FiniteResidueAbstractField D where
  field := field
  finiteResidueQuotient := by
    apply Cardinal.lt_aleph0_iff_finite.mp
    rw [← D.residueDegreeCardinal_eq_mk_residueQuotient]
    let E : AbstractExtension G := {
      field := field
      base := base.field
      below := below
    }
    rw [← E.relativeResidueDegreeCardinal_mul_residueDegreeCardinal D]
    apply Cardinal.mul_lt_aleph0_iff.mpr
    exact Or.inr (Or.inr ⟨by
      change Cardinal.mk
          (↥(base.field.toSubgroup.map D.degree.toMonoidHom) ⧸
            (field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
              (base.field.toSubgroup.map D.degree.toMonoidHom)) <
        Cardinal.aleph0
      exact Cardinal.lt_aleph0_of_finite _, by
      rw [D.residueDegreeCardinal_eq_mk_residueQuotient]
      exact Cardinal.lt_aleph0_of_finite _⟩)

end FiniteResidueAbstractField

/-- **A finite extension with residue-finite endpoints**: both endpoints carry
their finite absolute residue quotients, and the relative quotient is finite
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:985`][Yamaguchi2026]). -/
structure FiniteResidueAbstractExtension (D : DegreeData G) where
  /-- The top endpoint with its finite residue quotient. -/
  field : FiniteResidueAbstractField D
  /-- The base endpoint with its finite residue quotient. -/
  base : FiniteResidueAbstractField D
  /-- The top-field subgroup is contained in the base-field subgroup. -/
  below : field.field.toSubgroup ≤ base.field.toSubgroup
  /-- The relative extension quotient is finite. -/
  finiteQuotient :
    Finite
      (base.field.toSubgroup ⧸
        field.field.toSubgroup.subgroupOf base.field.toSubgroup)

namespace FiniteResidueAbstractExtension

/-- **Enrich a finite extension of a residue-finite base**: finiteness of the
upper absolute residue quotient is deduced from the cardinal tower identity
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:1006`][Yamaguchi2026]). -/
noncomputable def ofInclusion (D : DegreeData G)
    (field : ClosedSubgroup G) (base : FiniteResidueAbstractField D)
    (below : field.toSubgroup ≤ base.field.toSubgroup)
    [finiteQuotient : Finite
      (base.field.toSubgroup ⧸
        field.toSubgroup.subgroupOf base.field.toSubgroup)] :
    FiniteResidueAbstractExtension D where
  field := {
    field := field
    finiteResidueQuotient := by
      apply Cardinal.lt_aleph0_iff_finite.mp
      rw [← D.residueDegreeCardinal_eq_mk_residueQuotient]
      let E : FiniteAbstractExtension G := {
        field := field
        base := base.field
        below := below
        finiteQuotient := finiteQuotient
      }
      rw [← E.toAbstractExtension.relativeResidueDegreeCardinal_mul_residueDegreeCardinal
        D]
      apply Cardinal.mul_lt_aleph0_iff.mpr
      exact Or.inr (Or.inr ⟨E.relativeResidueDegreeCardinal_lt_aleph0 D, by
        rw [D.residueDegreeCardinal_eq_mk_residueQuotient]
        exact Cardinal.lt_aleph0_of_finite (D.residueQuotient base.field)⟩) }
  base := base
  below := below
  finiteQuotient := finiteQuotient

/-- Forget the endpoint residue-finiteness data. -/
def toFiniteAbstractExtension (E : FiniteResidueAbstractExtension D) :
    FiniteAbstractExtension G where
  field := E.field.field
  base := E.base.field
  below := E.below
  finiteQuotient := E.finiteQuotient

/-- A residue-finite extension supplies finiteness of its relative quotient. -/
instance (E : FiniteResidueAbstractExtension D) :
    Finite
      (E.base.field.toSubgroup ⧸
        E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup) :=
  E.finiteQuotient

/-- The positive relative degree. -/
noncomputable def degree (E : FiniteResidueAbstractExtension D) : ℕ+ :=
  E.toFiniteAbstractExtension.degree

/-- The positive relative residue degree. -/
noncomputable def residueDegree (E : FiniteResidueAbstractExtension D) : ℕ+ :=
  E.toFiniteAbstractExtension.residueDegree D

/-- The positive relative ramification index. -/
noncomputable def ramificationIndex
    (E : FiniteResidueAbstractExtension D) : ℕ+ :=
  E.toFiniteAbstractExtension.ramificationIndex D

/-- The enriched degree agrees with the underlying finite-extension degree. -/
@[simp] theorem degree_coe (E : FiniteResidueAbstractExtension D) :
    (E.degree : ℕ) = (E.toFiniteAbstractExtension.degree : ℕ) :=
  rfl

/-- The enriched residue degree agrees with the underlying invariant. -/
@[simp] theorem residueDegree_coe (E : FiniteResidueAbstractExtension D) :
    (E.residueDegree : ℕ) =
      (E.toFiniteAbstractExtension.residueDegree D : ℕ) :=
  rfl

/-- The enriched ramification index agrees with the underlying invariant. -/
@[simp] theorem ramificationIndex_coe
    (E : FiniteResidueAbstractExtension D) :
    (E.ramificationIndex : ℕ) =
      (E.toFiniteAbstractExtension.ramificationIndex D : ℕ) :=
  rfl

end FiniteResidueAbstractExtension

end Atlas.Knowledge
