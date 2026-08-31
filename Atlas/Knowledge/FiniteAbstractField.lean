import Mathlib
import Atlas.Knowledge.FiniteAbstractExtension
import Atlas.Knowledge.FiniteResidueAbstractField

/-!
# abstract field finite over the base

An abstract field of finite degree over the distinguished base field — the
objects the reciprocity engine's axioms quantify over (#104). Such a field is a
finite extension of the base, its absolute residue quotient is finite because
the ambient degree is surjective, and its positive residue degree therefore
exists, with the base field itself of residue degree one.

## Main definitions

* `FiniteAbstractField` — the field with its finiteness certificate, and
  `FiniteAbstractField.base` for the distinguished base.
* `FiniteAbstractField.toFiniteAbstractExtension` /
  `FiniteAbstractField.toFiniteResidueAbstractField` — the two enrichments.
* `FiniteAbstractField.residueDegree` — the positive absolute residue degree.

## Main statements

* `FiniteAbstractField.eq_of_field_eq` — the object is determined by its
  subgroup; proved.
* `FiniteAbstractField.base_residueDegree` — the base field has residue degree
  one; proved.

## Implementation notes

The source marks `toFiniteResidueAbstractField` `@[implicit_reducible]` — Lean
core's instances-transparency attribute; it is dropped here, restorable at the
first consumer that unfolds through it.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **An abstract field finite over the distinguished base**
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:1087`][Yamaguchi2026]). -/
structure FiniteAbstractField (G : Type u) [Group G] [TopologicalSpace G] where
  /-- The closed subgroup representing the abstract field. -/
  field : ClosedSubgroup G
  /-- The field has finite degree over the distinguished base. -/
  finite : Finite ((baseField G).toSubgroup ⧸
    field.toSubgroup.subgroupOf (baseField G).toSubgroup)

namespace FiniteAbstractField

/-- A finite abstract field is determined by its subgroup: the finiteness
component is proof-irrelevant. -/
theorem eq_of_field_eq (K L : FiniteAbstractField G)
    (h : K.field = L.field) : K = L := by
  cases K with
  | mk K hK =>
    cases L with
    | mk L hL =>
      cases h
      rfl

/-- The distinguished base field, with its trivial finite quotient. -/
noncomputable def base (G : Type u) [Group G] [TopologicalSpace G] :
    FiniteAbstractField G where
  field := baseField G
  finite := by
    letI : ((baseField G).toSubgroup.subgroupOf
        (baseField G).toSubgroup).Normal := by
      rw [show (baseField G).toSubgroup.subgroupOf (baseField G).toSubgroup = ⊤
        from by
          ext x
          exact ⟨fun _ => Subgroup.mem_top x, fun _ => x.2⟩]
      infer_instance
    letI : Subsingleton
        ((baseField G).toSubgroup ⧸
          (baseField G).toSubgroup.subgroupOf (baseField G).toSubgroup) := by
      constructor
      intro x y
      refine Quotient.inductionOn₂' x y ?_
      intro a b
      apply QuotientGroup.eq_iff_div_mem.mpr
      exact (a / b).2
    infer_instance

/-- A finite abstract field as a finite extension of the base. -/
def toFiniteAbstractExtension (K : FiniteAbstractField G) :
    FiniteAbstractExtension G where
  field := K.field
  base := baseField G
  below := le_baseField K.field
  finiteQuotient := K.finite

/-- A finite abstract field supplies finiteness over the base. -/
instance (K : FiniteAbstractField G) :
    Finite ((baseField G).toSubgroup ⧸
      K.field.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
  K.finite

/-- **A field finite over the base has finite absolute residue quotient**: from
the finite relative quotient and the surjectivity of the ambient degree
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:1150`][Yamaguchi2026]). -/
noncomputable def toFiniteResidueAbstractField
    (K : FiniteAbstractField G) (D : DegreeData G) :
    FiniteResidueAbstractField D where
  field := K.field
  finiteResidueQuotient := by
    apply Cardinal.lt_aleph0_iff_finite.mp
    change
      intersectionIndexCardinal (D.fieldImage K.field)
        (⊤ : Subgroup ProfiniteIntegerMul) < Cardinal.aleph0
    rw [D.fieldImage_eq_map]
    have htop :
        (baseField G).toSubgroup.map D.degree.toMonoidHom = ⊤ := by
      rw [baseField_toSubgroup]
      exact Subgroup.map_top_of_surjective _ D.degree_surjective
    rw [← htop]
    simpa only [FiniteAbstractField.toFiniteAbstractExtension,
      AbstractExtension.relativeResidueDegreeCardinal,
      relativeIndexCardinal] using
      K.toFiniteAbstractExtension.relativeResidueDegreeCardinal_lt_aleph0 D

/-- The positive absolute residue degree of a field finite over the base. -/
noncomputable def residueDegree (K : FiniteAbstractField G)
    (D : DegreeData G) : ℕ+ :=
  (K.toFiniteResidueAbstractField D).residueDegree

/-- **The base field has residue degree one**
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:1178`][Yamaguchi2026]). -/
@[simp] theorem base_residueDegree (D : DegreeData G) :
    (FiniteAbstractField.base G).residueDegree D = 1 := by
  apply Subtype.ext
  change (((FiniteAbstractField.base G).toFiniteResidueAbstractField
    D).residueDegree : ℕ) = 1
  apply Nat.cast_injective (R := Cardinal)
  rw [← FiniteResidueAbstractField.residueDegreeCardinal_eq_coe]
  exact D.residueDegreeCardinal_baseField

/-- The field residue degree is that of its residue-field enrichment. -/
@[simp] theorem residueDegree_coe (K : FiniteAbstractField G)
    (D : DegreeData G) :
    (K.residueDegree D : ℕ) =
      ((K.toFiniteResidueAbstractField D).residueDegree : ℕ) :=
  rfl

end FiniteAbstractField

end Atlas.Knowledge
