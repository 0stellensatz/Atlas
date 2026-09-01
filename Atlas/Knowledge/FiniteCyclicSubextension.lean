import Mathlib
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteAbstractFieldExtension

/-!
# finite cyclic subextension of an abstract field

A finite cyclic extension of a bundled finite abstract field: the closed
subgroup, its containment, normality of the relative subgroup, finiteness of
the relative Galois quotient, and a chosen generator with its cyclicity
witness — all travelling together, so none of them can detach from the
subgroups they belong to. This is the shape over which the class-field axiom
quantifies (#104).

## Main definitions

* `FiniteCyclicSubextension` — the bundled finite cyclic extension.
* `FiniteCyclicSubextension.toFiniteAbstractExtension` /
  `toFiniteAbstractFieldExtension` — the forgetful passages.

## Implementation notes

The engine's relative subgroup is `Subgroup.subgroupOf` as across the layer,
and the source's `@[implicit_reducible]` markers on the forgetful passages
are Lean-core transparency attributes, dropped as in the rest of the engine
layer.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **A finite cyclic extension of a bundled finite abstract field** — the
generator and its cyclicity proof travel with the finite normal extension
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean:30`]
[Yamaguchi2026]). -/
structure FiniteCyclicSubextension (K : FiniteAbstractField G) where
  /-- The closed subgroup representing the top field. -/
  field : ClosedSubgroup G
  /-- The top-field subgroup is contained in the base-field subgroup. -/
  below : field.toSubgroup ≤ K.field.toSubgroup
  /-- The top-field subgroup is normal inside the base-field subgroup. -/
  normal : (field.toSubgroup.subgroupOf K.field.toSubgroup).Normal
  /-- The relative Galois quotient is finite. -/
  finite : Finite (K.field.toSubgroup ⧸
    field.toSubgroup.subgroupOf K.field.toSubgroup)
  /-- A chosen generator of the relative Galois quotient. -/
  generator : K.field.toSubgroup ⧸
    field.toSubgroup.subgroupOf K.field.toSubgroup
  /-- Every quotient element is a power of the chosen generator. -/
  generates : ∀ x, x ∈ Subgroup.zpowers generator

namespace FiniteCyclicSubextension

variable {K : FiniteAbstractField G}

/-- Forget the cyclic generator and normality, retaining the underlying
finite abstract extension ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean:52`]
[Yamaguchi2026]). -/
def toFiniteAbstractExtension (E : FiniteCyclicSubextension K) :
    FiniteAbstractExtension G where
  field := E.field
  base := K.field
  below := E.below
  finiteQuotient := E.finite

/-- Structural unramifiedness of the underlying finite extension
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean:60`]
[Yamaguchi2026]). -/
def IsUnramified (E : FiniteCyclicSubextension K) (D : DegreeData G) : Prop :=
  E.toFiniteAbstractExtension.IsUnramified D

/-- Structural total ramification of the underlying finite extension
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean:64`]
[Yamaguchi2026]). -/
def IsTotallyRamified (E : FiniteCyclicSubextension K)
    (D : DegreeData G) : Prop :=
  E.toFiniteAbstractExtension.IsTotallyRamified D

/-- Retain the finite-over-base endpoint bundles as well as the relative
finite quotient ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean:71`]
[Yamaguchi2026]). -/
def toFiniteAbstractFieldExtension
    (E : FiniteCyclicSubextension K) : FiniteAbstractFieldExtension G := by
  letI : Finite
      (K.field.toSubgroup ⧸
        E.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
    E.finite
  exact FiniteAbstractFieldExtension.ofInclusion E.field K E.below

/-- A finite cyclic subextension supplies normality of its relative subgroup
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean:79`]
[Yamaguchi2026]). -/
instance (E : FiniteCyclicSubextension K) :
    (E.field.toSubgroup.subgroupOf K.field.toSubgroup).Normal :=
  E.normal

/-- A finite cyclic subextension supplies finiteness of its Galois quotient
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean:84`]
[Yamaguchi2026]). -/
instance (E : FiniteCyclicSubextension K) :
    Finite (K.field.toSubgroup ⧸
      E.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
  E.finite

/-- The finite quotient of a cyclic subextension, canonically enumerated
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean:89`]
[Yamaguchi2026]). -/
noncomputable instance (E : FiniteCyclicSubextension K) :
    Fintype (K.field.toSubgroup ⧸
      E.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
  Fintype.ofFinite _

end FiniteCyclicSubextension

end

end Atlas.Knowledge
