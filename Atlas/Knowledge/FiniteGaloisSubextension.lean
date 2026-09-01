import Mathlib
import Atlas.Knowledge.FiniteAbstractExtension
import Atlas.Knowledge.GaloisSubextension

/-!
# Finite Galois subextension

A finite Galois extension `L / K` of abstract fields, represented
contravariantly by `G_L ≤ G_K` with the relative subgroup normal and the
relative quotient finite — the index objects of the norm topology, and
the ambient bundle of the Frobenius power fixed-field tower (#104).

## Main definitions

* `FiniteGaloisSubextension` — the bundle: containment, normality,
  finiteness.
* `FiniteGaloisSubextension.extensionQuotient` — the finite quotient
  `G(L/K)` behind a named object boundary.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling, and
the normality instance is `subgroupOf_normalInstance`, after the layer's
`GaloisSubextension` item renamed its sibling the same way. The source
file's remaining API — the projection lemmas, the predicates, the
composita — waits for its consumers.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **A finite Galois extension `L / K`, represented by `G_L ≤ G_K`**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:26`]
[Yamaguchi2026]). -/
structure FiniteGaloisSubextension (K : ClosedSubgroup G) where
  /-- The closed subgroup representing the top field. -/
  field : ClosedSubgroup G
  /-- The top-field subgroup is contained in the base-field subgroup. -/
  below : field.toSubgroup ≤ K.toSubgroup
  /-- The top-field subgroup is normal inside the base-field subgroup. -/
  normal : (field.toSubgroup.subgroupOf K.toSubgroup).Normal
  /-- The relative Galois quotient is finite. -/
  finite : Finite (K.toSubgroup ⧸ field.toSubgroup.subgroupOf K.toSubgroup)

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- Forget only finiteness from a finite Galois subextension
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:41`]
[Yamaguchi2026]). -/
def toGaloisSubextension (L : FiniteGaloisSubextension K) :
    GaloisSubextension K where
  field := L.field
  below := L.below
  normal := L.normal

/-- Forget normality, retaining the underlying finite abstract extension —
the canonical bridge from a finite Galois subextension to the degree and
ramification API ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:50`]
[Yamaguchi2026]). -/
def toFiniteAbstractExtension (L : FiniteGaloisSubextension K) :
    FiniteAbstractExtension G where
  field := L.field
  base := K
  below := L.below
  finiteQuotient := L.finite

/-- **The actual finite quotient `G(L/K)`, kept behind a named object
boundary** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:59`]
[Yamaguchi2026]). -/
def extensionQuotient (L : FiniteGaloisSubextension K) : Type u :=
  K.toSubgroup ⧸ L.field.toSubgroup.subgroupOf K.toSubgroup

/-- A finite Galois subextension is represented by a normal subgroup
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:72`]
[Yamaguchi2026]). -/
instance subgroupOf_normalInstance (L : FiniteGaloisSubextension K) :
    (L.field.toSubgroup.subgroupOf K.toSubgroup).Normal :=
  L.normal

/-- The group structure transported across the named finite quotient
boundary ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:78`]
[Yamaguchi2026]). -/
instance extensionQuotient_groupInstance (L : FiniteGaloisSubextension K) :
    Group L.extensionQuotient := by
  change Group
    (K.toSubgroup ⧸ L.field.toSubgroup.subgroupOf K.toSubgroup)
  infer_instance

/-- The quotient represented by a finite Galois subextension is finite
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:85`]
[Yamaguchi2026]). -/
instance extensionQuotient_finiteInstance (L : FiniteGaloisSubextension K) :
    Finite L.extensionQuotient :=
  L.finite

/-- Comparison with the quotient presentation used by the underlying group
library ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:91`]
[Yamaguchi2026]). -/
def extensionQuotientMulEquiv (L : FiniteGaloisSubextension K) :
    L.extensionQuotient ≃*
      (K.toSubgroup ⧸ L.field.toSubgroup.subgroupOf K.toSubgroup) :=
  MulEquiv.refl _

/-- The finite and non-finite Galois bundles have the same quotient; this
named equivalence is the only public comparison clients need
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:143`]
[Yamaguchi2026]). -/
def toGaloisExtensionQuotientMulEquiv (L : FiniteGaloisSubextension K) :
    L.extensionQuotient ≃* L.toGaloisSubextension.extensionQuotient :=
  L.extensionQuotientMulEquiv.trans
    L.toGaloisSubextension.extensionQuotientMulEquiv.symm

end FiniteGaloisSubextension

end

end Atlas.Knowledge
