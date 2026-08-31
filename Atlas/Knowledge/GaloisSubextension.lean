import Mathlib
import Atlas.Knowledge.AbstractExtension

/-!
# Galois subextension

A not-necessarily-finite Galois extension above an abstract field: the upper
field's containment and the normality of the relative subgroup are carried by
the object, while no finiteness enters. The extension quotient — the Galois
group of the subextension — is a named object boundary with its group structure,
projection, and representative-free eliminator, and the ramification predicates
read through the underlying abstract extension.

## Main definitions

* `GaloisSubextension` — the extension object, with `toAbstractExtension`,
  `extensionQuotient`, `extensionQuotientMk`, and the comparison
  `extensionQuotientMulEquiv`.
* `GaloisSubextension.IsUnramified` / `GaloisSubextension.IsTotallyRamified` —
  through the underlying extension.

## Main statements

* `GaloisSubextension.extensionQuotient_inductionOn` — eliminate a Galois
  quotient without exposing a representative; proved.
* `GaloisSubextension.isUnramified_iff_inertia_le` /
  `GaloisSubextension.isTotallyRamified_iff_image_le` — the canonical readings;
  proved.

## Implementation notes

The relative subgroup is `Subgroup.subgroupOf`, spelled directly as in
`Atlas.Knowledge.AbstractExtension`; the quotient is a `def` rather than a
transparent abbreviation, so its group instance is transported by `change` and
the comparison with the underlying quotient presentation is a `MulEquiv.refl`
behind the boundary.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **A Galois subextension**: a not-necessarily-finite Galois extension above
`K` — the containment and the normality of the relative subgroup carried by the
object, no finiteness introduced
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:455`]
[Yamaguchi2026]). -/
structure GaloisSubextension (K : ClosedSubgroup G) where
  /-- The closed subgroup representing the top field. -/
  field : ClosedSubgroup G
  /-- The top-field subgroup is contained in the base-field subgroup. -/
  below : field.toSubgroup ≤ K.toSubgroup
  /-- The relative subgroup is normal in the base-field subgroup. -/
  normal : (field.toSubgroup.subgroupOf K.toSubgroup).Normal

namespace GaloisSubextension

variable {K : ClosedSubgroup G}

/-- Forget normality, keeping the underlying abstract extension. -/
def toAbstractExtension (L : GaloisSubextension K) : AbstractExtension G where
  field := L.field
  base := K
  below := L.below

/-- **The extension quotient** — the Galois group of the subextension, as a
named object boundary
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:476`]
[Yamaguchi2026]). -/
def extensionQuotient (L : GaloisSubextension K) : Type u :=
  K.toSubgroup ⧸ L.field.toSubgroup.subgroupOf K.toSubgroup

/-- Structural unramifiedness of a Galois subextension. -/
def IsUnramified (L : GaloisSubextension K) (D : DegreeData G) : Prop :=
  L.toAbstractExtension.IsUnramified D

/-- Structural total ramification of a Galois subextension. -/
def IsTotallyRamified (L : GaloisSubextension K) (D : DegreeData G) : Prop :=
  L.toAbstractExtension.IsTotallyRamified D

/-- A Galois subextension's relative subgroup is normal. -/
instance subgroupOf_normalInstance (L : GaloisSubextension K) :
    (L.field.toSubgroup.subgroupOf K.toSubgroup).Normal :=
  L.normal

/-- The group structure across the named quotient boundary. -/
instance extensionQuotient_groupInstance (L : GaloisSubextension K) :
    Group L.extensionQuotient := by
  change Group (K.toSubgroup ⧸ L.field.toSubgroup.subgroupOf K.toSubgroup)
  infer_instance

/-- Comparison with the underlying quotient presentation. -/
def extensionQuotientMulEquiv (L : GaloisSubextension K) :
    L.extensionQuotient ≃*
      (K.toSubgroup ⧸ L.field.toSubgroup.subgroupOf K.toSubgroup) :=
  MulEquiv.refl _

/-- The canonical quotient projection of a Galois subextension. -/
def extensionQuotientMk (L : GaloisSubextension K) :
    K.toSubgroup →* L.extensionQuotient :=
  QuotientGroup.mk' (L.field.toSubgroup.subgroupOf K.toSubgroup)

/-- The named projection agrees with `QuotientGroup.mk` under the comparison. -/
@[simp]
theorem extensionQuotientMk_apply (L : GaloisSubextension K)
    (k : K.toSubgroup) :
    L.extensionQuotientMulEquiv (L.extensionQuotientMk k) =
      (QuotientGroup.mk k :
        K.toSubgroup ⧸ L.field.toSubgroup.subgroupOf K.toSubgroup) :=
  rfl

/-- **Eliminate a Galois quotient without exposing a representative**
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:521`]
[Yamaguchi2026]). -/
protected theorem extensionQuotient_inductionOn
    (L : GaloisSubextension K) {motive : L.extensionQuotient → Prop}
    (q : L.extensionQuotient)
    (mk : ∀ k : K.toSubgroup, motive (L.extensionQuotientMk k)) :
    motive q :=
  @Quotient.inductionOn' K.toSubgroup
    (QuotientGroup.leftRel (L.field.toSubgroup.subgroupOf K.toSubgroup))
    motive q mk

/-- Unramifiedness is the inertia containment. -/
theorem isUnramified_iff_inertia_le (L : GaloisSubextension K)
    (D : DegreeData G) :
    L.IsUnramified D ↔
      K.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ L.field.toSubgroup :=
  L.toAbstractExtension.isUnramified_iff_inertia_le D

/-- Total ramification is the image containment. -/
theorem isTotallyRamified_iff_image_le (L : GaloisSubextension K)
    (D : DegreeData G) :
    L.IsTotallyRamified D ↔
      K.toSubgroup.map D.degree.toMonoidHom ≤
        L.field.toSubgroup.map D.degree.toMonoidHom :=
  L.toAbstractExtension.isTotallyRamified_iff_image_le D

end GaloisSubextension

end Atlas.Knowledge
