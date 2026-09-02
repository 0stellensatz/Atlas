import Mathlib
import Atlas.Knowledge.FiniteAbstractExtension
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteAbstractFieldExtension
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
* `FiniteGaloisSubextension.extensionQuotientMk` — the canonical quotient
  projection.
* `FiniteGaloisSubextension.compositum` — the compositum `L₁L₂`,
  contravariantly the intersection of the two closed subgroups.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
and the normality instance is `subgroupOf_normalInstance`, after the
layer's `GaloisSubextension` item renamed its sibling the same way.
Seven source declarations stay unported — none is consumed inside
`Main.lean`'s import closure, the window this port serves, though four
have consumers in `Reciprocity/` files beyond it —
`toGaloisSubextension_isUnramified_iff`,
`toGaloisSubextension_isTotallyRamified_iff`,
`isUnramified_toGaloisSubextension`, `finite_intermediate_extension`,
`baseChange`, and the pair `finiteNormSubgroup_compositum_le_left` /
`finiteNormSubgroup_compositum_le_right`; the source's two
tower-finiteness theorems already live in the layer's
`Atlas.Knowledge.finite_extension_trans` and
`Atlas.Knowledge.finite_extension_over_intermediate`.

Two proofs depart from the source.
`isTotallyRamified_toGaloisSubextension` is the hypothesis itself — the
finite and Galois predicates are definitionally equal, and the source's
route runs through the skipped bundling iff. `refl` closes its two
identity subproofs with `Subgroup.subgroupOf_self`, which the layer's
relative-subgroup spelling makes directly applicable where the source
proves the identity by hand.

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

/-- **The actual finite quotient `G(L/K)`, kept behind a named object boundary**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:59`]
[Yamaguchi2026]). -/
def extensionQuotient (L : FiniteGaloisSubextension K) : Type u :=
  K.toSubgroup ⧸ L.field.toSubgroup.subgroupOf K.toSubgroup

/-- Structural unramifiedness of the underlying finite extension
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:63`]
[Yamaguchi2026]). -/
def IsUnramified (L : FiniteGaloisSubextension K) (D : DegreeData G) : Prop :=
  L.toFiniteAbstractExtension.IsUnramified D

/-- Structural total ramification of the underlying finite extension
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:67`]
[Yamaguchi2026]). -/
def IsTotallyRamified (L : FiniteGaloisSubextension K)
    (D : DegreeData G) : Prop :=
  L.toFiniteAbstractExtension.IsTotallyRamified D

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

/-- **The canonical quotient projection for a finite Galois subextension**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:97`]
[Yamaguchi2026]). -/
def extensionQuotientMk (L : FiniteGaloisSubextension K) :
    K.toSubgroup →* L.extensionQuotient :=
  QuotientGroup.mk' (L.field.toSubgroup.subgroupOf K.toSubgroup)

/-- The named finite Galois quotient projection agrees with
`QuotientGroup.mk` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:103`]
[Yamaguchi2026]). -/
@[simp]
theorem extensionQuotientMk_apply (L : FiniteGaloisSubextension K)
    (k : K.toSubgroup) :
    L.extensionQuotientMulEquiv (L.extensionQuotientMk k) =
      (QuotientGroup.mk k :
        K.toSubgroup ⧸ L.field.toSubgroup.subgroupOf K.toSubgroup) :=
  rfl

/-- A quotient representative is trivial exactly when it lies in the
relative subgroup ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:112`]
[Yamaguchi2026]). -/
@[simp]
theorem extensionQuotientMk_eq_one_iff (L : FiniteGaloisSubextension K)
    (k : K.toSubgroup) :
    L.extensionQuotientMk k = 1 ↔
      k ∈ L.field.toSubgroup.subgroupOf K.toSubgroup := by
  constructor
  · intro h
    apply (QuotientGroup.eq_one_iff k).1
    calc
      (QuotientGroup.mk k :
          K.toSubgroup ⧸ L.field.toSubgroup.subgroupOf K.toSubgroup) =
          L.extensionQuotientMulEquiv (L.extensionQuotientMk k) :=
        (L.extensionQuotientMk_apply k).symm
      _ = L.extensionQuotientMulEquiv 1 :=
        congrArg L.extensionQuotientMulEquiv h
      _ = 1 := L.extensionQuotientMulEquiv.map_one
  · intro hk
    apply L.extensionQuotientMulEquiv.injective
    rw [L.extensionQuotientMk_apply, L.extensionQuotientMulEquiv.map_one]
    exact (QuotientGroup.eq_one_iff k).2 hk

/-- The canonical projection onto the finite Galois quotient is surjective
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:132`]
[Yamaguchi2026]). -/
theorem extensionQuotientMk_surjective (L : FiniteGaloisSubextension K) :
    Function.Surjective L.extensionQuotientMk := by
  intro q
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective
    (L.field.toSubgroup.subgroupOf K.toSubgroup)
    (L.extensionQuotientMulEquiv q)
  refine ⟨k, L.extensionQuotientMulEquiv.injective ?_⟩
  rw [L.extensionQuotientMk_apply]
  exact hk

/-- The finite and non-finite Galois bundles have the same quotient; this
named equivalence is the only public comparison clients need
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:143`]
[Yamaguchi2026]). -/
def toGaloisExtensionQuotientMulEquiv (L : FiniteGaloisSubextension K) :
    L.extensionQuotient ≃* L.toGaloisSubextension.extensionQuotient :=
  L.extensionQuotientMulEquiv.trans
    L.toGaloisSubextension.extensionQuotientMulEquiv.symm

/-- Eliminate a finite Galois quotient without exposing a chosen
representative ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:150`]
[Yamaguchi2026]). -/
protected theorem extensionQuotient_inductionOn
    (L : FiniteGaloisSubextension K) {motive : L.extensionQuotient → Prop}
    (q : L.extensionQuotient)
    (mk : ∀ k : K.toSubgroup, motive (L.extensionQuotientMk k)) :
    motive q := by
  exact @Quotient.inductionOn' K.toSubgroup
    (QuotientGroup.leftRel (L.field.toSubgroup.subgroupOf K.toSubgroup))
    motive q mk

/-- Transport a total-ramification proof through the finite-to-Galois
forgetful map ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:183`]
[Yamaguchi2026]). -/
theorem isTotallyRamified_toGaloisSubextension
    (L : FiniteGaloisSubextension K) (D : DegreeData G)
    (hL : L.IsTotallyRamified D) :
    L.toGaloisSubextension.IsTotallyRamified D :=
  hL

/-- Unramifiedness is the canonical inertia-containment condition
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:190`]
[Yamaguchi2026]). -/
theorem isUnramified_iff_inertia_le (L : FiniteGaloisSubextension K)
    (D : DegreeData G) :
    L.IsUnramified D ↔
      K.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ L.field.toSubgroup :=
  L.toFiniteAbstractExtension.isUnramified_iff_inertia_le D

/-- Total ramification is the canonical containment of degree images
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:197`]
[Yamaguchi2026]). -/
theorem isTotallyRamified_iff_image_le (L : FiniteGaloisSubextension K)
    (D : DegreeData G) :
    L.IsTotallyRamified D ↔
      K.toSubgroup.map D.degree.toMonoidHom ≤
        L.field.toSubgroup.map D.degree.toMonoidHom :=
  L.toFiniteAbstractExtension.isTotallyRamified_iff_image_le D

/-- Retain the finite-over-base endpoint bundles of a finite Galois
subextension of an abstract field which is finite over the distinguished
base ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:207`]
[Yamaguchi2026]). -/
def toFiniteAbstractFieldExtension
    {K : FiniteAbstractField G} (L : FiniteGaloisSubextension K.field) :
    FiniteAbstractFieldExtension G := by
  letI : Finite
      (K.field.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
    L.finite
  exact FiniteAbstractFieldExtension.ofInclusion L.field K L.below

/-- The trivial extension `K / K` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:332`]
[Yamaguchi2026]). -/
def refl (K : ClosedSubgroup G) : FiniteGaloisSubextension K where
  field := K
  below := le_rfl
  normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  finite := by
    rw [Subgroup.subgroupOf_self]
    infer_instance

/-- **The compositum `L₁L₂`, represented by `G_{L₁} ∩ G_{L₂}`**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:351`]
[Yamaguchi2026]). -/
def compositum (L₁ L₂ : FiniteGaloisSubextension K) :
    FiniteGaloisSubextension K where
  field := L₁.field ⊓ L₂.field
  below := fun _ h => L₁.below h.1
  normal := by
    have heq : (L₁.field ⊓ L₂.field).toSubgroup.subgroupOf K.toSubgroup =
        L₁.field.toSubgroup.subgroupOf K.toSubgroup ⊓
          L₂.field.toSubgroup.subgroupOf K.toSubgroup := by
      ext k
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      constructor
      · intro hk
        exact ⟨hk.1, hk.2⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, h₂⟩
    rw [heq]
    letI : (L₁.field.toSubgroup.subgroupOf K.toSubgroup).Normal := L₁.normal
    letI : (L₂.field.toSubgroup.subgroupOf K.toSubgroup).Normal := L₂.normal
    infer_instance
  finite := by
    have heq : (L₁.field ⊓ L₂.field).toSubgroup.subgroupOf K.toSubgroup =
        L₁.field.toSubgroup.subgroupOf K.toSubgroup ⊓
          L₂.field.toSubgroup.subgroupOf K.toSubgroup := by
      ext k
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      constructor
      · intro hk
        exact ⟨hk.1, hk.2⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, h₂⟩
    letI : (L₁.field.toSubgroup.subgroupOf K.toSubgroup).FiniteIndex :=
      @Subgroup.finiteIndex_of_finite_quotient K.toSubgroup _
        (L₁.field.toSubgroup.subgroupOf K.toSubgroup) L₁.finite
    letI : (L₂.field.toSubgroup.subgroupOf K.toSubgroup).FiniteIndex :=
      @Subgroup.finiteIndex_of_finite_quotient K.toSubgroup _
        (L₂.field.toSubgroup.subgroupOf K.toSubgroup) L₂.finite
    rw [heq]
    exact Subgroup.finite_quotient_of_finiteIndex

/-- The compositum lies below its left input ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:393`]
[Yamaguchi2026]). -/
theorem compositum_le_left (L₁ L₂ : FiniteGaloisSubextension K) :
    (L₁.compositum L₂).field.toSubgroup ≤ L₁.field.toSubgroup :=
  inf_le_left

/-- The compositum lies below its right input ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:398`]
[Yamaguchi2026]). -/
theorem compositum_le_right (L₁ L₂ : FiniteGaloisSubextension K) :
    (L₁.compositum L₂).field.toSubgroup ≤ L₂.field.toSubgroup :=
  inf_le_right

end FiniteGaloisSubextension

end

end Atlas.Knowledge
