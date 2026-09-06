import Mathlib
import Atlas.Knowledge.FrobeniusExponent
import Atlas.Knowledge.MaximalUnramifiedField

/-!
# inertia quotient as degree kernel

The canonical actual-group identification of the Frobenius norm-identity
lemma: the Galois quotient `G(L̃|K̃)` of the maximal unramified extensions
is the kernel of the continuous normalized degree inside `G(L̃|K)`, and it
is finite as soon as `L | K` is — no separate finiteness assumption enters
(#104).

## Main definitions

* `DegreeData.inertiaQuotientDegreeKernelEquiv` — `G(L̃|K̃)` as the kernel
  of `d_K` in `G(L̃|K)`.

## Main statements

* `DegreeData.maximalUnramifiedExtension_finite` — `L̃ | K̃` is finite when
  `L | K` is; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling; the
containment hypothesis of the finiteness statement and its two private
helpers lives only inside the source's `extensionSubgroup` spelling and
drops out here.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/- The inclusion of inertia cosets into the finite extension cosets
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:33`). -/
private noncomputable def inertiaCosetToExtensionCoset (D : DegreeData G)
    (K L : ClosedSubgroup G) :
    ((D.maximalUnramifiedField K).toSubgroup ⧸
        (D.maximalUnramifiedField L).toSubgroup.subgroupOf
          (D.maximalUnramifiedField K).toSubgroup) →
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
  Quotient.map'
    (fun x : (D.maximalUnramifiedField K).toSubgroup =>
      (⟨x.1, x.2.1⟩ : K.toSubgroup))
    (by
      intro x y hxy
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      exact hxy.1)

/- The coset inclusion is injective (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:48`). -/
private theorem inertiaCosetToExtensionCoset_injective (D : DegreeData G)
    (K L : ClosedSubgroup G) :
    Function.Injective (D.inertiaCosetToExtensionCoset K L) := by
  intro x y hxy
  refine Quotient.inductionOn₂' x y ?_ hxy
  intro a b hab
  apply Quotient.sound'
  rw [QuotientGroup.leftRel_apply]
  have habE :
      (⟨a.1, a.2.1⟩ : K.toSubgroup)⁻¹ * ⟨b.1, b.2.1⟩ ∈
        L.toSubgroup.subgroupOf K.toSubgroup := by
    exact QuotientGroup.leftRel_apply.mp (Quotient.exact' hab)
  refine ⟨habE, ?_⟩
  change D.degree (a.1⁻¹ * b.1) = 1
  rw [map_mul, map_inv]
  change (D.degree a.1)⁻¹ * D.degree b.1 = 1
  rw [show D.degree a.1 = 1 from a.2.2,
    show D.degree b.1 = 1 from b.2.2]
  simp

/-- **The extension `L̃ | K̃` is finite when `L | K` is** (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:70`). -/
theorem maximalUnramifiedExtension_finite (D : DegreeData G)
    (K L : ClosedSubgroup G)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    Finite
      ((D.maximalUnramifiedField K).toSubgroup ⧸
        (D.maximalUnramifiedField L).toSubgroup.subgroupOf
          (D.maximalUnramifiedField K).toSubgroup) :=
  Finite.of_injective (D.inertiaCosetToExtensionCoset K L)
    (D.inertiaCosetToExtensionCoset_injective K L)

/- The inertia quotient maps into the degree kernel (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:83`). -/
private noncomputable def inertiaCosetToDegreeKernel (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        (D.maximalUnramifiedField L).toSubgroup.subgroupOf
          (D.maximalUnramifiedField K.field).toSubgroup) →
      (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker :=
  fun r => Quotient.liftOn' r
    (fun x : (D.maximalUnramifiedField K.field).toSubgroup => by
      let k : K.field.toSubgroup := ⟨x.1, x.2.1⟩
      refine ⟨QuotientGroup.mk k, ?_⟩
      change D.normalizedDegree K k = 1
      change k ∈ (D.normalizedDegree K).toMonoidHom.ker
      rw [D.normalizedDegree_ker K]
      exact x.2.2)
    (by
      intro x y hxy
      apply Subtype.ext
      apply QuotientGroup.eq.mpr
      rw [← D.subgroupOf_maximalUnramifiedField K.field L hLK]
      rw [QuotientGroup.leftRel_apply] at hxy
      exact hxy)

/- The kernel comparison is bijective (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:108`). -/
private theorem inertiaCosetToDegreeKernel_bijective (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    Function.Bijective (D.inertiaCosetToDegreeKernel K L hLK) := by
  constructor
  · intro x y hxy
    refine Quotient.inductionOn₂' x y ?_ hxy
    intro a b hab
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    have hq : QuotientGroup.mk (⟨a.1, a.2.1⟩ : K.field.toSubgroup) =
        QuotientGroup.mk (⟨b.1, b.2.1⟩ : K.field.toSubgroup) :=
      congrArg Subtype.val hab
    have hkN :
        (⟨a.1, a.2.1⟩ : K.field.toSubgroup)⁻¹ * ⟨b.1, b.2.1⟩ ∈
          D.extensionInertiaWithin K.field L hLK :=
      QuotientGroup.eq.mp hq
    refine ⟨hkN.1, ?_⟩
    change D.degree (a.1⁻¹ * b.1) = 1
    rw [map_mul, map_inv]
    change (D.degree a.1)⁻¹ * D.degree b.1 = 1
    rw [show D.degree a.1 = 1 from a.2.2,
      show D.degree b.1 = 1 from b.2.2]
    simp
  · intro z
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective
      (D.extensionInertiaWithin K.field L hLK) z.1
    have hkNorm : D.normalizedDegree K k = 1 := by
      change D.extensionNormalizedDegreeContinuous K L hLK
          ((QuotientGroup.mk'
            (D.extensionInertiaWithin K.field L hLK)) k) = 1
      exact (congrArg
        (D.extensionNormalizedDegreeContinuous K L hLK) hk).trans z.2
    have hkI : k ∈ D.fieldInertiaWithin K.field := by
      rw [← D.normalizedDegree_ker K]
      exact hkNorm
    let x : (D.maximalUnramifiedField K.field).toSubgroup :=
      ⟨k.1, ⟨k.2, hkI⟩⟩
    refine ⟨QuotientGroup.mk x, ?_⟩
    apply Subtype.ext
    exact hk

/-- **The Galois quotient `G(L̃|K̃)` is the kernel of `d_K` in `G(L̃|K)`**
— the canonical actual-group identification of the Frobenius norm-identity
lemma (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:151`). -/
noncomputable def inertiaQuotientDegreeKernelEquiv (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        (D.maximalUnramifiedField L).toSubgroup.subgroupOf
          (D.maximalUnramifiedField K.field).toSubgroup) ≃
      (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker :=
  Equiv.ofBijective (D.inertiaCosetToDegreeKernel K L hLK)
    (D.inertiaCosetToDegreeKernel_bijective K L hLK)

end DegreeData

end

end Atlas.Knowledge
