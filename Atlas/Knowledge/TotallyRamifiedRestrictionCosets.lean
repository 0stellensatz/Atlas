import Mathlib
import Atlas.Knowledge.AbstractExtension
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractExtension
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.IntermediateGaloisCorrespondence
import Atlas.Knowledge.ReciprocityExactRows
import Atlas.Knowledge.ReductionGaloisArrows
import Atlas.Knowledge.RelativeNorm

/-!
# totally ramified restriction cosets

Restriction transport for finite Galois subextensions in the totally
ramified argument: the quotient restriction between named finite Galois
boundaries, the coset map from the lower maximal-unramified quotient to
a totally ramified quotient with its bijectivity, the induced coset and
multiplicative equivalences, the compatibility of relative actions and
norms along them, and the commutation and action-equality lemmas for
auxiliary quotient elements with equal restriction (#104).

## Main definitions

* `FiniteGaloisSubextension.abstractReciprocityRestrictionMulEquiv` —
  the multiplicative restriction equivalence from the lower Galois
  group to the original totally ramified quotient.

## Main statements

* `FiniteGaloisSubextension.abstractReciprocityRestrictionCosetMap_bijective`
  — the coset map is bijective when the upper extension is totally
  ramified and the auxiliary field contains the relevant inertia;
  proved.
* `FiniteGaloisSubextension.abstractReciprocity_relativeNorm_fixedFieldInclusion`
  — relative norm commutes with fixed-field inclusion along the
  restriction equivalence; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling, so
`mem_extensionSubgroup_iff` becomes Mathlib's `Subgroup.mem_subgroupOf`
and the correspondence lemma is the layer's
`subgroupOf_intermediateField_eq`. `DegreeData.AbstractExtension` and
`DegreeData.FiniteAbstractExtension` are the layer's top-level
`AbstractExtension` and `FiniteAbstractExtension`. The ambient group is
`Type u` where the source pins `IntegralRepGroupType` — a pure
widening: the representation-bearing statements only instantiate the
layer's already-polymorphic vocabulary. Three statement-level `let`
bindings for the lower containment go unreferenced under the spelling
(the quotient type no longer names its containment proof) and stay as
underscore-named `let`s, so the statement shape consumers walk through
matches the source's. `commute_of_same_restriction_of_inertia_le` sheds
the source's unused `[IsTopologicalGroup G]`: the elaborated proof
never consumes it and it is not derivable, so the ported statement is
strictly more general. Everything else ports token-for-token; the file
is the source's `TotallyRamifiedCase/RestrictionCosets.lean` whole.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

/-- Restriction between the named finite Galois quotient boundaries
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/RestrictionCosets.lean:23`]
[Yamaguchi2026]). -/
def bundledRestrictionHom
    {K : ClosedSubgroup G}
    (M L : FiniteGaloisSubextension K)
    (hML : M.field.toSubgroup ≤ L.field.toSubgroup) :
    M.extensionQuotient →* L.extensionQuotient :=
  L.extensionQuotientMulEquiv.symm.toMonoidHom.comp
    ((abstractReciprocityRestriction
      K L.field M.field hML L.below).comp
        M.extensionQuotientMulEquiv.toMonoidHom)

/-- The coset map from the lower maximal-unramified quotient to a
totally ramified quotient ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/RestrictionCosets.lean:35`]
[Yamaguchi2026]). -/
def abstractReciprocityRestrictionCosetMap
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup) :
    let M₀ := M.maximalUnramifiedSubextension D
    let _hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
      M.field_le_intermediateField (M.inertiaImage D)
    (M₀.toSubgroup ⧸ M.field.toSubgroup.subgroupOf M₀.toSubgroup) →
      (E.base.toSubgroup ⧸ E.subgroup) := by
  let S := M.inertiaImage D
  let M₀ := M.maximalUnramifiedSubextension D
  let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
    M.field_le_intermediateField S
  let hM₀K : M₀.toSubgroup ≤ E.base.toSubgroup :=
    M.intermediateField_le_base S
  exact Quotient.map'
    (fun x : M₀.toSubgroup =>
      (⟨x.1, hM₀K x.2⟩ : E.base.toSubgroup))
    (by
      intro x y hxy
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      exact hME hxy)

/-- **The restriction coset map is bijective when the upper extension is
totally ramified and the auxiliary field contains the relevant
inertia** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/RestrictionCosets.lean:61`]
[Yamaguchi2026]). -/
theorem abstractReciprocityRestrictionCosetMap_bijective
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    (hTot : E.IsTotallyRamified D)
    (hInertia : ∀ i : E.base.toSubgroup,
      i ∈ D.fieldInertiaWithin E.base →
      i.1 ∈ E.field.toSubgroup → i.1 ∈ M.field.toSubgroup) :
    Function.Bijective
      (M.abstractReciprocityRestrictionCosetMap D E hME) := by
  let S := M.inertiaImage D
  let M₀ := M.maximalUnramifiedSubextension D
  let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
    M.field_le_intermediateField S
  let hM₀K : M₀.toSubgroup ≤ E.base.toSubgroup :=
    M.intermediateField_le_base S
  constructor
  · intro x y hxy
    refine Quotient.inductionOn₂' x y ?_ hxy
    intro a b hab
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    let aK : E.base.toSubgroup := ⟨a.1, hM₀K a.2⟩
    let bK : E.base.toSubgroup := ⟨b.1, hM₀K b.2⟩
    let z : E.base.toSubgroup := aK⁻¹ * bK
    have habE : aK⁻¹ * bK ∈ E.subgroup := by
      exact QuotientGroup.leftRel_apply.mp (Quotient.exact' hab)
    have hzE : z.1 ∈ E.field.toSubgroup :=
      Subgroup.mem_subgroupOf.1 habE
    have haP : aK ∈ M.intermediateSubgroup S := by
      rw [← M.subgroupOf_intermediateField_eq S]
      exact Subgroup.mem_subgroupOf.2 a.2
    have hbP : bK ∈ M.intermediateSubgroup S := by
      rw [← M.subgroupOf_intermediateField_eq S]
      exact Subgroup.mem_subgroupOf.2 b.2
    have hzP : z ∈ M.intermediateSubgroup S :=
      (M.intermediateSubgroup S).mul_mem
        ((M.intermediateSubgroup S).inv_mem haP) hbP
    change (QuotientGroup.mk'
      (M.field.toSubgroup.subgroupOf E.base.toSubgroup)) z ∈
        (D.fieldInertiaWithin E.base).map
          (QuotientGroup.mk'
            (M.field.toSubgroup.subgroupOf E.base.toSubgroup)) at hzP
    obtain ⟨i, hiI, hi⟩ := hzP
    have hizM : i⁻¹ * z ∈
        M.field.toSubgroup.subgroupOf E.base.toSubgroup :=
      QuotientGroup.eq.mp hi
    have hizM' : i.1⁻¹ * z.1 ∈ M.field.toSubgroup :=
      Subgroup.mem_subgroupOf.1 hizM
    have hiE : i.1 ∈ E.field.toSubgroup := by
      have hmul := E.field.toSubgroup.mul_mem hzE
        (E.field.toSubgroup.inv_mem (hME hizM'))
      simpa [mul_inv_rev, mul_assoc] using hmul
    have hiM : i.1 ∈ M.field.toSubgroup := hInertia i hiI hiE
    have hzM : z.1 ∈ M.field.toSubgroup := by
      have hmul := M.field.toSubgroup.mul_mem hiM hizM'
      simpa [mul_assoc] using hmul
    exact hzM
  · intro x
    refine Quotient.inductionOn' x ?_
    intro k
    have hkDegree : D.degree k.1 ∈
        E.base.toSubgroup.map D.degree.toMonoidHom := ⟨k.1, k.2, rfl⟩
    obtain ⟨e, heE, heDegree⟩ :=
      (E.isTotallyRamified_iff_image_le D).1 hTot hkDegree
    let eE : E.field.toSubgroup := ⟨e, heE⟩
    let eK : E.base.toSubgroup := Subgroup.inclusion E.below eE
    let i : E.base.toSubgroup := k * eK⁻¹
    have hiI : i ∈ D.fieldInertiaWithin E.base := by
      change D.degree i.1 = 1
      dsimp [i, eK, eE]
      rw [map_mul, map_inv]
      change D.degree k.1 * (D.degree e)⁻¹ = 1
      change D.degree e = D.degree k.1 at heDegree
      rw [heDegree]
      simp
    have hiS : (QuotientGroup.mk'
        (M.field.toSubgroup.subgroupOf E.base.toSubgroup)) i ∈ S :=
      ⟨i, hiI, rfl⟩
    have hiP : i ∈ M.intermediateSubgroup S := hiS
    let iM₀ : M₀.toSubgroup := ⟨i.1, ⟨i, hiP, rfl⟩⟩
    refine ⟨QuotientGroup.mk iM₀, ?_⟩
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    change (i⁻¹ * k).1 ∈ E.field.toSubgroup
    simpa [i, eK, eE, mul_inv_rev, mul_assoc] using eE.2

/-- The equivalence induced by the totally ramified restriction coset
map ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/RestrictionCosets.lean:148`]
[Yamaguchi2026]). -/
def abstractReciprocityRestrictionCosetEquiv
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    (hTot : E.IsTotallyRamified D)
    (hInertia : ∀ i : E.base.toSubgroup,
      i ∈ D.fieldInertiaWithin E.base →
      i.1 ∈ E.field.toSubgroup → i.1 ∈ M.field.toSubgroup) :
    let M₀ := M.maximalUnramifiedSubextension D
    let _hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
      M.field_le_intermediateField (M.inertiaImage D)
    (M₀.toSubgroup ⧸ M.field.toSubgroup.subgroupOf M₀.toSubgroup) ≃
      E.quotient :=
  Equiv.ofBijective (M.abstractReciprocityRestrictionCosetMap D E hME)
    (M.abstractReciprocityRestrictionCosetMap_bijective
      D E hME hTot hInertia)

/-- **The multiplicative restriction equivalence from the lower Galois
group to the original totally ramified quotient** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/RestrictionCosets.lean:168`]
[Yamaguchi2026]). -/
def abstractReciprocityRestrictionMulEquiv
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    [hEnormal :
      (E.field.toSubgroup.subgroupOf E.base.toSubgroup).Normal]
    (hTot : E.IsTotallyRamified D)
    (hInertia : ∀ i : E.base.toSubgroup,
      i ∈ D.fieldInertiaWithin E.base →
      i.1 ∈ E.field.toSubgroup → i.1 ∈ M.field.toSubgroup) :
    let S := M.inertiaImage D
    let N := M.lowerFiniteGalois S
    letI : (M.field.toSubgroup.subgroupOf
        (M.maximalUnramifiedSubextension D).toSubgroup).Normal :=
      N.normal
    letI : Group E.quotient := by
      change Group
        (E.base.toSubgroup ⧸
          E.field.toSubgroup.subgroupOf E.base.toSubgroup)
      infer_instance
    N.extensionQuotient ≃*
      E.quotient := by
  let S := M.inertiaImage D
  let M₀ := M.maximalUnramifiedSubextension D
  let N := M.lowerFiniteGalois S
  let hM₀K : M₀.toSubgroup ≤ E.base.toSubgroup :=
    M.intermediateField_le_base S
  letI : (M.field.toSubgroup.subgroupOf M₀.toSubgroup).Normal := N.normal
  letI : Group E.quotient := by
    change Group
      (E.base.toSubgroup ⧸
        E.field.toSubgroup.subgroupOf E.base.toSubgroup)
    infer_instance
  let r : N.extensionQuotient →*
      E.quotient :=
    QuotientGroup.map
      (M.field.toSubgroup.subgroupOf M₀.toSubgroup)
      (E.field.toSubgroup.subgroupOf E.base.toSubgroup)
      (Subgroup.inclusion hM₀K)
      (by
        intro m hm
        exact hME hm)
  apply MulEquiv.ofBijective r
  have hr : (r : N.extensionQuotient →
      E.quotient) =
      M.abstractReciprocityRestrictionCosetMap D E hME := by
    funext x
    refine Quotient.inductionOn' x ?_
    intro m
    rfl
  rw [hr]
  exact M.abstractReciprocityRestrictionCosetMap_bijective
    D E hME hTot hInertia

/-- Relative coset actions are transported by the restriction coset
equivalence ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/RestrictionCosets.lean:223`]
[Yamaguchi2026]). -/
theorem relativeCosetAction_abstractReciprocityRestrictionCosetEquiv
    (A : Rep ℤ G) (D : DegreeData G) [IsTopologicalGroup G]
    (E : AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    (hTot : E.IsTotallyRamified D)
    (hInertia : ∀ i : E.base.toSubgroup,
      i ∈ D.fieldInertiaWithin E.base →
      i.1 ∈ E.field.toSubgroup → i.1 ∈ M.field.toSubgroup)
    (a : ambientFixedAddSubgroup A E.field)
    (r : let M₀ := M.maximalUnramifiedSubextension D
      let _hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
        M.field_le_intermediateField (M.inertiaImage D)
      M₀.toSubgroup ⧸ M.field.toSubgroup.subgroupOf M₀.toSubgroup) :
    let M₀ := M.maximalUnramifiedSubextension D
    let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
      M.field_le_intermediateField (M.inertiaImage D)
    relativeCosetAction A M₀ M.field hMM₀
        (fixedFieldInclusion A E.field M.field hME a) r =
      relativeCosetAction A E.base E.field E.below a
        (M.abstractReciprocityRestrictionCosetEquiv
          D E hME hTot hInertia r) := by
  let S := M.inertiaImage D
  let M₀ := M.maximalUnramifiedSubextension D
  let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
    M.field_le_intermediateField S
  let hM₀K : M₀.toSubgroup ≤ E.base.toSubgroup :=
    M.intermediateField_le_base S
  refine Quotient.inductionOn' r ?_
  intro x
  rfl

/-- **Relative norm commutes with fixed-field inclusion along the
totally ramified restriction equivalence** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/RestrictionCosets.lean:257`]
[Yamaguchi2026]). -/
theorem abstractReciprocity_relativeNorm_fixedFieldInclusion
    (A : Rep ℤ G) (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteAbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    (hTot : E.IsTotallyRamified D)
    (hInertia : ∀ i : E.base.toSubgroup,
      i ∈ D.fieldInertiaWithin E.base →
      i.1 ∈ E.field.toSubgroup → i.1 ∈ M.field.toSubgroup)
    (a : ambientFixedAddSubgroup A E.field) :
    let M₀ := M.maximalUnramifiedSubextension D
    let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
      M.field_le_intermediateField (M.inertiaImage D)
    let hM₀K : M₀.toSubgroup ≤ E.base.toSubgroup :=
      M.intermediateField_le_base (M.inertiaImage D)
    letI : Finite
        (M₀.toSubgroup ⧸ M.field.toSubgroup.subgroupOf M₀.toSubgroup) :=
      M.extension_over_intermediate_finite (M.inertiaImage D)
    relativeNorm A M₀ M.field hMM₀
        (fixedFieldInclusion A E.field M.field hME a) =
      fixedFieldInclusion A E.base M₀ hM₀K
        (relativeNorm A E.base E.field E.below a) := by
  let S := M.inertiaImage D
  let M₀ := M.maximalUnramifiedSubextension D
  let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
    M.field_le_intermediateField S
  let hM₀K : M₀.toSubgroup ≤ E.base.toSubgroup :=
    M.intermediateField_le_base S
  letI hMfinite : Finite
      (M₀.toSubgroup ⧸ M.field.toSubgroup.subgroupOf M₀.toSubgroup) :=
    M.extension_over_intermediate_finite S
  letI : Finite E.toAbstractExtension.quotient := by
    change Finite
      (E.base.toSubgroup ⧸
        E.field.toSubgroup.subgroupOf E.base.toSubgroup)
    exact E.finiteQuotient
  let e := M.abstractReciprocityRestrictionCosetEquiv
    D E.toAbstractExtension hME hTot hInertia
  apply Subtype.ext
  letI : Fintype
      (M₀.toSubgroup ⧸ M.field.toSubgroup.subgroupOf M₀.toSubgroup) :=
    Fintype.ofFinite _
  letI : Fintype
      (E.base.toSubgroup ⧸
        E.field.toSubgroup.subgroupOf E.base.toSubgroup) :=
    Fintype.ofFinite _
  letI : Fintype E.quotient :=
    Fintype.ofFinite _
  letI : Fintype E.toAbstractExtension.quotient :=
    Fintype.ofFinite _
  simp only [fixedFieldInclusion_coe, relativeNorm_apply_coe,
    relativeNormValue]
  calc
    ∑ r, relativeCosetAction A M₀ M.field hMM₀
        (fixedFieldInclusion A E.field M.field hME a) r =
      ∑ r, relativeCosetAction A E.base E.field E.below a (e r) := by
        apply Fintype.sum_congr
        intro r
        exact M.relativeCosetAction_abstractReciprocityRestrictionCosetEquiv
          A D E.toAbstractExtension hME hTot hInertia a r
    _ = ∑ q, relativeCosetAction A E.base E.field E.below a q :=
      e.sum_comp (relativeCosetAction A E.base E.field E.below a)

/-- Two auxiliary quotient elements commute when they have the same
restriction and the auxiliary field contains the inertia subgroup
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/RestrictionCosets.lean:320`]
[Yamaguchi2026]). -/
theorem commute_of_same_restriction_of_inertia_le
    (D : DegreeData G)
    (E : AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    (hIE : (D.fieldInertia E.field).toSubgroup ≤ M.field.toSubgroup)
    [hEnormal :
      (E.field.toSubgroup.subgroupOf E.base.toSubgroup).Normal]
    (g t : E.base.toSubgroup ⧸
      M.field.toSubgroup.subgroupOf E.base.toSubgroup)
    (hres : abstractReciprocityRestriction
        E.base E.field M.field hME E.below g =
      abstractReciprocityRestriction
        E.base E.field M.field hME E.below t) :
    Commute g t := by
  rw [Commute]
  let a : E.base.toSubgroup := Quotient.out g
  let b : E.base.toSubgroup := Quotient.out t
  have ha : (QuotientGroup.mk'
      (M.field.toSubgroup.subgroupOf E.base.toSubgroup)) a = g :=
    Quotient.out_eq' g
  have hb : (QuotientGroup.mk'
      (M.field.toSubgroup.subgroupOf E.base.toSubgroup)) b = t :=
    Quotient.out_eq' t
  have hcosetE :
      (QuotientGroup.mk'
        (E.field.toSubgroup.subgroupOf E.base.toSubgroup)) (a * b) =
      (QuotientGroup.mk'
        (E.field.toSubgroup.subgroupOf E.base.toSubgroup)) (b * a) := by
    rw [map_mul, map_mul]
    have haE : (QuotientGroup.mk'
        (E.field.toSubgroup.subgroupOf E.base.toSubgroup)) a =
        abstractReciprocityRestriction
          E.base E.field M.field hME E.below g := by
      calc
        (QuotientGroup.mk'
            (E.field.toSubgroup.subgroupOf E.base.toSubgroup)) a =
            abstractReciprocityRestriction E.base E.field M.field hME
              E.below
              ((QuotientGroup.mk'
                (M.field.toSubgroup.subgroupOf E.base.toSubgroup)) a) :=
          rfl
        _ = abstractReciprocityRestriction
            E.base E.field M.field hME E.below g :=
          congrArg (abstractReciprocityRestriction
            E.base E.field M.field hME E.below) ha
    have hbE : (QuotientGroup.mk'
        (E.field.toSubgroup.subgroupOf E.base.toSubgroup)) b =
        abstractReciprocityRestriction
          E.base E.field M.field hME E.below t := by
      calc
        (QuotientGroup.mk'
            (E.field.toSubgroup.subgroupOf E.base.toSubgroup)) b =
            abstractReciprocityRestriction E.base E.field M.field hME
              E.below
              ((QuotientGroup.mk'
                (M.field.toSubgroup.subgroupOf E.base.toSubgroup)) b) :=
          rfl
        _ = abstractReciprocityRestriction
            E.base E.field M.field hME E.below t :=
          congrArg (abstractReciprocityRestriction
            E.base E.field M.field hME E.below) hb
    rw [haE, hbE, hres]
  let z : E.base.toSubgroup := (a * b)⁻¹ * (b * a)
  have hzE : z ∈ E.field.toSubgroup.subgroupOf E.base.toSubgroup :=
    QuotientGroup.eq.mp hcosetE
  have hzE' : z.1 ∈ E.field.toSubgroup :=
    Subgroup.mem_subgroupOf.1 hzE
  have hzDegree : D.degree z.1 = 1 := by
    dsimp [z]
    rw [map_mul, map_inv, map_mul, map_mul]
    apply Multiplicative.ext
    change -((D.degree a.1).toAdd + (D.degree b.1).toAdd) +
        ((D.degree b.1).toAdd + (D.degree a.1).toAdd) = 0
    abel
  have hzM : z.1 ∈ M.field.toSubgroup :=
    hIE ⟨hzE', hzDegree⟩
  have hzH : z ∈ M.field.toSubgroup.subgroupOf E.base.toSubgroup :=
    Subgroup.mem_subgroupOf.2 hzM
  calc
    g * t = (QuotientGroup.mk'
        (M.field.toSubgroup.subgroupOf E.base.toSubgroup)) (a * b) := by
      rw [map_mul, ha, hb]
    _ = (QuotientGroup.mk'
        (M.field.toSubgroup.subgroupOf E.base.toSubgroup)) (b * a) :=
      QuotientGroup.eq.mpr hzH
    _ = t * g := by rw [map_mul, ha, hb]

/-- Equal restrictions induce equal relative coset actions on elements
fixed by the upper field ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/RestrictionCosets.lean:406`]
[Yamaguchi2026]). -/
theorem relativeCosetAction_eq_of_restriction_eq
    (A : Rep ℤ G) (E : AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    [hEnormal :
      (E.field.toSubgroup.subgroupOf E.base.toSubgroup).Normal]
    (a : ambientFixedAddSubgroup A E.field)
    (g t : E.base.toSubgroup ⧸
      M.field.toSubgroup.subgroupOf E.base.toSubgroup)
    (hres : abstractReciprocityRestriction
        E.base E.field M.field hME E.below g =
      abstractReciprocityRestriction
        E.base E.field M.field hME E.below t) :
    relativeCosetAction A E.base M.field M.below
        (fixedFieldInclusion A E.field M.field hME a) g =
      relativeCosetAction A E.base M.field M.below
        (fixedFieldInclusion A E.field M.field hME a) t := by
  refine Quotient.inductionOn₂' g t ?_ hres
  intro x y hxy
  simp only [relativeCosetAction_mk, fixedFieldInclusion_coe]
  have hxyE : x⁻¹ * y ∈ E.field.toSubgroup.subgroupOf E.base.toSubgroup :=
    QuotientGroup.eq.mp hxy
  let e : E.field.toSubgroup := ⟨(x⁻¹ * y).1, hxyE⟩
  have hy : y = x * Subgroup.inclusion E.below e := by
    apply Subtype.ext
    simp [e]
  rw [hy]
  change A.ρ x.1 a.1 = A.ρ (x.1 * e.1) a.1
  rw [map_mul]
  change A.ρ x.1 a.1 = A.ρ x.1 (A.ρ e.1 a.1)
  rw [a.2 e]

end FiniteGaloisSubextension

end

end Atlas.Knowledge
