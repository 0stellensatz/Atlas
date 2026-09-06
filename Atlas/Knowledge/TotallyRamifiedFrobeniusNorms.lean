import Mathlib
import Atlas.Knowledge.AbstractExtension
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractExtension
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.FiniteResidueAbstractField
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusExponent
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.FrobeniusFixedField
import Atlas.Knowledge.IntermediateGaloisCorrespondence
import Atlas.Knowledge.ReciprocityExactRows
import Atlas.Knowledge.ReductionGaloisArrows
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.TotallyRamifiedFrobeniusLift
import Atlas.Knowledge.TotallyRamifiedRestrictionCosets
import Atlas.Knowledge.TotallyRamifiedRestrictionEquiv

/-!
# totally ramified Frobenius norms

Frobenius actions and relative norms in the totally ramified auxiliary
tower: the Frobenius element `σ̃|_M` of the auxiliary quotient `G(M/K)`
with its restriction identity, the commutation of the lower cyclic
generator with it, the fixing of `A_Σ` under its action, the agreement
of the two constructed actions on `A_L`, and the two norm restrictions
`N_{M/M⁰}|_{A_L} = N_{L/K}` and `N_{M/M⁰}|_{A_Σ} = N_{Σ/K}` inside the
actual fixed group `A_{M⁰}` (#104).

## Main definitions

* `DegreeData.abstractReciprocityTotallyRamifiedFrobeniusInM` — the
  restriction `σ̃|_M` in the auxiliary quotient.

## Main statements

* `DegreeData.abstractReciprocityTotallyRamified_generator_commutes_frobenius`
  — the lower cyclic generator commutes with the selected Frobenius
  element; proved.
* `DegreeData.abstractReciprocity_totallyRamified_relativeNorm_L` — the
  first norm restriction, `N_{M/M⁰}|_{A_L} = N_{L/K}`; proved.
* `DegreeData.abstractReciprocity_totallyRamified_relativeNorm_sigma` —
  the second norm restriction, `N_{M/M⁰}|_{A_Σ} = N_{Σ/K}`; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling, so
`mem_extensionSubgroup_iff` becomes Mathlib's
`Subgroup.mem_subgroupOf`; `DegreeData.AbstractExtension` and
`DegreeData.FiniteAbstractExtension.ofInclusion` are the layer's
top-level `AbstractExtension` and
`FiniteAbstractExtension.ofInclusion`; the one `noncomputable def`
keyword drops under the file's `noncomputable section`; and the ambient
group is `Type u` where the source pins `IntegralRepGroupType`. All
eight declarations shed the source's `[T2Space G]` — the continuing
cascade of the same shed in
`Atlas.Knowledge.TotallyRamifiedFrobeniusLift` — and the second norm
restriction keeps the source's `[TotallyDisconnectedSpace G]`, which
`frobeniusFixedField_fieldInertia` consumes — the totally disconnected
topological group synthesizes the separation that lemma asks for.
Everything else ports token-for-token; the file is the source's
`TotallyRamifiedCase/FrobeniusNorms.lean` whole.

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

/-- **The restriction `σ̃|_M`, an element of the actual upper quotient
`G(M/K)`** (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusNorms.lean:24`). -/
def abstractReciprocityTotallyRamifiedFrobeniusInM
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    (D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q).extensionQuotient := by
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    K L hTot q
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  letI : (M.field.toSubgroup.subgroupOf K.field.toSubgroup).Normal :=
    M.normal
  have hIM : D.extensionInertiaWithin K.field L.field L.below ≤
      M.field.toSubgroup.subgroupOf K.field.toSubgroup := by
    intro x hx
    apply Subgroup.mem_subgroupOf.2
    apply
      D.maximalUnramifiedField_le_abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    exact ⟨Subgroup.mem_subgroupOf.1 hx.1,
      (D.mem_fieldInertiaWithin_iff K.field x).1 hx.2⟩
  let r : (K.field.toSubgroup ⧸
      D.extensionInertiaWithin K.field L.field L.below) →*
      (K.field.toSubgroup ⧸
        M.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
    QuotientGroup.map
      (D.extensionInertiaWithin K.field L.field L.below)
      (M.field.toSubgroup.subgroupOf K.field.toSubgroup)
      (MonoidHom.id K.field.toSubgroup) hIM
  exact M.extensionQuotientMulEquiv.symm (r σ.1)

/-- The Frobenius chosen in the auxiliary field has the expected
restriction (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusNorms.lean:58`). -/
@[simp]
theorem abstractReciprocityTotallyRamifiedFrobeniusInM_restriction
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    let hML := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
      K L hTot q
    M.bundledRestrictionHom L hML
      (D.abstractReciprocityTotallyRamifiedFrobeniusInM
        K L hTot q) = q := by
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    K L hTot q
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  let hML := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
    K L hTot q
  letI : (M.field.toSubgroup.subgroupOf K.field.toSubgroup).Normal :=
    M.normal
  have hIM : D.extensionInertiaWithin K.field L.field L.below ≤
      M.field.toSubgroup.subgroupOf K.field.toSubgroup := by
    intro x hx
    apply Subgroup.mem_subgroupOf.2
    apply
      D.maximalUnramifiedField_le_abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    exact ⟨Subgroup.mem_subgroupOf.1 hx.1,
      (D.mem_fieldInertiaWithin_iff K.field x).1 hx.2⟩
  let r : (K.field.toSubgroup ⧸
      D.extensionInertiaWithin K.field L.field L.below) →*
      (K.field.toSubgroup ⧸
        M.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
    QuotientGroup.map
      (D.extensionInertiaWithin K.field L.field L.below)
      (M.field.toSubgroup.subgroupOf K.field.toSubgroup)
      (MonoidHom.id K.field.toSubgroup) hIM
  change L.extensionQuotientMulEquiv.symm
      (abstractReciprocityRestriction K.field L.field M.field hML L.below
        (r σ.1)) = q
  apply L.extensionQuotientMulEquiv.injective
  rw [MulEquiv.apply_symm_apply]
  have hcompat : ∀ z : K.field.toSubgroup ⧸
      D.extensionInertiaWithin K.field L.field L.below,
      abstractReciprocityRestriction K.field L.field M.field hML L.below
          (r z) =
        D.extensionRestriction K.field L.field L.below z := by
    intro z
    refine Quotient.inductionOn' z ?_
    intro x
    rfl
  rw [hcompat]
  exact
    D.frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified_underlying
    K L hTot q

/-- Including the lower generator and then restricting recovers its
prescribed action (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusNorms.lean:114`). -/
@[simp]
theorem abstractReciprocityTotallyRamifiedLowerGenerator_inclusion_restriction
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    let S := M.inertiaImage D
    let hML := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
      K L hTot q
    M.bundledRestrictionHom L hML
      (M.lowerInclusionHom S
        (D.abstractReciprocityTotallyRamifiedLowerGenerator
          K L hTot q)) = q := by
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  let S := M.inertiaImage D
  let hML := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
    K L hTot q
  let e := D.abstractReciprocityTotallyRamifiedRestrictionEquiv
    K L hTot q
  let g := D.abstractReciprocityTotallyRamifiedLowerGenerator
    K L hTot q
  change M.bundledRestrictionHom L hML
      (M.lowerInclusionHom S g) = q
  have hcompat : ∀ x,
      M.bundledRestrictionHom L hML
        (M.lowerInclusionHom S x) = e x := by
    intro x
    refine Quotient.inductionOn' x ?_
    intro m
    rw [M.lowerInclusionHom_mk S m]
    dsimp [e, abstractReciprocityTotallyRamifiedRestrictionEquiv]
    rfl
  rw [hcompat]
  exact D.abstractReciprocityTotallyRamifiedRestrictionEquiv_lowerGenerator
    K L hTot q

/-- **The lower cyclic generator commutes with the selected Frobenius
element** (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusNorms.lean:155`). -/
theorem abstractReciprocityTotallyRamified_generator_commutes_frobenius
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    let S := M.inertiaImage D
    Commute
      (M.lowerInclusionHom S
        (D.abstractReciprocityTotallyRamifiedLowerGenerator
          K L hTot q))
      (D.abstractReciprocityTotallyRamifiedFrobeniusInM
        K L hTot q) := by
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  let S := M.inertiaImage D
  let hML := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
    K L hTot q
  let g := D.abstractReciprocityTotallyRamifiedLowerGenerator
    K L hTot q
  let t := D.abstractReciprocityTotallyRamifiedFrobeniusInM
    K L hTot q
  let EL : AbstractExtension G := {
    field := L.field
    base := K.field
    below := L.below }
  letI : (EL.field.toSubgroup.subgroupOf EL.base.toSubgroup).Normal := by
    change (L.field.toSubgroup.subgroupOf K.field.toSubgroup).Normal
    exact L.normal
  have hresBundled :
      M.bundledRestrictionHom L hML (M.lowerInclusionHom S g) =
        M.bundledRestrictionHom L hML t := by
    rw [D.abstractReciprocityTotallyRamifiedLowerGenerator_inclusion_restriction,
      D.abstractReciprocityTotallyRamifiedFrobeniusInM_restriction]
  have hresRaw :
      abstractReciprocityRestriction K.field L.field M.field hML L.below
          (M.extensionQuotientMulEquiv (M.lowerInclusionHom S g)) =
        abstractReciprocityRestriction K.field L.field M.field hML L.below
          (M.extensionQuotientMulEquiv t) := by
    apply L.extensionQuotientMulEquiv.symm.injective
    simpa [FiniteGaloisSubextension.bundledRestrictionHom] using hresBundled
  have hcommRaw := M.commute_of_same_restriction_of_inertia_le
    D EL hML
    (D.maximalUnramifiedField_le_abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q)
    (M.extensionQuotientMulEquiv (M.lowerInclusionHom S g))
    (M.extensionQuotientMulEquiv t) hresRaw
  rw [Commute]
  apply M.extensionQuotientMulEquiv.injective
  simpa only [map_mul] using hcommRaw.eq

/-- Frobenius fixes the automorphism used in the totally ramified
construction (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusNorms.lean:210`). -/
theorem abstractReciprocityTotallyRamified_frobenius_fixes_sigma
    (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L.field L.below
        (D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
          K L hTot q))) :
    let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
      K L hTot q
    let Sigma := D.frobeniusFixedField K L.field L.below σ
    let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    let hMSigma :=
      D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_sigma
        K L hTot q
    relativeCosetAction A K.field M.field M.below
        (fixedFieldInclusion A Sigma M.field hMSigma a)
        (M.extensionQuotientMulEquiv
          (D.abstractReciprocityTotallyRamifiedFrobeniusInM
            K L hTot q)) =
      (fixedFieldInclusion A Sigma M.field hMSigma a).1 := by
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    K L hTot q
  let Sigma := D.frobeniusFixedField K L.field L.below σ
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  let hMSigma :=
    D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_sigma
      K L hTot q
  letI : (M.field.toSubgroup.subgroupOf K.field.toSubgroup).Normal :=
    M.normal
  have hIM : D.extensionInertiaWithin K.field L.field L.below ≤
      M.field.toSubgroup.subgroupOf K.field.toSubgroup := by
    intro x hx
    apply Subgroup.mem_subgroupOf.2
    apply
      D.maximalUnramifiedField_le_abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    exact ⟨Subgroup.mem_subgroupOf.1 hx.1,
      (D.mem_fieldInertiaWithin_iff K.field x).1 hx.2⟩
  let r : (K.field.toSubgroup ⧸
      D.extensionInertiaWithin K.field L.field L.below) →*
      (K.field.toSubgroup ⧸
        M.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
    QuotientGroup.map
      (D.extensionInertiaWithin K.field L.field L.below)
      (M.field.toSubgroup.subgroupOf K.field.toSubgroup)
      (MonoidHom.id K.field.toSubgroup) hIM
  change relativeCosetAction A K.field M.field M.below
      (fixedFieldInclusion A Sigma M.field hMSigma a) (r σ.1) = _
  let x : K.field.toSubgroup := Quotient.out σ.1
  have hx : (QuotientGroup.mk x :
      K.field.toSubgroup ⧸
        D.extensionInertiaWithin K.field L.field L.below) = σ.1 :=
    Quotient.out_eq' σ.1
  rw [← hx]
  change A.ρ x.1 a.1 = a.1
  have hxClosure : (QuotientGroup.mk x :
      K.field.toSubgroup ⧸
        D.extensionInertiaWithin K.field L.field L.below) ∈
      (D.frobeniusClosure K L.field L.below σ).toSubgroup := by
    rw [hx]
    exact (D.frobeniusInClosure K L.field L.below σ).2
  let xSigma : Sigma.toSubgroup :=
    ⟨x.1, ⟨x, hxClosure, rfl⟩⟩
  exact a.2 xSigma

/-- The two constructed automorphisms induce the same action on the
extension field (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusNorms.lean:280`). -/
theorem abstractReciprocityTotallyRamified_actions_agree_on_L
    (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient)
    (a : ambientFixedAddSubgroup A L.field) :
    let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    let S := M.inertiaImage D
    let hML := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
      K L hTot q
    relativeCosetAction A K.field M.field M.below
        (fixedFieldInclusion A L.field M.field hML a)
        (M.extensionQuotientMulEquiv
          (M.lowerInclusionHom S
            (D.abstractReciprocityTotallyRamifiedLowerGenerator
              K L hTot q))) =
      relativeCosetAction A K.field M.field M.below
        (fixedFieldInclusion A L.field M.field hML a)
        (M.extensionQuotientMulEquiv
          (D.abstractReciprocityTotallyRamifiedFrobeniusInM
            K L hTot q)) := by
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  let S := M.inertiaImage D
  let hML := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
    K L hTot q
  let EL : AbstractExtension G := {
    field := L.field
    base := K.field
    below := L.below }
  letI : (EL.field.toSubgroup.subgroupOf EL.base.toSubgroup).Normal := by
    change (L.field.toSubgroup.subgroupOf K.field.toSubgroup).Normal
    exact L.normal
  apply M.relativeCosetAction_eq_of_restriction_eq A EL hML
  apply L.extensionQuotientMulEquiv.symm.injective
  simpa [FiniteGaloisSubextension.bundledRestrictionHom] using
    (show M.bundledRestrictionHom L hML
        (M.lowerInclusionHom S
          (D.abstractReciprocityTotallyRamifiedLowerGenerator
            K L hTot q)) =
      M.bundledRestrictionHom L hML
        (D.abstractReciprocityTotallyRamifiedFrobeniusInM
          K L hTot q) by
      rw [D.abstractReciprocityTotallyRamifiedLowerGenerator_inclusion_restriction,
        D.abstractReciprocityTotallyRamifiedFrobeniusInM_restriction])

/-- **The first norm restriction used: `N_{M/M⁰}|_{A_L} = N_{L/K}`,
with both sides included in `A_{M⁰}`** (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusNorms.lean:331`). -/
theorem abstractReciprocity_totallyRamified_relativeNorm_L
    (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient)
    (a : ambientFixedAddSubgroup A L.field) :
    let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    let M₀ := M.maximalUnramifiedSubextension D
    let hML := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
      K L hTot q
    let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
      M.field_le_intermediateField (M.inertiaImage D)
    let hM₀K : M₀.toSubgroup ≤ K.field.toSubgroup :=
      M.intermediateField_le_base (M.inertiaImage D)
    letI : Finite
        (K.field.toSubgroup ⧸
          L.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
      L.finite
    letI : Finite
        (M₀.toSubgroup ⧸ M.field.toSubgroup.subgroupOf M₀.toSubgroup) :=
      M.extension_over_intermediate_finite (M.inertiaImage D)
    relativeNorm A M₀ M.field hMM₀
        (fixedFieldInclusion A L.field M.field hML a) =
      fixedFieldInclusion A K.field M₀ hM₀K
        (relativeNorm A K.field L.field L.below a) := by
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  let hML := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
    K L hTot q
  letI : Finite
      (K.field.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
    L.finite
  have hInertia : ∀ i : K.field.toSubgroup,
      i ∈ D.fieldInertiaWithin K.field →
      i.1 ∈ L.field.toSubgroup → i.1 ∈ M.field.toSubgroup := by
    intro i hiI hiL
    apply
      D.maximalUnramifiedField_le_abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    exact ⟨hiL, (D.mem_fieldInertiaWithin_iff K.field i).1 hiI⟩
  exact M.abstractReciprocity_relativeNorm_fixedFieldInclusion
    A D L.toFiniteAbstractExtension hML hTot hInertia a

/-- **The second norm restriction used: `N_{M/M⁰}|_{A_Σ} = N_{Σ/K}`,
again in the actual fixed group `A_{M⁰}`** (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusNorms.lean:378`). -/
theorem abstractReciprocity_totallyRamified_relativeNorm_sigma
    (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L.field L.below
        (D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
          K L hTot q))) :
    letI : Finite
        (K.field.toSubgroup ⧸
          L.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
      L.finite
    let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
      K L hTot q
    let Sigma := D.frobeniusFixedField K L.field L.below σ
    let hSigmaK := D.frobeniusFixedField_le K L.field L.below σ
    letI : Finite
        (K.field.toSubgroup ⧸
          Sigma.toSubgroup.subgroupOf K.field.toSubgroup) :=
      D.frobeniusFixedField_finite K L.field L.below σ
    let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    let M₀ := M.maximalUnramifiedSubextension D
    let hMSigma :=
      D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_sigma
        K L hTot q
    let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
      M.field_le_intermediateField (M.inertiaImage D)
    let hM₀K : M₀.toSubgroup ≤ K.field.toSubgroup :=
      M.intermediateField_le_base (M.inertiaImage D)
    letI : Finite
        (M₀.toSubgroup ⧸ M.field.toSubgroup.subgroupOf M₀.toSubgroup) :=
      M.extension_over_intermediate_finite (M.inertiaImage D)
    relativeNorm A M₀ M.field hMM₀
        (fixedFieldInclusion A Sigma M.field hMSigma a) =
      fixedFieldInclusion A K.field M₀ hM₀K
        (relativeNorm A K.field Sigma hSigmaK a) := by
  letI : Finite
      (K.field.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
    L.finite
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    K L hTot q
  let Sigma := D.frobeniusFixedField K L.field L.below σ
  let hSigmaK := D.frobeniusFixedField_le K L.field L.below σ
  letI hSigmaFinite : Finite
      (K.field.toSubgroup ⧸
        Sigma.toSubgroup.subgroupOf K.field.toSubgroup) :=
    D.frobeniusFixedField_finite K L.field L.below σ
  let ESigma : FiniteAbstractExtension G :=
    FiniteAbstractExtension.ofInclusion Sigma K.field hSigmaK
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  let hMSigma :=
    D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_sigma
      K L hTot q
  have hSigmaTot : ESigma.IsTotallyRamified D := by
    have hrelative : (ESigma.residueDegree D : ℕ) = 1 := by
      calc
        (ESigma.residueDegree D : ℕ) =
            D.frobeniusExponent K L.field L.below σ :=
          D.frobeniusFixedField_residueDegreeOverBase K L.field L.below σ
        _ = 1 :=
          D.frobeniusExponent_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
            K L hTot q
    exact ESigma.isTotallyRamified_of_residueDegree_eq_one D hrelative
  have hInertia : ∀ i : K.field.toSubgroup,
      i ∈ D.fieldInertiaWithin K.field →
      i.1 ∈ Sigma.toSubgroup → i.1 ∈ M.field.toSubgroup := by
    intro i hiI hiSigma
    apply
      D.maximalUnramifiedField_le_abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    have hiSigmaInertia :
        i.1 ∈ (D.fieldInertia Sigma).toSubgroup :=
      ⟨hiSigma, (D.mem_fieldInertiaWithin_iff K.field i).1 hiI⟩
    rw [D.frobeniusFixedField_fieldInertia
      K L.field L.below σ] at hiSigmaInertia
    exact hiSigmaInertia
  exact M.abstractReciprocity_relativeNorm_fixedFieldInclusion
    A D ESigma hMSigma hSigmaTot hInertia a

end DegreeData

end

end Atlas.Knowledge
