import Mathlib
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractExtension
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.FiniteResidueAbstractField
import Atlas.Knowledge.IntermediateGaloisCorrespondence
import Atlas.Knowledge.ReductionGaloisArrows
import Atlas.Knowledge.TotallyRamifiedFrobeniusLift
import Atlas.Knowledge.TotallyRamifiedRestrictionCosets

/-!
# totally ramified restriction equivalence

The lower Galois group in the totally ramified auxiliary tower:
restriction identifies `G(M/M⁰)` with the original totally ramified
quotient `G(L/K)`, matching degrees, and transports the prescribed
generator of `G(L/K)` to a generator of `G(M/M⁰)` (#104).

## Main definitions

* `DegreeData.abstractReciprocityTotallyRamifiedRestrictionEquiv` —
  the identification `G(M/M⁰) ≃* G(L/K)`.

## Main statements

* `DegreeData.abstractReciprocityTotallyRamifiedLowerDegree_eq` — the
  lower extension's degree matches the original cyclic degree; proved.
* `DegreeData.abstractReciprocityTotallyRamifiedLowerGenerator_generates`
  — the constructed lower automorphism generates the cyclic quotient;
  proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
`extensionSubgroup_index_eq_degree` is the layer's
`subgroup_index_eq_degree`, the two `noncomputable def` keywords drop
under the file's `noncomputable section`, and the ambient group is
`Type u` where the source pins `IntegralRepGroupType`. All five
declarations shed the source's `[T2Space G]` — the cascade of the same
shed on the auxiliary-extension family in
`Atlas.Knowledge.TotallyRamifiedFrobeniusLift`: nothing here consumes
separation once that family stopped asking for it, and it is not
derivable from the kept instances, so the ported statements are
strictly more general. Everything else ports token-for-token; the file
is the source's `TotallyRamifiedCase/RestrictionEquiv.lean` whole.

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

/-- **Restriction identifies the actual lower Galois group `G(M/M⁰)`
with the original totally ramified group `G(L/K)`** (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/RestrictionEquiv.lean:25`). -/
def abstractReciprocityTotallyRamifiedRestrictionEquiv
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    let S := M.inertiaImage D
    let N := M.lowerFiniteGalois S
    letI : (M.field.toSubgroup.subgroupOf
        (M.maximalUnramifiedSubextension D).toSubgroup).Normal :=
      N.normal
    N.extensionQuotient ≃* L.extensionQuotient := by
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  let hML := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
    K L hTot q
  have hInertia : ∀ i : K.field.toSubgroup,
      i ∈ D.fieldInertiaWithin K.field →
      i.1 ∈ L.field.toSubgroup → i.1 ∈ M.field.toSubgroup := by
    intro i hiI hiL
    apply
      D.maximalUnramifiedField_le_abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    exact ⟨hiL, (D.mem_fieldInertiaWithin_iff K.field i).1 hiI⟩
  letI : (L.field.toSubgroup.subgroupOf K.field.toSubgroup).Normal :=
    L.normal
  let EL := L.toFiniteAbstractExtension.toAbstractExtension
  letI : (EL.field.toSubgroup.subgroupOf EL.base.toSubgroup).Normal := by
    change (L.field.toSubgroup.subgroupOf K.field.toSubgroup).Normal
    exact L.normal
  letI : Group EL.quotient := by
    change Group
      (K.field.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.field.toSubgroup)
    infer_instance
  exact (M.abstractReciprocityRestrictionMulEquiv
    D EL
      hML hTot hInertia).trans
      L.extensionQuotientMulEquiv.symm

/-- **Restriction identifies the degree of the totally ramified lower
extension `M/M⁰` with the original cyclic degree `[L:K]`**
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/RestrictionEquiv.lean:67`). -/
theorem abstractReciprocityTotallyRamifiedLowerDegree_eq
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  let N := M.lowerFiniteGalois (M.inertiaImage D)
  (N.toFiniteAbstractExtension.degree : ℕ) =
    (L.toFiniteAbstractExtension.degree : ℕ) := by
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  let S := M.inertiaImage D
  let M₀ := M.maximalUnramifiedSubextension D
  let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
    M.field_le_intermediateField S
  let N := M.lowerFiniteGalois S
  let E := L.toFiniteAbstractExtension
  let e := D.abstractReciprocityTotallyRamifiedRestrictionEquiv
    K L hTot q
  calc
    (N.toFiniteAbstractExtension.degree : ℕ) =
        (M.field.toSubgroup.subgroupOf M₀.toSubgroup).index :=
      N.toFiniteAbstractExtension.subgroup_index_eq_degree.symm
    _ = Nat.card N.extensionQuotient :=
      Subgroup.index_eq_card (M.field.toSubgroup.subgroupOf M₀.toSubgroup)
    _ = Nat.card L.extensionQuotient :=
      Nat.card_congr e.toEquiv
    _ = (L.field.toSubgroup.subgroupOf K.field.toSubgroup).index :=
      (Subgroup.index_eq_card
        (L.field.toSubgroup.subgroupOf K.field.toSubgroup)).symm
    _ = (E.degree : ℕ) := by
      have h := E.subgroup_index_eq_degree
      change (L.field.toSubgroup.subgroupOf K.field.toSubgroup).index =
        (E.degree : ℕ) at h
      exact h

/-- The generator of `G(M/M⁰)` corresponding to the prescribed
generator of `G(L/K)` (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/RestrictionEquiv.lean:107`). -/
def abstractReciprocityTotallyRamifiedLowerGenerator
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    let S := M.inertiaImage D
    let N := M.lowerFiniteGalois S
    letI : (M.field.toSubgroup.subgroupOf
        (M.maximalUnramifiedSubextension D).toSubgroup).Normal :=
      N.normal
    N.extensionQuotient := by
  exact (D.abstractReciprocityTotallyRamifiedRestrictionEquiv
    K L hTot q).symm q

/-- The restriction equivalence sends the constructed lower generator
to the target generator (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/RestrictionEquiv.lean:127`). -/
@[simp]
theorem abstractReciprocityTotallyRamifiedRestrictionEquiv_lowerGenerator
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    D.abstractReciprocityTotallyRamifiedRestrictionEquiv K L hTot q
      (D.abstractReciprocityTotallyRamifiedLowerGenerator
        K L hTot q) = q := by
  exact MulEquiv.apply_symm_apply _ q

/-- **The constructed lower automorphism generates the relevant cyclic
quotient** (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/RestrictionEquiv.lean:140`). -/
theorem abstractReciprocityTotallyRamifiedLowerGenerator_generates
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient)
    (hq : ∀ x, x ∈ Subgroup.zpowers q) :
    ∀ x, x ∈ Subgroup.zpowers
      (D.abstractReciprocityTotallyRamifiedLowerGenerator
        K L hTot q) := by
  let e := D.abstractReciprocityTotallyRamifiedRestrictionEquiv
    K L hTot q
  let g := D.abstractReciprocityTotallyRamifiedLowerGenerator
    K L hTot q
  intro x
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hq (e x))
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨n, ?_⟩
  apply e.injective
  rw [map_zpow,
    D.abstractReciprocityTotallyRamifiedRestrictionEquiv_lowerGenerator, hn]

end DegreeData

end

end Atlas.Knowledge
