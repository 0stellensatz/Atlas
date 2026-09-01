import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.ChosenPrimeElement
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteAbstractFieldExtension
import Atlas.Knowledge.FiniteFieldUnitMaps
import Atlas.Knowledge.FiniteIntermediateCompositum
import Atlas.Knowledge.FiniteIntermediateFieldRefinement
import Atlas.Knowledge.FiniteResidueAbstractField
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.FrobeniusQuotientAction
import Atlas.Knowledge.InfiniteUnitDescent
import Atlas.Knowledge.MaximalUnramifiedField
import Atlas.Knowledge.PrimeElement
import Atlas.Knowledge.ReciprocityMap
import Atlas.Knowledge.RelativeNormLaws
import Atlas.Knowledge.UnitRepresentation
import Atlas.Knowledge.ValuationData

/-!
# Prime unit differences

Differences of Frobenius fixed-field primes come from finite-stage
units: two primes differ by a unit at their finite compositum, which is
unramified over both fixed fields, and a prime differs from any Galois
translate of itself by a unit at a Galois refinement of its fixed
field's stage (#104).

## Main statements

* `DegreeData.frobeniusPrimeDifference_mem_infiniteUnitAddSubgroup` —
  two primes differ by a finite-stage unit; proved.
* `DegreeData.frobeniusPrime_actionDifference_mem_infiniteUnitAddSubgroup`
  — a prime and its translate differ by a finite-stage unit; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling, the
enrichment bridges are plain definitionally-equal terms for the source's
`simpa` bridges, the finiteness of a tower stage is #136's two-argument
instance-supplied form, the ambient group is `Type` after the chain, the
statements' enrichment binders synthesize through the transport
instances of `Atlas.Knowledge.FiniteFieldUnitMaps`, and the two
instance-derivable Hausdorff binders go. The citations name this file by
bare basename; it lives at
`AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/`
in the source. The source's no-op opens go.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **Two primes from Frobenius fixed fields differ by a finite-stage
unit after inclusion in `A_{L̃}`** — the common stage is their finite
compositum, unramified over both fixed fields
([Yamaguchi 2026, `PrimeUnitDifferences.lean:28`]
[Yamaguchi2026]). -/
theorem frobeniusPrimeDifference_mem_infiniteUnitAddSubgroup
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ τ : D.FrobeniusElements
      (K.toFiniteResidueAbstractField D) L hLK)
    (πσ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ))
    (πτ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK τ))
    (hπσ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ,
          D.frobeniusFixedField_absoluteFinite K L hLK σ⟩
      v.IsPrimeElement Sigma πσ)
    (hπτ :
      let KR := K.toFiniteResidueAbstractField D
      let Tau : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK τ,
          D.frobeniusFixedField_absoluteFinite K L hLK τ⟩
      v.IsPrimeElement Tau πτ) :
    let KR := K.toFiniteResidueAbstractField D
    let E := D.maximalUnramifiedField L
    let pσ := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK σ) E
      (D.fieldInertia_le_frobeniusFixedField KR L hLK σ) πσ
    let pτ := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK τ) E
      (D.fieldInertia_le_frobeniusFixedField KR L hLK τ) πτ
    pσ - pτ ∈ v.infiniteUnitAddSubgroup E K
      (D.maximalUnramifiedField_le_of_le hLK) := by
  dsimp only
  let KR := K.toFiniteResidueAbstractField D
  letI hLnormalKR : (L.toSubgroup.subgroupOf KR.field.toSubgroup).Normal :=
    hLnormal
  letI hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸ L.toSubgroup.subgroupOf KR.field.toSubgroup) :=
    hLfinite
  let E := D.maximalUnramifiedField L
  let S := D.frobeniusFixedField KR L hLK σ
  let T := D.frobeniusFixedField KR L hLK τ
  let hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le KR L hLK σ
  let hTK : T.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le KR L hLK τ
  let M := D.frobeniusFixedIntermediateField KR L hLK σ
  let N := D.frobeniusFixedIntermediateField KR L hLK τ
  let P := M.compositum N
  let hPS : P.field.toSubgroup ≤ S.toSubgroup :=
    M.compositum_le_left N
  let hPT : P.field.toSubgroup ≤ T.toSubgroup :=
    M.compositum_le_right N
  letI hSabsolute : Finite ((baseField G).toSubgroup ⧸
      S.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ
  letI hTabsolute : Finite ((baseField G).toSubgroup ⧸
      T.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    D.frobeniusFixedField_absoluteFinite K L hLK τ
  let Sigma : FiniteAbstractField G := ⟨S, hSabsolute⟩
  let Tau : FiniteAbstractField G := ⟨T, hTabsolute⟩
  letI hPfinite : Finite
      (K.field.toSubgroup ⧸ P.field.toSubgroup.subgroupOf K.field.toSubgroup) := P.finite
  let Pi : FiniteAbstractField G := P.toFiniteAbstractField K
  letI hPSfinite : Finite
      (S.toSubgroup ⧸ P.field.toSubgroup.subgroupOf S.toSubgroup) :=
    FiniteIntermediateField.finite_extension_of_le hSK hPS
  letI hPTfinite : Finite
      (T.toSubgroup ⧸ P.field.toSubgroup.subgroupOf T.toSubgroup) :=
    FiniteIntermediateField.finite_extension_of_le hTK hPT
  let EPS : FiniteAbstractFieldExtension G :=
    { field := Pi
      base := Sigma
      below := hPS
      finiteQuotient := hPSfinite }
  let EPT : FiniteAbstractFieldExtension G :=
    { field := Pi
      base := Tau
      below := hPT
      finiteQuotient := hPTfinite }
  have hPSunramified :
      EPS.IsUnramified D := by
    change D.fieldInertia S ≤ P.field.toSubgroup
    have hSI : D.fieldInertia S = D.fieldInertia L := by
      simpa [S] using
        D.frobeniusFixedField_fieldInertia KR L hLK σ
    rw [hSI]
    exact P.above
  have hPTunramified :
      EPT.IsUnramified D := by
    change D.fieldInertia T ≤ P.field.toSubgroup
    have hTI : D.fieldInertia T = D.fieldInertia L := by
      simpa [T] using
        D.frobeniusFixedField_fieldInertia KR L hLK τ
    rw [hTI]
    exact P.above
  let πσP := fixedFieldInclusion A S P.field hPS πσ
  let πτP := fixedFieldInclusion A T P.field hPT πτ
  have hπσP : v.IsPrimeElement Pi πσP := by
    exact v.prime_of_unramified EPS hPSunramified πσ hπσ
  have hπτP : v.IsPrimeElement Pi πτP := by
    exact v.prime_of_unramified EPT hPTunramified πτ hπτ
  let uP : v.unitAddSubgroup Pi :=
    ⟨πσP - πτP,
      v.sub_mem_unitAddSubgroup_of_prime Pi hπτP hπσP⟩
  rw [v.mem_infiniteUnitAddSubgroup_iff]
  refine ⟨P, uP, ?_⟩
  apply Subtype.ext
  rfl

/-- **The difference between a prime and any `G(L̃/K)`-translate of it is
a finite-stage unit** — a finite Galois refinement of the prime's fixed
field supplies a stage stable under the chosen representative
([Yamaguchi 2026, `PrimeUnitDifferences.lean:146`]
[Yamaguchi2026]). -/
theorem frobeniusPrime_actionDifference_mem_infiniteUnitAddSubgroup
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ))
    (hπ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ,
          D.frobeniusFixedField_absoluteFinite K L hLK σ⟩
      v.IsPrimeElement Sigma π)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) :
    let KR := K.toFiniteResidueAbstractField D
    let E := D.maximalUnramifiedField L
    let p := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK σ) E
      (D.fieldInertia_le_frobeniusFixedField KR L hLK σ) π
    p - D.frobeniusQuotientAction A K.field L hLK q p ∈
      v.infiniteUnitAddSubgroup E K
        (D.maximalUnramifiedField_le_of_le hLK) := by
  dsimp only
  let KR := K.toFiniteResidueAbstractField D
  letI hLnormalKR : (L.toSubgroup.subgroupOf KR.field.toSubgroup).Normal :=
    hLnormal
  letI hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸ L.toSubgroup.subgroupOf KR.field.toSubgroup) :=
    hLfinite
  let E := D.maximalUnramifiedField L
  let S := D.frobeniusFixedField KR L hLK σ
  let hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le KR L hLK σ
  let M := D.frobeniusFixedIntermediateField KR L hLK σ
  letI hEnormal : (E.toSubgroup.subgroupOf K.field.toSubgroup).Normal :=
    D.subgroupOf_maximalUnramifiedField_normal K.field L hLK
  let P := M.galoisRefinement
  let hPS : P.field.toSubgroup ≤ S.toSubgroup :=
    M.galoisRefinement_le_field
  letI hSabsolute : Finite ((baseField G).toSubgroup ⧸
      S.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ
  let Sigma : FiniteAbstractField G := ⟨S, hSabsolute⟩
  letI hPfinite : Finite
      (K.field.toSubgroup ⧸ P.field.toSubgroup.subgroupOf K.field.toSubgroup) := P.finite
  let Pi : FiniteAbstractField G := P.toFiniteAbstractField K
  letI hPSfinite : Finite
      (S.toSubgroup ⧸ P.field.toSubgroup.subgroupOf S.toSubgroup) :=
    FiniteIntermediateField.finite_extension_of_le hSK hPS
  letI hPnormal : (P.field.toSubgroup.subgroupOf K.field.toSubgroup).Normal := by
    exact FiniteIntermediateField.galoisRefinement_normal M
  let EPS : FiniteAbstractFieldExtension G :=
    { field := Pi
      base := Sigma
      below := hPS
      finiteQuotient := hPSfinite }
  let EPK : FiniteAbstractFieldExtension G :=
    { field := Pi
      base := K
      below := P.below
      finiteQuotient := hPfinite }
  have hPSunramified :
      EPS.IsUnramified D := by
    change D.fieldInertia S ≤ P.field.toSubgroup
    have hSI : D.fieldInertia S = D.fieldInertia L := by
      simpa [S] using
        D.frobeniusFixedField_fieldInertia KR L hLK σ
    rw [hSI]
    exact P.above
  let πP := fixedFieldInclusion A S P.field hPS π
  have hπP : v.IsPrimeElement Pi πP := by
    exact v.prime_of_unramified EPS hPSunramified π hπ
  let k : K.field.toSubgroup := Quotient.out q
  let πqP := normalExtensionAction A K.field P.field P.below hPnormal k πP
  have hπqP : v.IsPrimeElement Pi πqP := by
    rw [ValuationData.IsPrimeElement] at hπP ⊢
    calc
      v.valuationAt Pi πqP = v.valuationAt Pi πP := by
        have hvaluation :=
          v.valuationAt_normalExtensionAction EPK hPnormal k πP
        change v.valuationAt Pi
            (normalExtensionAction A K.field P.field P.below hPnormal k πP) =
          v.valuationAt Pi πP at hvaluation
        exact hvaluation
      _ = v.oneValue := hπP
  let uP : v.unitAddSubgroup Pi :=
    ⟨πP - πqP,
      v.sub_mem_unitAddSubgroup_of_prime Pi hπqP hπP⟩
  rw [v.mem_infiniteUnitAddSubgroup_iff]
  refine ⟨P, uP, ?_⟩
  have hkq : (QuotientGroup.mk k :
      K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = q :=
    Quotient.out_eq' q
  rw [← hkq, D.frobeniusQuotientAction_mk]
  apply Subtype.ext
  rfl

end DegreeData

end

end Atlas.Knowledge
