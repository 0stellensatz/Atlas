import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.ChosenPrimeElement
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteFieldUnitMaps
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.PrimeElement
import Atlas.Knowledge.ReciprocityIndependence
import Atlas.Knowledge.ReciprocityMap
import Atlas.Knowledge.ReciprocityMapMul
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.UnitCohomologyAxiom
import Atlas.Knowledge.ValuationData

/-!
# Finite reciprocity value

The reciprocity value on the Frobenius semigroup mapped to the finite
norm quotient: additivity survives the passage under the
unit-cohomology axiom, and the value is the finite class of a prime's
relative norm — for the chosen prime unconditionally, and for any prime
under the axiom (#104).

## Main definitions

* `DegreeData.finiteReciprocityValue` — the finite reciprocity value.

## Main statements

* `DegreeData.finiteReciprocityValue_mul` — additivity after passage,
  under the axiom; proved.
* `DegreeData.finiteReciprocityValue_eq_primeNormClass` — the
  chosen-prime formula; proved.
* `DegreeData.finiteReciprocityValue_eq_primeNormClass_of_isPrime` —
  the any-prime formula; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
the ambient group is `Type u` since the #104 hoist, and all four
declarations shed the source's `[T2Space G]` — on the two axiom-bearing
statements Hausdorff is instance-derivable from their
`[TotallyDisconnectedSpace G]`, while on the other two it was simply
unused, so those statements are strictly more general than the
source's. The `FiniteFieldUnitMaps` import is referenced by no name: it
carries the transport instances that let the Frobenius-element binders
synthesize across the residue enrichment. The citations name this file
by bare basename; it lives at
`AbstractClassFieldTheory/Reciprocity/Construction/` in the source. The
source's `open`s go — the layer keeps everything in one namespace.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **The finite reciprocity value**: the reciprocity value of a
Frobenius element after passage from the universal norm quotient to the
finite quotient by `N_{L|K} A_L`
([Yamaguchi 2026, `MainFiniteReciprocity.lean:37`][Yamaguchi2026]). -/
def finiteReciprocityValue (D : DegreeData G) (A : Rep ℤ G)
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK) :
    FiniteNormQuotient A K.field L hLK :=
  D.maximalUnramifiedToFiniteNormQuotient A K.field L hLK
    (D.reciprocityMap A v K L hLK σ)

/-- **Reciprocity multiplicativity remains additive after passage to
the finite quotient**
([Yamaguchi 2026, `MainFiniteReciprocity.lean:52`][Yamaguchi2026]). -/
theorem finiteReciprocityValue_mul
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (α β : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK) :
    D.finiteReciprocityValue A v K L hLK (α * β) =
      D.finiteReciprocityValue A v K L hLK α +
        D.finiteReciprocityValue A v K L hLK β := by
  unfold finiteReciprocityValue
  rw [D.reciprocityMap_mul A v hAxiom K L hLK α β]
  exact map_add
    (D.maximalUnramifiedToFiniteNormQuotient A K.field L hLK) _ _

/-- **The finite reciprocity value is the finite class of the chosen
prime's relative norm**
([Yamaguchi 2026, `MainFiniteReciprocity.lean:73`][Yamaguchi2026]). -/
theorem finiteReciprocityValue_eq_primeNormClass
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK) :
    let KR := K.toFiniteResidueAbstractField D
    let S := D.frobeniusFixedField KR L hLK σ
    let hSK := D.frobeniusFixedField_le KR L hLK σ
    letI : Finite
        (K.field.toSubgroup ⧸ S.toSubgroup.subgroupOf K.field.toSubgroup) :=
      D.frobeniusFixedField_finite KR L hLK σ
    letI : Finite ((baseField G).toSubgroup ⧸
        S.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
      D.frobeniusFixedField_absoluteFinite K L hLK σ
    let Sigma : FiniteAbstractField G := ⟨S, inferInstance⟩
    D.finiteReciprocityValue A v K L hLK σ =
      finiteNormClass A K.field L hLK
        (relativeNorm A K.field S hSK (v.chosenPrimeElement Sigma)) := by
  dsimp only
  rw [finiteReciprocityValue,
    D.reciprocityMap_eq_chosenPrime A v K L hLK σ]
  exact D.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass
    A K.field L hLK _

/-- **The same formula for any prime element of the fixed field** —
prime-choice independence is exactly the reciprocity construction's
consequence of the unit-cohomology axiom
([Yamaguchi 2026, `MainFiniteReciprocity.lean:103`][Yamaguchi2026]). -/
theorem finiteReciprocityValue_eq_primeNormClass_of_isPrime
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ))
    (hπ :
      let Sigma : FiniteAbstractField G :=
        { field := D.frobeniusFixedField
            (K.toFiniteResidueAbstractField D) L hLK σ
          finite := D.frobeniusFixedField_absoluteFinite K L hLK σ }
      v.IsPrimeElement Sigma π) :
    let KR := K.toFiniteResidueAbstractField D
    let S := D.frobeniusFixedField KR L hLK σ
    let hSK := D.frobeniusFixedField_le KR L hLK σ
    letI : Finite
        (K.field.toSubgroup ⧸ S.toSubgroup.subgroupOf K.field.toSubgroup) :=
      D.frobeniusFixedField_finite KR L hLK σ
    D.finiteReciprocityValue A v K L hLK σ =
      finiteNormClass A K.field L hLK
        (relativeNorm A K.field S hSK π) := by
  dsimp only
  rw [finiteReciprocityValue,
    ← D.reciprocityValueOfPrime_eq_reciprocityMap
      A v hAxiom K L hLK σ π hπ]
  exact D.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass
    A K.field L hLK _

end DegreeData

end

end Atlas.Knowledge
