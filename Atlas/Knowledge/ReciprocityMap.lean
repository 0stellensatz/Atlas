import Mathlib
import Atlas.Knowledge.ChosenPrimeElement
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.MaximalUnramifiedField
import Atlas.Knowledge.RelativeNormLaws

/-!
# reciprocity map

The reciprocity construction's map, defined: for a Frobenius element `σ`
with fixed field `Σ`, the reciprocity class is the class of `N_{Σ|K}(π_Σ)`
in `A_K / N_{L̃|K} A_{L̃}`, with `π_Σ` the canonical chosen prime supplied
by surjectivity of the normalized valuation `v_Σ`. Independence of the
prime element is the later theorem the unit-cohomology axiom feeds; here
the map itself and its chosen-prime representation are recorded (#104).

## Main definitions

* `DegreeData.frobeniusFixedIntermediateField` — `Σ` as a finite
  intermediate field of `L̃ | K`.
* `DegreeData.reciprocityValueOfPrime` — the reciprocity class of an
  explicit prime element.
* `DegreeData.reciprocityMap` — the reciprocity map on the Frobenius
  semigroup, at the chosen prime.

## Main statements

* `DegreeData.frobeniusFixedField_absoluteFinite` — `Σ | k` is finite, by
  the tower `Σ | K | k`; proved.
* `DegreeData.reciprocityMap_eq_chosenPrime` — the map at a Frobenius
  element is represented by the chosen prime of its fixed field; proved.

## Implementation notes

Instance search does not unfold the residue enrichment
`K.toFiniteResidueAbstractField D`, so the normality and finiteness
instances are transported by hand on both sides of the definition, as in
the source — but where the source transports them with `simpa` bridges,
the layer passes the hypotheses as plain terms: the mismatch sits in an
instance argument the simp set does not rewrite, while the enrichment's
field projection is definitional, so the ascribed `letI` accepts the bare
hypothesis. The source's statement-level `simpa` in the chosen-prime
representation, which rewrites an explicit argument, stays as written.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **The fixed field `Σ` as a finite intermediate field of `L̃ | K`**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityDefinition.lean:33`]
[Yamaguchi2026]). -/
def frobeniusFixedIntermediateField (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements K L hLK) :
    FiniteIntermediateField (D.maximalUnramifiedField L) K.field where
  field := D.frobeniusFixedField K L hLK σ
  above := D.fieldInertia_le_frobeniusFixedField K L hLK σ
  below := D.frobeniusFixedField_le K L hLK σ
  finite := D.frobeniusFixedField_finite K L hLK σ

/-- **The extension `Σ | k` is finite**, from the finite tower `Σ | K | k`
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityDefinition.lean:48`]
[Yamaguchi2026]). -/
theorem frobeniusFixedField_absoluteFinite (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK
      (hLnormal := hLnormal)) :
    Finite ((baseField G).toSubgroup ⧸
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
          (hLnormal := hLnormal) σ).toSubgroup.subgroupOf
        (baseField G).toSubgroup) := by
  let KR := K.toFiniteResidueAbstractField D
  letI hLnormalKR :
      (L.toSubgroup.subgroupOf KR.field.toSubgroup).Normal := hLnormal
  letI hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf KR.field.toSubgroup) := hLfinite
  letI : Finite (K.field.toSubgroup ⧸
      (D.frobeniusFixedField KR L hLK σ).toSubgroup.subgroupOf
        K.field.toSubgroup) :=
    D.frobeniusFixedField_finite KR L hLK σ
  exact relativeTowerQuotientFinite (baseField G) K.field
    (D.frobeniusFixedField KR L hLK σ)
    (D.frobeniusFixedField_le KR L hLK σ) (le_baseField K.field)

/-- **The reciprocity construction at an explicit prime element `π_Σ`**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityDefinition.lean:94`]
[Yamaguchi2026]). -/
def reciprocityValueOfPrime (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements K L hLK)
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)) :
    D.MaximalUnramifiedNormQuotient A K.field L := by
  letI : Finite (K.field.toSubgroup ⧸
      (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
        K.field.toSubgroup) :=
    D.frobeniusFixedField_finite K L hLK σ
  exact D.maximalUnramifiedNormClass A K.field L
    (relativeNorm A K.field (D.frobeniusFixedField K L hLK σ)
      (D.frobeniusFixedField_le K L hLK σ) π)

/-- **The reciprocity map on the Frobenius semigroup**, at the canonical
chosen prime supplied by surjectivity of `v_Σ`; the later independence
theorem identifies this value with the formula for every prime element
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityDefinition.lean:117`]
[Yamaguchi2026]). -/
def reciprocityMap (D : DegreeData G) (A : Rep ℤ G)
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf K.field.toSubgroup)] :
    D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK
        (hLnormal := hLnormal) →
      D.MaximalUnramifiedNormQuotient A K.field L :=
  fun σ => by
    let KR := K.toFiniteResidueAbstractField D
    letI hLnormalKR :
        (L.toSubgroup.subgroupOf KR.field.toSubgroup).Normal := hLnormal
    letI hLfiniteKR : Finite
        (KR.field.toSubgroup ⧸
          L.toSubgroup.subgroupOf KR.field.toSubgroup) := hLfinite
    letI : Finite ((baseField G).toSubgroup ⧸
        (D.frobeniusFixedField KR L hLK σ).toSubgroup.subgroupOf
          (baseField G).toSubgroup) :=
      D.frobeniusFixedField_absoluteFinite K L hLK σ
    let Sigma : FiniteAbstractField G :=
      ⟨D.frobeniusFixedField KR L hLK σ, inferInstance⟩
    exact D.reciprocityValueOfPrime A KR L hLK σ
      (v.chosenPrimeElement Sigma)

/-- **The reciprocity map at a Frobenius element is represented by the
chosen prime element of its fixed field** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityDefinition.lean:150`]
[Yamaguchi2026]). -/
theorem reciprocityMap_eq_chosenPrime (D : DegreeData G) (A : Rep ℤ G)
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK
      (hLnormal := hLnormal)) :
    D.reciprocityMap A v K L hLK σ = by
      let KR := K.toFiniteResidueAbstractField D
      letI : (L.toSubgroup.subgroupOf KR.field.toSubgroup).Normal :=
        hLnormal
      letI hLfiniteKR : Finite
          (KR.field.toSubgroup ⧸
            L.toSubgroup.subgroupOf KR.field.toSubgroup) := hLfinite
      letI : Finite ((baseField G).toSubgroup ⧸
          (D.frobeniusFixedField KR L hLK σ).toSubgroup.subgroupOf
            (baseField G).toSubgroup) :=
        D.frobeniusFixedField_absoluteFinite K L hLK σ
      let Sigma : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ, inferInstance⟩
      simpa only [Sigma, KR,
          FiniteAbstractField.toFiniteResidueAbstractField] using
        (D.reciprocityValueOfPrime A KR L hLK σ
          (v.chosenPrimeElement Sigma)) :=
  rfl

end DegreeData

end

end Atlas.Knowledge
