import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteFieldUnitMaps
import Atlas.Knowledge.FiniteResidueAbstractField
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.FrobeniusActionRemainder
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusExponent
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.FrobeniusNormIdentities
import Atlas.Knowledge.FrobeniusQuotientAction
import Atlas.Knowledge.InertiaQuotientDegreeKernel
import Atlas.Knowledge.MaximalUnramifiedField
import Atlas.Knowledge.PrimeElement
import Atlas.Knowledge.ReciprocityIndependence
import Atlas.Knowledge.ReciprocityMap
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.UnitCohomologyAxiom
import Atlas.Knowledge.ValuationData

/-!
# Norm-class relation

The Frobenius power-sum norm relation passed down to the
maximal-unramified norm quotient and then to the reciprocity map: the
relative norm of the power-sum combination `u`, the final quotient
step, and the conversion of the three-class equality into reciprocity
multiplicativity via prime-choice independence (#104).

## Main statements

* `DegreeData.relativeNorm_frobeniusPowerSum_alternating` — the norm of
  the power-sum combination; proved.
* `DegreeData.maximalUnramifiedNormClass_add_eq_of_relativeNorm` — the
  final quotient step; proved.
* `DegreeData.reciprocityMap_mul_of_primeNormClass_eq` — three norm
  classes to reciprocity multiplicativity; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling, and
the ambient group is `Type` after the `Type`-pinned quotient-action
chain. Four further departures: both `maximalUnramifiedExtension_finite`
call sites drop the containment argument, since the layer's form is
instance-supplied; the closing `simpa` becomes `exact hclasses.symm`,
the rewrite tripping on the instance position here while the terms are
defeq; the source's enrichment re-anchoring block in the independence
step is dropped entirely, the instances threading through by defeq; and
both representation-bearing theorems shed the source's `[T2Space G]`,
Hausdorff being instance-derivable from the remaining binders. The
quotient step also sheds the source's dead `Finite` instance on the
`L`-over-`K.field` quotient — only the maximal-unramified level is used.
The `FiniteFieldUnitMaps` import is referenced by no name: it carries
the transport instances that let the Frobenius-element binders
synthesize across the residue enrichment. The citations name this file
by bare basename; it lives at
`AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/`
in the source. The source's `open`s go — the layer keeps everything in
one namespace.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **Applying the relative norm from the maximal unramified extension
to the power-sum combination `u` gives the corresponding combination of
the three finite fixed-field norms**
([Yamaguchi 2026, `NormClassRelation.lean:29`][Yamaguchi2026]). -/
theorem relativeNorm_frobeniusPowerSum_alternating
    (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (φ σ₁ σ₂ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (π₁ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ₁))
    (π₃ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK (σ₁ * σ₂)))
    (π₄ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK
        (D.frobeniusActionConjugate K L hLK φ σ₂
          (D.frobeniusExponent K L hLK σ₁)))) :
    let σ₃ := σ₁ * σ₂
    let σ₄ := D.frobeniusActionConjugate K L hLK φ σ₂
      (D.frobeniusExponent K L hLK σ₁)
    let S₁ := D.frobeniusFixedField K L hLK σ₁
    let S₃ := D.frobeniusFixedField K L hLK σ₃
    let S₄ := D.frobeniusFixedField K L hLK σ₄
    let hS₁K := D.frobeniusFixedField_le K L hLK σ₁
    let hS₃K := D.frobeniusFixedField_le K L hLK σ₃
    let hS₄K := D.frobeniusFixedField_le K L hLK σ₄
    let p₁ := fixedFieldInclusion A S₁ (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField K L hLK σ₁) π₁
    let p₃ := fixedFieldInclusion A S₃ (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField K L hLK σ₃) π₃
    let p₄ := fixedFieldInclusion A S₄ (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField K L hLK σ₄) π₄
    let u := D.frobeniusPowerSum A K.field L hLK φ.1
        (D.frobeniusExponent K L hLK σ₄) p₄ +
      D.frobeniusPowerSum A K.field L hLK φ.1
        (D.frobeniusExponent K L hLK σ₁) p₁ -
      D.frobeniusPowerSum A K.field L hLK φ.1
        (D.frobeniusExponent K L hLK σ₃) p₃
    letI : Finite (K.field.toSubgroup ⧸ S₁.toSubgroup.subgroupOf K.field.toSubgroup) :=
      D.frobeniusFixedField_finite K L hLK σ₁
    letI : Finite (K.field.toSubgroup ⧸ S₃.toSubgroup.subgroupOf K.field.toSubgroup) :=
      D.frobeniusFixedField_finite K L hLK σ₃
    letI : Finite (K.field.toSubgroup ⧸ S₄.toSubgroup.subgroupOf K.field.toSubgroup) :=
      D.frobeniusFixedField_finite K L hLK σ₄
    letI : Finite
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          (D.maximalUnramifiedField L).toSubgroup.subgroupOf
            (D.maximalUnramifiedField K.field).toSubgroup) :=
      D.maximalUnramifiedExtension_finite K.field L
    ((relativeNorm A (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) u :
        ambientFixedAddSubgroup A (D.maximalUnramifiedField K.field)) : A.V) =
      ((relativeNorm A K.field S₄ hS₄K π₄ +
        relativeNorm A K.field S₁ hS₁K π₁ -
        relativeNorm A K.field S₃ hS₃K π₃ :
          ambientFixedAddSubgroup A K.field) : A.V) := by
  dsimp only
  let σ₃ := σ₁ * σ₂
  let σ₄ := D.frobeniusActionConjugate K L hLK φ σ₂
    (D.frobeniusExponent K L hLK σ₁)
  let S₁ := D.frobeniusFixedField K L hLK σ₁
  let S₃ := D.frobeniusFixedField K L hLK σ₃
  let S₄ := D.frobeniusFixedField K L hLK σ₄
  let hS₁K := D.frobeniusFixedField_le K L hLK σ₁
  let hS₃K := D.frobeniusFixedField_le K L hLK σ₃
  let hS₄K := D.frobeniusFixedField_le K L hLK σ₄
  let p₁ := fixedFieldInclusion A S₁ (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ₁) π₁
  let p₃ := fixedFieldInclusion A S₃ (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ₃) π₃
  let p₄ := fixedFieldInclusion A S₄ (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ₄) π₄
  let s₁ := D.frobeniusPowerSum A K.field L hLK φ.1
    (D.frobeniusExponent K L hLK σ₁) p₁
  let s₃ := D.frobeniusPowerSum A K.field L hLK φ.1
    (D.frobeniusExponent K L hLK σ₃) p₃
  let s₄ := D.frobeniusPowerSum A K.field L hLK φ.1
    (D.frobeniusExponent K L hLK σ₄) p₄
  let u := s₄ + s₁ - s₃
  letI hS₁finite : Finite
      (K.field.toSubgroup ⧸ S₁.toSubgroup.subgroupOf K.field.toSubgroup) :=
    D.frobeniusFixedField_finite K L hLK σ₁
  letI hS₃finite : Finite
      (K.field.toSubgroup ⧸ S₃.toSubgroup.subgroupOf K.field.toSubgroup) :=
    D.frobeniusFixedField_finite K L hLK σ₃
  letI hS₄finite : Finite
      (K.field.toSubgroup ⧸ S₄.toSubgroup.subgroupOf K.field.toSubgroup) :=
    D.frobeniusFixedField_finite K L hLK σ₄
  letI hIfinite : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        (D.maximalUnramifiedField L).toSubgroup.subgroupOf
            (D.maximalUnramifiedField K.field).toSubgroup) :=
    D.maximalUnramifiedExtension_finite K.field L
  have h₁ := (D.frobeniusNormIdentities A K L hLK φ σ₁ hφ π₁).1
  have h₃ := (D.frobeniusNormIdentities A K L hLK φ σ₃ hφ π₃).1
  have h₄ := (D.frobeniusNormIdentities A K L hLK φ σ₄ hφ π₄).1
  let N := relativeNorm A (D.maximalUnramifiedField K.field)
    (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
  change ((N (s₄ + s₁ - s₃) :
      ambientFixedAddSubgroup A (D.maximalUnramifiedField K.field)) : A.V) = _
  rw [map_sub, map_add]
  change (N s₄).1 + (N s₁).1 - (N s₃).1 = _
  rw [← h₄, ← h₁, ← h₃]
  rfl

/-- **The final quotient step of reciprocity multiplicativity**: once
the maximal-unramified norm of `u` descends to a universal norm in
`A_K`, the norm relation is exactly the desired equality of
reciprocity classes
([Yamaguchi 2026, `NormClassRelation.lean:140`][Yamaguchi2026]). -/
theorem maximalUnramifiedNormClass_add_eq_of_relativeNorm
    (D : DegreeData G) (A : Rep ℤ G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        (D.maximalUnramifiedField L).toSubgroup.subgroupOf
            (D.maximalUnramifiedField K.field).toSubgroup)]
    (r₁ r₂ r₃ : ambientFixedAddSubgroup A K.field)
    (u : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (hnorm :
      ((relativeNorm A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) u :
          ambientFixedAddSubgroup A (D.maximalUnramifiedField K.field)) : A.V) =
        ((r₁ + r₂ - r₃ : ambientFixedAddSubgroup A K.field) : A.V))
    (huniversal : ∃ aK : ambientFixedAddSubgroup A K.field,
      fixedFieldInclusion A K.field (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField_le K.field) aK =
        relativeNorm A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) u ∧
      aK ∈ D.maximalUnramifiedNormSubgroup A K.field L) :
    D.maximalUnramifiedNormClass A K.field L r₁ +
        D.maximalUnramifiedNormClass A K.field L r₂ =
      D.maximalUnramifiedNormClass A K.field L r₃ := by
  obtain ⟨aK, hdescend, haK⟩ := huniversal
  have hsum : r₁ + r₂ - r₃ = aK := by
    apply Subtype.ext
    exact hnorm.symm.trans (congrArg Subtype.val hdescend).symm
  have hmem : r₁ + r₂ - r₃ ∈
      D.maximalUnramifiedNormSubgroup A K.field L := by
    rw [hsum]
    exact haK
  have hzero := (D.maximalUnramifiedNormClass_eq_zero_iff
    A K.field L (r₁ + r₂ - r₃)).2 hmem
  rw [map_sub, map_add] at hzero
  exact sub_eq_zero.mp hzero

/-- **Prime-choice independence converts an equality of the three
explicit norm classes into reciprocity multiplicativity's equality for
the canonical reciprocity map**
([Yamaguchi 2026, `NormClassRelation.lean:182`][Yamaguchi2026]). -/
theorem reciprocityMap_mul_of_primeNormClass_eq
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ₁ σ₂ : D.FrobeniusElements
      (K.toFiniteResidueAbstractField D) L hLK)
    (π₁ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ₁))
    (π₂ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ₂))
    (π₃ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
        (σ₁ * σ₂)))
    (hπ₁ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma1 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ₁,
          D.frobeniusFixedField_absoluteFinite K L hLK σ₁⟩
      v.IsPrimeElement Sigma1 π₁)
    (hπ₂ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma2 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ₂,
          D.frobeniusFixedField_absoluteFinite K L hLK σ₂⟩
      v.IsPrimeElement Sigma2 π₂)
    (hπ₃ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma3 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK (σ₁ * σ₂),
          D.frobeniusFixedField_absoluteFinite K L hLK (σ₁ * σ₂)⟩
      v.IsPrimeElement Sigma3 π₃)
    (hclasses :
      let KR := K.toFiniteResidueAbstractField D
      let S₁ := D.frobeniusFixedField KR L hLK σ₁
      let S₂ := D.frobeniusFixedField KR L hLK σ₂
      let S₃ := D.frobeniusFixedField KR L hLK (σ₁ * σ₂)
      let hS₁K := D.frobeniusFixedField_le KR L hLK σ₁
      let hS₂K := D.frobeniusFixedField_le KR L hLK σ₂
      let hS₃K := D.frobeniusFixedField_le KR L hLK (σ₁ * σ₂)
      letI : Finite (K.field.toSubgroup ⧸ S₁.toSubgroup.subgroupOf K.field.toSubgroup) :=
        D.frobeniusFixedField_finite KR L hLK σ₁
      letI : Finite (K.field.toSubgroup ⧸ S₂.toSubgroup.subgroupOf K.field.toSubgroup) :=
        D.frobeniusFixedField_finite KR L hLK σ₂
      letI : Finite (K.field.toSubgroup ⧸ S₃.toSubgroup.subgroupOf K.field.toSubgroup) :=
        D.frobeniusFixedField_finite KR L hLK (σ₁ * σ₂)
      D.maximalUnramifiedNormClass A K.field L
          (relativeNorm A K.field S₁ hS₁K π₁) +
        D.maximalUnramifiedNormClass A K.field L
          (relativeNorm A K.field S₂ hS₂K π₂) =
        D.maximalUnramifiedNormClass A K.field L
          (relativeNorm A K.field S₃ hS₃K π₃)) :
    D.reciprocityMap A v K L hLK (σ₁ * σ₂) =
      D.reciprocityMap A v K L hLK σ₁ +
        D.reciprocityMap A v K L hLK σ₂ := by
  have h₁ := D.reciprocityValueOfPrime_eq_reciprocityMap
    A v hAxiom K L hLK σ₁ π₁ hπ₁
  have h₂ := D.reciprocityValueOfPrime_eq_reciprocityMap
    A v hAxiom K L hLK σ₂ π₂ hπ₂
  have h₃ := D.reciprocityValueOfPrime_eq_reciprocityMap
    A v hAxiom K L hLK (σ₁ * σ₂) π₃ hπ₃
  rw [← h₃, ← h₁, ← h₂]
  exact hclasses.symm

end DegreeData

end

end Atlas.Knowledge
