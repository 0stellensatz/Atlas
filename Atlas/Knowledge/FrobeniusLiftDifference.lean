import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.ChosenPrimeElement
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteFieldUnitMaps
import Atlas.Knowledge.FiniteIntermediateFieldRefinement
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FiniteReciprocityValue
import Atlas.Knowledge.FiniteResidueAbstractField
import Atlas.Knowledge.FiniteTower
import Atlas.Knowledge.FrobeniusDescent
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusExponent
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.ProfiniteInteger
import Atlas.Knowledge.ReciprocityMap
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.ValuationData

/-!
# Frobenius lift difference

The lift-comparison algebra of the finite reciprocity construction: the
quotient of two Frobenius lifts of unequal exponent is itself a
Frobenius lift whose exponent is the positive difference, recovering
the larger lift by multiplication and restricting trivially when the
lifts restrict equally; a trivially restricting lift has zero finite
reciprocity value; and equal restrictions with equal exponents force
equal lifts (#104).

## Main definitions

* `DegreeData.frobeniusLiftDifference` — the quotient lift.

## Main statements

* `DegreeData.frobeniusLiftDifference_coe` — the coercion is `σ⁻¹τ`;
  proved.
* `DegreeData.mul_frobeniusLiftDifference` — recovery of the larger
  lift; proved.
* `DegreeData.frobeniusRestriction_frobeniusLiftDifference` — trivial
  restriction of the quotient; proved.
* `DegreeData.finiteReciprocityValue_eq_zero_of_restriction_eq_one` —
  zero value on trivial restrictions; proved.
* `DegreeData.frobenius_eq_of_restriction_eq_of_exponent_eq` — lift
  equality from equal data; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling.
All three sections sit at the source's `Type u`, the value theorem's
since the #104 hoist unpinned the quotient-action chain it follows, and
that theorem sheds its enrichment `letI` bridge — the
`FiniteFieldUnitMaps` transport instance stands in for it — and the
source's `[T2Space G]`, which was simply unused there, so the ported
statement is strictly more general than the source's. The profinite
integers are the layer's `ProfiniteInteger`, the tower is the layer's
top-level `FiniteTower`, and the tower-finiteness call drops the
redundant base containment the layer's form does without. The
`AmbientFixedAddSubgroup` and `FiniteFieldUnitMaps` imports are
referenced by no name: the first carries the statement-level type the
norm quotient elaborates over, the second the transport instances that
let the Frobenius-element binders synthesize across the residue
enrichment. The citations name this file by bare basename; it lives at
`AbstractClassFieldTheory/Reciprocity/Construction/` in the source. The
source's `open`s go — the layer keeps everything in one namespace.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

section frobeniusLiftAlgebra

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **The quotient between two Frobenius lifts when the exponent of the
first is strictly smaller** — its exponent is the positive difference
([Yamaguchi 2026, `MainFiniteReciprocity.lean:150`][Yamaguchi2026]). -/
def frobeniusLiftDifference (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ τ : D.FrobeniusElements K L hLK)
    (hdegree : D.frobeniusExponent K L hLK σ <
      D.frobeniusExponent K L hLK τ) :
    D.FrobeniusElements K L hLK := by
  let nσ := D.frobeniusExponent K L hLK σ
  let nτ := D.frobeniusExponent K L hLK τ
  let m := nτ - nσ
  have hm : 0 < m := Nat.sub_pos_of_lt hdegree
  refine ⟨σ.1⁻¹ * τ.1, m, hm, ?_⟩
  rw [map_mul, map_inv,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK τ]
  have hle : nσ ≤ nτ := Nat.le_of_lt hdegree
  change ((Multiplicative.ofAdd (1 : ProfiniteInteger) : ProfiniteIntegerMul) ^ nσ)⁻¹ *
      (Multiplicative.ofAdd (1 : ProfiniteInteger) : ProfiniteIntegerMul) ^ nτ =
    (Multiplicative.ofAdd (1 : ProfiniteInteger) : ProfiniteIntegerMul) ^ m
  rw [← Nat.add_sub_of_le hle, pow_add]
  simp [m]

/-- **The lift difference coerces to the ambient quotient** `σ⁻¹τ`
([Yamaguchi 2026, `MainFiniteReciprocity.lean:175`][Yamaguchi2026]). -/
@[simp]
theorem frobeniusLiftDifference_coe (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ τ : D.FrobeniusElements K L hLK)
    (hdegree : D.frobeniusExponent K L hLK σ <
      D.frobeniusExponent K L hLK τ) :
    (D.frobeniusLiftDifference K L hLK σ τ hdegree).1 =
      σ.1⁻¹ * τ.1 :=
  by simp [frobeniusLiftDifference]

/-- **Multiplying the smaller lift by its quotient recovers the larger
lift**
([Yamaguchi 2026, `MainFiniteReciprocity.lean:187`][Yamaguchi2026]). -/
theorem mul_frobeniusLiftDifference (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ τ : D.FrobeniusElements K L hLK)
    (hdegree : D.frobeniusExponent K L hLK σ <
      D.frobeniusExponent K L hLK τ) :
    σ * D.frobeniusLiftDifference K L hLK σ τ hdegree = τ := by
  apply Subtype.ext
  rw [frobeniusMul_coe, frobeniusLiftDifference_coe]
  simp

/-- **When the two lifts restrict equally, their quotient restricts
trivially**
([Yamaguchi 2026, `MainFiniteReciprocity.lean:201`][Yamaguchi2026]). -/
theorem frobeniusRestriction_frobeniusLiftDifference (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ τ : D.FrobeniusElements K L hLK)
    (hRestriction : D.frobeniusRestriction K L hLK σ =
      D.frobeniusRestriction K L hLK τ)
    (hdegree : D.frobeniusExponent K L hLK σ <
      D.frobeniusExponent K L hLK τ) :
    D.frobeniusRestriction K L hLK
      (D.frobeniusLiftDifference K L hLK σ τ hdegree) = 1 := by
  change D.extensionRestriction K.field L hLK
    (D.frobeniusLiftDifference K L hLK σ τ hdegree).1 = 1
  rw [D.frobeniusLiftDifference_coe K L hLK σ τ hdegree]
  rw [map_mul, map_inv]
  change (D.frobeniusRestriction K L hLK σ)⁻¹ *
      D.frobeniusRestriction K L hLK τ = 1
  rw [hRestriction, inv_mul_cancel]

end DegreeData

end frobeniusLiftAlgebra

section trivialRestrictionValues

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **A Frobenius lift restricting trivially to `L` has zero finite
reciprocity value** — its fixed field contains `L`, so its norm to `K`
factors through `N_{L|K}`
([Yamaguchi 2026, `MainFiniteReciprocity.lean:234`][Yamaguchi2026]). -/
theorem finiteReciprocityValue_eq_zero_of_restriction_eq_one
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hσ : D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK σ = 1) :
    D.finiteReciprocityValue A v K L hLK σ = 0 := by
  let KR := K.toFiniteResidueAbstractField D
  let S := D.frobeniusFixedField KR L hLK σ
  let hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le KR L hLK σ
  let hSL : S.toSubgroup ≤ L.toSubgroup :=
    D.frobeniusFixedField_le_of_restriction_eq_one
      KR L hLK σ hσ
  letI hSfinite : Finite
      (K.field.toSubgroup ⧸ S.toSubgroup.subgroupOf K.field.toSubgroup) :=
    D.frobeniusFixedField_finite KR L hLK σ
  letI hSLfinite : Finite
      (L.toSubgroup ⧸ S.toSubgroup.subgroupOf L.toSubgroup) :=
    FiniteIntermediateField.finite_extension_of_le hLK hSL
  letI hSabsolute : Finite ((baseField G).toSubgroup ⧸
      S.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ
  let Sigma : FiniteAbstractField G := ⟨S, hSabsolute⟩
  rw [finiteReciprocityValue,
    D.reciprocityMap_eq_chosenPrime A v K L hLK σ]
  change D.maximalUnramifiedToFiniteNormQuotient A K.field L hLK
      (D.maximalUnramifiedNormClass A K.field L
        (relativeNorm A K.field S hSK (v.chosenPrimeElement Sigma))) = 0
  rw [D.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass]
  apply (finiteNormClass_eq_zero_iff A K.field L hLK _).2
  change relativeNorm A K.field S hSK (v.chosenPrimeElement Sigma) ∈
    (relativeNorm A K.field L hLK).range
  refine ⟨relativeNorm A L S hSL (v.chosenPrimeElement Sigma), ?_⟩
  let T : FiniteTower G :=
    { top := S
      middle := L
      base := K.field
      top_le_middle := hSL
      middle_le_base := hLK
      finiteTopQuotient := hSLfinite
      finiteBaseQuotient := hLfinite }
  exact T.norm_trans_apply A (v.chosenPrimeElement Sigma)

end DegreeData

end trivialRestrictionValues

section equalFrobeniusLifts

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **Equal restrictions and equal exponents give equal Frobenius
lifts** — the first case in the lift-independence proof
([Yamaguchi 2026, `MainFiniteReciprocity.lean:297`][Yamaguchi2026]). -/
theorem frobenius_eq_of_restriction_eq_of_exponent_eq (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    {σ τ : D.FrobeniusElements K L hLK}
    (hRestriction : D.frobeniusRestriction K L hLK σ =
      D.frobeniusRestriction K L hLK τ)
    (hExponent : D.frobeniusExponent K L hLK σ =
      D.frobeniusExponent K L hLK τ) :
    σ = τ := by
  apply D.frobenius_eq_of_restriction_eq_of_degree_eq
    K L hLK hRestriction
  rw [D.extensionNormalizedDegree_frobenius_eq_pow,
    D.extensionNormalizedDegree_frobenius_eq_pow, hExponent]

end DegreeData

end equalFrobeniusLifts

end

end Atlas.Knowledge
