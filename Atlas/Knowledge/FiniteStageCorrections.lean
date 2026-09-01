import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteResidueAbstractField
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.FrobeniusActionRemainder
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusExponent
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.FrobeniusQuotientAction
import Atlas.Knowledge.FrobeniusQuotientDescent
import Atlas.Knowledge.InfiniteUnitDescent
import Atlas.Knowledge.MaximalUnramifiedField
import Atlas.Knowledge.PrimeElement
import Atlas.Knowledge.PrimeUnitDifferences
import Atlas.Knowledge.ReciprocityMap
import Atlas.Knowledge.ValuationData

/-!
# Finite-stage corrections

The Frobenius power-sum combination `s₄ + s₁ - s₃` of reciprocity
multiplicativity and each of the three correction coefficients are
genuine finite-stage units: the combination splits into the power sums
of a prime difference and of a prime minus an action translate, and the
coefficients are exactly the differences the prime-unit lemmas control
(#104).

## Main statements

* `DegreeData.frobeniusPowerSum_alternating_mem_infiniteUnitAddSubgroup`
  — the power-sum combination is a finite-stage unit; proved.
* `DegreeData.frobeniusCorrectionTerms_mem_infiniteUnitAddSubgroup` —
  all three correction coefficients are finite-stage units; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling, and
the ambient group is `Type` after the `Type`-pinned quotient-action
chain. The source's `letI` bridges for the two enrichment instances are
dropped entirely — here the instances thread through by defeq and the
bridges are scaffolding — and both theorems shed the source's dead
`[T2Space G]`, Hausdorff being instance-derivable from the remaining
binders. The citations name this file by bare basename; it lives at
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

/-- **The Frobenius power-sum combination `s₄ + s₁ - s₃` of
multiplicativity is a genuine finite-stage unit** — splitting the long
sum into two blocks expresses it as the power sums of `p₄ - p₃` and of
`p₁` minus an action translate of `p₃`
([Yamaguchi 2026, `FiniteStageCorrections.lean:28`][Yamaguchi2026]). -/
theorem frobeniusPowerSum_alternating_mem_infiniteUnitAddSubgroup
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (φ σ₁ σ₂ : D.FrobeniusElements
      (K.toFiniteResidueAbstractField D) L hLK)
    (π₁ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ₁))
    (π₃ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
        (σ₁ * σ₂)))
    (π₄ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
        (D.frobeniusActionConjugate (K.toFiniteResidueAbstractField D)
          L hLK φ σ₂
          (D.frobeniusExponent (K.toFiniteResidueAbstractField D)
            L hLK σ₁))))
    (hπ₁ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma1 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ₁,
          D.frobeniusFixedField_absoluteFinite K L hLK σ₁⟩
      v.IsPrimeElement Sigma1 π₁)
    (hπ₃ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma3 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK (σ₁ * σ₂),
          D.frobeniusFixedField_absoluteFinite K L hLK (σ₁ * σ₂)⟩
      v.IsPrimeElement Sigma3 π₃)
    (hπ₄ :
      let KR := K.toFiniteResidueAbstractField D
      let σ₄ := D.frobeniusActionConjugate KR L hLK φ σ₂
        (D.frobeniusExponent KR L hLK σ₁)
      let Sigma4 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ₄,
          D.frobeniusFixedField_absoluteFinite K L hLK σ₄⟩
      v.IsPrimeElement Sigma4 π₄) :
    let KR := K.toFiniteResidueAbstractField D
    let σ₃ := σ₁ * σ₂
    let σ₄ := D.frobeniusActionConjugate KR L hLK φ σ₂
      (D.frobeniusExponent KR L hLK σ₁)
    let p₁ := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK σ₁)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₁) π₁
    let p₃ := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK σ₃)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₃) π₃
    let p₄ := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK σ₄)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₄) π₄
    let u := D.frobeniusPowerSum A KR.field L hLK φ.1
        (D.frobeniusExponent KR L hLK σ₄) p₄ +
      D.frobeniusPowerSum A KR.field L hLK φ.1
        (D.frobeniusExponent KR L hLK σ₁) p₁ -
      D.frobeniusPowerSum A KR.field L hLK φ.1
        (D.frobeniusExponent KR L hLK σ₃) p₃
    u ∈ v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK) := by
  dsimp only
  let KR := K.toFiniteResidueAbstractField D
  let σ₃ := σ₁ * σ₂
  let σ₄ := D.frobeniusActionConjugate KR L hLK φ σ₂
    (D.frobeniusExponent KR L hLK σ₁)
  let p₁ := fixedFieldInclusion A
    (D.frobeniusFixedField KR L hLK σ₁)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₁) π₁
  let p₃ := fixedFieldInclusion A
    (D.frobeniusFixedField KR L hLK σ₃)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₃) π₃
  let p₄ := fixedFieldInclusion A
    (D.frobeniusFixedField KR L hLK σ₄)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₄) π₄
  let n₁ := D.frobeniusExponent KR L hLK σ₁
  let n₃ := D.frobeniusExponent KR L hLK σ₃
  let n₄ := D.frobeniusExponent KR L hLK σ₄
  let U := v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
    (D.maximalUnramifiedField_le_of_le hLK)
  have h₄₃ : p₄ - p₃ ∈ U := by
    exact D.frobeniusPrimeDifference_mem_infiniteUnitAddSubgroup
      A v K L hLK σ₄ σ₃ π₄ π₃ hπ₄ hπ₃
  have h₁₃ : p₁ - p₃ ∈ U := by
    exact D.frobeniusPrimeDifference_mem_infiniteUnitAddSubgroup
      A v K L hLK σ₁ σ₃ π₁ π₃ hπ₁ hπ₃
  have h₃action : p₃ - D.frobeniusQuotientAction A KR.field L hLK
      (φ.1 ^ n₄) p₃ ∈ U := by
    exact D.frobeniusPrime_actionDifference_mem_infiniteUnitAddSubgroup
      A v K L hLK σ₃ π₃ hπ₃ (φ.1 ^ n₄)
  have h₁shift : p₁ - D.frobeniusQuotientAction A KR.field L hLK
      (φ.1 ^ n₄) p₃ ∈ U := by
    have heq : p₁ - D.frobeniusQuotientAction A KR.field L hLK
        (φ.1 ^ n₄) p₃ = (p₁ - p₃) +
          (p₃ - D.frobeniusQuotientAction A KR.field L hLK
            (φ.1 ^ n₄) p₃) := by
      abel
    rw [heq]
    exact U.add_mem h₁₃ h₃action
  have hn₃ : n₃ = n₄ + n₁ := by
    simp [n₁, n₃, n₄, σ₃, σ₄, Nat.add_comm]
  let u := D.frobeniusPowerSum A KR.field L hLK φ.1 n₄ p₄ +
    D.frobeniusPowerSum A KR.field L hLK φ.1 n₁ p₁ -
    D.frobeniusPowerSum A KR.field L hLK φ.1 n₃ p₃
  have huEq : u =
      D.frobeniusPowerSum A KR.field L hLK φ.1 n₄ (p₄ - p₃) +
      D.frobeniusPowerSum A KR.field L hLK φ.1 n₁
        (p₁ - D.frobeniusQuotientAction A KR.field L hLK
          (φ.1 ^ n₄) p₃) := by
    dsimp [u]
    rw [D.frobeniusPowerSum_sub_universalNormDescent,
      D.frobeniusPowerSum_sub_universalNormDescent, hn₃,
      D.frobeniusPowerSum_add]
    abel
  have hsum₄₃ : D.frobeniusPowerSum A KR.field L hLK φ.1 n₄
      (p₄ - p₃) ∈ U :=
    v.frobeniusPowerSum_mem_infiniteUnit_universalNormDescent
      K L hLK φ.1 n₄ (p₄ - p₃) h₄₃
  have hsum₁ : D.frobeniusPowerSum A KR.field L hLK φ.1 n₁
      (p₁ - D.frobeniusQuotientAction A KR.field L hLK
        (φ.1 ^ n₄) p₃) ∈ U :=
    v.frobeniusPowerSum_mem_infiniteUnit_universalNormDescent
      K L hLK φ.1 n₁ _ h₁shift
  rw [show D.frobeniusPowerSum A KR.field L hLK φ.1 n₄ p₄ +
      D.frobeniusPowerSum A KR.field L hLK φ.1 n₁ p₁ -
      D.frobeniusPowerSum A KR.field L hLK φ.1 n₃ p₃ = u from rfl,
    huEq]
  exact U.add_mem hsum₄₃ hsum₁

/-- **Each of the three correction coefficients in the group-ring
identity is a finite-stage unit** — in the left-action translation the
product is `τ₄τ₁`, so the third coefficient is `p₃ - τ₁p₃`, acted on by
`τ₄` in `frobeniusMultiplicativityCorrectionAction`
([Yamaguchi 2026, `FiniteStageCorrections.lean:173`][Yamaguchi2026]). -/
theorem frobeniusCorrectionTerms_mem_infiniteUnitAddSubgroup
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (φ σ₁ σ₂ : D.FrobeniusElements
      (K.toFiniteResidueAbstractField D) L hLK)
    (π₁ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ₁))
    (π₃ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
        (σ₁ * σ₂)))
    (π₄ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
        (D.frobeniusActionConjugate (K.toFiniteResidueAbstractField D)
          L hLK φ σ₂
          (D.frobeniusExponent (K.toFiniteResidueAbstractField D)
            L hLK σ₁))))
    (hπ₁ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma1 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ₁,
          D.frobeniusFixedField_absoluteFinite K L hLK σ₁⟩
      v.IsPrimeElement Sigma1 π₁)
    (hπ₃ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma3 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK (σ₁ * σ₂),
          D.frobeniusFixedField_absoluteFinite K L hLK (σ₁ * σ₂)⟩
      v.IsPrimeElement Sigma3 π₃)
    (hπ₄ :
      let KR := K.toFiniteResidueAbstractField D
      let σ₄ := D.frobeniusActionConjugate KR L hLK φ σ₂
        (D.frobeniusExponent KR L hLK σ₁)
      let Sigma4 : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ₄,
          D.frobeniusFixedField_absoluteFinite K L hLK σ₄⟩
      v.IsPrimeElement Sigma4 π₄) :
    let KR := K.toFiniteResidueAbstractField D
    let σ₃ := σ₁ * σ₂
    let σ₄ := D.frobeniusActionConjugate KR L hLK φ σ₂
      (D.frobeniusExponent KR L hLK σ₁)
    let p₁ := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK σ₁)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₁) π₁
    let p₃ := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK σ₃)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₃) π₃
    let p₄ := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK σ₄)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₄) π₄
    let τ₁ := D.frobeniusActionRemainder KR L hLK φ σ₁
    ∀ i : Fin 3,
      (![p₄ - p₃, p₁ - p₃,
          p₃ - D.frobeniusQuotientAction A KR.field L hLK τ₁ p₃] :
        Fin 3 → ambientFixedAddSubgroup A
          (D.maximalUnramifiedField L)) i ∈
        v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK) := by
  dsimp only
  let KR := K.toFiniteResidueAbstractField D
  let σ₃ := σ₁ * σ₂
  let σ₄ := D.frobeniusActionConjugate KR L hLK φ σ₂
    (D.frobeniusExponent KR L hLK σ₁)
  let p₁ := fixedFieldInclusion A
    (D.frobeniusFixedField KR L hLK σ₁)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₁) π₁
  let p₃ := fixedFieldInclusion A
    (D.frobeniusFixedField KR L hLK σ₃)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₃) π₃
  let p₄ := fixedFieldInclusion A
    (D.frobeniusFixedField KR L hLK σ₄)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField KR L hLK σ₄) π₄
  let τ₁ := D.frobeniusActionRemainder KR L hLK φ σ₁
  have h₄₃ := D.frobeniusPrimeDifference_mem_infiniteUnitAddSubgroup
    A v K L hLK σ₄ σ₃ π₄ π₃ hπ₄ hπ₃
  have h₁₃ := D.frobeniusPrimeDifference_mem_infiniteUnitAddSubgroup
    A v K L hLK σ₁ σ₃ π₁ π₃ hπ₁ hπ₃
  have h₃action :=
    D.frobeniusPrime_actionDifference_mem_infiniteUnitAddSubgroup
      A v K L hLK σ₃ π₃ hπ₃ τ₁
  intro i
  fin_cases i
  · change p₄ - p₃ ∈ _
    exact h₄₃
  · change p₁ - p₃ ∈ _
    exact h₁₃
  · change p₃ - D.frobeniusQuotientAction A KR.field L hLK τ₁ p₃ ∈ _
    exact h₃action

end DegreeData

end

end Atlas.Knowledge
