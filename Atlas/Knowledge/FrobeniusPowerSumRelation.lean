import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.FrobeniusActionRemainder
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusExponent
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.FrobeniusQuotientAction
import Atlas.Knowledge.FrobeniusQuotientDescent
import Atlas.Knowledge.FrobeniusSemigroup
import Atlas.Knowledge.MaximalUnramifiedField

/-!
# Frobenius power-sum relation

The three-term action identity from the Frobenius action remainders and
their fixed-field primes: the combination `s₄ + s₁ - s₃` of the three
power sums has its `φ`-difference equal to the remainder differences of
`σ₄` and `σ₁` plus the reversed difference for the product, whose
remainder splits as `τ₄τ₁` (#104).

## Main statements

* `DegreeData.frobeniusPowerSum_mul_action_sub` — the three-term action
  identity; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling, and
the ambient group is `Type u` since the #104 hoist. The citations name
this file by bare basename; it lives at
`AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/`
in the source. The source's no-op opens go.

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

/-- **The three Frobenius power sums attached to `σ₁`, `σ₁σ₂`, and the
left-action conjugate of `σ₂` satisfy the action-difference relation
universal norm descent consumes** (Yamaguchi 2026,
`FrobeniusPowerSumRelation.lean:28`). -/
theorem frobeniusPowerSum_mul_action_sub (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ σ₁ σ₂ : D.FrobeniusElements K L hLK)
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
    let p₁ := fixedFieldInclusion A
      (D.frobeniusFixedField K L hLK σ₁)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField K L hLK σ₁) π₁
    let p₃ := fixedFieldInclusion A
      (D.frobeniusFixedField K L hLK σ₃)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField K L hLK σ₃) π₃
    let p₄ := fixedFieldInclusion A
      (D.frobeniusFixedField K L hLK σ₄)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField K L hLK σ₄) π₄
    let τ₁ := D.frobeniusActionRemainder K L hLK φ σ₁
    let τ₄ := D.frobeniusActionRemainder K L hLK φ σ₄
    let u := D.frobeniusPowerSum A K.field L hLK φ.1
        (D.frobeniusExponent K L hLK σ₄) p₄ +
      D.frobeniusPowerSum A K.field L hLK φ.1
        (D.frobeniusExponent K L hLK σ₁) p₁ -
      D.frobeniusPowerSum A K.field L hLK φ.1
        (D.frobeniusExponent K L hLK σ₃) p₃
    D.frobeniusQuotientAction A K.field L hLK φ.1 u - u =
      (D.frobeniusQuotientAction A K.field L hLK τ₄ p₄ - p₄) +
      (D.frobeniusQuotientAction A K.field L hLK τ₁ p₁ - p₁) +
      (p₃ - D.frobeniusQuotientAction A K.field L hLK (τ₄ * τ₁) p₃) := by
  let σ₃ := σ₁ * σ₂
  let σ₄ := D.frobeniusActionConjugate K L hLK φ σ₂
    (D.frobeniusExponent K L hLK σ₁)
  let p₁ := fixedFieldInclusion A
    (D.frobeniusFixedField K L hLK σ₁)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ₁) π₁
  let p₃ := fixedFieldInclusion A
    (D.frobeniusFixedField K L hLK σ₃)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ₃) π₃
  let p₄ := fixedFieldInclusion A
    (D.frobeniusFixedField K L hLK σ₄)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ₄) π₄
  let s₁ := D.frobeniusPowerSum A K.field L hLK φ.1
    (D.frobeniusExponent K L hLK σ₁) p₁
  let s₃ := D.frobeniusPowerSum A K.field L hLK φ.1
    (D.frobeniusExponent K L hLK σ₃) p₃
  let s₄ := D.frobeniusPowerSum A K.field L hLK φ.1
    (D.frobeniusExponent K L hLK σ₄) p₄
  let τ₁ := D.frobeniusActionRemainder K L hLK φ σ₁
  let τ₃ := D.frobeniusActionRemainder K L hLK φ σ₃
  let τ₄ := D.frobeniusActionRemainder K L hLK φ σ₄
  have h₁ :
      D.frobeniusQuotientAction A K.field L hLK τ₁ p₁ =
        D.frobeniusQuotientAction A K.field L hLK
          (φ.1 ^ D.frobeniusExponent K L hLK σ₁) p₁ := by
    exact D.frobeniusActionRemainder_apply_fixedField
      A K L hLK φ σ₁ π₁
  have h₃ :
      D.frobeniusQuotientAction A K.field L hLK τ₃ p₃ =
        D.frobeniusQuotientAction A K.field L hLK
          (φ.1 ^ D.frobeniusExponent K L hLK σ₃) p₃ := by
    exact D.frobeniusActionRemainder_apply_fixedField
      A K L hLK φ σ₃ π₃
  have h₄ :
      D.frobeniusQuotientAction A K.field L hLK τ₄ p₄ =
        D.frobeniusQuotientAction A K.field L hLK
          (φ.1 ^ D.frobeniusExponent K L hLK σ₄) p₄ := by
    exact D.frobeniusActionRemainder_apply_fixedField
      A K L hLK φ σ₄ π₄
  have hτ : τ₃ = τ₄ * τ₁ := by
    exact D.frobeniusActionRemainder_mul K L hLK φ σ₁ σ₂
  change
    D.frobeniusQuotientAction A K.field L hLK φ.1
          (s₄ + s₁ - s₃) - (s₄ + s₁ - s₃) =
      (D.frobeniusQuotientAction A K.field L hLK τ₄ p₄ - p₄) +
        (D.frobeniusQuotientAction A K.field L hLK τ₁ p₁ - p₁) +
        (p₃ -
          D.frobeniusQuotientAction A K.field L hLK (τ₄ * τ₁) p₃)
  have hmap :
      D.frobeniusQuotientAction A K.field L hLK φ.1 (s₄ + s₁ - s₃) =
        D.frobeniusQuotientAction A K.field L hLK φ.1 s₄ +
          D.frobeniusQuotientAction A K.field L hLK φ.1 s₁ -
          D.frobeniusQuotientAction A K.field L hLK φ.1 s₃ := by
    change
      D.frobeniusQuotientActionLinearMap A K.field L hLK φ.1
          (s₄ + s₁ - s₃) =
        D.frobeniusQuotientActionLinearMap A K.field L hLK φ.1 s₄ +
          D.frobeniusQuotientActionLinearMap A K.field L hLK φ.1 s₁ -
          D.frobeniusQuotientActionLinearMap A K.field L hLK φ.1 s₃
    rw [map_sub, map_add]
  rw [hmap]
  calc
    _ =
        (D.frobeniusQuotientAction A K.field L hLK φ.1 s₄ - s₄) +
          (D.frobeniusQuotientAction A K.field L hLK φ.1 s₁ - s₁) -
          (D.frobeniusQuotientAction A K.field L hLK φ.1 s₃ - s₃) := by
      abel
    _ =
        (D.frobeniusQuotientAction A K.field L hLK
            (φ.1 ^ D.frobeniusExponent K L hLK σ₄) p₄ - p₄) +
          (D.frobeniusQuotientAction A K.field L hLK
            (φ.1 ^ D.frobeniusExponent K L hLK σ₁) p₁ - p₁) -
          (D.frobeniusQuotientAction A K.field L hLK
            (φ.1 ^ D.frobeniusExponent K L hLK σ₃) p₃ - p₃) := by
      dsimp only [s₁, s₃, s₄]
      rw [D.frobeniusPowerSum_action_sub,
        D.frobeniusPowerSum_action_sub,
        D.frobeniusPowerSum_action_sub]
    _ =
        (D.frobeniusQuotientAction A K.field L hLK τ₄ p₄ - p₄) +
          (D.frobeniusQuotientAction A K.field L hLK τ₁ p₁ - p₁) +
          (p₃ -
            D.frobeniusQuotientAction A K.field L hLK (τ₄ * τ₁) p₃) := by
      rw [← h₄, ← h₁, ← h₃, hτ]
      abel

end DegreeData

end

end Atlas.Knowledge
