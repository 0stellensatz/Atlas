import Mathlib
import Atlas.Knowledge.FrobeniusActionRemainder
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusExponent

/-!
# Correction sum

The three correction coefficients and action elements of reciprocity
multiplicativity: their packaging, the degree-zero property of all three
actions, and the identification of the three-term difference expression
with the correction sum, the explicit left-action form of the group-ring
identity (#104).

## Main definitions

* `frobeniusMultiplicativityCorrectionTerm` — the correction
  coefficients.
* `frobeniusMultiplicativityCorrectionAction` — the correction action
  elements.

## Main statements

* `DegreeData.frobeniusMultiplicativityCorrectionAction_mem_degreeKernel`
  — all three actions have degree zero; proved.
* `frobeniusMultiplicativity_actionDifference_eq_correctionSum` — the
  correction-sum form of the group-ring identity; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling, and
the two representation declarations generalize the source's
universe-device group type to `Type u` — nothing pins them — asking only
the `[Monoid R]` that `Rep ℤ R` needs, while the action tuple sheds its
`[Group R]` entirely. The citations name this file by bare basename; it
lives at
`AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/`
in the source. The source's no-op opens go.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

universe u

namespace Atlas.Knowledge

noncomputable section

/-- **The correction coefficients**, in the order the left-action
translation of the Frobenius multiplicativity identity produces
([Yamaguchi 2026, `CorrectionSum.lean:24`][Yamaguchi2026]). -/
def frobeniusMultiplicativityCorrectionTerm
    {R : Type u} [Monoid R]
    (B : Rep ℤ R) (τ₁ : R) (p₁ p₃ p₄ : B.V) : Fin 3 → B.V :=
  ![p₄ - p₃, p₁ - p₃, p₃ - B.ρ τ₁ p₃]

/-- **The correction action elements** `τ₄, τ₁, τ₄` — the last is `τ₄`
because the product in the actual `(*)` identity is `τ₄τ₁`
([Yamaguchi 2026, `CorrectionSum.lean:32`][Yamaguchi2026]). -/
def frobeniusMultiplicativityCorrectionAction {R : Type*}
    (τ₁ τ₄ : R) : Fin 3 → R :=
  ![τ₄, τ₁, τ₄]

section correctionActionDegrees

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **All three correction actions have normalized degree zero**, as the
universal norm-descent lemma requires ([Yamaguchi 2026, `CorrectionSum.lean:44`][Yamaguchi2026]). -/
theorem frobeniusMultiplicativityCorrectionAction_mem_degreeKernel
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ σ₁ σ₂ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    let σ₄ := D.frobeniusActionConjugate K L hLK φ σ₂
      (D.frobeniusExponent K L hLK σ₁)
    let τ₁ := D.frobeniusActionRemainder K L hLK φ σ₁
    let τ₄ := D.frobeniusActionRemainder K L hLK φ σ₄
    ∀ i : Fin 3,
      frobeniusMultiplicativityCorrectionAction τ₁ τ₄ i ∈
        (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker := by
  dsimp only
  let σ₄ := D.frobeniusActionConjugate K L hLK φ σ₂
    (D.frobeniusExponent K L hLK σ₁)
  let τ₁ := D.frobeniusActionRemainder K L hLK φ σ₁
  let τ₄ := D.frobeniusActionRemainder K L hLK φ σ₄
  have hτ₁ := D.frobeniusActionRemainder_mem_degreeKernel
    K L hLK φ σ₁ hφ
  have hτ₄ := D.frobeniusActionRemainder_mem_degreeKernel
    K L hLK φ σ₄ hφ
  intro i
  fin_cases i
  · exact hτ₄
  · exact hτ₁
  · exact hτ₄

end DegreeData

end correctionActionDegrees

/-- **The explicit left-action form of the group-ring identity**, factor
order and first two terms as they occur in `(*)`
([Yamaguchi 2026, `CorrectionSum.lean:79`][Yamaguchi2026]). -/
theorem frobeniusMultiplicativity_actionDifference_eq_correctionSum
    {R : Type u} [Monoid R] (B : Rep ℤ R)
    (τ₁ τ₄ : R) (p₁ p₃ p₄ : B.V) :
    (B.ρ τ₄ p₄ - p₄) + (B.ρ τ₁ p₁ - p₁) +
        (p₃ - B.ρ (τ₄ * τ₁) p₃) =
      ∑ i : Fin 3,
        (B.ρ (frobeniusMultiplicativityCorrectionAction τ₁ τ₄ i)
          (frobeniusMultiplicativityCorrectionTerm B τ₁ p₁ p₃ p₄ i) -
          frobeniusMultiplicativityCorrectionTerm B τ₁ p₁ p₃ p₄ i) := by
  have hmul : B.ρ (τ₄ * τ₁) p₃ = B.ρ τ₄ (B.ρ τ₁ p₃) := by
    rw [map_mul]
    rfl
  rw [hmul]
  simp [frobeniusMultiplicativityCorrectionAction,
    frobeniusMultiplicativityCorrectionTerm, Fin.sum_univ_succ, map_sub]
  abel

end

end Atlas.Knowledge
