import Mathlib
import Atlas.Knowledge.AbsoluteAbelianRestriction
import Atlas.Knowledge.AbsoluteLocalArtinRestriction
import Atlas.Knowledge.CycloFieldLowerRamificationGroupEqBot
import Atlas.Knowledge.FiniteExtensionIsMixedCharLocalField
import Atlas.Knowledge.IsArithmeticFrobeniusApplyOfPowEqOne
import Atlas.Knowledge.IsFrobeniusNormalizedAbelianLocalArtinMonoidHom
import Atlas.Knowledge.IsLocalReciprocity

/-!
# power action of local reciprocity

An Artin lift of an element of nonnegative normalized valuation `n` acts on roots of unity
of order prime to the residue characteristic by the `q ^ n` power map. This extends the
uniformizer normalization to norms of uniformizers from finite extensions.

## Main statements

* `IsLocalReciprocity.frobenius_of_normalizedValuation_eq_nat` — the power action at any
  nonnegative normalized valuation.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/-- Artin lifts act on prime-to-residue-characteristic roots of unity by the residue
cardinality raised to the normalized valuation
([Serre 1979, Chap. XIII, §4, Prop. 13, p.197][Serre1979]). -/
theorem IsLocalReciprocity.frobenius_of_normalizedValuation_eq_nat
    {φ : Kˣ →* Field.absoluteGaloisGroupAbelianization K} (hφ : IsLocalReciprocity K φ)
    (u : Kˣ) (n : ℕ) (hval : normalizedValuation K u = n)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hσ : (QuotientGroup.mk σ : Field.absoluteGaloisGroupAbelianization K) = φ u)
    (m : ℕ) (hm : Nat.Coprime m (Nat.card 𝓀[K]))
    (ζ : AlgebraicClosure K) (hζ : ζ ^ m = 1) :
    σ ζ = ζ ^ (Nat.card 𝓀[K] ^ n) := by
  have hcanonical := hφ.unique (isLocalReciprocity_absoluteLocalArtinMonoidHom K)
  rw [hcanonical] at hσ
  have hq1 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hm
    omega
  haveI : NeZero m := ⟨hm0⟩
  let E := cycloField K m
  let N := absoluteAbelianRestrictionKernel K E
  let F := absoluteFiniteQuotientField K N
  have hfield : F = E := absoluteFiniteQuotientField_restrictionKernel K E
  have hζF : ζ ∈ F := hfield ▸ mem_cycloField K hm0 hζ
  have hbotF : lowerRamificationGroup K F 0 = ⊥ := by
    rw [hfield]
    exact cycloField_lowerRamificationGroup_eq_bot K hm
  have hres : AlgEquiv.restrictNormalHom F σ = abelianLocalArtinMonoidHom K F u :=
    restrictNormalHom_absoluteLocalArtinMonoidHom_lift K N u σ hσ
  obtain ⟨vF, tF, hVF, _, hmixed⟩ := exists_extension_isMixedCharLocalField K F
  letI := vF
  letI := tF
  letI := hVF
  letI := hmixed
  let τ := unramifiedFrobeniusRealizationOfEmbedding K F IsAlgClosed.lift
  have hτ : IsArithmeticFrobenius K F τ :=
    isArithmeticFrobenius_unramifiedFrobeniusRealizationOfEmbedding K F IsAlgClosed.lift
  have hform : abelianLocalArtinMonoidHom K F u = τ ^ n := by
    rw [isFrobeniusNormalized_abelianLocalArtinMonoidHom K F hbotF τ hτ u,
      hval, zpow_natCast]
  let z : F := ⟨ζ, hζF⟩
  have hz : z ^ m = 1 := Subtype.ext hζ
  have hact : ∀ j : ℕ, (τ ^ j) z = z ^ (Nat.card 𝓀[K] ^ j) := by
    intro j
    induction j with
    | zero => simp only [pow_zero, AlgEquiv.one_apply, pow_one]
    | succ j ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow,
        hτ.apply_of_pow_eq_one hm hz, ← pow_mul, ← pow_succ']
  have hcomm : ((AlgEquiv.restrictNormalHom F σ z : F) : AlgebraicClosure K) = σ ζ :=
    AlgEquiv.restrictNormal_commutes σ F z
  rw [← hcomm, hres, hform, hact]
  rfl

end Atlas.Knowledge
