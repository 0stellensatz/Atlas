import Mathlib
import Atlas.Knowledge.FiniteExtensionIsMixedCharLocalField
import Atlas.Knowledge.IsArtinRestriction
import Atlas.Knowledge.LocalReciprocityNormNaturality

/-!
# norms in an Artin restriction kernel

A finite Galois Artin restriction kills norms from its upper field, including when that
field is nonabelian over the base. The absolute norm square supplies a lift fixing the
upper field pointwise.

## Main statements

* `IsAbelianizedArtinRestriction.apply_norm` — upper-field norms map to the identity.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
  [Algebra L (AlgebraicClosure K)] [IsScalarTower K L (AlgebraicClosure K)]

/-- Finite Galois Artin restrictions annihilate field norms
([Serre 1979, Chap. XIII, §4, Prop. 10 (a), p.197][Serre1979]). -/
theorem IsAbelianizedArtinRestriction.apply_norm
    {ρ : Kˣ →* Abelianization (L ≃ₐ[K] L)} (hρ : IsAbelianizedArtinRestriction K L ρ)
    (y : Lˣ) : ρ (normUnits K L y) = 1 := by
  obtain ⟨φK, hK, hρ⟩ := hρ
  obtain ⟨vL, tL, hVL, _, hmixed⟩ := exists_extension_isMixedCharLocalField K L
  letI := vL
  letI := tL
  letI := hVL
  letI := hmixed
  letI : Algebra.IsAlgebraic L (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := K) L
  letI : IsAlgClosure L (AlgebraicClosure K) := ⟨inferInstance, inferInstance⟩
  let e : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure K :=
    IsAlgClosure.equiv L (AlgebraicClosure L) (AlgebraicClosure K)
  obtain ⟨φL, hL⟩ := exists_isLocalReciprocity L
  obtain ⟨τ₀, hτ⟩ := QuotientGroup.mk_surjective (φL y)
  let τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L := τ₀
  let σ := AlgEquiv.autCongr (e.restrictScalars K) (τ.restrictScalars K)
  have hσ : (QuotientGroup.mk σ : Field.absoluteGaloisGroupAbelianization K) =
      φK (normUnits K L y) := hK.norm_lift K L hL (e.restrictScalars K) y τ hτ
  have hfix : AlgEquiv.restrictNormalHom (F := K) L σ = 1 := by
    ext a
    apply (algebraMap L (AlgebraicClosure K)).injective
    change algebraMap L (AlgebraicClosure K) (σ.restrictNormal L a) =
      algebraMap L (AlgebraicClosure K) a
    rw [AlgEquiv.restrictNormal_commutes]
    change e (τ (e.symm (algebraMap L (AlgebraicClosure K) a))) =
      algebraMap L (AlgebraicClosure K) a
    rw [e.symm.commutes, τ.commutes, e.commutes]
  rw [← hρ (normUnits K L y) σ hσ, hfix, map_one]

end Atlas.Knowledge
