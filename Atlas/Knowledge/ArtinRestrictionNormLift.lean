import Mathlib
import Atlas.Knowledge.AbelianizedRestrictionComp
import Atlas.Knowledge.IsArtinRestriction
import Atlas.Knowledge.LocalReciprocityNormNaturality

/-!
# Artin restriction of a norm lift

An upstairs Artin lift, viewed in any common algebraic closure, restricts to the finite
Artin value of the norm. The upper local field need not be normal over the base.

## Main statements

* `IsAbelianizedArtinRestriction.apply_norm_lift` — evaluate a norm using an ambient lift.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

/-- The absolute norm square evaluated on a finite normal floor
([Serre 1979, Chap. XIII, §4, Prop. 10 (a), p.197][Serre1979]). -/
theorem IsAbelianizedArtinRestriction.apply_norm_lift
    (F S M Ω : Type*) [Field F] [Field S] [Field M] [Field Ω]
    [Algebra F S] [FiniteDimensional F S]
    [Algebra F M] [Normal F M] [Algebra F Ω] [IsAlgClosure F Ω]
    [Algebra S Ω] [IsScalarTower F S Ω]
    [Algebra M Ω] [IsScalarTower F M Ω]
    [Algebra M (AlgebraicClosure F)] [IsScalarTower F M (AlgebraicClosure F)]
    [ValuativeRel F] [TopologicalSpace F] [IsMixedCharLocalField F]
    [ValuativeRel S] [TopologicalSpace S] [IsMixedCharLocalField S]
    [ValuativeExtension F S]
    {ρ : Fˣ →* Abelianization (M ≃ₐ[F] M)} (hρ : IsAbelianizedArtinRestriction F M ρ)
    {φ : Sˣ →* Field.absoluteGaloisGroupAbelianization S} (hφ : IsLocalReciprocity S φ)
    (e : AlgebraicClosure S ≃ₐ[S] Ω) (x : Sˣ)
    (σ : AlgebraicClosure S ≃ₐ[S] AlgebraicClosure S)
    (hσ : (QuotientGroup.mk σ : Field.absoluteGaloisGroupAbelianization S) = φ x) :
    ρ (normUnits F S x) = Abelianization.of
      (AlgEquiv.restrictNormalHom (F := F) M
        (AlgEquiv.autCongr (e.restrictScalars F) (σ.restrictScalars F))) := by
  obtain ⟨φF, hF, hρ⟩ := hρ
  let eF : AlgebraicClosure F ≃ₐ[F] Ω := IsAlgClosure.equiv F (AlgebraicClosure F) Ω
  let e' : AlgebraicClosure S ≃ₐ[F] AlgebraicClosure F :=
    (e.restrictScalars F).trans eF.symm
  let α := AlgEquiv.autCongr e' (σ.restrictScalars F)
  have hα := hF.norm_lift F S hφ e' x σ hσ
  have hconj : AlgEquiv.autCongr eF α =
      AlgEquiv.autCongr (e.restrictScalars F) (σ.restrictScalars F) := by
    ext a
    change eF (eF.symm (e (σ (e.symm (eF (eF.symm a)))))) = e (σ (e.symm a))
    rw [eF.apply_symm_apply, eF.apply_symm_apply]
  rw [← hρ (normUnits F S x) α hα, ← hconj]
  exact (abelianizedRestriction_autCongr F M (AlgebraicClosure F) Ω eF α).symm

end Atlas.Knowledge
