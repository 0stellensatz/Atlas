import Mathlib
import Atlas.Knowledge.ArtinRestrictionNormLift
import Atlas.Knowledge.SemilinearAutCongr

/-!
# Artin restriction under field isomorphisms

Compatible isomorphisms of a local base and a normal extension transport the Artin
restriction. The absolute norm square proves the assertion for the isomorphic base change.

## Main statements

* `IsAbelianizedArtinRestriction.equiv` — transport through compatible field isomorphisms.
* `normUnits_eq_symm_of_algEquiv` — the norm of an isomorphic extension is its inverse map.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

noncomputable section

/-- The norm in a degree-one extension is the inverse of its structural isomorphism. -/
theorem normUnits_eq_symm_of_algEquiv
    {E F : Type*} [Field E] [Field F] [Algebra E F] (τ : E ≃ₐ[E] F) (x : Fˣ) :
    normUnits E F x = Units.map τ.symm.toMonoidHom x := by
  apply Units.ext
  change Algebra.norm E (x : F) = τ.symm (x : F)
  simpa only [Algebra.norm_self, MonoidHom.id_apply] using
    (Algebra.norm_eq_of_algEquiv τ.symm (x : F)).symm

/-- Compatible base and upper-field isomorphisms transport the Artin restriction
([Serre 1979, Chap. XIII, §4, Prop. 10 (a), p.197][Serre1979]). -/
theorem IsAbelianizedArtinRestriction.equiv
    (E F M N : Type*) [Field E] [Field F] [Field M] [Field N]
    [Algebra E F] [FiniteDimensional E F] [Algebra E M] [Normal E M]
    [Algebra F N] [Normal F N] [Algebra E N] [IsScalarTower E F N]
    [Algebra M (AlgebraicClosure E)] [IsScalarTower E M (AlgebraicClosure E)]
    [Algebra N (AlgebraicClosure F)] [IsScalarTower F N (AlgebraicClosure F)]
    [ValuativeRel E] [TopologicalSpace E] [IsMixedCharLocalField E]
    [ValuativeRel F] [TopologicalSpace F] [IsMixedCharLocalField F] [ValuativeExtension E F]
    (τ : E ≃ₐ[E] F) (μ : M ≃ₐ[E] N)
    {ρ : Eˣ →* Abelianization (M ≃ₐ[E] M)} (hρ : IsAbelianizedArtinRestriction E M ρ) :
    let hμ : ∀ a, μ (algebraMap E M a) = algebraMap F N (τ a) := fun a => by
      have ht : τ a = algebraMap E F a := τ.commutes a
      exact (μ.commutes a).trans ((IsScalarTower.algebraMap_apply E F N a).trans
        (congrArg (algebraMap F N) ht.symm))
    IsAbelianizedArtinRestriction F N
      ((semilinearAutCongr τ.toRingEquiv μ.toRingEquiv hμ).abelianizationCongr.toMonoidHom.comp
        (ρ.comp (normUnits E F))) := by
  let hμ : ∀ a, μ (algebraMap E M a) = algebraMap F N (τ a) := fun a => by
    have ht : τ a = algebraMap E F a := τ.commutes a
    exact (μ.commutes a).trans ((IsScalarTower.algebraMap_apply E F N a).trans
      (congrArg (algebraMap F N) ht.symm))
  let d := semilinearAutCongr τ.toRingEquiv μ.toRingEquiv hμ
  obtain ⟨φE, hE, hρ⟩ := hρ
  obtain ⟨φF, hF⟩ := exists_isLocalReciprocity F
  refine ⟨φF, hF, ?_⟩
  intro x σ hσ
  letI : IsScalarTower E N (AlgebraicClosure F) := IsScalarTower.to₁₃₄ E F N (AlgebraicClosure F)
  letI : Algebra M (AlgebraicClosure F) :=
    ((algebraMap N (AlgebraicClosure F)).comp μ.toRingHom).toAlgebra
  letI : IsScalarTower E M (AlgebraicClosure F) := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap E (AlgebraicClosure F) a =
      algebraMap N (AlgebraicClosure F) (μ (algebraMap E M a))
    rw [μ.commutes, IsScalarTower.algebraMap_apply E N (AlgebraicClosure F)]
  let e : AlgebraicClosure F ≃ₐ[E] AlgebraicClosure E :=
    IsAlgClosure.equiv E (AlgebraicClosure F) (AlgebraicClosure E)
  have hσE := hE.norm_lift E F hF e x σ hσ
  have hr : d (AlgEquiv.restrictNormalHom (F := E) M (σ.restrictScalars E)) =
      AlgEquiv.restrictNormalHom (F := F) N σ := by
    ext a
    apply (algebraMap N (AlgebraicClosure F)).injective
    change algebraMap N (AlgebraicClosure F)
      (μ ((σ.restrictScalars E).restrictNormal M (μ.symm a))) =
        algebraMap N (AlgebraicClosure F) (σ.restrictNormal N a)
    calc
      _ = σ (algebraMap N (AlgebraicClosure F) (μ (μ.symm a))) :=
        AlgEquiv.restrictNormal_commutes (σ.restrictScalars E) M (μ.symm a)
      _ = σ (algebraMap N (AlgebraicClosure F) a) := by rw [μ.apply_symm_apply]
      _ = _ := (AlgEquiv.restrictNormal_commutes σ N a).symm
  change Abelianization.of (AlgEquiv.restrictNormalHom (F := F) N σ) =
    d.abelianizationCongr (ρ (normUnits E F x))
  rw [← hρ (normUnits E F x) (AlgEquiv.autCongr e (σ.restrictScalars E)) hσE,
    abelianizedRestriction_autCongr E M (AlgebraicClosure F) (AlgebraicClosure E),
    abelianizationCongr_of, hr]

end

end Atlas.Knowledge
