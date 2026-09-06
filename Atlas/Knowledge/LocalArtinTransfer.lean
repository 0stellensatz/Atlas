import Mathlib
import Atlas.Knowledge.AbstractFixedFieldArtinRestriction
import Atlas.Knowledge.AbstractFixedFieldTransferComparison
import Atlas.Knowledge.ArtinRestrictionEquiv
import Atlas.Knowledge.LocalClassFieldAxiom
import Atlas.Knowledge.UnitCohomologyDischarge

/-!
# local Artin transfer

The transfer square for arbitrary finite Galois towers follows from the abstract
transfer square, the intrinsic comparison on fixed fields, and invariance under
compatible field isomorphisms. The intermediate field need not be normal.

## Main statements

* `localArtinTransfer` — local Artin restrictions intertwine transfer and unit inclusion.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

noncomputable section

set_option maxHeartbeats 1200000 in
-- The comparison carries the intrinsic and fixed-field scalar structures through the tower.
/-- Transfer of local Artin restrictions is induced by inclusion of the base units
([Serre 1979, Chap. XIII, §4, Prop. 10 (b), p.197][Serre1979]). -/
theorem localArtinTransfer
    (K E M : Type*) [Field K] [Field E] [Field M]
    [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]
    [FiniteDimensional K M] [IsGalois K M] [IsGalois E M]
    [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
    [ValuativeRel E] [TopologicalSpace E] [IsMixedCharLocalField E] [ValuativeExtension K E]
    [Algebra M (AlgebraicClosure K)] [IsScalarTower K M (AlgebraicClosure K)]
    [Algebra M (AlgebraicClosure E)] [IsScalarTower E M (AlgebraicClosure E)]
    (artK : Kˣ →* Abelianization (M ≃ₐ[K] M))
    (artE : Eˣ →* Abelianization (M ≃ₐ[E] M))
    (hK : IsAbelianizedArtinRestriction K M artK)
    (hE : IsAbelianizedArtinRestriction E M artE) (x : Kˣ) :
    abelianizedTransferOfInjective
      (AlgEquiv.restrictScalarsHom (S := E) (A := M) K) (AlgEquiv.restrictScalars_injective K)
        (artK x) = artE (Units.map (algebraMap K E : K →* E) x) := by
  let Ω := AlgebraicClosure K
  letI : Algebra E Ω := ((algebraMap M Ω).comp (algebraMap E M)).toAlgebra
  letI : IsScalarTower E M Ω := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K E Ω := IsScalarTower.to₁₂₄ K E M Ω
  letI : FiniteDimensional K E := FiniteDimensional.left K E M
  let iE := IsScalarTower.toAlgHom K E Ω
  let iM := IsScalarTower.toAlgHom K M Ω
  let A₀ : IntermediateField K Ω := ⊥
  let A₁ := iE.fieldRange
  let A₂ := iM.fieldRange
  letI : FiniteDimensional K A₁ := (AlgEquiv.ofInjectiveField iE).toLinearEquiv.finiteDimensional
  letI : FiniteDimensional K A₂ := (AlgEquiv.ofInjectiveField iM).toLinearEquiv.finiteDimensional
  letI : IsGalois K A₂ := IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField iM)
  let H₀ := closedFixingSubgroup A₀
  let H₁ := closedFixingSubgroup A₁
  let L := closedFixingSubgroup A₂
  have h10 : H₁.toSubgroup ≤ H₀.toSubgroup := fixingSubgroupLeBase K Ω A₁
  have h21 : L.toSubgroup ≤ H₁.toSubgroup := by
    apply IntermediateField.fixingSubgroup_le
    rintro a ⟨b, rfl⟩
    exact ⟨algebraMap E M b, rfl⟩
  letI : (L.toSubgroup.subgroupOf H₀.toSubgroup).Normal := inferInstance
  letI : Finite (H₀.toSubgroup ⧸ L.toSubgroup.subgroupOf H₀.toSubgroup) :=
    baseFixingExtensionQuotient_finite_of_isSeparable K Ω A₂
  letI : Finite ((baseField (Ω ≃ₐ[K] Ω)).toSubgroup ⧸
      H₀.toSubgroup.subgroupOf (baseField (Ω ≃ₐ[K] Ω)).toSubgroup) := by
    rw [show H₀ = baseField (Ω ≃ₐ[K] Ω) from closedFixingSubgroup_bot_eq_baseField K Ω]
    exact (FiniteAbstractField.base (Ω ≃ₐ[K] Ω)).finite
  letI : Finite ((baseField (Ω ≃ₐ[K] Ω)).toSubgroup ⧸
      H₁.toSubgroup.subgroupOf (baseField (Ω ≃ₐ[K] Ω)).toSubgroup) := by
    rw [← closedFixingSubgroup_bot_eq_baseField K Ω]
    exact baseFixingExtensionQuotient_finite_of_isSeparable K Ω A₁
  letI : (L.toSubgroup.subgroupOf H₁.toSubgroup).Normal :=
    transferNormNaturality_intermediateExtension_normal H₀ H₁ L h10
  letI : Finite (H₁.toSubgroup ⧸ L.toSubgroup.subgroupOf H₁.toSubgroup) :=
    finite_extension_over_intermediate (h21.trans h10) h10 h21
  let B₀ : FiniteAbstractField (Ω ≃ₐ[K] Ω) := ⟨H₀, inferInstance⟩
  let B₁ : FiniteAbstractField (Ω ≃ₐ[K] Ω) := ⟨H₁, inferInstance⟩
  let L₀ : FiniteGaloisSubextension B₀.field := ⟨L, h21.trans h10, inferInstance, inferInstance⟩
  let L₁ : FiniteGaloisSubextension B₁.field := ⟨L, h21, inferInstance, inferInstance⟩
  let F₀ := abstractFixedField K Ω H₀
  let F₁ := abstractFixedField K Ω H₁
  let N := abstractFixedField K Ω L
  let τ₀ : K ≃ₐ[K] F₀ := (IntermediateField.botEquiv K Ω).symm.trans
    (IntermediateField.equivOfEq (InfiniteGalois.fixedField_fixingSubgroup A₀).symm)
  let τ₁ : E ≃ₐ[K] F₁ := (AlgEquiv.ofInjectiveField iE).trans
    (IntermediateField.equivOfEq (InfiniteGalois.fixedField_fixingSubgroup A₁).symm)
  let μ : M ≃ₐ[K] N := (AlgEquiv.ofInjectiveField iM).trans
    (IntermediateField.equivOfEq (InfiniteGalois.fixedField_fixingSubgroup A₂).symm)
  letI : FiniteDimensional K F₀ := τ₀.toLinearEquiv.finiteDimensional
  letI : FiniteDimensional K F₁ := τ₁.toLinearEquiv.finiteDimensional
  letI : FiniteDimensional K N := μ.toLinearEquiv.finiteDimensional
  letI : Algebra F₀ F₁ :=
    (IntermediateField.inclusion (abstractFixedField_le K Ω h10)).toRingHom.toAlgebra
  letI : Algebra F₀ N :=
    (IntermediateField.inclusion (abstractFixedField_le K Ω (h21.trans h10))).toRingHom.toAlgebra
  letI : Algebra F₁ N :=
    (IntermediateField.inclusion (abstractFixedField_le K Ω h21)).toRingHom.toAlgebra
  letI : IsScalarTower F₀ F₁ N := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K F₀ F₁ := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K F₀ N := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K F₁ N := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional F₀ N := FiniteDimensional.right K F₀ N
  letI : FiniteDimensional F₁ N := FiniteDimensional.right K F₁ N
  letI : IsGalois F₀ N := abstractRelativeFixedField_isGalois K Ω H₀ L (h21.trans h10) inferInstance
  letI : IsGalois F₁ N := abstractRelativeFixedField_isGalois K Ω H₁ L h21 inferInstance
  obtain ⟨v₀, t₀, hV₀, _, hF₀⟩ := exists_extension_isMixedCharLocalField K F₀
  letI := v₀
  letI := t₀
  letI := hV₀
  letI := hF₀
  letI : Algebra E F₁ := τ₁.toRingHom.toAlgebra
  let τ₁E : E ≃ₐ[E] F₁ := { τ₁.toRingEquiv with commutes' := fun _ => rfl }
  letI : FiniteDimensional E F₁ := τ₁E.toLinearEquiv.finiteDimensional
  letI : IsScalarTower K E F₁ := IsScalarTower.of_algebraMap_eq fun a => (τ₁.commutes a).symm
  obtain ⟨v₁, t₁, hV₁, _, hF₁⟩ := exists_extension_isMixedCharLocalField E F₁
  letI := v₁
  letI := t₁
  letI := hV₁
  letI := hF₁
  letI : ValuativeExtension K F₁ := valuativeExtension_trans K E F₁
  letI : Algebra E N := (μ.toRingHom.comp (algebraMap E M)).toAlgebra
  let μE : M ≃ₐ[E] N := { μ.toRingEquiv with commutes' := fun _ => rfl }
  letI : IsScalarTower E F₁ N := IsScalarTower.of_algebraMap_eq fun a => by
    apply N.val.injective
    change (μ (algebraMap E M a) : Ω) = (τ₁ a : Ω)
    rfl
  letI : Module.IsTorsionFree F₀ N :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap F₀ N).injective
  letI : Module.IsTorsionFree F₁ N :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap F₁ N).injective
  letI : Module.IsTorsionFree F₀ (AlgebraicClosure F₀) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (algebraMap F₀ (AlgebraicClosure F₀)).injective
  letI : Module.IsTorsionFree F₁ (AlgebraicClosure F₁) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (algebraMap F₁ (AlgebraicClosure F₁)).injective
  let j₀ : N →ₐ[F₀] AlgebraicClosure F₀ := IsAlgClosed.lift
  letI : Algebra N (AlgebraicClosure F₀) := j₀.toRingHom.toAlgebra
  letI : IsScalarTower F₀ N (AlgebraicClosure F₀) :=
    IsScalarTower.of_algebraMap_eq fun a => (j₀.commutes a).symm
  let j₁ : N →ₐ[F₁] AlgebraicClosure F₁ := IsAlgClosed.lift
  letI : Algebra N (AlgebraicClosure F₁) := j₁.toRingHom.toAlgebra
  letI : IsScalarTower F₁ N (AlgebraicClosure F₁) :=
    IsScalarTower.of_algebraMap_eq fun a => (j₁.commutes a).symm
  let hμ₀ : ∀ a, μ (algebraMap K M a) = algebraMap F₀ N (τ₀ a) := fun a => by
    have ht : τ₀ a = algebraMap K F₀ a := τ₀.commutes a
    exact (μ.commutes a).trans ((IsScalarTower.algebraMap_apply K F₀ N a).trans
      (congrArg (algebraMap F₀ N) ht.symm))
  let hμ₁ : ∀ a, μE (algebraMap E M a) = algebraMap F₁ N (τ₁E a) := fun a => by
    exact IsScalarTower.algebraMap_apply E F₁ N a
  let d₀ := semilinearAutCongr τ₀.toRingEquiv μ.toRingEquiv hμ₀
  let d₁ := semilinearAutCongr τ₁E.toRingEquiv μE.toRingEquiv hμ₁
  let ρ₀ := d₀.abelianizationCongr.toMonoidHom.comp (artK.comp (normUnits K F₀))
  let ρ₁ := d₁.abelianizationCongr.toMonoidHom.comp (artE.comp (normUnits E F₁))
  have hρ₀ : IsAbelianizedArtinRestriction F₀ N ρ₀ := hK.equiv K F₀ M N τ₀ μ
  have hρ₁ : IsAbelianizedArtinRestriction F₁ N ρ₁ := hE.equiv E F₁ M N τ₁E μE
  let a := Units.map τ₀.toMonoidHom x
  let inc := Units.map (algebraMap F₀ F₁ : F₀ →* F₁)
  have hn₀ : normUnits K F₀ a = x := by
    rw [normUnits_eq_symm_of_algEquiv τ₀]
    apply Units.ext
    exact τ₀.symm_apply_apply (x : K)
  have ha₁ : inc a = Units.map τ₁E.toMonoidHom (Units.map (algebraMap K E : K →* E) x) := by
    apply Units.ext
    apply F₁.val.injective
    change algebraMap K Ω (x : K) = algebraMap E Ω (algebraMap K E (x : K))
    exact IsScalarTower.algebraMap_apply K E Ω (x : K)
  have hn₁ : normUnits E F₁ (inc a) = Units.map (algebraMap K E : K →* E) x := by
    rw [ha₁, normUnits_eq_symm_of_algEquiv τ₁E]
    apply Units.ext
    exact τ₁E.symm_apply_apply _
  let hcf := algebraicClosureUnits_satisfiesClassFieldAxiom K
  let hAxiom := localHenselianValuation_satisfiesUnramifiedUnitCohomology K
  letI : Algebra (abstractRelativeFixedField K (AlgebraicClosure K) L₀.below)
      (AlgebraicClosure (abstractFixedField K (AlgebraicClosure K) B₀.field)) :=
    j₀.toRingHom.toAlgebra
  letI : IsScalarTower (abstractFixedField K (AlgebraicClosure K) B₀.field)
      (abstractRelativeFixedField K (AlgebraicClosure K) L₀.below)
      (AlgebraicClosure (abstractFixedField K (AlgebraicClosure K) B₀.field)) :=
    IsScalarTower.of_algebraMap_eq fun a => (j₀.commutes a).symm
  letI : Algebra (abstractRelativeFixedField K (AlgebraicClosure K) L₁.below)
      (AlgebraicClosure (abstractFixedField K (AlgebraicClosure K) B₁.field)) :=
    j₁.toRingHom.toAlgebra
  letI : IsScalarTower (abstractFixedField K (AlgebraicClosure K) B₁.field)
      (abstractRelativeFixedField K (AlgebraicClosure K) L₁.below)
      (AlgebraicClosure (abstractFixedField K (AlgebraicClosure K) B₁.field)) :=
    IsScalarTower.of_algebraMap_eq fun a => (j₁.commutes a).symm
  have hleft := abstractFixedFieldArtinRestriction K B₀ L₀ hcf hAxiom ρ₀ hρ₀ a
  have hright := abstractFixedFieldArtinRestriction K B₁ L₁ hcf hAxiom ρ₁ hρ₁ (inc a)
  have hsquare := DFunLike.congr_fun (abstractFixedFieldNormResidueSymbol_transfer_inclusion
    K Ω (localResidueDatum K) (localHenselianValuation K) hcf hAxiom H₀ H₁ L h21 h10)
      (Additive.ofMul a)
  change abstractFixedFieldAbelianizedTransfer K Ω H₀ H₁ L h21 h10
      (abstractFixedFieldNormResidueSymbol K Ω (localResidueDatum K)
        (localHenselianValuation K) hcf hAxiom H₀ L (h21.trans h10) (Additive.ofMul a)) =
    abstractFixedFieldNormResidueSymbol K Ω (localResidueDatum K)
      (localHenselianValuation K) hcf hAxiom H₁ L h21 (Additive.ofMul (inc a)) at hsquare
  rw [hleft, hright, abstractFixedFieldTransferComparison] at hsquare
  let i := AlgEquiv.restrictScalarsHom (S := E) (A := M) K
  let j := AlgEquiv.restrictScalarsHom (S := F₁) (A := N) F₀
  have hs : abelianizedTransferOfInjective j (AlgEquiv.restrictScalars_injective F₀)
      (d₀.abelianizationCongr (artK x)) =
      d₁.abelianizationCongr (artE (Units.map (algebraMap K E : K →* E) x)) := by
    have h := congrArg Additive.toMul hsquare
    change abelianizedTransferOfInjective j (AlgEquiv.restrictScalars_injective F₀)
      (d₀.abelianizationCongr (artK (normUnits K F₀ a))) =
      d₁.abelianizationCongr (artE (normUnits E F₁ (inc a))) at h
    rwa [hn₀, hn₁] at h
  have hcomm (σ : M ≃ₐ[E] M) : d₀ (i σ) = j (d₁ σ) := by
    ext b
    rfl
  have hn := abelianizedTransferOfInjective_natural i (AlgEquiv.restrictScalars_injective K)
    j (AlgEquiv.restrictScalars_injective F₀) d₀ d₁ hcomm (artK x)
  exact d₁.abelianizationCongr.injective (hn.symm.trans hs)

end

end Atlas.Knowledge
