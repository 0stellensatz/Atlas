import Mathlib
import Atlas.Knowledge.AbstractFixedFieldGaloisRestriction
import Atlas.Knowledge.AbstractFixedFieldNormResidueSymbol
import Atlas.Knowledge.AbstractFixedFieldRelativeNorm
import Atlas.Knowledge.ArtinRestrictionNormKernel
import Atlas.Knowledge.ArtinRestrictionNormLift
import Atlas.Knowledge.ArtinUniformizerResidueDegree
import Atlas.Knowledge.LocalFixedFieldIntrinsicDegree
import Atlas.Knowledge.NormResidueSymbolPrimeCharacterization

/-!
# intrinsic Artin restriction on an abstract fixed field

The norm-residue symbol induced by the original local class formation is the intrinsic
Artin restriction of each finite fixed field. Norms vanish by the absolute norm square;
prime norms are read using the residue degree of an Artin uniformizer.

## Main statements

* `abstractFixedFieldArtinRestriction` — the induced symbol equals the intrinsic restriction.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

noncomputable section

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]
  (H : FiniteAbstractField (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
  (L : FiniteGaloisSubextension H.field)
  [ValuativeRel (abstractFixedField K (AlgebraicClosure K) H.field)]
  [TopologicalSpace (abstractFixedField K (AlgebraicClosure K) H.field)]
  [IsMixedCharLocalField (abstractFixedField K (AlgebraicClosure K) H.field)]
  [ValuativeExtension K (abstractFixedField K (AlgebraicClosure K) H.field)]

variable [Finite ((baseField (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)).toSubgroup ⧸
    H.field.toSubgroup.subgroupOf
      (baseField (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)).toSubgroup)]
  [Finite (H.field.toSubgroup ⧸ L.field.toSubgroup.subgroupOf H.field.toSubgroup)]

local instance : CompactSpace (Field.absoluteGaloisGroup K) :=
  inferInstanceAs (CompactSpace (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))

local instance : TotallyDisconnectedSpace (Field.absoluteGaloisGroup K) :=
  inferInstanceAs (TotallyDisconnectedSpace (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))

local instance : T2Space (Field.absoluteGaloisGroup K) :=
  inferInstanceAs (T2Space (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))

local instance : IsGalois (abstractFixedField K (AlgebraicClosure K) H.field)
    (abstractRelativeFixedField K (AlgebraicClosure K) L.below) :=
  abstractRelativeFixedField_isGalois K (AlgebraicClosure K) H.field L.field L.below L.normal

variable [Algebra (abstractRelativeFixedField K (AlgebraicClosure K) L.below)
    (AlgebraicClosure (abstractFixedField K (AlgebraicClosure K) H.field))]
  [IsScalarTower (abstractFixedField K (AlgebraicClosure K) H.field)
    (abstractRelativeFixedField K (AlgebraicClosure K) L.below)
    (AlgebraicClosure (abstractFixedField K (AlgebraicClosure K) H.field))]

set_option maxHeartbeats 800000 in
-- The prime-norm comparison unfolds nested fixed fields and both absolute Galois presentations.
/-- The abstract symbol at a finite fixed field is its intrinsic Artin restriction.
This generalizes the abelian-floor comparison in Yamaguchi 2026,
`FixedFieldIntrinsicReciprocity/AmbientPrimeComparison.lean:188` to arbitrary
finite Galois floors. -/
theorem abstractFixedFieldArtinRestriction
    (hcf : SatisfiesClassFieldAxiom (galoisAmbientUnitsRep K (AlgebraicClosure K)))
    (hAxiom : (localHenselianValuation K).SatisfiesUnramifiedUnitCohomology (localResidueDatum K))
    (ρ : (abstractFixedField K (AlgebraicClosure K) H.field)ˣ →*
      Abelianization ((abstractRelativeFixedField K (AlgebraicClosure K) L.below)
        ≃ₐ[abstractFixedField K (AlgebraicClosure K) H.field]
        (abstractRelativeFixedField K (AlgebraicClosure K) L.below)))
    (hρ : IsAbelianizedArtinRestriction
      (abstractFixedField K (AlgebraicClosure K) H.field)
      (abstractRelativeFixedField K (AlgebraicClosure K) L.below) ρ)
    (x : (abstractFixedField K (AlgebraicClosure K) H.field)ˣ) :
    abstractFixedFieldNormResidueSymbol K (AlgebraicClosure K)
      (localResidueDatum K) (localHenselianValuation K) hcf hAxiom
      H.field L.field L.below (Additive.ofMul x) = Additive.ofMul (ρ x) := by
  let Ω := AlgebraicClosure K
  let F := abstractFixedField K Ω H.field
  let M := abstractRelativeFixedField K Ω L.below
  let D : DegreeData (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) := localResidueDatum K
  let A := galoisAmbientUnitsRep K Ω
  let v := localHenselianValuation K
  let q := abstractExtensionQuotientEquivGaloisGroup K Ω H.field L.field L.below L.normal
  let u := abstractFixedFieldUnitsEquivGaloisFixed K Ω H.field
  let f : ambientFixedAddSubgroup A H.field →+ Additive (Abelianization L.extensionQuotient) :=
    (MulEquiv.toAdditive q.abelianizationCongr.symm).toAddMonoidHom.comp
      ((MonoidHom.toAdditive ρ).comp u.symm.toAddMonoidHom)
  letI : FiniteDimensional F M :=
    abstractRelativeFixedField_finiteDimensional K Ω H.field L.field L.below H.finite L.finite
  letI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.tower_top (K := K) F
  letI : IsAlgClosure F Ω := ⟨inferInstance, inferInstance⟩
  have hnorm : ∀ y, f (relativeNorm A H.field L.field L.below y) = 0 := by
    intro y
    obtain ⟨z, rfl⟩ := (abstractRelativeFixedFieldUnitsEquivGaloisFixed
      K Ω H.field L.field L.below).surjective y
    have hz := relativeNorm_abstractFixedFieldUnit_eq_normUnits
      K Ω H.field L.field L.below z.toMul
    refine (congrArg f hz).trans ?_
    change Additive.ofMul (q.abelianizationCongr.symm
      (ρ (Additive.toMul (u.symm (u (Additive.ofMul (normUnits F M z.toMul))))))) = 0
    rw [u.symm_apply_apply]
    change Additive.ofMul (q.abelianizationCongr.symm (ρ (normUnits F M z.toMul))) = 0
    rw [hρ.apply_norm F M, map_one]
    rfl
  have hprime : ∀ σQ : D.FrobeniusElements (H.toFiniteResidueAbstractField D) L.field L.below,
      let S : FiniteAbstractField (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :=
        ⟨D.frobeniusFixedField (H.toFiniteResidueAbstractField D) L.field L.below σQ,
          D.frobeniusFixedField_absoluteFinite H L.field L.below σQ⟩
      letI : Finite (H.field.toSubgroup ⧸ S.field.toSubgroup.subgroupOf H.field.toSubgroup) :=
        D.frobeniusFixedField_finite (H.toFiniteResidueAbstractField D) L.field L.below σQ
      f (relativeNorm A H.field S.field
        (D.frobeniusFixedField_le (H.toFiniteResidueAbstractField D) L.field L.below σQ)
        (v.chosenPrimeElement S)) = Additive.ofMul (Abelianization.of
          (D.frobeniusRestriction (H.toFiniteResidueAbstractField D) L.field L.below σQ)) := by
    intro σQ
    let S : FiniteAbstractField (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :=
      ⟨D.frobeniusFixedField (H.toFiniteResidueAbstractField D) L.field L.below σQ,
        D.frobeniusFixedField_absoluteFinite H L.field L.below σQ⟩
    let hSH := D.frobeniusFixedField_le (H.toFiniteResidueAbstractField D) L.field L.below σQ
    let S₀ := abstractRelativeFixedField K Ω hSH
    letI : Finite (H.field.toSubgroup ⧸ S.field.toSubgroup.subgroupOf H.field.toSubgroup) :=
      D.frobeniusFixedField_finite (H.toFiniteResidueAbstractField D) L.field L.below σQ
    letI : IsScalarTower K F S₀ := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower F S₀ Ω := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower K S₀ Ω := IsScalarTower.to₁₃₄ K F S₀ Ω
    letI : FiniteDimensional F S₀ :=
      abstractRelativeFixedField_finiteDimensional K Ω H.field S.field hSH H.finite inferInstance
    letI : FiniteDimensional K S₀ := abstractFixedField_finiteDimensional K Ω S.field S.finite
    obtain ⟨vS, tS, hVS, _, hS⟩ := exists_extension_isMixedCharLocalField F S₀
    letI := vS
    letI := tS
    letI := hVS
    letI := hS
    letI : ValuativeExtension K S₀ := valuativeExtension_trans K F S₀
    letI : Algebra.IsAlgebraic S₀ Ω := Algebra.IsAlgebraic.tower_top (K := K) S₀
    letI : IsAlgClosure S₀ Ω := ⟨inferInstance, inferInstance⟩
    letI : Module.IsTorsionFree S₀ (AlgebraicClosure S₀) :=
      (Module.isTorsionFree_iff_algebraMap_injective).mpr
        (algebraMap S₀ (AlgebraicClosure S₀)).injective
    let e : AlgebraicClosure S₀ ≃ₐ[S₀] Ω := IsAlgClosure.equiv S₀ (AlgebraicClosure S₀) Ω
    letI : FiniteDimensional K (abstractFixedField K (AlgebraicClosure K) S.field) :=
      abstractFixedField_finiteDimensional K (AlgebraicClosure K) S.field S.finite
    letI : ValuativeRel (abstractFixedField K (AlgebraicClosure K) S.field) := vS
    letI : TopologicalSpace (abstractFixedField K (AlgebraicClosure K) S.field) := tS
    letI : IsMixedCharLocalField (abstractFixedField K (AlgebraicClosure K) S.field) := hS
    letI : ValuativeExtension K (abstractFixedField K (AlgebraicClosure K) S.field) :=
      valuativeExtension_trans K F S₀
    let π : S₀ˣ := ((abstractFixedFieldUnitsEquivGaloisFixed K Ω S.field).symm
      (v.chosenPrimeElement S)).toMul
    have hπ : abstractRelativeFixedFieldUnitsEquivGaloisFixed K Ω H.field S.field hSH
        (Additive.ofMul π) = v.chosenPrimeElement S :=
      (abstractFixedFieldUnitsEquivGaloisFixed K Ω S.field).apply_symm_apply _
    have hval : normalizedValuation S₀ π = 1 := by
      have hv := localHenselianValuation_valuationAt_abstractFixedFieldUnit_coe K S π
      change ((v.valuationAt S (abstractRelativeFixedFieldUnitsEquivGaloisFixed
        K Ω H.field S.field hSH (Additive.ofMul π))) : ProfiniteInteger) =
        Int.castRingHom ProfiniteInteger (normalizedValuation S₀ π) at hv
      rw [hπ, v.valuationAt_chosenPrimeElement, v.oneValue_coe] at hv
      have hv' : ((normalizedValuation S₀ π : ℤ) : ProfiniteInteger) =
          ((1 : ℤ) : ProfiniteInteger) := by
        rw [Int.cast_one]
        exact hv.symm
      exact Int.cast_injective hv'
    obtain ⟨φS, hφS⟩ := exists_isLocalReciprocity S₀
    obtain ⟨τ₀, hτ⟩ := QuotientGroup.mk_surjective (φS π)
    let τ : AlgebraicClosure S₀ ≃ₐ[S₀] AlgebraicClosure S₀ := τ₀
    let s : S.field.toSubgroup :=
      (abstractSubgroupEquivGaloisGroup K Ω S.field).symm (AlgEquiv.autCongr e τ)
    have hs : D.normalizedDegree (D.frobeniusFixedResidueField
        (H.toFiniteResidueAbstractField D) L.field L.below σQ) s =
        Multiplicative.ofAdd (1 : ProfiniteInteger) :=
      (localResidueDegree_eq_normalizedDegree_abstractFixedFieldEquiv K S e τ).symm.trans
        (hφS.residueDegree_of_valuation_one S₀ π hval τ hτ)
    have hq := D.frobeniusRestriction_of_fixedField_degree_one
      (H.toFiniteResidueAbstractField D) L.field L.below σQ s hs
    have hsread : abstractSubgroupEquivGaloisGroup K Ω H.field (Subgroup.inclusion hSH s) =
        AlgEquiv.autCongr (e.restrictScalars F) (τ.restrictScalars F) := by
      have hs' := (abstractSubgroupEquivGaloisGroup K Ω S.field).apply_symm_apply
        (AlgEquiv.autCongr e τ)
      ext a
      exact DFunLike.congr_fun hs' a
    have hρπ : ρ (normUnits F S₀ π) =
        q.abelianizationCongr (Abelianization.of
          (D.frobeniusRestriction (H.toFiniteResidueAbstractField D) L.field L.below σQ)) := by
      rw [hρ.apply_norm_lift F S₀ M Ω hφS e π τ hτ, ← hsread]
      rw [← abstractExtensionQuotientEquivGaloisGroup_mk]
      change Abelianization.of (q (QuotientGroup.mk (Subgroup.inclusion hSH s))) = _
      exact congrArg (fun z => Abelianization.of (q z)) hq
    change f (relativeNorm A H.field S.field hSH (v.chosenPrimeElement S)) = _
    rw [← hπ, relativeNorm_abstractFixedFieldUnit_eq_normUnits]
    change Additive.ofMul (q.abelianizationCongr.symm
      (ρ (Additive.toMul (u.symm (u (Additive.ofMul (normUnits F S₀ π))))))) = _
    rw [u.symm_apply_apply]
    change Additive.ofMul (q.abelianizationCongr.symm (ρ (normUnits F S₀ π))) = _
    rw [hρπ, q.abelianizationCongr.symm_apply_apply]
    rfl
  have hx := D.normResidueSymbol_eq_of_primeNorms A v hcf hAxiom H L f hnorm hprime
    (u (Additive.ofMul x))
  change (MulEquiv.toAdditive q.abelianizationCongr)
    (D.normResidueSymbol A v hcf hAxiom H L
      (finiteNormClass A H.field L.field L.below (u (Additive.ofMul x)))) = _
  rw [hx]
  change Additive.ofMul (q.abelianizationCongr (q.abelianizationCongr.symm
    (ρ (Additive.toMul (u.symm (u (Additive.ofMul x))))))) = _
  rw [u.symm_apply_apply, q.abelianizationCongr.apply_symm_apply]
  rfl

end

end Atlas.Knowledge
