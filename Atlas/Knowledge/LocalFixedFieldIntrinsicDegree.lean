import Mathlib
import Atlas.Knowledge.LocalFixedResidueDegree
import Atlas.Knowledge.LocalFixedResidueFinrank
import Atlas.Knowledge.LocalResidueDegreeBaseChange

/-!
# intrinsic degree on a fixed field

The residue degree of the intrinsic absolute Galois group of a finite fixed field agrees with
its normalized degree as a subgroup of the original absolute Galois group. The closure
identification carries the residue action to the action over the fixed residue field.

## Main statements

* `localResidueDegree_eq_normalizedDegree_abstractFixedFieldEquiv` — intrinsic and ambient
  normalized degrees agree.

## Implementation notes

The source is `LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldLocalData.lean:768`.
The field's valuative and topological structures are arbitrary compatible local-field
structures. `Atlas.Knowledge.LocalResidueDegreeBaseChange` compares residue degrees through
closure equivalences, and `Atlas.Knowledge.LocalFixedResidueDegree` supplies the normalized
ambient degree. The residue comparison follows the source's semilinear square.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

noncomputable section

private theorem semilinearConjugate_commutes
    {k k' Omega Omega' : Type*}
    [Field k] [Field k'] [Field Omega] [Field Omega']
    [Algebra k Omega] [Algebra k' Omega']
    (tau : k ≃+* k') (e : Omega ≃+* Omega')
    (he :
      ∀ x : k,
        e (algebraMap k Omega x) =
          algebraMap k' Omega' (tau x))
    (sigma : Omega ≃ₐ[k] Omega) (x : k') :
    e (sigma (e.symm (algebraMap k' Omega' x))) =
      algebraMap k' Omega' x := by
  have hpre :
      e.symm (algebraMap k' Omega' x) =
        algebraMap k Omega (tau.symm x) := by
    apply e.injective
    rw [e.apply_symm_apply, he, tau.apply_symm_apply]
  rw [hpre, sigma.commutes, he, tau.apply_symm_apply]

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]
  (H : FiniteAbstractField (Field.absoluteGaloisGroup K))
  [FiniteDimensional K (abstractFixedField K (AlgebraicClosure K) H.field)]
  [ValuativeRel (abstractFixedField K (AlgebraicClosure K) H.field)]
  [TopologicalSpace (abstractFixedField K (AlgebraicClosure K) H.field)]
  [IsMixedCharLocalField (abstractFixedField K (AlgebraicClosure K) H.field)]
  [ValuativeExtension K (abstractFixedField K (AlgebraicClosure K) H.field)]

/-- The intrinsic residue degree over a finite fixed field is the normalized ambient degree
(Yamaguchi 2026, `FixedFieldLocalData.lean:768`). -/
theorem localResidueDegree_eq_normalizedDegree_abstractFixedFieldEquiv
    (e : AlgebraicClosure (abstractFixedField K (AlgebraicClosure K) H.field)
      ≃ₐ[abstractFixedField K (AlgebraicClosure K) H.field] AlgebraicClosure K)
    (sigma : Field.absoluteGaloisGroup
      (abstractFixedField K (AlgebraicClosure K) H.field)) :
    localResidueDegree (abstractFixedField K (AlgebraicClosure K) H.field) sigma =
      (localResidueDatum K).normalizedDegree
        (H.toFiniteResidueAbstractField (localResidueDatum K))
        ((abstractSubgroupEquivGaloisGroup K (AlgebraicClosure K) H.field).symm
          (AlgEquiv.autCongr e sigma)) := by
  let F := abstractFixedField K (AlgebraicClosure K) H.field
  let A := localAbsoluteValuationSubring K
  let C := (ValuativeRel.valuation F).valuationSubring
  let V := (valuation K).valuationSubring
  let kK := IsLocalRing.ResidueField V
  let kF := IsLocalRing.ResidueField C
  let k₀ := decompositionResidueField K A
  let kA := decompositionResidueField F A
  let Omega := selectedResidueField A
  let R := localAbstractFixedResidueIntermediateField K H.field
  let standardResidueAlgebra : Algebra kK kF := by
    change Algebra 𝓀[K] 𝓀[F]
    infer_instance
  letI : Algebra kK kF := standardResidueAlgebra
  letI : Module kK kF := Algebra.toModule
  have hC : A.comap (algebraMap F (AlgebraicClosure K)) = C := by
    ext x
    exact localAbsoluteValuationSubring_restrict K F x
  have htop : decompositionGroup F A = ⊤ :=
    localAbstractFixedDecompositionGroup_eq_top K H.field
  let eK : kK ≃+* k₀ :=
    localBaseResidueEquivDecompositionResidue K
  let eA : kF ≃+* kA :=
    residueFieldEquivDecompositionResidueOfEqTop F A C hC htop
  let i : V →+* C :=
    algebraMap V C
  let bar : kF →+* Omega :=
    (algebraMap kA Omega).comp eA.toRingHom
  have hbar_base (x : kK) :
      bar (algebraMap kK kF x) =
        algebraMap k₀ Omega (eK x) := by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    have hres :
        algebraMap kK kF
            (IsLocalRing.residue V a) =
          IsLocalRing.residue C (i a) := by
      change algebraMap 𝓀[K] 𝓀[F]
          (IsLocalRing.residue 𝒪[K] a) =
        IsLocalRing.residue 𝒪[F] (algebraMap 𝒪[K] 𝒪[F] a)
      exact Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap
        (valuation K) (valuation F) a
    rw [hres]
    change algebraMap kA Omega
        (eA (IsLocalRing.residue C (i a))) =
      algebraMap k₀ Omega
        (eK (IsLocalRing.residue V a))
    rw [residueFieldEquivDecompositionResidueOfEqTop_algebraMap]
    have hbase :=
      localBaseResidueEquivDecompositionResidue_algebraMap K a
    change algebraMap k₀ Omega
      (eK (IsLocalRing.residue V a)) = _ at hbase
    rw [hbase]
    congr 1
  letI : Algebra k₀ kF :=
    ((algebraMap kK kF).comp eK.symm.toRingHom).toAlgebra
  let barAlg : kF →ₐ[k₀] Omega :=
    { bar with
      commutes' := fun z => by
        change bar (algebraMap kK kF (eK.symm z)) =
          algebraMap k₀ Omega z
        simpa using hbar_base (eK.symm z) }
  have hR : R = barAlg.fieldRange := by
    change IntermediateField.adjoin k₀
        (Set.range (algebraMap kA Omega)) = barAlg.fieldRange
    apply le_antisymm
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro y ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := eA.surjective z
      exact ⟨x, rfl⟩
    · rintro y ⟨x, rfl⟩
      apply IntermediateField.subset_adjoin
      exact ⟨eA x, rfl⟩
  let eRange : kF ≃+* barAlg.fieldRange :=
    (AlgEquiv.ofInjectiveField barAlg).toRingEquiv
  let eTop : kF ≃+* R :=
    eRange.trans
      (IntermediateField.equivOfEq hR.symm).toRingEquiv
  have heTop (x : kF) :
      algebraMap R Omega (eTop x) = bar x := by
    rfl
  let tau : kA ≃+* R := eA.symm.trans eTop
  let eOmega : Omega ≃+* Omega := RingEquiv.refl Omega
  have heOmega (x : kA) :
      eOmega (algebraMap kA Omega x) =
        algebraMap R Omega (tau x) := by
    change algebraMap kA Omega x =
      algebraMap R Omega (eTop (eA.symm x))
    rw [heTop]
    simp [bar]
  let sigmaH : H.field.toSubgroup :=
    (abstractSubgroupEquivGaloisGroup
      K (AlgebraicClosure K) H.field).symm
        (AlgEquiv.autCongr e sigma)
  let rhoA : Omega ≃ₐ[kA] Omega :=
    residueAlgActionOfEqTop F A htop
      (AlgEquiv.autCongr e sigma)
  let rhoH : Omega ≃ₐ[R] Omega :=
    localAbstractFixedResidueActionOverIntermediateField
      K H.field sigmaH
  let conjugate : Omega ≃ₐ[R] Omega :=
    { eOmega.symm.trans (rhoA.toRingEquiv.trans eOmega) with
      commutes' :=
        semilinearConjugate_commutes
          tau eOmega heOmega rhoA }
  have hconjugate : conjugate = rhoH := by
    apply AlgEquiv.ext
    intro x
    change residueAlgActionOfEqTop F A htop
        (AlgEquiv.autCongr e sigma) x =
      localResidueAlgAction K sigmaH.1 x
    have hsigmaH :
        abstractSubgroupEquivGaloisGroup
            K (AlgebraicClosure K) H.field sigmaH =
          AlgEquiv.autCongr e sigma :=
      (abstractSubgroupEquivGaloisGroup
        K (AlgebraicClosure K) H.field).apply_symm_apply
          (AlgEquiv.autCongr e sigma)
    rw [localAbstractFixedResidueAction_apply K H.field sigmaH]
    rw [hsigmaH]
  letI : Fintype kA :=
    localBaseChangeDecompositionResidueFintype K F
  letI : Algebra k₀ R := R.algebra
  letI : Module k₀ R := Algebra.toModule
  letI : FiniteDimensional k₀ R :=
    localAbstractFixedResidueIntermediateField_finiteDimensional K H.field
  letI : Finite R := Module.finite_of_finite k₀
  letI : Fintype R := Fintype.ofFinite R
  have hlocal :
      localResidueDegree F sigma =
        residueAbsoluteDegreeIn kA Omega rhoA := by
    exact
      localResidueDegree_eq_residueAbsoluteDegreeIn_baseChange K F e sigma
  rw [localResidueDatum_normalizedDegree_eq_residueAbsoluteDegreeIn]
  change localResidueDegree F sigma =
    residueAbsoluteDegreeIn R Omega rhoH
  rw [hlocal, ← hconjugate]
  exact
    (residueAbsoluteDegreeIn_semilinear_conjugation
      kA Omega tau eOmega heOmega rhoA).symm

end

end Atlas.Knowledge
