import Mathlib
import Atlas.Knowledge.LocalAbsoluteValuationSubringComap
import Atlas.Knowledge.LocalResidueDatum

/-!
# residue degree under finite base change

The intrinsic residue degree of a finite local extension is preserved when its algebraic
closure is identified with the algebraic closure of the base field. The valuation-ring
comparison induces compatible equivalences of the residue base fields and their closures;
Frobenius degree is invariant under this semilinear conjugation.

## Main statements

* `localResidueDegree_eq_residueAbsoluteDegreeIn_baseChange` — intrinsic residue degree read
  in the ambient closure of the base field.

## Implementation notes

The source is `LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldLocalData.lean:358`.
Atlas uses algebraic closures, with their integral-closure valuation rings. The field tower
and the closure equivalence are explicit; the local-field structures are arbitrary compatible
ones. The source's choice of a separable-closure embedding becomes the given scalar tower.
The two local fields may occupy different universes.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

noncomputable section

@[reducible]
private def valuationSubringEquivOfComapEq
    {L M : Type*} [Field L] [Field M]
    (A : ValuationSubring M) (B : ValuationSubring L)
    (e : L ≃+* M) (h : B = A.comap e.toRingHom) :
    B ≃+* A where
  toFun x := ⟨e x, by
    change (x : L) ∈ A.comap e.toRingHom
    rw [← h]
    exact x.property⟩
  invFun y := ⟨e.symm y, by
    rw [h]
    change e (e.symm y) ∈ A
    simp⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp
  map_mul' x y := by
    ext
    simp
  map_add' x y := by
    ext
    simp

variable (K F : Type*)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsMixedCharLocalField F]
  [Algebra K F] [FiniteDimensional K F] [ValuativeExtension K F]
  [Algebra F (AlgebraicClosure K)] [IsScalarTower K F (AlgebraicClosure K)]

local instance : IsGalois F (AlgebraicClosure K) :=
  IsGalois.tower_top_of_isGalois K F (AlgebraicClosure K)

/-- The finite decomposition residue field over the extension, enumerated through its given
residue field ([Yamaguchi 2026, `FixedFieldLocalData.lean:304`][Yamaguchi2026]). -/
@[implicit_reducible]
noncomputable def localBaseChangeDecompositionResidueFintype :
    Fintype (decompositionResidueField F (localAbsoluteValuationSubring K)) := by
  let A := localAbsoluteValuationSubring K
  let C := (valuation F).valuationSubring
  have hcomap : A.comap (algebraMap F (AlgebraicClosure K)) = C :=
    localAbsoluteValuationSubring_comap_embedding K F
      (IsScalarTower.toAlgHom K F (AlgebraicClosure K))
  let residueEquiv : IsLocalRing.ResidueField C ≃+* decompositionResidueField F A :=
    residueFieldEquivDecompositionResidueOfEqTop F A C hcomap
      (localAbsoluteDecompositionGroup_eq_top_over K F)
  letI : Fintype 𝓀[F] := Fintype.ofFinite _
  exact Fintype.ofEquiv 𝓀[F] residueEquiv.toEquiv

/-- The intrinsic residue degree agrees with the residue degree after transport to the
base field's algebraic closure
([Yamaguchi 2026, `FixedFieldLocalData.lean:358`][Yamaguchi2026]). -/
theorem localResidueDegree_eq_residueAbsoluteDegreeIn_baseChange
    (e : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure K)
    (sigma : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    letI : Fintype (decompositionResidueField F (localAbsoluteValuationSubring K)) :=
      localBaseChangeDecompositionResidueFintype K F
    localResidueDegree F sigma =
      residueAbsoluteDegreeIn
        (decompositionResidueField F (localAbsoluteValuationSubring K))
        (selectedResidueField (localAbsoluteValuationSubring K))
        (residueAlgActionOfEqTop F (localAbsoluteValuationSubring K)
          (localAbsoluteDecompositionGroup_eq_top_over K F) (AlgEquiv.autCongr e sigma)) := by
  letI : Fintype (decompositionResidueField F (localAbsoluteValuationSubring K)) :=
    localBaseChangeDecompositionResidueFintype K F
  let A := localAbsoluteValuationSubring K
  let AF := localAbsoluteValuationSubring F
  let C := (ValuativeRel.valuation F).valuationSubring
  let kF := IsLocalRing.ResidueField C
  let kA := decompositionResidueField F A
  let kAF := decompositionResidueField F AF
  let OmegaA := selectedResidueField A
  let OmegaF := selectedResidueField AF
  have hAcomap :
      A.comap (algebraMap F (AlgebraicClosure K)) = C := by
    exact localAbsoluteValuationSubring_comap_embedding K F
      (IsScalarTower.toAlgHom K F (AlgebraicClosure K))
  have hAFcomap :
      AF.comap (algebraMap F (AlgebraicClosure F)) = C := by
    ext x
    exact localAbsoluteValuationSubring_pullback F x
  have hAtop :
      decompositionGroup F A = ⊤ :=
    localAbsoluteDecompositionGroup_eq_top_over K F
  have hAFtop :
      decompositionGroup F AF = ⊤ :=
    localAbsoluteDecompositionGroup_eq_top F
  let eA : kF ≃+* kA :=
    residueFieldEquivDecompositionResidueOfEqTop F
      A C hAcomap hAtop
  let eAF : kF ≃+* kAF :=
    residueFieldEquivDecompositionResidueOfEqTop F
      AF C hAFcomap hAFtop
  let tau : kAF ≃+* kA :=
    eAF.symm.trans eA
  have hAF :
      AF = A.comap e.toRingHom :=
    localAbsoluteValuationSubring_comap_equiv K F e
  let r : AF ≃+* A :=
    valuationSubringEquivOfComapEq A AF e.toRingEquiv hAF
  let eResidue : OmegaF ≃+* OmegaA :=
    IsLocalRing.ResidueField.mapEquiv r
  have hr (x : AF) :
      ((r x : A) : AlgebraicClosure K) =
        e (x : AlgebraicClosure F) := by
    rfl
  have heResidue (x : kAF) :
      eResidue (algebraMap kAF OmegaF x) =
        algebraMap kA OmegaA (tau x) := by
    obtain ⟨y, rfl⟩ := eAF.surjective x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    rw [residueFieldEquivDecompositionResidueOfEqTop_algebraMap]
    have htau :
        tau (eAF (IsLocalRing.residue C a)) =
          eA (IsLocalRing.residue C a) := by
      simp [tau]
    rw [htau]
    change IsLocalRing.ResidueField.map r
        (IsLocalRing.residue AF _) =
      algebraMap kA OmegaA
        (eA (IsLocalRing.residue C a))
    rw [IsLocalRing.ResidueField.map_residue,
      residueFieldEquivDecompositionResidueOfEqTop_algebraMap]
    congr 1
    apply Subtype.ext
    exact (hr _).trans (e.commutes (a : F))
  let rhoF : OmegaF ≃ₐ[kAF] OmegaF :=
    localResidueAlgAction F sigma
  let rhoA : OmegaA ≃ₐ[kA] OmegaA :=
    residueAlgActionOfEqTop F A hAtop
      (AlgEquiv.autCongr e sigma)
  let conjugate : OmegaA ≃ₐ[kA] OmegaA :=
    { eResidue.symm.trans (rhoF.toRingEquiv.trans eResidue) with
      commutes' := fun x => by
        change eResidue
            (rhoF (eResidue.symm (algebraMap kA OmegaA x))) =
          algebraMap kA OmegaA x
        have hpre :
            eResidue.symm (algebraMap kA OmegaA x) =
              algebraMap kAF OmegaF (tau.symm x) := by
          apply eResidue.injective
          rw [eResidue.apply_symm_apply, heResidue,
            tau.apply_symm_apply]
        rw [hpre, rhoF.commutes, heResidue,
          tau.apply_symm_apply] }
  have hconjugate : conjugate = rhoA := by
    apply AlgEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := eResidue.surjective x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    change eResidue
        (rhoF (eResidue.symm
          (eResidue (IsLocalRing.residue AF a)))) =
      rhoA (eResidue (IsLocalRing.residue AF a))
    rw [eResidue.symm_apply_apply]
    change IsLocalRing.ResidueField.map r
        (residueAlgActionOfEqTop F AF hAFtop sigma
          (IsLocalRing.residue AF a)) =
      residueAlgActionOfEqTop F A hAtop
        (AlgEquiv.autCongr e sigma)
        (IsLocalRing.ResidueField.map r
          (IsLocalRing.residue AF a))
    dsimp only [residueAlgActionOfEqTop]
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply,
      decompositionGroupResidueAction_residue,
      IsLocalRing.ResidueField.map_residue,
      IsLocalRing.ResidueField.map_residue,
      decompositionGroupResidueAction_residue]
    congr 1
    apply Subtype.ext
    change e (sigma (a : AlgebraicClosure F)) =
      AlgEquiv.autCongr e sigma (e (a : AlgebraicClosure F))
    simp [AlgEquiv.autCongr_apply]
  change residueAbsoluteDegreeIn kAF OmegaF rhoF =
    residueAbsoluteDegreeIn kA OmegaA rhoA
  rw [← hconjugate]
  exact
    (residueAbsoluteDegreeIn_semilinear_conjugation
      kAF OmegaF tau eResidue heResidue rhoF).symm

end

end Atlas.Knowledge
