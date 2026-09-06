import Mathlib
import Atlas.Knowledge.LocalFixedResidueField
import Atlas.Knowledge.NormalizedDegree

/-!
# normalized degree on fixed residue fields

The normalized degree of a finite abstract field is the intrinsic Frobenius degree over its
selected residue subfield. Restricting the residue action to that subfield scales the original
degree by its finite field degree, exactly the factor divided out in the normalized degree.

## Main statements

* `localResidueDatum_normalizedDegree_eq_residueAbsoluteDegreeIn` — normalized degree read
  over the fixed residue subfield.

## Implementation notes

The source is `LocalClassFieldTheory/Finite/LocalReciprocity/FiniteSubgroupResidueDegree.lean`.
The residue field and its degree are those of `Atlas.Knowledge.LocalFixedResidueField`.
The positive factor cancels by `ProfiniteInteger.nsmul_left_injective`. The ambient closure
is `AlgebraicClosure K`, and the local field may occupy any universe.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/-- The residue action of `H`, with scalars restricted to the actual finite
residue subfield selected by `H` inside the common residue algebraic
closure (Yamaguchi 2026, `FiniteSubgroupResidueDegree.lean:217`). -/
noncomputable def localAbstractFixedResidueActionOverIntermediateField
    (H : ClosedSubgroup (Field.absoluteGaloisGroup K)) :
    H.toSubgroup →*
      (selectedResidueField (localAbsoluteValuationSubring K) ≃ₐ[
        localAbstractFixedResidueIntermediateField K H]
        selectedResidueField (localAbsoluteValuationSubring K)) := by
  let F := localAbstractFixedResidueIntermediateField K H
  let rhoH : H.toSubgroup →*
      (selectedResidueField (localAbsoluteValuationSubring K) ≃ₐ[
        decompositionResidueField K (localAbsoluteValuationSubring K)]
        selectedResidueField (localAbsoluteValuationSubring K)) :=
    (localResidueAlgAction K).toMonoidHom.comp H.toSubgroup.subtype
  let rhoF : H.toSubgroup →* F.fixingSubgroup :=
    rhoH.codRestrict F.fixingSubgroup
      (by
        intro sigma
        rw [← localAbstractFixedResidueAction_map_eq_fixingSubgroup K H]
        exact ⟨sigma.1, sigma.2, rfl⟩)
  exact
    (IntermediateField.fixingSubgroupEquiv F).toMonoidHom.comp rhoF

/-- Restricting residue scalars changes only the scalar-linearity proof,
not the underlying automorphism of the selected residue field
(Yamaguchi 2026, `FiniteSubgroupResidueDegree.lean:238`). -/
@[simp]
theorem localAbstractFixedResidueActionOverIntermediateField_apply
    (H : ClosedSubgroup (Field.absoluteGaloisGroup K))
    (sigma : H.toSubgroup)
    (x : selectedResidueField (localAbsoluteValuationSubring K)) :
    localAbstractFixedResidueActionOverIntermediateField K H sigma x =
      localResidueAlgAction K sigma.1 x := by
  rfl

/-- **Finite local reciprocity, pointwise fixed-field degree comparison.**
The normalized degree on a finite abstract field is the ordinary intrinsic
absolute residue degree after changing the finite residue base to the
residue subfield selected by that fixed field (Yamaguchi 2026,
`FiniteSubgroupResidueDegree.lean:383`). -/
theorem localResidueDatum_normalizedDegree_eq_residueAbsoluteDegreeIn
    (H : FiniteAbstractField (Field.absoluteGaloisGroup K))
    (sigma : H.field.toSubgroup) :
    let F := localAbstractFixedResidueIntermediateField K H.field
    letI : Algebra
        (decompositionResidueField K (localAbsoluteValuationSubring K))
        F := F.algebra
    letI : Module
        (decompositionResidueField K (localAbsoluteValuationSubring K))
        F := Algebra.toModule
    letI : FiniteDimensional
        (decompositionResidueField K (localAbsoluteValuationSubring K))
        F :=
      localAbstractFixedResidueIntermediateField_finiteDimensional K H.field
    letI : Finite F := Module.finite_of_finite
      (decompositionResidueField K (localAbsoluteValuationSubring K))
    letI : Fintype F := Fintype.ofFinite F
    (localResidueDatum K).normalizedDegree
        (H.toFiniteResidueAbstractField (localResidueDatum K)) sigma =
      residueAbsoluteDegreeIn F
        (selectedResidueField (localAbsoluteValuationSubring K))
        (localAbstractFixedResidueActionOverIntermediateField
          K H.field sigma) := by
  let A := localAbsoluteValuationSubring K
  let k := decompositionResidueField K A
  let Omega := selectedResidueField A
  let F := localAbstractFixedResidueIntermediateField K H.field
  letI : Algebra k F := F.algebra
  letI : Module k F := Algebra.toModule
  letI : FiniteDimensional k F :=
    localAbstractFixedResidueIntermediateField_finiteDimensional K H.field
  letI : Finite F := Module.finite_of_finite k
  letI : Fintype F := Fintype.ofFinite F
  let HF := H.toFiniteResidueAbstractField (localResidueDatum K)
  let tau : Omega ≃ₐ[F] Omega :=
    localAbstractFixedResidueActionOverIntermediateField K H.field sigma
  have htau :
      tau.restrictScalars k =
        localResidueAlgAction K sigma.1 := by
    apply AlgEquiv.ext
    intro x
    rfl
  have hbase :=
    residueAbsoluteDegreeIn_restrictScalars k Omega F tau
  rw [htau] at hbase
  have hdegree :
      (HF.residueDegree : ℕ) =
        Module.finrank k F :=
    localResidueDatum_residueDegree_eq_selectedResidueFinrank K H
  apply Multiplicative.ext
  apply ProfiniteInteger.nsmul_left_injective HF.residueDegree.pos.ne'
  change
    (HF.residueDegree : ℕ) •
        ((localResidueDatum K).normalizedDegree HF sigma).toAdd =
      (HF.residueDegree : ℕ) •
        (residueAbsoluteDegreeIn F Omega tau).toAdd
  rw [(localResidueDatum K).residueDegree_nsmul_normalizedDegree HF,
    hdegree]
  change
    (residueAbsoluteDegreeIn k Omega
      (localResidueAlgAction K sigma.1)).toAdd =
        Module.finrank k F •
          (residueAbsoluteDegreeIn F Omega tau).toAdd
  exact congrArg Multiplicative.toAdd hbase

end

end Atlas.Knowledge
