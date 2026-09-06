import Mathlib
import Atlas.Knowledge.AbelianizedTransferOfInjective
import Atlas.Knowledge.AbstractFixedFieldGaloisRestriction
import Atlas.Knowledge.AbstractFixedFieldTransferNaturality

/-!
# comparison of abstract and concrete Galois transfer

The transfer used by the class formation is the group-theoretic transfer into the
automorphisms fixing the intermediate concrete field. The quotient/Galois equivalences
commute with the subgroup inclusions on representatives.

## Main statements

* `abstractFixedFieldTransferComparison` — the two transfer presentations agree.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable (k Ω : Type*) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  (K K' L : ClosedSubgroup (Ω ≃ₐ[k] Ω))
  (hLK' : L.toSubgroup ≤ K'.toSubgroup) (hK'K : K'.toSubgroup ≤ K.toSubgroup)
  [(L.toSubgroup.subgroupOf K.toSubgroup).Normal]
  [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
  [Finite ((baseField (Ω ≃ₐ[k] Ω)).toSubgroup ⧸
    K.toSubgroup.subgroupOf (baseField (Ω ≃ₐ[k] Ω)).toSubgroup)]

/-- The transfer induced on fixed fields is the concrete automorphism-group transfer
(Yamaguchi 2026, `MainTransfer.lean:172`). -/
theorem abstractFixedFieldTransferComparison :
    let F := abstractFixedField k Ω K
    let E := abstractFixedField k Ω K'
    let N := abstractFixedField k Ω L
    letI : Algebra F E :=
      (IntermediateField.inclusion (abstractFixedField_le k Ω hK'K)).toRingHom.toAlgebra
    letI : Algebra F N :=
      (IntermediateField.inclusion
        (abstractFixedField_le k Ω (hLK'.trans hK'K))).toRingHom.toAlgebra
    letI : Algebra E N :=
      (IntermediateField.inclusion (abstractFixedField_le k Ω hLK')).toRingHom.toAlgebra
    letI : IsScalarTower F E N := IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional F N := abstractRelativeFixedField_finiteDimensional
      k Ω K L (hLK'.trans hK'K) inferInstance inferInstance
    abstractFixedFieldAbelianizedTransfer k Ω K K' L hLK' hK'K =
      MonoidHom.toAdditive (abelianizedTransferOfInjective
        (AlgEquiv.restrictScalarsHom (S := E) (A := N) F)
          (AlgEquiv.restrictScalars_injective F)) := by
  let F := abstractFixedField k Ω K
  let E := abstractFixedField k Ω K'
  let N := abstractFixedField k Ω L
  letI : Algebra F E :=
    (IntermediateField.inclusion (abstractFixedField_le k Ω hK'K)).toRingHom.toAlgebra
  letI : Algebra F N :=
    (IntermediateField.inclusion (abstractFixedField_le k Ω (hLK'.trans hK'K))).toRingHom.toAlgebra
  letI : Algebra E N :=
    (IntermediateField.inclusion (abstractFixedField_le k Ω hLK')).toRingHom.toAlgebra
  letI : IsScalarTower F E N := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional F N := abstractRelativeFixedField_finiteDimensional
    k Ω K L (hLK'.trans hK'K) inferInstance inferInstance
  letI : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal :=
    transferNormNaturality_intermediateExtension_normal K K' L hK'K
  letI : Finite (K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) :=
    finite_extension_over_intermediate (hLK'.trans hK'K) hK'K hLK'
  let i := transferNormNaturalityIntermediateInclusion K K' L hK'K
  let hi := transferNormNaturalityIntermediateInclusion_injective K K' L hK'K
  let j := AlgEquiv.restrictScalarsHom (S := E) (A := N) F
  let q := abstractExtensionQuotientEquivGaloisGroup k Ω K L (hLK'.trans hK'K) inferInstance
  let q' := abstractExtensionQuotientEquivGaloisGroup k Ω K' L hLK' inferInstance
  have hcomm (a : K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) :
      q (i a) = j (q' a) := by
    induction a using QuotientGroup.induction_on with | H s =>
      ext x
      exact (abstractExtensionQuotientEquivGaloisGroup_mk_apply_val k Ω K L
        (hLK'.trans hK'K) inferInstance (Subgroup.inclusion hK'K s) x).symm.trans
          (abstractExtensionQuotientEquivGaloisGroup_mk_apply_val k Ω K' L hLK' inferInstance s x)
  have hiEq : abelianizedTransferOfInjective i hi = transferNormNaturalityTransfer K K' L hK'K := by
    rw [abelianizedTransferOfInjective_eq]
    rfl
  apply AddMonoidHom.ext
  intro a
  have h := abelianizedTransferOfInjective_natural i hi j
    (AlgEquiv.restrictScalars_injective F) q q' hcomm (q.abelianizationCongr.symm a.toMul)
  have hc := congrArg (abelianizedTransferOfInjective j (AlgEquiv.restrictScalars_injective F))
    (q.abelianizationCongr.apply_symm_apply a.toMul)
  have hiPoint := congrArg q'.abelianizationCongr
    (DFunLike.congr_fun hiEq (q.abelianizationCongr.symm a.toMul))
  exact congrArg Additive.ofMul ((hc.symm.trans h).trans hiPoint).symm

end

end Atlas.Knowledge
