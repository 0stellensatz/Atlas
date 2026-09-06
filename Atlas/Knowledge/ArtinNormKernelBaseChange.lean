import Mathlib
import Atlas.Knowledge.IsLocalReciprocity
import Atlas.Knowledge.NormUnits
import Atlas.Knowledge.RestrictScalarsContinuous
import Atlas.Knowledge.SemilinearConjugationContinuous

/-!
# norm kernels under base change

If an Artin lift over a finite extension fixes a finite abelian field over the original base,
the norm of its input is a norm from that abelian field. The fixing kernel cuts out a finite
abelian extension upstairs, and transitivity of field norms proves the assertion.

## Main statements

* `IsLocalReciprocity.norm_mem_normRange_of_restriction_eq_one` — an upstairs Artin kernel
  maps into the downstairs norm subgroup.

## Implementation notes

The argument uses the norm-kernel field of `Atlas.Knowledge.IsLocalReciprocity` and ordinary
norm transitivity. The larger base need not be normal over the smaller one, and the closure
equivalence may use any embedding of that base.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

noncomputable section

variable (K E : Type*) [Field K] [Field E] [Algebra K E]
  [ValuativeRel E] [TopologicalSpace E] [IsMixedCharLocalField E]

/-- The norm of an input whose upstairs Artin lift fixes an abelian field is a norm from
that field ([Serre 1979, Chap. XIII, §4, Prop. 10 (a), p.197][Serre1979]). -/
theorem IsLocalReciprocity.norm_mem_normRange_of_restriction_eq_one
    [FiniteDimensional K E]
    {φ : Eˣ →* Field.absoluteGaloisGroupAbelianization E} (hφ : IsLocalReciprocity E φ)
    (e : AlgebraicClosure E ≃ₐ[K] AlgebraicClosure K)
    (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (x : Eˣ) (σ : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E)
    (hσ : (QuotientGroup.mk σ : Field.absoluteGaloisGroupAbelianization E) = φ x)
    (hfixL : AlgEquiv.restrictNormalHom L
      (AlgEquiv.autCongr e (σ.restrictScalars K)) = 1) :
    normUnits K E x ∈ (normUnits K L).range := by
  letI : CommGroup (L ≃ₐ[K] L) :=
    { (inferInstance : Group (L ≃ₐ[K] L)) with
      mul_comm := IsMulCommutative.is_comm.comm }
  let r : (AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) →* (L ≃ₐ[K] L) :=
    (AlgEquiv.restrictNormalHom L).comp
      ((AlgEquiv.autCongr e).toMonoidHom.comp
        (AlgEquiv.restrictScalarsHom (S := E) (A := AlgebraicClosure E) K))
  have hconj : Continuous (AlgEquiv.autCongr e).toMonoidHom :=
    semilinear_conjugation_continuous (RingEquiv.refl K) e.toRingEquiv
      e.commutes (AlgEquiv.autCongr e).toMonoidHom (fun _ => rfl)
  have hr : Continuous r :=
    (InfiniteGalois.restrictNormalHom_continuous L).comp
      (hconj.comp (restrictScalarsHom_continuous K E (AlgebraicClosure E)))
  let W := r.ker
  have hWopen : IsOpen (W : Set (AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E)) :=
    (isOpen_discrete ({1} : Set (L ≃ₐ[K] L))).preimage hr
  have hWclosed : IsClosed (W : Set (AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E)) :=
    Subgroup.isClosed_of_isOpen W hWopen
  let P := IntermediateField.fixedField W
  have hPfix : P.fixingSubgroup = W :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨W, hWclosed⟩
  letI : FiniteDimensional E P :=
    (InfiniteGalois.isOpen_iff_finite P).mp (by rw [hPfix]; exact hWopen)
  letI : IsGalois E P :=
    (InfiniteGalois.normal_iff_isGalois P).mp (by rw [hPfix]; infer_instance)
  have hcommW : commutator (AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) ≤ W :=
    Abelianization.commutator_subset_ker r
  have hcomm : ∀ a b : P ≃ₐ[E] P, a * b = b * a := by
    intro a b
    obtain ⟨a', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure E) a
    obtain ⟨b', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure E) b
    rw [← commutatorElement_eq_one_iff_mul_comm]
    have hc : a' * b' * a'⁻¹ * b'⁻¹ ∈
        (AlgEquiv.restrictNormalHom (F := E) (K₁ := AlgebraicClosure E) P).ker := by
      rw [IntermediateField.restrictNormalHom_ker, hPfix]
      exact hcommW (Subgroup.commutator_mem_commutator
        (Subgroup.mem_top a') (Subgroup.mem_top b'))
    have := MonoidHom.mem_ker.mp hc
    simpa only [commutatorElement_def, map_mul, map_inv] using this
  have hx : x ∈ (normUnits E P).range := by
    change x ∈ (Units.map (Algebra.norm E (S := P))).range
    rw [← hφ.normKernel P hcomm]
    exact ⟨σ, by rw [hPfix]; exact hfixL, hσ⟩
  obtain ⟨y, hy⟩ := hx
  let j : L →ₐ[K] AlgebraicClosure E := e.symm.toAlgHom.comp L.val
  have hj : ∀ a : L, j a ∈ P := by
    intro a τ
    change τ.1 (e.symm a) = e.symm a
    have hrτ : r τ.1 = 1 := τ.2
    have hact := congrArg (fun g : L ≃ₐ[K] L => (g a : AlgebraicClosure K)) hrτ
    have hres := AlgEquiv.restrictNormal_commutes
      (AlgEquiv.autCongr e (τ.1.restrictScalars K)) L a
    have heq : e (τ.1 (e.symm a)) = (a : AlgebraicClosure K) := hres.symm.trans hact
    exact e.injective (heq.trans (e.apply_symm_apply a).symm)
  let f : L →ₐ[K] P := j.codRestrict (P.restrictScalars K).toSubalgebra hj
  letI : Algebra L P := f.toRingHom.toAlgebra
  letI : IsScalarTower K L P := IsScalarTower.of_algHom f
  refine ⟨normUnits L P y, ?_⟩
  rw [normUnits_tower K L P, ← normUnits_tower K E P, hy]

end

end Atlas.Knowledge
