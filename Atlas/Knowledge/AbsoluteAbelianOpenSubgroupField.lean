import Mathlib

/-!
# finite field of an open abelian subgroup

Every open subgroup of the topological abelianization of an absolute Galois group is the
image of the fixing subgroup of a finite abelian subextension. Its inverse image contains
the commutator and is open, so the infinite Galois correspondence gives the field.

## Main statements

* `absoluteAbelianOpenSubgroupField` — the finite abelian field representing an open subgroup.
-/

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [CharZero K]

/-- An open subgroup of the topological abelianization comes from a finite abelian field. -/
theorem absoluteAbelianOpenSubgroupField
    {U : Subgroup (Field.absoluteGaloisGroupAbelianization K)}
    (hU : IsOpen (U : Set (Field.absoluteGaloisGroupAbelianization K))) :
    ∃ L : IntermediateField K (AlgebraicClosure K), ∃ _ : FiniteDimensional K ↥L,
      ∃ _ : IsGalois K ↥L, (∀ σ τ : ↥L ≃ₐ[K] ↥L, σ * τ = τ * σ) ∧
        Subgroup.map
          (QuotientGroup.mk' (commutator (Field.absoluteGaloisGroup K)).topologicalClosure)
          (IntermediateField.fixingSubgroup L) = U := by
  haveI : IsGalois K (AlgebraicClosure K) := ⟨⟩
  set N := (commutator (Field.absoluteGaloisGroup K)).topologicalClosure with hNdef
  set W := Subgroup.comap (QuotientGroup.mk' N) U with hWdef
  have hWopen : IsOpen (W : Set (Field.absoluteGaloisGroup K)) :=
    hU.preimage continuous_quot_mk
  have hcommW : commutator (Field.absoluteGaloisGroup K) ≤ W := by
    intro n hn
    have hn1 : QuotientGroup.mk' N n = 1 :=
      (QuotientGroup.eq_one_iff n).mpr (Subgroup.le_topologicalClosure _ hn)
    rw [hWdef, Subgroup.mem_comap, hn1]
    exact U.one_mem
  haveI hWnormal : W.Normal := by
    constructor
    intro n hn g
    have hbr : g * n * g⁻¹ * n⁻¹ ∈ commutator (Field.absoluteGaloisGroup K) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n)
    have hsplit : g * n * g⁻¹ = g * n * g⁻¹ * n⁻¹ * n := by group
    rw [hsplit]
    exact W.mul_mem (hcommW hbr) hn
  have hWclosed : IsClosed (W : Set (Field.absoluteGaloisGroup K)) :=
    Subgroup.isClosed_of_isOpen W hWopen
  have hfix : (IntermediateField.fixedField W).fixingSubgroup = W :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨W, hWclosed⟩
  haveI hfin : FiniteDimensional K ↥(IntermediateField.fixedField W) :=
    (InfiniteGalois.isOpen_iff_finite (IntermediateField.fixedField W)).mp
      (by rw [hfix]; exact hWopen)
  haveI hgal : IsGalois K ↥(IntermediateField.fixedField W) :=
    (InfiniteGalois.normal_iff_isGalois (IntermediateField.fixedField W)).mp
      (by rw [hfix]; exact hWnormal)
  refine ⟨IntermediateField.fixedField W, hfin, hgal, fun σ τ => ?_, ?_⟩
  · obtain ⟨σ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K) σ
    obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K) τ
    rw [← commutatorElement_eq_one_iff_mul_comm]
    have hker : σ' * τ' * σ'⁻¹ * τ'⁻¹ ∈
        (AlgEquiv.restrictNormalHom (F := K) ↥(IntermediateField.fixedField W)).ker := by
      rw [IntermediateField.restrictNormalHom_ker, hfix]
      exact hcommW (Subgroup.commutator_mem_commutator (Subgroup.mem_top σ')
        (Subgroup.mem_top τ'))
    have := MonoidHom.mem_ker.mp hker
    simpa [commutatorElement_def, map_mul, map_inv] using this
  · rw [hfix, hWdef]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) U

end Atlas.Knowledge
