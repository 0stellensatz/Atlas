import Mathlib
import Atlas.Knowledge.LocalAbsoluteValuationSubring

/-!
# absolute valuation rings under finite base change

An equivalence of algebraic closures over a finite extension of local fields identifies
their absolute valuation rings. The identification follows from transitivity of integrality:
the integers of the extension field are integral over the integers of the base field.

## Main statements

* `localAbsoluteValuationSubring_comap_equiv` — the absolute valuation rings correspond.

## Implementation notes

The source is `LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldLocalData.lean`. It uses
uniqueness of extended valuations on its separable closures. Atlas's
`Atlas.Knowledge.LocalAbsoluteValuationSubring` is the integral closure of the integer ring,
so the same comparison follows from `Atlas.Knowledge.integer_isIntegral`. Both local fields
carry their given valuative structures, related by `ValuativeExtension`; no canonical
choice of a topology on the extension is imposed.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

/-- Pullback along an embedding of a finite extension recovers its given integer ring
([Yamaguchi 2026, `UnramifiedComparison.lean:150`][Yamaguchi2026]). -/
theorem localAbsoluteValuationSubring_comap_embedding
    (K F : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] [Field F] [ValuativeRel F]
    [Algebra K F] [FiniteDimensional K F] [ValuativeExtension K F]
    (i : F →ₐ[K] AlgebraicClosure K) :
    (localAbsoluteValuationSubring K).comap i.toRingHom = (valuation F).valuationSubring := by
  ext x
  change IsIntegral 𝒪[K] (i x) ↔ x ∈ 𝒪[F]
  rw [mem_integer_iff_isIntegral K F]
  exact isIntegral_algHom_iff (i.restrictScalars 𝒪[K]) i.injective

/-- An equivalence of algebraic closures over a finite extension identifies the two absolute
valuation rings ([Yamaguchi 2026, `FixedFieldLocalData.lean:188`][Yamaguchi2026]). -/
theorem localAbsoluteValuationSubring_comap_equiv
    (K F : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsMixedCharLocalField F] [Algebra K F] [FiniteDimensional K F]
    [ValuativeExtension K F]
    [Algebra F (AlgebraicClosure K)] [IsScalarTower K F (AlgebraicClosure K)]
    (e : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure K) :
    localAbsoluteValuationSubring F = (localAbsoluteValuationSubring K).comap e.toRingHom := by
  letI : IsScalarTower 𝒪[K] F (AlgebraicClosure K) :=
    IsScalarTower.to₁₃₄ 𝒪[K] K F (AlgebraicClosure K)
  ext x
  change IsIntegral 𝒪[F] x ↔ IsIntegral 𝒪[K] (e x)
  have hmap : IsIntegral 𝒪[K] (e x) ↔ IsIntegral 𝒪[K] x :=
    isIntegral_algHom_iff (e.restrictScalars 𝒪[K]).toAlgHom e.injective
  rw [hmap]
  exact ⟨fun h => isIntegral_trans x h, fun h => h.tower_top⟩

/-- The whole Galois group over an extension preserves the ambient absolute valuation
ring ([Yamaguchi 2026, `FixedFieldLocalData.lean:240`][Yamaguchi2026]). -/
theorem localAbsoluteDecompositionGroup_eq_top_over
    (K F : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] [Field F] [Algebra K F]
    [Algebra F (AlgebraicClosure K)] [IsScalarTower K F (AlgebraicClosure K)] :
    decompositionGroup F (localAbsoluteValuationSubring K) = ⊤ := by
  letI : IsScalarTower 𝒪[K] F (AlgebraicClosure K) :=
    IsScalarTower.to₁₃₄ 𝒪[K] K F (AlgebraicClosure K)
  apply top_unique
  intro σ _
  rw [mem_decompositionGroup_iff_apply_mem]
  intro x
  change IsIntegral 𝒪[K] (σ x) ↔ IsIntegral 𝒪[K] x
  exact isIntegral_algHom_iff (σ.restrictScalars 𝒪[K]).toAlgHom σ.injective

end Atlas.Knowledge
