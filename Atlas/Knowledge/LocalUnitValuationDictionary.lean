import Mathlib
import Atlas.Knowledge.LocalHenselianValuation
import Atlas.Knowledge.PrimeElement

/-!
# local unit valuation dictionary

The valuation dictionary of the local instantiation: the abstract
normalized valuation of the local Henselian datum, applied to a
fixed-field unit through the unit dictionary, is the concrete
normalized valuation of the fixed field — and a unit lands in the
abstract unit subgroup exactly when its concrete valuation vanishes
(#104).

## Main statements

* `localHenselianValuation_valuationAt_abstractFixedFieldUnit_coe` —
  the abstract valuation reads as the concrete one; proved.
* `abstractFixedFieldUnit_mem_localHenselianValuation_unitAddSubgroup_iff`
  — unit membership is concrete valuation zero; proved.

## Implementation notes

The reading cancels the residue degree in the exact value group: the
divided valuation times the residue degree is the norm-composite, the
norm-composite of a fixed-field unit is the base valuation of its field
norm, the concrete norm law converts that to the residue degree times
the fixed field's valuation, and the C-phase dictionary identifies the
two degrees. Membership in the abstract unit subgroup is definitionally
the vanishing of the abstract valuation — the corollary bridges by type
ascription, never by rewriting at the membership site, because the two
spellings of the absolute Galois group's instances agree only
definitionally. The valuation reading has a near-token counterpart in
the source, in its `valuationMap` and separable-closure vocabulary; the
membership corollary does not — the source needs the value-one case,
prime elements, and never the value-zero case.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

noncomputable section


variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]
  (Kb : FiniteAbstractField (Field.absoluteGaloisGroup K))
  [FiniteDimensional K (abstractFixedField K (AlgebraicClosure K) Kb.field)]
  [ValuativeRel (abstractFixedField K (AlgebraicClosure K) Kb.field)]
  [TopologicalSpace (abstractFixedField K (AlgebraicClosure K) Kb.field)]
  [ValuativeExtension K (abstractFixedField K (AlgebraicClosure K) Kb.field)]
  [IsMixedCharLocalField (abstractFixedField K (AlgebraicClosure K) Kb.field)]

/-- The valuation reading: the abstract normalized valuation of the
local Henselian datum, at a fixed-field unit through the unit
dictionary, is the concrete normalized valuation of the fixed field
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldLocalData.lean:86`]
[Yamaguchi2026], the source counterpart in its `valuationMap` and
separable-closure vocabulary). -/
theorem localHenselianValuation_valuationAt_abstractFixedFieldUnit_coe
    (x : (abstractFixedField K (AlgebraicClosure K) Kb.field)ˣ) :
    (((localHenselianValuation K).valuationAt Kb
        (abstractFixedFieldUnitsEquivGaloisFixed
          K (AlgebraicClosure K) Kb.field (Additive.ofMul x))) :
      ProfiniteInteger) =
      Int.castRingHom ProfiniteInteger
        (normalizedValuation
          (abstractFixedField K (AlgebraicClosure K) Kb.field) x) := by
  apply ProfiniteInteger.nsmul_left_injective
    (Kb.residueDegree (localResidueDatum K)).pos.ne'
  have hlaw : normalizedValuationAddHom K
      (Additive.ofMul (Units.map
        ((Algebra.norm K :
          abstractFixedField K (AlgebraicClosure K) Kb.field →* K)) x)) =
      ((Kb.residueDegree (localResidueDatum K) : ℕ) : ℤ) *
        normalizedValuation
          (abstractFixedField K (AlgebraicClosure K) Kb.field) x := by
    have h1 := normalizedValuation_norm_of_isSeparable K
      (abstractFixedField K (AlgebraicClosure K) Kb.field) x
    rw [inertiaDeg_eq_finrank_residueField K
        (abstractFixedField K (AlgebraicClosure K) Kb.field),
      ← localResidueDatum_residueDegree_eq_residueFinrank K Kb] at h1
    exact h1
  calc (Kb.residueDegree (localResidueDatum K) : ℕ) •
        (((localHenselianValuation K).valuationAt Kb
          (abstractFixedFieldUnitsEquivGaloisFixed
            K (AlgebraicClosure K) Kb.field (Additive.ofMul x))) :
          ProfiniteInteger)
      = (localHenselianValuation K).normCompositeAt Kb
          (abstractFixedFieldUnitsEquivGaloisFixed
            K (AlgebraicClosure K) Kb.field (Additive.ofMul x)) :=
        (localHenselianValuation K).residueDegree_nsmul_dividedAt Kb _
    _ = localBaseValuation K
          (normToBase (galoisAmbientUnitsRep K (AlgebraicClosure K)) Kb.field
            (abstractFixedFieldUnitsEquivGaloisFixed
              K (AlgebraicClosure K) Kb.field (Additive.ofMul x))) := rfl
    _ = Int.castRingHom ProfiniteInteger
          (normalizedValuationAddHom K
            (Additive.ofMul (Units.map
              ((Algebra.norm K :
                abstractFixedField K (AlgebraicClosure K) Kb.field →* K))
              x))) :=
        localBaseValuation_normToBase_abstractFixedFieldUnit K Kb.field x
    _ = Int.castRingHom ProfiniteInteger
          (((Kb.residueDegree (localResidueDatum K) : ℕ) : ℤ) *
            normalizedValuation
              (abstractFixedField K (AlgebraicClosure K) Kb.field) x) := by
        rw [hlaw]
    _ = Int.castRingHom ProfiniteInteger
          ((Kb.residueDegree (localResidueDatum K) : ℕ) •
            normalizedValuation
              (abstractFixedField K (AlgebraicClosure K) Kb.field) x) := by
        rw [nsmul_eq_mul]
    _ = (Kb.residueDegree (localResidueDatum K) : ℕ) •
          Int.castRingHom ProfiniteInteger
            (normalizedValuation
              (abstractFixedField K (AlgebraicClosure K) Kb.field) x) :=
        map_nsmul _ _ _

/-- The membership corollary: a fixed-field unit lands in the abstract
unit subgroup exactly when its concrete valuation vanishes — new to the
layer; the source's nearest statement is the value-one prime reading
([Yamaguchi 2026,
`LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean:235`][Yamaguchi2026]). -/
theorem abstractFixedFieldUnit_mem_localHenselianValuation_unitAddSubgroup_iff
    (x : (abstractFixedField K (AlgebraicClosure K) Kb.field)ˣ) :
    abstractFixedFieldUnitsEquivGaloisFixed
        K (AlgebraicClosure K) Kb.field (Additive.ofMul x) ∈
      (localHenselianValuation K).unitAddSubgroup Kb ↔
      normalizedValuation
        (abstractFixedField K (AlgebraicClosure K) Kb.field) x = 0 := by
  constructor
  · intro h
    have h0 : (localHenselianValuation K).valuationAt Kb
        (abstractFixedFieldUnitsEquivGaloisFixed
          K (AlgebraicClosure K) Kb.field (Additive.ofMul x)) = 0 := h
    have hc : (((localHenselianValuation K).valuationAt Kb
        (abstractFixedFieldUnitsEquivGaloisFixed
          K (AlgebraicClosure K) Kb.field (Additive.ofMul x))) :
        ProfiniteInteger) = 0 := by
      rw [h0]
      rfl
    rw [localHenselianValuation_valuationAt_abstractFixedFieldUnit_coe]
      at hc
    simpa using hc
  · intro h
    have hc : (((localHenselianValuation K).valuationAt Kb
        (abstractFixedFieldUnitsEquivGaloisFixed
          K (AlgebraicClosure K) Kb.field (Additive.ofMul x))) :
        ProfiniteInteger) = 0 := by
      rw [localHenselianValuation_valuationAt_abstractFixedFieldUnit_coe, h]
      simp
    exact Subtype.ext hc


end

end Atlas.Knowledge
