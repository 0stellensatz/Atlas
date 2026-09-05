import Mathlib
import Atlas.Knowledge.ChosenPrimeElement
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractExtension
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.GaloisExtensionQuotient
import Atlas.Knowledge.IntermediateFieldNormResidueNaturality
import Atlas.Knowledge.IntermediateFieldUnitsFixedSubgroup
import Atlas.Knowledge.LocalBaseValuation
import Atlas.Knowledge.LocalHenselianValuation
import Atlas.Knowledge.LocalResidueDatum
import Atlas.Knowledge.LowerRamificationGroup
import Atlas.Knowledge.NormQuotient
import Atlas.Knowledge.NormalizedValuation
import Atlas.Knowledge.PrimeElement
import Atlas.Knowledge.ProfiniteInteger
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.ResidueDatumIn
import Atlas.Knowledge.SeparableFixedFieldNorm
import Atlas.Knowledge.UnramifiedComparison
import Atlas.Knowledge.UnramifiedNormRange
import Atlas.Knowledge.ValuationData

/-!
# local abstract prime field unit

The abstract reciprocity construction fixes a prime element of the base
by choice; transported through the base unit dictionary it is an actual
field unit of `K`, of concrete normalized valuation exactly one — so at
any unramified level it defines the same norm class as every concrete
uniformizer, the identity that lets the constructed Artin map be
evaluated on a uniformizer rather than on the opaque choice (#104).

## Main definitions

* `localAbstractPrimeFieldUnit` — the transported abstract prime.

## Main statements

* `localHenselianValuation_valuationAt_baseUnit` — the abstract
  valuation of a transported base unit is its concrete normalized
  valuation; proved.
* `normalizedValuation_localAbstractPrimeFieldUnit` — the transported
  prime has concrete valuation one; proved.
* `normClass_localAbstractPrimeFieldUnit_eq_uniformizer` — at an
  unramified level it represents the class of every uniformizer;
  proved.

## Implementation notes

The valuation reading is exact where the source's is modular: the
source proves `valuationMap` of its transported prime equal to `1`
only in `ZMod n` for each positive `n`
(`LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormalization.lean:122`),
which is all its comparison consumes, while the layer's
`Atlas.Knowledge.ProfiniteInteger` is `CharZero`, so the same chain
lands the integer identity `normalizedValuation K _ = 1` and the
modular statements follow by casting. The sign seam of the arc is
disclosed here rather than repaired: the source's additive valuation
gives a *uniformizer* value `-1` and normalizes its Artin map at the
*inverse* integer-ring uniformizer
(`LocalFieldTheory/NonarchimedeanLocalField/IdealQuotients.lean:269`),
while the layer's `normalizedValuation` gives a uniformizer value `+1`
(`Atlas.Knowledge.normalizedValuation_irreducible`); the layer's
Henselian datum was built at the layer's sign, so the transported
prime lands on an actual uniformizer, not on an inverse, and the
closing theorem quantifies over `normalizedValuation K u = 1` — the
irreducible-element form converts by
`Atlas.Knowledge.normalizedValuation_irreducible`. The base reading
itself is the missing degree of the layer's dictionary:
`Atlas.Knowledge.LocalUnitValuationDictionary` reads fixed-field units
above every `Kb`, and the bottom coordinate — through the trivial
self-extension of degree one, `relativeNorm_fixedFieldInclusion` at
`Atlas.Knowledge.galoisAmbientFiniteAbstractBase_residueDegree_eq_one`
— is built here. The closing theorem consumes
`Atlas.Knowledge.unramifiedNormRange` where the source consumes its
`normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure`; both
are the counting of the unramified norm subgroup, so only the layer's
already-proved form enters.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer
  New York, 1979.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

noncomputable section

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/-- **The transported abstract prime**: the chosen prime element of
the local Henselian datum at the ambient base, read back through the
base unit dictionary as an actual unit of `K` ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormalization.lean:114`]
[Yamaguchi2026]). -/
def localAbstractPrimeFieldUnit : Kˣ :=
  Additive.toMul
    ((baseUnitsEquivGaloisAmbientFixed K (AlgebraicClosure K)).symm
      ((localHenselianValuation K).chosenPrimeElement
        (galoisAmbientFiniteAbstractBase K (AlgebraicClosure K))))

/-- **The abstract valuation of a transported base unit is its
concrete normalized valuation**: the base residue degree is one, so
the divided valuation is the norm composite, and the norm from the
base to itself is the identity ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormalization.lean:55`]
[Yamaguchi2026]). -/
theorem localHenselianValuation_valuationAt_baseUnit (x : Kˣ) :
    (((localHenselianValuation K).valuationAt
        (galoisAmbientFiniteAbstractBase K (AlgebraicClosure K))
        (baseUnitsEquivGaloisAmbientFixed K (AlgebraicClosure K)
          (Additive.ofMul x))) : ProfiniteInteger) =
      Int.castRingHom ProfiniteInteger (normalizedValuation K x) := by
  letI : Finite
      ((baseField (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)).toSubgroup ⧸
        (closedFixingSubgroup
          (⊥ : IntermediateField K
            (AlgebraicClosure K))).toSubgroup.subgroupOf
          (baseField (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)).toSubgroup) :=
    (galoisAmbientFiniteAbstractBase K (AlgebraicClosure K)).finite
  have h := (localHenselianValuation K).residueDegree_nsmul_dividedAt
    (galoisAmbientFiniteAbstractBase K (AlgebraicClosure K))
    (baseUnitsEquivGaloisAmbientFixed K (AlgebraicClosure K)
      (Additive.ofMul x))
  have h1 : ((galoisAmbientFiniteAbstractBase K
      (AlgebraicClosure K)).residueDegree (localResidueDatum K) : ℕ) =
      1 := by
    rw [galoisAmbientFiniteAbstractBase_residueDegree_eq_one K
      (AlgebraicClosure K) (localResidueDatum K)]
    rfl
  have h2 := congrArg
    (fun n : ℕ => n • (localHenselianValuation K).dividedAt
      (galoisAmbientFiniteAbstractBase K (AlgebraicClosure K))
      (baseUnitsEquivGaloisAmbientFixed K (AlgebraicClosure K)
        (Additive.ofMul x))) h1
  have hinc : fixedFieldInclusion
      (galoisAmbientUnitsRep K (AlgebraicClosure K))
      (baseField (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
      (closedFixingSubgroup (⊥ : IntermediateField K (AlgebraicClosure K)))
      (le_baseField _) (baseFieldUnitsEquiv K (Additive.ofMul x)) =
      baseUnitsEquivGaloisAmbientFixed K (AlgebraicClosure K)
        (Additive.ofMul x) :=
    Subtype.ext rfl
  have hnorm : relativeNorm (galoisAmbientUnitsRep K (AlgebraicClosure K))
      (baseField (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
      (closedFixingSubgroup (⊥ : IntermediateField K (AlgebraicClosure K)))
      (le_baseField _)
      (fixedFieldInclusion (galoisAmbientUnitsRep K (AlgebraicClosure K))
        (baseField (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
        (closedFixingSubgroup
          (⊥ : IntermediateField K (AlgebraicClosure K)))
        (le_baseField _) (baseFieldUnitsEquiv K (Additive.ofMul x))) =
      ((FiniteAbstractExtension.ofInclusion
          (closedFixingSubgroup
            (⊥ : IntermediateField K (AlgebraicClosure K)))
          (baseField (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
          (le_baseField _)).degree : ℕ) •
        baseFieldUnitsEquiv K (Additive.ofMul x) :=
    relativeNorm_fixedFieldInclusion
      (galoisAmbientUnitsRep K (AlgebraicClosure K))
      (FiniteAbstractExtension.ofInclusion
        (closedFixingSubgroup
          (⊥ : IntermediateField K (AlgebraicClosure K)))
        (baseField (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
        (le_baseField _))
      (baseFieldUnitsEquiv K (Additive.ofMul x))
  have hdeg : ((FiniteAbstractExtension.ofInclusion
      (closedFixingSubgroup (⊥ : IntermediateField K (AlgebraicClosure K)))
      (baseField (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
      (le_baseField _)).degree : ℕ) = 1 := by
    rw [← FiniteAbstractExtension.relIndex_eq_degree,
      FiniteAbstractExtension.ofInclusion_field,
      FiniteAbstractExtension.ofInclusion_base,
      closedFixingSubgroup_bot_eq_baseField K (AlgebraicClosure K)]
    exact Subgroup.relIndex_self _
  calc (((localHenselianValuation K).valuationAt
        (galoisAmbientFiniteAbstractBase K (AlgebraicClosure K))
        (baseUnitsEquivGaloisAmbientFixed K (AlgebraicClosure K)
          (Additive.ofMul x))) : ProfiniteInteger)
      = (1 : ℕ) • (localHenselianValuation K).dividedAt
          (galoisAmbientFiniteAbstractBase K (AlgebraicClosure K))
          (baseUnitsEquivGaloisAmbientFixed K (AlgebraicClosure K)
            (Additive.ofMul x)) := by
        rw [(localHenselianValuation K).valuationAt_coe, one_nsmul]
    _ = ((galoisAmbientFiniteAbstractBase K
          (AlgebraicClosure K)).residueDegree (localResidueDatum K) : ℕ) •
          (localHenselianValuation K).dividedAt
            (galoisAmbientFiniteAbstractBase K (AlgebraicClosure K))
            (baseUnitsEquivGaloisAmbientFixed K (AlgebraicClosure K)
              (Additive.ofMul x)) := h2.symm
    _ = (localHenselianValuation K).normCompositeAt
          (galoisAmbientFiniteAbstractBase K (AlgebraicClosure K))
          (baseUnitsEquivGaloisAmbientFixed K (AlgebraicClosure K)
            (Additive.ofMul x)) := h
    _ = localBaseValuation K
          (relativeNorm (galoisAmbientUnitsRep K (AlgebraicClosure K))
            (baseField (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
            (closedFixingSubgroup
              (⊥ : IntermediateField K (AlgebraicClosure K)))
            (le_baseField _)
            (baseUnitsEquivGaloisAmbientFixed K (AlgebraicClosure K)
              (Additive.ofMul x))) := rfl
    _ = localBaseValuation K
          (relativeNorm (galoisAmbientUnitsRep K (AlgebraicClosure K))
            (baseField (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
            (closedFixingSubgroup
              (⊥ : IntermediateField K (AlgebraicClosure K)))
            (le_baseField _)
            (fixedFieldInclusion
              (galoisAmbientUnitsRep K (AlgebraicClosure K))
              (baseField (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
              (closedFixingSubgroup
                (⊥ : IntermediateField K (AlgebraicClosure K)))
              (le_baseField _)
              (baseFieldUnitsEquiv K (Additive.ofMul x)))) := by
        rw [hinc]
    _ = localBaseValuation K
          (((FiniteAbstractExtension.ofInclusion
              (closedFixingSubgroup
                (⊥ : IntermediateField K (AlgebraicClosure K)))
              (baseField (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
              (le_baseField _)).degree : ℕ) •
            baseFieldUnitsEquiv K (Additive.ofMul x)) := by
        rw [hnorm]
    _ = localBaseValuation K
          ((1 : ℕ) • baseFieldUnitsEquiv K (Additive.ofMul x)) := by
        rw [hdeg]
    _ = localBaseValuation K (baseFieldUnitsEquiv K (Additive.ofMul x)) := by
        rw [one_nsmul]
    _ = Int.castRingHom ProfiniteInteger
          (normalizedValuationAddHom K (Additive.ofMul x)) :=
        localBaseValuation_baseFieldUnitsEquiv K (Additive.ofMul x)
    _ = Int.castRingHom ProfiniteInteger (normalizedValuation K x) := rfl

/-- **The transported abstract prime has concrete normalized valuation
one** — exact, not merely modulo each positive integer as at the
source ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormalization.lean:122`]
[Yamaguchi2026]). -/
theorem normalizedValuation_localAbstractPrimeFieldUnit :
    normalizedValuation K (localAbstractPrimeFieldUnit K) = 1 := by
  have h := localHenselianValuation_valuationAt_baseUnit K
    (localAbstractPrimeFieldUnit K)
  have htrans : baseUnitsEquivGaloisAmbientFixed K (AlgebraicClosure K)
      (Additive.ofMul (localAbstractPrimeFieldUnit K)) =
      (localHenselianValuation K).chosenPrimeElement
        (galoisAmbientFiniteAbstractBase K (AlgebraicClosure K)) :=
    (baseUnitsEquivGaloisAmbientFixed K
      (AlgebraicClosure K)).apply_symm_apply _
  rw [htrans, (localHenselianValuation K).valuationAt_chosenPrimeElement,
    (localHenselianValuation K).oneValue_coe] at h
  have h2 : ((normalizedValuation K (localAbstractPrimeFieldUnit K) : ℤ) :
      ProfiniteInteger) = ((1 : ℤ) : ProfiniteInteger) := by
    rw [Int.cast_one]
    exact h.symm
  exact Int.cast_injective h2

variable (L : Type u) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  [IsMixedCharLocalField L] [IsGalois K L]

/-- **At an unramified level the transported abstract prime represents
the class of every uniformizer**: both have normalized valuation one,
so they differ by a valuation unit, and at trivial inertia the units
are norms — `Atlas.Knowledge.unramifiedNormRange`. The
irreducible-element form of the hypothesis converts by
`Atlas.Knowledge.normalizedValuation_irreducible`
([Serre 1979, Chap. XIII, §4, Prop. 13, p.197][Serre1979];
[Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormalization.lean:174`]
[Yamaguchi2026], at the layer's sign). -/
theorem normClass_localAbstractPrimeFieldUnit_eq_uniformizer
    (h : lowerRamificationGroup K L 0 = ⊥) (u : Kˣ)
    (hu : normalizedValuation K u = 1) :
    normClass K L (localAbstractPrimeFieldUnit K) = normClass K L u := by
  rw [normClass_eq_iff_mul_inv_mem]
  have hval : normalizedValuationHom K
      (localAbstractPrimeFieldUnit K * u⁻¹) = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_normalizedValuationHom, normalizedValuation_mul,
      normalizedValuation_inv,
      normalizedValuation_localAbstractPrimeFieldUnit, hu]
    simp
  rw [localNormSubgroup_eq_comap_normalizedValuationHom K L h,
    Subgroup.mem_comap, hval]
  exact Subgroup.one_mem _

end

end Atlas.Knowledge
