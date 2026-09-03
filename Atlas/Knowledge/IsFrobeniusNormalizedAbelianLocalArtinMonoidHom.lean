import Mathlib
import Atlas.Knowledge.AbelianLocalArtinMonoidHom
import Atlas.Knowledge.AbstractReciprocityEquiv
import Atlas.Knowledge.ChosenPrimeElement
import Atlas.Knowledge.ConcreteReciprocityTransport
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteGaloisRealization
import Atlas.Knowledge.FiniteLocalReciprocityLaw
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FiniteNormQuotientEquivNormQuotient
import Atlas.Knowledge.GaloisExtensionQuotient
import Atlas.Knowledge.IntermediateFieldNormResidueNaturality
import Atlas.Knowledge.IntermediateFieldUnitsFixedSubgroup
import Atlas.Knowledge.IsArithmeticFrobenius
import Atlas.Knowledge.IsFrobeniusNormalized
import Atlas.Knowledge.LocalAbstractPrimeFieldUnit
import Atlas.Knowledge.LocalClassFieldAxiom
import Atlas.Knowledge.LocalHenselianValuation
import Atlas.Knowledge.LocalResidueDatum
import Atlas.Knowledge.LowerRamificationGroup
import Atlas.Knowledge.NormQuotient
import Atlas.Knowledge.NormalizedValuation
import Atlas.Knowledge.ResidueDatumIn
import Atlas.Knowledge.SeparableFixedFieldNorm
import Atlas.Knowledge.UnitCohomologyDischarge
import Atlas.Knowledge.UnramifiedComparison
import Atlas.Knowledge.UnramifiedNormQuotient
import Atlas.Knowledge.UnramifiedNormRange
import Atlas.Knowledge.UnramifiedReciprocityEquiv

/-!
# Frobenius-normalized abelian local Artin homomorphism

The Frobenius normalization of finite local reciprocity: at a level
with trivial inertia, the constructed local Artin map sends the
transported abstract prime to the realized arithmetic Frobenius, and
with it every field unit to Frobenius raised to its normalized
valuation — `Atlas.Knowledge.abelianLocalArtinMonoidHom` satisfies the
layer's `Atlas.Knowledge.IsFrobeniusNormalized` predicate, and any unit
of normalized valuation one maps to an arithmetic Frobenius. This is
the `frobenius`-field input of `Atlas.Knowledge.IsLocalReciprocity`,
delivered one finite abelian level at a time (#104).

## Main statements

* `localArtinMonoidHom_localAbstractPrimeFieldUnit` — the map
  evaluates on the transported prime as the realized Frobenius; proved.
* `localArtinMonoidHom_eq_frobenius_zpow` — the full unramified Artin
  formula; proved.
* `isFrobeniusNormalized_abelianLocalArtinMonoidHom` — the abelian
  Artin homomorphism is Frobenius-normalized; proved.
* `isArithmeticFrobenius_abelianLocalArtinMonoidHom` — a unit of
  valuation one maps to an arithmetic Frobenius; proved.

## Implementation notes

Not a port: the source normalizes by identifying its symbol with a
separately constructed field-facing unramified reciprocity isomorphism
(`LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormalization.lean:299`,
`:353`) and reads the result at its chosen *inverse* integer-ring
uniformizer (`:366`), its additive valuation giving uniformizers the
value `-1`; the layer carries no second field-facing map, states the
normalization through its own predicates
`Atlas.Knowledge.IsFrobeniusNormalized` and
`Atlas.Knowledge.IsArithmeticFrobenius` against the realized abstract
Frobenius of `Atlas.Knowledge.UnramifiedComparison`, and quantifies
over any unit of `Atlas.Knowledge.normalizedValuation` value `+1` — the
sign seam disclosed on `Atlas.Knowledge.LocalAbstractPrimeFieldUnit`,
the irreducible-element form converting by
`Atlas.Knowledge.normalizedValuation_irreducible`. Unramifiedness is
the layer's trivial inertia `lowerRamificationGroup K L 0 = ⊥` for the
source's `IsUnramifiedValuedExtension`, and the ambient conversion of
the arc applies: the source's pinned separable closure becomes
`AlgebraicClosure K`. The prime evaluation composes the merged abstract
generator calculation
`Atlas.Knowledge.ValuationData.unramifiedReciprocity_frobenius_image`
with the reciprocity transport where the source routes through its
`ConcreteReciprocityPrimeNorm.lean`, which stays unported; the zpow
formula is then direct — a unit differs from the matching prime power
by a valuation-zero unit, and units are norms at trivial inertia
(`Atlas.Knowledge.unramifiedNormRange`) — where the source consumes its
field-facing map's own normalization. The assembly is term-mode
`congrArg`/`Eq.trans` bridging throughout: the ambient group is spelled
both `Field.absoluteGaloisGroup K` (the local degree datum) and
`AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K` (the realization), a
plain definition instance search will not unfold, so the abstract
evaluation is applied with every instance explicit — the
`inferInstanceAs` re-registrations, explicitly passed normality and
finiteness witnesses, an `@`-application pinning the abstract
Frobenius's ambient spelling, and a base-spelling `Abelianization.of`.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer
  New York, 1979.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

noncomputable section

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]
variable [Field L] [Algebra K L] [FiniteDimensional K L]

section Galois

variable [IsGalois K L]

/-- **The constructed local Artin map sends the transported abstract
prime to the class of the realized arithmetic Frobenius**: the merged
abstract generator calculation, carried through the reciprocity
transport down to `Atlas.Knowledge.localArtinMonoidHom` ([Serre 1979,
Chap. XIII, §4, Prop. 13, p.197][Serre1979]; [Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormalization.lean:195`]
[Yamaguchi2026], which lands on its constructed Frobenius under its
unramified-valued-extension hypothesis). -/
theorem localArtinMonoidHom_localAbstractPrimeFieldUnit
    (h : lowerRamificationGroup K L 0 = ⊥) :
    localArtinMonoidHom K L (localAbstractPrimeFieldUnit K) =
      Abelianization.of
        (unramifiedFrobeniusRealizationOfEmbedding K L IsAlgClosed.lift) := by
  -- the realized level's normality and finiteness, stated at the ambient
  -- base's `.field` spelling; the two ambient-group spellings block
  -- instance search below, so every consumer takes these explicitly
  have hnormal' :
      ((finiteGaloisClosedFixingSubgroupOfEmbedding K L (AlgebraicClosure K)
          IsAlgClosed.lift).toSubgroup.subgroupOf
        (galoisAmbientFiniteAbstractBase K
          (AlgebraicClosure K)).field.toSubgroup).Normal :=
    finiteGaloisExtensionSubgroupOfEmbedding_normal K L (AlgebraicClosure K)
      IsAlgClosed.lift
  have hfinite' : Finite
      ((galoisAmbientFiniteAbstractBase K
          (AlgebraicClosure K)).field.toSubgroup ⧸
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L (AlgebraicClosure K)
            IsAlgClosed.lift).toSubgroup.subgroupOf
          (galoisAmbientFiniteAbstractBase K
            (AlgebraicClosure K)).field.toSubgroup) :=
    (finiteGaloisAbstractExtensionOfEmbedding K L (AlgebraicClosure K)
      IsAlgClosed.lift).finite
  haveI : IsTopologicalGroup (Field.absoluteGaloisGroup K) :=
    inferInstanceAs
      (IsTopologicalGroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
  haveI : CompactSpace (Field.absoluteGaloisGroup K) :=
    inferInstanceAs
      (CompactSpace (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
  haveI : TotallyDisconnectedSpace (Field.absoluteGaloisGroup K) :=
    inferInstanceAs
      (TotallyDisconnectedSpace (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
  -- the merged abstract generator calculation, fully applied at the
  -- local data
  have hfrob := @ValuationData.unramifiedReciprocity_frobenius_image
    (Field.absoluteGaloisGroup K) _ _ (localResidueDatum K)
    (galoisAmbientUnitsRep K (AlgebraicClosure K))
    (localHenselianValuation K)
    (localHenselianValuation_satisfiesUnramifiedUnitCohomology K)
    _ _ _
    (galoisAmbientFiniteAbstractBase K (AlgebraicClosure K))
    (finiteGaloisClosedFixingSubgroupOfEmbedding K L (AlgebraicClosure K)
      IsAlgClosed.lift)
    (finiteGaloisAbstractExtensionOfEmbedding K L (AlgebraicClosure K)
      IsAlgClosed.lift).below
    hnormal' hfinite'
    (finiteGaloisAbstractExtensionOfEmbedding_isUnramified K L
      IsAlgClosed.lift h)
  -- the transported prime represents the chosen abstract prime
  have htrans : baseUnitsEquivGaloisAmbientFixed K (AlgebraicClosure K)
      (Additive.ofMul (localAbstractPrimeFieldUnit K)) =
      (localHenselianValuation K).chosenPrimeElement
        (galoisAmbientFiniteAbstractBase K (AlgebraicClosure K)) :=
    (baseUnitsEquivGaloisAmbientFixed K
      (AlgebraicClosure K)).apply_symm_apply _
  -- the additive computation: the transported equivalence sends the
  -- realized Frobenius class to the prime's norm class
  have hforward :
      concreteReciprocityAddEquivOfEmbedding K L (AlgebraicClosure K)
          IsAlgClosed.lift (localResidueDatum K) (localHenselianValuation K)
          (algebraicClosureUnits_satisfiesClassFieldAxiom K)
          (localHenselianValuation_satisfiesUnramifiedUnitCohomology K)
          (Additive.ofMul (Abelianization.of
            (unramifiedFrobeniusRealizationOfEmbedding K L
              IsAlgClosed.lift))) =
        Additive.ofMul (normClass K L (localAbstractPrimeFieldUnit K)) := by
    -- peel the realization off the quotient equivalence's abelianization
    have hsource : MulEquiv.toAdditive
        ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
          (AlgebraicClosure K) IsAlgClosed.lift).abelianizationCongr.symm)
        (Additive.ofMul (Abelianization.of
          (unramifiedFrobeniusRealizationOfEmbedding K L IsAlgClosed.lift))) =
        Additive.ofMul (@Abelianization.of
          ((closedFixingSubgroup
              (⊥ : IntermediateField K (AlgebraicClosure K))).toSubgroup ⧸
            (finiteGaloisClosedFixingSubgroupOfEmbedding K L (AlgebraicClosure K)
                IsAlgClosed.lift).toSubgroup.subgroupOf
              (closedFixingSubgroup
                (⊥ : IntermediateField K (AlgebraicClosure K))).toSubgroup) _
          (@DegreeData.unramifiedFrobenius
          (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) _ _
          (localResidueDatum K)
          ((galoisAmbientFiniteAbstractBase K
            (AlgebraicClosure K)).toFiniteResidueAbstractField
              (localResidueDatum K))
          (finiteGaloisClosedFixingSubgroupOfEmbedding K L
            (AlgebraicClosure K) IsAlgClosed.lift)
          (finiteGaloisAbstractExtensionOfEmbedding K L
            (AlgebraicClosure K) IsAlgClosed.lift).below
          hnormal')) :=
      congrArg Additive.ofMul
        (((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
          (AlgebraicClosure K)
          IsAlgClosed.lift).abelianizationCongr).symm_apply_apply
          (@Abelianization.of
            ((closedFixingSubgroup
                (⊥ : IntermediateField K (AlgebraicClosure K))).toSubgroup ⧸
              (finiteGaloisClosedFixingSubgroupOfEmbedding K L (AlgebraicClosure K)
                  IsAlgClosed.lift).toSubgroup.subgroupOf
                (closedFixingSubgroup
                  (⊥ : IntermediateField K (AlgebraicClosure K))).toSubgroup) _
            (@DegreeData.unramifiedFrobenius
            (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) _ _
            (localResidueDatum K)
            ((galoisAmbientFiniteAbstractBase K
              (AlgebraicClosure K)).toFiniteResidueAbstractField
                (localResidueDatum K))
            (finiteGaloisClosedFixingSubgroupOfEmbedding K L
              (AlgebraicClosure K) IsAlgClosed.lift)
            (finiteGaloisAbstractExtensionOfEmbedding K L
              (AlgebraicClosure K) IsAlgClosed.lift).below
            hnormal')))
    -- the norm-class transport, read at the transported prime
    have hbase := finiteNormQuotientEquivEmbeddedNormQuotient_finiteNormClass
      K (AlgebraicClosure K) L IsAlgClosed.lift
      (baseUnitsEquivGaloisAmbientFixed K (AlgebraicClosure K)
        (Additive.ofMul (localAbstractPrimeFieldUnit K)))
    rw [(baseUnitsEquivGaloisAmbientFixed K
      (AlgebraicClosure K)).symm_apply_apply] at hbase
    have hRHS : (MulEquiv.toAdditive
        (normQuotientEquivOfNormSubgroupEq K
          (AlgHom.fieldRange (IsAlgClosed.lift : L →ₐ[K] AlgebraicClosure K))
          L
          (localNormSubgroup_fieldRange_eq K (AlgebraicClosure K) L
            IsAlgClosed.lift)))
        ((MonoidHom.toAdditive
          (normClass K
            (AlgHom.fieldRange
              (IsAlgClosed.lift : L →ₐ[K] AlgebraicClosure K))))
          (Additive.ofMul (localAbstractPrimeFieldUnit K))) =
        Additive.ofMul (normClass K L (localAbstractPrimeFieldUnit K)) := by
      change Additive.ofMul
          (normQuotientEquivOfNormSubgroupEq K
            (AlgHom.fieldRange
              (IsAlgClosed.lift : L →ₐ[K] AlgebraicClosure K)) L
            (localNormSubgroup_fieldRange_eq K (AlgebraicClosure K) L
              IsAlgClosed.lift)
            (normClass K
              (AlgHom.fieldRange
                (IsAlgClosed.lift : L →ₐ[K] AlgebraicClosure K))
              (localAbstractPrimeFieldUnit K))) = _
      rw [normQuotientEquivOfNormSubgroupEq_normClass]
    -- the transport's finiteness input, at the embedded spelling
    haveI hfiniteE : Finite
        ((closedFixingSubgroup
            (⊥ : IntermediateField K (AlgebraicClosure K))).toSubgroup ⧸
          (closedFixingSubgroup (AlgHom.fieldRange
            (IsAlgClosed.lift :
              L →ₐ[K] AlgebraicClosure K))).toSubgroup.subgroupOf
            (closedFixingSubgroup
              (⊥ : IntermediateField K (AlgebraicClosure K))).toSubgroup) :=
      hfinite'
    -- unfold the transported equivalence into its three-stage composite
    change finiteNormQuotientEquivEmbeddedNormQuotient K (AlgebraicClosure K)
        L IsAlgClosed.lift
        ((localResidueDatum K).abstractReciprocityEquiv
          (galoisAmbientUnitsRep K (AlgebraicClosure K))
          (localHenselianValuation K)
          (algebraicClosureUnits_satisfiesClassFieldAxiom K)
          (localHenselianValuation_satisfiesUnramifiedUnitCohomology K)
          (galoisAmbientFiniteAbstractBase K (AlgebraicClosure K))
          (finiteGaloisAbstractExtensionOfEmbedding K L (AlgebraicClosure K)
            IsAlgClosed.lift)
          (MulEquiv.toAdditive
            ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
              (AlgebraicClosure K)
              IsAlgClosed.lift).abelianizationCongr.symm)
            (Additive.ofMul (Abelianization.of
              (unramifiedFrobeniusRealizationOfEmbedding K L
                IsAlgClosed.lift))))) =
      Additive.ofMul (normClass K L (localAbstractPrimeFieldUnit K))
    refine Eq.trans
      (congrArg (fun z => finiteNormQuotientEquivEmbeddedNormQuotient K
        (AlgebraicClosure K) L IsAlgClosed.lift z) ?_)
      (hbase.trans hRHS)
    calc (localResidueDatum K).abstractReciprocityEquiv
          (galoisAmbientUnitsRep K (AlgebraicClosure K))
          (localHenselianValuation K)
          (algebraicClosureUnits_satisfiesClassFieldAxiom K)
          (localHenselianValuation_satisfiesUnramifiedUnitCohomology K)
          (galoisAmbientFiniteAbstractBase K (AlgebraicClosure K))
          (finiteGaloisAbstractExtensionOfEmbedding K L (AlgebraicClosure K)
            IsAlgClosed.lift)
          (MulEquiv.toAdditive
            ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
              (AlgebraicClosure K)
              IsAlgClosed.lift).abelianizationCongr.symm)
            (Additive.ofMul (Abelianization.of
              (unramifiedFrobeniusRealizationOfEmbedding K L
                IsAlgClosed.lift))))
        = (localResidueDatum K).abstractReciprocityEquiv
            (galoisAmbientUnitsRep K (AlgebraicClosure K))
            (localHenselianValuation K)
            (algebraicClosureUnits_satisfiesClassFieldAxiom K)
            (localHenselianValuation_satisfiesUnramifiedUnitCohomology K)
            (galoisAmbientFiniteAbstractBase K (AlgebraicClosure K))
            (finiteGaloisAbstractExtensionOfEmbedding K L
              (AlgebraicClosure K) IsAlgClosed.lift)
            (Additive.ofMul (@Abelianization.of
              ((closedFixingSubgroup
                  (⊥ : IntermediateField K (AlgebraicClosure K))).toSubgroup ⧸
                (finiteGaloisClosedFixingSubgroupOfEmbedding K L (AlgebraicClosure K)
                    IsAlgClosed.lift).toSubgroup.subgroupOf
                  (closedFixingSubgroup
                    (⊥ : IntermediateField K (AlgebraicClosure K))).toSubgroup) _
              (@DegreeData.unramifiedFrobenius
                (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) _ _
                (localResidueDatum K)
                ((galoisAmbientFiniteAbstractBase K
                  (AlgebraicClosure K)).toFiniteResidueAbstractField
                    (localResidueDatum K))
                (finiteGaloisClosedFixingSubgroupOfEmbedding K L
                  (AlgebraicClosure K) IsAlgClosed.lift)
                (finiteGaloisAbstractExtensionOfEmbedding K L
                  (AlgebraicClosure K) IsAlgClosed.lift).below
                hnormal'))) :=
          congrArg (fun z => (localResidueDatum K).abstractReciprocityEquiv
            (galoisAmbientUnitsRep K (AlgebraicClosure K))
            (localHenselianValuation K)
            (algebraicClosureUnits_satisfiesClassFieldAxiom K)
            (localHenselianValuation_satisfiesUnramifiedUnitCohomology K)
            (galoisAmbientFiniteAbstractBase K (AlgebraicClosure K))
            (finiteGaloisAbstractExtensionOfEmbedding K L
              (AlgebraicClosure K) IsAlgClosed.lift) z) hsource
      _ = finiteNormClass (galoisAmbientUnitsRep K (AlgebraicClosure K))
            (closedFixingSubgroup
              (⊥ : IntermediateField K (AlgebraicClosure K)))
            (closedFixingSubgroup (AlgHom.fieldRange
              (IsAlgClosed.lift : L →ₐ[K] AlgebraicClosure K)))
            (fixingSubgroupLeBase K (AlgebraicClosure K)
              (AlgHom.fieldRange
                (IsAlgClosed.lift : L →ₐ[K] AlgebraicClosure K)))
            (baseUnitsEquivGaloisAmbientFixed K (AlgebraicClosure K)
              (Additive.ofMul (localAbstractPrimeFieldUnit K))) :=
          (((localResidueDatum K).abstractReciprocityEquiv_apply_of
            (galoisAmbientUnitsRep K (AlgebraicClosure K))
            (localHenselianValuation K)
            (algebraicClosureUnits_satisfiesClassFieldAxiom K)
            (localHenselianValuation_satisfiesUnramifiedUnitCohomology K)
            (galoisAmbientFiniteAbstractBase K (AlgebraicClosure K))
            (finiteGaloisAbstractExtensionOfEmbedding K L
              (AlgebraicClosure K) IsAlgClosed.lift)
            (@DegreeData.unramifiedFrobenius
              (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) _ _
              (localResidueDatum K)
              ((galoisAmbientFiniteAbstractBase K
                (AlgebraicClosure K)).toFiniteResidueAbstractField
                  (localResidueDatum K))
              (finiteGaloisClosedFixingSubgroupOfEmbedding K L
                (AlgebraicClosure K) IsAlgClosed.lift)
              (finiteGaloisAbstractExtensionOfEmbedding K L
                (AlgebraicClosure K) IsAlgClosed.lift).below
              hnormal')).trans
            hfrob).trans
            (congrArg (fun a => finiteNormClass
              (galoisAmbientUnitsRep K (AlgebraicClosure K))
              (closedFixingSubgroup
                (⊥ : IntermediateField K (AlgebraicClosure K)))
              (closedFixingSubgroup (AlgHom.fieldRange
                (IsAlgClosed.lift : L →ₐ[K] AlgebraicClosure K)))
              (fixingSubgroupLeBase K (AlgebraicClosure K)
                (AlgHom.fieldRange
                  (IsAlgClosed.lift : L →ₐ[K] AlgebraicClosure K))) a)
              htrans.symm)
  -- reduce the Artin evaluation to the additive computation
  change (abelianizationEquivNormQuotient K L).symm
      (normClass K L (localAbstractPrimeFieldUnit K)) =
    Abelianization.of
      (unramifiedFrobeniusRealizationOfEmbedding K L IsAlgClosed.lift)
  apply (abelianizationEquivNormQuotient K L).injective
  rw [(abelianizationEquivNormQuotient K L).apply_symm_apply]
  exact (congrArg Additive.toMul hforward).symm

variable [ValuativeRel L] [TopologicalSpace L] [ValuativeExtension K L]
  [IsMixedCharLocalField L]

/-- **The full unramified Artin formula**: the constructed local Artin
map sends every field unit to the class of the realized arithmetic
Frobenius raised to its normalized valuation ([Serre 1979, Chap. XIII,
§4, Prop. 13, p.197][Serre1979]; [Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormalization.lean:383`,
valuation sign reversed][Yamaguchi2026]). -/
theorem localArtinMonoidHom_eq_frobenius_zpow
    (h : lowerRamificationGroup K L 0 = ⊥) (x : Kˣ) :
    localArtinMonoidHom K L x =
      Abelianization.of
          (unramifiedFrobeniusRealizationOfEmbedding K L IsAlgClosed.lift) ^
        normalizedValuation K x := by
  -- `x` and the matching prime power differ by a valuation-zero unit
  have hval : normalizedValuationHom K
      (x * (localAbstractPrimeFieldUnit K ^ normalizedValuation K x)⁻¹) =
      1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_normalizedValuationHom, normalizedValuation_mul,
      normalizedValuation_inv, normalizedValuation_zpow,
      normalizedValuation_localAbstractPrimeFieldUnit]
    simp
  -- at trivial inertia the norm subgroup is a valuation preimage
  have hrange : localNormSubgroup K L =
      Subgroup.comap (normalizedValuationHom K)
        (Subgroup.zpowers
          (Multiplicative.ofAdd (Module.finrank K L : ℤ))) := by
    rw [← unramifiedNormRange K L h]
    rfl
  -- so the norm classes agree, and the equivalence carries powers
  have hclass : normClass K L x =
      normClass K L (localAbstractPrimeFieldUnit K) ^
        normalizedValuation K x := by
    rw [← map_zpow, normClass_eq_iff_mul_inv_mem, hrange,
      Subgroup.mem_comap, hval]
    exact Subgroup.one_mem _
  calc localArtinMonoidHom K L x
      = (abelianizationEquivNormQuotient K L).symm (normClass K L x) := rfl
    _ = (abelianizationEquivNormQuotient K L).symm
          (normClass K L (localAbstractPrimeFieldUnit K) ^
            normalizedValuation K x) := by rw [hclass]
    _ = (abelianizationEquivNormQuotient K L).symm
          (normClass K L (localAbstractPrimeFieldUnit K)) ^
            normalizedValuation K x := map_zpow _ _ _
    _ = localArtinMonoidHom K L (localAbstractPrimeFieldUnit K) ^
          normalizedValuation K x := rfl
    _ = Abelianization.of
            (unramifiedFrobeniusRealizationOfEmbedding K L
              IsAlgClosed.lift) ^
          normalizedValuation K x := by
        rw [localArtinMonoidHom_localAbstractPrimeFieldUnit K L h]

end Galois

section AbelianGalois

open scoped IsMulCommutative

variable [ValuativeRel L] [TopologicalSpace L] [ValuativeExtension K L]
  [IsMixedCharLocalField L] [IsAbelianGalois K L]

/-- **The abelian local Artin homomorphism is Frobenius-normalized at
unramified levels** — the arithmetic normalization of local class field
theory, stated through the layer's predicate against every arithmetic
Frobenius, which trivial inertia pins to the realization ([Serre 1979,
Chap. XIII, §4, Prop. 13, p.197][Serre1979]; [Milne 2020, Chap. I, §1,
Thm. 1.1 (a), p.20][MilneCFT]; [Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormalization.lean:479`,
at the layer's valuation sign][Yamaguchi2026]). -/
theorem isFrobeniusNormalized_abelianLocalArtinMonoidHom
    (h : lowerRamificationGroup K L 0 = ⊥) :
    IsFrobeniusNormalized K L (abelianLocalArtinMonoidHom K L) := by
  intro σ hσ x
  -- trivial inertia pins every arithmetic Frobenius to the realization
  rw [isArithmeticFrobenius_unique K L h hσ
    (isArithmeticFrobenius_unramifiedFrobeniusRealizationOfEmbedding K L
      IsAlgClosed.lift)]
  change (Abelianization.equivOfComm (H := (L ≃ₐ[K] L))).symm
      (localArtinMonoidHom K L x) = _
  rw [localArtinMonoidHom_eq_frobenius_zpow K L h x, map_zpow]
  exact congrArg (fun τ : L ≃ₐ[K] L => τ ^ normalizedValuation K x)
    ((Abelianization.equivOfComm (H := (L ≃ₐ[K] L))).symm_apply_apply
      (unramifiedFrobeniusRealizationOfEmbedding K L IsAlgClosed.lift))

/-- **A unit of normalized valuation one maps to an arithmetic
Frobenius under the abelian local Artin homomorphism** — uniformizer to
Frobenius, read at every uniformizer rather than at a chosen one
([Milne 2020, Chap. I, §1, Thm. 1.1 (a), p.20][MilneCFT];
[Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormalization.lean:366`]
[Yamaguchi2026], its chosen-inverse-uniformizer form at the opposite
sign). -/
theorem isArithmeticFrobenius_abelianLocalArtinMonoidHom
    (h : lowerRamificationGroup K L 0 = ⊥) (u : Kˣ)
    (hu : normalizedValuation K u = 1) :
    IsArithmeticFrobenius K L (abelianLocalArtinMonoidHom K L u) := by
  have hσ := isArithmeticFrobenius_unramifiedFrobeniusRealizationOfEmbedding
    K L (IsAlgClosed.lift : L →ₐ[K] AlgebraicClosure K)
  rw [isFrobeniusNormalized_abelianLocalArtinMonoidHom K L h _ hσ u, hu,
    zpow_one]
  exact hσ

end AbelianGalois

end

end Atlas.Knowledge
