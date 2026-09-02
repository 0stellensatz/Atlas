import Mathlib
import Atlas.Knowledge.AbstractRelativeUnitsNorm
import Atlas.Knowledge.GalUnits
import Atlas.Knowledge.LocalUnitValuationDictionary
import Atlas.Knowledge.LocalUnramifiedInertia
import Atlas.Knowledge.NormalizedValuation
import Atlas.Knowledge.UnitCohomologyAxiom
import Atlas.Knowledge.UnramifiedUnitCohomology

/-!
# unit cohomology discharge

The valuation datum of a mixed-characteristic local field satisfies the
unramified-unit-cohomology axiom: for every finite unramified cyclic
extension of the abstract class formation, unit norms are surjective
and norm-zero units are generator differences. This is the discharge
the reciprocity arc's threaded `hAxiom` hypothesis has awaited since
`Atlas.Knowledge.AbstractReciprocityEquiv` — the direct local proof
`Atlas.Knowledge.ClassFieldAxiom`'s notes promised in place of the
source's Tate-cohomology derivation (#104).

## Main statements

* `unitRepresentation_primitive_of_unramifiedUnitPrimitive` — the
  unit-representation transport of the generator primitive; proved.
* `localHenselianValuation_satisfiesUnramifiedUnitCohomology` — the
  local datum satisfies the unramified-unit-cohomology axiom; proved.

## Implementation notes

The assembly follows the class-field-axiom template: pass to the fixed
fields, transport local-field structures along the extension chain —
keeping the valuative-extension witnesses the template discards, and
deriving the base-to-top witness by the transitivity item — read the
abstract extension as concretely unramified through
`Atlas.Knowledge.LocalUnramifiedInertia`, and close the two conjuncts
with the concrete unramified unit facts of
`Atlas.Knowledge.UnramifiedUnitCohomology` through the unit
dictionaries: the first by the valuation dictionary and the norm
reading, the second by the unit-representation transport, whose
generator device term-modes the template's rewrite — the mixed
absolute-Galois-group instance spellings tolerate exact-level
definitional bridging but not rewriting. The transport lemma takes the
two concrete facts as explicit hypotheses, so the dictionary layer and
the discharge stay separately testable. Neither declaration has a
source counterpart: at the pin the source holds no proof of the
predicate outside its abstract Tate-cohomology derivation.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

noncomputable section

/-- The unit-representation transport: from the concrete unit
membership and generator-primitive facts, the second conjunct of the
unramified-unit-cohomology axiom, elementwise — new to the layer, with
no source counterpart (#104). -/
theorem unitRepresentation_primitive_of_unramifiedUnitPrimitive
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K]
    (Kb : FiniteAbstractField (Field.absoluteGaloisGroup K))
    (Eb : FiniteUnramifiedCyclicExtension (localResidueDatum K) Kb)
    [ValuativeRel
      (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below)]
    [TopologicalSpace
      (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below)]
    [IsMixedCharLocalField
      (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below)]
    (hunit : ∀ ε : (abstractRelativeFixedField K (AlgebraicClosure K)
        Eb.below)ˣ,
      normalizedValuation
          (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below) ε =
        0 →
      abstractRelativeFixedFieldUnitsEquivGaloisFixed K (AlgebraicClosure K)
          Kb.field Eb.field Eb.below (Additive.ofMul ε) ∈
        (localHenselianValuation K).unitAddSubgroup
          Eb.toFiniteAbstractFieldExtension.field)
    (hprim : ∀ y : (abstractRelativeFixedField K (AlgebraicClosure K)
        Eb.below)ˣ,
      Algebra.norm (abstractFixedField K (AlgebraicClosure K) Kb.field)
          ((y : abstractRelativeFixedField K (AlgebraicClosure K)
            Eb.below)) = 1 →
      ∃ ε : (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below)ˣ,
        normalizedValuation
            (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below)
            ε = 0 ∧
          ((ε : abstractRelativeFixedField K (AlgebraicClosure K)
              Eb.below)) /
              abstractExtensionQuotientEquivGaloisGroup K
                (AlgebraicClosure K) Kb.field Eb.field Eb.below Eb.normal
                Eb.generator
                ((ε : abstractRelativeFixedField K (AlgebraicClosure K)
                  Eb.below)) =
            ((y : abstractRelativeFixedField K (AlgebraicClosure K)
              Eb.below))) :
    ∀ u : (Eb.unitRepresentation (localHenselianValuation K)).V,
      (Eb.unitRepresentation (localHenselianValuation K)).norm.hom u = 0 →
        ∃ ε : (Eb.unitRepresentation (localHenselianValuation K)).V,
          (Eb.unitRepresentation (localHenselianValuation K)).ρ
              Eb.generator ε - ε = u := by
  intro u hnorm
  letI : FiniteDimensional
      (abstractFixedField K (AlgebraicClosure K) Kb.field)
      (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below) :=
    abstractRelativeFixedField_finiteDimensional
      K (AlgebraicClosure K) Kb.field Eb.field Eb.below Kb.finite Eb.finite
  letI : IsGalois
      (abstractFixedField K (AlgebraicClosure K) Kb.field)
      (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below) :=
    abstractRelativeFixedField_isGalois
      K (AlgebraicClosure K) Kb.field Eb.field Eb.below Eb.normal
  -- the ambient coefficient of the representation norm of `u` vanishes
  have h0 : (ambientFixedAddSubgroup
        (galoisAmbientUnitsRep K (AlgebraicClosure K))
        Eb.toFiniteAbstractFieldExtension.field.field).subtype
      (((localHenselianValuation K).unitAddSubgroup
        Eb.toFiniteAbstractFieldExtension.field).subtype
        ((Eb.unitRepresentation (localHenselianValuation K)).norm.hom u)) =
      0 := by
    rw [hnorm]
    rfl
  -- hence the engine's relative norm of `u`'s coefficient vanishes
  have hrel : relativeNorm (galoisAmbientUnitsRep K (AlgebraicClosure K))
      Kb.field Eb.field Eb.below
      (((localHenselianValuation K).unitAddSubgroup
        Eb.toFiniteAbstractFieldExtension.field).subtype u) = 0 := by
    have hnc := (localHenselianValuation K).unitRepresentation_norm_coe
      Eb.toFiniteAbstractFieldExtension Eb.normal u
    exact Subtype.ext (hnc.symm.trans h0)
  -- the unit of the relative fixed field attached to `u`
  let xE : (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below)ˣ :=
    Additive.toMul
      ((abstractRelativeFixedFieldUnitsEquivGaloisFixed K
        (AlgebraicClosure K) Kb.field Eb.field Eb.below).symm
        (((localHenselianValuation K).unitAddSubgroup
          Eb.toFiniteAbstractFieldExtension.field).subtype u))
  have hxz : abstractRelativeFixedFieldUnitsEquivGaloisFixed K
      (AlgebraicClosure K) Kb.field Eb.field Eb.below
      (Additive.ofMul xE) =
      (((localHenselianValuation K).unitAddSubgroup
        Eb.toFiniteAbstractFieldExtension.field).subtype u) :=
    (abstractRelativeFixedFieldUnitsEquivGaloisFixed K
      (AlgebraicClosure K) Kb.field Eb.field Eb.below).apply_symm_apply _
  -- the field-norm reading: the attached unit has norm one
  have hxnorm : Algebra.norm
      (abstractFixedField K (AlgebraicClosure K) Kb.field)
      ((xE : abstractRelativeFixedField K (AlgebraicClosure K)
        Eb.below)) = 1 := by
    apply (algebraMap (abstractFixedField K (AlgebraicClosure K) Kb.field)
      (AlgebraicClosure K)).injective
    have hval := relativeNorm_abstractRelativeFixedFieldUnit_val K
      (AlgebraicClosure K) Kb.field Eb.field Eb.below Eb.normal xE
    rw [hxz] at hval
    rw [map_one]
    exact hval.symm.trans
      (congrArg
        (fun t : (ambientFixedAddSubgroup
            (galoisAmbientUnitsRep K (AlgebraicClosure K)) Kb.field) =>
          ((Additive.toMul
            ((ambientFixedAddSubgroup
              (galoisAmbientUnitsRep K (AlgebraicClosure K))
              Kb.field).subtype t) : (AlgebraicClosure K)ˣ) :
            AlgebraicClosure K)) hrel)
  -- the inverse unit has norm one as well
  have hxnormInv : Algebra.norm
      (abstractFixedField K (AlgebraicClosure K) Kb.field)
      (((xE⁻¹ : (abstractRelativeFixedField K (AlgebraicClosure K)
        Eb.below)ˣ) : abstractRelativeFixedField K (AlgebraicClosure K)
        Eb.below)) = 1 := by
    have hmul : Algebra.norm
        (abstractFixedField K (AlgebraicClosure K) Kb.field)
        (((xE⁻¹ : (abstractRelativeFixedField K (AlgebraicClosure K)
          Eb.below)ˣ) : abstractRelativeFixedField K (AlgebraicClosure K)
          Eb.below)) *
        Algebra.norm (abstractFixedField K (AlgebraicClosure K) Kb.field)
        ((xE : abstractRelativeFixedField K (AlgebraicClosure K)
          Eb.below)) = 1 := by
      rw [← map_mul,
        show ((xE⁻¹ : (abstractRelativeFixedField K (AlgebraicClosure K)
              Eb.below)ˣ) : abstractRelativeFixedField K
              (AlgebraicClosure K) Eb.below) *
            ((xE : abstractRelativeFixedField K (AlgebraicClosure K)
              Eb.below)) = 1 by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one],
        map_one]
    rw [hxnorm, mul_one] at hmul
    exact hmul
  -- the concrete primitive at the inverse unit
  obtain ⟨ε₀, hval₀, hquot⟩ := hprim xE⁻¹ hxnormInv
  have hquot' : abstractExtensionQuotientEquivGaloisGroup K
        (AlgebraicClosure K) Kb.field Eb.field Eb.below Eb.normal
        Eb.generator
        ((ε₀ : abstractRelativeFixedField K (AlgebraicClosure K)
          Eb.below)) /
        ((ε₀ : abstractRelativeFixedField K (AlgebraicClosure K)
          Eb.below)) =
      ((xE : abstractRelativeFixedField K (AlgebraicClosure K)
        Eb.below)) := by
    rw [Units.val_inv_eq_inv_val] at hquot
    rw [← inv_div, hquot, inv_inv]
  have hmem := hunit ε₀ hval₀
  let εV : (Eb.unitRepresentation (localHenselianValuation K)).V :=
    (⟨abstractRelativeFixedFieldUnitsEquivGaloisFixed K
        (AlgebraicClosure K) Kb.field Eb.field Eb.below
        (Additive.ofMul ε₀), hmem⟩ :
      (localHenselianValuation K).unitAddSubgroup
        Eb.toFiniteAbstractFieldExtension.field)
  refine ⟨εV, ?_⟩
  -- the σ − 1 identity, read through the dictionaries
  -- (i) the coefficient of the acted element is the Galois image
  have h4' : (((localHenselianValuation K).unitAddSubgroup
        Eb.toFiniteAbstractFieldExtension.field).subtype
        ((Eb.unitRepresentation (localHenselianValuation K)).ρ
          Eb.generator εV)) =
      abstractRelativeFixedFieldUnitsEquivGaloisFixed K (AlgebraicClosure K)
        Kb.field Eb.field Eb.below
        (Additive.ofMul
          (galUnits
            (abstractExtensionQuotientEquivGaloisGroup K
              (AlgebraicClosure K) Kb.field Eb.field Eb.below Eb.normal
              Eb.generator) ε₀)) := by
    apply Subtype.ext
    apply Additive.ext
    apply Units.ext
    have hact := (localHenselianValuation K).unitRepresentation_action_coe
      Eb.toFiniteAbstractFieldExtension Eb.normal Eb.generator εV
    have hcoset := relativeCosetAction_abstractRelativeFixedFieldUnit_val
      K (AlgebraicClosure K) Kb.field Eb.field Eb.below Eb.normal
      (Additive.ofMul ε₀) Eb.generator
    exact (congrArg
      (fun t : (galoisAmbientUnitsRep K (AlgebraicClosure K)).V =>
        ((Additive.toMul t : (AlgebraicClosure K)ˣ) :
          AlgebraicClosure K)) hact).trans hcoset
  have h4 : (abstractRelativeFixedFieldUnitsEquivGaloisFixed K
      (AlgebraicClosure K) Kb.field Eb.field Eb.below).symm
      (((localHenselianValuation K).unitAddSubgroup
        Eb.toFiniteAbstractFieldExtension.field).subtype
        ((Eb.unitRepresentation (localHenselianValuation K)).ρ
          Eb.generator εV)) =
      Additive.ofMul
        (galUnits
          (abstractExtensionQuotientEquivGaloisGroup K
            (AlgebraicClosure K) Kb.field Eb.field Eb.below Eb.normal
            Eb.generator) ε₀) :=
    (congrArg
      (fun t => (abstractRelativeFixedFieldUnitsEquivGaloisFixed K
        (AlgebraicClosure K) Kb.field Eb.field Eb.below).symm t)
      h4').trans
      ((abstractRelativeFixedFieldUnitsEquivGaloisFixed K
        (AlgebraicClosure K) Kb.field Eb.field Eb.below).symm_apply_apply
        (Additive.ofMul
          (galUnits
            (abstractExtensionQuotientEquivGaloisGroup K
              (AlgebraicClosure K) Kb.field Eb.field Eb.below Eb.normal
              Eb.generator) ε₀)))
  -- (ii) the coefficient of `εV` reads back as `ε₀`
  have h3 : (abstractRelativeFixedFieldUnitsEquivGaloisFixed K
      (AlgebraicClosure K) Kb.field Eb.field Eb.below).symm
      (((localHenselianValuation K).unitAddSubgroup
        Eb.toFiniteAbstractFieldExtension.field).subtype εV) =
      Additive.ofMul ε₀ :=
    (abstractRelativeFixedFieldUnitsEquivGaloisFixed K
      (AlgebraicClosure K) Kb.field Eb.field
      Eb.below).symm_apply_apply (Additive.ofMul ε₀)
  -- (iii) the coefficient of `u` reads back as `xE`
  have h2 : (abstractRelativeFixedFieldUnitsEquivGaloisFixed K
      (AlgebraicClosure K) Kb.field Eb.field Eb.below).symm
      (((localHenselianValuation K).unitAddSubgroup
        Eb.toFiniteAbstractFieldExtension.field).subtype u) =
      Additive.ofMul xE := rfl
  -- (iv) the multiplicative σ − 1 identity, additively
  have hmulUnits : galUnits
      (abstractExtensionQuotientEquivGaloisGroup K
        (AlgebraicClosure K) Kb.field Eb.field Eb.below Eb.normal
        Eb.generator) ε₀ = xE * ε₀ := by
    apply Units.ext
    rw [Units.val_mul, galUnits_coe, ← hquot',
      div_mul_cancel₀ _ (Units.ne_zero ε₀)]
  have hmulAdd : Additive.ofMul
      (galUnits
        (abstractExtensionQuotientEquivGaloisGroup K
          (AlgebraicClosure K) Kb.field Eb.field Eb.below Eb.normal
          Eb.generator) ε₀) =
      Additive.ofMul xE + Additive.ofMul ε₀ :=
    (congrArg (fun t => Additive.ofMul t) hmulUnits).trans
      (ofMul_mul xE ε₀)
  -- (v) the sum splits along the dictionary
  let w : (Eb.unitRepresentation (localHenselianValuation K)).V := u + εV
  have hsplit : (((localHenselianValuation K).unitAddSubgroup
        Eb.toFiniteAbstractFieldExtension.field).subtype w) =
      (((localHenselianValuation K).unitAddSubgroup
        Eb.toFiniteAbstractFieldExtension.field).subtype u) +
      (((localHenselianValuation K).unitAddSubgroup
        Eb.toFiniteAbstractFieldExtension.field).subtype εV) := rfl
  have hsum : (abstractRelativeFixedFieldUnitsEquivGaloisFixed K
      (AlgebraicClosure K) Kb.field Eb.field Eb.below).symm
      (((localHenselianValuation K).unitAddSubgroup
        Eb.toFiniteAbstractFieldExtension.field).subtype w) =
      Additive.ofMul xE + Additive.ofMul ε₀ :=
    (congrArg
      (fun t => (abstractRelativeFixedFieldUnitsEquivGaloisFixed K
        (AlgebraicClosure K) Kb.field Eb.field Eb.below).symm t)
      hsplit).trans
      ((map_add ((abstractRelativeFixedFieldUnitsEquivGaloisFixed K
          (AlgebraicClosure K) Kb.field Eb.field Eb.below).symm)
        (((localHenselianValuation K).unitAddSubgroup
          Eb.toFiniteAbstractFieldExtension.field).subtype u)
        (((localHenselianValuation K).unitAddSubgroup
          Eb.toFiniteAbstractFieldExtension.field).subtype εV)).trans
        (congrArg₂ (· + ·) h2 h3))
  -- assemble: the action is `u` plus the coefficient of `εV`
  have hstep : (Eb.unitRepresentation (localHenselianValuation K)).ρ
      Eb.generator εV = w :=
    Subtype.ext
      ((abstractRelativeFixedFieldUnitsEquivGaloisFixed K
        (AlgebraicClosure K) Kb.field Eb.field Eb.below).symm.injective
        (h4.trans (hmulAdd.trans hsum.symm)))
  rw [hstep]
  exact add_sub_cancel_right u εV

/-- **The discharge**: the valuation datum of a mixed-characteristic
local field satisfies the unramified-unit-cohomology axiom — the direct
local proof `Atlas.Knowledge.ClassFieldAxiom`'s notes promised in place
of the source's Tate-cohomology derivation; the mathematical content is
the cohomological triviality of unramified units ([Milne 2020, Chap.
III, §1, Prop. 1.1 and Prop. 1.2, pp.97–98][MilneCFT]). -/
theorem localHenselianValuation_satisfiesUnramifiedUnitCohomology
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] :
    (localHenselianValuation K).SatisfiesUnramifiedUnitCohomology
      (localResidueDatum K) := by
  intro Kb Eb
  -- the lower fixed field and its local structure
  letI : FiniteDimensional K
      (abstractFixedField K (AlgebraicClosure K) Kb.field) :=
    abstractFixedField_finiteDimensional
      K (AlgebraicClosure K) Kb.field Kb.finite
  obtain ⟨vF, tF, hVF, _hVTF, hF⟩ :=
    exists_extension_isMixedCharLocalField K
      (abstractFixedField K (AlgebraicClosure K) Kb.field)
  letI := vF
  letI := tF
  letI := hVF
  letI := hF
  -- the upper fixed field and its local structure over the lower
  letI : FiniteDimensional
      (abstractFixedField K (AlgebraicClosure K) Kb.field)
      (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below) :=
    abstractRelativeFixedField_finiteDimensional
      K (AlgebraicClosure K) Kb.field Eb.field Eb.below Kb.finite Eb.finite
  letI : IsGalois
      (abstractFixedField K (AlgebraicClosure K) Kb.field)
      (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below) :=
    abstractRelativeFixedField_isGalois
      K (AlgebraicClosure K) Kb.field Eb.field Eb.below Eb.normal
  obtain ⟨vE, tE, hVE, _hVTE, hE⟩ :=
    exists_extension_isMixedCharLocalField
      (abstractFixedField K (AlgebraicClosure K) Kb.field)
      (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below)
  letI := vE
  letI := tE
  letI := hVE
  letI := hE
  letI instKE : ValuativeExtension K
      (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below) :=
    valuativeExtension_trans K
      (abstractFixedField K (AlgebraicClosure K) Kb.field)
      (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below)
  -- the absolute spelling of the upper fixed field, re-registered
  letI : ValuativeRel
      (abstractFixedField K (AlgebraicClosure K) Eb.field) := vE
  letI : TopologicalSpace
      (abstractFixedField K (AlgebraicClosure K) Eb.field) := tE
  letI : ValuativeExtension K
      (abstractFixedField K (AlgebraicClosure K) Eb.field) := instKE
  letI : FiniteDimensional K
      (abstractFixedField K (AlgebraicClosure K) Eb.field) :=
    abstractFixedField_finiteDimensional
      K (AlgebraicClosure K) Eb.field inferInstance
  letI : IsMixedCharLocalField
      (abstractFixedField K (AlgebraicClosure K) Eb.field) := hE
  -- the inertia half: abstract unramifiedness gives trivial inertia
  have htriv := lowerRamificationGroup_eq_bot_of_isUnramified K Kb Eb
  -- the generator's Galois image generates
  have hg' : ∀ τ : (abstractRelativeFixedField K (AlgebraicClosure K)
        Eb.below) ≃ₐ[abstractFixedField K (AlgebraicClosure K) Kb.field]
        (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below),
      τ ∈ Subgroup.zpowers
        (abstractExtensionQuotientEquivGaloisGroup K (AlgebraicClosure K)
          Kb.field Eb.field Eb.below Eb.normal Eb.generator) := by
    intro τ
    obtain ⟨q, rfl⟩ := (abstractExtensionQuotientEquivGaloisGroup K
      (AlgebraicClosure K) Kb.field Eb.field Eb.below Eb.normal).surjective τ
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Eb.generates q)
    exact Subgroup.mem_zpowers_iff.mpr
      ⟨n, ((map_zpow (abstractExtensionQuotientEquivGaloisGroup K
            (AlgebraicClosure K) Kb.field Eb.field Eb.below Eb.normal)
            Eb.generator n).symm.trans
          (congrArg (fun t => abstractExtensionQuotientEquivGaloisGroup K
              (AlgebraicClosure K) Kb.field Eb.field Eb.below Eb.normal t)
            hn))⟩
  -- the top-field membership direction of the unit dictionary
  have hunit : ∀ ε : (abstractRelativeFixedField K (AlgebraicClosure K)
      Eb.below)ˣ,
      normalizedValuation
          (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below) ε =
        0 →
      abstractRelativeFixedFieldUnitsEquivGaloisFixed K (AlgebraicClosure K)
          Kb.field Eb.field Eb.below (Additive.ofMul ε) ∈
        (localHenselianValuation K).unitAddSubgroup
          Eb.toFiniteAbstractFieldExtension.field := by
    intro ε hval
    exact
      (abstractFixedFieldUnit_mem_localHenselianValuation_unitAddSubgroup_iff
        K ⟨Eb.field, inferInstance⟩ ε).mpr hval
  constructor
  · -- (a): every base unit is a relative norm of a unit
    intro u
    let x : (abstractFixedField K (AlgebraicClosure K) Kb.field)ˣ :=
      Additive.toMul
        ((abstractFixedFieldUnitsEquivGaloisFixed K (AlgebraicClosure K)
          Kb.field).symm u.1)
    have hx : abstractFixedFieldUnitsEquivGaloisFixed K (AlgebraicClosure K)
        Kb.field (Additive.ofMul x) = u.1 :=
      (abstractFixedFieldUnitsEquivGaloisFixed K (AlgebraicClosure K)
        Kb.field).apply_symm_apply u.1
    have hu0 : (localHenselianValuation K).valuationAt Kb u.1 = 0 := u.2
    have hval : (localHenselianValuation K).valuationAt Kb
        (abstractFixedFieldUnitsEquivGaloisFixed K (AlgebraicClosure K)
          Kb.field (Additive.ofMul x)) = 0 :=
      (congrArg (fun t => (localHenselianValuation K).valuationAt Kb t)
        hx).trans hu0
    have hmem : abstractFixedFieldUnitsEquivGaloisFixed K
        (AlgebraicClosure K) Kb.field (Additive.ofMul x) ∈
        (localHenselianValuation K).unitAddSubgroup Kb := hval
    have hx0 : normalizedValuation
        (abstractFixedField K (AlgebraicClosure K) Kb.field) x = 0 :=
      (abstractFixedFieldUnit_mem_localHenselianValuation_unitAddSubgroup_iff
        K Kb x).mp hmem
    obtain ⟨ε₀, hval₀, hnorm₀⟩ := unramifiedUnitNorm_surjective
      (abstractFixedField K (AlgebraicClosure K) Kb.field)
      (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below)
      htriv x hx0
    refine ⟨(⟨abstractRelativeFixedFieldUnitsEquivGaloisFixed K
        (AlgebraicClosure K) Kb.field Eb.field Eb.below
        (Additive.ofMul ε₀), hunit ε₀ hval₀⟩ :
      (localHenselianValuation K).unitAddSubgroup
        Eb.toFiniteAbstractFieldExtension.field), ?_⟩
    have hkey : relativeNorm (galoisAmbientUnitsRep K (AlgebraicClosure K))
        Kb.field Eb.field Eb.below
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed K
          (AlgebraicClosure K) Kb.field Eb.field Eb.below
          (Additive.ofMul ε₀)) =
        abstractFixedFieldUnitsEquivGaloisFixed K (AlgebraicClosure K)
          Kb.field (Additive.ofMul x) := by
      apply Subtype.ext
      apply Additive.ext
      apply Units.ext
      exact (relativeNorm_abstractRelativeFixedFieldUnit_val K
        (AlgebraicClosure K) Kb.field Eb.field Eb.below Eb.normal ε₀).trans
        (congrArg
          (fun t : (abstractFixedField K (AlgebraicClosure K) Kb.field)ˣ =>
            algebraMap (abstractFixedField K (AlgebraicClosure K) Kb.field)
              (AlgebraicClosure K)
              (t : abstractFixedField K (AlgebraicClosure K) Kb.field))
          hnorm₀)
    exact hkey.trans hx
  · -- (b): every representation-norm-zero unit is a σ − 1 difference
    exact unitRepresentation_primitive_of_unramifiedUnitPrimitive K Kb Eb
      hunit
      (fun y hy => unramifiedUnitPrimitive
        (abstractFixedField K (AlgebraicClosure K) Kb.field)
        (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below)
        htriv
        (abstractExtensionQuotientEquivGaloisGroup K (AlgebraicClosure K)
          Kb.field Eb.field Eb.below Eb.normal Eb.generator)
        hg' y hy)

end

end Atlas.Knowledge
