import Mathlib
import Atlas.Knowledge.AbstractRelativeFixedField
import Atlas.Knowledge.FiniteUnramifiedCyclicExtension
import Atlas.Knowledge.LocalFixedResidueFinrank
import Atlas.Knowledge.LocalResidueDatum
import Atlas.Knowledge.LowerRamificationGroup
import Atlas.Knowledge.MapMaximalIdealEqPowCardInertia
import Atlas.Knowledge.NormalizedDegree

/-!
# local unramified inertia (WIP skeleton)
-/

open ValuativeRel

namespace Atlas.Knowledge

noncomputable section

/-- WIP: abstract unramifiedness at the local datum forces trivial
relative inertia at the fixed fields. -/
theorem lowerRamificationGroup_eq_bot_of_isUnramified
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K]
    (Kb : FiniteAbstractField (Field.absoluteGaloisGroup K))
    (Eb : FiniteUnramifiedCyclicExtension (localResidueDatum K) Kb)
    [FiniteDimensional K (abstractFixedField K (AlgebraicClosure K) Kb.field)]
    [ValuativeRel (abstractFixedField K (AlgebraicClosure K) Kb.field)]
    [TopologicalSpace (abstractFixedField K (AlgebraicClosure K) Kb.field)]
    [IsMixedCharLocalField (abstractFixedField K (AlgebraicClosure K) Kb.field)]
    [ValuativeExtension K (abstractFixedField K (AlgebraicClosure K) Kb.field)]
    [valE : ValuativeRel
      (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below)]
    [ValuativeExtension (abstractFixedField K (AlgebraicClosure K) Kb.field)
      (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below)]
    [valKE : ValuativeExtension K
      (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below)] :
    lowerRamificationGroup
      (abstractFixedField K (AlgebraicClosure K) Kb.field)
      (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below) 0 = ⊥ := by
  let Exa := Eb.toFiniteAbstractFieldExtension.toFiniteAbstractExtension
  -- the abstract arithmetic: unramified means the degree is the residue degree
  have h2 : (Exa.residueDegree (localResidueDatum K) : ℕ) = (Exa.degree : ℕ) :=
    Exa.residueDegree_eq_degree_of_isUnramified (localResidueDatum K)
      Eb.toFiniteAbstractFieldExtension_isUnramified
  -- the relative degree is the concrete field degree
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
  have h3 : (Exa.degree : ℕ) =
      Module.finrank
        (abstractFixedField K (AlgebraicClosure K) Kb.field)
        (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below) := by
    letI := Eb.normal
    letI := Eb.finite
    calc (Exa.degree : ℕ)
        = Nat.card
            (Additive (Kb.field.toSubgroup ⧸
              Eb.field.toSubgroup.subgroupOf Kb.field.toSubgroup)) :=
          (additiveExtensionQuotient_card Exa).symm
      _ = Nat.card (Kb.field.toSubgroup ⧸
              Eb.field.toSubgroup.subgroupOf Kb.field.toSubgroup) :=
          Nat.card_congr Additive.toMul
      _ = Nat.card
            ((abstractRelativeFixedField K (AlgebraicClosure K) Eb.below)
              ≃ₐ[abstractFixedField K (AlgebraicClosure K) Kb.field]
              (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below)) :=
          Nat.card_congr
            (abstractExtensionQuotientEquivGaloisGroup
              K (AlgebraicClosure K) Kb.field Eb.field Eb.below
              Eb.normal).toEquiv
      _ = Module.finrank
            (abstractFixedField K (AlgebraicClosure K) Kb.field)
            (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below) :=
          IsGalois.card_aut_eq_finrank _ _
  -- the top field as a finite abstract field, and the residue bundle
  let Tb : FiniteAbstractField (Field.absoluteGaloisGroup K) :=
    ⟨Eb.field, inferInstance⟩
  let Er : FiniteResidueAbstractExtension (localResidueDatum K) :=
    ⟨Tb.toFiniteResidueAbstractField (localResidueDatum K),
      Kb.toFiniteResidueAbstractField (localResidueDatum K),
      Eb.below, Eb.finite⟩
  have h4a : (Er.residueDegree : ℕ) *
      (Kb.residueDegree (localResidueDatum K) : ℕ) =
      (Tb.residueDegree (localResidueDatum K) : ℕ) :=
    FiniteResidueAbstractExtension.residueDegree_mul_absoluteResidueDegree
      (localResidueDatum K) Er
  -- instance transport from the relative to the absolute spelling
  have hres : (abstractRelativeFixedField
        K (AlgebraicClosure K) Eb.below).restrictScalars K =
      abstractFixedField K (AlgebraicClosure K) Eb.field :=
    IntermediateField.extendScalars_restrictScalars _
  letI : ValuativeRel
      (abstractFixedField K (AlgebraicClosure K) Eb.field) := hres ▸
    (valE : ValuativeRel
      ((abstractRelativeFixedField
        K (AlgebraicClosure K) Eb.below).restrictScalars K))
  letI : ValuativeExtension K
      (abstractFixedField K (AlgebraicClosure K) Eb.field) := by
    sorry
  letI : FiniteDimensional K
      (abstractFixedField K (AlgebraicClosure K) Eb.field) :=
    abstractFixedField_finiteDimensional
      K (AlgebraicClosure K) Eb.field Tb.finite
  -- base dictionaries at the two endpoints
  have h4b : (Kb.residueDegree (localResidueDatum K) : ℕ) =
      Module.finrank 𝓀[K]
        𝓀[abstractFixedField K (AlgebraicClosure K) Kb.field] :=
    localResidueDatum_residueDegree_eq_residueFinrank K Kb
  have h4c : (Tb.residueDegree (localResidueDatum K) : ℕ) =
      Module.finrank 𝓀[K]
        𝓀[abstractFixedField K (AlgebraicClosure K) Eb.field] :=
    localResidueDatum_residueDegree_eq_residueFinrank K Tb
  sorry

end

end Atlas.Knowledge
