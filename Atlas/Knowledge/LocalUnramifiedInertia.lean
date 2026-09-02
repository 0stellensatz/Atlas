import Mathlib
import Atlas.Knowledge.AbstractRelativeFixedField
import Atlas.Knowledge.FiniteAbstractExtension
import Atlas.Knowledge.FiniteUnramifiedCyclicExtension
import Atlas.Knowledge.FinrankResidueInertia
import Atlas.Knowledge.LocalFixedResidueFinrank
import Atlas.Knowledge.LocalResidueDatum
import Atlas.Knowledge.LowerRamificationGroup
import Atlas.Knowledge.NormalizedDegree

/-!
# local unramified inertia

Abstract unramifiedness at the local datum forces trivial concrete
inertia: a finite unramified cyclic extension of the abstract class
formation of a mixed-characteristic local field has trivial zeroth
ramification group at its fixed fields. This is the inertia half of
the local unramified-unit-cohomology discharge — with it, the
concrete unramified unit facts apply to every abstract extension the
axiom quantifies over (#104).

## Main statements

* `lowerRamificationGroup_eq_bot_of_isUnramified` — abstract
  unramifiedness gives trivial concrete inertia; proved.
* `localResidueDatum_residueDegree_top_eq_relativeResidueFinrank` —
  the top-field residue dictionary in the relative spelling; proved.

## Implementation notes

The route is cardinality arithmetic, not inertia lifting: abstractly
an unramified extension has residue degree equal to its degree, the
degree reads as the concrete field degree through the extension
quotient, the residue degrees read as concrete residue finranks
through the base dictionary at both endpoints and the residue tower,
and the concrete fundamental identity `n = f · #G₀` then forces the
inertia order to one. The two `restrictScalars` transport lemmas
carry the valuative structure between the relative and absolute
spellings of the top fixed field — the two spellings' coercions are
not definitionally equal, and the transport substitutes along the
propositional identification with the structures aligned by `HEq`.
The statement takes the valuative structures as instance binders in
the C-phase pattern; the discharge's assembly supplies them from its
extension chain. This direction has no source counterpart: the
source's comparison of the two unramifiedness notions is the
realization-side converse ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedComparison.lean:291`]
[Yamaguchi2026]), and its local-reciprocity arc never needs this one
because its unit-cohomology axiom is derived through the
Tate-cohomology reading the layer replaces.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

noncomputable section

section General

variable {K : Type*} [Field K] [ValuativeRel K]
  {Ω : Type*} [Field Ω] [Algebra K Ω]
  {F : IntermediateField K Ω}

/-- Transport of a `ValuativeExtension` witness from a relative
intermediate field to an absolute spelling of the same field, along a
propositional identification of its `restrictScalars` with the
absolute spelling, given that the valuative structures agree. -/
theorem valuativeExtension_of_restrictScalars_eq
    (E' : IntermediateField F Ω) (L : IntermediateField K Ω)
    (h : E'.restrictScalars K = L)
    [vE : ValuativeRel E'] [ValuativeExtension K E']
    [vL : ValuativeRel L] (hv : HEq vE vL) :
    ValuativeExtension K L := by
  subst h
  obtain rfl := eq_of_heq hv
  exact ‹ValuativeExtension K E'›

/-- The residue degree over the base is spelling-independent: the
relative and absolute readings of one intermediate field carry the
same residue finrank when their valuative structures agree. -/
theorem residue_finrank_of_restrictScalars_eq
    (E' : IntermediateField F Ω) (L : IntermediateField K Ω)
    (h : E'.restrictScalars K = L)
    [vE : ValuativeRel E'] [ValuativeExtension K E']
    [vL : ValuativeRel L] [ValuativeExtension K L]
    (hv : HEq vE vL) :
    Module.finrank 𝓀[K] 𝓀[L] = Module.finrank 𝓀[K] 𝓀[E'] := by
  subst h
  obtain rfl := eq_of_heq hv
  rfl

end General

/-- **The top-field residue dictionary in the relative spelling**: the
abstract residue degree of the top field of a finite unramified cyclic
extension is the residue finrank of its relative fixed field
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFinrankTransfer.lean:123`]
[Yamaguchi2026], read through the spelling transport). -/
theorem localResidueDatum_residueDegree_top_eq_relativeResidueFinrank
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K]
    (Kb : FiniteAbstractField (Field.absoluteGaloisGroup K))
    (Eb : FiniteUnramifiedCyclicExtension (localResidueDatum K) Kb)
    [valE : ValuativeRel
      (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below)]
    [valKE : ValuativeExtension K
      (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below)] :
    ((⟨Eb.field, inferInstance⟩ : FiniteAbstractField
        (Field.absoluteGaloisGroup K)).residueDegree
          (localResidueDatum K) : ℕ) =
      Module.finrank 𝓀[K]
        𝓀[abstractRelativeFixedField K (AlgebraicClosure K) Eb.below] := by
  have hres : (abstractRelativeFixedField
        K (AlgebraicClosure K) Eb.below).restrictScalars K =
      abstractFixedField K (AlgebraicClosure K) Eb.field :=
    IntermediateField.extendScalars_restrictScalars _
  letI vT : ValuativeRel
      (abstractFixedField K (AlgebraicClosure K) Eb.field) :=
    cast (congrArg
        (fun X : IntermediateField K (AlgebraicClosure K) => ValuativeRel X)
        hres)
      (valE : ValuativeRel
        ((abstractRelativeFixedField
          K (AlgebraicClosure K) Eb.below).restrictScalars K))
  have hv : HEq valE vT := (cast_heq _ _).symm
  letI wT : ValuativeExtension K
      (abstractFixedField K (AlgebraicClosure K) Eb.field) :=
    valuativeExtension_of_restrictScalars_eq _ _ hres hv
  letI : FiniteDimensional K
      (abstractFixedField K (AlgebraicClosure K) Eb.field) :=
    abstractFixedField_finiteDimensional
      K (AlgebraicClosure K) Eb.field inferInstance
  calc ((⟨Eb.field, inferInstance⟩ : FiniteAbstractField
        (Field.absoluteGaloisGroup K)).residueDegree
          (localResidueDatum K) : ℕ)
      = Module.finrank 𝓀[K]
          𝓀[abstractFixedField K (AlgebraicClosure K) Eb.field] :=
        localResidueDatum_residueDegree_eq_residueFinrank
          K ⟨Eb.field, inferInstance⟩
    _ = Module.finrank 𝓀[K]
          𝓀[abstractRelativeFixedField K (AlgebraicClosure K) Eb.below] :=
        residue_finrank_of_restrictScalars_eq _ _ hres hv

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- **Abstract unramifiedness gives trivial concrete inertia**: a
finite unramified cyclic extension of the local datum has trivial
zeroth ramification group at its fixed fields — the inertia half of
the local unramified-unit-cohomology discharge. The source's
comparison of the two notions runs the other way, on realizations
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedComparison.lean:291`]
[Yamaguchi2026]). -/
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
  -- the residue bundle over the two endpoints
  let Er : FiniteResidueAbstractExtension (localResidueDatum K) :=
    ⟨(⟨Eb.field, inferInstance⟩ : FiniteAbstractField
        (Field.absoluteGaloisGroup K)).toFiniteResidueAbstractField
          (localResidueDatum K),
      Kb.toFiniteResidueAbstractField (localResidueDatum K),
      Eb.below, Eb.finite⟩
  have h4a : (Er.residueDegree : ℕ) *
      (Kb.residueDegree (localResidueDatum K) : ℕ) =
      ((⟨Eb.field, inferInstance⟩ : FiniteAbstractField
        (Field.absoluteGaloisGroup K)).residueDegree
          (localResidueDatum K) : ℕ) :=
    FiniteResidueAbstractExtension.residueDegree_mul_absoluteResidueDegree
      (localResidueDatum K) Er
  -- base dictionaries at the two endpoints, and the residue tower
  have h4b : (Kb.residueDegree (localResidueDatum K) : ℕ) =
      Module.finrank 𝓀[K]
        𝓀[abstractFixedField K (AlgebraicClosure K) Kb.field] :=
    localResidueDatum_residueDegree_eq_residueFinrank K Kb
  have h4c : ((⟨Eb.field, inferInstance⟩ : FiniteAbstractField
        (Field.absoluteGaloisGroup K)).residueDegree
          (localResidueDatum K) : ℕ) =
      Module.finrank 𝓀[K]
        𝓀[abstractRelativeFixedField K (AlgebraicClosure K) Eb.below] :=
    localResidueDatum_residueDegree_top_eq_relativeResidueFinrank K Kb Eb
  have h4d : Module.finrank 𝓀[K]
        𝓀[abstractRelativeFixedField K (AlgebraicClosure K) Eb.below] =
      Module.finrank 𝓀[K]
          𝓀[abstractFixedField K (AlgebraicClosure K) Kb.field] *
        Module.finrank
          𝓀[abstractFixedField K (AlgebraicClosure K) Kb.field]
          𝓀[abstractRelativeFixedField K (AlgebraicClosure K) Eb.below] :=
    residueFinrank_mul_residueFinrank K
      (abstractFixedField K (AlgebraicClosure K) Kb.field)
      (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below)
  -- cancel the positive base residue degree
  have h4 : (Er.residueDegree : ℕ) =
      Module.finrank
        𝓀[abstractFixedField K (AlgebraicClosure K) Kb.field]
        𝓀[abstractRelativeFixedField K (AlgebraicClosure K) Eb.below] := by
    have hpos : 0 < (Kb.residueDegree (localResidueDatum K) : ℕ) :=
      (Kb.residueDegree (localResidueDatum K)).pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h4a, h4c, h4d, h4b]
    exact Nat.mul_comm _ _
  -- the abstract relative residue degree is the extension's
  have hbridge : (Er.residueDegree : ℕ) =
      (Exa.residueDegree (localResidueDatum K) : ℕ) := rfl
  -- the concrete fundamental identity forces the inertia order to one
  letI : FiniteDimensional K
      (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below) :=
    Module.Finite.trans
      (abstractFixedField K (AlgebraicClosure K) Kb.field)
      (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below)
  have h5 : Module.finrank
        (abstractFixedField K (AlgebraicClosure K) Kb.field)
        (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below) =
      Module.finrank
          𝓀[abstractFixedField K (AlgebraicClosure K) Kb.field]
          𝓀[abstractRelativeFixedField K (AlgebraicClosure K) Eb.below] *
        Nat.card (lowerRamificationGroup
          (abstractFixedField K (AlgebraicClosure K) Kb.field)
          (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below) 0) :=
    finrank_eq_finrank_residueField_mul_card_inertia K
      (abstractFixedField K (AlgebraicClosure K) Kb.field)
      (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below)
  have hN : 0 < Module.finrank
      (abstractFixedField K (AlgebraicClosure K) Kb.field)
      (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below) :=
    Module.finrank_pos
  have hNf : Module.finrank
      (abstractFixedField K (AlgebraicClosure K) Kb.field)
      (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below) =
      Module.finrank
        𝓀[abstractFixedField K (AlgebraicClosure K) Kb.field]
        𝓀[abstractRelativeFixedField K (AlgebraicClosure K) Eb.below] := by
    rw [← h3, ← h2, ← hbridge, h4]
  have hfpos : 0 < Module.finrank
      𝓀[abstractFixedField K (AlgebraicClosure K) Kb.field]
      𝓀[abstractRelativeFixedField K (AlgebraicClosure K) Eb.below] :=
    hNf ▸ hN
  have hself : Module.finrank
      𝓀[abstractFixedField K (AlgebraicClosure K) Kb.field]
      𝓀[abstractRelativeFixedField K (AlgebraicClosure K) Eb.below] =
      Module.finrank
          𝓀[abstractFixedField K (AlgebraicClosure K) Kb.field]
          𝓀[abstractRelativeFixedField K (AlgebraicClosure K) Eb.below] *
        Nat.card (lowerRamificationGroup
          (abstractFixedField K (AlgebraicClosure K) Kb.field)
          (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below)
          0) := by
    calc (Module.finrank
          𝓀[abstractFixedField K (AlgebraicClosure K) Kb.field]
          𝓀[abstractRelativeFixedField K (AlgebraicClosure K) Eb.below])
        = Module.finrank
            (abstractFixedField K (AlgebraicClosure K) Kb.field)
            (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below) :=
          hNf.symm
      _ = _ := h5
  have hone : Nat.card (lowerRamificationGroup
      (abstractFixedField K (AlgebraicClosure K) Kb.field)
      (abstractRelativeFixedField K (AlgebraicClosure K) Eb.below) 0) = 1 :=
    (Nat.eq_of_mul_eq_mul_left hfpos
      (by rw [Nat.mul_one]; exact hself)).symm
  exact Subgroup.eq_bot_of_card_eq _ hone

end

end Atlas.Knowledge
