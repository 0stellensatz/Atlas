import Mathlib
import Atlas.Knowledge.AbstractFixedField
import Atlas.Knowledge.AdditiveNormSubgroup
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.ClassFieldAxiom
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbelianClassification
import Atlas.Knowledge.FiniteAbelianSubextension
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.FiniteNormQuotientEquivNormQuotient
import Atlas.Knowledge.GaloisExtensionQuotient
import Atlas.Knowledge.IntermediateFieldNormResidueNaturality
import Atlas.Knowledge.IntermediateFieldUnitsFixedSubgroup
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.LocalClassFieldAxiom
import Atlas.Knowledge.LocalHenselianValuation
import Atlas.Knowledge.LocalResidueDatum
import Atlas.Knowledge.NormQuotient
import Atlas.Knowledge.NormSubgroupMap
import Atlas.Knowledge.NormSubgroupOrderEmbedding
import Atlas.Knowledge.NormTopology
import Atlas.Knowledge.ResidueDatumIn
import Atlas.Knowledge.SeparableFixedFieldNorm
import Atlas.Knowledge.UnitCohomologyAxiom
import Atlas.Knowledge.UnitCohomologyDischarge
import Atlas.Knowledge.ValuationData

/-!
# norm subgroup surjectivity

The surjectivity half of the local classification for a
mixed-characteristic local field `K` (#104): an open finite-index
subgroup of `Kˣ` which is open for the abstract norm topology —
transported to the base fixed coefficients — is the ordinary norm
subgroup of a finite abelian subextension, so the norm subgroup map is
surjective once every finite-index subgroup is norm-open; and a finite
Galois extension whose norm subgroup lies in `H` witnesses exactly that
norm-openness. With the two ordinary norm laws
`N_{L₁L₂} = N_{L₁} ∩ N_{L₂}` and `N_{L₁ ∩ L₂} = N_{L₁} N_{L₂}`
transported from the abstract classification. The finite local
existence theorem is one input away: for every open finite-index
subgroup `H` of `Kˣ` a finite Galois extension whose norm subgroup lies
in `H`, which the standard open subgroups and the compositum of a
Lubin–Tate level field with an unramified extension supply.

## Main statements

* `exists_finiteAbelianNormSubgroup_eq_of_normOpen` — an open
  finite-index subgroup which is open for the abstract norm topology,
  transported to the base fixed coefficients, is the ordinary norm
  subgroup of a finite abelian subextension; proved.
* `finiteAbelianNormSubgroupMap_surjective_of_normOpen`,
  `localFiniteAbelianNormSubgroupMap_surjective_of_normOpen` —
  surjectivity from norm-openness of every finite-index subgroup,
  threaded and at the algebraic closure; proved.
* `finiteIndexSubgroup_isNormOpen_of_normSubgroup_le` — a finite Galois
  extension with norm subgroup in `H` makes `H` norm-open; proved.
* `finiteAbelianNormSubgroup_compositum`,
  `finiteAbelianNormSubgroup_intersection` — the ordinary norm laws,
  with their `local`-prefixed closers; proved.
* `exists_finiteGaloisExtension_normSubgroup_map_le_of_normSubgroup_le`
  — a concrete finite Galois extension packaged in the absolute Galois
  model with its norm bound; proved.

## Implementation notes

The ambient conversion of the layer's reciprocity arc, as in
`Atlas.Knowledge.NormSubgroupOrderEmbedding`: the source's pinned
`SeparableClosure K` and intrinsic abbreviations become a separably
closed Galois ambient `Ω` with `galoisAmbientUnitsRep K Ω`,
`closedFixingSubgroup ⊥`, and
`Atlas.Knowledge.galoisAmbientFiniteAbstractBase`, the four
reciprocity-dependent declarations thread `D`, `v`, `hcf`, and
`hAxiom`, and the closers at `AlgebraicClosure K` supply the layer's
local data. The source's chosen embedding
`separableEmbeddingIntoSeparableClosure` is Mathlib's
`IsSepClosed.lift` over `Ω`, and the realization's finiteness witness
is the layer's `baseFixingExtensionQuotient_finite_of_isSeparable`. The
two ordinary norm laws, the norm-openness witness, and the packaging
sit outside the local-field section, since the threaded form needs no
local field where the source's class-field-axiom witness did, and the
source's `omit` of the local-field binders on the last two is thereby
the section boundary. The local field is `IsMixedCharLocalField` where
the source's is nonarchimedean, and the source's `Type` is the layer's
`Type u`. The norm-openness witness keeps the source's
`[H.FiniteIndex]` binder, which its proof never uses — the openness
criterion `normTopology_addSubgroup_isOpen_iff` carries no index
hypothesis — for the statement's fidelity and its name; the
surjectivity theorem's norm-openness hypothesis, which the witness
exists to discharge, binds the instance itself, so shedding it would
buy that consumer nothing. The import block lists every item whose
declarations the file spells, the class `IsMixedCharLocalField` and the
field `SatisfiesUnramifiedUnitCohomology` included. Everything else
ports token-for-token; the file is the source's
`Finite/Existence/NormSubgroupSurjectivity.lean`.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable (K : Type u) [Field K]
variable (Ω : Type u) [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]

/-- **The ordinary norm subgroup of a compositum is the intersection of
the two ordinary norm subgroups**, given the reciprocity inputs over
the ambient ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupSurjectivity.lean:31`]
[Yamaguchi2026]). -/
theorem finiteAbelianNormSubgroup_compositum
    (D : DegreeData (Ω ≃ₐ[K] Ω)) (v : ValuationData D (galoisAmbientUnitsRep K Ω))
    (hcf : SatisfiesClassFieldAxiom (galoisAmbientUnitsRep K Ω))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (L₁ L₂ : FiniteAbelianSubextension (closedFixingSubgroup (⊥ : IntermediateField K Ω))) :
    finiteAbelianNormSubgroup K Ω (L₁.compositum L₂) =
      finiteAbelianNormSubgroup K Ω L₁ ⊓
        finiteAbelianNormSubgroup K Ω L₂ := by
  have habs :=
    FiniteAbelianSubextension.normSubgroup_compositum
      v hcf hAxiom (galoisAmbientFiniteAbstractBase K Ω) L₁ L₂
  have hmapped := congrArg
    (fun S : AddSubgroup
        (ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup (⊥ : IntermediateField K Ω))) ↦
      S.map (baseUnitsEquivGaloisAmbientFixed K Ω).symm.toAddMonoidHom) habs
  change ((L₁.compositum L₂).normSubgroup
      (galoisAmbientUnitsRep K Ω)).map
        (baseUnitsEquivGaloisAmbientFixed K Ω).symm.toAddMonoidHom =
    (L₁.normSubgroup (galoisAmbientUnitsRep K Ω) ⊓
      L₂.normSubgroup (galoisAmbientUnitsRep K Ω)).map
        (baseUnitsEquivGaloisAmbientFixed K Ω).symm.toAddMonoidHom at hmapped
  rw [AddSubgroup.map_inf _ _ _
    (baseUnitsEquivGaloisAmbientFixed K Ω).symm.injective] at hmapped
  rw [map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup,
    map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup,
    map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup] at hmapped
  apply Subgroup.ext
  intro x
  change Additive.ofMul x ∈ additiveNormSubgroup K
      (abstractFixedField K Ω
        (L₁.compositum L₂).field) ↔
    Additive.ofMul x ∈
      (additiveNormSubgroup K
        (abstractFixedField K Ω L₁.field) ⊓
       additiveNormSubgroup K
        (abstractFixedField K Ω L₂.field))
  exact Iff.of_eq (congrArg
    (fun S : AddSubgroup (Additive Kˣ) => Additive.ofMul x ∈ S) hmapped)

/-- **The ordinary norm subgroup of an intersection field is the
supremum of the two ordinary norm subgroups**, given the reciprocity
inputs over the ambient ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupSurjectivity.lean:72`]
[Yamaguchi2026]). -/
theorem finiteAbelianNormSubgroup_intersection
    (D : DegreeData (Ω ≃ₐ[K] Ω)) (v : ValuationData D (galoisAmbientUnitsRep K Ω))
    (hcf : SatisfiesClassFieldAxiom (galoisAmbientUnitsRep K Ω))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (L₁ L₂ : FiniteAbelianSubextension (closedFixingSubgroup (⊥ : IntermediateField K Ω))) :
    finiteAbelianNormSubgroup K Ω (L₁.intersection L₂) =
      finiteAbelianNormSubgroup K Ω L₁ ⊔
        finiteAbelianNormSubgroup K Ω L₂ := by
  have habs :=
    FiniteAbelianSubextension.normSubgroup_intersection
      v hcf hAxiom (galoisAmbientFiniteAbstractBase K Ω) L₁ L₂
  have hmapped := congrArg
    (fun S : AddSubgroup
        (ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup (⊥ : IntermediateField K Ω))) ↦
      S.map (baseUnitsEquivGaloisAmbientFixed K Ω).symm.toAddMonoidHom) habs
  change ((L₁.intersection L₂).normSubgroup
      (galoisAmbientUnitsRep K Ω)).map
        (baseUnitsEquivGaloisAmbientFixed K Ω).symm.toAddMonoidHom =
    (L₁.normSubgroup (galoisAmbientUnitsRep K Ω) ⊔
      L₂.normSubgroup (galoisAmbientUnitsRep K Ω)).map
        (baseUnitsEquivGaloisAmbientFixed K Ω).symm.toAddMonoidHom at hmapped
  rw [AddSubgroup.map_sup] at hmapped
  rw [map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup,
    map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup,
    map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup] at hmapped
  apply (Subgroup.toAddSubgroup :
    Subgroup Kˣ ≃o AddSubgroup (Additive Kˣ)).injective
  change additiveNormSubgroup K
      (abstractFixedField K Ω
        (L₁.intersection L₂).field) =
    Subgroup.toAddSubgroup
      (finiteAbelianNormSubgroup K Ω L₁ ⊔
        finiteAbelianNormSubgroup K Ω L₂)
  rw [(Subgroup.toAddSubgroup :
    Subgroup Kˣ ≃o AddSubgroup (Additive Kˣ)).map_sup]
  exact hmapped

/-- **A finite Galois extension whose ordinary norm subgroup is
contained in `H` witnesses that `H` is open for the abstract norm
topology** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupSurjectivity.lean:188`]
[Yamaguchi2026]). -/
theorem finiteIndexSubgroup_isNormOpen_of_normSubgroup_le
    (E : Type u) [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    (H : Subgroup Kˣ) [H.FiniteIndex]
    (hnorm : localNormSubgroup K E ≤ H) :
    let A := galoisAmbientUnitsRep K Ω
    let B := closedFixingSubgroup (⊥ : IntermediateField K Ω)
    let e := baseUnitsEquivGaloisAmbientFixed K Ω
    IsNormOpen A B
      ((H.toAddSubgroup.map e.toAddMonoidHom :
        AddSubgroup (ambientFixedAddSubgroup A B)) :
        Set (ambientFixedAddSubgroup A B)) := by
  let A := galoisAmbientUnitsRep K Ω
  let B := closedFixingSubgroup (⊥ : IntermediateField K Ω)
  let e := baseUnitsEquivGaloisAmbientFixed K Ω
  let i : E →ₐ[K] Ω := IsSepClosed.lift
  let R : IntermediateField K Ω := AlgHom.fieldRange i
  letI : FiniteDimensional K R :=
    (AlgEquiv.ofInjectiveField i).toLinearEquiv.finiteDimensional
  letI : IsGalois K R := IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField i)
  let L : FiniteGaloisSubextension B := {
    field := closedFixingSubgroup R
    below := fixingSubgroupLeBase K Ω R
    normal := inferInstance
    finite := baseFixingExtensionQuotient_finite_of_isSeparable K Ω R }
  have hnormLe : additiveNormSubgroup K R ≤ H.toAddSubgroup := by
    intro x hx
    change Additive.toMul x ∈ localNormSubgroup K R at hx
    change Additive.toMul x ∈ H
    apply hnorm
    rw [← localNormSubgroup_fieldRange_eq K Ω E i]
    exact hx
  have hmap :
      (L.normSubgroup A).map e.symm.toAddMonoidHom =
        additiveNormSubgroup K R := by
    simpa [A, B, L, R, e,
      FiniteGaloisSubextension.normSubgroup] using
      (map_finiteNormSubgroup_eq_additiveNormSubgroup
        K Ω R)
  have hLE :
      L.normSubgroup A ≤ H.toAddSubgroup.map e.toAddMonoidHom := by
    intro x hx
    have hxmap : e.symm x ∈
        (L.normSubgroup A).map e.symm.toAddMonoidHom :=
      ⟨x, hx, rfl⟩
    rw [hmap] at hxmap
    exact ⟨e.symm x, hnormLe hxmap, e.apply_symm_apply x⟩
  exact (normTopology_addSubgroup_isOpen_iff A B
    (H.toAddSubgroup.map e.toAddMonoidHom)).2 ⟨L, hLE⟩

/-- Package a concrete finite Galois extension in the absolute Galois
model, retaining a prescribed upper bound for its ordinary norm
subgroup ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupSurjectivity.lean:243`]
[Yamaguchi2026]). -/
theorem exists_finiteGaloisExtension_normSubgroup_map_le_of_normSubgroup_le
    (E : Type u) [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    (J : Subgroup Kˣ)
    (hnorm : localNormSubgroup K E ≤ J) :
    ∃ T : FiniteGaloisSubextension (closedFixingSubgroup (⊥ : IntermediateField K Ω)),
      (T.normSubgroup (galoisAmbientUnitsRep K Ω)).map
          (baseUnitsEquivGaloisAmbientFixed K Ω).symm.toAddMonoidHom ≤
        J.toAddSubgroup := by
  let A := galoisAmbientUnitsRep K Ω
  let B := closedFixingSubgroup (⊥ : IntermediateField K Ω)
  let e := baseUnitsEquivGaloisAmbientFixed K Ω
  let i : E →ₐ[K] Ω := IsSepClosed.lift
  let R : IntermediateField K Ω := AlgHom.fieldRange i
  letI : FiniteDimensional K R :=
    (AlgEquiv.ofInjectiveField i).toLinearEquiv.finiteDimensional
  letI : IsGalois K R := IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField i)
  let T : FiniteGaloisSubextension B := {
    field := closedFixingSubgroup R
    below := fixingSubgroupLeBase K Ω R
    normal := inferInstance
    finite := baseFixingExtensionQuotient_finite_of_isSeparable K Ω R }
  have hmap :
      (T.normSubgroup A).map e.symm.toAddMonoidHom =
        additiveNormSubgroup K R := by
    simpa [A, B, e, T, R, FiniteGaloisSubextension.normSubgroup] using
      (map_finiteNormSubgroup_eq_additiveNormSubgroup
        K Ω R)
  refine ⟨T, ?_⟩
  intro x hx
  rw [hmap] at hx
  change Additive.toMul x ∈ J
  apply hnorm
  rw [← localNormSubgroup_fieldRange_eq K Ω E i]
  exact hx

section LocalField

variable [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/-- A native open finite-index subgroup which is open for the abstract
norm topology is the ordinary norm subgroup of a finite abelian
subextension, given the reciprocity inputs over the ambient `Ω`
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupSurjectivity.lean:111`]
[Yamaguchi2026]). -/
theorem exists_finiteAbelianNormSubgroup_eq_of_normOpen
    (D : DegreeData (Ω ≃ₐ[K] Ω)) (v : ValuationData D (galoisAmbientUnitsRep K Ω))
    (hcf : SatisfiesClassFieldAxiom (galoisAmbientUnitsRep K Ω))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (H : OpenFiniteIndexSubgroup K)
    (hnormOpen :
      IsNormOpen (galoisAmbientUnitsRep K Ω) (closedFixingSubgroup (⊥ : IntermediateField K Ω))
        ((H.subgroup.toAddSubgroup.map
          (baseUnitsEquivGaloisAmbientFixed K Ω).toAddMonoidHom :
          AddSubgroup (ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
            (closedFixingSubgroup (⊥ : IntermediateField K Ω)))) : Set _)) :
    ∃ L, finiteAbelianNormSubgroupMap K Ω L = H := by
  letI : H.subgroup.FiniteIndex := H.finiteIndex
  let Habs : AddSubgroup
      (ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup (⊥ : IntermediateField K Ω))) :=
    H.subgroup.toAddSubgroup.map
      (baseUnitsEquivGaloisAmbientFixed K Ω).toAddMonoidHom
  have hopen :
      IsNormOpen (galoisAmbientUnitsRep K Ω) (closedFixingSubgroup (⊥ : IntermediateField K Ω))
        (Habs : Set _) := by
    simpa only [Habs] using hnormOpen
  let Hopen : FiniteAbelianSubextension.NormOpenAddSubgroup
      (galoisAmbientUnitsRep K Ω) (closedFixingSubgroup (⊥ : IntermediateField K Ω)) :=
    ⟨Habs, hopen⟩
  obtain ⟨L, hL⟩ :=
    FiniteAbelianSubextension.normSubgroupMap_surjective
      v hcf hAxiom (galoisAmbientFiniteAbstractBase K Ω) Hopen
  refine ⟨L, ?_⟩
  apply OpenFiniteIndexSubgroup.ext
  have habs : L.normSubgroup (galoisAmbientUnitsRep K Ω) = Habs :=
    congrArg Subtype.val hL
  have hmapped := congrArg
    (fun S : AddSubgroup
        (ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup (⊥ : IntermediateField K Ω))) ↦
      S.map (baseUnitsEquivGaloisAmbientFixed K Ω).symm.toAddMonoidHom) habs
  change (L.normSubgroup (galoisAmbientUnitsRep K Ω)).map
      (baseUnitsEquivGaloisAmbientFixed K Ω).symm.toAddMonoidHom =
    Habs.map (baseUnitsEquivGaloisAmbientFixed K Ω).symm.toAddMonoidHom at hmapped
  rw [map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup] at hmapped
  have hcancel :
      Habs.map (baseUnitsEquivGaloisAmbientFixed K Ω).symm.toAddMonoidHom =
        H.subgroup.toAddSubgroup := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hx
      refine ⟨baseUnitsEquivGaloisAmbientFixed K Ω x, ⟨x, hx, rfl⟩, ?_⟩
      exact (baseUnitsEquivGaloisAmbientFixed K Ω).symm_apply_apply x
  rw [hcancel] at hmapped
  apply Subgroup.ext
  intro x
  change Additive.ofMul x ∈ additiveNormSubgroup K
      (abstractFixedField K Ω L.field) ↔
    Additive.ofMul x ∈ H.subgroup.toAddSubgroup
  exact Iff.of_eq (congrArg
    (fun S : AddSubgroup (Additive Kˣ) => Additive.ofMul x ∈ S) hmapped)

/-- **If all native finite-index subgroups are norm-open, the ordinary
norm-subgroup map is surjective**, given the reciprocity inputs over
the ambient ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupSurjectivity.lean:171`]
[Yamaguchi2026]). -/
theorem finiteAbelianNormSubgroupMap_surjective_of_normOpen
    (D : DegreeData (Ω ≃ₐ[K] Ω)) (v : ValuationData D (galoisAmbientUnitsRep K Ω))
    (hcf : SatisfiesClassFieldAxiom (galoisAmbientUnitsRep K Ω))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (hnormOpen : ∀ (H : Subgroup Kˣ) [H.FiniteIndex],
      IsNormOpen (galoisAmbientUnitsRep K Ω) (closedFixingSubgroup (⊥ : IntermediateField K Ω))
        ((H.toAddSubgroup.map
          (baseUnitsEquivGaloisAmbientFixed K Ω).toAddMonoidHom :
          AddSubgroup (ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
            (closedFixingSubgroup (⊥ : IntermediateField K Ω)))) : Set _)) :
    Function.Surjective (finiteAbelianNormSubgroupMap K Ω) := by
  intro H
  letI : H.subgroup.FiniteIndex := H.finiteIndex
  apply exists_finiteAbelianNormSubgroup_eq_of_normOpen K Ω D v hcf hAxiom H
  exact hnormOpen H.subgroup

end LocalField

section AlgebraicClosure

variable [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

/-- The compositum norm law at the algebraic closure, with the layer's
local data supplied ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupSurjectivity.lean:31`]
[Yamaguchi2026]). -/
theorem localFiniteAbelianNormSubgroup_compositum
    (L₁ L₂ : FiniteAbelianSubextension
      (closedFixingSubgroup (⊥ : IntermediateField K (AlgebraicClosure K)))) :
    finiteAbelianNormSubgroup K (AlgebraicClosure K) (L₁.compositum L₂) =
      finiteAbelianNormSubgroup K (AlgebraicClosure K) L₁ ⊓
        finiteAbelianNormSubgroup K (AlgebraicClosure K) L₂ := by
  exact finiteAbelianNormSubgroup_compositum K (AlgebraicClosure K)
    (localResidueDatum K) (localHenselianValuation K)
    (algebraicClosureUnits_satisfiesClassFieldAxiom K)
    (localHenselianValuation_satisfiesUnramifiedUnitCohomology K) L₁ L₂

/-- The intersection norm law at the algebraic closure, with the
layer's local data supplied ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupSurjectivity.lean:72`]
[Yamaguchi2026]). -/
theorem localFiniteAbelianNormSubgroup_intersection
    (L₁ L₂ : FiniteAbelianSubextension
      (closedFixingSubgroup (⊥ : IntermediateField K (AlgebraicClosure K)))) :
    finiteAbelianNormSubgroup K (AlgebraicClosure K) (L₁.intersection L₂) =
      finiteAbelianNormSubgroup K (AlgebraicClosure K) L₁ ⊔
        finiteAbelianNormSubgroup K (AlgebraicClosure K) L₂ := by
  exact finiteAbelianNormSubgroup_intersection K (AlgebraicClosure K)
    (localResidueDatum K) (localHenselianValuation K)
    (algebraicClosureUnits_satisfiesClassFieldAxiom K)
    (localHenselianValuation_satisfiesUnramifiedUnitCohomology K) L₁ L₂

/-- **Surjectivity of the norm-subgroup map at the algebraic closure**
from norm-openness of every finite-index subgroup, with the layer's
local data supplied ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupSurjectivity.lean:171`]
[Yamaguchi2026]). -/
theorem localFiniteAbelianNormSubgroupMap_surjective_of_normOpen
    (hnormOpen : ∀ (H : Subgroup Kˣ) [H.FiniteIndex],
      IsNormOpen (galoisAmbientUnitsRep K (AlgebraicClosure K))
        (closedFixingSubgroup (⊥ : IntermediateField K (AlgebraicClosure K)))
        ((H.toAddSubgroup.map
          (baseUnitsEquivGaloisAmbientFixed K (AlgebraicClosure K)).toAddMonoidHom :
          AddSubgroup (ambientFixedAddSubgroup (galoisAmbientUnitsRep K (AlgebraicClosure K))
            (closedFixingSubgroup (⊥ : IntermediateField K (AlgebraicClosure K))))) : Set _)) :
    Function.Surjective (finiteAbelianNormSubgroupMap K (AlgebraicClosure K)) := by
  exact finiteAbelianNormSubgroupMap_surjective_of_normOpen K (AlgebraicClosure K)
    (localResidueDatum K) (localHenselianValuation K)
    (algebraicClosureUnits_satisfiesClassFieldAxiom K)
    (localHenselianValuation_satisfiesUnramifiedUnitCohomology K) hnormOpen

end AlgebraicClosure

end

end Atlas.Knowledge
