import Mathlib
import Atlas.Knowledge.AbstractFixedField
import Atlas.Knowledge.AbstractFixedFieldNorm
import Atlas.Knowledge.AbstractFixedFieldUnitsEquiv
import Atlas.Knowledge.AdditiveNormSubgroup
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.ClassFieldAxiom
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbelianClassification
import Atlas.Knowledge.FiniteAbelianSubextension
import Atlas.Knowledge.FiniteExtensionTransitivity
import Atlas.Knowledge.FiniteLocalReciprocityLaw
import Atlas.Knowledge.GaloisExtensionQuotient
import Atlas.Knowledge.IntermediateFieldNormResidueNaturality
import Atlas.Knowledge.IntermediateFieldUnitsFixedSubgroup
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.LocalClassFieldAxiom
import Atlas.Knowledge.LocalHenselianValuation
import Atlas.Knowledge.LocalResidueDatum
import Atlas.Knowledge.NormQuotient
import Atlas.Knowledge.NormUnits
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.ResidueDatumIn
import Atlas.Knowledge.SeparableFixedFieldNorm
import Atlas.Knowledge.UnitCohomologyAxiom
import Atlas.Knowledge.UnitCohomologyDischarge
import Atlas.Knowledge.UnitsFiniteIndexOpen
import Atlas.Knowledge.ValuationData

/-!
# norm subgroup order embedding

The norm subgroup map of a mixed-characteristic local field `K`,
`L ↦ N_{L/K} Lˣ`, from the finite abelian subextensions of the Galois
group of a separably closed Galois ambient — at the algebraic closure,
the absolute Galois group; the class formation's abstract subextensions
over the fixing subgroup of the base — to the open finite-index
subgroups of `Kˣ`, as an order embedding into the opposite poset: the
abstract classification's injectivity and order reversal (#104),
transported through the identification of the abstract norm subgroup
with the ordinary norm subgroup of the represented fixed field. The
abstract data lives over a separably closed Galois ambient `Ω`, with
the reciprocity inputs threaded, and closes at the algebraic closure
with the layer's local data.

## Main definitions

* `OpenFiniteIndexSubgroup` — the open finite-index subgroups of `Kˣ`,
  ordered by inclusion.
* `finiteAbelianNormSubgroup`, `finiteAbelianNormSubgroupMap` — the
  ordinary norm subgroup of the represented fixed field, and the map
  into open finite-index subgroups.
* `finiteAbelianNormSubgroupOrderEmbedding`,
  `localFiniteAbelianNormSubgroupOrderEmbedding` — the order embedding,
  threaded over the ambient and closed at the algebraic closure.

## Main statements

* `abstractFixedField_isGalois_of_base_normal` — normality over the
  base fixing group makes the fixed field Galois; proved.
* `finiteAbelianSubextension_fixedField_isAbelianGalois` — the
  represented fixed field is abelian; proved.
* `map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup` — the
  abstract norm subgroup transports to the ordinary one; proved.
* `finiteAbelianNormSubgroupMap_injective`,
  `finiteAbelianSubextension_le_iff_normSubgroup_le` — injectivity and
  order reversal, with their `local`-prefixed closers at the algebraic
  closure; proved.

## Implementation notes

The ambient conversion of the layer's reciprocity arc: the source works
over its pinned `SeparableClosure K` through the intrinsic
abbreviations, the layer over a separably closed Galois ambient `Ω` —
`intrinsicAbsoluteUnits`, `intrinsicAbstractBase`, and
`intrinsicFiniteAbstractBase` become `galoisAmbientUnitsRep K Ω`,
`closedFixingSubgroup ⊥`, and
`Atlas.Knowledge.galoisAmbientFiniteAbstractBase` — instantiated at
`AlgebraicClosure K` in the closing declarations, where the layer's
local data live (`Atlas.Knowledge.localHenselianValuation`,
`Atlas.Knowledge.algebraicClosureUnits_satisfiesClassFieldAxiom`,
`Atlas.Knowledge.localHenselianValuation_satisfiesUnramifiedUnitCohomology`),
the Galoisness of the algebraic closure an instance, `K` having
characteristic zero. The base index finiteness
`intrinsicAbstractBase_index_finite` is renamed
`galoisAmbientBase_index_finite` with the abbreviation it is stated
over. The three reciprocity-dependent declarations thread `D`, `v`,
`hcf`, and `hAxiom` in their general form, as the layer's `OfEmbedding`
halves do, and their `local`-prefixed closers supply all four. The
local field is `IsMixedCharLocalField` where the source's is
nonarchimedean, the layer's instantiation being mixed-characteristic
throughout. Openness of the norm subgroup is the layer's
`Atlas.Knowledge.unitsFiniteIndexOpen` applied to its finite index, so
`finiteAbelianNormSubgroup_finiteIndex` precedes
`finiteAbelianNormSubgroup_isOpen` here, where the source proves
openness first through its `TopologicalReciprocity.lean`, which the
layer does not carry. The source's `LocalAbsoluteData.lean` — its
`OpenFiniteIndexSubgroup`, the Galoisness criterion, and the base index
finiteness, hoisted over `Ω` — is ported alongside as its first
consumer arrives. The import block lists every item whose declarations
the file spells, `Atlas.Knowledge.NormSubgroupMap` reaching it only
through the classification's statements and so through that import. The
relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
`mem_extensionSubgroup_iff` becoming Mathlib's
`Subgroup.mem_subgroupOf`, so the Galoisness criterion's `hsub` bridge
is gone; the Galois groups are spelled `≃ₐ[·]`, `closedFixingSubgroup`
takes only the intermediate field, the tower finiteness is the layer's
top-level `finite_extension_trans`, and
`finiteAbelianSubextension_le_iff_normSubgroup_le` omits the
local-field binders its statement never needed. Everything else ports
token-for-token; the file is the source's
`Finite/Existence/LocalAbsoluteData.lean` and
`Finite/Existence/NormSubgroupOrderEmbedding.lean`.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

/-- **An open finite-index subgroup of the ordinary topological group
`Kˣ`** — a genuine public object rather than a transparent subtype
alias, so that its topological and finite-index contracts remain
available without exposing a particular nested-pair representation
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/LocalAbsoluteData.lean:26`]
[Yamaguchi2026]). -/
structure OpenFiniteIndexSubgroup
    (K : Type u) [Field K] [TopologicalSpace K] where
  /-- The underlying subgroup of field units. -/
  subgroup : Subgroup Kˣ
  /-- The underlying subgroup is open in the unit-group topology. -/
  isOpen : IsOpen (subgroup : Set Kˣ)
  /-- The underlying subgroup has finite index. -/
  finiteIndex : subgroup.FiniteIndex

namespace OpenFiniteIndexSubgroup

variable {K : Type u} [Field K] [TopologicalSpace K]

/-- An open finite-index subgroup coerces to its underlying subgroup
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/LocalAbsoluteData.lean:40`]
[Yamaguchi2026]). -/
instance : Coe (OpenFiniteIndexSubgroup K) (Subgroup Kˣ) :=
  ⟨OpenFiniteIndexSubgroup.subgroup⟩

/-- Two open finite-index subgroups with the same underlying subgroup
are equal ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/LocalAbsoluteData.lean:45`]
[Yamaguchi2026]). -/
@[ext]
theorem ext {H H' : OpenFiniteIndexSubgroup K}
    (h : H.subgroup = H'.subgroup) : H = H' := by
  cases H
  cases H'
  cases h
  rfl

/-- Open finite-index subgroups inherit the inclusion order of their
underlying subgroups ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/LocalAbsoluteData.lean:53`]
[Yamaguchi2026]). -/
instance : PartialOrder (OpenFiniteIndexSubgroup K) :=
  PartialOrder.lift OpenFiniteIndexSubgroup.subgroup
    (fun _ _ h ↦ OpenFiniteIndexSubgroup.ext h)

end OpenFiniteIndexSubgroup

variable (K : Type u) [Field K]
variable (Ω : Type u) [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]

omit [IsSepClosed Ω] in
/-- **Normality over the abstract base fixing group makes the
represented fixed field Galois over the concrete base field**
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/LocalAbsoluteData.lean:61`]
[Yamaguchi2026]). -/
theorem abstractFixedField_isGalois_of_base_normal
    (H : ClosedSubgroup (Ω ≃ₐ[K] Ω))
    (hnormal :
      (H.toSubgroup.subgroupOf (baseField (Ω ≃ₐ[K] Ω)).toSubgroup).Normal) :
    IsGalois K (abstractFixedField K Ω H) := by
  let B := baseField (Ω ≃ₐ[K] Ω)
  have hrelative :
      (H.toSubgroup.subgroupOf B.toSubgroup).Normal := hnormal
  have hconj :
      ∀ h g : Ω ≃ₐ[K] Ω,
        h ∈ H.toSubgroup → g ∈ B.toSubgroup →
          g * h * g⁻¹ ∈ H.toSubgroup :=
    (Subgroup.normal_subgroupOf_iff (le_baseField H)).1 hrelative
  letI : H.toSubgroup.Normal :=
    { conj_mem := fun h hh g => hconj h g hh (by simp [B, baseField]) }
  apply (InfiniteGalois.normal_iff_isGalois
    (abstractFixedField K Ω H)).1
  have hfix :
      (abstractFixedField K Ω H).fixingSubgroup =
        H.toSubgroup := by
    have hclosed := closedFixingSubgroup_abstractFixedField_eq K Ω H
    exact congrArg ClosedSubgroup.toSubgroup hclosed
  rw [hfix]
  infer_instance

omit [IsSepClosed Ω] in
/-- The closed fixing group of the ground field is absolutely finite in
the abstract Galois-theoretic sense — it is the full absolute Galois
group ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/LocalAbsoluteData.lean:101`]
[Yamaguchi2026]). -/
instance galoisAmbientBase_index_finite :
    Finite ((baseField (Ω ≃ₐ[K] Ω)).toSubgroup ⧸
      (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup.subgroupOf
        (baseField (Ω ≃ₐ[K] Ω)).toSubgroup) :=
  (galoisAmbientFiniteAbstractBase K Ω).finite

omit [IsSepClosed Ω] in
/-- Finiteness over the concrete fixing group of the ground field
implies finiteness over the abstract class-formation `baseField`
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean:27`]
[Yamaguchi2026]). -/
theorem finiteAbelianSubextension_finite_over_absoluteBase
    (L : FiniteAbelianSubextension (closedFixingSubgroup (⊥ : IntermediateField K Ω))) :
    Finite ((baseField (Ω ≃ₐ[K] Ω)).toSubgroup ⧸
      L.field.toSubgroup.subgroupOf (baseField (Ω ≃ₐ[K] Ω)).toSubgroup) := by
  letI : Finite ((closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      L.field.toSubgroup.subgroupOf
        (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup) :=
    L.finite
  simpa only using
    (finite_extension_trans L.below
      (le_baseField (closedFixingSubgroup (⊥ : IntermediateField K Ω))))

omit [IsSepClosed Ω] in
/-- Normality over the concrete ground-field fixing group is normality
over the abstract class-formation `baseField` ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean:41`]
[Yamaguchi2026]). -/
theorem finiteAbelianSubextension_normal_over_absoluteBase
    (L : FiniteAbelianSubextension (closedFixingSubgroup (⊥ : IntermediateField K Ω))) :
    (L.field.toSubgroup.subgroupOf (baseField (Ω ≃ₐ[K] Ω)).toSubgroup).Normal := by
  refine { conj_mem := fun h hh g ↦ ?_ }
  rw [Subgroup.mem_subgroupOf] at hh ⊢
  let h' : (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup := ⟨h, L.below hh⟩
  let g' : (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup := ⟨g, by
    rw [show closedFixingSubgroup (⊥ : IntermediateField K Ω) =
        baseField (Ω ≃ₐ[K] Ω) from
      closedFixingSubgroup_bot_eq_baseField K Ω]
    exact g.property⟩
  have hh' : h' ∈ L.field.toSubgroup.subgroupOf
      (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup :=
    Subgroup.mem_subgroupOf.2 hh
  have hout := L.normal.conj_mem h' hh' g'
  have hout' := Subgroup.mem_subgroupOf.1 hout
  change ((g : Ω ≃ₐ[K] Ω) *
      (h : Ω ≃ₐ[K] Ω) *
      (g : Ω ≃ₐ[K] Ω)⁻¹) ∈ L.field
  change ((g' : Ω ≃ₐ[K] Ω) *
      (h' : Ω ≃ₐ[K] Ω) *
      (g' : Ω ≃ₐ[K] Ω)⁻¹) ∈ L.field at hout'
  exact hout'

omit [IsSepClosed Ω] in
/-- **The ordinary norm subgroup of the fixed field represented by an
abstract finite abelian extension** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean:70`]
[Yamaguchi2026]). -/
def finiteAbelianNormSubgroup
    (L : FiniteAbelianSubextension (closedFixingSubgroup (⊥ : IntermediateField K Ω))) :
    Subgroup Kˣ :=
  localNormSubgroup K (abstractFixedField K Ω L.field)

omit [IsSepClosed Ω] in
/-- The fixed field represented by an abstract finite abelian extension
is an actual finite abelian extension of `K`; the commutativity
assertion is transported across the concrete quotient–Galois-group
equivalence, rather than being inferred merely from the name of the
abstract package ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean:78`]
[Yamaguchi2026]). -/
theorem finiteAbelianSubextension_fixedField_isAbelianGalois
    (L : FiniteAbelianSubextension (closedFixingSubgroup (⊥ : IntermediateField K Ω))) :
    IsAbelianGalois K
      (abstractFixedField K Ω L.field) := by
  let E := abstractFixedField K Ω L.field
  letI : Finite ((baseField (Ω ≃ₐ[K] Ω)).toSubgroup ⧸
      L.field.toSubgroup.subgroupOf (baseField (Ω ≃ₐ[K] Ω)).toSubgroup) :=
    finiteAbelianSubextension_finite_over_absoluteBase K Ω L
  letI : FiniteDimensional K E :=
    abstractFixedField_finiteDimensional
      K Ω L.field inferInstance
  letI : IsGalois K E :=
    abstractFixedField_isGalois_of_base_normal K Ω L.field
      (finiteAbelianSubextension_normal_over_absoluteBase K Ω L)
  letI : (L.field.toSubgroup.subgroupOf
      (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup).Normal := L.normal
  let e : L.extensionQuotient ≃* (E ≃ₐ[K] E) := by
    let e₀ := baseFixingExtensionQuotientEquivGaloisGroup
      K Ω E
    have hclosed : closedFixingSubgroup E =
        L.field :=
      closedFixingSubgroup_abstractFixedField_eq
        K Ω L.field
    have hsub :
        (closedFixingSubgroup E).toSubgroup.subgroupOf
            (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup =
          L.field.toSubgroup.subgroupOf
            (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup := by
      ext σ
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact SetLike.ext_iff.mp hclosed σ.1
    exact L.extensionQuotientMulEquiv.trans
      ((QuotientGroup.quotientMulEquivOfEq hsub.symm).trans e₀)
  refine { is_comm.comm := fun σ τ ↦ ?_ }
  exact e.symm.injective (by
    simpa only [map_mul] using
      mul_comm (e.symm σ) (e.symm τ))

omit [IsSepClosed Ω] in
/-- The concrete fixed field of an abstract compositum is the
compositum of the two concrete fixed fields inside the ambient
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean:119`]
[Yamaguchi2026]). -/
theorem finiteAbelianSubextension_compositum_fixedField
    (U T : FiniteAbelianSubextension (closedFixingSubgroup (⊥ : IntermediateField K Ω))) :
    abstractFixedField K Ω (U.compositum T).field =
      abstractFixedField K Ω U.field ⊔
        abstractFixedField K Ω T.field := by
  let EU := abstractFixedField K Ω U.field
  let ET := abstractFixedField K Ω T.field
  rw [← InfiniteGalois.fixedField_fixingSubgroup (EU ⊔ ET)]
  apply congrArg IntermediateField.fixedField
  change
    (U.field.toSubgroup ⊓ T.field.toSubgroup) =
      (EU ⊔ ET).fixingSubgroup
  rw [IntermediateField.fixingSubgroup_sup]
  rw [show EU.fixingSubgroup = U.field.toSubgroup by
      exact InfiniteGalois.fixingSubgroup_fixedField U.field,
    show ET.fixingSubgroup = T.field.toSubgroup by
      exact InfiniteGalois.fixingSubgroup_fixedField T.field]

/-- The relative class-formation norm of a unit in an arbitrary
abstract fixed field is the ordinary field norm, before identifying the
base fixed units with `Kˣ` ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean:140`]
[Yamaguchi2026]). -/
theorem relativeNorm_abstractFixedFieldUnit_val_of_isGalois
    (H : ClosedSubgroup (Ω ≃ₐ[K] Ω))
    (hH : H.toSubgroup ≤ (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup)
    [Finite ((closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      H.toSubgroup.subgroupOf (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup)]
    [FiniteDimensional K
      (abstractFixedField K Ω H)]
    [IsGalois K (abstractFixedField K Ω H)]
    (x : (abstractFixedField K Ω H)ˣ) :
    ((Additive.toMul
      ((relativeNorm (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup (⊥ : IntermediateField K Ω))
        H hH (abstractFixedFieldUnitsEquivGaloisFixed
          K Ω H (Additive.ofMul x))).1 :
        Additive Ωˣ) : Ωˣ) :
      Ω) =
      algebraMap K Ω
        (Algebra.norm K
          (x : abstractFixedField K Ω H)) := by
  let E := abstractFixedField K Ω H
  let y : ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω) H :=
    abstractFixedFieldUnitsEquivGaloisFixed
      K Ω H (Additive.ofMul x)
  let yE := intermediateFieldUnitsEquivGaloisFixed
    K Ω E (Additive.ofMul x)
  have hy : yE.1 = y.1 := by
    rw [intermediateFieldUnitsEquivGaloisFixed_coe]
    exact (abstractFixedFieldUnitsEquivGaloisFixed_coe
      K Ω H (Additive.ofMul x)).symm
  have hnorm :=
    relativeNorm_intermediateFieldUnit_val_of_isSeparable
      K Ω E x
  have htransport := relativeNorm_coe_eq_of_closedSubgroup_eq
    (galoisAmbientUnitsRep K Ω)
    (closedFixingSubgroup (⊥ : IntermediateField K Ω))
    (closedFixingSubgroup (⊥ : IntermediateField K Ω))
    (closedFixingSubgroup E) H
    (fixingSubgroupLeBase K Ω E) hH
    rfl (closedFixingSubgroup_abstractFixedField_eq
      K Ω H)
    yE y hy
  have htransport' := congrArg
    (fun z : Additive Ωˣ ↦
      ((Additive.toMul z : Ωˣ) : Ω))
    htransport
  change
    ((Additive.toMul
      ((relativeNorm (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup (⊥ : IntermediateField K Ω))
        H hH y).1 : Additive Ωˣ) :
        Ωˣ) : Ω) = _
  exact htransport'.symm.trans hnorm

/-- The preceding norm identity after identifying the base fixed units
with `Additive Kˣ` ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean:192`]
[Yamaguchi2026]). -/
theorem baseUnitsEquivGaloisAmbientFixed_symm_relativeNorm_abstractFixedFieldUnit_eq_normUnits
    (H : ClosedSubgroup (Ω ≃ₐ[K] Ω))
    (hH : H.toSubgroup ≤ (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup)
    [Finite ((closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      H.toSubgroup.subgroupOf (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup)]
    [FiniteDimensional K
      (abstractFixedField K Ω H)]
    [IsGalois K (abstractFixedField K Ω H)]
    (x : (abstractFixedField K Ω H)ˣ) :
    (baseUnitsEquivGaloisAmbientFixed K Ω).symm
      (relativeNorm (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup (⊥ : IntermediateField K Ω))
        H hH (abstractFixedFieldUnitsEquivGaloisFixed
          K Ω H (Additive.ofMul x))) =
      Additive.ofMul
        (normUnits K (abstractFixedField K Ω H) x) := by
  apply (baseUnitsEquivGaloisAmbientFixed K Ω).injective
  rw [(baseUnitsEquivGaloisAmbientFixed K Ω).apply_symm_apply]
  apply Subtype.ext
  apply Additive.ext
  apply Units.ext
  calc
    _ = algebraMap K Ω
        (Algebra.norm K
          (x : abstractFixedField K Ω H)) :=
      relativeNorm_abstractFixedFieldUnit_val_of_isGalois K Ω H hH x
    _ = algebraMap K Ω
        ((normUnits K (abstractFixedField K Ω H) x :
          Kˣ) : K) := by
      rw [normUnits_apply_coe]
    _ = _ :=
      (baseUnitsEquivGaloisAmbientFixed_val K Ω
        (normUnits K (abstractFixedField K Ω H) x)).symm

/-- **Transporting the abstract finite norm subgroup back to `Kˣ` gives
literally the ordinary norm subgroup of the represented fixed field**
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean:227`]
[Yamaguchi2026]). -/
theorem map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup
    (L : FiniteAbelianSubextension (closedFixingSubgroup (⊥ : IntermediateField K Ω))) :
    (L.normSubgroup (galoisAmbientUnitsRep K Ω)).map
        (baseUnitsEquivGaloisAmbientFixed K Ω).symm.toAddMonoidHom =
      additiveNormSubgroup K
        (abstractFixedField K Ω L.field) := by
  letI : Finite ((closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      L.field.toSubgroup.subgroupOf
        (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup) :=
    L.finite
  letI : Finite ((baseField (Ω ≃ₐ[K] Ω)).toSubgroup ⧸
      L.field.toSubgroup.subgroupOf (baseField (Ω ≃ₐ[K] Ω)).toSubgroup) :=
    finiteAbelianSubextension_finite_over_absoluteBase K Ω L
  let E := abstractFixedField K Ω L.field
  letI : FiniteDimensional K E :=
    abstractFixedField_finiteDimensional
      K Ω L.field inferInstance
  letI : IsGalois K E :=
    abstractFixedField_isGalois_of_base_normal K Ω L.field
      (finiteAbelianSubextension_normal_over_absoluteBase K Ω L)
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases ha with ⟨b, rfl⟩
    let u : Eˣ := Additive.toMul
      ((abstractFixedFieldUnitsEquivGaloisFixed
        K Ω L.field).symm b)
    have hb :
        abstractFixedFieldUnitsEquivGaloisFixed
            K Ω L.field (Additive.ofMul u) = b := by
      change abstractFixedFieldUnitsEquivGaloisFixed
          K Ω L.field
            ((abstractFixedFieldUnitsEquivGaloisFixed
              K Ω L.field).symm b) = b
      exact (abstractFixedFieldUnitsEquivGaloisFixed
        K Ω L.field).apply_symm_apply b
    rw [← hb]
    change (baseUnitsEquivGaloisAmbientFixed K Ω).symm
      (relativeNorm (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup (⊥ : IntermediateField K Ω))
        L.field L.below (abstractFixedFieldUnitsEquivGaloisFixed
          K Ω L.field (Additive.ofMul u))) ∈
        additiveNormSubgroup K E
    rw [baseUnitsEquivGaloisAmbientFixed_symm_relativeNorm_abstractFixedFieldUnit_eq_normUnits]
    exact ⟨u, rfl⟩
  · intro hy
    change Additive.toMul y ∈ localNormSubgroup K E at hy
    rcases hy with ⟨u, hu⟩
    refine ⟨baseUnitsEquivGaloisAmbientFixed K Ω
      (Additive.ofMul (normUnits K E u)), ?_, ?_⟩
    · refine ⟨abstractFixedFieldUnitsEquivGaloisFixed
          K Ω L.field (Additive.ofMul u), ?_⟩
      apply (baseUnitsEquivGaloisAmbientFixed K Ω).symm.injective
      change (baseUnitsEquivGaloisAmbientFixed K Ω).symm
          (relativeNorm (galoisAmbientUnitsRep K Ω)
            (closedFixingSubgroup (⊥ : IntermediateField K Ω))
            L.field L.below (abstractFixedFieldUnitsEquivGaloisFixed
              K Ω L.field (Additive.ofMul u))) =
        (baseUnitsEquivGaloisAmbientFixed K Ω).symm
          (baseUnitsEquivGaloisAmbientFixed K Ω
          (Additive.ofMul (normUnits K E u)))
      rw [baseUnitsEquivGaloisAmbientFixed_symm_relativeNorm_abstractFixedFieldUnit_eq_normUnits,
        (baseUnitsEquivGaloisAmbientFixed K Ω).symm_apply_apply]
    · change (baseUnitsEquivGaloisAmbientFixed K Ω).symm
        (baseUnitsEquivGaloisAmbientFixed K Ω
          (Additive.ofMul (normUnits K E u))) = y
      rw [(baseUnitsEquivGaloisAmbientFixed K Ω).symm_apply_apply]
      exact congrArg Additive.ofMul hu

/-- An abstract fixed-coefficient norm containment transports back to
the corresponding containment of ordinary norm subgroups in `Kˣ`
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean:296`]
[Yamaguchi2026]). -/
theorem finiteAbelianNormSubgroup_le_of_abstractNormSubgroup_le_map
    (L : FiniteAbelianSubextension (closedFixingSubgroup (⊥ : IntermediateField K Ω)))
    (H : Subgroup Kˣ)
    (h :
      L.normSubgroup (galoisAmbientUnitsRep K Ω) ≤
        H.toAddSubgroup.map
          (baseUnitsEquivGaloisAmbientFixed K Ω).toAddMonoidHom) :
    finiteAbelianNormSubgroup K Ω L ≤ H := by
  let e := baseUnitsEquivGaloisAmbientFixed K Ω
  intro x hx
  have hxAdd :
      Additive.ofMul x ∈
        additiveNormSubgroup K
          (abstractFixedField K Ω L.field) := by
    exact hx
  rw [← map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup K Ω L] at hxAdd
  rcases hxAdd with ⟨y, hy, hyx⟩
  rcases h hy with ⟨z, hz, hzy⟩
  have hzEq : z = Additive.ofMul x := by
    calc
      z = e.symm (e z) := (e.symm_apply_apply z).symm
      _ = e.symm y := congrArg e.symm hzy
      _ = Additive.ofMul x := hyx
  change Additive.ofMul x ∈ H.toAddSubgroup
  simpa [hzEq] using hz

section LocalField

variable [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

omit [IsSepClosed Ω] in
/-- The ordinary norm subgroup of a represented finite abelian
extension has finite index: its quotient is the finite abelianized
Galois group under the layer's finite local reciprocity,
`abelianizationEquivNormQuotient` ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean:345`]
[Yamaguchi2026]). -/
theorem finiteAbelianNormSubgroup_finiteIndex
    (L : FiniteAbelianSubextension (closedFixingSubgroup (⊥ : IntermediateField K Ω))) :
    (finiteAbelianNormSubgroup K Ω L).FiniteIndex := by
  let E := abstractFixedField K Ω L.field
  letI : Finite ((baseField (Ω ≃ₐ[K] Ω)).toSubgroup ⧸
      L.field.toSubgroup.subgroupOf (baseField (Ω ≃ₐ[K] Ω)).toSubgroup) :=
    finiteAbelianSubextension_finite_over_absoluteBase K Ω L
  letI : FiniteDimensional K E :=
    abstractFixedField_finiteDimensional
      K Ω L.field inferInstance
  letI : IsGalois K E :=
    abstractFixedField_isGalois_of_base_normal K Ω L.field
      (finiteAbelianSubextension_normal_over_absoluteBase K Ω L)
  letI : Finite (E ≃ₐ[K] E) := by
    apply Nat.finite_of_card_ne_zero
    rw [IsGalois.card_aut_eq_finrank K E]
    exact Nat.ne_of_gt Module.finrank_pos
  letI : Finite (Abelianization (E ≃ₐ[K] E)) :=
    Finite.of_surjective Abelianization.of QuotientGroup.mk_surjective
  letI : Finite (NormQuotient K E) :=
    Finite.of_equiv (Abelianization (E ≃ₐ[K] E))
      (abelianizationEquivNormQuotient K E).toEquiv
  letI : Finite (Kˣ ⧸ localNormSubgroup K E) := by
    change Finite (NormQuotient K E)
    infer_instance
  change (localNormSubgroup K E).FiniteIndex
  exact Subgroup.finiteIndex_of_finite_quotient

omit [IsSepClosed Ω] in
/-- The ordinary norm subgroup of a represented finite abelian
extension is open — by the layer's openness of every finite-index
subgroup of `Kˣ`, where the source argues through its topological
reciprocity ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean:328`]
[Yamaguchi2026]). -/
theorem finiteAbelianNormSubgroup_isOpen
    (L : FiniteAbelianSubextension (closedFixingSubgroup (⊥ : IntermediateField K Ω))) :
    IsOpen (finiteAbelianNormSubgroup K Ω L : Set Kˣ) :=
  unitsFiniteIndexOpen K (finiteAbelianNormSubgroup K Ω L)
    (finiteAbelianNormSubgroup_finiteIndex K Ω L)

omit [IsSepClosed Ω] in
/-- **The norm subgroup map**, sending a finite abelian extension to
its ordinary norm subgroup, with native openness and finite index
recorded ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean:376`]
[Yamaguchi2026]). -/
def finiteAbelianNormSubgroupMap :
    FiniteAbelianSubextension (closedFixingSubgroup (⊥ : IntermediateField K Ω)) →
      OpenFiniteIndexSubgroup K :=
  fun L ↦ ⟨finiteAbelianNormSubgroup K Ω L,
    finiteAbelianNormSubgroup_isOpen K Ω L,
    finiteAbelianNormSubgroup_finiteIndex K Ω L⟩

/-- The norm subgroup map is injective, given the reciprocity inputs
over the ambient ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean:384`]
[Yamaguchi2026]). -/
theorem finiteAbelianNormSubgroupMap_injective
    (D : DegreeData (Ω ≃ₐ[K] Ω)) (v : ValuationData D (galoisAmbientUnitsRep K Ω))
    (hcf : SatisfiesClassFieldAxiom (galoisAmbientUnitsRep K Ω))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D) :
    Function.Injective (finiteAbelianNormSubgroupMap K Ω) := by
  intro L₁ L₂ hL
  apply FiniteAbelianSubextension.normSubgroupMap_injective
    v hcf hAxiom (galoisAmbientFiniteAbstractBase K Ω)
  apply Subtype.ext
  apply (AddSubgroup.map_injective
    (f := (baseUnitsEquivGaloisAmbientFixed K Ω).symm.toAddMonoidHom)
    (baseUnitsEquivGaloisAmbientFixed K Ω).symm.injective)
  change (L₁.normSubgroup (galoisAmbientUnitsRep K Ω)).map
      (baseUnitsEquivGaloisAmbientFixed K Ω).symm.toAddMonoidHom =
    (L₂.normSubgroup (galoisAmbientUnitsRep K Ω)).map
      (baseUnitsEquivGaloisAmbientFixed K Ω).symm.toAddMonoidHom
  rw [map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup,
    map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup]
  have hsub : finiteAbelianNormSubgroup K Ω L₁ =
      finiteAbelianNormSubgroup K Ω L₂ :=
    congrArg OpenFiniteIndexSubgroup.subgroup hL
  exact congrArg Subgroup.toAddSubgroup hsub

omit [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K] in
/-- **The order reversal for finite abelian subextensions**, expressed
for the actual fixed fields and their ordinary norm subgroups, given
the reciprocity inputs over the ambient ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean:408`]
[Yamaguchi2026]). -/
theorem finiteAbelianSubextension_le_iff_normSubgroup_le
    (D : DegreeData (Ω ≃ₐ[K] Ω)) (v : ValuationData D (galoisAmbientUnitsRep K Ω))
    (hcf : SatisfiesClassFieldAxiom (galoisAmbientUnitsRep K Ω))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (L₁ L₂ : FiniteAbelianSubextension (closedFixingSubgroup (⊥ : IntermediateField K Ω))) :
    L₁ ≤ L₂ ↔
      finiteAbelianNormSubgroup K Ω L₂ ≤
        finiteAbelianNormSubgroup K Ω L₁ := by
  refine (FiniteAbelianSubextension.le_iff_normSubgroup_le
    v hcf hAxiom (galoisAmbientFiniteAbstractBase K Ω) L₁ L₂).trans ?_
  rw [← AddSubgroup.map_le_map_iff_of_injective
    (f := (baseUnitsEquivGaloisAmbientFixed K Ω).symm.toAddMonoidHom)
    (baseUnitsEquivGaloisAmbientFixed K Ω).symm.injective]
  rw [map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup,
    map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup]
  rfl

/-- **The ordinary norm-subgroup assignment is an order embedding into
the opposite poset of native open finite-index subgroups**, given the
reciprocity inputs over the ambient ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean:426`]
[Yamaguchi2026]). -/
def finiteAbelianNormSubgroupOrderEmbedding
    (D : DegreeData (Ω ≃ₐ[K] Ω)) (v : ValuationData D (galoisAmbientUnitsRep K Ω))
    (hcf : SatisfiesClassFieldAxiom (galoisAmbientUnitsRep K Ω))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D) :
    FiniteAbelianSubextension (closedFixingSubgroup (⊥ : IntermediateField K Ω)) ↪o
      (OpenFiniteIndexSubgroup K)ᵒᵈ where
  toFun := finiteAbelianNormSubgroupMap K Ω
  inj' := finiteAbelianNormSubgroupMap_injective K Ω D v hcf hAxiom
  map_rel_iff' := by
    intro L₁ L₂
    change finiteAbelianNormSubgroup K Ω L₂ ≤
        finiteAbelianNormSubgroup K Ω L₁ ↔ L₁ ≤ L₂
    exact (finiteAbelianSubextension_le_iff_normSubgroup_le K Ω D v hcf hAxiom L₁ L₂).symm

end LocalField

section AlgebraicClosure

variable [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

/-- The norm subgroup map is injective at the algebraic closure, with
the layer's local data supplied ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean:384`]
[Yamaguchi2026]). -/
theorem localFiniteAbelianNormSubgroupMap_injective :
    Function.Injective (finiteAbelianNormSubgroupMap K (AlgebraicClosure K)) := by
  exact finiteAbelianNormSubgroupMap_injective K (AlgebraicClosure K)
    (localResidueDatum K) (localHenselianValuation K)
    (algebraicClosureUnits_satisfiesClassFieldAxiom K)
    (localHenselianValuation_satisfiesUnramifiedUnitCohomology K)

/-- The order reversal at the algebraic closure, with the layer's local
data supplied ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean:408`]
[Yamaguchi2026]). -/
theorem localFiniteAbelianSubextension_le_iff_normSubgroup_le
    (L₁ L₂ : FiniteAbelianSubextension
      (closedFixingSubgroup (⊥ : IntermediateField K (AlgebraicClosure K)))) :
    L₁ ≤ L₂ ↔
      finiteAbelianNormSubgroup K (AlgebraicClosure K) L₂ ≤
        finiteAbelianNormSubgroup K (AlgebraicClosure K) L₁ := by
  exact finiteAbelianSubextension_le_iff_normSubgroup_le K (AlgebraicClosure K)
    (localResidueDatum K) (localHenselianValuation K)
    (algebraicClosureUnits_satisfiesClassFieldAxiom K)
    (localHenselianValuation_satisfiesUnramifiedUnitCohomology K) L₁ L₂

/-- **The order embedding at the algebraic closure**, with the layer's
local data supplied ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean:426`]
[Yamaguchi2026]). -/
def localFiniteAbelianNormSubgroupOrderEmbedding :
    FiniteAbelianSubextension
        (closedFixingSubgroup (⊥ : IntermediateField K (AlgebraicClosure K))) ↪o
      (OpenFiniteIndexSubgroup K)ᵒᵈ :=
  finiteAbelianNormSubgroupOrderEmbedding K (AlgebraicClosure K)
    (localResidueDatum K) (localHenselianValuation K)
    (algebraicClosureUnits_satisfiesClassFieldAxiom K)
    (localHenselianValuation_satisfiesUnramifiedUnitCohomology K)

end AlgebraicClosure

end

end Atlas.Knowledge
