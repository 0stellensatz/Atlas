import Mathlib
import Atlas.Knowledge.AbstractExtension
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.ChosenPrimeElement
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractExtension
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteAbstractFieldExtension
import Atlas.Knowledge.FiniteIntermediateFieldRefinement
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FiniteReciprocityCandidate
import Atlas.Knowledge.FiniteReciprocityHom
import Atlas.Knowledge.FiniteResidueAbstractExtension
import Atlas.Knowledge.FiniteResidueAbstractField
import Atlas.Knowledge.FiniteTower
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusExponent
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.FrobeniusFixedField
import Atlas.Knowledge.NormalizedDegree
import Atlas.Knowledge.PrimeElement
import Atlas.Knowledge.ProfiniteInteger
import Atlas.Knowledge.ReciprocityMap
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.RelativeNormConjugation
import Atlas.Knowledge.RelativeNormLaws
import Atlas.Knowledge.TopologicalGeneration
import Atlas.Knowledge.UnitCohomologyAxiom
import Atlas.Knowledge.ValuationData

/-!
# Finite reciprocity naturality norm

The two vertical maps of norm–conjugation naturality, built on the
actual finite Galois quotients and the actual finite norm quotients:
restriction and the Frobenius tower transport on the left, the norms
`N_{K'|K}` and conjugation on the right, the totally ramified
intermediate extension of a transported lift, and the first commuting
square — restriction corresponds to the norm under the finite
reciprocity homomorphism (#104).

## Main definitions

* `finiteReciprocityNaturalityRestriction` — the left vertical map.
* `DegreeData.finiteReciprocityNaturalityFrobeniusTowerMap` — the
  infinite-quotient restriction.
* `DegreeData.finiteReciprocityNaturalityFrobeniusTowerMapContinuous` —
  its continuous form.
* `DegreeData.finiteReciprocityNaturalityFrobeniusTowerLift` — the
  transported Frobenius lift.
* `finiteReciprocityNaturalityNormMap` — the right vertical map.
* `conjugateFixedElementHom` — the conjugation map on fixed elements.
* `finiteReciprocityNaturalityConjugationNormMap` — the conjugation
  diagram's right vertical map.

## Main statements

* `DegreeData.finiteReciprocityNaturalityFrobeniusTowerMap_degree` —
  the normalized-degree square; proved.
* `DegreeData.finiteReciprocityNaturalityFrobeniusTowerLift_exponent` —
  the exponent multiplies by the residue degree; proved.
* `DegreeData.finiteReciprocityNaturalityRestriction_frobeniusTowerLift`
  — the transported lift restricts along the left map; proved.
* `DegreeData.finiteReciprocityNaturalityFrobeniusFixedField_isTotallyRamified`
  — `Σ' | Σ` is totally ramified; proved.
* `DegreeData.finiteReciprocityNaturalityFrobeniusFixedField_le` — the
  transported lift's fixed field lies inside the original's; proved.
* `finiteReciprocityNaturality_norm_tower_class` — the first diagram's
  norm identity; proved.
* `DegreeData.finiteReciprocityNaturality_restriction_norm_commutes` —
  the first diagram commutes; proved.
* `finiteReciprocityNaturality_conjugation_norm_class` — the
  conjugation diagram's norm identity; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling.
Both sections sit at the source's `Type u`, the representation section
since the #104 hoist unpinned the quotient-action chain it follows. The
profinite integers are the layer's `ProfiniteInteger` with
`ProfiniteInteger.ofAdd_one_pow_injective` for the source's injectivity
device, the bundles are the layer's top-level
`FiniteResidueAbstractExtension`, `FiniteTower`, and
`AbstractExtension`, and the containment-consuming call sites adapt to
the layer's containment-free forms: all six `finite_conjugateExtension`
occurrences and all three `finite_extension_of_le` sites drop their
redundant containments. The restriction map and its computation rule
shed the source's two containments the `extensionSubgroup` spelling
consumed, so their argument lists are two shorter, and the dead-binder
sweep sheds the tower-map chain's `[IsTopologicalGroup G]`, the
commuting square's `[T2Space G]`, and the totally-ramified theorem's
`[T2Space G]`, all simply unused. Two source tactics survive with
accepted lint findings, both disclosed here: the fixed-field
containment proof keeps the source's flexible simp on
`DegreeData.frobeniusClosure`, which a restricted replacement cannot
close, and the totally-ramified theorem keeps its base finiteness
instance, which the `unusedArguments` linter flags although deleting it
breaks the proof's instance synthesis — the binder is stated over the
bundle and the synthesis wants its field, definitionally equal but not
syntactically. The citations name this file by bare basename; it lives
at `AbstractClassFieldTheory/Reciprocity/Construction/` in the source.
The source's `open`s go — the layer keeps everything in one namespace.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **The left vertical map of the first naturality diagram**:
restriction from `G(L'|K')` to `G(L|K)`
([Yamaguchi 2026, `MainNaturality.lean:34`][Yamaguchi2026]). -/
def finiteReciprocityNaturalityRestriction
    (K K' L L' : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L'.toSubgroup.subgroupOf K'.toSubgroup).Normal] :
    (K'.toSubgroup ⧸ L'.toSubgroup.subgroupOf K'.toSubgroup) →*
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) := by
  apply QuotientGroup.map
    (L'.toSubgroup.subgroupOf K'.toSubgroup)
    (L.toSubgroup.subgroupOf K.toSubgroup)
    (Subgroup.inclusion hK'K)
  intro k' hk'L'
  change k'.1 ∈ L'.toSubgroup at hk'L'
  change (Subgroup.inclusion hK'K k').1 ∈ L.toSubgroup
  exact hL'L hk'L'

/-- Restriction sends a represented class to the included
representative's class
([Yamaguchi 2026, `MainNaturality.lean:56`][Yamaguchi2026]). -/
@[simp]
theorem finiteReciprocityNaturalityRestriction_mk
    (K K' L L' : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L'.toSubgroup.subgroupOf K'.toSubgroup).Normal]
    (k' : K'.toSubgroup) :
    finiteReciprocityNaturalityRestriction K K' L L' hK'K hL'L
        (QuotientGroup.mk k') =
      QuotientGroup.mk (Subgroup.inclusion hK'K k') :=
  rfl

namespace DegreeData

/-- **Restriction on the infinite Frobenius quotients** underlying the
first naturality diagram
([Yamaguchi 2026, `MainNaturality.lean:74`][Yamaguchi2026]). -/
def finiteReciprocityNaturalityFrobeniusTowerMap
    (D : DegreeData G)
    (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L'.toSubgroup.subgroupOf K'.toSubgroup).Normal] :
    (K'.toSubgroup ⧸ D.extensionInertiaWithin K' L' hL'K') →*
      (K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) := by
  apply QuotientGroup.map
    (D.extensionInertiaWithin K' L' hL'K')
    (D.extensionInertiaWithin K L hLK)
    (Subgroup.inclusion hK'K)
  rintro k' ⟨hk'L', hk'I⟩
  constructor
  · change k'.1 ∈ L'.toSubgroup at hk'L'
    change (Subgroup.inclusion hK'K k').1 ∈ L.toSubgroup
    exact hL'L hk'L'
  · exact hk'I

/-- The tower map evaluates on a representative by inclusion
([Yamaguchi 2026, `MainNaturality.lean:98`][Yamaguchi2026]). -/
@[simp]
theorem finiteReciprocityNaturalityFrobeniusTowerMap_mk
    (D : DegreeData G)
    (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L'.toSubgroup.subgroupOf K'.toSubgroup).Normal]
    (k' : K'.toSubgroup) :
    D.finiteReciprocityNaturalityFrobeniusTowerMap K K' L L'
        hLK hL'K' hK'K hL'L (QuotientGroup.mk k') =
      QuotientGroup.mk (Subgroup.inclusion hK'K k') := rfl

/-- **The continuous form of the tower map**, transporting the closed
cyclic subgroup generated by a Frobenius lift
([Yamaguchi 2026, `MainNaturality.lean:114`][Yamaguchi2026]). -/
def finiteReciprocityNaturalityFrobeniusTowerMapContinuous
    (D : DegreeData G) [IsTopologicalGroup G]
    (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L'.toSubgroup.subgroupOf K'.toSubgroup).Normal] :
    (K'.toSubgroup ⧸ D.extensionInertiaWithin K' L' hL'K') →ₜ*
      (K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) where
  toMonoidHom := D.finiteReciprocityNaturalityFrobeniusTowerMap
    K K' L L' hLK hL'K' hK'K hL'L
  continuous_toFun := by
    rw [← QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    change Continuous (fun k' : K'.toSubgroup =>
      QuotientGroup.mk (Subgroup.inclusion hK'K k'))
    apply QuotientGroup.continuous_mk.comp
    exact continuous_subtype_val.subtype_mk _

/-- **The normalized-degree square on the two infinite Frobenius
quotients**: the tower map multiplies the normalized degree by the
residue degree
([Yamaguchi 2026, `MainNaturality.lean:136`][Yamaguchi2026]). -/
theorem finiteReciprocityNaturalityFrobeniusTowerMap_degree
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D)
    (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ E.base.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ E.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L'.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (q : E.field.toSubgroup ⧸
      D.extensionInertiaWithin E.field.field L' hL'K') :
    (D.extensionNormalizedDegree E.base L hLK
      (D.finiteReciprocityNaturalityFrobeniusTowerMap
        E.base.field E.field.field L L'
        hLK hL'K' E.below hL'L q)).toAdd =
      (E.residueDegree : ℕ) •
        (D.extensionNormalizedDegree E.field L' hL'K' q).toAdd := by
  refine Quotient.inductionOn' q ?_
  intro k'
  simpa using D.frobeniusRestrictionNaturality_normalizedDegree E k'

/-- **A positive Frobenius lift over `K'` remains one over `K`**, its
exponent multiplied by `f_{K'|K}`
([Yamaguchi 2026, `MainNaturality.lean:159`][Yamaguchi2026]). -/
def finiteReciprocityNaturalityFrobeniusTowerLift
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D)
    (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ E.base.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ E.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L'.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements E.field L' hL'K') :
    D.FrobeniusElements E.base L hLK := by
  let f := (E.residueDegree : ℕ)
  let n := D.frobeniusExponent E.field L' hL'K' σ
  refine ⟨D.finiteReciprocityNaturalityFrobeniusTowerMap
      E.base.field E.field.field L L' hLK hL'K' E.below hL'L σ.1,
    f * n, Nat.mul_pos E.residueDegree.property
      (D.frobeniusExponent_pos E.field L' hL'K' σ), ?_⟩
  apply Multiplicative.ext
  rw [D.finiteReciprocityNaturalityFrobeniusTowerMap_degree E L L'
    hLK hL'K' hL'L σ.1]
  rw [D.extensionNormalizedDegree_frobenius_eq_pow E.field L' hL'K' σ]
  change f • (n • (1 : ProfiniteInteger)) = (f * n) • (1 : ProfiniteInteger)
  rw [smul_smul]

/-- The tower lift coerces to the tower map's value
([Yamaguchi 2026, `MainNaturality.lean:185`][Yamaguchi2026]). -/
@[simp]
theorem finiteReciprocityNaturalityFrobeniusTowerLift_coe
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D)
    (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ E.base.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ E.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L'.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements E.field L' hL'K') :
    (D.finiteReciprocityNaturalityFrobeniusTowerLift
      E L L' hLK hL'K' hL'L σ).1 =
      D.finiteReciprocityNaturalityFrobeniusTowerMap
        E.base.field E.field.field L L' hLK hL'K' E.below hL'L σ.1 := by
  simp [finiteReciprocityNaturalityFrobeniusTowerLift]

/-- **The tower lift's exponent is the residue degree times the
original exponent**
([Yamaguchi 2026, `MainNaturality.lean:203`][Yamaguchi2026]). -/
@[simp]
theorem finiteReciprocityNaturalityFrobeniusTowerLift_exponent
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D)
    (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ E.base.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ E.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L'.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements E.field L' hL'K') :
    D.frobeniusExponent E.base L hLK
        (D.finiteReciprocityNaturalityFrobeniusTowerLift
          E L L' hLK hL'K' hL'L σ) =
      (E.residueDegree : ℕ) *
        D.frobeniusExponent E.field L' hL'K' σ := by
  apply ProfiniteInteger.ofAdd_one_pow_injective
  let f := (E.residueDegree : ℕ)
  let n := D.frobeniusExponent E.field L' hL'K' σ
  calc
    (Multiplicative.ofAdd (1 : ProfiniteInteger)) ^
        D.frobeniusExponent E.base L hLK
          (D.finiteReciprocityNaturalityFrobeniusTowerLift
            E L L' hLK hL'K' hL'L σ) =
      D.extensionNormalizedDegree E.base L hLK
        (D.finiteReciprocityNaturalityFrobeniusTowerLift
          E L L' hLK hL'K' hL'L σ).1 :=
      (D.extensionNormalizedDegree_frobenius_eq_pow E.base L hLK _).symm
    _ = (Multiplicative.ofAdd (1 : ProfiniteInteger)) ^ (f * n) := by
      apply Multiplicative.ext
      rw [D.finiteReciprocityNaturalityFrobeniusTowerLift_coe]
      rw [D.finiteReciprocityNaturalityFrobeniusTowerMap_degree E L L'
        hLK hL'K' hL'L σ.1]
      rw [D.extensionNormalizedDegree_frobenius_eq_pow
        E.field L' hL'K' σ]
      change f • (n • (1 : ProfiniteInteger)) = (f * n) • (1 : ProfiniteInteger)
      rw [smul_smul]
    _ = (Multiplicative.ofAdd (1 : ProfiniteInteger)) ^
        ((E.residueDegree : ℕ) *
          D.frobeniusExponent E.field L' hL'K' σ) := by rfl

/-- **Restriction of the transported lift is the restriction of the
original lift along the left vertical map**
([Yamaguchi 2026, `MainNaturality.lean:245`][Yamaguchi2026]). -/
theorem finiteReciprocityNaturalityRestriction_frobeniusTowerLift
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D)
    (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ E.base.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ E.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L'.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements E.field L' hL'K') :
    finiteReciprocityNaturalityRestriction
        E.base.field E.field.field L L' E.below hL'L
        (D.frobeniusRestriction E.field L' hL'K' σ) =
      D.frobeniusRestriction E.base L hLK
        (D.finiteReciprocityNaturalityFrobeniusTowerLift
          E L L' hLK hL'K' hL'L σ) := by
  change finiteReciprocityNaturalityRestriction
      E.base.field E.field.field L L' E.below hL'L
      (D.extensionRestriction E.field.field L' hL'K' σ.1) =
    D.extensionRestriction E.base.field L hLK
      (D.finiteReciprocityNaturalityFrobeniusTowerLift
        E L L' hLK hL'K' hL'L σ).1
  rw [D.finiteReciprocityNaturalityFrobeniusTowerLift_coe]
  refine Quotient.inductionOn' σ.1 ?_
  intro k'
  rfl

/-- **The fixed field of a transported Frobenius lift lies inside the
original lift's fixed field** — `Σ' | Σ` is an intermediate extension
([Yamaguchi 2026, `MainNaturality.lean:274`][Yamaguchi2026]). -/
theorem finiteReciprocityNaturalityFrobeniusFixedField_le
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D)
    (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ E.base.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ E.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L'.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements E.field L' hL'K') :
    (D.frobeniusFixedField E.field L' hL'K' σ).toSubgroup ≤
      (D.frobeniusFixedField E.base L hLK
        (D.finiteReciprocityNaturalityFrobeniusTowerLift
          E L L' hLK hL'K' hL'L σ)).toSubgroup := by
  rintro g ⟨k', hk', rfl⟩
  let k : E.base.field.toSubgroup := Subgroup.inclusion E.below k'
  refine ⟨k, ?_, rfl⟩
  change QuotientGroup.mk k ∈
    (D.frobeniusClosure E.base L hLK
      (D.finiteReciprocityNaturalityFrobeniusTowerLift
        E L L' hLK hL'K' hL'L σ)).toSubgroup
  change QuotientGroup.mk k' ∈
    (D.frobeniusClosure E.field L' hL'K' σ).toSubgroup at hk'
  have hmap := map_mem_closedSubgroupGenerated_singleton
    (D.finiteReciprocityNaturalityFrobeniusTowerMapContinuous
      E.base.field E.field.field L L' hLK hL'K' E.below hL'L) σ.1 (by
        simpa [DegreeData.frobeniusClosure] using hk')
  let f := D.finiteReciprocityNaturalityFrobeniusTowerMap
    E.base.field E.field.field L L' hLK hL'K' E.below hL'L
  change f (QuotientGroup.mk k') ∈
    (closedSubgroupGenerated ({f σ.1} : Set _) : Subgroup _) at hmap
  simp [DegreeData.frobeniusClosure]
  change f (QuotientGroup.mk k') ∈
    (closedSubgroupGenerated ({f σ.1} : Set _) : Subgroup _)
  exact hmap

/-- **The intermediate extension `Σ' | Σ` attached to a transported
Frobenius lift is totally ramified**
([Yamaguchi 2026, `MainNaturality.lean:312`][Yamaguchi2026]). -/
theorem finiteReciprocityNaturalityFrobeniusFixedField_isTotallyRamified
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G]
    (E : FiniteResidueAbstractExtension D)
    (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ E.base.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ E.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L'.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    [Finite
      (E.base.toSubgroup ⧸ L.toSubgroup.subgroupOf E.base.field.toSubgroup)]
    [hL'K'finite : Finite
      (E.field.toSubgroup ⧸ L'.toSubgroup.subgroupOf E.field.field.toSubgroup)]
    (σ : D.FrobeniusElements E.field L' hL'K') :
    (AbstractExtension.mk
      (D.frobeniusFixedField E.field L' hL'K' σ)
      (D.frobeniusFixedField E.base L hLK
        (D.finiteReciprocityNaturalityFrobeniusTowerLift
          E L L' hLK hL'K' hL'L σ))
      (D.finiteReciprocityNaturalityFrobeniusFixedField_le
        E L L' hLK hL'K' hL'L σ)).IsTotallyRamified D := by
  let τ := D.finiteReciprocityNaturalityFrobeniusTowerLift
    E L L' hLK hL'K' hL'L σ
  let S' := D.frobeniusFixedField E.field L' hL'K' σ
  let S := D.frobeniusFixedField E.base L hLK τ
  let hS'S := D.finiteReciprocityNaturalityFrobeniusFixedField_le
    E L L' hLK hL'K' hL'L σ
  let FS := D.frobeniusFixedResidueField E.base L hLK τ
  let FS' := D.frobeniusFixedResidueField E.field L' hL'K' σ
  have hresidue : (FS.residueDegree : ℕ) = (FS'.residueDegree : ℕ) := by
    calc
      (FS.residueDegree : ℕ) =
          D.frobeniusExponent E.base L hLK τ *
            (E.base.residueDegree : ℕ) :=
        D.frobeniusFixedResidueField_residueDegree E.base L hLK τ
      _ = ((E.residueDegree : ℕ) *
            D.frobeniusExponent E.field L' hL'K' σ) *
          (E.base.residueDegree : ℕ) := by
        rw [D.finiteReciprocityNaturalityFrobeniusTowerLift_exponent]
      _ = D.frobeniusExponent E.field L' hL'K' σ *
          ((E.residueDegree : ℕ) * (E.base.residueDegree : ℕ)) := by
        ac_rfl
      _ = D.frobeniusExponent E.field L' hL'K' σ *
          (E.field.residueDegree : ℕ) := by
        rw [E.residueDegree_mul_absoluteResidueDegree D]
      _ = (FS'.residueDegree : ℕ) :=
        (D.frobeniusFixedResidueField_residueDegree E.field L' hL'K' σ).symm
  let hS'K' := D.frobeniusFixedField_le E.field L' hL'K' σ
  let hSK := D.frobeniusFixedField_le E.base L hLK τ
  letI : Finite (E.field.toSubgroup ⧸
      S'.toSubgroup.subgroupOf E.field.field.toSubgroup) :=
    D.frobeniusFixedField_finite E.field L' hL'K' σ
  letI : Finite (E.base.toSubgroup ⧸
      S.toSubgroup.subgroupOf E.base.field.toSubgroup) :=
    D.frobeniusFixedField_finite E.base L hLK τ
  letI : Finite (E.base.toSubgroup ⧸
      S'.toSubgroup.subgroupOf E.base.field.toSubgroup) :=
    relativeTowerQuotientFinite E.base.field E.field.field S' hS'K' E.below
  letI hS'Sfinite : Finite
      (S.toSubgroup ⧸ S'.toSubgroup.subgroupOf S.toSubgroup) :=
    FiniteIntermediateField.finite_extension_of_le hSK hS'S
  let ES'S : FiniteResidueAbstractExtension D :=
    { field := FS'
      base := FS
      below := hS'S
      finiteQuotient := hS'Sfinite }
  have hrelative : (ES'S.residueDegree : ℕ) = 1 := by
    change (ES'S.base.residueDegree : ℕ) =
      (ES'S.field.residueDegree : ℕ) at hresidue
    have hmul := ES'S.residueDegree_mul_absoluteResidueDegree D
    rw [← hresidue] at hmul
    have hpos : 0 < (ES'S.base.residueDegree : ℕ) :=
      ES'S.base.residueDegree.property
    nlinarith
  exact ES'S.toFiniteAbstractExtension.isTotallyRamified_of_residueDegree_eq_one
    D hrelative

end DegreeData

/- Finiteness of the composite extension in the first diagram
([Yamaguchi 2026, `MainNaturality.lean:394`][Yamaguchi2026]). -/
private theorem finiteReciprocityNaturality_tower_finite
    (K K' L' : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    [Finite (K.toSubgroup ⧸ K'.toSubgroup.subgroupOf K.toSubgroup)]
    [Finite (K'.toSubgroup ⧸ L'.toSubgroup.subgroupOf K'.toSubgroup)] :
    Finite (K.toSubgroup ⧸
      L'.toSubgroup.subgroupOf K.toSubgroup) :=
  relativeTowerQuotientFinite K K' L' hL'K' hK'K

end GroupOnly

section Representation

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **The right vertical map of the first naturality diagram**: the
norm `N_{K'|K}` descended to the finite norm quotients
([Yamaguchi 2026, `MainNaturality.lean:413`][Yamaguchi2026]). -/
def finiteReciprocityNaturalityNormMap
    (A : Rep ℤ G) (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLKfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    [hL'K'finite : Finite
      (K'.toSubgroup ⧸ L'.toSubgroup.subgroupOf K'.toSubgroup)]
    [hK'Kfinite : Finite
      (K.toSubgroup ⧸ K'.toSubgroup.subgroupOf K.toSubgroup)] :
    FiniteNormQuotient A K' L' hL'K' →+
      FiniteNormQuotient A K L hLK := by
  letI hL'Kfinite : Finite (K.toSubgroup ⧸
      L'.toSubgroup.subgroupOf K.toSubgroup) :=
    finiteReciprocityNaturality_tower_finite K K' L' hK'K hL'K'
  letI hL'Lfinite : Finite
      (L.toSubgroup ⧸ L'.toSubgroup.subgroupOf L.toSubgroup) :=
    FiniteIntermediateField.finite_extension_of_le hLK hL'L
  let f : ambientFixedAddSubgroup A K' →+ FiniteNormQuotient A K L hLK :=
    (finiteNormClassHom A K L hLK).comp (relativeNorm A K K' hK'K)
  apply finiteNormQuotientLift A K' L' hL'K' f
  rintro _ ⟨a, rfl⟩
  let TLL' : FiniteTower G :=
    { top := L'
      middle := L
      base := K
      top_le_middle := hL'L
      middle_le_base := hLK
      finiteTopQuotient := hL'Lfinite
      finiteBaseQuotient := hLKfinite }
  let TKK' : FiniteTower G :=
    { top := L'
      middle := K'
      base := K
      top_le_middle := hL'K'
      middle_le_base := hK'K
      finiteTopQuotient := hL'K'finite
      finiteBaseQuotient := hK'Kfinite }
  apply (finiteNormClass_eq_zero_iff A K L hLK _).2
  refine ⟨relativeNorm A L L' hL'L a, ?_⟩
  calc
    relativeNorm A K L hLK (relativeNorm A L L' hL'L a) =
        relativeNorm A K L' (hL'L.trans hLK) a :=
      TLL'.norm_trans_apply A a
    _ = relativeNorm A K L' (hL'K'.trans hK'K) a := by
      congr 2
    _ = relativeNorm A K K' hK'K (relativeNorm A K' L' hL'K' a) :=
      (TKK'.norm_trans_apply A a).symm

/-- The norm map carries a finite norm class to the norm's class over
the base
([Yamaguchi 2026, `MainNaturality.lean:467`][Yamaguchi2026]). -/
@[simp]
theorem finiteReciprocityNaturalityNormMap_finiteNormClass
    (A : Rep ℤ G) (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLKfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    [Finite
      (K'.toSubgroup ⧸ L'.toSubgroup.subgroupOf K'.toSubgroup)]
    [hK'Kfinite : Finite
      (K.toSubgroup ⧸ K'.toSubgroup.subgroupOf K.toSubgroup)]
    (a : ambientFixedAddSubgroup A K') :
    finiteReciprocityNaturalityNormMap A K K' L L' hLK hL'K' hK'K hL'L
        (finiteNormClass A K' L' hL'K' a) =
      finiteNormClass A K L hLK (relativeNorm A K K' hK'K a) :=
  by
    simp [finiteReciprocityNaturalityNormMap]
    rfl

/-- **The additive map `a ↦ a^s` between the two fixed subgroups**
([Yamaguchi 2026, `MainNaturality.lean:488`][Yamaguchi2026]). -/
def conjugateFixedElementHom [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (s : G) :
    ambientFixedAddSubgroup A K →+
      ambientFixedAddSubgroup A (conjugateClosedSubgroup K s) where
  toFun := conjugateFixedElement A K s
  map_zero' := by
    apply Subtype.ext
    exact map_zero (A.ρ s⁻¹)
  map_add' a b := by
    apply Subtype.ext
    exact map_add (A.ρ s⁻¹) a.1 b.1

/-- The homomorphism evaluates by the underlying conjugation map
([Yamaguchi 2026, `MainNaturality.lean:502`][Yamaguchi2026]). -/
@[simp]
theorem conjugateFixedElementHom_apply [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (s : G)
    (a : ambientFixedAddSubgroup A K) :
    conjugateFixedElementHom A K s a = conjugateFixedElement A K s a :=
  rfl

/-- **The right vertical map of the conjugation diagram**, descended to
the finite norm quotients
([Yamaguchi 2026, `MainNaturality.lean:510`][Yamaguchi2026]). -/
def finiteReciprocityNaturalityConjugationNormMap
    [ContinuousMul G] (A : Rep ℤ G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    letI : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
        (conjugateClosedSubgroup L s).toSubgroup.subgroupOf
          (conjugateClosedSubgroup K s).toSubgroup) :=
      finite_conjugateExtension K L s
    FiniteNormQuotient A K L hLK →+
      FiniteNormQuotient A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s) := by
  letI hConjFinite : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
      (conjugateClosedSubgroup L s).toSubgroup.subgroupOf
        (conjugateClosedSubgroup K s).toSubgroup) :=
    finite_conjugateExtension K L s
  let f : ambientFixedAddSubgroup A K →+
      FiniteNormQuotient A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s) :=
    (finiteNormClassHom A (conjugateClosedSubgroup K s)
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s)).comp
        (conjugateFixedElementHom A K s)
  apply finiteNormQuotientLift A K L hLK f
  rintro _ ⟨a, rfl⟩
  apply (finiteNormClass_eq_zero_iff A (conjugateClosedSubgroup K s)
    (conjugateClosedSubgroup L s) (conjugateClosedSubgroup_mono hLK s) _).2
  refine ⟨conjugateFixedElement A L s a, ?_⟩
  exact relativeNorm_conjugate_apply A K L hLK s a

/-- The conjugation norm map carries a class to its conjugate's
class
([Yamaguchi 2026, `MainNaturality.lean:547`][Yamaguchi2026]). -/
@[simp]
theorem finiteReciprocityNaturalityConjugationNormMap_finiteNormClass
    [ContinuousMul G] (A : Rep ℤ G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (a : ambientFixedAddSubgroup A K) :
    letI : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
        (conjugateClosedSubgroup L s).toSubgroup.subgroupOf
          (conjugateClosedSubgroup K s).toSubgroup) :=
      finite_conjugateExtension K L s
    finiteReciprocityNaturalityConjugationNormMap A K L hLK s
        (finiteNormClass A K L hLK a) =
      finiteNormClass A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s) (conjugateClosedSubgroup_mono hLK s)
        (conjugateFixedElement A K s a) := by
  letI hConjFinite : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
      (conjugateClosedSubgroup L s).toSubgroup.subgroupOf
        (conjugateClosedSubgroup K s).toSubgroup) :=
    finite_conjugateExtension K L s
  simp [finiteReciprocityNaturalityConjugationNormMap]
  rfl

/-- **The norm identity of the first diagram in the target quotient** —
taking `S = Σ` and `S' = Σ'` gives the calculation
([Yamaguchi 2026, `MainNaturality.lean:574`][Yamaguchi2026]). -/
theorem finiteReciprocityNaturality_norm_tower_class
    (A : Rep ℤ G)
    (K K' L L' S S' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    (hSK : S.toSubgroup ≤ K.toSubgroup)
    (hS'K' : S'.toSubgroup ≤ K'.toSubgroup)
    (hS'S : S'.toSubgroup ≤ S.toSubgroup)
    [hLKfinite : Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    [hL'K'finite : Finite (K'.toSubgroup ⧸ L'.toSubgroup.subgroupOf K'.toSubgroup)]
    [hK'Kfinite : Finite (K.toSubgroup ⧸ K'.toSubgroup.subgroupOf K.toSubgroup)]
    [hSKfinite : Finite (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup)]
    [hS'K'finite : Finite (K'.toSubgroup ⧸ S'.toSubgroup.subgroupOf K'.toSubgroup)]
    [hS'Sfinite : Finite (S.toSubgroup ⧸ S'.toSubgroup.subgroupOf S.toSubgroup)]
    (π : ambientFixedAddSubgroup A S') :
    finiteReciprocityNaturalityNormMap A K K' L L' hLK hL'K' hK'K hL'L
        (finiteNormClass A K' L' hL'K'
          (relativeNorm A K' S' hS'K' π)) =
      finiteNormClass A K L hLK
        (relativeNorm A K S hSK (relativeNorm A S S' hS'S π)) := by
  letI hS'Kfinite : Finite (K.toSubgroup ⧸
      S'.toSubgroup.subgroupOf K.toSubgroup) :=
    finiteReciprocityNaturality_tower_finite K K' S' hK'K hS'K'
  let TKK' : FiniteTower G :=
    { top := S'
      middle := K'
      base := K
      top_le_middle := hS'K'
      middle_le_base := hK'K
      finiteTopQuotient := hS'K'finite
      finiteBaseQuotient := hK'Kfinite }
  let TSS' : FiniteTower G :=
    { top := S'
      middle := S
      base := K
      top_le_middle := hS'S
      middle_le_base := hSK
      finiteTopQuotient := hS'Sfinite
      finiteBaseQuotient := hSKfinite }
  rw [finiteReciprocityNaturalityNormMap_finiteNormClass]
  apply congrArg (finiteNormClass A K L hLK)
  calc
    relativeNorm A K K' hK'K (relativeNorm A K' S' hS'K' π) =
        relativeNorm A K S' (hS'K'.trans hK'K) π :=
      TKK'.norm_trans_apply A π
    _ = relativeNorm A K S' (hS'S.trans hSK) π := by
      congr 2
    _ = relativeNorm A K S hSK (relativeNorm A S S' hS'S π) :=
      (TSS'.norm_trans_apply A π).symm

namespace DegreeData

/-- **The first naturality diagram commutes**: restriction on finite
Galois groups corresponds under the finite reciprocity homomorphism to
the norm `N_{K'|K}` on finite norm quotients
([Yamaguchi 2026, `MainNaturality.lean:631`][Yamaguchi2026]). -/
theorem finiteReciprocityNaturality_restriction_norm_commutes
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (E : FiniteAbstractFieldExtension G)
    (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ E.base.field.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ E.field.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L'.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    [hLKfinite : Finite
      (E.base.field.toSubgroup ⧸ L.toSubgroup.subgroupOf E.base.field.toSubgroup)]
    [hL'K'finite : Finite
      (E.field.field.toSubgroup ⧸
        L'.toSubgroup.subgroupOf E.field.field.toSubgroup)] :
    (finiteReciprocityNaturalityNormMap A E.base.field E.field.field L L'
      hLK hL'K' E.below hL'L).comp
        (D.finiteReciprocityHom A v hAxiom E.field L' hL'K') =
      (D.finiteReciprocityHom A v hAxiom E.base L hLK).comp
      (finiteReciprocityNaturalityRestriction
          E.base.field E.field.field L L' E.below hL'L).toAdditive := by
  let ER := E.toFiniteResidueAbstractExtension D
  letI hL'K'finiteER : Finite
      (ER.field.field.toSubgroup ⧸
        L'.toSubgroup.subgroupOf ER.field.field.toSubgroup) := by
    change Finite
      (ER.field.field.toSubgroup ⧸
        L'.toSubgroup.subgroupOf ER.field.field.toSubgroup) at hL'K'finite
    exact hL'K'finite
  letI hLKfiniteER : Finite
      (ER.base.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf ER.base.field.toSubgroup) := by
    change Finite
      (ER.base.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf ER.base.field.toSubgroup) at hLKfinite
    exact hLKfinite
  letI hLnormalERbase :
      (L.toSubgroup.subgroupOf ER.base.field.toSubgroup).Normal := by
    change (L.toSubgroup.subgroupOf ER.base.field.toSubgroup).Normal at hLnormal
    exact hLnormal
  letI hL'normalERfield :
      (L'.toSubgroup.subgroupOf ER.field.field.toSubgroup).Normal := by
    change (L'.toSubgroup.subgroupOf ER.field.field.toSubgroup).Normal at hL'normal
    exact hL'normal
  apply AddMonoidHom.ext
  intro q
  let σ := D.chosenFiniteReciprocityFrobeniusLift ER.field L' hL'K' q.toMul
  let τ := D.finiteReciprocityNaturalityFrobeniusTowerLift
    ER L L' hLK hL'K' hL'L σ
  have hσ : D.frobeniusRestriction ER.field L' hL'K' σ = q.toMul :=
    D.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift
      ER.field L' hL'K' q.toMul
  have hτ : D.frobeniusRestriction ER.base L hLK τ =
      ((finiteReciprocityNaturalityRestriction
        E.base.field E.field.field L L' E.below hL'L).toAdditive q).toMul := by
    rw [← D.finiteReciprocityNaturalityRestriction_frobeniusTowerLift
      ER L L' hLK hL'K' hL'L σ, hσ]
    rfl
  let S' := D.frobeniusFixedField ER.field L' hL'K' σ
  let S := D.frobeniusFixedField ER.base L hLK τ
  let hS'K' := D.frobeniusFixedField_le ER.field L' hL'K' σ
  let hSK := D.frobeniusFixedField_le ER.base L hLK τ
  let hS'S := D.finiteReciprocityNaturalityFrobeniusFixedField_le
    ER L L' hLK hL'K' hL'L σ
  letI hS'K'finite : Finite
      (E.field.field.toSubgroup ⧸
        S'.toSubgroup.subgroupOf E.field.field.toSubgroup) :=
    D.frobeniusFixedField_finite ER.field L' hL'K' σ
  letI hSKfinite : Finite
      (E.base.field.toSubgroup ⧸
        S.toSubgroup.subgroupOf E.base.field.toSubgroup) :=
    D.frobeniusFixedField_finite ER.base L hLK τ
  letI hS'Kfinite : Finite
      (E.base.field.toSubgroup ⧸
        S'.toSubgroup.subgroupOf E.base.field.toSubgroup) :=
    finiteReciprocityNaturality_tower_finite
      E.base.field E.field.field S' E.below hS'K'
  letI hS'Sfinite : Finite
      (S.toSubgroup ⧸ S'.toSubgroup.subgroupOf S.toSubgroup) :=
    FiniteIntermediateField.finite_extension_of_le
      (K := E.base.field) hSK hS'S
  letI hSabsolute : Finite ((baseField G).toSubgroup ⧸
      S.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    D.frobeniusFixedField_absoluteFinite E.base L hLK τ
  letI hS'absolute : Finite ((baseField G).toSubgroup ⧸
      S'.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    D.frobeniusFixedField_absoluteFinite E.field L' hL'K' σ
  let Sfinite : FiniteAbstractField G := ⟨S, hSabsolute⟩
  let S'finite : FiniteAbstractField G := ⟨S', hS'absolute⟩
  let ES'S : FiniteAbstractFieldExtension G :=
    { field := S'finite
      base := Sfinite
      below := hS'S
      finiteQuotient := hS'Sfinite }
  let π : ambientFixedAddSubgroup A S' := v.chosenPrimeElement S'finite
  have hπ : v.IsPrimeElement S'finite π := v.chosenPrimeElement_isPrime S'finite
  let πS : ambientFixedAddSubgroup A S := relativeNorm A S S' hS'S π
  have hTot : ES'S.IsTotallyRamified D := by
    have hTot' :=
      D.finiteReciprocityNaturalityFrobeniusFixedField_isTotallyRamified
        ER L L' hLK hL'K' hL'L σ
    change ES'S.IsTotallyRamified D at hTot'
    exact hTot'
  have hπS : v.IsPrimeElement Sfinite πS :=
    v.norm_prime_of_totallyRamified ES'S hTot π hπ
  change finiteReciprocityNaturalityNormMap
      A E.base.field E.field.field L L' hLK hL'K' E.below hL'L
      (D.finiteReciprocityHom A v hAxiom E.field L' hL'K' q) =
    D.finiteReciprocityHom A v hAxiom E.base L hLK
      ((finiteReciprocityNaturalityRestriction
        E.base.field E.field.field L L' E.below hL'L).toAdditive q)
  calc
    finiteReciprocityNaturalityNormMap
        A E.base.field E.field.field L L' hLK hL'K' E.below hL'L
        (D.finiteReciprocityHom A v hAxiom E.field L' hL'K' q) =
      finiteReciprocityNaturalityNormMap
        A E.base.field E.field.field L L' hLK hL'K' E.below hL'L
        (finiteNormClass A E.field.field L' hL'K'
          (relativeNorm A E.field.field S' hS'K' π)) := by
      apply congrArg (finiteReciprocityNaturalityNormMap
        A E.base.field E.field.field L L' hLK hL'K' E.below hL'L)
      have hprime :=
        D.finiteReciprocityHom_apply_eq_primeNormClass
          A v hAxiom E.field L' hL'K' q σ hσ π hπ
      change D.finiteReciprocityHom A v hAxiom E.field L' hL'K' q =
        finiteNormClass A E.field.field L' hL'K'
          (relativeNorm A E.field.field S' hS'K' π) at hprime
      exact hprime
    _ = finiteNormClass A E.base.field L hLK
        (relativeNorm A E.base.field S hSK πS) := by
      exact finiteReciprocityNaturality_norm_tower_class
        A E.base.field E.field.field L L' S S'
        hLK hL'K' E.below hL'L hSK hS'K' hS'S π
    _ = D.finiteReciprocityHom A v hAxiom E.base L hLK
        ((finiteReciprocityNaturalityRestriction
          E.base.field E.field.field L L' E.below hL'L).toAdditive q) := by
      symm
      have hprime :=
        D.finiteReciprocityHom_apply_eq_primeNormClass
          A v hAxiom E.base L hLK _ τ hτ πS hπS
      change D.finiteReciprocityHom A v hAxiom E.base L hLK _ =
        finiteNormClass A E.base.field L hLK
          (relativeNorm A E.base.field S hSK πS) at hprime
      exact hprime

end DegreeData

/-- **The norm identity of the conjugation diagram in the conjugate
quotient**
([Yamaguchi 2026, `MainNaturality.lean:786`][Yamaguchi2026]). -/
theorem finiteReciprocityNaturality_conjugation_norm_class
    [ContinuousMul G] (A : Rep ℤ G)
    (K L S : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hSK : S.toSubgroup ≤ K.toSubgroup) (s : G)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    [Finite (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup)]
    (π : ambientFixedAddSubgroup A S) :
    let hConjLK := conjugateClosedSubgroup_mono hLK s
    let hConjSK := conjugateClosedSubgroup_mono hSK s
    letI : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
        (conjugateClosedSubgroup L s).toSubgroup.subgroupOf
          (conjugateClosedSubgroup K s).toSubgroup) :=
      finite_conjugateExtension K L s
    letI : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
        (conjugateClosedSubgroup S s).toSubgroup.subgroupOf
          (conjugateClosedSubgroup K s).toSubgroup) :=
      finite_conjugateExtension K S s
    finiteReciprocityNaturalityConjugationNormMap A K L hLK s
        (finiteNormClass A K L hLK
          (relativeNorm A K S hSK π)) =
      finiteNormClass A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s) hConjLK
        (relativeNorm A (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup S s) hConjSK
          (conjugateFixedElement A S s π)) := by
  dsimp only
  rw [finiteReciprocityNaturalityConjugationNormMap_finiteNormClass,
    relativeNorm_conjugate_apply]

end Representation

end

end Atlas.Knowledge
