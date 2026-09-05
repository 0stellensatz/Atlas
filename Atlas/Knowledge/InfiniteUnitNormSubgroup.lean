import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteAbstractFieldExtension
import Atlas.Knowledge.FiniteFieldUnitMaps
import Atlas.Knowledge.FiniteIntermediateFieldRefinement
import Atlas.Knowledge.FiniteTower
import Atlas.Knowledge.InfiniteNormSubgroup
import Atlas.Knowledge.InfiniteUnitDescent
import Atlas.Knowledge.PrimeElement
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.RelativeNormLaws
import Atlas.Knowledge.ValuationData

/-!
# Infinite unit norm subgroup

The finite-level unit norm ranges `N_{M/K} U_M` and their intersection,
the universal unit norm group `N_{E/K} U_E = ⋂_M N_{M/K} U_M`, with the
tower compatibility that lets a norm from any finite overfield land in
any lower range, and the comparison bounding the unit norm groups by the
ambient norm subgroups (#104).

## Main definitions

* `ValuationData.finiteIntermediateUnitNormRange` — the image
  `N_{M/K} U_M` from one finite intermediate field.
* `ValuationData.infiniteUnitNormSubgroup` — the universal unit norm
  group.

## Main statements

* `ValuationData.mem_finiteIntermediateUnitNormRange_of_overfield` — a
  unit norm from a finite overfield of `M` lies in `M`'s range; proved.
* `ValuationData.infiniteUnitNormSubgroup_le_normSubgroup` — the unit
  norm group sits inside the ambient norm subgroup; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
the finiteness of a tower stage is #136's two-argument
instance-supplied form, `FiniteTower` sits at the layer's top level,
and the ambient group is `Type u` since the #104 hoist flipped the
unit-descent chain the file draws on; the source's no-op `open`s are
dropped, and its `simpa` bridge for the intermediate unit is the plain
definitionally-equal term — the mismatch it smoothed lives in a
proof-irrelevant field, and the layer's simp set over-reduces the unit
group to its subtype instead.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- **The image `N_{M/K} U_M` from one finite intermediate field**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitNormSubgroup.lean:30`]
[Yamaguchi2026]). -/
def finiteIntermediateUnitNormRange
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (M : FiniteIntermediateField E K.field) :
    AddSubgroup (ambientFixedAddSubgroup A K.field) := by
  letI : Finite
      (K.field.toSubgroup ⧸
        M.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
    M.finite
  exact ((relativeNorm A K.field M.field M.below).comp
    (v.unitAddSubgroup (M.toFiniteAbstractField K)).subtype).range

/-- **A unit norm from a finite overfield of `M` already lies in the unit
norm range attached to `M`**, by transitivity of the actual norm
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitNormSubgroup.lean:43`]
[Yamaguchi2026]). -/
theorem mem_finiteIntermediateUnitNormRange_of_overfield
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (M P : FiniteIntermediateField E K.field)
    (hPM : P.field.toSubgroup ≤ M.field.toSubgroup)
    [hPfinite : Finite
      (K.field.toSubgroup ⧸
        P.field.toSubgroup.subgroupOf K.field.toSubgroup)]
    (uP : v.unitAddSubgroup (P.toFiniteAbstractField K))
    (aK : ambientFixedAddSubgroup A K.field)
    (haK : relativeNorm A K.field P.field P.below uP.1 = aK) :
    aK ∈ v.finiteIntermediateUnitNormRange E K M := by
  letI hMfinite : Finite
      (K.field.toSubgroup ⧸
        M.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
    M.finite
  letI hPMfinite : Finite
      (M.field.toSubgroup ⧸
        P.field.toSubgroup.subgroupOf M.field.toSubgroup) :=
    FiniteIntermediateField.finite_extension_of_le M.below hPM
  letI : Finite
      ((M.toFiniteAbstractField K).field.toSubgroup ⧸
        P.field.toSubgroup.subgroupOf
          (M.toFiniteAbstractField K).field.toSubgroup) := by
    change Finite
      (M.field.toSubgroup ⧸
        P.field.toSubgroup.subgroupOf M.field.toSubgroup)
    exact hPMfinite
  let EMP : FiniteAbstractFieldExtension G :=
    FiniteAbstractFieldExtension.ofInclusion
      P.field (M.toFiniteAbstractField K) hPM
  let uM : v.unitAddSubgroup (M.toFiniteAbstractField K) :=
    v.finiteUnitNorm EMP uP
  let T : FiniteTower G := {
    top := P.field
    middle := M.field
    base := K.field
    top_le_middle := hPM
    middle_le_base := M.below
    finiteTopQuotient := hPMfinite
    finiteBaseQuotient := hMfinite }
  simp only [finiteIntermediateUnitNormRange]
  change aK ∈ ((relativeNorm A K.field M.field M.below).comp
    (v.unitAddSubgroup (M.toFiniteAbstractField K)).subtype).range
  refine ⟨uM, ?_⟩
  change relativeNorm A K.field M.field M.below
      (relativeNorm A M.field P.field hPM uP.1) = aK
  calc
    _ = relativeNorm A K.field P.field (hPM.trans M.below) uP.1 :=
      T.norm_trans_apply A uP.1
    _ = relativeNorm A K.field P.field P.below uP.1 := by rfl
    _ = aK := haK

/-- **The universal unit norm group `N_{E/K} U_E = ⋂_M N_{M/K} U_M`**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitNormSubgroup.lean:95`]
[Yamaguchi2026]). -/
def infiniteUnitNormSubgroup
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G) :
    AddSubgroup (ambientFixedAddSubgroup A K.field) :=
  ⨅ M : FiniteIntermediateField E K.field,
    v.finiteIntermediateUnitNormRange E K M

/-- Membership in the universal unit norm group is membership in every
finite-level range ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitNormSubgroup.lean:107`]
[Yamaguchi2026]). -/
@[simp]
theorem mem_infiniteUnitNormSubgroup_iff
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A K.field) :
    a ∈ v.infiniteUnitNormSubgroup E K ↔
      ∀ M : FiniteIntermediateField E K.field,
        a ∈ v.finiteIntermediateUnitNormRange E K M := by
  simp [infiniteUnitNormSubgroup]

/-- Each unit norm range sits inside the corresponding ambient norm range
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitNormSubgroup.lean:120`]
[Yamaguchi2026]). -/
theorem finiteIntermediateUnitNormRange_le_normRange
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (M : FiniteIntermediateField E K.field) :
    v.finiteIntermediateUnitNormRange E K M ≤
      finiteIntermediateNormRange A E K.field M := by
  letI hMfinite : Finite
      (K.field.toSubgroup ⧸
        M.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
    M.finite
  change
    ((relativeNorm A K.field M.field M.below).comp
      (v.unitAddSubgroup (M.toFiniteAbstractField K)).subtype).range ≤
        (relativeNorm A K.field M.field M.below).range
  rw [AddMonoidHom.range_comp]
  exact AddSubgroup.map_le_range _ _

/-- **The universal unit norm group sits inside the ambient norm
subgroup** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitNormSubgroup.lean:137`]
[Yamaguchi2026]). -/
theorem infiniteUnitNormSubgroup_le_normSubgroup
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G) :
    v.infiniteUnitNormSubgroup E K ≤
      infiniteNormSubgroup A E K.field := by
  intro a ha
  rw [mem_infiniteNormSubgroup_iff]
  intro M
  exact v.finiteIntermediateUnitNormRange_le_normRange E K M
    ((v.mem_infiniteUnitNormSubgroup_iff E K a).1 ha M)

end ValuationData

end

end Atlas.Knowledge
