import Mathlib
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FiniteReciprocityNaturalityNorm
import Atlas.Knowledge.FiniteTower
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.IntermediateGaloisTransfer
import Atlas.Knowledge.TransferNormFrobeniusGeometry

/-!
# reciprocity exact rows

For a finite Galois tower `L | M | K`, the two rows of the abstract
reciprocity diagram on the actual finite Galois groups and finite norm
quotients: `1 → G(L/M) → G(L/K) → G(M/K) → 1` and
`A_M / N_{L/M} A_L → A_K / N_{L/K} A_L → A_K / N_{M/K} A_M → 0`. No
exactness or bijectivity statement is taken as an input; both rows are
proved directly from quotient membership and norm transitivity (#104).

## Main definitions

* `abstractReciprocityNormMap` — the first arrow in the lower row,
  induced by `N_{M/K}`.
* `abstractReciprocityNormProjection` — the quotient projection
  `A_K/N_{L/K}A_L → A_K/N_{M/K}A_M` in the lower row.

## Main statements

* `abstractReciprocity_galois_exact` — the upper row is exact at
  `G(L/K)`; proved.
* `abstractReciprocity_normQuotient_exact` — the lower row is exact at
  `A_K/N_{L/K}A_L`; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling, so
`mem_extensionSubgroup_iff` becomes Mathlib's
`Subgroup.mem_subgroupOf`. Calls to the layer's slimmed transfer forms
shed the containments those items stopped asking for:
`transferNormNaturality_intermediateExtension_normal K M L hMK` and
`transferNormNaturalityIntermediateInclusion K M L hMK` drop the
source's `hLM`, and the layer's six-argument
`finiteReciprocityNaturalityRestriction K K M L le_rfl hLM` replaces
the source's eight-argument call. `DegreeData.FiniteTower` is the
layer's top-level `FiniteTower`. One `noncomputable section` holds
everything at `Type u` since the #104 hoist merged its two
ambient-group scopes: the Galois row keeps the source's per-declaration
`Type*` generality, the norm projection family generalizes to `Type u`
from the source's file-level `IntegralRepGroupType` pin (which only its
`Rep`-machinery neighbours ever forced), and the four declarations that
consume the naturality norm map — `Type`-pinned until the hoist — keep
the place the former shadowing `variable` line gave them, which leaves
the projection family ahead of `abstractReciprocityNormMap` relative to
the source order. The source redeclares
`{G : Type*} [Group G] [TopologicalSpace G]` on each group-only
declaration to escape its file-level `IntegralRepGroupType`; one
`variable` line makes that unnecessary here. Three containments the
source's `extensionSubgroup` statements consumed go inert under the
spelling and stay as underscore-named semantic guards, keeping every
arity the source's callers expect: `_hMK` on
`abstractReciprocityRestriction` and `_hLM` on
`abstractReciprocityInclusion` and
`abstractReciprocity_lowerExtension_finite`. The source file's
`ValuationData` section (`:32`–`:427`) is deliberately unprovided, per
the interface decision recorded in `Atlas.Knowledge.ClassFieldAxiom`;
the remaining tail (`:890`–`:1263`) is the next brick.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The restriction `G(L/K) → G(M/K)` in the upper row — the base
containment is an inert semantic guard (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:453`). -/
def abstractReciprocityRestriction
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (_hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) →*
      (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) := by
  apply QuotientGroup.map
    (L.toSubgroup.subgroupOf K.toSubgroup)
    (M.toSubgroup.subgroupOf K.toSubgroup)
    (MonoidHom.id K.toSubgroup)
  intro k hk
  exact hLM hk

/-- The restriction fixes quotient representatives (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:475`). -/
@[simp]
theorem abstractReciprocityRestriction_mk
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (k : K.toSubgroup) :
    abstractReciprocityRestriction K M L hLM hMK (QuotientGroup.mk k) =
      QuotientGroup.mk k :=
  rfl

/-- Restriction to the intermediate Galois extension is surjective
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:489`). -/
theorem abstractReciprocityRestriction_surjective
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    Function.Surjective (abstractReciprocityRestriction K M L hLM hMK) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro k
  exact ⟨QuotientGroup.mk k, rfl⟩

/-- With equal base fields, norm–conjugation naturality's Galois-side
restriction is the restriction of the exact row (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:505`). -/
theorem finiteReciprocityNaturalityRestriction_sameBase_eq_restriction
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    finiteReciprocityNaturalityRestriction K K M L le_rfl hLM =
      abstractReciprocityRestriction K M L hLM hMK := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro k
  rfl

/-- Finiteness of `L | K` implies finiteness of the quotient `G(M/K)`,
derived from the actual surjective restriction map (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:523`). -/
theorem abstractReciprocity_intermediateQuotient_finite
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
  Finite.of_surjective (abstractReciprocityRestriction K M L hLM hMK)
    (abstractReciprocityRestriction_surjective K M L hLM hMK)

/-- The inclusion `G(L/M) → G(L/K)` in the upper row; normality of
`L | M` is derived from normality of `L | K`, and the upper containment
is an inert semantic guard (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:539`). -/
def abstractReciprocityInclusion
    (K M L : ClosedSubgroup G)
    (_hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    letI : (L.toSubgroup.subgroupOf M.toSubgroup).Normal :=
      transferNormNaturality_intermediateExtension_normal K M L hMK
    (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup) →*
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) := by
  letI : (L.toSubgroup.subgroupOf M.toSubgroup).Normal :=
    transferNormNaturality_intermediateExtension_normal K M L hMK
  exact transferNormNaturalityIntermediateInclusion K M L hMK

/-- On quotient representatives, the inclusion is induced by inclusion
of the intermediate subgroup (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:559`). -/
@[simp]
theorem abstractReciprocityInclusion_mk
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (m : M.toSubgroup) :
    letI : (L.toSubgroup.subgroupOf M.toSubgroup).Normal :=
      transferNormNaturality_intermediateExtension_normal K M L hMK
    abstractReciprocityInclusion K M L hLM hMK (QuotientGroup.mk m) =
      QuotientGroup.mk (Subgroup.inclusion hMK m) := by
  letI : (L.toSubgroup.subgroupOf M.toSubgroup).Normal :=
    transferNormNaturality_intermediateExtension_normal K M L hMK
  rfl

/-- **The upper row is exact at `G(L/K)`: the image of `G(L/M)` is
exactly the kernel of restriction to `G(M/K)`** (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:577`). -/
theorem abstractReciprocity_galois_exact
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    letI : (L.toSubgroup.subgroupOf M.toSubgroup).Normal :=
      transferNormNaturality_intermediateExtension_normal K M L hMK
    (abstractReciprocityRestriction K M L hLM hMK).ker =
      (abstractReciprocityInclusion K M L hLM hMK).range := by
  letI : (L.toSubgroup.subgroupOf M.toSubgroup).Normal :=
    transferNormNaturality_intermediateExtension_normal K M L hMK
  ext q
  refine QuotientGroup.induction_on q ?_
  intro k
  constructor
  · intro hk
    change abstractReciprocityRestriction K M L hLM hMK
      (QuotientGroup.mk k) = 1 at hk
    have hkM : k ∈ M.toSubgroup.subgroupOf K.toSubgroup :=
      (QuotientGroup.eq_one_iff k).1 hk
    let m : M.toSubgroup := ⟨k.1, hkM⟩
    refine ⟨QuotientGroup.mk m, ?_⟩
    exact congrArg
      (fun t : K.toSubgroup =>
        (QuotientGroup.mk t :
          K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup))
      (Subtype.ext rfl)
  · rintro ⟨q, hq⟩
    rw [← hq]
    refine QuotientGroup.induction_on q ?_
    intro m
    change (QuotientGroup.mk (Subgroup.inclusion hMK m) :
      K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) = 1
    exact (QuotientGroup.eq_one_iff _).2 m.2

/-- Finiteness of `L | K` also implies finiteness of `L | M` — the upper
containment is an inert semantic guard (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:616`). -/
theorem abstractReciprocity_lowerExtension_finite
    (K M L : ClosedSubgroup G)
    (_hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    Finite (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup) := by
  let inclusion :
      (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup) →
        (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
    Quotient.map' (Subgroup.inclusion hMK) (by
      intro x y hxy
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      apply Subgroup.mem_subgroupOf.2
      simpa using Subgroup.mem_subgroupOf.1 hxy)
  apply Finite.of_injective inclusion
  intro x y
  refine QuotientGroup.induction_on x ?_
  intro m
  refine QuotientGroup.induction_on y ?_
  intro n h
  apply QuotientGroup.eq.mpr
  apply Subgroup.mem_subgroupOf.2
  have h' :
      (QuotientGroup.mk (Subgroup.inclusion hMK m) :
          K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) =
        QuotientGroup.mk (Subgroup.inclusion hMK n) := by
    simpa [inclusion] using h
  have hmem := QuotientGroup.eq.mp h'
  have hG := Subgroup.mem_subgroupOf.1 hmem
  simpa using hG

/-- Norm transitivity identifies the norm image from `L` with a subgroup
of the norm image from `M` (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:652`). -/
theorem abstractReciprocity_finiteNormSubgroup_le
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hKMfinite : Finite
      (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup)]
    [hMLfinite : Finite
      (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup)]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    finiteNormSubgroup A K L (hLM.trans hMK) ≤
      finiteNormSubgroup A K M hMK := by
  let T : FiniteTower G :=
    { top := L
      middle := M
      base := K
      top_le_middle := hLM
      middle_le_base := hMK
      finiteTopQuotient := hMLfinite
      finiteBaseQuotient := hKMfinite }
  rintro _ ⟨a, rfl⟩
  refine ⟨relativeNorm A M L hLM a, ?_⟩
  exact T.norm_trans_apply A a

/-- **The quotient projection `A_K/N_{L/K}A_L → A_K/N_{M/K}A_M` in the
lower row** (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:730`). -/
def abstractReciprocityNormProjection
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    letI : Finite (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    FiniteNormQuotient A K L (hLM.trans hMK) →+
      FiniteNormQuotient A K M hMK := by
  letI : Finite (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  letI : Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  apply finiteNormQuotientLift A K L (hLM.trans hMK)
    (finiteNormClassHom A K M hMK)
  intro a ha
  exact (finiteNormClass_eq_zero_iff A K M hMK a).2
    (abstractReciprocity_finiteNormSubgroup_le A K M L hLM hMK ha)

/-- The norm projection preserves the representative while passing to
the intermediate norm quotient (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:760`). -/
@[simp]
theorem abstractReciprocityNormProjection_finiteNormClass
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (a : ambientFixedAddSubgroup A K) :
    letI : Finite (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    abstractReciprocityNormProjection A K M L hLM hMK
        (finiteNormClass A K L (hLM.trans hMK) a) =
      finiteNormClass A K M hMK a := by
  letI : Finite (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  letI : Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  simp only [abstractReciprocityNormProjection]
  rfl

/-- The quotient projection in the lower row is surjective
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:818`). -/
theorem abstractReciprocityNormProjection_surjective
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    letI : Finite (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    Function.Surjective (abstractReciprocityNormProjection A K M L hLM hMK) := by
  letI : Finite (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  letI : Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  intro q
  refine FiniteNormQuotient.induction_on A K M hMK q ?_
  intro a
  exact ⟨finiteNormClass A K L (hLM.trans hMK) a, by
    rw [abstractReciprocityNormProjection_finiteNormClass]⟩

/-- **The first arrow in the lower row, induced by `N_{M/K}`**
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:677`). -/
def abstractReciprocityNormMap
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    letI : Finite (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    FiniteNormQuotient A M L hLM →+
      FiniteNormQuotient A K L (hLM.trans hMK) := by
  letI : Finite (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  letI : Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  exact finiteReciprocityNaturalityNormMap A K M L L (hLM.trans hMK) hLM hMK le_rfl

/-- The norm map sends a finite norm class to the class of the
corresponding relative norm (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:703`). -/
@[simp]
theorem abstractReciprocityNormMap_finiteNormClass
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (a : ambientFixedAddSubgroup A M) :
    letI : Finite (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    abstractReciprocityNormMap A K M L hLM hMK
        (finiteNormClass A M L hLM a) =
      finiteNormClass A K L (hLM.trans hMK)
        (relativeNorm A K M hMK a) := by
  letI : Finite (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  letI : Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  exact finiteReciprocityNaturalityNormMap_finiteNormClass A K M L L
    (hLM.trans hMK) hLM hMK le_rfl a

/-- When the two base fields coincide, the naturality norm map is the
ordinary projection between the two actual finite norm quotients
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:786`). -/
theorem finiteReciprocityNaturalityNormMap_sameBase_eq_normProjection
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    letI : Finite (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ K.toSubgroup.subgroupOf K.toSubgroup) :=
      (FiniteGaloisSubextension.refl K).finite
    finiteReciprocityNaturalityNormMap A K K M L hMK (hLM.trans hMK) le_rfl hLM =
      abstractReciprocityNormProjection A K M L hLM hMK := by
  letI : Finite (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  letI : Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  letI : Finite (K.toSubgroup ⧸ K.toSubgroup.subgroupOf K.toSubgroup) :=
    (FiniteGaloisSubextension.refl K).finite
  apply AddMonoidHom.ext
  intro q
  refine FiniteNormQuotient.induction_on A K L (hLM.trans hMK) q ?_
  intro a
  rw [finiteReciprocityNaturalityNormMap_finiteNormClass,
    abstractReciprocityNormProjection_finiteNormClass,
    relativeNorm_self]

/-- **The lower row is exact at `A_K/N_{L/K}A_L`** (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:843`). -/
theorem abstractReciprocity_normQuotient_exact
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    letI : Finite (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    Function.Exact (abstractReciprocityNormMap A K M L hLM hMK)
      (abstractReciprocityNormProjection A K M L hLM hMK) := by
  letI : Finite (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  letI : Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  rw [AddMonoidHom.exact_iff]
  ext q
  refine FiniteNormQuotient.induction_on A K L (hLM.trans hMK) q ?_
  intro a
  constructor
  · intro ha
    change abstractReciprocityNormProjection A K M L hLM hMK
        (finiteNormClass A K L (hLM.trans hMK) a) = 0 at ha
    rw [abstractReciprocityNormProjection_finiteNormClass] at ha
    have haM : a ∈ finiteNormSubgroup A K M hMK :=
      (finiteNormClass_eq_zero_iff A K M hMK a).1 ha
    obtain ⟨b, rfl⟩ := haM
    exact ⟨finiteNormClass A M L hLM b, by
      rw [abstractReciprocityNormMap_finiteNormClass]⟩
  · rintro ⟨q, hq⟩
    rw [← hq]
    refine FiniteNormQuotient.induction_on A M L hLM q ?_
    intro b
    change abstractReciprocityNormProjection A K M L hLM hMK
        (abstractReciprocityNormMap A K M L hLM hMK
          (finiteNormClass A M L hLM b)) = 0
    rw [abstractReciprocityNormMap_finiteNormClass,
      abstractReciprocityNormProjection_finiteNormClass]
    exact (finiteNormClass_eq_zero_iff A K M hMK _).2 ⟨b, rfl⟩

end

end Atlas.Knowledge
