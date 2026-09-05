import Mathlib
import Atlas.Knowledge.AbstractExtension
import Atlas.Knowledge.ChosenPrimeElement
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractExtension
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteAbstractFieldExtension
import Atlas.Knowledge.FiniteFieldUnitMaps
import Atlas.Knowledge.FiniteResidueAbstractField
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.PrimeElement
import Atlas.Knowledge.ReciprocityMap
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.UnramifiedNormQuotient
import Atlas.Knowledge.ValuationData

/-!
# Unramified Frobenius fixed field

The unramified-case facts behind the norm-quotient equivalence: for an
unramified `L | K`, the fixed field of the chosen degree-one Frobenius
lift is itself unramified of degree one over `K`, so the included prime
of `K` is a prime of that fixed field and its relative norm is the
original prime (#104).

## Main statements

* `DegreeData.unramifiedFrobenius_fixedField_isUnramified` — the fixed
  field is unramified; proved.
* `DegreeData.unramifiedFrobenius_fixedField_degree` — the fixed field
  has degree one; proved.
* `ValuationData.unramifiedFrobenius_primeNorm` — the included prime's
  norm is the original prime; proved.
* `ValuationData.unramifiedFrobenius_includedPrime_isPrime` — the
  included prime is prime; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling.
Both sections sit at the source's `Type u`, the two valuation theorems'
since the #104 hoist unpinned the quotient-action chain it follows, and
the source's mid-file `unramifiedReciprocity` section is cut at the
prime lemmas and closed here as `unramifiedReciprocityHead`, its
remainder being the next brick. All four theorems shed the source's
`[T2Space G]`, and the first its `[CompactSpace G]` too — all simply
unused, so the ported statements are strictly more general than the
source's — and the valuation theorems drop the source's four enrichment
`letI` re-anchors, statement-level and proof-level alike: the
`FiniteFieldUnitMaps` transport instance stands in, so their statements
have one fewer binding than the source's. The extension bundles are the
layer's top-level `AbstractExtension`, `FiniteAbstractExtension`, and
`FiniteAbstractFieldExtension`. The `FiniteFieldUnitMaps` import is
referenced by no name, carrying the transport instances above. The
citations name this file by bare basename; it lives at
`AbstractClassFieldTheory/Reciprocity/Construction/` in the source. The
source's `open`s go — the layer keeps everything in one namespace.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

section unramifiedFixedFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **For an unramified `L | K`, the fixed field of the degree-one
Frobenius lift is itself unramified over `K`**
([Yamaguchi 2026, `MainFiniteReciprocity.lean:805`][Yamaguchi2026]). -/
theorem unramifiedFrobenius_fixedField_isUnramified
    (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (hUnramified :
      (AbstractExtension.mk L K.field hLK).IsUnramified D) :
    (AbstractExtension.mk
      (D.frobeniusFixedField K L hLK
        (D.chosenUnramifiedFrobeniusLift K L hLK)) K.field
      (D.frobeniusFixedField_le K L hLK
        (D.chosenUnramifiedFrobeniusLift K L hLK))).IsUnramified D := by
  let σ := D.chosenUnramifiedFrobeniusLift K L hLK
  let S := D.frobeniusFixedField K L hLK σ
  let hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le K L hLK σ
  rw [(AbstractExtension.mk S K.field hSK).isUnramified_iff_inertia_le D]
  intro g hg
  have hgL : g ∈ L.toSubgroup :=
    ((AbstractExtension.mk L K.field hLK).isUnramified_iff_inertia_le D).1
      hUnramified hg
  exact D.fieldInertia_le_frobeniusFixedField K L hLK σ
    ⟨hgL, hg.2⟩

/-- **The fixed field of the degree-one lift has degree one over `K` in
the unramified case** — `f_{Σ|K} = d_K(φ_K) = 1` together with
`[Σ:K] = f_{Σ|K}`
([Yamaguchi 2026, `MainFiniteReciprocity.lean:833`][Yamaguchi2026]). -/
theorem unramifiedFrobenius_fixedField_degree
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hUnramified :
      (AbstractExtension.mk L K.field hLK).IsUnramified D) :
    let σ := D.chosenUnramifiedFrobeniusLift K L hLK
    let S := D.frobeniusFixedField K L hLK σ
    let hSK := D.frobeniusFixedField_le K L hLK σ
    letI : Finite
        (K.field.toSubgroup ⧸ S.toSubgroup.subgroupOf K.field.toSubgroup) :=
      D.frobeniusFixedField_finite K L hLK σ
    ((FiniteAbstractExtension.ofInclusion S K.field hSK).degree : ℕ) = 1 := by
  let σ := D.chosenUnramifiedFrobeniusLift K L hLK
  let S := D.frobeniusFixedField K L hLK σ
  let hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le K L hLK σ
  letI : Finite
      (K.field.toSubgroup ⧸ S.toSubgroup.subgroupOf K.field.toSubgroup) :=
    D.frobeniusFixedField_finite K L hLK σ
  let E : FiniteAbstractExtension G :=
    FiniteAbstractExtension.ofInclusion S K.field hSK
  have hSUnramified :
      (AbstractExtension.mk S K.field hSK).IsUnramified D :=
    D.unramifiedFrobenius_fixedField_isUnramified
      K L hLK hUnramified
  calc
    (E.degree : ℕ) = (E.residueDegree D : ℕ) := by
      symm
      exact E.residueDegree_eq_degree_of_isUnramified D (by
        simpa [E, FiniteAbstractExtension.ofInclusion] using hSUnramified)
    _ = D.frobeniusExponent K L hLK σ :=
      D.frobeniusFixedField_residueDegreeOverBase K L hLK σ
    _ = 1 := D.chosenUnramifiedFrobeniusLift_exponent K L hLK

end DegreeData

end unramifiedFixedFields

section unramifiedReciprocityHead

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

/-- **The prime element of `K`, included into the fixed field of the
degree-one lift, has norm equal to the original prime element**
([Yamaguchi 2026, `MainFiniteReciprocity.lean:887`][Yamaguchi2026]). -/
theorem unramifiedFrobenius_primeNorm
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hUnramified :
      (AbstractExtension.mk L K.field hLK).IsUnramified D) :
    let KR := K.toFiniteResidueAbstractField D
    let σ := D.chosenUnramifiedFrobeniusLift KR L hLK
    let S := D.frobeniusFixedField KR L hLK σ
    let hSK := D.frobeniusFixedField_le KR L hLK σ
    letI : Finite
        (K.field.toSubgroup ⧸ S.toSubgroup.subgroupOf K.field.toSubgroup) :=
      D.frobeniusFixedField_finite KR L hLK σ
    relativeNorm A K.field S hSK
        (fixedFieldInclusion A K.field S hSK (v.chosenPrimeElement K)) =
      v.chosenPrimeElement K := by
  dsimp only
  let KR := K.toFiniteResidueAbstractField D
  let σ := D.chosenUnramifiedFrobeniusLift KR L hLK
  letI : Finite
      (K.field.toSubgroup ⧸
        (D.frobeniusFixedField KR L hLK σ).toSubgroup.subgroupOf
          K.field.toSubgroup) :=
    D.frobeniusFixedField_finite KR L hLK σ
  let S := D.frobeniusFixedField KR L hLK σ
  let hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le KR L hLK σ
  let E : FiniteAbstractExtension G :=
    FiniteAbstractExtension.ofInclusion S K.field hSK
  change relativeNorm A K.field S hSK
      (fixedFieldInclusion A K.field S hSK (v.chosenPrimeElement K)) =
    v.chosenPrimeElement K
  calc
    relativeNorm A K.field S hSK
        (fixedFieldInclusion A K.field S hSK (v.chosenPrimeElement K)) =
        (E.degree : ℕ) • v.chosenPrimeElement K := by
      have hnorm :=
        relativeNorm_fixedFieldInclusion A E (v.chosenPrimeElement K)
      change relativeNorm A K.field S hSK
          (fixedFieldInclusion A K.field S hSK (v.chosenPrimeElement K)) =
        (E.degree : ℕ) • v.chosenPrimeElement K at hnorm
      exact hnorm
    _ = 1 • v.chosenPrimeElement K := by
      rw [show (E.degree : ℕ) = 1 by
        have hdegree :=
          D.unramifiedFrobenius_fixedField_degree
            KR L hLK hUnramified
        change (E.degree : ℕ) = 1 at hdegree
        exact hdegree]
    _ = v.chosenPrimeElement K := one_nsmul _

/-- **The included prime element is a prime element of the degree-one
lift's fixed field**
([Yamaguchi 2026, `MainFiniteReciprocity.lean:947`][Yamaguchi2026]). -/
theorem unramifiedFrobenius_includedPrime_isPrime
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hUnramified :
      (AbstractExtension.mk L K.field hLK).IsUnramified D) :
    let KR := K.toFiniteResidueAbstractField D
    let σ := D.chosenUnramifiedFrobeniusLift KR L hLK
    let S := D.frobeniusFixedField KR L hLK σ
    let hSK := D.frobeniusFixedField_le KR L hLK σ
    letI : Finite
        (K.field.toSubgroup ⧸ S.toSubgroup.subgroupOf K.field.toSubgroup) :=
      D.frobeniusFixedField_finite KR L hLK σ
    letI : Finite ((baseField G).toSubgroup ⧸
        S.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
      D.frobeniusFixedField_absoluteFinite K L hLK σ
    let Sigma : FiniteAbstractField G := ⟨S, inferInstance⟩
    v.IsPrimeElement Sigma
      (fixedFieldInclusion A K.field S hSK (v.chosenPrimeElement K)) := by
  dsimp only
  let KR := K.toFiniteResidueAbstractField D
  let σ := D.chosenUnramifiedFrobeniusLift KR L hLK
  let S := D.frobeniusFixedField KR L hLK σ
  let hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le KR L hLK σ
  letI hSfinite : Finite
      (K.field.toSubgroup ⧸ S.toSubgroup.subgroupOf K.field.toSubgroup) :=
    D.frobeniusFixedField_finite KR L hLK σ
  letI hSabsolute : Finite ((baseField G).toSubgroup ⧸
      S.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ
  let Sigma : FiniteAbstractField G := ⟨S, hSabsolute⟩
  let ES : FiniteAbstractFieldExtension G :=
    { field := Sigma
      base := K
      below := hSK
      finiteQuotient := hSfinite }
  have hES : ES.IsUnramified D := by
    have hunramified :=
      D.unramifiedFrobenius_fixedField_isUnramified KR L hLK hUnramified
    change ES.IsUnramified D at hunramified
    exact hunramified
  exact v.prime_of_unramified ES hES
    (v.chosenPrimeElement K) (v.chosenPrimeElement_isPrime K)

end ValuationData

end unramifiedReciprocityHead

end

end Atlas.Knowledge
