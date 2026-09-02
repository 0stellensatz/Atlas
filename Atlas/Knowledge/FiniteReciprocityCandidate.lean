import Mathlib
import Atlas.Knowledge.ChosenPrimeElement
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteFieldUnitMaps
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FiniteReciprocityValue
import Atlas.Knowledge.FiniteResidueAbstractField
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusExponent
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.FrobeniusFixedField
import Atlas.Knowledge.FrobeniusLiftDifference
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.ValuationData

/-!
# Finite reciprocity candidate

The candidate map of the finite reciprocity equivalence: the complete
degree comparison of two Frobenius lifts, a chosen lift for each finite
Galois automorphism, and the candidate that evaluates a norm class
through its chosen lift — with the prime-norm-class formula and the
value at zero (#104).

## Main definitions

* `DegreeData.chosenFiniteReciprocityFrobeniusLift` — a specified lift.
* `DegreeData.finiteReciprocityCandidate` — the candidate map.

## Main statements

* `DegreeData.finiteReciprocityHom_lift_comparison` — the complete
  degree comparison; proved.
* `DegreeData.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift`
  — the chosen lift restricts to the prescribed automorphism; proved.
* `DegreeData.finiteReciprocityCandidate_apply` — evaluation through
  the chosen lift; proved.
* `DegreeData.finiteReciprocityCandidate_eq_primeNormClass` — the
  prime-norm-class formula; proved.
* `DegreeData.finiteReciprocityCandidate_zero` — zero to zero; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling.
The chosen-lift section stays at the source's `Type u`; the two
representation-bearing sections are `Type` after the `Type`-pinned
quotient-action chain, shed their enrichment `letI` bridges, the
instances threading through by defeq, and shed the source's `[T2Space
G]`, which was simply unused there — the ported statements are strictly
more general than the source's. The zero lemma loses the source's
`@[simp]`: the evaluation lemma's own `@[simp]` rewrites its left-hand
side first, so as a pair they fail `simpNF`, and the evaluation lemma
is the one simp can use. The `FiniteFieldUnitMaps` import is referenced
by no name: it carries the transport instances that let the
Frobenius-element binders synthesize across the residue enrichment. The
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

section liftComparison

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : Type} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **The complete degree comparison**: two lifts of the same finite
automorphism are either equal, or the larger-degree lift is the smaller
one times a positive Frobenius lift which restricts trivially and
therefore has zero value in the finite norm quotient
([Yamaguchi 2026, `MainFiniteReciprocity.lean:327`][Yamaguchi2026]). -/
theorem finiteReciprocityHom_lift_comparison
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ τ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hRestriction : D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK σ =
      D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK τ) :
    σ = τ ∨
      (∃ ι : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK,
        τ = σ * ι ∧
        D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK ι = 1 ∧
        D.finiteReciprocityValue A v K L hLK ι = 0) ∨
      (∃ ι : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK,
        σ = τ * ι ∧
        D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK ι = 1 ∧
        D.finiteReciprocityValue A v K L hLK ι = 0) := by
  let KR := K.toFiniteResidueAbstractField D
  rcases lt_trichotomy
      (D.frobeniusExponent KR L hLK σ)
      (D.frobeniusExponent KR L hLK τ) with hlt | heq | hgt
  · right
    left
    let ι := D.frobeniusLiftDifference KR L hLK σ τ hlt
    refine ⟨ι, ?_, ?_, ?_⟩
    · exact (D.mul_frobeniusLiftDifference KR L hLK σ τ hlt).symm
    · exact D.frobeniusRestriction_frobeniusLiftDifference
        KR L hLK σ τ hRestriction hlt
    · exact D.finiteReciprocityValue_eq_zero_of_restriction_eq_one
        A v K L hLK ι
        (D.frobeniusRestriction_frobeniusLiftDifference
          KR L hLK σ τ hRestriction hlt)
  · left
    exact D.frobenius_eq_of_restriction_eq_of_exponent_eq
      KR L hLK hRestriction heq
  · right
    right
    let ι := D.frobeniusLiftDifference KR L hLK τ σ hgt
    refine ⟨ι, ?_, ?_, ?_⟩
    · exact (D.mul_frobeniusLiftDifference KR L hLK τ σ hgt).symm
    · exact D.frobeniusRestriction_frobeniusLiftDifference
        KR L hLK τ σ hRestriction.symm hgt
    · exact D.finiteReciprocityValue_eq_zero_of_restriction_eq_one
        A v K L hLK ι
        (D.frobeniusRestriction_frobeniusLiftDifference
          KR L hLK τ σ hRestriction.symm hgt)

end DegreeData

end liftComparison

section chosenFrobeniusLifts

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **A specified Frobenius lift of a finite Galois automorphism**,
chosen from the surjectivity in the finite degree-quotient
decomposition
([Yamaguchi 2026, `MainFiniteReciprocity.lean:395`][Yamaguchi2026]). -/
def chosenFiniteReciprocityFrobeniusLift (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (q : K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup) :
    D.FrobeniusElements K L hLK :=
  Classical.choose (D.frobeniusRestriction_surjective K L hLK q)

/-- **The chosen lift restricts to the prescribed automorphism**
([Yamaguchi 2026, `MainFiniteReciprocity.lean:407`][Yamaguchi2026]). -/
@[simp]
theorem frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (q : K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup) :
    D.frobeniusRestriction K L hLK
      (D.chosenFiniteReciprocityFrobeniusLift K L hLK q) = q :=
  Classical.choose_spec (D.frobeniusRestriction_surjective K L hLK q)

end DegreeData

end chosenFrobeniusLifts

section finiteReciprocityHomHead

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : Type} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **The canonical candidate underlying the finite reciprocity
equivalence**: choose the finite degree-quotient decomposition lift and
evaluate in the finite norm quotient; lift-independence and additivity
reduce to the concrete steps above and reciprocity multiplicativity
([Yamaguchi 2026, `MainFiniteReciprocity.lean:433`][Yamaguchi2026]). -/
def finiteReciprocityCandidate (D : DegreeData G) (A : Rep ℤ G)
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)] :
    Additive (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup) →
      FiniteNormQuotient A K.field L hLK :=
  fun q => D.finiteReciprocityValue A v K L hLK
    (D.chosenFiniteReciprocityFrobeniusLift
      (K.toFiniteResidueAbstractField D) L hLK q.toMul)

/-- **The candidate evaluates through the chosen lift**
([Yamaguchi 2026, `MainFiniteReciprocity.lean:449`][Yamaguchi2026]). -/
@[simp]
theorem finiteReciprocityCandidate_apply (D : DegreeData G) (A : Rep ℤ G)
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (q : Additive
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)) :
    D.finiteReciprocityCandidate A v K L hLK q =
      D.finiteReciprocityValue A v K L hLK
        (D.chosenFiniteReciprocityFrobeniusLift
          (K.toFiniteResidueAbstractField D) L hLK q.toMul) :=
  rfl

/-- **The candidate is the finite class of the chosen prime's relative
norm from the chosen lift's fixed field**
([Yamaguchi 2026, `MainFiniteReciprocity.lean:467`][Yamaguchi2026]). -/
theorem finiteReciprocityCandidate_eq_primeNormClass
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (q : Additive
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)) :
    let KR := K.toFiniteResidueAbstractField D
    let σ := D.chosenFiniteReciprocityFrobeniusLift KR L hLK q.toMul
    let S := D.frobeniusFixedField KR L hLK σ
    let hSK := D.frobeniusFixedField_le KR L hLK σ
    letI : Finite
        (K.field.toSubgroup ⧸ S.toSubgroup.subgroupOf K.field.toSubgroup) :=
      D.frobeniusFixedField_finite KR L hLK σ
    letI : Finite ((baseField G).toSubgroup ⧸
        S.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
      D.frobeniusFixedField_absoluteFinite K L hLK σ
    let Sigma : FiniteAbstractField G := ⟨S, inferInstance⟩
    D.finiteReciprocityCandidate A v K L hLK q =
      finiteNormClass A K.field L hLK
        (relativeNorm A K.field S hSK (v.chosenPrimeElement Sigma)) := by
  dsimp only
  exact D.finiteReciprocityValue_eq_primeNormClass
    A v K L hLK
      (D.chosenFiniteReciprocityFrobeniusLift
        (K.toFiniteResidueAbstractField D) L hLK q.toMul)

/-- **The candidate sends zero to zero**
([Yamaguchi 2026, `MainFiniteReciprocity.lean:501`][Yamaguchi2026]). -/
theorem finiteReciprocityCandidate_zero (D : DegreeData G) (A : Rep ℤ G)
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)] :
    D.finiteReciprocityCandidate A v K L hLK 0 = 0 := by
  apply D.finiteReciprocityValue_eq_zero_of_restriction_eq_one
  exact D.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift
    (K.toFiniteResidueAbstractField D) L hLK
      (1 : K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)

end DegreeData

end finiteReciprocityHomHead

end

end Atlas.Knowledge
