import Mathlib
import Atlas.Knowledge.FiniteIntermediateFieldRefinement
import Atlas.Knowledge.MaximalUnramifiedField
import Atlas.Knowledge.ReciprocityMap
import Atlas.Knowledge.UnitCohomologyAxiom
import Atlas.Knowledge.UnramifiedQuotientGenerator

/-!
# reciprocity independence

Independence of the prime element: assuming the unit-cohomology axiom,
replacing the chosen prime of the Frobenius fixed field by any other prime
does not change the reciprocity class. The difference of primes is a unit,
and at each finite level the Galois refinement of the level meets the fixed
field in an unramified cyclic compositum, where the axiom writes the unit
as a norm — so the difference of reciprocity values is a norm from every
finite intermediate field of the maximal unramified extension (#104).

## Main statements

* `DegreeData.reciprocityValueOfPrime_eq_reciprocityMap` — the reciprocity
  value at any prime element is the reciprocity map's value; proved.

## Implementation notes

Where the source destructures the axiom into two Tate-vanishing facts and
feeds the `Ĥ⁰` eliminator, the layer's elementary axiom hands the norm
witness directly, at the same bundle and generator. The bridges across the
residue enrichment — the instance transports and the explicit
unramifiedness argument alike — are plain terms, as in
`Atlas.Knowledge.ReciprocityMap`, and three of the source's locals — one
already dead in the source — are dead here and not carried.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **Independence of the prime element**: assuming the unit-cohomology axiom,
the reciprocity value at any prime of the Frobenius fixed field is the
reciprocity map's value (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean:369`). -/
theorem reciprocityValueOfPrime_eq_reciprocityMap
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK
      (hLnormal := hLnormal))
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
        (hLnormal := hLnormal) σ))
    (hπ :
      let Sigma : FiniteAbstractField G :=
        { field := D.frobeniusFixedField
            (K.toFiniteResidueAbstractField D) L hLK
            (hLnormal := hLnormal) σ
          finite := D.frobeniusFixedField_absoluteFinite K L hLK σ }
      v.IsPrimeElement Sigma π) :
    D.reciprocityValueOfPrime A (K.toFiniteResidueAbstractField D)
        L hLK (hLnormal := hLnormal) (hLfinite := hLfinite) σ π =
      D.reciprocityMap A v K L hLK σ := by
  let KR := K.toFiniteResidueAbstractField D
  letI hLnormalKR :
      (L.toSubgroup.subgroupOf KR.field.toSubgroup).Normal := hLnormal
  letI hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf KR.field.toSubgroup) := hLfinite
  let S := D.frobeniusFixedField KR L hLK σ
  let E := D.maximalUnramifiedField L
  have hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le KR L hLK σ
  letI hSfinite : Finite
      (K.field.toSubgroup ⧸ S.toSubgroup.subgroupOf K.field.toSubgroup) :=
    D.frobeniusFixedField_finite KR L hLK σ
  letI hSabsolute : Finite ((baseField G).toSubgroup ⧸
      S.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ
  let Sigma : FiniteAbstractField G := ⟨S, hSabsolute⟩
  have hπSigma : v.IsPrimeElement Sigma π := by
    simpa [Sigma, S, KR] using hπ
  let π₀ : ambientFixedAddSubgroup A S := v.chosenPrimeElement Sigma
  let u : v.unitAddSubgroup Sigma :=
    ⟨π - π₀, v.sub_chosenPrimeElement_mem_unitAddSubgroup Sigma hπSigma⟩
  rw [D.reciprocityMap_eq_chosenPrime A v K L hLK σ]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  change relativeNorm A K.field S hSK π -
      relativeNorm A K.field S hSK π₀ ∈ infiniteNormSubgroup A E K.field
  rw [← map_sub]
  change relativeNorm A K.field S hSK u.1 ∈
    infiniteNormSubgroup A E K.field
  rw [mem_infiniteNormSubgroup_iff]
  intro M
  letI hEnormal :
      (E.toSubgroup.subgroupOf K.field.toSubgroup).Normal :=
    D.subgroupOf_maximalUnramifiedField_normal K.field L hLK
  let R := M.galoisRefinement
  let P := R.compositumWith S
  have hPS : P.toSubgroup ≤ S.toSubgroup :=
    R.compositumWith_le_right S
  have hPK : P.toSubgroup ≤ K.field.toSubgroup := hPS.trans hSK
  have hPM : P.toSubgroup ≤ M.field.toSubgroup :=
    (R.compositumWith_le_left S).trans M.galoisRefinement_le_field
  letI hPSnormal :
      (P.toSubgroup.subgroupOf S.toSubgroup).Normal :=
    FiniteIntermediateField.compositumWith_normal R S hSK
  letI hPSfinite : Finite
      (S.toSubgroup ⧸ P.toSubgroup.subgroupOf S.toSubgroup) :=
    R.compositumWith_finite S hSK
  letI hPKfinite : Finite
      (K.field.toSubgroup ⧸ P.toSubgroup.subgroupOf K.field.toSubgroup) :=
    R.compositumWith_finite_over_base S
  have hSinertia : D.fieldInertia S = E := by
    dsimp [S, E]
    exact D.frobeniusFixedField_fieldInertia KR L hLK σ
  have hPSunramified :
      (⟨P, S, hPS⟩ : AbstractExtension G).IsUnramified D := by
    intro x hx
    change x ∈ R.field.toSubgroup ∧ x ∈ S.toSubgroup
    refine ⟨R.above ?_, hx.1⟩
    have hxI : x ∈ D.fieldInertia S := ⟨hx.1, hx.2⟩
    rw [hSinertia] at hxI
    exact hxI
  let Sresidue := Sigma.toFiniteResidueAbstractField D
  letI hPSnormalResidue :
      (P.toSubgroup.subgroupOf Sresidue.field.toSubgroup).Normal :=
    hPSnormal
  letI hPSfiniteResidue : Finite
      (Sresidue.field.toSubgroup ⧸
        P.toSubgroup.subgroupOf Sresidue.field.toSubgroup) :=
    hPSfinite
  obtain ⟨g, hg⟩ :=
    D.exists_quotient_generator_of_unramified
      Sresidue P hPS hPSunramified
  letI : Fintype (S.toSubgroup ⧸ P.toSubgroup.subgroupOf S.toSubgroup) :=
    Fintype.ofFinite _
  let Euc : FiniteUnramifiedCyclicExtension D Sigma :=
    { field := P
      below := hPS
      normal := hPSnormal
      finite := hPSfinite
      generator := g
      generates := hg
      unramified := hPSunramified }
  obtain ⟨ε, hε⟩ := (hAxiom Sigma Euc).1 u
  letI hMfinite : Finite
      (K.field.toSubgroup ⧸
        M.field.toSubgroup.subgroupOf K.field.toSubgroup) := M.finite
  letI hPMfinite : Finite
      (M.field.toSubgroup ⧸ P.toSubgroup.subgroupOf M.field.toSubgroup) :=
    FiniteIntermediateField.finite_extension_of_le M.below hPM
  change relativeNorm A K.field S hSK u.1 ∈
    (relativeNorm A K.field M.field M.below).range
  refine ⟨relativeNorm A M.field P hPM ε.1, ?_⟩
  let TMP : FiniteTower G :=
    { top := P
      middle := M.field
      base := K.field
      top_le_middle := hPM
      middle_le_base := M.below
      finiteTopQuotient := hPMfinite
      finiteBaseQuotient := hMfinite }
  let TSP : FiniteTower G :=
    { top := P
      middle := S
      base := K.field
      top_le_middle := hPS
      middle_le_base := hSK
      finiteTopQuotient := hPSfinite
      finiteBaseQuotient := hSfinite }
  calc
    relativeNorm A K.field M.field M.below
        (relativeNorm A M.field P hPM ε.1) =
        relativeNorm A K.field P hPK ε.1 :=
      TMP.norm_trans_apply A ε.1
    _ = relativeNorm A K.field S hSK
        (relativeNorm A S P hPS ε.1) :=
      (TSP.norm_trans_apply A ε.1).symm
    _ = relativeNorm A K.field S hSK u.1 := congrArg _ hε

end DegreeData

end

end Atlas.Knowledge
