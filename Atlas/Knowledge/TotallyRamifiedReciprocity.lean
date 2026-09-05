import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.ChosenPrimeElement
import Atlas.Knowledge.ClassFieldAxiom
import Atlas.Knowledge.CyclicTotallyRamifiedFixedSource
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractExtension
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteAbstractFieldExtension
import Atlas.Knowledge.FiniteCyclicSubextension
import Atlas.Knowledge.FiniteExtensionTransitivity
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FiniteReciprocityHom
import Atlas.Knowledge.FiniteResidueAbstractField
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusExponent
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.IntermediateGaloisCorrespondence
import Atlas.Knowledge.PrimeElement
import Atlas.Knowledge.ReciprocityMap
import Atlas.Knowledge.ReciprocityReductionArithmetic
import Atlas.Knowledge.ReductionGaloisArrows
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.TotallyRamifiedFixedSource
import Atlas.Knowledge.TotallyRamifiedFrobeniusLift
import Atlas.Knowledge.TotallyRamifiedRestrictionEquiv
import Atlas.Knowledge.UnitCohomologyAxiom
import Atlas.Knowledge.ValuationData

/-!
# totally ramified reciprocity

Exponent vanishing, injectivity, and finally bijectivity of finite
reciprocity in the cyclic totally ramified case, derived from the
constructed fixed source: the exponent in the chosen cyclic
decomposition is zero, the reciprocity homomorphism of the finite
reciprocity equivalence has trivial kernel, and the class-field-axiom
order equality upgrades that to bijectivity (#104).

## Main statements

* `ValuationData.abstractReciprocity_cyclicTotallyRamified_finiteReciprocityHom_bijective`
  — the cyclic totally ramified instance of the abstract reciprocity
  theorem; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
`FiniteGaloisSubextension.finite_extension_trans` is the layer's
top-level `finite_extension_trans`, `extensionSubgroup_index_eq_degree`
is `subgroup_index_eq_degree`, and
`DegreeData.FiniteAbstractExtension.ofInclusion` is the top-level
`FiniteAbstractExtension.ofInclusion`. The ambient group sits in one
`{G : Type u}` scope, universe-polymorphic since the #104 hoist — every
declaration consumes `Atlas.Knowledge.DegreeData.finiteReciprocityHom`
or the fixed-source theorem, both flipped with it. All three
declarations shed the source's `[T2Space G]` (the continuing cascade)
and keep `[TotallyDisconnectedSpace G]`, which the fixed-source chain
consumes. `L` rebundles as the structure literal over `E.field`,
matching the fixed-source statement's spelling (the recurrence the #194
review recorded). One proof step departs: the generator-restriction
bridge in the injectivity proof closes by `rw` and `exact` where the
source's `calc` fails its `Trans`-instance synthesis over the let-bound
quotient spellings. This completes the source's `TotallyRamifiedCase/`
directory.

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

/-- The exponent in the chosen cyclic decomposition is zero
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/Conclusion.lean:25`]
[Yamaguchi2026]). -/
theorem abstractReciprocity_cyclicTotallyRamified_exponent_eq_zero
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (E : FiniteCyclicSubextension K)
    (hTot : E.IsTotallyRamified D)
    (k : ℕ)
    (hk : k < (E.toFiniteAbstractExtension.degree : ℕ))
    (piSigma : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D)
        E.field E.below
        (D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
          (K.toFiniteResidueAbstractField D)
          E.toFiniteGaloisSubextension
          hTot
          E.galoisGenerator)))
    (piL : ambientFixedAddSubgroup A E.field) :
    let L : FiniteAbstractField G :=
      ⟨E.field, E.toFiniteAbstractFieldExtension.field.finite⟩
    let KR := K.toFiniteResidueAbstractField D
    letI : Finite
        ((baseField G).toSubgroup ⧸
          KR.field.toSubgroup.subgroupOf (baseField G).toSubgroup) := by
      change Finite
        ((baseField G).toSubgroup ⧸
          K.field.toSubgroup.subgroupOf (baseField G).toSubgroup)
      exact K.finite
    let LG := E.toFiniteGaloisSubextension
    letI : Finite
        (KR.field.toSubgroup ⧸
          LG.field.toSubgroup.subgroupOf KR.field.toSubgroup) :=
      LG.finite
    let q := E.galoisGenerator
    let hLGTot := hTot
    let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
      KR LG hLGTot q
    let Sigma := D.frobeniusFixedField KR LG.field LG.below σ
    let hSigmaK := D.frobeniusFixedField_le KR LG.field LG.below σ
    letI : Finite
        (K.field.toSubgroup ⧸
          Sigma.toSubgroup.subgroupOf K.field.toSubgroup) :=
      D.frobeniusFixedField_finite KR LG.field LG.below σ
    ∀ (w : v.unitAddSubgroup L)
      (_hpiL : v.IsPrimeElement L piL)
      (_hnorm :
        relativeNorm A K.field E.field E.below (k • piL + w.1) =
          relativeNorm A K.field Sigma hSigmaK (k • piSigma)),
      k = 0 := by
  dsimp only
  let L : FiniteAbstractField G :=
    ⟨E.field, E.toFiniteAbstractFieldExtension.field.finite⟩
  let KR := K.toFiniteResidueAbstractField D
  let LG := E.toFiniteGaloisSubextension
  letI hLGfinite : Finite
      (KR.field.toSubgroup ⧸
        LG.field.toSubgroup.subgroupOf KR.field.toSubgroup) :=
    LG.finite
  letI hLGfiniteOverK : Finite
      (K.field.toSubgroup ⧸
        LG.field.toSubgroup.subgroupOf K.field.toSubgroup) := by
    have h := hLGfinite
    change Finite
      (K.field.toSubgroup ⧸
        LG.field.toSubgroup.subgroupOf K.field.toSubgroup) at h
    exact h
  let q := E.galoisGenerator
  let hLGTot := hTot
  letI hKRabsolute : Finite ((baseField G).toSubgroup ⧸
      KR.field.toSubgroup.subgroupOf (baseField G).toSubgroup) := by
    change Finite ((baseField G).toSubgroup ⧸
      K.field.toSubgroup.subgroupOf (baseField G).toSubgroup)
    exact K.finite
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    KR LG hLGTot q
  let Sigma := D.frobeniusFixedField KR LG.field LG.below σ
  let hSigmaK := D.frobeniusFixedField_le KR LG.field LG.below σ
  letI hSigmaFinite : Finite
      (K.field.toSubgroup ⧸
        Sigma.toSubgroup.subgroupOf K.field.toSubgroup) :=
    D.frobeniusFixedField_finite KR LG.field LG.below σ
  intro w hpiL hnorm
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    KR LG hLGTot q
  letI hMfinite : Finite
      (KR.field.toSubgroup ⧸
        M.field.toSubgroup.subgroupOf KR.field.toSubgroup) :=
    M.finite
  let S := M.inertiaImage D
  let M₀ := M.maximalUnramifiedSubextension D
  let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
    M.field_le_intermediateField S
  let hM₀K : M₀.toSubgroup ≤ K.field.toSubgroup :=
    M.intermediateField_le_base S
  let N := M.lowerFiniteGalois S
  letI hNnormal : (M.field.toSubgroup.subgroupOf M₀.toSubgroup).Normal :=
    N.normal
  letI hNfinite : Finite
      (M₀.toSubgroup ⧸ M.field.toSubgroup.subgroupOf M₀.toSubgroup) :=
    N.finite
  letI hM₀finite : Finite
      (K.field.toSubgroup ⧸ M₀.toSubgroup.subgroupOf K.field.toSubgroup) :=
    M.intermediateField_finite S
  letI hM₀absolute : Finite ((baseField G).toSubgroup ⧸
      M₀.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    finite_extension_trans hM₀K (le_baseField K.field)
  letI hMabsolute : Finite ((baseField G).toSubgroup ⧸
      M.field.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    finite_extension_trans M.below (le_baseField K.field)
  let MF : FiniteAbstractField G := ⟨M.field, hMabsolute⟩
  let M₀F : FiniteAbstractField G := ⟨M₀, hM₀absolute⟩
  let EN : FiniteAbstractFieldExtension G :=
    { field := MF
      base := M₀F
      below := hMM₀
      finiteQuotient := hNfinite }
  obtain ⟨x, hx⟩ :=
    v.abstractReciprocity_cyclicTotallyRamified_fixedSource hcf
      K E hTot k piSigma piL w hpiL hnorm
  have hkLower : k < (N.toFiniteAbstractExtension.degree : ℕ) := by
    rw [D.abstractReciprocityTotallyRamifiedLowerDegree_eq
      KR LG hLGTot q]
    exact hk
  exact abstractReciprocity_totallyRamified_valuation_forces_exponent_zero
    v EN (by
      simpa [EN, FiniteAbstractFieldExtension.IsTotallyRamified,
        FiniteAbstractFieldExtension.toFiniteAbstractExtension] using
          M.maximalUnramifiedSubextension_isTotallyRamified D)
      k hkLower x hx

/-- In the cyclic totally ramified case, the reciprocity homomorphism
of the finite reciprocity equivalence has trivial kernel — the final
kernel calculation ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/Conclusion.lean:154`]
[Yamaguchi2026]). -/
theorem abstractReciprocity_cyclicTotallyRamified_finiteReciprocityHom_injective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G)
    (E : FiniteCyclicSubextension K)
    (hTot : E.IsTotallyRamified D) :
    Function.Injective
      (D.finiteReciprocityHom A v hAxiom K E.field E.below) := by
  let L : FiniteAbstractField G :=
    ⟨E.field, E.toFiniteAbstractFieldExtension.field.finite⟩
  let KR := K.toFiniteResidueAbstractField D
  let LG := E.toFiniteGaloisSubextension
  letI hLGfinite : Finite
      (KR.field.toSubgroup ⧸
        LG.field.toSubgroup.subgroupOf KR.field.toSubgroup) :=
    LG.finite
  letI hLGfiniteOverK : Finite
      (K.field.toSubgroup ⧸
        LG.field.toSubgroup.subgroupOf K.field.toSubgroup) := by
    have h := hLGfinite
    change Finite
      (K.field.toSubgroup ⧸
        LG.field.toSubgroup.subgroupOf K.field.toSubgroup) at h
    exact h
  let q := E.galoisGenerator
  let qRaw := E.generator
  let hLGTot := hTot
  letI hKRabsolute : Finite ((baseField G).toSubgroup ⧸
      KR.field.toSubgroup.subgroupOf (baseField G).toSubgroup) := by
    change Finite ((baseField G).toSubgroup ⧸
      K.field.toSubgroup.subgroupOf (baseField G).toSubgroup)
    exact K.finite
  let Q := K.field.toSubgroup ⧸
    E.field.toSubgroup.subgroupOf K.field.toSubgroup
  let EF := E.toFiniteAbstractExtension
  letI hQFintype : Fintype Q := Fintype.ofFinite _
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    KR LG hLGTot q
  let Sigma := D.frobeniusFixedField KR LG.field LG.below σ
  let hSigmaK := D.frobeniusFixedField_le KR LG.field LG.below σ
  letI hSigmaFinite : Finite
      (K.field.toSubgroup ⧸
        Sigma.toSubgroup.subgroupOf K.field.toSubgroup) :=
    D.frobeniusFixedField_finite KR LG.field LG.below σ
  letI hSigmaAbsolute : Finite ((baseField G).toSubgroup ⧸
      Sigma.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    D.frobeniusFixedField_absoluteFinite K LG.field LG.below σ
  let SigmaF : FiniteAbstractField G := ⟨Sigma, hSigmaAbsolute⟩
  let piSigma : ambientFixedAddSubgroup A Sigma := v.chosenPrimeElement SigmaF
  let piL : ambientFixedAddSubgroup A E.field := v.chosenPrimeElement L
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨i, hi, _⟩ :=
    IsCyclic.unique_zpow_zmod (a := qRaw) E.generates x.toMul
  let k : ℕ := i.val
  have hcard : Fintype.card Q = (EF.degree : ℕ) := by
    calc
      Fintype.card Q = Nat.card Q := by
        rw [Nat.card_eq_fintype_card]
      _ = (E.field.toSubgroup.subgroupOf K.field.toSubgroup).index :=
        (Subgroup.index_eq_card
          (E.field.toSubgroup.subgroupOf K.field.toSubgroup)).symm
      _ = (EF.degree : ℕ) :=
        EF.subgroup_index_eq_degree
  have hk : k < (EF.degree : ℕ) := by
    rw [← hcard]
    exact i.val_lt
  have hxrepr : x = k • Additive.ofMul qRaw := by
    apply Additive.toMul.injective
    change x.toMul = qRaw ^ k
    exact hi
  rw [hxrepr, map_nsmul,
    D.finiteReciprocityHom_apply_eq_primeNormClass
      A v hAxiom K E.field E.below (Additive.ofMul qRaw) σ
      (by
        change D.frobeniusRestriction KR LG.field LG.below σ = qRaw
        rw [D.frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified_underlying
          KR LG hLGTot q]
        exact
          E.toFiniteGaloisSubextension.extensionQuotientMulEquiv.apply_symm_apply
          E.generator)
      piSigma (v.chosenPrimeElement_isPrime SigmaF)] at hx
  have hclass :
      finiteNormClass A K.field E.field E.below
          (relativeNorm A K.field Sigma hSigmaK (k • piSigma)) = 0 := by
    have hx' := hx
    change k • finiteNormClass A K.field E.field E.below
        (relativeNorm A K.field Sigma hSigmaK piSigma) = 0 at hx'
    rw [map_nsmul, finiteNormClass_nsmul]
    exact hx'
  have hSigmaResidue :
      ((FiniteAbstractExtension.ofInclusion
        Sigma K.field hSigmaK).residueDegree D : ℕ) = 1 := by
    calc
      ((FiniteAbstractExtension.ofInclusion
          Sigma K.field hSigmaK).residueDegree D : ℕ) =
          D.frobeniusExponent KR LG.field LG.below σ :=
        D.frobeniusFixedField_residueDegreeOverBase KR LG.field LG.below σ
      _ = 1 :=
        D.frobeniusExponent_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
          KR LG hLGTot q
  obtain ⟨w, hnorm⟩ :=
    v.primeNormClass_eq_zero_exists_unit_norm_eq
      K L SigmaF E.below hSigmaK hTot hSigmaResidue
      k piSigma piL (v.chosenPrimeElement_isPrime SigmaF)
      (v.chosenPrimeElement_isPrime L) hclass
  have hkzero := v.abstractReciprocity_cyclicTotallyRamified_exponent_eq_zero
    hcf K E hTot k hk piSigma piL
      w (v.chosenPrimeElement_isPrime L) hnorm
  rw [hxrepr, hkzero, zero_nsmul]

/-- **The cyclic totally ramified instance of the abstract reciprocity
theorem** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/Conclusion.lean:273`]
[Yamaguchi2026]). -/
theorem abstractReciprocity_cyclicTotallyRamified_finiteReciprocityHom_bijective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G)
    (E : FiniteCyclicSubextension K)
    (hTot : E.IsTotallyRamified D) :
    Function.Bijective
      (D.finiteReciprocityHom A v hAxiom K E.field E.below) := by
  let EF := E.toFiniteAbstractExtension
  letI hEbaseAbsolute : Finite ((baseField G).toSubgroup ⧸
      EF.base.toSubgroup.subgroupOf (baseField G).toSubgroup) := by
    simpa [EF, FiniteCyclicSubextension.toFiniteAbstractExtension] using
      K.finite
  letI : Finite (FiniteNormQuotient A K.field E.field E.below) :=
    finiteNormQuotient_finite_of_classFieldAxiom
      A hcf EF E.normal E.generator E.generates
  apply (Nat.bijective_iff_injective_and_card
    (D.finiteReciprocityHom A v hAxiom K E.field E.below)).2
  exact ⟨v.abstractReciprocity_cyclicTotallyRamified_finiteReciprocityHom_injective
      hcf hAxiom K E hTot,
    cyclicReciprocity_card_equality
      A hcf EF E.normal E.generator E.generates⟩

end ValuationData

end

end Atlas.Knowledge
