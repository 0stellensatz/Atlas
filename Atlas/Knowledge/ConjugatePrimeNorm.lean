import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteFieldUnitMaps
import Atlas.Knowledge.FiniteResidueAbstractField
import Atlas.Knowledge.FrobeniusActionRemainder
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.NormalizedValuationLaws
import Atlas.Knowledge.PrimeElement
import Atlas.Knowledge.ReciprocityMap
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.RelativeNormConjugation
import Atlas.Knowledge.RelativeNormLaws
import Atlas.Knowledge.ValuationData

/-!
# Conjugate prime norm

Prime elements transport across Frobenius-action conjugation: the
conjugate fixed field takes the conjugated prime, primality survives by
the conjugation compatibility of normalized valuations, and the two
relative norms agree in the base fixed field because the conjugating
representative already lies in `G_K` (#104).

## Main statements

* `DegreeData.exists_primeElement_frobeniusActionConjugate_norm_eq` —
  the conjugated prime with equal norm; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling, the
two enrichment bridges (`hLnormalKR`, `hLfiniteKR`) are plain
definitionally-equal terms for the source's `simpa` bridges — the
recorded trap — the signature's Frobenius binders synthesize across the
enrichment through the transport instances of
`Atlas.Knowledge.FiniteFieldUnitMaps`, and the ambient group is `Type`
after the chain. The two fixed-field containments carry explicit
`K.field` ascriptions, the conjugate-fixed-field bridge is the plain
definitionally-equal term for the source's `simpa`, and the conjugate
extension's finiteness is #137's containment-free form. The dead
Hausdorff binder goes. The
citations name this file by bare basename; it lives at
`AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/`
in the source, whose full path exceeds the line budget. The source's
no-op opens go.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **The prime for the conjugate Frobenius fixed field may be chosen as
the conjugate of a prime in the original fixed field, with equal norms
in `A_K`**: conjugation compatibility of normalized valuations preserves
primality, and conjugation equivariance of the relative norm with the
representative lying in `G_K` equates the norms
([Yamaguchi 2026, `ConjugatePrimeNorm.lean:36`]
[Yamaguchi2026]). -/
theorem exists_primeElement_frobeniusActionConjugate_norm_eq
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (φ σ : D.FrobeniusElements
      (K.toFiniteResidueAbstractField D) L hLK) (m : ℕ)
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ))
    (hπ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ,
          D.frobeniusFixedField_absoluteFinite K L hLK σ⟩
      v.IsPrimeElement Sigma π) :
    let KR := K.toFiniteResidueAbstractField D
    let σ' := D.frobeniusActionConjugate KR L hLK φ σ m
    let S := D.frobeniusFixedField KR L hLK σ
    let S' := D.frobeniusFixedField KR L hLK σ'
    let hSK := D.frobeniusFixedField_le KR L hLK σ
    let hS'K := D.frobeniusFixedField_le KR L hLK σ'
    letI : Finite (K.field.toSubgroup ⧸ S.toSubgroup.subgroupOf K.field.toSubgroup) :=
      D.frobeniusFixedField_finite KR L hLK σ
    letI : Finite (K.field.toSubgroup ⧸ S'.toSubgroup.subgroupOf K.field.toSubgroup) :=
      D.frobeniusFixedField_finite KR L hLK σ'
    let Sigma' : FiniteAbstractField G :=
      ⟨S', D.frobeniusFixedField_absoluteFinite K L hLK σ'⟩
    ∃ π' : ambientFixedAddSubgroup A S',
      v.IsPrimeElement Sigma' π' ∧
        relativeNorm A K.field S' hS'K π' =
          relativeNorm A K.field S hSK π := by
  dsimp only
  let KR := K.toFiniteResidueAbstractField D
  letI hLnormalKR : (L.toSubgroup.subgroupOf KR.field.toSubgroup).Normal :=
    hLnormal
  letI hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸ L.toSubgroup.subgroupOf KR.field.toSubgroup) :=
    hLfinite
  let σ' := D.frobeniusActionConjugate KR L hLK φ σ m
  let S := D.frobeniusFixedField KR L hLK σ
  let S' := D.frobeniusFixedField KR L hLK σ'
  let hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le KR L hLK σ
  let hS'K : S'.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le KR L hLK σ'
  letI hSfinite : Finite
      (K.field.toSubgroup ⧸ S.toSubgroup.subgroupOf K.field.toSubgroup) :=
    D.frobeniusFixedField_finite KR L hLK σ
  letI hS'finite : Finite
      (K.field.toSubgroup ⧸ S'.toSubgroup.subgroupOf K.field.toSubgroup) :=
    D.frobeniusFixedField_finite KR L hLK σ'
  letI hSabsolute : Finite ((baseField G).toSubgroup ⧸
      S.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ
  letI hS'absolute : Finite ((baseField G).toSubgroup ⧸
      S'.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ'
  let Sigma : FiniteAbstractField G := ⟨S, hSabsolute⟩
  let Sigma' : FiniteAbstractField G := ⟨S', hS'absolute⟩
  let q := φ.1 ^ m
  let k : K.field.toSubgroup := Quotient.out q
  let s : G := k.1⁻¹
  let C := conjugateClosedSubgroup S s
  let Kc := conjugateClosedSubgroup K.field s
  let hCS := conjugateClosedSubgroup_mono hSK s
  have hC : C = S' :=
    D.conjugate_frobeniusFixedField_actionConjugate KR L hLK φ σ m
  have hKc : Kc = K.field := by
    ext x
    change x ∈ conjugateClosedSubgroup K.field s ↔ x ∈ K.field
    rw [conjugateClosedSubgroup_mem]
    constructor
    · intro hx
      change x ∈ K.field.toSubgroup
      simpa [s, mul_assoc] using K.field.toSubgroup.mul_mem
        (K.field.toSubgroup.mul_mem k.2 hx) (K.field.toSubgroup.inv_mem k.2)
    · intro hx
      change s * x * s⁻¹ ∈ K.field.toSubgroup
      simpa [s] using K.field.toSubgroup.mul_mem
        (K.field.toSubgroup.mul_mem (K.field.toSubgroup.inv_mem k.2) hx) k.2
  letI hCabsolute : Finite ((baseField G).toSubgroup ⧸
      C.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    Finite.of_equiv
      ((baseField G).toSubgroup ⧸
        S.toSubgroup.subgroupOf (baseField G).toSubgroup)
      (by
        simpa [C, baseField] using
          (absoluteConjugateCosetEquiv S s).symm)
  let SigmaC : FiniteAbstractField G := Sigma.conjugate s
  let πC : ambientFixedAddSubgroup A C :=
    conjugateFixedElement A S s π
  let π' : ambientFixedAddSubgroup A S' :=
    ⟨πC.1, by rw [← hC]; exact πC.2⟩
  have hπC : v.IsPrimeElement SigmaC πC := by
    rw [ValuationData.IsPrimeElement] at hπ ⊢
    have hconj : v.valuationAt SigmaC πC = v.valuationAt Sigma π := by
      simpa [C, SigmaC, Sigma, πC] using
        v.normalizedValuation_conjugate Sigma s π
    exact hconj.trans hπ
  have hπ' : v.IsPrimeElement Sigma' π' := by
    rw [ValuationData.IsPrimeElement] at hπC ⊢
    have valuation_transport
        (C₀ S₀ : FiniteAbstractField G)
        (h : C₀.field = S₀.field)
        (aC : ambientFixedAddSubgroup A C₀.field)
        (aS : ambientFixedAddSubgroup A S₀.field)
        (ha : aC.1 = aS.1) :
        v.valuationAt S₀ aS = v.valuationAt C₀ aC := by
      cases C₀ with
      | mk C₀ hC₀ =>
          cases S₀ with
          | mk S₀ hS₀ =>
              dsimp only at h
              subst S₀
              congr 1
              exact Subtype.ext ha.symm
    have hSigmaField : SigmaC.field = Sigma'.field := by
      change C = S'
      exact hC
    have hv : v.valuationAt Sigma' π' = v.valuationAt SigmaC πC :=
      valuation_transport SigmaC Sigma' hSigmaField πC π' rfl
    exact hv.trans hπC
  refine ⟨π', hπ', ?_⟩
  letI hCSfinite : Finite
      (Kc.toSubgroup ⧸ C.toSubgroup.subgroupOf Kc.toSubgroup) :=
    finite_conjugateExtension K.field S s
  have hnormC := relativeNorm_conjugate_apply A K.field S hSK s π
  apply Subtype.ext
  have relativeNorm_transport
      (K₀ K₁ L₀ L₁ : ClosedSubgroup G)
      (h₀ : L₀.toSubgroup ≤ K₀.toSubgroup)
      (h₁ : L₁.toSubgroup ≤ K₁.toSubgroup)
      [Finite (K₀.toSubgroup ⧸ L₀.toSubgroup.subgroupOf K₀.toSubgroup)]
      [Finite (K₁.toSubgroup ⧸ L₁.toSubgroup.subgroupOf K₁.toSubgroup)]
      (hK₀ : K₀ = K₁) (hL₀ : L₀ = L₁)
      (a₀ : ambientFixedAddSubgroup A L₀)
      (a₁ : ambientFixedAddSubgroup A L₁)
      (ha : a₀.1 = a₁.1) :
      ((relativeNorm A K₀ L₀ h₀ a₀ :
        ambientFixedAddSubgroup A K₀) : A.V) =
      ((relativeNorm A K₁ L₁ h₁ a₁ :
        ambientFixedAddSubgroup A K₁) : A.V) := by
    subst K₁
    subst L₁
    have ha' : a₀ = a₁ := Subtype.ext ha
    subst a₁
    rfl
  have hleft :
      ((relativeNorm A K.field S' hS'K π' :
        ambientFixedAddSubgroup A K.field) : A.V) =
      ((relativeNorm A Kc C hCS πC :
        ambientFixedAddSubgroup A Kc) : A.V) := by
    exact (relativeNorm_transport Kc K.field C S' hCS hS'K
      hKc hC πC π' rfl).symm
  calc
    ((relativeNorm A K.field S' hS'K π' :
        ambientFixedAddSubgroup A K.field) : A.V) =
        ((relativeNorm A Kc C hCS πC :
          ambientFixedAddSubgroup A Kc) : A.V) := hleft
    _ = ((conjugateFixedElement A K.field s
        (relativeNorm A K.field S hSK π) :
          ambientFixedAddSubgroup A Kc) : A.V) :=
      congrArg Subtype.val hnormC
    _ = ((relativeNorm A K.field S hSK π :
        ambientFixedAddSubgroup A K.field) : A.V) := by
      rw [conjugateFixedElement_coe]
      have hs : s⁻¹ = k.1 := by simp [s]
      rw [hs]
      change A.ρ k.1 (relativeNorm A K.field S hSK π).1 =
        (relativeNorm A K.field S hSK π).1
      exact (relativeNorm A K.field S hSK π).2 k

end DegreeData

end

end Atlas.Knowledge
