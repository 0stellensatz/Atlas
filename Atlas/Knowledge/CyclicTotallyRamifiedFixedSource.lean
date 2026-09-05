import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.ClassFieldAxiom
import Atlas.Knowledge.CyclicFixedCycleEquiv
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.ElementFixedAddSubgroup
import Atlas.Knowledge.ExtensionFixedRepresentation
import Atlas.Knowledge.ExtensionFixedRepresentationEquiv
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteAbstractFieldExtension
import Atlas.Knowledge.FiniteCyclicSubextension
import Atlas.Knowledge.FiniteExtensionTransitivity
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.FiniteResidueAbstractField
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.IntermediateGaloisCorrespondence
import Atlas.Knowledge.PrimeElement
import Atlas.Knowledge.ProfiniteInteger
import Atlas.Knowledge.ReductionGaloisArrows
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.TotallyRamifiedFrobeniusLift
import Atlas.Knowledge.TotallyRamifiedFixedSource
import Atlas.Knowledge.TotallyRamifiedFrobeniusNorms
import Atlas.Knowledge.TotallyRamifiedRestrictionEquiv
import Atlas.Knowledge.UnitRepresentation
import Atlas.Knowledge.ValuationData

/-!
# cyclic totally ramified fixed source

The fixed source in the totally ramified reciprocity argument: a finite
cyclic extension converts to the canonical finite Galois boundary, and
the complete source-producing fixed-element calculation runs — all
fields, restriction maps, norm identities, and action identities
constructed from the original data, none exposed as a hypothesis — to
yield an element of `A_{M₀}` whose inclusion has normalized valuation
exactly `k` (#104).

## Main definitions

* `FiniteCyclicSubextension.toFiniteGaloisSubextension` — forget only
  the chosen cyclic generator.

## Main statements

* `ValuationData.abstractReciprocity_cyclicTotallyRamified_fixedSource`
  — the complete source-producing calculation; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
`ZHat` is `ProfiniteInteger`, and
`FiniteGaloisSubextension.finite_extension_trans` and
`finite_extension_over_intermediate` are the layer's top-level forms.
One `noncomputable section` holds everything at `Type u` since the #104
hoist flipped the class-formation stock: the commuting-combination
lemma (widened to `Type*` in its own group, like its private sibling in
`Atlas.Knowledge.TotallyRamifiedFixedSource`), the action-transport
lemma, the `FiniteCyclicSubextension` trio, and then the fixed-source
theorem, whose fixed vector enters
`Atlas.Knowledge.cyclicFixedCycleEquiv` through the elementwise
`Atlas.Knowledge.elementFixedAddSubgroup`, clear of the one-universe
`{k G : Type u}` block of Mathlib's `Rep.FiniteCyclicGroup`. That
theorem sheds the source's `[T2Space G]` (the continuing cascade) and
keeps `[TotallyDisconnectedSpace G]`, which the norm restriction over
the Frobenius fixed field consumes. Two proof-level adjustments answer
the layer's transparency: `L` rebundles as the structure literal over
`E.field` (the layer's `toFiniteAbstractFieldExtension` routes through
`ofInclusion`, whose projections do not reduce reducibly, which blocked
the source's defeq elaboration of the prime-unit sum), and the one simp
step that mixes the `K.field`/`KR.field` spellings past the
simplifier's instances-transparency check — the nsmul bridge in the
Frobenius-fixes-`Σ` calculation — closes by direct `exact`. Everything
else ports token-for-token; the file is the source's
`TotallyRamifiedCase/FixedSource.lean` whole.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- If two commuting group elements act compatibly on a coboundary, the
standard corrected combination is fixed by the first element
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FixedSource.lean:23`]
[Yamaguchi2026]). -/
theorem abstractReciprocity_fixedCombination_of_commute
    {Q : Type*} [Group Q] (B : Rep ℤ Q)
    (g t : Q) (hcomm : Commute g t) (c b a : B.V)
    (htc : B.ρ t c = c)
    (hgb : B.ρ g b = B.ρ t b)
    (hbc : b - c = B.ρ g a - a) :
    B.ρ g (b + a - B.ρ t a) = b + a - B.ρ t a := by
  have hcommAction : B.ρ g (B.ρ t a) = B.ρ t (B.ρ g a) := by
    calc
      B.ρ g (B.ρ t a) = B.ρ (g * t) a := by
        rw [map_mul]
        rfl
      _ = B.ρ (t * g) a := by rw [hcomm.eq]
      _ = B.ρ t (B.ρ g a) := by
        rw [map_mul]
        rfl
  have hb : b = c + B.ρ g a - a := by
    calc
      b = (b - c) + c := by abel
      _ = (B.ρ g a - a) + c := by rw [hbc]
      _ = c + B.ρ g a - a := by abel
  have htbc := congrArg (fun z : B.V ↦ B.ρ t z) hbc
  have htbc' : B.ρ t b - c = B.ρ t (B.ρ g a) - B.ρ t a := by
    simpa only [map_sub, htc] using htbc
  have htb : B.ρ t b = c + B.ρ t (B.ρ g a) - B.ρ t a := by
    calc
      B.ρ t b = (B.ρ t b - c) + c := by abel
      _ = (B.ρ t (B.ρ g a) - B.ρ t a) + c := by rw [htbc']
      _ = c + B.ρ t (B.ρ g a) - B.ρ t a := by abel
  calc
    B.ρ g (b + a - B.ρ t a) =
        B.ρ g b + B.ρ g a - B.ρ g (B.ρ t a) := by
      simp only [map_add, map_sub]
    _ = B.ρ t b + B.ρ g a - B.ρ t (B.ρ g a) := by
      rw [hgb, hcommAction]
    _ = c + B.ρ g a - B.ρ t a := by rw [htb]; abel
    _ = b + a - B.ρ t a := by rw [hb]; abel

namespace FiniteGaloisSubextension

/-- The lower inclusion homomorphism preserves the relative coset
action ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FixedSource.lean:63`]
[Yamaguchi2026]). -/
theorem relativeCosetAction_lowerInclusionHom
    (A : Rep ℤ G) [IsTopologicalGroup G] {K : ClosedSubgroup G}
    (M : FiniteGaloisSubextension K) (S : Subgroup M.extensionQuotient)
    (a : ambientFixedAddSubgroup A M.field)
    (g : (M.intermediateField S).toSubgroup ⧸
      M.field.toSubgroup.subgroupOf
        (M.intermediateField S).toSubgroup) :
    relativeCosetAction A (M.intermediateField S) M.field
        (M.field_le_intermediateField S) a g =
      relativeCosetAction A K M.field M.below a
        (M.lowerInclusionHom S g) := by
  refine Quotient.inductionOn' g ?_
  intro m
  rfl

end FiniteGaloisSubextension

namespace FiniteCyclicSubextension

variable {K : FiniteAbstractField G}

/-- **Forget only the chosen cyclic generator; the resulting finite
Galois bundle is the canonical input to the finite reciprocity
construction** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FixedSource.lean:83`]
[Yamaguchi2026]). -/
def toFiniteGaloisSubextension (E : FiniteCyclicSubextension K) :
    FiniteGaloisSubextension K.field where
  field := E.field
  below := E.below
  normal := E.normal
  finite := E.finite

/-- The cyclic generator transported across the finite Galois quotient
boundary ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FixedSource.lean:91`]
[Yamaguchi2026]). -/
def galoisGenerator (E : FiniteCyclicSubextension K) :
    E.toFiniteGaloisSubextension.extensionQuotient :=
  E.toFiniteGaloisSubextension.extensionQuotientMulEquiv.symm E.generator

/-- The transported generator still generates the whole finite Galois
quotient ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FixedSource.lean:96`]
[Yamaguchi2026]). -/
theorem galoisGenerator_generates (E : FiniteCyclicSubextension K) :
    ∀ x, x ∈ Subgroup.zpowers E.galoisGenerator := by
  intro x
  let e := E.toFiniteGaloisSubextension.extensionQuotientMulEquiv
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (E.generates (e x))
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨n, ?_⟩
  apply e.injective
  change e (e.symm E.generator ^ n) = e x
  rw [map_zpow, e.apply_symm_apply]
  exact hn

end FiniteCyclicSubextension

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- **The complete source-producing calculation in the cyclic totally
ramified case of the abstract reciprocity theorem.** All fields,
restriction maps, norm identities, and action identities are
constructed from the original data; none is exposed as a hypothesis
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FixedSource.lean:118`]
[Yamaguchi2026]). -/
theorem abstractReciprocity_cyclicTotallyRamified_fixedSource
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (E : FiniteCyclicSubextension K)
    (hTot : E.IsTotallyRamified D)
    (k : ℕ)
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
    let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      KR LG hLGTot q
    letI : Finite
        (KR.field.toSubgroup ⧸
          M.field.toSubgroup.subgroupOf KR.field.toSubgroup) :=
      M.finite
    letI : Finite ((baseField G).toSubgroup ⧸
        M.field.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
      finite_extension_trans M.below (le_baseField K.field)
    let MF : FiniteAbstractField G := ⟨M.field, inferInstance⟩
    let S := M.inertiaImage D
    let M₀ := M.maximalUnramifiedSubextension D
    let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
      M.field_le_intermediateField S
    ∃ x : ambientFixedAddSubgroup A M₀,
      ((v.valuationAt MF
        (fixedFieldInclusion A M₀ M.field hMM₀ x) :
          v.valueGroup) : ProfiniteInteger) =
        Int.castRingHom ProfiniteInteger (k : ℤ) := by
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
  let hq := E.galoisGenerator_generates
  let hLGTot := hTot
  letI hKRabsolute : Finite ((baseField G).toSubgroup ⧸
      KR.field.toSubgroup.subgroupOf (baseField G).toSubgroup) := by
    change Finite
      ((baseField G).toSubgroup ⧸
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
  letI hMabsolute : Finite ((baseField G).toSubgroup ⧸
      M.field.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    finite_extension_trans M.below (le_baseField K.field)
  let MF : FiniteAbstractField G := ⟨M.field, hMabsolute⟩
  let S := M.inertiaImage D
  let M₀ := M.maximalUnramifiedSubextension D
  let hML := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
    KR LG hLGTot q
  let hMSigma :=
    D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_sigma
      KR LG hLGTot q
  let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
    M.field_le_intermediateField S
  let hM₀K : M₀.toSubgroup ≤ K.field.toSubgroup :=
    M.intermediateField_le_base S
  let N := M.lowerFiniteGalois S
  letI hMnormal : (M.field.toSubgroup.subgroupOf K.field.toSubgroup).Normal :=
    M.normal
  letI hNnormal : (M.field.toSubgroup.subgroupOf M₀.toSubgroup).Normal :=
    N.normal
  letI hNfinite : Finite
      (M₀.toSubgroup ⧸ M.field.toSubgroup.subgroupOf M₀.toSubgroup) :=
    N.finite
  letI hMLfinite : Finite
      (E.field.toSubgroup ⧸ M.field.toSubgroup.subgroupOf E.field.toSubgroup) :=
    finite_extension_over_intermediate
      M.below E.below hML
  letI hM₀finite : Finite
      (K.field.toSubgroup ⧸ M₀.toSubgroup.subgroupOf K.field.toSubgroup) :=
    M.intermediateField_finite S
  letI hM₀absolute : Finite ((baseField G).toSubgroup ⧸
      M₀.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    finite_extension_trans hM₀K (le_baseField K.field)
  let M₀F : FiniteAbstractField G := ⟨M₀, hM₀absolute⟩
  let EN : FiniteAbstractFieldExtension G :=
    { field := MF
      base := M₀F
      below := hMM₀
      finiteQuotient := hNfinite }
  let EM : FiniteAbstractFieldExtension G :=
    { field := MF
      base := K
      below := M.below
      finiteQuotient := M.finite }
  let EML : FiniteAbstractFieldExtension G :=
    { field := MF
      base := L
      below := hML
      finiteQuotient := hMLfinite }
  have hUnramifiedML :
      EML.IsUnramified D := by
    change EML.toFiniteAbstractExtension.IsUnramified D
    rw [EML.toFiniteAbstractExtension.isUnramified_iff_inertia_le D]
    intro x hx
    apply
      D.maximalUnramifiedField_le_abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      KR LG hLGTot q
    exact hx
  let piSigmaM : ambientFixedAddSubgroup A M.field :=
    fixedFieldInclusion A Sigma M.field hMSigma piSigma
  let piLM : ambientFixedAddSubgroup A M.field :=
    fixedFieldInclusion A E.field M.field hML piL
  let wUnitM : v.unitAddSubgroup MF :=
    v.unitInclusion EML hUnramifiedML w
  let wM : ambientFixedAddSubgroup A M.field := wUnitM.1
  have hpiLM : v.IsPrimeElement MF piLM := by
    exact v.prime_of_unramified EML hUnramifiedML piL hpiL
  let cM : ambientFixedAddSubgroup A M.field := k • piSigmaM
  let bM : ambientFixedAddSubgroup A M.field := k • piLM + wM
  let uM : ambientFixedAddSubgroup A M.field := cM - k • piLM
  have hbM :
      bM = fixedFieldInclusion A E.field M.field hML (k • piL + w.1) := by
    apply Subtype.ext
    rfl
  have hcM :
      cM = fixedFieldInclusion A Sigma M.field hMSigma (k • piSigma) := by
    apply Subtype.ext
    rfl
  have hNormL :
      relativeNorm A M₀ M.field hMM₀
          (fixedFieldInclusion A E.field M.field hML (k • piL + w.1)) =
        fixedFieldInclusion A K.field M₀ hM₀K
          (relativeNorm A K.field E.field E.below (k • piL + w.1)) := by
    have h :=
      D.abstractReciprocity_totallyRamified_relativeNorm_L
        A KR LG hLGTot q (k • piL + w.1)
    change
      relativeNorm A M₀ M.field hMM₀
          (fixedFieldInclusion A E.field M.field hML (k • piL + w.1)) =
        fixedFieldInclusion A K.field M₀ hM₀K
          (relativeNorm A K.field E.field E.below (k • piL + w.1)) at h
    exact h
  have hNormSigma :
      relativeNorm A M₀ M.field hMM₀
          (fixedFieldInclusion A Sigma M.field hMSigma (k • piSigma)) =
        fixedFieldInclusion A K.field M₀ hM₀K
          (relativeNorm A K.field Sigma hSigmaK (k • piSigma)) := by
    have h :=
      D.abstractReciprocity_totallyRamified_relativeNorm_sigma
        A KR LG hLGTot q (k • piSigma)
    change
      relativeNorm A M₀ M.field hMM₀
          (fixedFieldInclusion A Sigma M.field hMSigma (k • piSigma)) =
        fixedFieldInclusion A K.field M₀ hM₀K
          (relativeNorm A K.field Sigma hSigmaK (k • piSigma)) at h
    exact h
  have hNormBC : relativeNorm A M₀ M.field hMM₀ bM =
      relativeNorm A M₀ M.field hMM₀ cM := by
    calc
      relativeNorm A M₀ M.field hMM₀ bM =
          relativeNorm A M₀ M.field hMM₀
            (fixedFieldInclusion A E.field M.field hML
              (k • piL + w.1)) := congrArg _ hbM
      _ =
          fixedFieldInclusion A K.field M₀ hM₀K
            (relativeNorm A K.field E.field E.below (k • piL + w.1)) :=
        hNormL
      _ = fixedFieldInclusion A K.field M₀ hM₀K
          (relativeNorm A K.field Sigma hSigmaK (k • piSigma)) := by
        exact congrArg
          (fixedFieldInclusion A K.field M₀ hM₀K) hnorm
      _ = relativeNorm A M₀ M.field hMM₀
          (fixedFieldInclusion A Sigma M.field hMSigma (k • piSigma)) :=
        hNormSigma.symm
      _ = relativeNorm A M₀ M.field hMM₀ cM :=
        congrArg _ hcM.symm
  have hnormWU : relativeNorm A M₀ M.field hMM₀ wM =
      relativeNorm A M₀ M.field hMM₀ uM := by
    dsimp only [bM, cM, uM] at hNormBC ⊢
    rw [map_add, map_nsmul, map_nsmul] at hNormBC
    rw [map_sub, map_nsmul, map_nsmul]
    exact eq_sub_of_add_eq' hNormBC
  let g := D.abstractReciprocityTotallyRamifiedLowerGenerator
    KR LG hLGTot q
  have hg : ∀ x, x ∈ Subgroup.zpowers g :=
    D.abstractReciprocityTotallyRamifiedLowerGenerator_generates
      KR LG hLGTot q hq
  letI hNFintype : Fintype N.extensionQuotient := Fintype.ofFinite _
  letI hNCyclic : IsCyclic N.extensionQuotient := by
    rw [isCyclic_iff_exists_zpowers_eq_top]
    refine ⟨g, ?_⟩
    ext x
    constructor
    · intro _
      exact Subgroup.mem_top x
    · intro _
      exact hg x
  letI hNcomm : CommGroup N.extensionQuotient := IsCyclic.commGroup
  obtain ⟨aN, haN⟩ :=
    abstractReciprocity_exists_hMinusOne_primitive hcf
      EN N.normal g hg uM wM hnormWU
  let B := extensionFixedRepresentation A K.field M.field M.below M.normal
  let B₀ := extensionFixedRepresentation A M₀ M.field hMM₀ N.normal
  let eB := extensionFixedRepresentationEquiv A K.field M.field M.below
    M.normal
  let eB₀ := extensionFixedRepresentationEquiv A M₀ M.field hMM₀ N.normal
  let gB := M.extensionQuotientMulEquiv (M.lowerInclusionHom S g)
  let tB := M.extensionQuotientMulEquiv
    (D.abstractReciprocityTotallyRamifiedFrobeniusInM
      KR LG hLGTot q)
  let aB : B.V := eB.symm (eB₀ aN)
  let bB : B.V := eB.symm bM
  let cB : B.V := eB.symm cM
  have haNLocal :
      B₀.ρ g aN - aN = eB₀.symm (wM - uM) := by
    have h := haN
    change B₀.ρ g aN - aN = eB₀.symm (wM - uM) at h
    exact h
  have hActionPrimitive : eB (B.ρ gB aB) = eB₀ (B₀.ρ g aN) := by
    apply Subtype.ext
    calc
      (eB (B.ρ gB aB)).1 =
          relativeCosetAction A K.field M.field M.below (eB aB) gB :=
        extensionFixedRepresentation_action_coe
          A K.field M.field M.below M.normal gB aB
      _ = relativeCosetAction A M₀ M.field hMM₀ (eB₀ aN) g := by
        exact (M.relativeCosetAction_lowerInclusionHom A S (eB₀ aN) g).symm
      _ = (eB₀ (B₀.ρ g aN)).1 := by
        exact (extensionFixedRepresentation_action_coe
          A M₀ M.field hMM₀ N.normal g aN).symm
  have hprimitiveB : B.ρ gB aB - aB = eB.symm (wM - uM) := by
    apply eB.injective
    calc
      eB (B.ρ gB aB - aB) =
          eB₀ (B₀.ρ g aN) - eB₀ aN := by
        rw [map_sub, hActionPrimitive]
        simp [aB]
      _ = eB₀ (B₀.ρ g aN - aN) := by
        rw [map_sub]
      _ = eB₀ (eB₀.symm (wM - uM)) :=
        congrArg eB₀ haNLocal
      _ = wM - uM := eB₀.apply_symm_apply _
      _ = eB (eB.symm (wM - uM)) :=
        (eB.apply_symm_apply _).symm
  have hbc : bB - cB = B.ρ gB aB - aB := by
    rw [hprimitiveB]
    apply eB.injective
    dsimp only [bB, cB]
    simp only [map_sub, AddEquiv.apply_symm_apply]
    dsimp only [bM, cM, uM]
    abel
  have htc : B.ρ tB cB = cB := by
    apply eB.injective
    apply Subtype.ext
    calc
      (eB (B.ρ tB cB)).1 =
          relativeCosetAction A K.field M.field M.below cM tB :=
        extensionFixedRepresentation_action_coe
          A K.field M.field M.below M.normal tB cB
      _ = cM.1 := by
        dsimp only [cM]
        have hActionNsmul :
            relativeCosetAction A K.field M.field M.below
                (k • piSigmaM) tB =
              k • relativeCosetAction A K.field M.field M.below
                piSigmaM tB := by
          refine Quotient.inductionOn' tB ?_
          intro t
          exact map_nsmul (A.ρ t.1) k piSigmaM.1
        rw [hActionNsmul]
        congr 1
        have h :=
          D.abstractReciprocityTotallyRamified_frobenius_fixes_sigma
            A KR LG hLGTot q piSigma
        change
          relativeCosetAction A K.field M.field M.below
              (fixedFieldInclusion A Sigma M.field hMSigma piSigma) tB =
            (fixedFieldInclusion A Sigma M.field hMSigma piSigma).1 at h
        simpa [piSigmaM] using h
      _ = (eB cB).1 := rfl
  have hgb : B.ρ gB bB = B.ρ tB bB := by
    apply eB.injective
    apply Subtype.ext
    calc
      (eB (B.ρ gB bB)).1 =
          relativeCosetAction A K.field M.field M.below bM gB :=
        extensionFixedRepresentation_action_coe
          A K.field M.field M.below M.normal gB bB
      _ = relativeCosetAction A K.field M.field M.below bM tB := by
        have h :=
          D.abstractReciprocityTotallyRamified_actions_agree_on_L
            A KR LG hLGTot q (k • piL + w.1)
        change
          relativeCosetAction A K.field M.field M.below
              (fixedFieldInclusion A E.field M.field hML
                (k • piL + w.1)) gB =
            relativeCosetAction A K.field M.field M.below
              (fixedFieldInclusion A E.field M.field hML
                (k • piL + w.1)) tB at h
        rw [hbM]
        exact h
      _ = (eB (B.ρ tB bB)).1 := by
        exact (extensionFixedRepresentation_action_coe
          A K.field M.field M.below M.normal tB bB).symm
  have hcomm : Commute gB tB :=
    (D.abstractReciprocityTotallyRamified_generator_commutes_frobenius
      KR LG hLGTot q).map M.extensionQuotientMulEquiv.toMonoidHom
  let xB : B.V := bB + aB - B.ρ tB aB
  have hxB : B.ρ gB xB = xB :=
    abstractReciprocity_fixedCombination_of_commute
      B gB tB hcomm cB bB aB htc hgb hbc
  let xB₀ : B₀.V := eB₀.symm (eB xB)
  have hActionX : eB₀ (B₀.ρ g xB₀) = eB (B.ρ gB xB) := by
    apply Subtype.ext
    calc
      (eB₀ (B₀.ρ g xB₀)).1 =
          relativeCosetAction A M₀ M.field hMM₀ (eB₀ xB₀) g :=
        extensionFixedRepresentation_action_coe
          A M₀ M.field hMM₀ N.normal g xB₀
      _ = relativeCosetAction A K.field M.field M.below (eB xB) gB :=
        M.relativeCosetAction_lowerInclusionHom A S (eB xB) g
      _ = (eB (B.ρ gB xB)).1 := by
        exact (extensionFixedRepresentation_action_coe
          A K.field M.field M.below M.normal gB xB).symm
  have hxB₀ : B₀.ρ g xB₀ = xB₀ := by
    apply eB₀.injective
    rw [hActionX, hxB]
    rfl
  let xCycle : elementFixedAddSubgroup B₀ g := ⟨xB₀, hxB₀⟩
  let x : ambientFixedAddSubgroup A M₀ :=
    (cyclicFixedCycleEquiv A M₀ M.field hMM₀
      N.normal g hg).symm xCycle
  refine ⟨x, ?_⟩
  have hxFormula : fixedFieldInclusion A M₀ M.field hMM₀ x = eB xB := by
    apply Subtype.ext
    rfl
  have hActionVal :=
    v.valuationAt_extensionFixedRepresentation_action
      EM M.normal tB aB
  have hval : v.valuationAt MF
      (fixedFieldInclusion A M₀ M.field hMM₀ x) =
      k • v.oneValue := by
    rw [hxFormula]
    have hxBFormula : eB xB = bM + eB aB - eB (B.ρ tB aB) := by
      apply Subtype.ext
      rfl
    rw [hxBFormula]
    dsimp only [bM]
    rw [map_sub, map_add, map_add, map_nsmul, hpiLM,
      wUnitM.2, hActionVal]
    abel
  calc
    ((v.valuationAt MF
        (fixedFieldInclusion A M₀ M.field hMM₀ x) :
          v.valueGroup) : ProfiniteInteger) =
        ((k • v.oneValue : v.valueGroup) : ProfiniteInteger) :=
      congrArg Subtype.val hval
    _ = k • (1 : ProfiniteInteger) := rfl
    _ = Int.castRingHom ProfiniteInteger (k : ℤ) := by
      simp

end ValuationData

end

end Atlas.Knowledge
