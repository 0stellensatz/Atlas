import Mathlib
import Atlas.Knowledge.AbstractReciprocityEquiv
import Atlas.Knowledge.ClassFieldAxiom
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteAbstractFieldExtension
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.FiniteReciprocityNaturalityConjugation
import Atlas.Knowledge.FiniteReciprocityNaturalityNorm
import Atlas.Knowledge.IntermediateGaloisTransfer
import Atlas.Knowledge.NormResidueNaturalityArrows
import Atlas.Knowledge.NormalizedValuationLaws
import Atlas.Knowledge.RelativeNormConjugation
import Atlas.Knowledge.RelativeNormLaws
import Atlas.Knowledge.TransferNormFrobeniusGeometry
import Atlas.Knowledge.TransferNormNaturality
import Atlas.Knowledge.UnitCohomologyAxiom
import Atlas.Knowledge.ValuationData

/-!
# norm-residue naturality

The three printed commutative diagrams for the norm-residue symbol: it
commutes with restriction on Galois groups together with the relative
norm, with conjugation on both sides, and with transfer together with
inclusion of fixed elements. Each diagram follows from the
corresponding reciprocity square of norm–conjugation or transfer–norm
naturality by inverting the horizontal reciprocity isomorphisms (#104).

## Main statements

* `DegreeData.normResidueNaturality_norm_restriction` — the
  norm/restriction diagram; proved.
* `DegreeData.normResidueNaturality_conjugation` — the conjugation
  diagram; proved.
* `DegreeData.normResidueNaturality_transfer_inclusion` — the
  inclusion/transfer diagram; proved.

## Implementation notes

The relative subgroups are the layer's `Subgroup.subgroupOf` spelling,
with the argument lists of the wrapped naturality maps following their
layer signatures, and the ambient group sits in one `{G : Type u}`
scope, universe-polymorphic since the #104 hoist. All three theorems
thread `hAxiom : v.SatisfiesUnramifiedUnitCohomology D` after `hcf` —
the interface departure recorded in `Atlas.Knowledge.ClassFieldAxiom`'s
notes and carried by every reciprocity declaration since
`Atlas.Knowledge.AbstractReciprocityEquiv`: the statements take the
hypothesis because the layer's `normResidueSymbol` signature carries
it, and the proofs pass it where the source derives
`v.classFieldAxiom_implies_unramifiedUnitCohomology hcf`; each
statement is correspondingly weaker than the source's, with the
discharge the local instantiation's obligation. All three shed the
source's `[T2Space G]` (the continuing cascade) and keep
`[TotallyDisconnectedSpace G]`. Everything else ports token-for-token;
the file is the source's `Reciprocity/Main.lean:987`–`:1007` and
`:1330`–`:1563`, and it closes that source file.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A commutative square of additive isomorphisms remains commutative
after replacing both horizontal isomorphisms by their inverses
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:989`][Yamaguchi2026]). -/
private theorem normResidueNaturality_symm_naturality
    {Q B Q' B' : Type*}
    [AddCommGroup Q] [AddCommGroup B]
    [AddCommGroup Q'] [AddCommGroup B']
    (r : Q ≃+ B) (r' : Q' ≃+ B')
    (q : Q →+ Q') (b : B →+ B')
    (h : b.comp r.toAddMonoidHom =
      r'.toAddMonoidHom.comp q) :
    q.comp r.symm.toAddMonoidHom =
      r'.symm.toAddMonoidHom.comp b := by
  apply AddMonoidHom.ext
  intro x
  apply r'.injective
  change r' (q (r.symm x)) = r' (r'.symm (b x))
  rw [r'.apply_symm_apply]
  have hx := DFunLike.congr_fun h (r.symm x)
  change b (r (r.symm x)) = r' (q (r.symm x)) at hx
  rw [r.apply_symm_apply] at hx
  exact hx.symm

namespace DegreeData

/-- **Reciprocity naturality, first diagram.** The norm-residue symbol
commutes with restriction on Galois groups and the relative norm on
norm quotients ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:1337`][Yamaguchi2026]). -/
theorem normResidueNaturality_norm_restriction
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (T : FiniteAbstractFieldExtension G) (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ T.base.field.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ T.field.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf T.base.field.toSubgroup).Normal]
    [hL'normal :
      (L'.toSubgroup.subgroupOf T.field.field.toSubgroup).Normal]
    [hLKfinite : Finite
      (T.base.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf T.base.field.toSubgroup)]
    [hL'K'finite : Finite
      (T.field.field.toSubgroup ⧸
        L'.toSubgroup.subgroupOf T.field.field.toSubgroup)] :
    let E : FiniteGaloisSubextension T.base.field :=
      ⟨L, hLK, hLnormal, hLKfinite⟩
    let E' : FiniteGaloisSubextension T.field.field :=
      ⟨L', hL'K', hL'normal, hL'K'finite⟩
    (MonoidHom.toAdditive
        (normResidueNaturalityAbelianizedRestriction
          T.base.field T.field.field L L' T.below hL'L)).comp
      (D.normResidueSymbol A v hcf hAxiom T.field E').toAddMonoidHom =
      (D.normResidueSymbol A v hcf hAxiom T.base E).toAddMonoidHom.comp
        (finiteReciprocityNaturalityNormMap A
          T.base.field T.field.field L L'
          hLK hL'K' T.below hL'L) := by
  dsimp only
  let E : FiniteGaloisSubextension T.base.field :=
    ⟨L, hLK, hLnormal, hLKfinite⟩
  let E' : FiniteGaloisSubextension T.field.field :=
    ⟨L', hL'K', hL'normal, hL'K'finite⟩
  let q := MonoidHom.toAdditive
    (normResidueNaturalityAbelianizedRestriction
      T.base.field T.field.field L L' T.below hL'L)
  let b := finiteReciprocityNaturalityNormMap A
    T.base.field T.field.field L L' hLK hL'K' T.below hL'L
  have hRec :
      b.comp
          (D.abstractReciprocityEquiv A v hcf hAxiom
            T.field E').toAddMonoidHom =
        (D.abstractReciprocityEquiv A v hcf hAxiom
          T.base E).toAddMonoidHom.comp q := by
    apply AddMonoidHom.ext
    intro x
    change b (D.abstractReciprocityEquiv A v hcf hAxiom T.field E'
        (Additive.ofMul x.toMul)) =
      D.abstractReciprocityEquiv A v hcf hAxiom T.base E
        (q (Additive.ofMul x.toMul))
    refine QuotientGroup.induction_on x.toMul ?_
    intro z
    change b (D.abstractReciprocityEquiv A v hcf hAxiom T.field E'
        (Additive.ofMul (Abelianization.of z))) =
      D.abstractReciprocityEquiv A v hcf hAxiom T.base E
        (Additive.ofMul (Abelianization.of
          (finiteReciprocityNaturalityRestriction
            T.base.field T.field.field L L' T.below hL'L z)))
    rw [D.abstractReciprocityEquiv_apply_of A v hcf hAxiom T.field E' z]
    rw [D.abstractReciprocityEquiv_apply_of A v hcf hAxiom T.base E
      (finiteReciprocityNaturalityRestriction
        T.base.field T.field.field L L' T.below hL'L z)]
    have h := D.finiteReciprocityNaturality_restriction_norm_commutes
      A v hAxiom T L L' hLK hL'K' hL'L
    exact DFunLike.congr_fun h (Additive.ofMul z)
  exact normResidueNaturality_symm_naturality
    (D.abstractReciprocityEquiv A v hcf hAxiom T.field E')
    (D.abstractReciprocityEquiv A v hcf hAxiom T.base E) q b hRec

/-- **Reciprocity naturality, second diagram.** The norm-residue symbol
commutes with conjugation of the extension and of norm classes
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:1410`][Yamaguchi2026]). -/
theorem normResidueNaturality_conjugation
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) (s : G)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf K.field.toSubgroup)] :
    let Ks := K.conjugate s
    let Ls := conjugateClosedSubgroup L s
    let hLsKs := conjugateClosedSubgroup_mono hLK s
    letI : Finite (Ks.field.toSubgroup ⧸
        Ls.toSubgroup.subgroupOf Ks.field.toSubgroup) :=
      finite_conjugateExtension K.field L s
    let E : FiniteGaloisSubextension K.field :=
      ⟨L, hLK, hLnormal, hLfinite⟩
    let Es : FiniteGaloisSubextension Ks.field :=
      ⟨Ls, hLsKs, inferInstance, inferInstance⟩
    (MonoidHom.toAdditive
        (normResidueNaturalityAbelianizedConjugation
          K.field L s).toMonoidHom).comp
      (D.normResidueSymbol A v hcf hAxiom K E).toAddMonoidHom =
      (D.normResidueSymbol A v hcf hAxiom Ks Es).toAddMonoidHom.comp
        (finiteReciprocityNaturalityConjugationNormMap
          A K.field L hLK s) := by
  dsimp only
  letI hLsfinite : Finite
      ((conjugateClosedSubgroup K.field s).toSubgroup ⧸
        (conjugateClosedSubgroup L s).toSubgroup.subgroupOf
          (conjugateClosedSubgroup K.field s).toSubgroup) :=
    finite_conjugateExtension K.field L s
  let Ks := K.conjugate s
  let E : FiniteGaloisSubextension K.field :=
    ⟨L, hLK, hLnormal, hLfinite⟩
  let Es : FiniteGaloisSubextension Ks.field :=
    ⟨conjugateClosedSubgroup L s, conjugateClosedSubgroup_mono hLK s,
      inferInstance, hLsfinite⟩
  let q := MonoidHom.toAdditive
    (normResidueNaturalityAbelianizedConjugation K.field L s).toMonoidHom
  let b := finiteReciprocityNaturalityConjugationNormMap A K.field L hLK s
  have hRec :
      b.comp
          (D.abstractReciprocityEquiv A v hcf hAxiom K E).toAddMonoidHom =
        (D.abstractReciprocityEquiv A v hcf hAxiom
          Ks Es).toAddMonoidHom.comp q := by
    apply AddMonoidHom.ext
    intro x
    change b (D.abstractReciprocityEquiv A v hcf hAxiom K E
        (Additive.ofMul x.toMul)) =
      D.abstractReciprocityEquiv A v hcf hAxiom Ks Es
        (q (Additive.ofMul x.toMul))
    refine QuotientGroup.induction_on x.toMul ?_
    intro z
    change b (D.abstractReciprocityEquiv A v hcf hAxiom K E
        (Additive.ofMul (Abelianization.of z))) =
      D.abstractReciprocityEquiv A v hcf hAxiom Ks Es
        (Additive.ofMul (Abelianization.of
          (finiteReciprocityNaturalityConjugation K.field L s z)))
    rw [D.abstractReciprocityEquiv_apply_of A v hcf hAxiom K E z]
    rw [D.abstractReciprocityEquiv_apply_of A v hcf hAxiom
      Ks Es
      (finiteReciprocityNaturalityConjugation K.field L s z)]
    have h := D.finiteReciprocityNaturality_conjugation_commutes
      A v hAxiom K L hLK s
    exact DFunLike.congr_fun h (Additive.ofMul z)
  exact normResidueNaturality_symm_naturality
    (D.abstractReciprocityEquiv A v hcf hAxiom K E)
    (D.abstractReciprocityEquiv A v hcf hAxiom Ks Es) q b hRec

/-- **Reciprocity naturality, third diagram.** The norm-residue symbol
commutes with transfer on abelianized Galois groups and inclusion on
norm quotients ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:1482`][Yamaguchi2026]). -/
theorem normResidueNaturality_transfer_inclusion
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (T : FiniteAbstractFieldExtension G) (L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ T.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf T.base.field.toSubgroup).Normal]
    [hLfinite : Finite
      (T.base.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf T.base.field.toSubgroup)] :
    letI : (L.toSubgroup.subgroupOf T.field.field.toSubgroup).Normal :=
      transferNormNaturality_intermediateExtension_normal
        T.base.field T.field.field L T.below
    letI : Finite
        (T.field.field.toSubgroup ⧸
          L.toSubgroup.subgroupOf T.field.field.toSubgroup) :=
      Finite.of_injective
        (transferNormNaturalityIntermediateInclusion
          T.base.field T.field.field L T.below)
        (transferNormNaturalityIntermediateInclusion_injective
          T.base.field T.field.field L T.below)
    let E : FiniteGaloisSubextension T.base.field :=
      ⟨L, hLK'.trans T.below, hLnormal, hLfinite⟩
    let E' : FiniteGaloisSubextension T.field.field :=
      ⟨L, hLK', inferInstance, inferInstance⟩
    (MonoidHom.toAdditive
        (transferNormNaturalityTransfer
          T.base.field T.field.field L T.below)).comp
      (D.normResidueSymbol A v hcf hAxiom T.base E).toAddMonoidHom =
      (D.normResidueSymbol A v hcf hAxiom T.field E').toAddMonoidHom.comp
        (transferNormNaturalityNormQuotientInclusion A
          T.base.field T.field.field L hLK' T.below) := by
  dsimp only
  letI : (L.toSubgroup.subgroupOf T.field.field.toSubgroup).Normal :=
    transferNormNaturality_intermediateExtension_normal
      T.base.field T.field.field L T.below
  letI : Finite
      (T.field.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf T.field.field.toSubgroup) :=
    Finite.of_injective
      (transferNormNaturalityIntermediateInclusion
        T.base.field T.field.field L T.below)
      (transferNormNaturalityIntermediateInclusion_injective
        T.base.field T.field.field L T.below)
  let E : FiniteGaloisSubextension T.base.field :=
    ⟨L, hLK'.trans T.below, hLnormal, hLfinite⟩
  let E' : FiniteGaloisSubextension T.field.field :=
    ⟨L, hLK', inferInstance, inferInstance⟩
  let q := MonoidHom.toAdditive
    (transferNormNaturalityTransfer
      T.base.field T.field.field L T.below)
  let b := transferNormNaturalityNormQuotientInclusion A
    T.base.field T.field.field L hLK' T.below
  have hRec :
      b.comp
          (D.abstractReciprocityEquiv A v hcf hAxiom
            T.base E).toAddMonoidHom =
        (D.abstractReciprocityEquiv A v hcf hAxiom
          T.field E').toAddMonoidHom.comp q := by
    apply AddMonoidHom.ext
    intro x
    change
      b
          (D.transferNormNaturalityAbelianizedReciprocity
            A v hAxiom T.base L (hLK'.trans T.below) x) =
        D.transferNormNaturalityAbelianizedReciprocity
          A v hAxiom T.field L hLK' (q x)
    have h := congrArg (fun f => f x)
      (D.transferNormNaturality A v hAxiom T L hLK').symm
    exact h
  exact normResidueNaturality_symm_naturality
    (D.abstractReciprocityEquiv A v hcf hAxiom T.base E)
    (D.abstractReciprocityEquiv A v hcf hAxiom T.field E') q b hRec

end DegreeData

end

end Atlas.Knowledge
