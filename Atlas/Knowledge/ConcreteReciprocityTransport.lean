import Mathlib
import Atlas.Knowledge.AbstractReciprocityEquiv
import Atlas.Knowledge.ClassFieldAxiom
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteGaloisRealization
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.FiniteNormQuotientEquivNormQuotient
import Atlas.Knowledge.GaloisExtensionQuotient
import Atlas.Knowledge.IntrinsicAbsoluteData
import Atlas.Knowledge.NormQuotient
import Atlas.Knowledge.SeparableEmbeddingIntoSeparableClosure
import Atlas.Knowledge.SeparableFixedFieldNorm
import Atlas.Knowledge.UnitCohomologyAxiom
import Atlas.Knowledge.ValuationData

/-!
# concrete reciprocity transport

The final comparison step of the local reciprocity law: once the
absolute-Galois datum, the henselian valuation, and the class-field
axiom have been constructed, the abstract reciprocity theorem is
transported through the concrete finite Galois realization in a
separable closure and through the actual field norm, yielding
`G(L/K)ᵃᵇ ≃ Kˣ/N_{L/K}(Lˣ)` and the norm-residue symbol with its
surjectivity and kernel laws. The coefficient module remains the
units of the separable closure, which is essential in imperfect
positive characteristic (#104).

## Main definitions

* `concreteReciprocityEquiv` — the transported reciprocity
  isomorphism `G(L/K)ᵃᵇ ≃* Kˣ/N_{L/K}(Lˣ)`.
* `concreteNormResidueSymbol` — the local norm-residue symbol.

## Main statements

* `concreteNormResidueSymbol_surjective` — the symbol is onto; proved.
* `concreteNormResidueSymbol_ker` — its kernel is exactly the field
  norm subgroup; proved.

## Implementation notes

The interface departure of the reciprocity arc: every declaration
consuming the reciprocity isomorphism threads
`hAxiom : v.SatisfiesUnramifiedUnitCohomology D` after `hcf` — the
convention recorded in `Atlas.Knowledge.ClassFieldAxiom`'s notes and
carried since `Atlas.Knowledge.AbstractReciprocityEquiv` — so each
statement is weaker than the source's, with the discharge the local
instantiation's obligation. The Galois groups are spelled `≃ₐ[·]`,
the chosen embedding is the layer's flat
`separableEmbeddingIntoSeparableClosure`, `closedFixingSubgroup`
takes only the intermediate field behind the intrinsic abbreviations,
and the realization's finiteness witness is the layer's
`baseFixingExtensionQuotient_finite_of_isSeparable`, whose
separability hypotheses the realization's Galois instances
synthesize. Everything else ports token-for-token; the file is the
source's `LocalReciprocity/ConcreteReciprocityTransport.lean` whole.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

private abbrev G (K : Type) [Field K] :=
  intrinsicAbsoluteGalois K

private abbrev A (K : Type) [Field K] : Rep ℤ (G K) :=
  intrinsicAbsoluteUnits K

private abbrev B (K : Type) [Field K] : ClosedSubgroup (G K) :=
  intrinsicAbstractBase K

/-- The finite abstract extension object determined by an explicit
embedding of `L` into the fixed separable closure ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean:44`]
[Yamaguchi2026]). -/
def finiteGaloisAbstractExtensionOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) : FiniteGaloisSubextension (B K) where
  field := finiteGaloisClosedFixingSubgroupOfEmbedding K L i
  below := fixingSubgroupLeBase K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i)
  normal := inferInstance
  finite := baseFixingExtensionQuotient_finite_of_isSeparable
    K (SeparableClosure K) (finiteGaloisFieldRangeOfEmbedding K L i)

/-- The concrete realization of `L/K` as the finite Galois extension
object to which the abstract reciprocity theorem is applied
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean:55`]
[Yamaguchi2026]). -/
def finiteGaloisAbstractExtension : FiniteGaloisSubextension (B K) :=
  finiteGaloisAbstractExtensionOfEmbedding K L
    (separableEmbeddingIntoSeparableClosure K L)

/-- The additive reciprocity equivalence transported through an
explicit realization of `L/K` in the separable closure
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean:62`]
[Yamaguchi2026]). -/
def concreteReciprocityAddEquivOfEmbedding
    (i : L →ₐ[K] SeparableClosure K)
    (D : DegreeData (G K)) (v : ValuationData D (A K))
    (hcf : SatisfiesClassFieldAxiom (A K))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D) :
    Additive (Abelianization (L ≃ₐ[K] L)) ≃+
      Additive (NormQuotient K L) :=
  (MulEquiv.toAdditive
      ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
        K L i).abelianizationCongr.symm)).trans
    ((D.abstractReciprocityEquiv (A K) v hcf hAxiom
      (intrinsicFiniteAbstractBase K)
      (finiteGaloisAbstractExtensionOfEmbedding K L i)).trans
        (finiteNormQuotientEquivEmbeddedNormQuotient
          K (SeparableClosure K) L i))

/-- Multiplicative form of reciprocity transported through an explicit
embedding ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean:76`]
[Yamaguchi2026]). -/
def concreteReciprocityEquivOfEmbedding
    (i : L →ₐ[K] SeparableClosure K)
    (D : DegreeData (G K)) (v : ValuationData D (A K))
    (hcf : SatisfiesClassFieldAxiom (A K))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D) :
    Abelianization (L ≃ₐ[K] L) ≃* NormQuotient K L := by
  let e : Additive (Abelianization (L ≃ₐ[K] L)) ≃+
      Additive (NormQuotient K L) :=
    concreteReciprocityAddEquivOfEmbedding K L i D v hcf hAxiom
  let em : Multiplicative (Additive (Abelianization (L ≃ₐ[K] L))) ≃*
      Multiplicative (Additive (NormQuotient K L)) :=
    @AddEquiv.toMultiplicative
      (Additive (Abelianization (L ≃ₐ[K] L)))
      (Additive (NormQuotient K L)) inferInstance inferInstance e
  exact (MulEquiv.multiplicativeAdditive
      (Abelianization (L ≃ₐ[K] L))).symm.trans
    (em.trans
        (MulEquiv.multiplicativeAdditive (NormQuotient K L)))

/-- Norm-residue symbol obtained from an explicit separable-closure
realization ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean:95`]
[Yamaguchi2026]). -/
def concreteNormResidueSymbolOfEmbedding
    (i : L →ₐ[K] SeparableClosure K)
    (D : DegreeData (G K)) (v : ValuationData D (A K))
    (hcf : SatisfiesClassFieldAxiom (A K))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D) :
    Kˣ →* Abelianization (L ≃ₐ[K] L) :=
  (concreteReciprocityEquivOfEmbedding
    K L i D v hcf hAxiom).symm.toMonoidHom.comp
    (normClass K L)

/-- The additive form of the concrete reciprocity isomorphism; the
inputs are the three genuine structures constructed in the preceding
part of the proof, not additional reciprocity hypotheses
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean:107`]
[Yamaguchi2026]). -/
def concreteReciprocityAddEquiv
    (D : DegreeData (G K)) (v : ValuationData D (A K))
    (hcf : SatisfiesClassFieldAxiom (A K))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D) :
    Additive (Abelianization (L ≃ₐ[K] L)) ≃+
      Additive (NormQuotient K L) :=
  concreteReciprocityAddEquivOfEmbedding K L
    (separableEmbeddingIntoSeparableClosure K L) D v hcf hAxiom

/-- **The public multiplicative form of the transported reciprocity
isomorphism `G(L/K)ᵃᵇ ≃ Kˣ/N_{L/K}Lˣ`** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean:117`]
[Yamaguchi2026]). -/
def concreteReciprocityEquiv
    (D : DegreeData (G K)) (v : ValuationData D (A K))
    (hcf : SatisfiesClassFieldAxiom (A K))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D) :
    Abelianization (L ≃ₐ[K] L) ≃* NormQuotient K L :=
  concreteReciprocityEquivOfEmbedding K L
    (separableEmbeddingIntoSeparableClosure K L) D v hcf hAxiom

/-- **The local norm-residue symbol obtained by inverting reciprocity
and precomposing with the quotient map on `Kˣ`** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean:126`]
[Yamaguchi2026]). -/
def concreteNormResidueSymbol
    (D : DegreeData (G K)) (v : ValuationData D (A K))
    (hcf : SatisfiesClassFieldAxiom (A K))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D) :
    Kˣ →* Abelianization (L ≃ₐ[K] L) :=
  concreteNormResidueSymbolOfEmbedding K L
    (separableEmbeddingIntoSeparableClosure K L) D v hcf hAxiom

/-- The local norm-residue symbol is onto ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean:135`]
[Yamaguchi2026]). -/
theorem concreteNormResidueSymbol_surjective
    (D : DegreeData (G K)) (v : ValuationData D (A K))
    (hcf : SatisfiesClassFieldAxiom (A K))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D) :
    Function.Surjective (concreteNormResidueSymbol K L D v hcf hAxiom) :=
  (concreteReciprocityEquiv K L D v hcf hAxiom).symm.surjective.comp
    (QuotientGroup.mk'_surjective (localNormSubgroup K L))

/-- The kernel of the local norm-residue symbol is exactly the field
norm subgroup ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean:143`]
[Yamaguchi2026]). -/
theorem concreteNormResidueSymbol_ker
    (D : DegreeData (G K)) (v : ValuationData D (A K))
    (hcf : SatisfiesClassFieldAxiom (A K))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D) :
    (concreteNormResidueSymbol K L D v hcf hAxiom).ker =
      localNormSubgroup K L := by
  ext x
  rw [MonoidHom.mem_ker]
  change
    (concreteReciprocityEquiv K L D v hcf hAxiom).symm
        (normClass K L x) = 1 ↔
      x ∈ localNormSubgroup K L
  constructor
  · intro hx
    have hx' := congrArg (concreteReciprocityEquiv K L D v hcf hAxiom) hx
    rw [(concreteReciprocityEquiv K L D v hcf hAxiom).apply_symm_apply,
      map_one] at hx'
    exact (normClass_eq_one_iff_mem K L x).1 hx'
  · intro hx
    have hq : normClass K L x = 1 :=
      (normClass_eq_one_iff_mem K L x).2 hx
    rw [hq, map_one]

end

end Atlas.Knowledge
