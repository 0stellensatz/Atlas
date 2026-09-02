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
surjectivity and kernel laws. The coefficient module remains the units
of the separable closure, which is essential in imperfect positive
characteristic (#104).

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
instantiation's obligation. The Galois groups are spelled `≃ₐ[·]`, the
chosen embedding is the layer's flat
`separableEmbeddingIntoSeparableClosure`, `closedFixingSubgroup` takes
only the intermediate field — behind the intrinsic abbreviations in
the chosen half — and the realization's finiteness witness is the
layer's `baseFixingExtensionQuotient_finite_of_isSeparable`, whose
separability hypotheses the realization's Galois instances synthesize.
The `OfEmbedding` half is generalized over a separably closed Galois
ambient `Ω` in place of the pinned separable closure, so the
algebraic-closure instantiation of the local data can enter; the
private `G`/`A`/`B` abbreviations and `intrinsicFiniteAbstractBase`
are pinned to the separable closure, so that half spells them out and
rebuilds the intrinsic base inline — definitionally the same term,
`FiniteAbstractField.finite` being Prop-valued — while the chosen
half's statements are unchanged at the separable closure. Everything
else ports token-for-token; the file is the source's
`LocalReciprocity/ConcreteReciprocityTransport.lean` whole.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

variable (Ω : Type) [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]

private abbrev G (K : Type) [Field K] :=
  intrinsicAbsoluteGalois K

private abbrev A (K : Type) [Field K] : Rep ℤ (G K) :=
  intrinsicAbsoluteUnits K

private abbrev B (K : Type) [Field K] : ClosedSubgroup (G K) :=
  intrinsicAbstractBase K

/-- The finite abstract extension object determined by an explicit
embedding of `L` into the fixed separable closure ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean:46`]
[Yamaguchi2026]). -/
def finiteGaloisAbstractExtensionOfEmbedding
    (i : L →ₐ[K] Ω) :
    FiniteGaloisSubextension
      (closedFixingSubgroup (⊥ : IntermediateField K Ω)) where
  field := finiteGaloisClosedFixingSubgroupOfEmbedding K L Ω i
  below := fixingSubgroupLeBase K Ω
    (finiteGaloisFieldRangeOfEmbedding K L Ω i)
  normal := inferInstance
  finite := baseFixingExtensionQuotient_finite_of_isSeparable
    K Ω (finiteGaloisFieldRangeOfEmbedding K L Ω i)

/-- The concrete realization of `L/K` as the finite Galois extension
object to which the abstract reciprocity theorem is applied
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean:57`]
[Yamaguchi2026]). -/
def finiteGaloisAbstractExtension : FiniteGaloisSubextension (B K) :=
  finiteGaloisAbstractExtensionOfEmbedding K L (SeparableClosure K)
    (separableEmbeddingIntoSeparableClosure K L)

/-- The additive reciprocity equivalence transported through an
explicit realization of `L/K` in the separable closure ([Yamaguchi
2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean:63`]
[Yamaguchi2026]). -/
def concreteReciprocityAddEquivOfEmbedding
    (i : L →ₐ[K] Ω)
    (D : DegreeData (Ω ≃ₐ[K] Ω))
    (v : ValuationData D (galoisAmbientUnitsRep K Ω))
    (hcf : SatisfiesClassFieldAxiom (galoisAmbientUnitsRep K Ω))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D) :
    Additive (Abelianization (L ≃ₐ[K] L)) ≃+
      Additive (NormQuotient K L) :=
  (MulEquiv.toAdditive
      ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
        K L Ω i).abelianizationCongr.symm)).trans
    ((D.abstractReciprocityEquiv (galoisAmbientUnitsRep K Ω) v hcf hAxiom
      ⟨closedFixingSubgroup (⊥ : IntermediateField K Ω), by
        rw [closedFixingSubgroup_bot_eq_baseField]
        exact (FiniteAbstractField.base (Ω ≃ₐ[K] Ω)).finite⟩
      (finiteGaloisAbstractExtensionOfEmbedding K L Ω i)).trans
        (finiteNormQuotientEquivEmbeddedNormQuotient
          K Ω L i))

/-- Multiplicative form of reciprocity transported through an explicit
embedding ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean:78`]
[Yamaguchi2026]). -/
def concreteReciprocityEquivOfEmbedding
    (i : L →ₐ[K] Ω)
    (D : DegreeData (Ω ≃ₐ[K] Ω))
    (v : ValuationData D (galoisAmbientUnitsRep K Ω))
    (hcf : SatisfiesClassFieldAxiom (galoisAmbientUnitsRep K Ω))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D) :
    Abelianization (L ≃ₐ[K] L) ≃* NormQuotient K L := by
  let e : Additive (Abelianization (L ≃ₐ[K] L)) ≃+
      Additive (NormQuotient K L) :=
    concreteReciprocityAddEquivOfEmbedding K L Ω i D v hcf hAxiom
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
`LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean:98`]
[Yamaguchi2026]). -/
def concreteNormResidueSymbolOfEmbedding
    (i : L →ₐ[K] Ω)
    (D : DegreeData (Ω ≃ₐ[K] Ω))
    (v : ValuationData D (galoisAmbientUnitsRep K Ω))
    (hcf : SatisfiesClassFieldAxiom (galoisAmbientUnitsRep K Ω))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D) :
    Kˣ →* Abelianization (L ≃ₐ[K] L) :=
  (concreteReciprocityEquivOfEmbedding
    K L Ω i D v hcf hAxiom).symm.toMonoidHom.comp
    (normClass K L)

/-- The additive form of the concrete reciprocity isomorphism; its
inputs are the three genuine structures constructed in the preceding
part of the proof, together with the threaded unit-cohomology
hypothesis, whose local proof is
`Atlas.Knowledge.localHenselianValuation_satisfiesUnramifiedUnitCohomology`
— at the algebraic-closure ambient, which the hoist of this transport
joins ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean:109`]
[Yamaguchi2026]). -/
def concreteReciprocityAddEquiv
    (D : DegreeData (G K)) (v : ValuationData D (A K))
    (hcf : SatisfiesClassFieldAxiom (A K))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D) :
    Additive (Abelianization (L ≃ₐ[K] L)) ≃+
      Additive (NormQuotient K L) :=
  concreteReciprocityAddEquivOfEmbedding K L (SeparableClosure K)
    (separableEmbeddingIntoSeparableClosure K L) D v hcf hAxiom

/-- **The public multiplicative form of the transported reciprocity
isomorphism `G(L/K)ᵃᵇ ≃ Kˣ/N_{L/K}Lˣ`** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean:119`]
[Yamaguchi2026]). -/
def concreteReciprocityEquiv
    (D : DegreeData (G K)) (v : ValuationData D (A K))
    (hcf : SatisfiesClassFieldAxiom (A K))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D) :
    Abelianization (L ≃ₐ[K] L) ≃* NormQuotient K L :=
  concreteReciprocityEquivOfEmbedding K L (SeparableClosure K)
    (separableEmbeddingIntoSeparableClosure K L) D v hcf hAxiom

/-- **The local norm-residue symbol obtained by inverting reciprocity
and precomposing with the quotient map on `Kˣ`** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean:128`]
[Yamaguchi2026]). -/
def concreteNormResidueSymbol
    (D : DegreeData (G K)) (v : ValuationData D (A K))
    (hcf : SatisfiesClassFieldAxiom (A K))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D) :
    Kˣ →* Abelianization (L ≃ₐ[K] L) :=
  concreteNormResidueSymbolOfEmbedding K L (SeparableClosure K)
    (separableEmbeddingIntoSeparableClosure K L) D v hcf hAxiom

/-- The local norm-residue symbol is onto ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean:136`]
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
`LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean:145`]
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
