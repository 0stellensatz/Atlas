import Mathlib
import Atlas.Knowledge.AbstractReciprocityEquiv
import Atlas.Knowledge.ClassFieldAxiom
import Atlas.Knowledge.ConcreteReciprocityTransport
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteAbstractFieldExtension
import Atlas.Knowledge.FiniteGaloisRealization
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.FiniteLocalReciprocityLaw
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FiniteNormQuotientEquivNormQuotient
import Atlas.Knowledge.FiniteReciprocityNaturalityNorm
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.GaloisExtensionQuotient
import Atlas.Knowledge.IntermediateFieldRestrictNormalHom
import Atlas.Knowledge.IntermediateFieldUnitsFixedSubgroup
import Atlas.Knowledge.LocalClassFieldAxiom
import Atlas.Knowledge.LocalHenselianValuation
import Atlas.Knowledge.LocalResidueDatum
import Atlas.Knowledge.NormQuotient
import Atlas.Knowledge.NormResidueNaturality
import Atlas.Knowledge.NormResidueNaturalityArrows
import Atlas.Knowledge.ResidueDatumIn
import Atlas.Knowledge.SeparableFixedFieldNorm
import Atlas.Knowledge.UnitCohomologyAxiom
import Atlas.Knowledge.UnitCohomologyDischarge
import Atlas.Knowledge.ValuationData

/-!
# intermediate-field norm-residue naturality

The abstract class formation supplies restriction naturality; here it
is transported to the concrete local norm-residue symbol: for two
finite abelian Galois intermediate fields `E ≤ F` of the ambient
closure, restriction `Gal(F/K) → Gal(E/K)` carries the norm-residue
automorphism of `F` to that of `E`, and the closing theorem states this
for the layer's canonical local norm-residue symbol (#104).

## Main definitions

* `galoisAmbientFiniteAbstractBase` — the bottom fixing subgroup as a
  finite abstract field.

## Main statements

* `finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply` —
  the quotient equivalence on a representative; proved.
* `concreteNormResidueSymbolOfEmbedding_eq_abstract` — the concrete
  symbol as the transported abstract symbol; proved.
* `concreteNormResidueAutomorphism_restrict` — restriction naturality
  before specializing the local structures; proved.
* `localArtinAutomorphism_restrict` — restriction naturality of the
  canonical local norm-residue symbol; proved.

## Implementation notes

The ambient conversion of the arc: the source works over its pinned
`SeparableClosure K`, the layer over a separably closed Galois ambient
`Ω` instantiated at `AlgebraicClosure K` in the closing theorem — so
the source's private `absoluteGalois`, `absoluteUnits`, and
`abstractBase` abbreviations become `Ω ≃ₐ[K] Ω`,
`galoisAmbientUnitsRep K Ω`, and `closedFixingSubgroup ⊥`, and its
`intrinsicFiniteAbstractBase` is rebuilt here, hoisted over `Ω`, as
`galoisAmbientFiniteAbstractBase`. The general statements thread
`hAxiom : v.SatisfiesUnramifiedUnitCohomology D` after `hcf` — the
interface departure carried since
`Atlas.Knowledge.AbstractReciprocityEquiv` — while the closing theorem
supplies all four local inputs, discharging the hypothesis by
`Atlas.Knowledge.localHenselianValuation_satisfiesUnramifiedUnitCohomology`,
so it threads nothing.

The structural departure: the source reaches its
canonical symbol through the embedding-independence theorem of its
`ConcreteReciprocityCanonical.lean`, which the layer skips, and pins
the restriction chain to the inclusions `E.val`, `F.val`. The layer's
canonical symbol lives at the chosen `IsAlgClosed.lift`, so the chain
here is stated at arbitrary embeddings `iE`, `iF` instead: the
quotient-compatibility privates strengthen `[IsGalois]` to
`[IsAbelianGalois]` and replace the source's inclusion-definitional
step by a conjugation-triviality argument — any embedding of a normal
intermediate field restricts, by `AlgHom.fieldRange_of_normal` and
`AlgHom.restrictNormal'`, to an automorphism of it, and conjugation by
that automorphism is trivial on an abelian Galois group. Two
representative formulas the privates consume are pulled in from the
otherwise-skipped `ConcreteReciprocityCanonical.lean` (`:573`, `:612`),
hoisted over `Ω`; its base-unit comparison law (`:635`) is rederived
from the layer's
`finiteNormQuotientEquivEmbeddedNormQuotient_finiteNormClass` as a
private lemma without the source's simp attribute — only this file
consumes it — and its private finiteness instances are replaced by
`letI`-in-type bindings. The closing theorem takes the layer's
`[IsMixedCharLocalField K]` where the source takes
`[IsNonarchimedeanLocalField K]`, and needs no `omit` dance: the local
instances enter only in its own section. Galois groups are spelled
`≃ₐ[·]`. Everything else ports token-for-token; the file is the
source's `LocalReciprocity/IntermediateFieldNormResidueNaturality.lean`
whole. The source's `τ` binders are spelled `tau`.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

open scoped IsMulCommutative

variable (K : Type u) [Field K]
variable (Ω : Type u) [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]

/-- **The bottom fixing subgroup packaged as a finite abstract field**;
its defining quotient is the trivial finite quotient. The source's
separable-closure form, hoisted over the ambient `Ω` (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/IntrinsicAbsoluteData.lean:61`). -/
@[reducible]
def galoisAmbientFiniteAbstractBase :
    FiniteAbstractField (Ω ≃ₐ[K] Ω) where
  field := closedFixingSubgroup (⊥ : IntermediateField K Ω)
  finite := by
    rw [closedFixingSubgroup_bot_eq_baseField]
    exact (FiniteAbstractField.base (Ω ≃ₐ[K] Ω)).finite

omit [IsSepClosed Ω] in
/-- The engine's quotient equivalence at the base evaluates a
representative through the ambient inclusion (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityCanonical.lean:573`). -/
private theorem baseFixingExtensionQuotientEquivGaloisGroup_mk_apply
    (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
    (tau : (closedFixingSubgroup
      (⊥ : IntermediateField K Ω)).toSubgroup) (x : E) :
    E.val (baseFixingExtensionQuotientEquivGaloisGroup K Ω E
      (QuotientGroup.mk tau) x) = tau.1 (E.val x) := by
  letI : (closedFixingSubgroup E).toSubgroup.Normal :=
    closedFixingSubgroup_normal K Ω E
  have hq :
      baseFixingExtensionQuotientEquivAmbient K Ω E
          (QuotientGroup.mk tau) =
        QuotientGroup.mk' (closedFixingSubgroup E).toSubgroup tau.1 := by
    rfl
  have hn := InfiniteGalois.normalAutEquivQuotient_apply
    (closedFixingSubgroup E) tau.1
  change InfiniteGalois.normalAutEquivQuotient (closedFixingSubgroup E)
      (QuotientGroup.mk' _ tau.1) = _ at hn
  change E.val
      ((AlgEquiv.autCongr
          (IntermediateField.equivOfEq
            (InfiniteGalois.fixedField_fixingSubgroup E))
          ((InfiniteGalois.normalAutEquivQuotient (closedFixingSubgroup E))
            (baseFixingExtensionQuotientEquivAmbient K Ω E
              (QuotientGroup.mk tau)))) x) =
    tau.1 (E.val x)
  rw [hq, hn, AlgEquiv.autCongr_apply]
  simp only [AlgEquiv.trans_apply, IntermediateField.equivOfEq_symm,
    IntermediateField.equivOfEq_apply]
  change
    (((AlgEquiv.restrictNormalHom
      (IntermediateField.fixedField
        (closedFixingSubgroup E).toSubgroup) tau.1)
      ⟨E.val x, _⟩ : IntermediateField.fixedField
        (closedFixingSubgroup E).toSubgroup) : Ω) =
      tau.1 (E.val x)
  rw [AlgEquiv.restrictNormalHom_apply]

section EmbeddedExtension

variable (L : Type u) [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

omit [IsSepClosed Ω] in
/-- **Formula for the quotient equivalence on a representative**,
expressed without mentioning the auxiliary fixed-field equality used
internally (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityCanonical.lean:612`). -/
@[simp]
theorem finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
    (i : L →ₐ[K] Ω)
    (tau : (closedFixingSubgroup
      (⊥ : IntermediateField K Ω)).toSubgroup) (x : L) :
    i (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L Ω i
      (QuotientGroup.mk tau) x) = tau.1 (i x) := by
  let E := finiteGaloisFieldRangeOfEmbedding K L Ω i
  let e := finiteGaloisFieldRangeEquivOfEmbedding K L Ω i
  let g := baseFixingExtensionQuotientEquivGaloisGroup
    K Ω E (QuotientGroup.mk tau)
  have hb := baseFixingExtensionQuotientEquivGaloisGroup_mk_apply
    K Ω E tau (e x)
  have he (y : E) : i (e.symm y) = E.val y := by
    exact congrArg Subtype.val (e.apply_symm_apply y)
  change i (((e.autCongr).symm g) x) = tau.1 (i x)
  calc
    i (((e.autCongr).symm g) x) = E.val (g (e x)) := by
      simpa only [AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply,
        AlgEquiv.trans_apply, AlgEquiv.symm_symm] using he (g (e x))
    _ = tau.1 (E.val (e x)) := hb
    _ = tau.1 (i x) := rfl

/-- The finite abstract norm class represented by a base-field unit in
an explicit ambient realization (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/IntermediateFieldNormResidueNaturality.lean:50`). -/
private def embeddedBaseNormClass (i : L →ₐ[K] Ω) (a : Kˣ) :
    letI := (finiteGaloisAbstractExtensionOfEmbedding K L Ω i).finite
    FiniteNormQuotient (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup (⊥ : IntermediateField K Ω))
      (finiteGaloisAbstractExtensionOfEmbedding K L Ω i).field
      (finiteGaloisAbstractExtensionOfEmbedding K L Ω i).below :=
  letI := (finiteGaloisAbstractExtensionOfEmbedding K L Ω i).finite
  finiteNormClass (galoisAmbientUnitsRep K Ω)
    (closedFixingSubgroup (⊥ : IntermediateField K Ω))
    (finiteGaloisAbstractExtensionOfEmbedding K L Ω i).field
    (finiteGaloisAbstractExtensionOfEmbedding K L Ω i).below
    (baseUnitsEquivGaloisAmbientFixed K Ω (Additive.ofMul a))

/-- The explicit norm-quotient comparison sends a base-unit
representative to the same representative in the ordinary field norm
quotient (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityCanonical.lean:635`). -/
private theorem
    finiteNormQuotientEquivEmbeddedNormQuotient_finiteNormClass_baseUnit
    (i : L →ₐ[K] Ω) (a : Kˣ) :
    finiteNormQuotientEquivEmbeddedNormQuotient K Ω L i
        (embeddedBaseNormClass K Ω L i a) =
      Additive.ofMul (normClass K L a) := by
  have h := finiteNormQuotientEquivEmbeddedNormQuotient_finiteNormClass
    K Ω L i (baseUnitsEquivGaloisAmbientFixed K Ω (Additive.ofMul a))
  rw [(baseUnitsEquivGaloisAmbientFixed K Ω).symm_apply_apply] at h
  calc
    finiteNormQuotientEquivEmbeddedNormQuotient K Ω L i
        (embeddedBaseNormClass K Ω L i a) =
      (MulEquiv.toAdditive
        (normQuotientEquivOfNormSubgroupEq K (AlgHom.fieldRange i) L
          (localNormSubgroup_fieldRange_eq K Ω L i)))
        ((MonoidHom.toAdditive (normClass K (AlgHom.fieldRange i)))
          (Additive.ofMul a)) := h
    _ = Additive.ofMul (normClass K L a) := by
      change Additive.ofMul
          (normQuotientEquivOfNormSubgroupEq K (AlgHom.fieldRange i) L
            (localNormSubgroup_fieldRange_eq K Ω L i)
            (normClass K (AlgHom.fieldRange i) a)) = _
      rw [normQuotientEquivOfNormSubgroupEq_normClass]

/-- **Before specializing the local datum, the concrete norm-residue
symbol is the abstract norm-residue class transported through the
canonical quotient equivalence.** This pointwise transport formula
expresses abstract restriction naturality as a statement about actual
field automorphisms (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/IntermediateFieldNormResidueNaturality.lean:65`). -/
theorem concreteNormResidueSymbolOfEmbedding_eq_abstract
    (i : L →ₐ[K] Ω)
    (D : DegreeData (Ω ≃ₐ[K] Ω))
    (v : ValuationData D (galoisAmbientUnitsRep K Ω))
    (hcf : SatisfiesClassFieldAxiom (galoisAmbientUnitsRep K Ω))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D) (a : Kˣ) :
    concreteNormResidueSymbolOfEmbedding K L Ω i D v hcf hAxiom a =
      (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
        K L Ω i).abelianizationCongr
        (Additive.toMul
          (D.normResidueSymbol (galoisAmbientUnitsRep K Ω) v hcf hAxiom
            (galoisAmbientFiniteAbstractBase K Ω)
            (finiteGaloisAbstractExtensionOfEmbedding K L Ω i)
            (embeddedBaseNormClass K Ω L i a))) := by
  let Eabs := finiteGaloisAbstractExtensionOfEmbedding K L Ω i
  let q := finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L Ω i
  let xabs := embeddedBaseNormClass K Ω L i a
  let z := D.normResidueSymbol (galoisAmbientUnitsRep K Ω) v hcf hAxiom
    (galoisAmbientFiniteAbstractBase K Ω) Eabs xabs
  have hnorm :
      finiteNormQuotientEquivEmbeddedNormQuotient K Ω L i xabs =
        Additive.ofMul (normClass K L a) :=
    finiteNormQuotientEquivEmbeddedNormQuotient_finiteNormClass_baseUnit
      K Ω L i a
  have hsource :
      MulEquiv.toAdditive q.abelianizationCongr.symm
          (Additive.ofMul (q.abelianizationCongr (Additive.toMul z))) = z := by
    apply Additive.toMul.injective
    exact q.abelianizationCongr.symm_apply_apply (Additive.toMul z)
  have hforward :
      concreteReciprocityAddEquivOfEmbedding K L Ω i D v hcf hAxiom
          (Additive.ofMul (q.abelianizationCongr (Additive.toMul z))) =
        Additive.ofMul (normClass K L a) := by
    change finiteNormQuotientEquivEmbeddedNormQuotient K Ω L i
        (D.abstractReciprocityEquiv (galoisAmbientUnitsRep K Ω) v hcf hAxiom
          (galoisAmbientFiniteAbstractBase K Ω) Eabs
          (MulEquiv.toAdditive q.abelianizationCongr.symm
            (Additive.ofMul
              (q.abelianizationCongr (Additive.toMul z))))) = _
    rw [hsource]
    change finiteNormQuotientEquivEmbeddedNormQuotient K Ω L i
        (D.abstractReciprocityEquiv (galoisAmbientUnitsRep K Ω) v hcf hAxiom
          (galoisAmbientFiniteAbstractBase K Ω) Eabs
          ((D.abstractReciprocityEquiv (galoisAmbientUnitsRep K Ω) v hcf
            hAxiom (galoisAmbientFiniteAbstractBase K Ω) Eabs).symm
              xabs)) = _
    rw [(D.abstractReciprocityEquiv (galoisAmbientUnitsRep K Ω) v hcf hAxiom
      (galoisAmbientFiniteAbstractBase K Ω) Eabs).apply_symm_apply,
      hnorm]
  change (concreteReciprocityEquivOfEmbedding K L Ω i D v hcf hAxiom).symm
      (normClass K L a) =
    q.abelianizationCongr (Additive.toMul z)
  apply (concreteReciprocityEquivOfEmbedding K L Ω i D v hcf hAxiom).injective
  rw [(concreteReciprocityEquivOfEmbedding
    K L Ω i D v hcf hAxiom).apply_symm_apply]
  exact (congrArg Additive.toMul hforward).symm

end EmbeddedExtension

section IntermediateRestriction

omit [IsSepClosed Ω] in
/-- The quotient equivalence at an arbitrary embedding of an abelian
intermediate field evaluates through the inclusion as well: the
embedding restricts to an automorphism of the field, and conjugation by
it is trivial on the abelian Galois group. The `E.val`-definitional
step of the source, generalized past the inclusion (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityCanonical.lean:612`). -/
private theorem
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply_val
    (E : IntermediateField K Ω)
    [FiniteDimensional K E] [IsAbelianGalois K E]
    (i : E →ₐ[K] Ω)
    (sigma : (closedFixingSubgroup
      (⊥ : IntermediateField K Ω)).toSubgroup) (x : E) :
    E.val (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K E Ω i
      (QuotientGroup.mk sigma) x) = sigma.1 (E.val x) := by
  let tau := finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K E Ω i
    (QuotientGroup.mk sigma)
  let g : E ≃ₐ[K] E := i.restrictNormal' E
  have hg : ∀ y : E, E.val (g y) = i y := fun y =>
    i.restrictNormal_commutes E y
  have hcomm : ∀ y : E, tau (g y) = g (tau y) := by
    intro y
    have h := mul_comm tau g
    calc
      tau (g y) = (tau * g) y := rfl
      _ = (g * tau) y := by rw [h]
      _ = g (tau y) := rfl
  have key : ∀ y : E, E.val (tau (g y)) = sigma.1 (E.val (g y)) := by
    intro y
    rw [hcomm y, hg (tau y), hg y]
    exact finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
      K Ω E i sigma y
  have hx := key (g.symm x)
  rwa [g.apply_symm_apply] at hx

omit [IsSepClosed Ω] in
/-- Restriction between the actual Galois groups is compatible with the
abstract quotient presentations attached to arbitrary embeddings
(Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/IntermediateFieldNormResidueNaturality.lean:132`). -/
private theorem intermediateFieldRestrict_abstractQuotient_mk
    (E F : IntermediateField K Ω) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsAbelianGalois K E] [IsAbelianGalois K F]
    (iE : E →ₐ[K] Ω) (iF : F →ₐ[K] Ω)
    (sigma : (closedFixingSubgroup
      (⊥ : IntermediateField K Ω)).toSubgroup) :
    intermediateFieldRestrictNormalHom E F hEF
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K F Ω iF
          (QuotientGroup.mk sigma)) =
      finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K E Ω iE
        (QuotientGroup.mk (Subgroup.inclusion le_rfl sigma)) := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.coe_injective
  calc
    E.val ((intermediateFieldRestrictNormalHom E F hEF)
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K F Ω iF
          (QuotientGroup.mk sigma)) x) =
      F.val
        ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K F Ω iF
            (QuotientGroup.mk sigma))
          (IntermediateField.inclusion hEF x)) :=
            intermediateFieldRestrictNormalHom_apply_val E F hEF _ x
    _ = sigma.1 (F.val (IntermediateField.inclusion hEF x)) := by
      exact
        finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply_val
          K Ω F iF sigma (IntermediateField.inclusion hEF x)
    _ = (Subgroup.inclusion le_rfl sigma).1 (E.val x) := rfl
    _ = E.val
        ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K E Ω iE
          (QuotientGroup.mk (Subgroup.inclusion le_rfl sigma))) x) := by
      exact
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply_val
          K Ω E iE (Subgroup.inclusion le_rfl sigma) x).symm

/-- Containment of the abstract extension subgroups attached to
arbitrary embeddings of nested intermediate fields (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/IntermediateFieldNormResidueNaturality.lean:165`). -/
private theorem embeddedAbstractExtension_field_le
    (E F : IntermediateField K Ω) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsGalois K E] [IsGalois K F]
    (iE : E →ₐ[K] Ω) (iF : F →ₐ[K] Ω) :
    (finiteGaloisAbstractExtensionOfEmbedding K F Ω iF).field.toSubgroup ≤
      (finiteGaloisAbstractExtensionOfEmbedding K E Ω iE).field.toSubgroup
    := by
  change
    (closedFixingSubgroup (AlgHom.fieldRange iF)).toSubgroup ≤
      (closedFixingSubgroup (AlgHom.fieldRange iE)).toSubgroup
  rw [AlgHom.fieldRange_of_normal iE, AlgHom.fieldRange_of_normal iF]
  change F.fixingSubgroup ≤ E.fixingSubgroup
  exact IntermediateField.fixingSubgroup_le hEF

/-- Restriction of actual Galois groups transports the abstract
abelianized restriction across the quotient equivalences of arbitrary
embeddings (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/IntermediateFieldNormResidueNaturality.lean:181`). -/
private theorem intermediateFieldRestrict_abstractAbelianization
    (E F : IntermediateField K Ω) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsAbelianGalois K E] [IsAbelianGalois K F]
    (iE : E →ₐ[K] Ω) (iF : F →ₐ[K] Ω)
    (z : Abelianization
      (finiteGaloisAbstractExtensionOfEmbedding K F Ω iF).extensionQuotient) :
    intermediateFieldRestrictNormalHom E F hEF
        ((Abelianization.equivOfComm (H := (F ≃ₐ[K] F))).symm
          ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
            K F Ω iF).abelianizationCongr z)) =
      (Abelianization.equivOfComm (H := (E ≃ₐ[K] E))).symm
        ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          K E Ω iE).abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            (closedFixingSubgroup (⊥ : IntermediateField K Ω))
            (closedFixingSubgroup (⊥ : IntermediateField K Ω))
            (finiteGaloisAbstractExtensionOfEmbedding K E Ω iE).field
            (finiteGaloisAbstractExtensionOfEmbedding K F Ω iF).field
            le_rfl (embeddedAbstractExtension_field_le K Ω E F hEF iE iF)
            z)) := by
  let B := closedFixingSubgroup (⊥ : IntermediateField K Ω)
  let EE := finiteGaloisAbstractExtensionOfEmbedding K E Ω iE
  let EF := finiteGaloisAbstractExtensionOfEmbedding K F Ω iF
  let qE := finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K E Ω iE
  let qF := finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K F Ω iF
  letI : (EE.field.toSubgroup.subgroupOf B.toSubgroup).Normal := EE.normal
  letI : (EF.field.toSubgroup.subgroupOf B.toSubgroup).Normal := EF.normal
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨sigma, rfl⟩ := QuotientGroup.mk_surjective q
  change
    intermediateFieldRestrictNormalHom E F hEF
        ((Abelianization.equivOfComm (H := (F ≃ₐ[K] F))).symm
          (qF.abelianizationCongr
            (Abelianization.of (QuotientGroup.mk sigma)))) =
      (Abelianization.equivOfComm (H := (E ≃ₐ[K] E))).symm
        (qE.abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            B B EE.field EF.field le_rfl
            (embeddedAbstractExtension_field_le K Ω E F hEF iE iF)
            (Abelianization.of (QuotientGroup.mk sigma))))
  rw [abelianizationCongr_of]
  change
    intermediateFieldRestrictNormalHom E F hEF
        (qF (QuotientGroup.mk sigma)) =
      (Abelianization.equivOfComm (H := (E ≃ₐ[K] E))).symm
        (qE.abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            B B EE.field EF.field le_rfl
            (embeddedAbstractExtension_field_le K Ω E F hEF iE iF)
            (Abelianization.of (QuotientGroup.mk sigma))))
  rw [normResidueNaturalityAbelianizedRestriction_of_mk]
  change
    intermediateFieldRestrictNormalHom E F hEF
        (qF (QuotientGroup.mk sigma)) =
      (Abelianization.equivOfComm (H := (E ≃ₐ[K] E))).symm
        (qE.abelianizationCongr
          (Abelianization.of
            (QuotientGroup.mk (Subgroup.inclusion le_rfl sigma))))
  rw [abelianizationCongr_of]
  change
    intermediateFieldRestrictNormalHom E F hEF
        (qF (QuotientGroup.mk sigma)) =
      qE (QuotientGroup.mk (Subgroup.inclusion le_rfl sigma))
  exact intermediateFieldRestrict_abstractQuotient_mk
    K Ω E F hEF iE iF sigma

/-- **Restriction naturality for the concrete norm-residue symbol,
before specializing the four structures of the local class formation.**
Both extensions are literal intermediate fields of the ambient closure,
realized through arbitrary embeddings, and the vertical Galois map is
the actual restriction map (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/IntermediateFieldNormResidueNaturality.lean:250`). -/
theorem concreteNormResidueAutomorphism_restrict
    (E F : IntermediateField K Ω) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsAbelianGalois K E] [IsAbelianGalois K F]
    (iE : E →ₐ[K] Ω) (iF : F →ₐ[K] Ω)
    (D : DegreeData (Ω ≃ₐ[K] Ω))
    (v : ValuationData D (galoisAmbientUnitsRep K Ω))
    (hcf : SatisfiesClassFieldAxiom (galoisAmbientUnitsRep K Ω))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D) (a : Kˣ) :
    intermediateFieldRestrictNormalHom E F hEF
        ((Abelianization.equivOfComm (H := (F ≃ₐ[K] F))).symm
          (concreteNormResidueSymbolOfEmbedding
            K F Ω iF D v hcf hAxiom a)) =
      (Abelianization.equivOfComm (H := (E ≃ₐ[K] E))).symm
        (concreteNormResidueSymbolOfEmbedding
          K E Ω iE D v hcf hAxiom a) := by
  let B := closedFixingSubgroup (⊥ : IntermediateField K Ω)
  let BF := galoisAmbientFiniteAbstractBase K Ω
  let EE := finiteGaloisAbstractExtensionOfEmbedding K E Ω iE
  let EF := finiteGaloisAbstractExtensionOfEmbedding K F Ω iF
  let qE := finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K E Ω iE
  let qF := finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K F Ω iF
  let xE := embeddedBaseNormClass K Ω E iE a
  let xF := embeddedBaseNormClass K Ω F iF a
  have hFE : EF.field.toSubgroup ≤ EE.field.toSubgroup :=
    embeddedAbstractExtension_field_le K Ω E F hEF iE iF
  letI hEENormal : (EE.field.toSubgroup.subgroupOf B.toSubgroup).Normal :=
    EE.normal
  letI hEFNormal : (EF.field.toSubgroup.subgroupOf B.toSubgroup).Normal :=
    EF.normal
  letI hEEFinite : Finite
      (B.toSubgroup ⧸ EE.field.toSubgroup.subgroupOf B.toSubgroup) :=
    EE.finite
  letI hEFFinite : Finite
      (B.toSubgroup ⧸ EF.field.toSubgroup.subgroupOf B.toSubgroup) :=
    EF.finite
  letI hBBFinite : Finite
      (B.toSubgroup ⧸ B.toSubgroup.subgroupOf B.toSubgroup) := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  let T : FiniteAbstractFieldExtension (Ω ≃ₐ[K] Ω) := {
    field := BF
    base := BF
    below := le_rfl
    finiteQuotient := hBBFinite }
  letI : (EE.field.toSubgroup.subgroupOf T.base.field.toSubgroup).Normal := by
    change (EE.field.toSubgroup.subgroupOf B.toSubgroup).Normal
    exact hEENormal
  letI : (EF.field.toSubgroup.subgroupOf T.field.field.toSubgroup).Normal := by
    change (EF.field.toSubgroup.subgroupOf B.toSubgroup).Normal
    exact hEFNormal
  letI : Finite
      (T.base.field.toSubgroup ⧸
        EE.field.toSubgroup.subgroupOf T.base.field.toSubgroup) := by
    change Finite
      (B.toSubgroup ⧸ EE.field.toSubgroup.subgroupOf B.toSubgroup)
    exact hEEFinite
  letI : Finite
      (T.field.field.toSubgroup ⧸
        EF.field.toSubgroup.subgroupOf T.field.field.toSubgroup) := by
    change Finite
      (B.toSubgroup ⧸ EF.field.toSubgroup.subgroupOf B.toSubgroup)
    exact hEFFinite
  have hnorm : finiteReciprocityNaturalityNormMap (galoisAmbientUnitsRep K Ω)
        B B EE.field EF.field EE.below EF.below le_rfl hFE xF = xE := by
    dsimp only [xF, xE, embeddedBaseNormClass]
    rw [finiteReciprocityNaturalityNormMap_finiteNormClass,
      relativeNorm_self]
  have hraw := D.normResidueNaturality_norm_restriction
    (galoisAmbientUnitsRep K Ω) v hcf hAxiom
    T EE.field EF.field EE.below EF.below hFE
  have hrawa := DFunLike.congr_fun hraw xF
  change _ =
    D.normResidueSymbol (galoisAmbientUnitsRep K Ω) v hcf hAxiom BF EE
      (finiteReciprocityNaturalityNormMap (galoisAmbientUnitsRep K Ω)
        B B EE.field EF.field EE.below EF.below le_rfl hFE xF) at hrawa
  rw [hnorm] at hrawa
  let zF := D.normResidueSymbol (galoisAmbientUnitsRep K Ω) v hcf hAxiom
    BF EF xF
  let zE := D.normResidueSymbol (galoisAmbientUnitsRep K Ω) v hcf hAxiom
    BF EE xE
  have hz : normResidueNaturalityAbelianizedRestriction
        B B EE.field EF.field le_rfl hFE
        (Additive.toMul zF) = Additive.toMul zE := by
    exact congrArg Additive.toMul hrawa
  rw [concreteNormResidueSymbolOfEmbedding_eq_abstract
      K Ω F iF D v hcf hAxiom a,
    concreteNormResidueSymbolOfEmbedding_eq_abstract
      K Ω E iE D v hcf hAxiom a]
  change intermediateFieldRestrictNormalHom E F hEF
      ((Abelianization.equivOfComm (H := (F ≃ₐ[K] F))).symm
        (qF.abelianizationCongr (Additive.toMul zF))) =
    (Abelianization.equivOfComm (H := (E ≃ₐ[K] E))).symm
      (qE.abelianizationCongr (Additive.toMul zE))
  calc
    intermediateFieldRestrictNormalHom E F hEF
        ((Abelianization.equivOfComm (H := (F ≃ₐ[K] F))).symm
          (qF.abelianizationCongr (Additive.toMul zF))) =
      (Abelianization.equivOfComm (H := (E ≃ₐ[K] E))).symm
        (qE.abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            B B EE.field EF.field le_rfl hFE
            (Additive.toMul zF))) :=
      intermediateFieldRestrict_abstractAbelianization
        K Ω E F hEF iE iF (Additive.toMul zF)
    _ = (Abelianization.equivOfComm (H := (E ≃ₐ[K] E))).symm
        (qE.abelianizationCongr (Additive.toMul zE)) := by rw [hz]; rfl

end IntermediateRestriction

section LocalField

variable [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

/-- **Restriction naturality for the canonical local norm-residue
symbol**, expressed through automorphisms of finite abelian
intermediate fields of the algebraic closure (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/IntermediateFieldNormResidueNaturality.lean:359`). -/
theorem localArtinAutomorphism_restrict
    (E F : IntermediateField K (AlgebraicClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsAbelianGalois K E] [IsAbelianGalois K F] (a : Kˣ) :
    intermediateFieldRestrictNormalHom E F hEF
        ((Abelianization.equivOfComm (H := (F ≃ₐ[K] F))).symm
          (localArtinMonoidHom K F a)) =
      (Abelianization.equivOfComm (H := (E ≃ₐ[K] E))).symm
        (localArtinMonoidHom K E a) :=
  concreteNormResidueAutomorphism_restrict K (AlgebraicClosure K)
    E F hEF IsAlgClosed.lift IsAlgClosed.lift
    (localResidueDatum K)
    (localHenselianValuation K)
    (algebraicClosureUnits_satisfiesClassFieldAxiom K)
    (localHenselianValuation_satisfiesUnramifiedUnitCohomology K) a

end LocalField

end

end Atlas.Knowledge
