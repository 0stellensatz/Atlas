import Mathlib
import Atlas.Knowledge.AbstractFixedFieldNormResidueSymbol
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.NormResidueNaturality

/-!
# transfer naturality on fixed fields

Transfer on the abelianized Galois groups of a finite fixed-field tower commutes with unit
inclusion under the induced norm-residue symbols. Normality is required only for the total
extension.

## Main statements

* `abstractFixedFieldNormResidueSymbol_transfer_inclusion` — the transfer/inclusion square.

## Implementation notes

The source is `LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldNormResidueNaturality.lean`.
The base and ambient fields occupy independent universes. The source's relative subgroup is
`Subgroup.subgroupOf`; the unit-cohomology hypothesis is explicit, as in
`Atlas.Knowledge.NormResidueNaturality`. The arrows use the actual fixed-field carriers through
`Atlas.Knowledge.AbstractRelativeFixedField`.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u v

variable (k : Type u) (Ω : Type v) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- Inclusion of the units of the lower concrete fixed field in the units
of the larger concrete fixed field
([Yamaguchi 2026, `FixedFieldNormResidueNaturality.lean:26`][Yamaguchi2026]). -/
def abstractFixedFieldUnitsInclusion
    (K K' : ClosedSubgroup (Gal(Ω/k)))
    (hK'K : K'.toSubgroup ≤ K.toSubgroup) :
    Additive (abstractFixedField k Ω K)ˣ →+
      Additive (abstractFixedField k Ω K')ˣ :=
  MonoidHom.toAdditive
    (Units.map
      (IntermediateField.inclusion
        (abstractFixedField_le k Ω hK'K)).toRingHom)

omit [IsGalois k Ω] in
/-- The concrete fixed-field unit equivalences identify actual unit
inclusion with inclusion of fixed coefficients
([Yamaguchi 2026, `FixedFieldNormResidueNaturality.lean:39`][Yamaguchi2026]). -/
theorem abstractFixedFieldUnitsEquiv_inclusion
    (K K' : ClosedSubgroup (Gal(Ω/k)))
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (x : Additive (abstractFixedField k Ω K)ˣ) :
    abstractFixedFieldUnitsEquivGaloisFixed k Ω K'
        (abstractFixedFieldUnitsInclusion k Ω K K' hK'K x) =
      fixedFieldInclusion (galoisAmbientUnitsRep k Ω)
        K K' hK'K
        (abstractFixedFieldUnitsEquivGaloisFixed k Ω K x) := by
  apply Subtype.ext
  apply Additive.ext
  apply Units.ext
  rfl

omit [IsGalois k Ω] in
private theorem fixedFieldIntermediateFinite
    {K K' L : ClosedSubgroup (Gal(Ω/k))}
    (_hLK : L.toSubgroup ≤ K.toSubgroup)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (_hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    Finite (K.toSubgroup ⧸ K'.toSubgroup.subgroupOf K.toSubgroup) := by
  letI : (L.toSubgroup.subgroupOf K.toSubgroup).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  letI : (K'.toSubgroup.subgroupOf K.toSubgroup).FiniteIndex :=
    Subgroup.finiteIndex_of_le (Subgroup.subgroupOf_mono K.toSubgroup hLK')
  infer_instance

/-- Transfer between the abelianized actual relative Galois groups in a
fixed-field tower, transported through the two canonical quotient/Galois
equivalences
([Yamaguchi 2026, `FixedFieldNormResidueNaturality.lean:282`][Yamaguchi2026]). -/
noncomputable def abstractFixedFieldAbelianizedTransfer
    (K K' L : ClosedSubgroup (Gal(Ω/k)))
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hLfinite : Finite
      (K.toSubgroup ⧸
        L.toSubgroup.subgroupOf K.toSubgroup)] :
    letI : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal :=
      transferNormNaturality_intermediateExtension_normal K K' L hK'K
    letI : Finite
        (K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) :=
      finite_extension_over_intermediate
        (hLK'.trans hK'K) hK'K hLK'
    Additive (Abelianization
        Gal(abstractRelativeFixedField k Ω (hLK'.trans hK'K) /
          abstractFixedField k Ω K)) →+
      Additive (Abelianization
        Gal(abstractRelativeFixedField k Ω hLK' /
          abstractFixedField k Ω K')) := by
  letI : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal :=
    transferNormNaturality_intermediateExtension_normal K K' L hK'K
  letI : Finite
      (K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) :=
    finite_extension_over_intermediate
      (hLK'.trans hK'K) hK'K hLK'
  exact MonoidHom.toAdditive
    ((abstractExtensionQuotientEquivGaloisGroup
      k Ω K' L hLK' inferInstance).abelianizationCongr.toMonoidHom.comp
      ((transferNormNaturalityTransfer K K' L hK'K).comp
        (abstractExtensionQuotientEquivGaloisGroup
          k Ω K L (hLK'.trans hK'K)
          hLnormal).abelianizationCongr.symm.toMonoidHom))

/-- Transfer-inclusion naturality for actual fixed fields.
Transfer of the actual relative Galois abelianizations is compatible with
inclusion of actual fixed-field units and the unit-level norm-residue
symbols
([Yamaguchi 2026, `FixedFieldNormResidueNaturality.lean:321`][Yamaguchi2026]). -/
theorem abstractFixedFieldNormResidueSymbol_transfer_inclusion
    (D : DegreeData (Gal(Ω/k)))
    (v : ValuationData D (galoisAmbientUnitsRep k Ω))
    (hcf : SatisfiesClassFieldAxiom
      (galoisAmbientUnitsRep k Ω))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K K' L : ClosedSubgroup (Gal(Ω/k)))
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hLfinite : Finite
      (K.toSubgroup ⧸
        L.toSubgroup.subgroupOf K.toSubgroup)]
    [hKabsolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        K.toSubgroup.subgroupOf (baseField (Gal(Ω/k))).toSubgroup)] :
    letI : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal :=
      transferNormNaturality_intermediateExtension_normal K K' L hK'K
    letI : Finite
        (K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) :=
      finite_extension_over_intermediate
        (hLK'.trans hK'K) hK'K hLK'
    letI : Finite
        (K.toSubgroup ⧸ K'.toSubgroup.subgroupOf K.toSubgroup) :=
      fixedFieldIntermediateFinite k Ω
        (hLK'.trans hK'K) hLK' hK'K
    letI : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
        K'.toSubgroup.subgroupOf (baseField (Gal(Ω/k))).toSubgroup) :=
      finite_extension_trans hK'K (le_baseField K)
    (abstractFixedFieldAbelianizedTransfer
        k Ω K K' L hLK' hK'K).comp
      (abstractFixedFieldNormResidueSymbol
        k Ω D v hcf hAxiom K L (hLK'.trans hK'K)) =
      (abstractFixedFieldNormResidueSymbol
        k Ω D v hcf hAxiom K' L hLK').comp
        (abstractFixedFieldUnitsInclusion k Ω K K' hK'K) := by
  letI : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal :=
    transferNormNaturality_intermediateExtension_normal K K' L hK'K
  letI : Finite
      (K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) :=
    finite_extension_over_intermediate
      (hLK'.trans hK'K) hK'K hLK'
  letI : Finite
      (K.toSubgroup ⧸ K'.toSubgroup.subgroupOf K.toSubgroup) :=
    fixedFieldIntermediateFinite k Ω
      (hLK'.trans hK'K) hLK' hK'K
  letI : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      K'.toSubgroup.subgroupOf (baseField (Gal(Ω/k))).toSubgroup) :=
    finite_extension_trans hK'K (le_baseField K)
  let KF : FiniteAbstractField (Gal(Ω/k)) :=
    ⟨K, hKabsolute⟩
  let K'F : FiniteAbstractField (Gal(Ω/k)) :=
    ⟨K', inferInstance⟩
  let T : FiniteAbstractFieldExtension (Gal(Ω/k)) :=
    { field := K'F
      base := KF
      below := hK'K
      finiteQuotient := inferInstance }
  apply AddMonoidHom.ext
  intro x
  have h := DFunLike.congr_fun
    (D.normResidueNaturality_transfer_inclusion
      (galoisAmbientUnitsRep k Ω) v hcf hAxiom
      T L hLK')
    (finiteNormClass (galoisAmbientUnitsRep k Ω)
      K L (hLK'.trans hK'K)
      (abstractFixedFieldUnitsEquivGaloisFixed k Ω K x))
  dsimp only [T, KF, K'F] at h
  let q := abstractExtensionQuotientEquivGaloisGroup
    k Ω K L (hLK'.trans hK'K) hLnormal
  let q' := abstractExtensionQuotientEquivGaloisGroup
    k Ω K' L hLK' (inferInstance :
      (L.toSubgroup.subgroupOf K'.toSubgroup).Normal)
  let E : FiniteGaloisSubextension KF.field :=
    ⟨L, hLK'.trans hK'K, hLnormal, hLfinite⟩
  let E' : FiniteGaloisSubextension K'F.field :=
    ⟨L, hLK', inferInstance, inferInstance⟩
  change Additive.ofMul
      (q'.abelianizationCongr
        (transferNormNaturalityTransfer K K' L hK'K
          (q.abelianizationCongr.symm
            (q.abelianizationCongr
              (Additive.toMul
                (D.normResidueSymbol
                  (galoisAmbientUnitsRep k Ω) v hcf hAxiom KF E
                  (finiteNormClass (galoisAmbientUnitsRep k Ω)
                    K L (hLK'.trans hK'K)
                    (abstractFixedFieldUnitsEquivGaloisFixed
                      k Ω K x)))))))) =
    Additive.ofMul
      (q'.abelianizationCongr
        (Additive.toMul
          (D.normResidueSymbol
            (galoisAmbientUnitsRep k Ω) v hcf hAxiom K'F E'
            (finiteNormClass (galoisAmbientUnitsRep k Ω) K' L hLK'
              (abstractFixedFieldUnitsEquivGaloisFixed k Ω K'
                (abstractFixedFieldUnitsInclusion
                  k Ω K K' hK'K x))))))
  apply Additive.toMul.injective
  change q'.abelianizationCongr _ = q'.abelianizationCongr _
  rw [q'.abelianizationCongr.apply_eq_iff_eq]
  rw [q.abelianizationCongr.symm_apply_apply]
  change _ =
    D.normResidueSymbol
      (galoisAmbientUnitsRep k Ω) v hcf hAxiom K'F E'
        (transferNormNaturalityNormQuotientInclusion
          (galoisAmbientUnitsRep k Ω) K K' L hLK' hK'K
          (finiteNormClass (galoisAmbientUnitsRep k Ω)
            K L (hLK'.trans hK'K)
            (abstractFixedFieldUnitsEquivGaloisFixed k Ω K x))) at h
  rw [transferNormNaturality_normQuotientInclusion_finiteNormClass] at h
  rw [← abstractFixedFieldUnitsEquiv_inclusion k Ω K K' hK'K x] at h
  exact congrArg Additive.toMul h

end

end Atlas.Knowledge
