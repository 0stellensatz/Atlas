import Mathlib
import Atlas.Knowledge.AbstractFixedFieldUnitsEquiv
import Atlas.Knowledge.AbstractReciprocityEquiv
import Atlas.Knowledge.AbstractRelativeFixedField

/-!
# fixed-field norm-residue symbol

The norm-residue symbol at an arbitrary finite abstract base, expressed on the units and
abelianized Galois group of its actual fixed fields. It composes the abstract symbol with the
fixed-unit and relative-Galois identifications.

## Main definitions

* `abstractFixedFieldNormResidueSymbol` — the symbol on actual fixed-field units.

## Implementation notes

The base field and the Galois ambient occupy independent universes. As in
`Atlas.Knowledge.AbstractReciprocityEquiv`, the unit-cohomology hypothesis is explicit;
local specializations supply `Atlas.Knowledge.UnitCohomologyDischarge`. This symbol is induced
by the class formation on the ambient group. Identifying it with the intrinsic local Artin
map of the fixed field is a separate comparison.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u v

variable (k : Type u) (Ω : Type v) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- The norm-residue symbol on the actual units of a concrete fixed field,
obtained from the abstract class-formation symbol through the canonical
fixed-unit and relative-Galois identifications
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldNormResidueNaturality.lean:56`]
[Yamaguchi2026]). -/
noncomputable def abstractFixedFieldNormResidueSymbol
    (D : DegreeData (Gal(Ω/k)))
    (v : ValuationData D (galoisAmbientUnitsRep k Ω))
    (hcf : SatisfiesClassFieldAxiom
      (galoisAmbientUnitsRep k Ω))
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    [hKabsolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        K.toSubgroup.subgroupOf (baseField (Gal(Ω/k))).toSubgroup)] :
    Additive (abstractFixedField k Ω K)ˣ →+
      Additive (Abelianization
        Gal(abstractRelativeFixedField k Ω hLK /
          abstractFixedField k Ω K)) := by
  let KF : FiniteAbstractField (Gal(Ω/k)) :=
    ⟨K, hKabsolute⟩
  let E : FiniteGaloisSubextension KF.field :=
    ⟨L, hLK, hnormal, hfinite⟩
  exact
    (MulEquiv.toAdditive
      (abstractExtensionQuotientEquivGaloisGroup
        k Ω K L hLK hnormal).abelianizationCongr).toAddMonoidHom.comp
      ((D.normResidueSymbol (galoisAmbientUnitsRep k Ω)
        v hcf hAxiom KF E).toAddMonoidHom.comp
        ((finiteNormClassHom (galoisAmbientUnitsRep k Ω)
          K L hLK).comp
          (abstractFixedFieldUnitsEquivGaloisFixed
            k Ω K).toAddMonoidHom))

end

end Atlas.Knowledge
