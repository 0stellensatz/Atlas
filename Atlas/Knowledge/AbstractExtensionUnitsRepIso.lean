import Mathlib
import Atlas.Knowledge.AbstractFixedFieldUnitsEquiv
import Atlas.Knowledge.AbstractRelativeFixedField
import Atlas.Knowledge.ExtensionFixedRepresentationEquiv

/-!
# extension representation as the units of the relative fixed field

The engine's descended representation of a finite abstract extension,
identified as an actual Galois module: its carrier is the unit group of the
concrete relative fixed field, the identification intertwines the descended
quotient action with the ordinary relative Galois action, and the whole
comparison packages as an isomorphism of representations after reindexing
along the quotient-to-Galois-group equivalence. This is the bridge on which
the engine's cohomological hypotheses become statements about the units of a
concrete finite Galois extension (#104).

## Main definitions

* `abstractExtensionFixedRepresentationUnitsEquiv` — the carrier is the
  upper fixed field's unit group.
* `abstractExtensionFixedRepresentationIsoUnitsRes` — the representation
  isomorphism with the reindexed unit representation.

## Main statements

* `abstractExtensionFixedRepresentationUnitsEquiv_action` — the carrier
  comparison intertwines the two actions; proved.

## Implementation notes

The relative unit representation is spelled through
`Atlas.Knowledge.galoisAmbientUnitsRep` even where the source names
`Rep.ofAlgebraAutOnUnits` directly — the same simp-normality point recorded
with the dictionary applies at the relative level. The engine's relative
subgroup is `Subgroup.subgroupOf` as across the layer, and the
representation-equivalence packaging is Mathlib's `Rep.mkIso` over
`AddEquiv.toIntLinearEquiv`.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u v

variable (k : Type u) (Ω : Type v) [Field k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω]

/-- **Scalar extension does not change the upper unit group**: the units of
the relative fixed field are the coefficients fixed by the upper subgroup
(Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean:87`). -/
def abstractRelativeFixedFieldUnitsEquivGaloisFixed
    (K L : ClosedSubgroup (Ω ≃ₐ[k] Ω))
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    Additive (abstractRelativeFixedField k Ω hLK)ˣ ≃+
      ambientFixedAddSubgroup (galoisAmbientUnitsRep k Ω) L := by
  change Additive (abstractFixedField k Ω L)ˣ ≃+ _
  exact abstractFixedFieldUnitsEquivGaloisFixed k Ω L

omit [IsGalois k Ω] in
/-- The relative reading forgets to the ambient inclusion (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean:98`). -/
@[simp]
theorem abstractRelativeFixedFieldUnitsEquivGaloisFixed_coe
    (K L : ClosedSubgroup (Ω ≃ₐ[k] Ω))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (x : Additive (abstractRelativeFixedField k Ω hLK)ˣ) :
    ((abstractRelativeFixedFieldUnitsEquivGaloisFixed
        k Ω K L hLK x).1 : Additive Ωˣ) =
      intermediateFieldUnitsToGaloisAmbient k Ω
        (abstractFixedField k Ω L) x :=
  rfl

/-- **The carrier of the descended representation is the upper unit group**
(Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean:110`). -/
def abstractExtensionFixedRepresentationUnitsEquiv
    (K L : ClosedSubgroup (Ω ≃ₐ[k] Ω))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) :
    (extensionFixedRepresentation (galoisAmbientUnitsRep k Ω)
        K L hLK hnormal).V ≃+
      Additive (abstractRelativeFixedField k Ω hLK)ˣ :=
  (extensionFixedRepresentationEquiv (galoisAmbientUnitsRep k Ω)
      K L hLK hnormal).trans
    (abstractRelativeFixedFieldUnitsEquivGaloisFixed
      k Ω K L hLK).symm

omit [IsGalois k Ω] in
/-- Round trip of the two carrier readings (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean:125`). -/
@[simp]
theorem abstractRelativeUnitsEquiv_extensionUnitsEquiv
    (K L : ClosedSubgroup (Ω ≃ₐ[k] Ω))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (x : (extensionFixedRepresentation (galoisAmbientUnitsRep k Ω)
      K L hLK hnormal).V) :
    abstractRelativeFixedFieldUnitsEquivGaloisFixed k Ω K L hLK
        (abstractExtensionFixedRepresentationUnitsEquiv
          k Ω K L hLK hnormal x) =
      extensionFixedRepresentationEquiv
        (galoisAmbientUnitsRep k Ω) K L hLK hnormal x := by
  exact (abstractRelativeFixedFieldUnitsEquivGaloisFixed
    k Ω K L hLK).apply_symm_apply
      (extensionFixedRepresentationEquiv
        (galoisAmbientUnitsRep k Ω) K L hLK hnormal x)

/-- **A quotient representative acts as restriction of the same ambient
automorphism** on the relative fixed field (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean:143`). -/
theorem abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
    (K L : ClosedSubgroup (Ω ≃ₐ[k] Ω))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (σ : K.toSubgroup)
    (x : abstractRelativeFixedField k Ω hLK) :
    letI := hnormal
    σ.1 (x : Ω) =
      (((abstractExtensionQuotientEquivGaloisGroup
          k Ω K L hLK hnormal
          (QuotientGroup.mk' (L.toSubgroup.subgroupOf K.toSubgroup) σ)) x :
        abstractRelativeFixedField k Ω hLK) : Ω) := by
  letI := hnormal
  letI : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  let H : ClosedSubgroup (Ω ≃ₐ[abstractFixedField k Ω K] Ω) :=
    closedFixingSubgroup (abstractRelativeFixedField k Ω hLK)
  letI : H.toSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  change σ.1 (x : Ω) =
    ((((IntermediateField.equivOfEq
      (InfiniteGalois.fixedField_fixingSubgroup
        (abstractRelativeFixedField k Ω hLK))).autCongr
      (InfiniteGalois.normalAutEquivQuotient
        (closedFixingSubgroup (abstractRelativeFixedField k Ω hLK))
        ((abstractSubgroupEquivGaloisGroup k Ω K σ :
            Ω ≃ₐ[abstractFixedField k Ω K] Ω) :
          (Ω ≃ₐ[abstractFixedField k Ω K] Ω) ⧸
            (closedFixingSubgroup
              (abstractRelativeFixedField k Ω hLK)).toSubgroup))) x :
      abstractRelativeFixedField k Ω hLK) : Ω)
  rw [InfiniteGalois.normalAutEquivQuotient_apply,
    AlgEquiv.autCongr_apply]
  simp only [AlgEquiv.trans_apply, IntermediateField.equivOfEq_symm,
    IntermediateField.equivOfEq_apply]
  change σ.1 (x : Ω) =
    (((AlgEquiv.restrictNormalHom
      (IntermediateField.fixedField H.toSubgroup)
      (abstractSubgroupEquivGaloisGroup k Ω K σ))
      ⟨(x : Ω), _⟩ : IntermediateField.fixedField H.toSubgroup) : Ω)
  rw [AlgEquiv.restrictNormalHom_apply]
  rfl

/-- **The abstract coset action on an upper unit is the relative Galois
action** (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean:198`). -/
theorem relativeCosetAction_abstractRelativeFixedFieldUnit_val
    (K L : ClosedSubgroup (Ω ≃ₐ[k] Ω))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (x : Additive (abstractRelativeFixedField k Ω hLK)ˣ)
    (q : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :
    letI := hnormal
    ((Additive.toMul
      (relativeCosetAction (galoisAmbientUnitsRep k Ω)
        K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK x) q) : Ωˣ) : Ω) =
      (((Additive.toMul
        ((galoisAmbientUnitsRep (abstractFixedField k Ω K)
          (abstractRelativeFixedField k Ω hLK)).ρ
            (abstractExtensionQuotientEquivGaloisGroup
              k Ω K L hLK hnormal q) x) :
          (abstractRelativeFixedField k Ω hLK)ˣ) :
        abstractRelativeFixedField k Ω hLK) : Ω) := by
  letI := hnormal
  refine Quotient.inductionOn' q ?_
  intro σ
  rw [relativeCosetAction_mk]
  change σ.1 ((Additive.toMul x :
      (abstractRelativeFixedField k Ω hLK)ˣ) : Ω) = _
  exact abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
    k Ω K L hLK hnormal σ
      (Additive.toMul x : (abstractRelativeFixedField k Ω hLK)ˣ)

/-- **The carrier comparison intertwines the descended action with the
relative Galois action** (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean:229`). -/
theorem abstractExtensionFixedRepresentationUnitsEquiv_action
    (K L : ClosedSubgroup (Ω ≃ₐ[k] Ω))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (q : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
    (x : (extensionFixedRepresentation (galoisAmbientUnitsRep k Ω)
      K L hLK hnormal).V) :
    letI := hnormal
    abstractExtensionFixedRepresentationUnitsEquiv k Ω K L hLK hnormal
        ((extensionFixedRepresentation (galoisAmbientUnitsRep k Ω)
          K L hLK hnormal).ρ q x) =
      (galoisAmbientUnitsRep (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK)).ρ
          (abstractExtensionQuotientEquivGaloisGroup
            k Ω K L hLK hnormal q)
          (abstractExtensionFixedRepresentationUnitsEquiv
            k Ω K L hLK hnormal x) := by
  letI := hnormal
  let eFixed := abstractRelativeFixedFieldUnitsEquivGaloisFixed
    k Ω K L hLK
  apply eFixed.injective
  rw [abstractRelativeUnitsEquiv_extensionUnitsEquiv]
  apply Subtype.ext
  apply Additive.ext
  apply Units.ext
  have haction := extensionFixedRepresentation_action_coe
    (galoisAmbientUnitsRep k Ω) K L hLK hnormal q x
  change
    ((Additive.toMul
      ((extensionFixedRepresentation (galoisAmbientUnitsRep k Ω)
        K L hLK hnormal).ρ q x).1 : Ωˣ) : Ω) = _
  rw [haction]
  rw [← abstractRelativeUnitsEquiv_extensionUnitsEquiv
    k Ω K L hLK hnormal x]
  exact relativeCosetAction_abstractRelativeFixedFieldUnit_val
    k Ω K L hLK hnormal
      (abstractExtensionFixedRepresentationUnitsEquiv
        k Ω K L hLK hnormal x) q

/-- **The descended representation is the reindexed unit representation** of
the concrete relative Galois extension (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean:271`). -/
def abstractExtensionFixedRepresentationIsoUnitsRes
    (K L : ClosedSubgroup (Ω ≃ₐ[k] Ω))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) :
    letI := hnormal
    extensionFixedRepresentation (galoisAmbientUnitsRep k Ω)
        K L hLK hnormal ≅
      Rep.res
        (abstractExtensionQuotientEquivGaloisGroup
          k Ω K L hLK hnormal).toMonoidHom
        (galoisAmbientUnitsRep (abstractFixedField k Ω K)
          (abstractRelativeFixedField k Ω hLK)) := by
  letI := hnormal
  let e := abstractExtensionFixedRepresentationUnitsEquiv
    k Ω K L hLK hnormal
  refine Rep.mkIso (Representation.Equiv.mk e.toIntLinearEquiv ?_)
  intro q
  apply LinearMap.ext
  intro x
  exact abstractExtensionFixedRepresentationUnitsEquiv_action
    k Ω K L hLK hnormal q x

end

end Atlas.Knowledge
