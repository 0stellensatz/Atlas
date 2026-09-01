import Mathlib
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.ResidueDatumIn

/-!
# abstract quotients at the base fixing subgroup

The engine represents the ground field by the fixing subgroup of the bottom
intermediate field — the whole Galois group — and a Galois subextension `E/K`
by the subgroup fixing `E`. The engine's relative quotient at the base is
then canonically the ambient quotient by `Gal(Ω/E)`, and for a finite Galois
`E/K` the actual group `Gal(E/K)`. These are the identifications on which
the abstract norm of the ambient unit module is compared with the field norm
(#104).

## Main definitions

* `baseFixingExtensionQuotientEquivGaloisGroup` — the engine's quotient at
  the base is `Gal(E/K)`.

## Main statements

* `closedFixingSubgroup_bot_eq_baseField` — the bottom fixing subgroup is the
  engine's base field; proved.
* `baseFixingToAmbientQuotient_ker` — the kernel of the ambient quotient map
  is the engine's relative subgroup; proved.

## Implementation notes

The source records separately that its `extensionSubgroup` at the base is
`Subgroup.subgroupOf` of the ambient fixing subgroups; in the layer's
`subgroupOf` spelling that statement is the spelling itself, so it has no
counterpart here — and neither has the source's normality instance for the
relative presentation, which Mathlib's `Subgroup.normal_subgroupOf` already
provides. The remaining normality statement is an instance, keyed to
`Atlas.Knowledge.closedFixingSubgroup` applications.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u v

variable (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω]

/-- **The bottom fixing subgroup is the engine's base field**
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/GaloisExtensionQuotient.lean:25`]
[Yamaguchi2026]). -/
theorem closedFixingSubgroup_bot_eq_baseField :
    closedFixingSubgroup (⊥ : IntermediateField K Ω) =
      baseField (Ω ≃ₐ[K] Ω) := by
  ext σ
  change σ ∈ (⊥ : IntermediateField K Ω).fixingSubgroup ↔
    σ ∈ (⊤ : Subgroup (Ω ≃ₐ[K] Ω))
  rw [IntermediateField.fixingSubgroup_bot]

/-- The fixing subgroup of an intermediate field lies in the bottom fixing
subgroup ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/GaloisExtensionQuotient.lean:35`]
[Yamaguchi2026]). -/
theorem fixingSubgroupLeBase
    (E : IntermediateField K Ω) :
    (closedFixingSubgroup E).toSubgroup ≤
      (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup :=
  IntermediateField.fixingSubgroup_le bot_le

/-- The fixing subgroup of a Galois subextension is normal in the ambient
Galois group ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/GaloisExtensionQuotient.lean:54`]
[Yamaguchi2026]). -/
instance closedFixingSubgroup_normal
    (E : IntermediateField K Ω) [IsGalois K E] :
    (closedFixingSubgroup E).toSubgroup.Normal :=
  (InfiniteGalois.normal_iff_isGalois E).2 inferInstance

/-- Restriction to the ambient quotient by the fixing subgroup of `E`
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/GaloisExtensionQuotient.lean:71`]
[Yamaguchi2026]). -/
def baseFixingToAmbientQuotient
    (E : IntermediateField K Ω) [IsGalois K E] :
    (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup →*
      (Ω ≃ₐ[K] Ω) ⧸ (closedFixingSubgroup E).toSubgroup :=
  (QuotientGroup.mk' (closedFixingSubgroup E).toSubgroup).comp
    (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup.subtype

/-- **The kernel of the ambient quotient map is the engine's relative
subgroup** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/GaloisExtensionQuotient.lean:80`]
[Yamaguchi2026]). -/
theorem baseFixingToAmbientQuotient_ker
    (E : IntermediateField K Ω) [IsGalois K E] :
    (baseFixingToAmbientQuotient K Ω E).ker =
      (closedFixingSubgroup E).toSubgroup.subgroupOf
        (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup := by
  ext x
  change
    (QuotientGroup.mk' (closedFixingSubgroup E).toSubgroup x.1 = 1) ↔
      x.1 ∈ (closedFixingSubgroup E).toSubgroup
  exact QuotientGroup.eq_one_iff x.1

/-- The ambient quotient map is onto ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/GaloisExtensionQuotient.lean:95`]
[Yamaguchi2026]). -/
theorem baseFixingToAmbientQuotient_surjective
    (E : IntermediateField K Ω) [IsGalois K E] :
    Function.Surjective (baseFixingToAmbientQuotient K Ω E) := by
  intro q
  refine Quotient.inductionOn' q ?_
  intro σ
  have hσ :
      σ ∈ (closedFixingSubgroup
        (⊥ : IntermediateField K Ω)).toSubgroup := by
    change σ ∈ (⊥ : IntermediateField K Ω).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_bot]
    exact Subgroup.mem_top σ
  exact ⟨⟨σ, hσ⟩, rfl⟩

/-- **The engine's quotient at the base is the ambient quotient** by the
fixing subgroup of `E` ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/GaloisExtensionQuotient.lean:111`]
[Yamaguchi2026]). -/
def baseFixingExtensionQuotientEquivAmbient
    (E : IntermediateField K Ω) [IsGalois K E] :
    ((closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      (closedFixingSubgroup E).toSubgroup.subgroupOf
        (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup) ≃*
      (Ω ≃ₐ[K] Ω) ⧸ (closedFixingSubgroup E).toSubgroup :=
  (QuotientGroup.quotientMulEquivOfEq
      (baseFixingToAmbientQuotient_ker K Ω E).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (baseFixingToAmbientQuotient K Ω E)
      (baseFixingToAmbientQuotient_surjective K Ω E))

/-- The ambient reading acts on representatives ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/GaloisExtensionQuotient.lean:126`]
[Yamaguchi2026]). -/
@[simp]
theorem baseFixingExtensionQuotientEquivAmbient_mk
    (E : IntermediateField K Ω) [IsGalois K E]
    (σ : (closedFixingSubgroup
      (⊥ : IntermediateField K Ω)).toSubgroup) :
    baseFixingExtensionQuotientEquivAmbient K Ω E (QuotientGroup.mk σ) =
      QuotientGroup.mk σ.1 :=
  rfl

/-- **The engine's quotient at the base is `Gal(E/K)`** for a Galois
subextension ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/GaloisExtensionQuotient.lean:136`]
[Yamaguchi2026]). -/
def baseFixingExtensionQuotientEquivGaloisGroup
    (E : IntermediateField K Ω) [IsGalois K E] :
    ((closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      (closedFixingSubgroup E).toSubgroup.subgroupOf
        (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup) ≃*
      (E ≃ₐ[K] E) := by
  let H : ClosedSubgroup (Ω ≃ₐ[K] Ω) := closedFixingSubgroup E
  letI : H.toSubgroup.Normal := closedFixingSubgroup_normal K Ω E
  exact (baseFixingExtensionQuotientEquivAmbient K Ω E).trans
    ((InfiniteGalois.normalAutEquivQuotient H).trans
      (AlgEquiv.autCongr
        (IntermediateField.equivOfEq
          (InfiniteGalois.fixedField_fixingSubgroup E))))

end

end Atlas.Knowledge
