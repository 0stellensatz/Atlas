import Mathlib
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.GaloisExtensionQuotient
import Atlas.Knowledge.IntermediateFieldUnitsFixedSubgroup
import Atlas.Knowledge.ResidueDatumIn

/-!
# intrinsic absolute Galois data

The absolute Galois group of a field, its integral unit
representation, and its distinguished abstract base field, all formed
from the field's chosen separable closure — the packaging under which
the abstract reciprocity engine is instantiated on an actual field
(#104).

## Main definitions

* `intrinsicAbsoluteGalois` — the absolute Galois group over the
  chosen separable closure.
* `intrinsicAbsoluteUnits` — its integral representation on the
  separable closure's units.
* `intrinsicAbstractBase` — the base subgroup as the bottom fixing
  subgroup.
* `intrinsicAbstractBaseEquivAbsolute` — the base-to-absolute
  equivalence.
* `intrinsicFiniteAbstractBase` — the base packaged as a finite
  abstract field.

## Main statements

* `intrinsicFiniteAbstractBase_eq_base` — the finite intrinsic base is
  the engine's distinguished base; proved.

## Implementation notes

The Galois group is spelled
`SeparableClosure F ≃ₐ[F] SeparableClosure F` — the layer does not use
Mathlib's `Gal(E/F)` notation, a pure syntactic expansion of the same
type — and `SeparableClosure` is Mathlib's. `closedFixingSubgroup`
takes only the intermediate field, its ambient pair implicit in the
layer where the source passes `F (SeparableClosure F)` explicitly.
Everything else ports token-for-token; the file is the source's
`LocalReciprocity/IntrinsicAbsoluteData.lean`.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

/-- The absolute Galois group of a field, formed using its chosen
separable closure (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/IntrinsicAbsoluteData.lean:20`). -/
abbrev intrinsicAbsoluteGalois
    (F : Type u) [Field F] :=
  SeparableClosure F ≃ₐ[F] SeparableClosure F

/-- The integral representation of the intrinsic absolute Galois group
on the units of the chosen separable closure (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/IntrinsicAbsoluteData.lean:26`). -/
abbrev intrinsicAbsoluteUnits
    (F : Type u) [Field F] :
    Rep ℤ (intrinsicAbsoluteGalois F) :=
  galoisAmbientUnitsRep F (SeparableClosure F)

/-- The closed base subgroup of the intrinsic absolute Galois group,
expressed as the fixing subgroup of the bottom intermediate field
(Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/IntrinsicAbsoluteData.lean:33`). -/
abbrev intrinsicAbstractBase
    (F : Type u) [Field F] :
    ClosedSubgroup (intrinsicAbsoluteGalois F) :=
  closedFixingSubgroup (⊥ : IntermediateField F (SeparableClosure F))

/-- The canonical equivalence from the intrinsic abstract base
subgroup to the full absolute Galois group (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/IntrinsicAbsoluteData.lean:41`). -/
noncomputable def intrinsicAbstractBaseEquivAbsolute
    (F : Type u) [Field F] :
    (intrinsicAbstractBase F).toSubgroup ≃*
      intrinsicAbsoluteGalois F :=
  (MulEquiv.subgroupCongr (by
    rw [intrinsicAbstractBase,
      closedFixingSubgroup_bot_eq_baseField,
      baseField_toSubgroup])).trans Subgroup.topEquiv

/-- The inverse intrinsic-base equivalence has underlying automorphism
equal to the supplied absolute Galois automorphism (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/IntrinsicAbsoluteData.lean:53`). -/
@[simp]
theorem intrinsicAbstractBaseEquivAbsolute_symm_apply_val
    (F : Type u) [Field F] (σ : intrinsicAbsoluteGalois F) :
    ((intrinsicAbstractBaseEquivAbsolute F).symm σ).1 = σ := by
  simp [intrinsicAbstractBaseEquivAbsolute]

/-- **The intrinsic abstract base packaged as a finite abstract
field**; its defining quotient is the trivial finite quotient
(Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/IntrinsicAbsoluteData.lean:61`). -/
@[reducible]
noncomputable def intrinsicFiniteAbstractBase
    (F : Type u) [Field F] :
    FiniteAbstractField (intrinsicAbsoluteGalois F) where
  field := intrinsicAbstractBase F
  finite := by
    rw [intrinsicAbstractBase, closedFixingSubgroup_bot_eq_baseField]
    exact (FiniteAbstractField.base (intrinsicAbsoluteGalois F)).finite

/-- The finite intrinsic base is the distinguished finite base of the
abstract class formation (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/IntrinsicAbsoluteData.lean:72`). -/
@[simp]
theorem intrinsicFiniteAbstractBase_eq_base
    (F : Type u) [Field F] :
    intrinsicFiniteAbstractBase F =
      FiniteAbstractField.base (intrinsicAbsoluteGalois F) := by
  have h := closedFixingSubgroup_bot_eq_baseField F (SeparableClosure F)
  change intrinsicAbstractBase F =
    baseField (intrinsicAbsoluteGalois F) at h
  exact FiniteAbstractField.eq_of_field_eq _ _ h

end

end Atlas.Knowledge
