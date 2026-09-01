import Mathlib
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.ResidueDatumIn

/-!
# fixed fields of abstract closed subgroups

The dictionary between the reciprocity engine's abstract fields — closed
subgroups of a Galois group — and actual intermediate fields of a Galois
extension: the fixed field of the subgroup, with the fixing-subgroup round
trip, the transfer of the engine's finiteness witness to finite-dimensionality
of the fixed field, and the identification of the subgroup with the Galois
group of the ambient extension over its fixed field. This is the
field-theoretic entry of the engine's local-side instantiation (#104).

## Main definitions

* `abstractFixedField` — the fixed field of an abstract closed subgroup.
* `abstractSubgroupEquivGaloisGroup` — the subgroup as the Galois group over
  its fixed field.

## Main statements

* `closedFixingSubgroup_abstractFixedField_eq` — the fixing subgroup of the
  fixed field recovers the subgroup; proved.
* `abstractFixedField_finiteDimensional` — the engine's finiteness witness
  makes the fixed field a finite extension; proved.

## Implementation notes

The engine's finiteness witness is spelled with `Subgroup.subgroupOf` against
`Atlas.Knowledge.baseField`, matching
`Atlas.Knowledge.FiniteAbstractField.finite`; the source's `extensionSubgroup`
is an abbreviation of the same subgroup. The closed fixing subgroup is
`Atlas.Knowledge.closedFixingSubgroup`, already in the layer with the residue
datum.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u v

variable (k : Type u) (Ω : Type v) [Field k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω]

/-- **The fixed field of an abstract closed subgroup** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:26`]
[Yamaguchi2026]). -/
abbrev abstractFixedField (H : ClosedSubgroup (Ω ≃ₐ[k] Ω)) :
    IntermediateField k Ω :=
  IntermediateField.fixedField H.toSubgroup

/-- **Passing to the fixed field and back recovers the subgroup**
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:32`]
[Yamaguchi2026]). -/
theorem closedFixingSubgroup_abstractFixedField_eq
    (H : ClosedSubgroup (Ω ≃ₐ[k] Ω)) :
    closedFixingSubgroup (abstractFixedField k Ω H) = H := by
  ext σ
  change σ ∈ (abstractFixedField k Ω H).fixingSubgroup ↔ σ ∈ H
  rw [InfiniteGalois.fixingSubgroup_fixedField H]
  rfl

omit [IsGalois k Ω] in
/-- **The engine's finiteness witness gives a finite ambient quotient**
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:43`]
[Yamaguchi2026]). -/
theorem ambientQuotientFiniteOfAbstractFinite
    (H : ClosedSubgroup (Ω ≃ₐ[k] Ω))
    (hfinite : Finite ((baseField (Ω ≃ₐ[k] Ω)).toSubgroup ⧸
      H.toSubgroup.subgroupOf (baseField (Ω ≃ₐ[k] Ω)).toSubgroup)) :
    Finite ((Ω ≃ₐ[k] Ω) ⧸ H.toSubgroup) := by
  apply Nat.finite_of_card_ne_zero
  change H.toSubgroup.index ≠ 0
  rw [← Subgroup.relIndex_top_right]
  change (H.toSubgroup.subgroupOf (baseField (Ω ≃ₐ[k] Ω)).toSubgroup).index ≠ 0
  exact Subgroup.index_ne_zero_of_finite

omit [IsGalois k Ω] in
/-- **An abstract field finite over the base is an open subgroup**
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:61`]
[Yamaguchi2026]). -/
theorem abstractFiniteClosedSubgroup_isOpen
    (H : ClosedSubgroup (Ω ≃ₐ[k] Ω))
    (hfinite : Finite ((baseField (Ω ≃ₐ[k] Ω)).toSubgroup ⧸
      H.toSubgroup.subgroupOf (baseField (Ω ≃ₐ[k] Ω)).toSubgroup)) :
    IsOpen H.carrier := by
  letI : Finite ((Ω ≃ₐ[k] Ω) ⧸ H.toSubgroup) :=
    ambientQuotientFiniteOfAbstractFinite k Ω H hfinite
  letI : Subgroup.FiniteIndex H.toSubgroup :=
    H.toSubgroup.finiteIndex_of_finite_quotient
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex H.toSubgroup H.isClosed'

/-- **The fixed field of an abstract field finite over the base is a finite
extension** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:74`]
[Yamaguchi2026]). -/
theorem abstractFixedField_finiteDimensional
    (H : ClosedSubgroup (Ω ≃ₐ[k] Ω))
    (hfinite : Finite ((baseField (Ω ≃ₐ[k] Ω)).toSubgroup ⧸
      H.toSubgroup.subgroupOf (baseField (Ω ≃ₐ[k] Ω)).toSubgroup)) :
    FiniteDimensional k (abstractFixedField k Ω H) := by
  apply (InfiniteGalois.isOpen_iff_finite
    (K := Ω) (abstractFixedField k Ω H)).1
  rw [InfiniteGalois.fixingSubgroup_fixedField H]
  exact abstractFiniteClosedSubgroup_isOpen k Ω H hfinite

omit [IsGalois k Ω] in
/-- Inclusion of abstract subgroups reverses to inclusion of fixed fields
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:87`]
[Yamaguchi2026]). -/
theorem abstractFixedField_le {K L : ClosedSubgroup (Ω ≃ₐ[k] Ω)}
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    abstractFixedField k Ω K ≤ abstractFixedField k Ω L :=
  IntermediateField.fixedField_le hLK

/-- **The subgroup is the Galois group over its fixed field**
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:94`]
[Yamaguchi2026]). -/
def abstractSubgroupEquivGaloisGroup
    (H : ClosedSubgroup (Ω ≃ₐ[k] Ω)) :
    H.toSubgroup ≃* (Ω ≃ₐ[abstractFixedField k Ω H] Ω) :=
  (MulEquiv.subgroupCongr
      (InfiniteGalois.fixingSubgroup_fixedField H).symm).trans
    (IntermediateField.fixingSubgroupEquiv (abstractFixedField k Ω H))

/-- The Galois-group reading acts as the original automorphism
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:103`]
[Yamaguchi2026]). -/
@[simp]
theorem abstractSubgroupEquivGaloisGroup_apply
    (H : ClosedSubgroup (Ω ≃ₐ[k] Ω)) (σ : H.toSubgroup) (x : Ω) :
    abstractSubgroupEquivGaloisGroup k Ω H σ x = σ.1 x :=
  rfl

end

end Atlas.Knowledge
