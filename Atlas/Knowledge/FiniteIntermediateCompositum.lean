import Mathlib
import Atlas.Knowledge.FiniteIntermediateFieldRefinement
import Atlas.Knowledge.RelativeNormLaws

/-!
# composita of finite intermediate fields

The finite-stage closure facts the universal norm-descent lemma runs on:
the compositum of two finite intermediate fields — their intersection on
the Galois-group side — is again one, and a finite intermediate field over
a base finite over the global base is itself finite over the global base
(#104).

## Main definitions

* `FiniteIntermediateField.compositum` — the compositum of two finite
  intermediate fields.

## Main statements

* `FiniteIntermediateField.absoluteFinite` — a finite intermediate field
  over a finite base is finite over the global base; proved.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- **The compositum of two finite intermediate fields of `E | K`**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteIntermediateCompositum.lean:22`]
[Yamaguchi2026]). -/
def compositum {E K : ClosedSubgroup G}
    (M N : FiniteIntermediateField E K) :
    FiniteIntermediateField E K where
  field := M.field ⊓ N.field
  above := fun x hx => ⟨M.above hx, N.above hx⟩
  below := (inf_le_left :
    (M.field ⊓ N.field).toSubgroup ≤ M.field.toSubgroup).trans M.below
  finite := by
    letI : Finite
        (K.toSubgroup ⧸ N.field.toSubgroup.subgroupOf K.toSubgroup) :=
      N.finite
    exact M.compositumWith_finite_over_base N.field

/-- The compositum lies below its left input ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteIntermediateCompositum.lean:35`]
[Yamaguchi2026]). -/
theorem compositum_le_left {E K : ClosedSubgroup G}
    (M N : FiniteIntermediateField E K) :
    (M.compositum N).field.toSubgroup ≤ M.field.toSubgroup :=
  inf_le_left

/-- The compositum lies below its right input ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteIntermediateCompositum.lean:41`]
[Yamaguchi2026]). -/
theorem compositum_le_right {E K : ClosedSubgroup G}
    (M N : FiniteIntermediateField E K) :
    (M.compositum N).field.toSubgroup ≤ N.field.toSubgroup :=
  inf_le_right

/-- **A finite intermediate field over a finite base is finite over the
global base** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteIntermediateCompositum.lean:48`]
[Yamaguchi2026]). -/
theorem absoluteFinite {E K : ClosedSubgroup G}
    [hKfinite : Finite ((baseField G).toSubgroup ⧸
      K.toSubgroup.subgroupOf (baseField G).toSubgroup)]
    (M : FiniteIntermediateField E K) :
    Finite ((baseField G).toSubgroup ⧸
      M.field.toSubgroup.subgroupOf (baseField G).toSubgroup) := by
  letI : Finite
      (K.toSubgroup ⧸ M.field.toSubgroup.subgroupOf K.toSubgroup) :=
    M.finite
  exact relativeTowerQuotientFinite (baseField G) K M.field M.below
    (le_baseField K)

end FiniteIntermediateField

end

end Atlas.Knowledge
