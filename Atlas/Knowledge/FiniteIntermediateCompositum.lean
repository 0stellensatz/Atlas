import Mathlib
import Atlas.Knowledge.FiniteIntermediateFieldRefinement
import Atlas.Knowledge.RelativeNormLaws

/-!
# composita of finite intermediate fields

The finite-stage closure facts the universal norm-descent lemma runs on:
the compositum of two finite intermediate fields — their intersection on
the Galois-group side — is again one, a finite intermediate field over a
base finite over the global base is itself finite over the global base,
the finite relative quotient has a recorded positive cardinality, and any
finite family of stages has a common finite overfield below a given one
(#104).

## Main definitions

* `FiniteIntermediateField.compositum` — the compositum of two finite
  intermediate fields.
* `FiniteIntermediateField.quotientCard` — the cardinality of the finite
  relative Galois quotient.

## Main statements

* `FiniteIntermediateField.absoluteFinite` — a finite intermediate field
  over a finite base is finite over the global base; proved.
* `FiniteIntermediateField.exists_common_compositum` — finitely many
  stages have a common finite overfield below a given one; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling, and
the compositum's finiteness over the base is #136's generalized form,
called without the containment the source passes. The cardinality and
common-compositum facts come from the source's second compositum file,
absorbed here rather than shipped as a near-namesake item.

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
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteIntermediateCompositum.lean:21`]
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
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteIntermediateCompositum.lean:34`]
[Yamaguchi2026]). -/
theorem compositum_le_left {E K : ClosedSubgroup G}
    (M N : FiniteIntermediateField E K) :
    (M.compositum N).field.toSubgroup ≤ M.field.toSubgroup :=
  inf_le_left

/-- The compositum lies below its right input ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteIntermediateCompositum.lean:40`]
[Yamaguchi2026]). -/
theorem compositum_le_right {E K : ClosedSubgroup G}
    (M N : FiniteIntermediateField E K) :
    (M.compositum N).field.toSubgroup ≤ N.field.toSubgroup :=
  inf_le_right

/-- **A finite intermediate field over a finite base is finite absolutely**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteIntermediateCompositum.lean:47`]
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

/-- **The cardinality of the finite relative Galois quotient** — recording
the bundled finiteness lets fixed-field constructions read it without a
second parameter ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteIntermediateFieldCompositum.lean:32`]
[Yamaguchi2026]). -/
noncomputable def quotientCard {E K : ClosedSubgroup G}
    (M : FiniteIntermediateField E K) : ℕ := by
  letI : Finite
      (K.toSubgroup ⧸ M.field.toSubgroup.subgroupOf K.toSubgroup) :=
    M.finite
  exact Nat.card
    (K.toSubgroup ⧸ M.field.toSubgroup.subgroupOf K.toSubgroup)

/-- The recorded cardinality is positive ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteIntermediateFieldCompositum.lean:40`]
[Yamaguchi2026]). -/
theorem quotientCard_pos {E K : ClosedSubgroup G}
    (M : FiniteIntermediateField E K) : 0 < M.quotientCard := by
  letI : Finite
      (K.toSubgroup ⧸ M.field.toSubgroup.subgroupOf K.toSubgroup) :=
    M.finite
  exact Nat.card_pos

/-- **Finitely many stages have a common finite overfield below a given
one** — existentially, avoiding an artificial ordering of the family
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteIntermediateFieldCompositum.lean:49`]
[Yamaguchi2026]). -/
theorem exists_common_compositum {E K : ClosedSubgroup G} {ι : Type*}
    (M : FiniteIntermediateField E K) (s : Finset ι)
    (F : ι → FiniteIntermediateField E K) :
    ∃ P : FiniteIntermediateField E K,
      P.field.toSubgroup ≤ M.field.toSubgroup ∧
        ∀ i ∈ s, P.field.toSubgroup ≤ (F i).field.toSubgroup := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨M, le_rfl, by simp⟩
  | @insert i s hi ih =>
      rcases ih with ⟨P, hPM, hPF⟩
      let Q := P.compositum (F i)
      refine ⟨Q, (P.compositum_le_left (F i)).trans hPM, ?_⟩
      intro j hj
      rw [Finset.mem_insert] at hj
      rcases hj with hji | hj
      · simpa [hji] using P.compositum_le_right (F i)
      · exact (P.compositum_le_left (F i)).trans (hPF j hj)

end FiniteIntermediateField

end

end Atlas.Knowledge
