import Mathlib
import Atlas.Knowledge.InfiniteNormSubgroup

/-!
# refinements of finite intermediate fields

The two refinements the independence argument runs on: every finite
intermediate field of an extension with normal bottom admits a finite
Galois refinement — the field of the normal core of its subgroup — and any
finite intermediate field meets a finite extension of the base in a
compositum that is finite over both, normal over the second input when the
first is normal over the base. Contravariantly these are the normal core
and the intersection of subgroups, with the index bookkeeping that keeps
every quotient finite (#104).

## Main definitions

* `FiniteIntermediateField.normalCoreField` — the normal core, embedded
  back into the ambient group.
* `FiniteIntermediateField.galoisRefinement` — the finite Galois
  refinement of a finite intermediate field.
* `FiniteIntermediateField.compositumWith` — the compositum with a second
  field, as the intersection of subgroups.

## Main statements

* `FiniteIntermediateField.subgroupOf_normalCoreField` — the refinement's
  subgroup is the normal core; proved.
* `FiniteIntermediateField.compositumWith_finite` /
  `FiniteIntermediateField.compositumWith_finite_over_base` — the
  compositum is finite over the second input and over the base; proved.
* `FiniteIntermediateField.compositumWith_normal` — normality passes to
  the compositum; proved.
* `FiniteIntermediateField.finite_extension_of_le` — a finite extension of
  the base is finite over any intermediate field; proved.

## Implementation notes

The identity the source names `extensionSubgroup_normalCoreField` is
`subgroupOf_normalCoreField` here, after the spelling its statement uses —
the #133 precedent. The source's membership lemma at the relative subgroup
is Mathlib's `Subgroup.mem_subgroupOf`, and its closedness helper is the
inline preimage along the subtype inclusion. Two containment hypotheses the
source carries — the base containment in the compositum's finiteness over
the base, and the outer containment in `finite_extension_of_le` — are
unused in the `subgroupOf` spelling and dropped.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- **The normal core of a finite intermediate field**, embedded back into
the ambient absolute Galois group ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean:28`]
[Yamaguchi2026]). -/
def normalCoreField [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K) :
    ClosedSubgroup G where
  toSubgroup :=
    (M.field.toSubgroup.subgroupOf K.toSubgroup).normalCore.map
      K.toSubgroup.subtype
  isClosed' := by
    change IsClosed
      (Subtype.val ''
        ((M.field.toSubgroup.subgroupOf K.toSubgroup).normalCore :
          Set K.toSubgroup))
    exact K.isClosed'.isClosedEmbedding_subtypeVal.isClosedMap _
      ((M.field.toSubgroup.subgroupOf K.toSubgroup).normalCore_isClosed
        (M.field.isClosed'.preimage continuous_subtype_val))

/-- The normal core field lies below the base of the construction
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean:43`]
[Yamaguchi2026]). -/
theorem normalCoreField_le [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K) :
    (M.normalCoreField).toSubgroup ≤ K.toSubgroup := by
  rintro g ⟨k, _, rfl⟩
  exact k.2

/-- The normal core is contained in the field it refines
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean:50`]
[Yamaguchi2026]). -/
theorem normalCoreField_le_field [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K) :
    (M.normalCoreField).toSubgroup ≤ M.field.toSubgroup := by
  rintro g ⟨k, hk, rfl⟩
  exact Subgroup.mem_subgroupOf.1
    ((M.field.toSubgroup.subgroupOf K.toSubgroup).normalCore_le hk)

/-- **The refinement's subgroup is the normal core** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean:58`]
[Yamaguchi2026]). -/
theorem subgroupOf_normalCoreField [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K) :
    M.normalCoreField.toSubgroup.subgroupOf K.toSubgroup =
      (M.field.toSubgroup.subgroupOf K.toSubgroup).normalCore := by
  ext k
  constructor
  · intro hk
    obtain ⟨k', hk', hk'n⟩ := hk
    have hk'eq : k' = k := by
      apply Subtype.ext
      exact hk'n
    simpa [hk'eq] using hk'
  · intro hk
    exact ⟨k, hk, rfl⟩

/-- **The finite Galois refinement of a finite intermediate field**, once
the bottom extension is normal ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean:75`]
[Yamaguchi2026]). -/
def galoisRefinement [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    [hEnormal :
      (E.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    FiniteIntermediateField E K where
  field := M.normalCoreField
  above := by
    intro e he
    let eK : K.toSubgroup := ⟨e, M.below (M.above he)⟩
    have heE : eK ∈ E.toSubgroup.subgroupOf K.toSubgroup :=
      Subgroup.mem_subgroupOf.2 he
    have hle : E.toSubgroup.subgroupOf K.toSubgroup ≤
        M.field.toSubgroup.subgroupOf K.toSubgroup := by
      intro x hx
      apply Subgroup.mem_subgroupOf.2
      exact M.above (Subgroup.mem_subgroupOf.1 hx)
    have heCore : eK ∈
        (M.field.toSubgroup.subgroupOf K.toSubgroup).normalCore :=
      (Subgroup.normal_le_normalCore.mpr hle) heE
    exact ⟨eK, heCore, rfl⟩
  below := M.normalCoreField_le
  finite := by
    let H := M.field.toSubgroup.subgroupOf K.toSubgroup
    letI : Finite (K.toSubgroup ⧸ H) := M.finite
    letI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    letI : H.normalCore.FiniteIndex := inferInstance
    rw [M.subgroupOf_normalCoreField]
    infer_instance

/-- A Galois refinement lies below the field it refines ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean:105`]
[Yamaguchi2026]). -/
theorem galoisRefinement_le_field [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    [_hEnormal :
      (E.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    (M.galoisRefinement).field.toSubgroup ≤ M.field.toSubgroup :=
  M.normalCoreField_le_field

/-- The subgroup representing a Galois refinement is normal
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean:113`]
[Yamaguchi2026]). -/
instance galoisRefinement_normal [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    [hEnormal :
      (E.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    ((M.galoisRefinement).field.toSubgroup.subgroupOf
      K.toSubgroup).Normal := by
  change (M.normalCoreField.toSubgroup.subgroupOf K.toSubgroup).Normal
  rw [M.subgroupOf_normalCoreField]
  infer_instance

/-- **The field compositum `MΣ`**, contravariantly the intersection
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean:125`]
[Yamaguchi2026]). -/
def compositumWith
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    (S : ClosedSubgroup G) : ClosedSubgroup G :=
  M.field ⊓ S

/-- The compositum lies below its left input ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean:131`]
[Yamaguchi2026]). -/
theorem compositumWith_le_left
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    (S : ClosedSubgroup G) :
    (M.compositumWith S).toSubgroup ≤ M.field.toSubgroup :=
  inf_le_left

/-- The compositum lies below its right input ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean:138`]
[Yamaguchi2026]). -/
theorem compositumWith_le_right
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    (S : ClosedSubgroup G) :
    (M.compositumWith S).toSubgroup ≤ S.toSubgroup :=
  inf_le_right

/-- A field above both inputs lies above the compositum ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean:145`]
[Yamaguchi2026]). -/
theorem above_le_compositumWith
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    (S : ClosedSubgroup G) (hES : E.toSubgroup ≤ S.toSubgroup) :
    E.toSubgroup ≤ (M.compositumWith S).toSubgroup :=
  fun _ h => ⟨M.above h, hES h⟩

/-- **The compositum is finite over the second input** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean:152`]
[Yamaguchi2026]). -/
theorem compositumWith_finite
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    (S : ClosedSubgroup G) (hSK : S.toSubgroup ≤ K.toSubgroup) :
    Finite (S.toSubgroup ⧸
      (M.compositumWith S).toSubgroup.subgroupOf S.toSubgroup) := by
  letI : Finite (K.toSubgroup ⧸
      M.field.toSubgroup.subgroupOf K.toSubgroup) := M.finite
  have hMK : M.field.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have hinter := Subgroup.relIndex_inter_ne_zero hMK S.toSubgroup
  have hKinfS : K.toSubgroup ⊓ S.toSubgroup = S.toSubgroup :=
    inf_eq_right.mpr hSK
  rw [hKinfS] at hinter
  apply Nat.finite_of_card_ne_zero
  change ((M.compositumWith S).toSubgroup.subgroupOf S.toSubgroup).index ≠ 0
  have hsub : (M.compositumWith S).toSubgroup.subgroupOf S.toSubgroup =
      M.field.toSubgroup.subgroupOf S.toSubgroup := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    change (x.1 ∈ M.field.toSubgroup ∧ x.1 ∈ S.toSubgroup) ↔
      x.1 ∈ M.field.toSubgroup
    exact and_iff_left x.2
  rw [hsub]
  simpa [Subgroup.relIndex] using hinter

/-- **Normality passes to the compositum** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean:181`]
[Yamaguchi2026]). -/
theorem compositumWith_normal
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    (S : ClosedSubgroup G) (hSK : S.toSubgroup ≤ K.toSubgroup)
    [hMnormal : (M.field.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    ((M.compositumWith S).toSubgroup.subgroupOf S.toSubgroup).Normal := by
  constructor
  intro p hp s
  have hpP : p.1 ∈ (M.compositumWith S).toSubgroup :=
    Subgroup.mem_subgroupOf.1 hp
  let pK : K.toSubgroup := ⟨p.1, hSK p.2⟩
  let sK : K.toSubgroup := ⟨s.1, hSK s.2⟩
  have hpM : pK ∈ M.field.toSubgroup.subgroupOf K.toSubgroup :=
    Subgroup.mem_subgroupOf.2 hpP.1
  have hconjM : sK * pK * sK⁻¹ ∈
      M.field.toSubgroup.subgroupOf K.toSubgroup :=
    hMnormal.conj_mem pK hpM sK
  have hconjM' : s.1 * p.1 * s.1⁻¹ ∈ M.field.toSubgroup := by
    have := Subgroup.mem_subgroupOf.1 hconjM
    change (sK * pK * sK⁻¹).1 ∈ M.field.toSubgroup
    exact this
  apply Subgroup.mem_subgroupOf.2
  refine ⟨hconjM', ?_⟩
  exact S.toSubgroup.mul_mem
      (S.toSubgroup.mul_mem s.2 p.2) (S.toSubgroup.inv_mem s.2)

/-- **The compositum of two finite extensions of the base is finite over
the base** — contravariantly, the finite-index theorem for an intersection
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean:211`]
[Yamaguchi2026]). -/
theorem compositumWith_finite_over_base
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    (S : ClosedSubgroup G)
    [hSfinite : Finite (K.toSubgroup ⧸
      S.toSubgroup.subgroupOf K.toSubgroup)] :
    Finite (K.toSubgroup ⧸
      (M.compositumWith S).toSubgroup.subgroupOf K.toSubgroup) := by
  have hMindex : M.field.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    letI : Finite (K.toSubgroup ⧸
        M.field.toSubgroup.subgroupOf K.toSubgroup) := M.finite
    exact Subgroup.index_ne_zero_of_finite
  have hSindex : S.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  apply Nat.finite_of_card_ne_zero
  change ((M.compositumWith S).toSubgroup.subgroupOf K.toSubgroup).index ≠ 0
  have hsub : (M.compositumWith S).toSubgroup.subgroupOf K.toSubgroup =
      (M.field.toSubgroup ⊓ S.toSubgroup).subgroupOf K.toSubgroup := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    rfl
  rw [hsub]
  simpa only [Subgroup.relIndex] using
    Subgroup.relIndex_inf_ne_zero hMindex hSindex

/-- **A finite extension of the base is finite over any intermediate
field** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean:240`]
[Yamaguchi2026]). -/
theorem finite_extension_of_le
    {P M K : ClosedSubgroup G}
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    (hPM : P.toSubgroup ≤ M.toSubgroup)
    [hPfinite : Finite
      (K.toSubgroup ⧸ P.toSubgroup.subgroupOf K.toSubgroup)] :
    Finite (M.toSubgroup ⧸ P.toSubgroup.subgroupOf M.toSubgroup) := by
  have hPKindex : P.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have hPMindex : P.toSubgroup.relIndex M.toSubgroup ≠ 0 := by
    intro hzero
    have hmul := Subgroup.relIndex_mul_relIndex
      P.toSubgroup M.toSubgroup K.toSubgroup hPM hMK
    rw [hzero, zero_mul] at hmul
    exact hPKindex hmul.symm
  apply Nat.finite_of_card_ne_zero
  change (P.toSubgroup.subgroupOf M.toSubgroup).index ≠ 0
  simpa [Subgroup.relIndex] using hPMindex

end FiniteIntermediateField

end

end Atlas.Knowledge
