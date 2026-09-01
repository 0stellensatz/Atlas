import Mathlib
import Atlas.Knowledge.RelativeNorm

/-!
# norm subgroups for infinite extensions

The norm subgroup of a possibly infinite abstract extension `E | K`:
`N_{E|K} A_E = ⋂_M N_{M|K} A_M`, the intersection of the norm images from
all finite intermediate fields `M`, recorded literally as the construction
defines it. The quotient `A_K / N_{E|K} A_E` is an opaque public object:
clients reach it through the class map, the induction principle, and the
lift, never through the concrete quotient representation (#104).

## Main definitions

* `FiniteIntermediateField` — a finite intermediate field of an abstract
  extension, with the base field as the first example.
* `infiniteNormSubgroup` — the intersection of the finite-level norm
  images.
* `InfiniteNormQuotient` / `infiniteNormClass` /
  `infiniteNormQuotientLift` — the opaque quotient with its class map and
  its universal property.

## Main statements

* `mem_infiniteNormSubgroup_iff` — membership is being a norm from every
  finite level; proved.
* `infiniteNormClass_eq_zero_iff` / `infiniteNormClass_surjective` /
  `InfiniteNormQuotient.induction_on` — the class map's kernel and
  surjectivity, and the induction principle; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling, as
across the arc, and the base field's finiteness closes by
`Subgroup.subgroupOf_self` where the source builds the top identity by
hand.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **A finite intermediate field `M` of an abstract extension `E | K`**:
contravariantly, its subgroup lies between `G_E` and `G_K`
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:28`]
[Yamaguchi2026]). -/
structure FiniteIntermediateField (E K : ClosedSubgroup G) where
  /-- The closed subgroup representing the intermediate field. -/
  field : ClosedSubgroup G
  /-- The extension endpoint lies below the intermediate-field subgroup. -/
  above : E.toSubgroup ≤ field.toSubgroup
  /-- The intermediate-field subgroup lies below the base endpoint. -/
  below : field.toSubgroup ≤ K.toSubgroup
  /-- The intermediate field has finite degree over the base endpoint. -/
  finite : Finite
    (K.toSubgroup ⧸ field.toSubgroup.subgroupOf K.toSubgroup)

namespace FiniteIntermediateField

/-- The base field itself is a finite intermediate field ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:42`]
[Yamaguchi2026]). -/
def base (E K : ClosedSubgroup G) (hEK : E.toSubgroup ≤ K.toSubgroup) :
    FiniteIntermediateField E K where
  field := K
  above := hEK
  below := le_rfl
  finite := by
    rw [Subgroup.subgroupOf_self]
    infer_instance

end FiniteIntermediateField

/-- The norm image from a finite intermediate field `M` to `K`
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:68`]
[Yamaguchi2026]). -/
def finiteIntermediateNormRange
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    (M : FiniteIntermediateField E K) :
    AddSubgroup (ambientFixedAddSubgroup A K) := by
  letI := M.finite
  exact (relativeNorm A K M.field M.below).range

/-- **The norm subgroup of a possibly infinite extension**:
`N_{E|K} A_E = ⋂_M N_{M|K} A_M` over the finite intermediate fields
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:78`]
[Yamaguchi2026]). -/
def infiniteNormSubgroup
    (A : Rep ℤ G) (E K : ClosedSubgroup G) :
    AddSubgroup (ambientFixedAddSubgroup A K) :=
  ⨅ M : FiniteIntermediateField E K,
    finiteIntermediateNormRange A E K M

/-- **Membership in the infinite norm subgroup is being a norm from every
finite level** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:86`]
[Yamaguchi2026]). -/
@[simp]
theorem mem_infiniteNormSubgroup_iff
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) :
    a ∈ infiniteNormSubgroup A E K ↔
      ∀ M : FiniteIntermediateField E K,
        a ∈ finiteIntermediateNormRange A E K M := by
  simp [infiniteNormSubgroup]

/-- **The quotient `A_K / N_{E|K} A_E` the reciprocity map lands in** —
opaque: clients use `infiniteNormClass`,
`InfiniteNormQuotient.induction_on`, or `infiniteNormQuotientLift`, never
the concrete quotient representation ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:99`]
[Yamaguchi2026]). -/
def InfiniteNormQuotient
    (A : Rep ℤ G) (E K : ClosedSubgroup G) :=
  ambientFixedAddSubgroup A K ⧸ infiniteNormSubgroup A E K

/-- The additive group structure on the infinite norm quotient
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:104`]
[Yamaguchi2026]). -/
instance infiniteNormQuotientAddCommGroup
    (A : Rep ℤ G) (E K : ClosedSubgroup G) :
    AddCommGroup (InfiniteNormQuotient A E K) := by
  unfold InfiniteNormQuotient
  infer_instance

/-- The explicit boundary to the concrete quotient implementation
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:111`]
[Yamaguchi2026]). -/
def infiniteNormQuotientConcreteEquiv
    (A : Rep ℤ G) (E K : ClosedSubgroup G) :
    InfiniteNormQuotient A E K ≃+
      ambientFixedAddSubgroup A K ⧸ infiniteNormSubgroup A E K := by
  unfold InfiniteNormQuotient
  exact AddEquiv.refl _

/-- **The canonical class map into the infinite norm quotient**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:119`]
[Yamaguchi2026]). -/
def infiniteNormClass
    (A : Rep ℤ G) (E K : ClosedSubgroup G) :
    ambientFixedAddSubgroup A K →+
      InfiniteNormQuotient A E K := by
  unfold InfiniteNormQuotient
  exact QuotientAddGroup.mk' (infiniteNormSubgroup A E K)

/-- The concrete equivalence sends a class to its quotient class. -/
@[simp]
theorem infiniteNormQuotientConcreteEquiv_infiniteNormClass
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) :
    infiniteNormQuotientConcreteEquiv A E K (infiniteNormClass A E K a) =
      QuotientAddGroup.mk' (infiniteNormSubgroup A E K) a := by
  rfl

/-- **A norm class vanishes exactly on the norm subgroup**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:138`]
[Yamaguchi2026]). -/
@[simp]
theorem infiniteNormClass_eq_zero_iff
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) :
    infiniteNormClass A E K a = 0 ↔
      a ∈ infiniteNormSubgroup A E K := by
  unfold infiniteNormClass InfiniteNormQuotient
  exact QuotientAddGroup.eq_zero_iff a

/-- **Every norm-quotient class has an ambient representative**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:147`]
[Yamaguchi2026]). -/
theorem infiniteNormClass_surjective
    (A : Rep ℤ G) (E K : ClosedSubgroup G) :
    Function.Surjective (infiniteNormClass A E K) := by
  intro q
  obtain ⟨a, rfl⟩ :=
    QuotientAddGroup.mk'_surjective (infiniteNormSubgroup A E K) q
  exact ⟨a, rfl⟩

/-- **Eliminate a norm-quotient class through an ambient representative**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:158`]
[Yamaguchi2026]). -/
@[elab_as_elim]
theorem InfiniteNormQuotient.induction_on
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    {motive : InfiniteNormQuotient A E K → Prop}
    (q : InfiniteNormQuotient A E K)
    (h : ∀ a, motive (infiniteNormClass A E K a)) : motive q := by
  obtain ⟨a, rfl⟩ := infiniteNormClass_surjective A E K q
  exact h a

/-- **Descend an additive homomorphism that kills the norm subgroup**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:167`]
[Yamaguchi2026]). -/
def infiniteNormQuotientLift
    {B : Type*} [AddCommGroup B]
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : infiniteNormSubgroup A E K ≤ f.ker) :
    InfiniteNormQuotient A E K →+ B := by
  unfold InfiniteNormQuotient
  exact QuotientAddGroup.lift (infiniteNormSubgroup A E K) f hf

/-- Lifting the canonical class recovers the representative's value. -/
@[simp]
theorem infiniteNormQuotientLift_infiniteNormClass
    {B : Type*} [AddCommGroup B]
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : infiniteNormSubgroup A E K ≤ f.ker)
    (a : ambientFixedAddSubgroup A K) :
    infiniteNormQuotientLift A E K f hf (infiniteNormClass A E K a) =
      f a := by
  rfl

end

end Atlas.Knowledge
