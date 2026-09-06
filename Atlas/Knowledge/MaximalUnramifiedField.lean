import Mathlib
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.InfiniteNormSubgroup

/-!
# maximal unramified field

The maximal unramified extension `L̃` of an abstract field, represented
contravariantly by the absolute inertia `I_L = G_L ∩ ker d`, with the order
laws its consumers need and the identification of its relative subgroup
inside a base with the relative inertia. On top of it, the norm subgroup
`N_{L̃|K} A_{L̃}` of the reciprocity construction — the infinite norm
subgroup for the maximal unramified field — and the opaque quotient
`A_K / N_{L̃|K} A_{L̃}` the reciprocity map lands in, with its class map,
induction principle, and universal property (#104).

## Main definitions

* `DegreeData.maximalUnramifiedField` — the maximal unramified extension,
  as the absolute inertia.
* `DegreeData.maximalUnramifiedNormSubgroup` — `N_{L̃|K} A_{L̃}`.
* `DegreeData.MaximalUnramifiedNormQuotient` /
  `DegreeData.maximalUnramifiedNormClass` /
  `DegreeData.maximalUnramifiedNormQuotientLift` — the opaque quotient
  with its class map and universal property.

## Main statements

* `DegreeData.subgroupOf_maximalUnramifiedField` — inside `G_K`, the
  subgroup of `L̃` is the relative inertia; proved.
* `DegreeData.maximalUnramifiedNormClass_eq_zero_iff` /
  `DegreeData.maximalUnramifiedNormClass_surjective` /
  `DegreeData.MaximalUnramifiedNormQuotient.induction_on` — the class
  map's kernel, surjectivity, and induction principle; proved.

## Implementation notes

The identities the source names `extensionSubgroup_maximalUnramifiedField`
and its normality corollary are `subgroupOf_maximalUnramifiedField` and
`subgroupOf_maximalUnramifiedField_normal` here, after the spelling their
statements use — the #133 precedent. The source's membership lemma at the
relative subgroup is Mathlib's `Subgroup.mem_subgroupOf`.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **The maximal unramified extension `L̃`**, represented by
`I_L = G_L ∩ ker d` (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:198`). -/
def maximalUnramifiedField (D : DegreeData G) (L : ClosedSubgroup G) :
    ClosedSubgroup G :=
  D.fieldInertia L

/-- The implementation boundary: the maximal unramified field is the
absolute inertia, and downstream code uses this theorem rather than
unfolding the definition. -/
theorem maximalUnramifiedField_eq_fieldInertia
    (D : DegreeData G) (L : ClosedSubgroup G) :
    D.maximalUnramifiedField L = D.fieldInertia L := by
  rfl

/-- Membership in the maximal unramified field is the inertia condition
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:213`). -/
@[simp]
theorem mem_maximalUnramifiedField_iff
    (D : DegreeData G) (L : ClosedSubgroup G) (g : G) :
    g ∈ D.maximalUnramifiedField L ↔ g ∈ L ∧ D.degree g = 1 := by
  rw [D.maximalUnramifiedField_eq_fieldInertia]
  exact D.mem_fieldInertia_iff L g

/-- The maximal unramified field extends its field (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:220`). -/
theorem maximalUnramifiedField_le (D : DegreeData G)
    (L : ClosedSubgroup G) :
    (D.maximalUnramifiedField L).toSubgroup ≤ L.toSubgroup := by
  rw [D.maximalUnramifiedField_eq_fieldInertia]
  exact inf_le_left

/-- The maximal unramified field extends any field its field extends
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:226`). -/
theorem maximalUnramifiedField_le_of_le (D : DegreeData G)
    {L K : ClosedSubgroup G} (hLK : L.toSubgroup ≤ K.toSubgroup) :
    (D.maximalUnramifiedField L).toSubgroup ≤ K.toSubgroup :=
  (D.maximalUnramifiedField_le L).trans hLK

/-- Monotonicity of maximal unramified fields (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:232`). -/
theorem maximalUnramifiedField_mono (D : DegreeData G)
    {K L : ClosedSubgroup G} (hLK : L.toSubgroup ≤ K.toSubgroup) :
    (D.maximalUnramifiedField L).toSubgroup ≤
      (D.maximalUnramifiedField K).toSubgroup := by
  intro g hg
  have hg' : g ∈ D.maximalUnramifiedField L := hg
  obtain ⟨hgL, hgd⟩ := (D.mem_maximalUnramifiedField_iff L g).1 hg'
  exact (D.mem_maximalUnramifiedField_iff K g).2 ⟨hLK hgL, hgd⟩

/-- **Inside `G_K`, the subgroup of `L̃` is the relative inertia**
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:243`). -/
theorem subgroupOf_maximalUnramifiedField (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup) :
    (D.maximalUnramifiedField L).toSubgroup.subgroupOf K.toSubgroup =
      D.extensionInertiaWithin K L hLK := by
  ext k
  constructor
  · intro hk
    have hkMax : k.1 ∈ D.maximalUnramifiedField L :=
      Subgroup.mem_subgroupOf.1 hk
    have hkData := (D.mem_maximalUnramifiedField_iff L k.1).1 hkMax
    exact ⟨Subgroup.mem_subgroupOf.2 hkData.1,
      (D.mem_fieldInertiaWithin_iff K k).2 hkData.2⟩
  · intro hk
    apply Subgroup.mem_subgroupOf.2
    apply (D.mem_maximalUnramifiedField_iff L k.1).2
    exact ⟨Subgroup.mem_subgroupOf.1 hk.1,
      (D.mem_fieldInertiaWithin_iff K k).1 hk.2⟩

/-- The subgroup of the maximal unramified field is normal in the base
subgroup (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:265`). -/
theorem subgroupOf_maximalUnramifiedField_normal (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    ((D.maximalUnramifiedField L).toSubgroup.subgroupOf
      K.toSubgroup).Normal := by
  rw [D.subgroupOf_maximalUnramifiedField K L hLK]
  infer_instance

/-- **The norm subgroup `N_{L̃|K} A_{L̃}` of the reciprocity construction**
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:285`). -/
def maximalUnramifiedNormSubgroup (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) :
    AddSubgroup (ambientFixedAddSubgroup A K) :=
  infiniteNormSubgroup A (D.maximalUnramifiedField L) K

/-- The maximal-unramified norm subgroup is the infinite norm subgroup for
the maximal unramified field. -/
theorem maximalUnramifiedNormSubgroup_eq_infiniteNormSubgroup
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G) :
    D.maximalUnramifiedNormSubgroup A K L =
      infiniteNormSubgroup A (D.maximalUnramifiedField L) K := by
  rfl

/-- Membership in the maximal-unramified norm subgroup, levelwise
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:300`). -/
@[simp]
theorem mem_maximalUnramifiedNormSubgroup_iff
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) :
    a ∈ D.maximalUnramifiedNormSubgroup A K L ↔
      a ∈ infiniteNormSubgroup A (D.maximalUnramifiedField L) K := by
  rw [D.maximalUnramifiedNormSubgroup_eq_infiniteNormSubgroup]

/-- **The quotient `A_K / N_{L̃|K} A_{L̃}`** — opaque, not a reducible alias
for the infinite norm quotient (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:311`). -/
def MaximalUnramifiedNormQuotient (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) :=
  InfiniteNormQuotient A (D.maximalUnramifiedField L) K

/-- The additive group structure on the maximal-unramified norm quotient
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:316`). -/
instance maximalUnramifiedNormQuotientAddCommGroup
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G) :
    AddCommGroup (D.MaximalUnramifiedNormQuotient A K L) := by
  unfold MaximalUnramifiedNormQuotient
  infer_instance

/-- The explicit boundary to the corresponding infinite norm quotient
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:323`). -/
def maximalUnramifiedNormQuotientInfiniteEquiv
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G) :
    D.MaximalUnramifiedNormQuotient A K L ≃+
      InfiniteNormQuotient A (D.maximalUnramifiedField L) K := by
  unfold MaximalUnramifiedNormQuotient
  exact AddEquiv.refl _

/-- **The canonical class map into the maximal-unramified norm quotient**
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:331`). -/
def maximalUnramifiedNormClass
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G) :
    ambientFixedAddSubgroup A K →+
      D.MaximalUnramifiedNormQuotient A K L := by
  unfold MaximalUnramifiedNormQuotient
  exact infiniteNormClass A (D.maximalUnramifiedField L) K

/-- The boundary equivalence preserves the canonical class. -/
@[simp]
theorem maximalUnramifiedNormQuotientInfiniteEquiv_maximalUnramifiedNormClass
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) :
    D.maximalUnramifiedNormQuotientInfiniteEquiv A K L
        (D.maximalUnramifiedNormClass A K L a) =
      infiniteNormClass A (D.maximalUnramifiedField L) K a := by
  rfl

/-- **A class vanishes exactly on the defining norm subgroup**
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:350`). -/
@[simp]
theorem maximalUnramifiedNormClass_eq_zero_iff
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) :
    D.maximalUnramifiedNormClass A K L a = 0 ↔
      a ∈ D.maximalUnramifiedNormSubgroup A K L := by
  unfold maximalUnramifiedNormClass MaximalUnramifiedNormQuotient
  exact infiniteNormClass_eq_zero_iff A (D.maximalUnramifiedField L) K a

/-- **Every class has an ambient representative** (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:359`). -/
theorem maximalUnramifiedNormClass_surjective
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G) :
    Function.Surjective (D.maximalUnramifiedNormClass A K L) := by
  intro q
  obtain ⟨a, ha⟩ :=
    infiniteNormClass_surjective A (D.maximalUnramifiedField L) K q
  exact ⟨a, ha⟩

/-- **Eliminate a class through an ambient representative**
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:370`). -/
@[elab_as_elim]
theorem MaximalUnramifiedNormQuotient.induction_on
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)
    {motive : D.MaximalUnramifiedNormQuotient A K L → Prop}
    (q : D.MaximalUnramifiedNormQuotient A K L)
    (h : ∀ a, motive (D.maximalUnramifiedNormClass A K L a)) :
    motive q := by
  obtain ⟨a, rfl⟩ := D.maximalUnramifiedNormClass_surjective A K L q
  exact h a

/-- **Descend a homomorphism that kills the norm subgroup**
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:379`). -/
def maximalUnramifiedNormQuotientLift
    {B : Type*} [AddCommGroup B]
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : D.maximalUnramifiedNormSubgroup A K L ≤ f.ker) :
    D.MaximalUnramifiedNormQuotient A K L →+ B := by
  unfold MaximalUnramifiedNormQuotient
  refine infiniteNormQuotientLift A (D.maximalUnramifiedField L) K f ?_
  intro a ha
  exact hf ((D.mem_maximalUnramifiedNormSubgroup_iff A K L a).2 ha)

/-- The lift sends a class back to its representative's value
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/NormSubgroup.lean:392`). -/
@[simp]
theorem maximalUnramifiedNormQuotientLift_maximalUnramifiedNormClass
    {B : Type*} [AddCommGroup B]
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : D.maximalUnramifiedNormSubgroup A K L ≤ f.ker)
    (a : ambientFixedAddSubgroup A K) :
    D.maximalUnramifiedNormQuotientLift A K L f hf
        (D.maximalUnramifiedNormClass A K L a) = f a := by
  unfold maximalUnramifiedNormQuotientLift maximalUnramifiedNormClass
    MaximalUnramifiedNormQuotient
  exact infiniteNormQuotientLift_infiniteNormClass
    A (D.maximalUnramifiedField L) K f (by
      intro b hb
      exact hf ((D.mem_maximalUnramifiedNormSubgroup_iff A K L b).2 hb)) a

end DegreeData

end

end Atlas.Knowledge
