import Mathlib
import Atlas.Knowledge.ProfiniteInteger
import Atlas.Knowledge.RelativeIndexCardinal

/-!
# degree datum

The opening datum of Neukirch-style abstract class field theory: a continuous
surjection `d : G →ₜ* ℤ̂` from the ambient profinite group, with a field
represented contravariantly by a closed subgroup and the base field by the full
group. From the datum alone: the inertia group `I = ker d`, the restricted degree
of a field, its degree image `d(G_K)` and inertia `I_K = G_K ⊓ I`, and the
absolute residue data — the quotient of `ℤ̂` by the degree image and its cardinal
size. This is the vocabulary every later engine brick (#104) speaks.

## Main definitions

* `ProfiniteIntegerMul` — `ℤ̂` written multiplicatively.
* `DegreeData` — the continuous surjective degree homomorphism.
* `baseField` — the full ambient subgroup, the contravariant base field.
* `DegreeData.inertia` / `DegreeData.fieldInertia` /
  `DegreeData.fieldInertiaWithin` — the degree kernel, absolutely, over a field,
  and inside it.
* `DegreeData.restrictedDegree` / `DegreeData.fieldImage` — the degree of a
  field and its image in `ℤ̂`.
* `DegreeData.residueQuotient` / `DegreeData.residueDegreeCardinal` — the
  absolute residue quotient and its cardinal size.

## Main statements

* `DegreeData.fieldImage_eq_map` — the image is the mapped subgroup; proved.
* `DegreeData.residueDegreeCardinal_baseField` — the base field has absolute
  residue degree one; proved.

## Implementation notes

Profinite hypotheses belong to the ambient group and are requested only by the
results that use them, never duplicated as fields of the datum. The membership
rules are `Iff.rfl`-level and marked `@[simp]`; the residue cardinal is the
`Atlas.Knowledge.relativeIndexCardinal` of the degree image in `⊤`, so the index
calculus applies to it verbatim, and its unfolding to the quotient's cardinality
is deliberately not a `simp` lemma — as one it would pre-empt the two computed
values. The residue quotient is stated before the cardinal that sizes it,
swapping the source's order.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

universe u

/-- **The profinite integers written multiplicatively**: multiplication here is
addition in `ℤ̂` (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Fields.lean:25`). -/
abbrev ProfiniteIntegerMul : Type := Multiplicative ProfiniteInteger

/-- **The degree datum**: a continuous surjection `d : G →ₜ* ℤ̂` on a topological
group — the opening datum of abstract class field theory (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Fields.lean:31`). -/
structure DegreeData (G : Type*) [Group G] [TopologicalSpace G] where
  /-- The continuous degree homomorphism to the profinite integers. -/
  degree : G →ₜ* ProfiniteIntegerMul
  /-- The degree homomorphism is surjective. -/
  degree_surjective : Function.Surjective degree

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **The base field**: represented contravariantly by the full ambient group
(Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:41`). -/
def baseField (G : Type u) [Group G] [TopologicalSpace G] : ClosedSubgroup G where
  toSubgroup := ⊤
  isClosed' := isClosed_univ

/-- The base field is represented by the full ambient subgroup. -/
@[simp]
theorem baseField_toSubgroup (G : Type u) [Group G] [TopologicalSpace G] :
    (baseField G).toSubgroup = ⊤ :=
  rfl

/-- Every abstract field lies over the base field. -/
theorem le_baseField (K : ClosedSubgroup G) :
    K.toSubgroup ≤ (baseField G).toSubgroup :=
  le_top

namespace DegreeData

/-- **The inertia group** `I = ker d`, closed because the degree is continuous
into a Hausdorff target (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Fields.lean:59`). -/
def inertia (D : DegreeData G) : ClosedSubgroup G where
  toSubgroup := D.degree.toMonoidHom.ker
  isClosed' := by
    change IsClosed {g : G | (D.degree g).toAdd = 0}
    exact isClosed_eq D.degree.continuous_toFun continuous_const

/-- An element is inertial exactly when its degree is the identity. -/
@[simp]
theorem mem_inertia_iff (D : DegreeData G) (g : G) :
    g ∈ D.inertia ↔ D.degree g = 1 :=
  Iff.rfl

/-- The degree restricted to the subgroup representing a field. -/
def restrictedDegree (D : DegreeData G) (K : ClosedSubgroup G) :
    K.toSubgroup →ₜ* ProfiniteIntegerMul where
  toMonoidHom := D.degree.toMonoidHom.comp K.toSubgroup.subtype
  continuous_toFun := D.degree.continuous_toFun.comp continuous_subtype_val

/-- The restricted degree evaluates through the ambient element. -/
@[simp]
theorem restrictedDegree_apply (D : DegreeData G) (K : ClosedSubgroup G)
    (k : K.toSubgroup) : D.restrictedDegree K k = D.degree k.1 :=
  rfl

/-- **The degree image** `d(G_K)` in `ℤ̂` (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Fields.lean:84`). -/
def fieldImage (D : DegreeData G) (K : ClosedSubgroup G) :
    Subgroup ProfiniteIntegerMul :=
  (D.restrictedDegree K).toMonoidHom.range

/-- The degree image is the mapped subgroup. -/
theorem fieldImage_eq_map (D : DegreeData G) (K : ClosedSubgroup G) :
    D.fieldImage K = K.toSubgroup.map D.degree.toMonoidHom := by
  ext z
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.1, k.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

/-- **The inertia group of a field** `I_K = G_K ⊓ I`
(Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Fields.lean:98`). -/
def fieldInertia (D : DegreeData G) (K : ClosedSubgroup G) : ClosedSubgroup G :=
  K ⊓ D.inertia

/-- Field inertia is the field elements of degree one. -/
@[simp]
theorem mem_fieldInertia_iff (D : DegreeData G) (K : ClosedSubgroup G) (g : G) :
    g ∈ D.fieldInertia K ↔ g ∈ K ∧ D.degree g = 1 :=
  Iff.rfl

/-- `I_K` viewed inside `G_K`: the kernel of the restricted degree. -/
def fieldInertiaWithin (D : DegreeData G) (K : ClosedSubgroup G) :
    Subgroup K.toSubgroup :=
  (D.restrictedDegree K).toMonoidHom.ker

/-- The internal field inertia is normal: it is a kernel. -/
instance fieldInertiaWithin_normal (D : DegreeData G) (K : ClosedSubgroup G) :
    (D.fieldInertiaWithin K).Normal := by
  rw [fieldInertiaWithin]
  infer_instance

/-- Membership in the internal field inertia is ambient degree one. -/
@[simp]
theorem mem_fieldInertiaWithin_iff (D : DegreeData G) (K : ClosedSubgroup G)
    (k : K.toSubgroup) : k ∈ D.fieldInertiaWithin K ↔ D.degree k.1 = 1 :=
  Iff.rfl

/-- **The absolute residue quotient** of a field: `ℤ̂` modulo the degree image
(Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:132`). -/
def residueQuotient (D : DegreeData G) (K : ClosedSubgroup G) : Type :=
  (⊤ : Subgroup ProfiniteIntegerMul) ⧸ (D.fieldImage K).subgroupOf ⊤

/-- **The absolute residue degree as a cardinal**: the index of the degree image
(Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:126`). -/
noncomputable def residueDegreeCardinal (D : DegreeData G)
    (K : ClosedSubgroup G) : Cardinal :=
  relativeIndexCardinal
    (show D.fieldImage K ≤ (⊤ : Subgroup ProfiniteIntegerMul) from le_top)

/-- The cardinal residue degree is the size of the residue quotient. -/
theorem residueDegreeCardinal_eq_mk_residueQuotient
    (D : DegreeData G) (K : ClosedSubgroup G) :
    D.residueDegreeCardinal K = Cardinal.mk (D.residueQuotient K) :=
  rfl

/-- **The base field has absolute residue degree one**: the degree is surjective,
so its image is everything (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Fields.lean:143`). -/
@[simp] theorem residueDegreeCardinal_baseField (D : DegreeData G) :
    D.residueDegreeCardinal (baseField G) = 1 := by
  change
    intersectionIndexCardinal (D.fieldImage (baseField G))
      (⊤ : Subgroup ProfiniteIntegerMul) = 1
  rw [D.fieldImage_eq_map, baseField_toSubgroup,
    Subgroup.map_top_of_surjective _ D.degree_surjective]
  change Cardinal.mk (↥(⊤ : Subgroup ProfiniteIntegerMul) ⧸ ⊤) = 1
  letI : Subsingleton (↥(⊤ : Subgroup ProfiniteIntegerMul) ⧸
      (⊤ : Subgroup ↥(⊤ : Subgroup ProfiniteIntegerMul))) := by
    constructor
    intro x y
    refine Quotient.inductionOn₂' x y ?_
    intro a b
    apply QuotientGroup.eq_iff_div_mem.mpr
    simp
  exact Cardinal.mk_eq_one _

end DegreeData

end Atlas.Knowledge
