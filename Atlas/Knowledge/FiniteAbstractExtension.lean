import Mathlib
import Atlas.Knowledge.AbstractExtension

/-!
# finite abstract extension

An abstract extension carrying finiteness of its relative coset space, so that
its invariants are genuinely positive naturals: the degree, the relative residue
degree, and the relative ramification index, with the finite fundamental
identity `[L : K] = f · e` over `ℕ`. Finiteness of the residue and ramification
quotients is *derived* from the cardinal fundamental identity — the argument the
natural-valued convention cannot make, since `0 = 0 * 0` — and the cardinal
invariants specialize to the positive naturals at this boundary.

## Main definitions

* `FiniteAbstractExtension` — the extension with its finiteness certificate,
  its `quotient`, and `FiniteAbstractExtension.ofInclusion` to bundle one.
* `FiniteAbstractExtension.degree` / `FiniteAbstractExtension.residueDegree` /
  `FiniteAbstractExtension.ramificationIndex` — the three positive invariants.
* `FiniteAbstractExtension.IsUnramified` /
  `FiniteAbstractExtension.IsTotallyRamified` — through the underlying
  extension.

## Main statements

* `FiniteAbstractExtension.residueQuotientFinite` /
  `FiniteAbstractExtension.ramificationQuotientFinite` — finiteness of the
  residue and inertia quotients, from the cardinal identity; proved.
* `FiniteAbstractExtension.degree_eq_residueDegree_mul_ramificationIndex` — the
  finite fundamental identity; proved.
* `FiniteAbstractExtension.isTotallyRamified_iff_residueDegree_eq_one` and the
  unramified/totally-ramified degeneracies; proved.
* `FiniteAbstractExtension.degreeCardinal_eq_coe` and its residue and
  ramification siblings — the cardinal invariants specialize; proved.

## Implementation notes

`relativeResidueDegreeCardinal_lt_aleph0` is public here where the source keeps
it private: the residue-field bundles in the sibling files consume it across
the file boundary the source does not have; its ramification sibling stays
private. The relative subgroup is `Subgroup.subgroupOf`, as across the layer,
and the source's `extensionSubgroup_index_eq_degree` is named
`subgroup_index_eq_degree` for it. The additive reading of the Galois
quotient's order, `additiveExtensionQuotient_card`, lives here with the
degree it computes, though the source keeps it beside the norm quotients.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **A finite abstract extension**: finiteness of the relative coset space is
carried by the object, so the numerical invariants are positive naturals rather
than the raw index convention encoding infinity as zero (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Fields.lean:552`). -/
structure FiniteAbstractExtension (G : Type*) [Group G] [TopologicalSpace G]
    extends AbstractExtension G where
  /-- The relative quotient of the base subgroup by the extension subgroup is
  finite. -/
  finiteQuotient :
    Finite
      (toAbstractExtension.base.toSubgroup ⧸
        toAbstractExtension.field.toSubgroup.subgroupOf
          toAbstractExtension.base.toSubgroup)

namespace FiniteAbstractExtension

variable (E : FiniteAbstractExtension G)

/-- The subgroup of the base represented by a finite extension. -/
def subgroup : Subgroup E.base.toSubgroup :=
  E.field.toSubgroup.subgroupOf E.base.toSubgroup

/-- The finite extension's relative coset space. -/
def quotient : Type u :=
  E.base.toSubgroup ⧸ E.subgroup

/-- Bundle an inclusion whose relative coset type is known finite — the
canonical boundary from subgroup data to the finite extension API
(Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:577`). -/
def ofInclusion (field base : ClosedSubgroup G)
    (below : field.toSubgroup ≤ base.toSubgroup)
    [hfinite : Finite
      (base.toSubgroup ⧸ field.toSubgroup.subgroupOf base.toSubgroup)] :
    FiniteAbstractExtension G where
  field := field
  base := base
  below := below
  finiteQuotient := hfinite

/-- The field endpoint of a bundled inclusion is the supplied field. -/
@[simp] theorem ofInclusion_field (field base : ClosedSubgroup G)
    (below : field.toSubgroup ≤ base.toSubgroup)
    [Finite (base.toSubgroup ⧸ field.toSubgroup.subgroupOf base.toSubgroup)] :
    (ofInclusion field base below).field = field :=
  rfl

/-- The base endpoint of a bundled inclusion is the supplied base. -/
@[simp] theorem ofInclusion_base (field base : ClosedSubgroup G)
    (below : field.toSubgroup ≤ base.toSubgroup)
    [Finite (base.toSubgroup ⧸ field.toSubgroup.subgroupOf base.toSubgroup)] :
    (ofInclusion field base below).base = base :=
  rfl

/-- Unramifiedness of a finite extension, through the underlying extension. -/
def IsUnramified (D : DegreeData G) : Prop :=
  E.toAbstractExtension.IsUnramified D

/-- Total ramification of a finite extension, through the underlying
extension. -/
def IsTotallyRamified (D : DegreeData G) : Prop :=
  E.toAbstractExtension.IsTotallyRamified D

/-- Finite-extension unramifiedness is that of the underlying extension. -/
@[simp] theorem isUnramified_iff (D : DegreeData G) :
    E.IsUnramified D ↔ E.toAbstractExtension.IsUnramified D :=
  Iff.rfl

/-- Finite-extension total ramification is that of the underlying extension. -/
@[simp] theorem isTotallyRamified_iff (D : DegreeData G) :
    E.IsTotallyRamified D ↔ E.toAbstractExtension.IsTotallyRamified D :=
  Iff.rfl

/-- The inertia-containment reading of unramifiedness. -/
theorem isUnramified_iff_inertia_le (D : DegreeData G) :
    E.IsUnramified D ↔
      E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ E.field.toSubgroup :=
  E.toAbstractExtension.isUnramified_iff_inertia_le D

/-- The image-containment reading of total ramification. -/
theorem isTotallyRamified_iff_image_le (D : DegreeData G) :
    E.IsTotallyRamified D ↔
      E.base.toSubgroup.map D.degree.toMonoidHom ≤
        E.field.toSubgroup.map D.degree.toMonoidHom :=
  E.toAbstractExtension.isTotallyRamified_iff_image_le D

/-- The coset space of a finite abstract extension is finite. -/
instance quotientFinite : Finite E.quotient := by
  simpa [quotient, subgroup] using E.finiteQuotient

/-- The finite instance in the concrete quotient presentation. -/
instance representedQuotientFinite :
    Finite
      (E.base.toSubgroup ⧸
        E.field.toSubgroup.subgroupOf E.base.toSubgroup) :=
  E.finiteQuotient

private theorem degreeCardinal_lt_aleph0 :
    E.toAbstractExtension.degreeCardinal < Cardinal.aleph0 := by
  change Cardinal.mk
      (E.base.toSubgroup ⧸ E.field.toSubgroup.subgroupOf E.base.toSubgroup) <
    Cardinal.aleph0
  exact Cardinal.lt_aleph0_of_finite _

private theorem relativeDegreeCardinals_lt_aleph0 (D : DegreeData G) :
    Cardinal.lift.{u}
          (E.toAbstractExtension.relativeResidueDegreeCardinal D) <
        Cardinal.aleph0 ∧
      E.toAbstractExtension.relativeRamificationIndexCardinal D <
        Cardinal.aleph0 := by
  have hresidueUnlifted :
      E.toAbstractExtension.relativeResidueDegreeCardinal D ≠ 0 := by
    rw [AbstractExtension.relativeResidueDegreeCardinal,
      relativeIndexCardinal, intersectionIndexCardinal]
    exact Cardinal.mk_ne_zero _
  have hresidue :
      Cardinal.lift.{u}
          (E.toAbstractExtension.relativeResidueDegreeCardinal D) ≠ 0 := by
    intro hzero
    exact hresidueUnlifted (Cardinal.lift_eq_zero.mp hzero)
  have hramification :
      E.toAbstractExtension.relativeRamificationIndexCardinal D ≠ 0 := by
    rw [AbstractExtension.relativeRamificationIndexCardinal,
      relativeIndexCardinal, intersectionIndexCardinal]
    exact Cardinal.mk_ne_zero _
  apply (Cardinal.mul_lt_aleph0_iff_of_ne_zero hresidue hramification).mp
  have hiden := E.toAbstractExtension
    |>.degreeCardinal_eq_relativeResidueDegreeCardinal_mul_relativeRamificationIndexCardinal D
  rw [← hiden]
  exact E.degreeCardinal_lt_aleph0

/-- **The relative residue cardinal of a finite extension is finite** — from the
cardinal fundamental identity, the argument the zero convention cannot make;
public here because the residue-field bundles consume it across files
(Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:683`). -/
theorem relativeResidueDegreeCardinal_lt_aleph0 (D : DegreeData G) :
    E.toAbstractExtension.relativeResidueDegreeCardinal D <
      Cardinal.aleph0 :=
  Cardinal.lift_lt_aleph0.mp (E.relativeDegreeCardinals_lt_aleph0 D).1

/- The relative ramification cardinal of a finite extension is finite. -/
private theorem relativeRamificationIndexCardinal_lt_aleph0 (D : DegreeData G) :
    E.toAbstractExtension.relativeRamificationIndexCardinal D <
      Cardinal.aleph0 :=
  (E.relativeDegreeCardinals_lt_aleph0 D).2

/-- **The residue coset type of a finite extension is finite** — derived from
the cardinal fundamental identity, not from a natural-valued index
(Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:698`). -/
instance residueQuotientFinite (D : DegreeData G) :
    Finite
      (↥(E.base.toSubgroup.map D.degree.toMonoidHom) ⧸
        (E.field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
          (E.base.toSubgroup.map D.degree.toMonoidHom)) := by
  apply Cardinal.lt_aleph0_iff_finite.mp
  simpa [AbstractExtension.relativeResidueDegreeCardinal,
    relativeIndexCardinal, intersectionIndexCardinal] using
      E.relativeResidueDegreeCardinal_lt_aleph0 D

/-- The inertia coset type of a finite extension is finite, likewise from the
cardinal identity. -/
instance ramificationQuotientFinite (D : DegreeData G) :
    Finite
      (↥(E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) ⧸
        (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker).subgroupOf
          (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker)) := by
  apply Cardinal.lt_aleph0_iff_finite.mp
  simpa [AbstractExtension.relativeRamificationIndexCardinal,
    relativeIndexCardinal, intersectionIndexCardinal] using
      E.relativeRamificationIndexCardinal_lt_aleph0 D

/-- **The positive degree** of a finite abstract extension
(Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Fields.lean:721`). -/
noncomputable def degree : ℕ+ := by
  letI : Nonempty E.quotient := ⟨QuotientGroup.mk 1⟩
  exact ⟨Nat.card E.quotient, Nat.card_pos⟩

/-- **The positive relative residue degree**
(Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Fields.lean:728`). -/
noncomputable def residueDegree (D : DegreeData G) : ℕ+ :=
  ⟨Nat.card
      (↥(E.base.toSubgroup.map D.degree.toMonoidHom) ⧸
        (E.field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
          (E.base.toSubgroup.map D.degree.toMonoidHom)),
    Nat.card_pos⟩

/-- **The positive relative ramification index**
(Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Fields.lean:736`). -/
noncomputable def ramificationIndex (D : DegreeData G) : ℕ+ :=
  ⟨Nat.card
      (↥(E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) ⧸
        (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker).subgroupOf
          (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker)),
    Nat.card_pos⟩

/-- The natural value of the degree is the quotient's cardinality. -/
@[simp] theorem degree_coe : (E.degree : ℕ) = Nat.card E.quotient :=
  rfl

/-- The natural value of the residue degree is the mapped-quotient cardinality. -/
@[simp] theorem residueDegree_coe (D : DegreeData G) :
    (E.residueDegree D : ℕ) =
      Nat.card
        (↥(E.base.toSubgroup.map D.degree.toMonoidHom) ⧸
          (E.field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
            (E.base.toSubgroup.map D.degree.toMonoidHom)) :=
  rfl

/-- The natural value of the ramification index is the inertia-quotient
cardinality. -/
@[simp] theorem ramificationIndex_coe (D : DegreeData G) :
    (E.ramificationIndex D : ℕ) =
      Nat.card
        (↥(E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) ⧸
          (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker).subgroupOf
            (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker)) :=
  rfl

/-- The subgroup relative index is the positive degree — a finite-only bridge. -/
@[simp] theorem relIndex_eq_degree :
    E.field.toSubgroup.relIndex E.base.toSubgroup = (E.degree : ℕ) := by
  rw [Subgroup.relIndex, Subgroup.index, E.degree_coe]
  rfl

/-- The index of the represented extension subgroup is the degree. -/
@[simp] theorem subgroup_index_eq_degree :
    (E.field.toSubgroup.subgroupOf E.base.toSubgroup).index = (E.degree : ℕ) := by
  rw [Subgroup.index, E.degree_coe]
  rfl

/-- The relative index of the mapped subgroups is the residue degree. -/
@[simp] theorem mapped_relIndex_eq_residueDegree (D : DegreeData G) :
    (E.field.toSubgroup.map D.degree.toMonoidHom).relIndex
        (E.base.toSubgroup.map D.degree.toMonoidHom) =
      (E.residueDegree D : ℕ) := by
  rw [Subgroup.relIndex, Subgroup.index, E.residueDegree_coe]

/-- The relative index inside the degree kernel is the ramification index. -/
@[simp] theorem inertia_relIndex_eq_ramificationIndex (D : DegreeData G) :
    (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker).relIndex
        (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) =
      (E.ramificationIndex D : ℕ) := by
  rw [Subgroup.relIndex, Subgroup.index, E.ramificationIndex_coe]

/-- **The finite fundamental identity** `[L : K] = f · e`, in the positive
invariants alone (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Fields.lean:799`). -/
theorem degree_eq_residueDegree_mul_ramificationIndex (D : DegreeData G) :
    (E.degree : ℕ) =
      (E.residueDegree D : ℕ) * (E.ramificationIndex D : ℕ) := by
  rw [← E.relIndex_eq_degree, ← E.mapped_relIndex_eq_residueDegree D,
    ← E.inertia_relIndex_eq_ramificationIndex D]
  exact relIndex_eq_map_relIndex_mul_inf_ker_relIndex
    D.degree.toMonoidHom E.below

/-- An unramified finite extension has ramification index one. -/
theorem ramificationIndex_eq_one_of_isUnramified (D : DegreeData G)
    (hE : E.IsUnramified D) :
    (E.ramificationIndex D : ℕ) = 1 := by
  rw [← E.inertia_relIndex_eq_ramificationIndex D, Subgroup.relIndex_eq_one]
  intro x hx
  exact ⟨hE hx, hx.2⟩

/-- A totally ramified finite extension has residue degree one. -/
theorem residueDegree_eq_one_of_isTotallyRamified (D : DegreeData G)
    (hE : E.IsTotallyRamified D) :
    (E.residueDegree D : ℕ) = 1 := by
  rw [← E.mapped_relIndex_eq_residueDegree D, Subgroup.relIndex_eq_one]
  exact hE

/-- **Residue degree one characterizes total ramification** — keeping callers on
the structural predicate rather than the image-index implementation
(Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:827`). -/
theorem isTotallyRamified_iff_residueDegree_eq_one (D : DegreeData G) :
    E.IsTotallyRamified D ↔ (E.residueDegree D : ℕ) = 1 := by
  constructor
  · exact E.residueDegree_eq_one_of_isTotallyRamified D
  · intro h
    rw [isTotallyRamified_iff_image_le]
    rw [← E.mapped_relIndex_eq_residueDegree D,
      Subgroup.relIndex_eq_one] at h
    exact h

/-- Constructing the structural predicate from the invariant. -/
theorem isTotallyRamified_of_residueDegree_eq_one (D : DegreeData G)
    (h : (E.residueDegree D : ℕ) = 1) : E.IsTotallyRamified D :=
  (E.isTotallyRamified_iff_residueDegree_eq_one D).2 h

/-- In an unramified finite extension, residue degree equals degree. -/
theorem residueDegree_eq_degree_of_isUnramified (D : DegreeData G)
    (hE : E.IsUnramified D) :
    (E.residueDegree D : ℕ) = (E.degree : ℕ) := by
  rw [E.degree_eq_residueDegree_mul_ramificationIndex D,
    E.ramificationIndex_eq_one_of_isUnramified D hE, mul_one]

/-- In a totally ramified finite extension, ramification index equals degree. -/
theorem ramificationIndex_eq_degree_of_isTotallyRamified (D : DegreeData G)
    (hE : E.IsTotallyRamified D) :
    (E.ramificationIndex D : ℕ) = (E.degree : ℕ) := by
  rw [E.degree_eq_residueDegree_mul_ramificationIndex D,
    E.residueDegree_eq_one_of_isTotallyRamified D hE, one_mul]

/-- The cardinal degree specializes to the positive degree. -/
@[simp] theorem degreeCardinal_eq_coe :
    E.toAbstractExtension.degreeCardinal = ((E.degree : ℕ) : Cardinal) := by
  change Cardinal.mk
      (E.base.toSubgroup ⧸ E.field.toSubgroup.subgroupOf E.base.toSubgroup) =
    (Nat.card
      (E.base.toSubgroup ⧸ E.field.toSubgroup.subgroupOf E.base.toSubgroup) :
        Cardinal)
  simpa [quotient, subgroup] using
    ((Nat.cast_card :
      (Nat.card E.quotient : Cardinal) = Cardinal.mk E.quotient).symm)

/-- The cardinal residue degree specializes to the positive residue degree. -/
@[simp] theorem relativeResidueDegreeCardinal_eq_coe (D : DegreeData G) :
    E.toAbstractExtension.relativeResidueDegreeCardinal D =
      ((E.residueDegree D : ℕ) : Cardinal) := by
  change Cardinal.mk
    (↥(E.base.toSubgroup.map D.degree.toMonoidHom) ⧸
      (E.field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
        (E.base.toSubgroup.map D.degree.toMonoidHom)) =
      (Nat.card
        (↥(E.base.toSubgroup.map D.degree.toMonoidHom) ⧸
          (E.field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
            (E.base.toSubgroup.map D.degree.toMonoidHom)) : Cardinal)
  exact (Nat.cast_card).symm

/-- The cardinal ramification index specializes to the positive one. -/
@[simp] theorem relativeRamificationIndexCardinal_eq_coe (D : DegreeData G) :
    E.toAbstractExtension.relativeRamificationIndexCardinal D =
      ((E.ramificationIndex D : ℕ) : Cardinal) := by
  change Cardinal.mk
    (↥(E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) ⧸
      (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker).subgroupOf
        (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker)) =
      (Nat.card
        (↥(E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) ⧸
          (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker).subgroupOf
            (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker)) : Cardinal)
  exact (Nat.cast_card).symm

end FiniteAbstractExtension

/-- **The additive Galois quotient has the degree as its order**
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/CyclicNormQuotient.lean:537`). -/
theorem additiveExtensionQuotient_card
    (E : FiniteAbstractExtension G) :
    Nat.card
        (Additive
          (E.base.toSubgroup ⧸
            E.field.toSubgroup.subgroupOf E.base.toSubgroup)) =
      (E.degree : ℕ) := by
  calc
    Nat.card
        (Additive
          (E.base.toSubgroup ⧸
            E.field.toSubgroup.subgroupOf E.base.toSubgroup)) =
        Nat.card
          (E.base.toSubgroup ⧸
            E.field.toSubgroup.subgroupOf E.base.toSubgroup) :=
      (Nat.card_congr
        (Additive.ofMul :
          (E.base.toSubgroup ⧸
              E.field.toSubgroup.subgroupOf E.base.toSubgroup) ≃
            Additive
              (E.base.toSubgroup ⧸
                E.field.toSubgroup.subgroupOf E.base.toSubgroup))).symm
    _ = (E.field.toSubgroup.subgroupOf E.base.toSubgroup).index :=
      (Subgroup.index_eq_card
        (E.field.toSubgroup.subgroupOf E.base.toSubgroup)).symm
    _ = (E.degree : ℕ) := E.subgroup_index_eq_degree

end Atlas.Knowledge
