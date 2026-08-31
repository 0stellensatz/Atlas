import Mathlib
import Atlas.Knowledge.DegreeData

/-!
# abstract field extension

An extension of abstract fields in the contravariant closed-subgroup model,
carrying the containment that makes `L / K` meaningful, with its cardinal-valued
invariants: the degree, the relative residue degree, and the relative
ramification index, each the cardinality of an actual coset type. The
cardinal-valued fundamental identity `[L : K] = f · e` and the Frobenius
compatibility `f_{L/K} · f_K = f_L` hold with no finiteness assumption, and
unramifiedness and total ramification are containments of subgroups, never
conditions on a natural-valued index. Towers multiply all three invariants.

## Main definitions

* `AbstractExtension` — the extension object, with `quotient`, `degreeCardinal`,
  `relativeResidueDegreeCardinal`, `relativeRamificationIndexCardinal`.
* `AbstractExtension.IsUnramified` / `AbstractExtension.IsTotallyRamified` —
  inertia contained in the field / degree images equal.
* `Tower` — three fields, two containments; the composable tower.

## Main statements

* `degreeCardinal_eq_relativeResidueDegreeCardinal_mul_relativeRamificationIndexCardinal`
  — the cardinal fundamental identity, in the `AbstractExtension` namespace like
  the rest; proved.
* `AbstractExtension.relativeResidueDegreeCardinal_mul_residueDegreeCardinal` —
  the Frobenius residue compatibility; proved.
* `AbstractExtension.relativeRamificationIndexCardinal_eq_one_of_isUnramified` /
  `AbstractExtension.relativeResidueDegreeCardinal_eq_one_of_isTotallyRamified`
  — the two degenerate invariants; proved.
* `Tower.degreeCardinal_mul` and its residue and ramification siblings — towers
  multiply; proved.

## Implementation notes

Every invariant is an `Atlas.Knowledge.relativeIndexCardinal`, so the fundamental
identity is the image–kernel splitting read at the degree homomorphism and the
tower laws are its multiplicativity; the universe lift on the residue factor is
forced by the image living over `ℤ̂`'s universe. The relative subgroup is spelled
`Subgroup.subgroupOf` directly, as in the sibling
`Atlas.Knowledge.extensionFixedRepresentation`.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **An abstract field extension**: the two closed subgroups and the containment
that makes `L / K` meaningful — keeping the proof in the object prevents
extension predicates from forming over unrelated subgroups
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:219`]
[Yamaguchi2026]). -/
structure AbstractExtension (G : Type*) [Group G] [TopologicalSpace G] where
  /-- The closed subgroup contravariantly representing the extension field. -/
  field : ClosedSubgroup G
  /-- The closed subgroup contravariantly representing the base field. -/
  base : ClosedSubgroup G
  /-- Contravariance turns the field inclusion into this subgroup inclusion. -/
  below : field.toSubgroup ≤ base.toSubgroup

namespace AbstractExtension

/-- The extension field's subgroup viewed inside the base field's. -/
def subgroup (E : AbstractExtension G) : Subgroup E.base.toSubgroup :=
  E.field.toSubgroup.subgroupOf E.base.toSubgroup

/-- The relative coset space of an abstract extension. -/
def quotient (E : AbstractExtension G) : Type u :=
  E.base.toSubgroup ⧸ E.subgroup

/-- **The cardinal degree**: the size of the coset space — infinity is not
encoded as zero
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:241`]
[Yamaguchi2026]). -/
noncomputable def degreeCardinal (E : AbstractExtension G) : Cardinal :=
  relativeIndexCardinal E.below

/-- The cardinal degree is the cardinality of the coset space. -/
@[simp] theorem degreeCardinal_eq_mk_quotient (E : AbstractExtension G) :
    E.degreeCardinal = Cardinal.mk E.quotient :=
  rfl

/-- **The relative residue degree as a cardinal**: the index of the degree
images
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:252`]
[Yamaguchi2026]). -/
noncomputable def relativeResidueDegreeCardinal
    (E : AbstractExtension G) (D : DegreeData G) : Cardinal :=
  relativeIndexCardinal (Subgroup.map_mono (f := D.degree.toMonoidHom) E.below)

/-- **The relative ramification index as a cardinal**: the index inside the
degree kernel
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:259`]
[Yamaguchi2026]). -/
noncomputable def relativeRamificationIndexCardinal
    (E : AbstractExtension G) (D : DegreeData G) : Cardinal :=
  relativeIndexCardinal
    (show E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤
      E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker from
        inf_le_inf E.below le_rfl)

/-- **The cardinal fundamental identity** `[L : K] = f · e`: the residue factor
lifted from `ℤ̂`'s universe, no finiteness or infinite-index convention involved
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:269`]
[Yamaguchi2026]). -/
theorem degreeCardinal_eq_relativeResidueDegreeCardinal_mul_relativeRamificationIndexCardinal
    (E : AbstractExtension G) (D : DegreeData G) :
    E.degreeCardinal =
      Cardinal.lift.{u} (E.relativeResidueDegreeCardinal D) *
        E.relativeRamificationIndexCardinal D := by
  simpa [degreeCardinal, relativeResidueDegreeCardinal,
    relativeRamificationIndexCardinal] using
    (relativeIndexCardinal_eq_map_mul_inf_ker
      D.degree.toMonoidHom E.below)

/-- **Frobenius residue compatibility**: the relative residue cardinal times the
absolute residue cardinal of the base is the absolute residue cardinal of the
field ([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:282`]
[Yamaguchi2026]). -/
theorem relativeResidueDegreeCardinal_mul_residueDegreeCardinal
    (E : AbstractExtension G) (D : DegreeData G) :
    E.relativeResidueDegreeCardinal D * D.residueDegreeCardinal E.base =
      D.residueDegreeCardinal E.field := by
  change
    intersectionIndexCardinal
        (E.field.toSubgroup.map D.degree.toMonoidHom)
        (E.base.toSubgroup.map D.degree.toMonoidHom) *
      intersectionIndexCardinal (D.fieldImage E.base)
        (⊤ : Subgroup ProfiniteIntegerMul) =
        intersectionIndexCardinal (D.fieldImage E.field)
          (⊤ : Subgroup ProfiniteIntegerMul)
  rw [D.fieldImage_eq_map, D.fieldImage_eq_map]
  simpa only [relativeIndexCardinal] using
    (relativeIndexCardinal_mul
      (Subgroup.map_mono (f := D.degree.toMonoidHom) E.below)
      (show E.base.toSubgroup.map D.degree.toMonoidHom ≤
        (⊤ : Subgroup ProfiniteIntegerMul) from le_top))

/-- **Unramifiedness**: the base's inertia is already contained in the field's
subgroup — a containment, never a condition on a natural-valued index
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:372`]
[Yamaguchi2026]). -/
def IsUnramified (E : AbstractExtension G) (D : DegreeData G) : Prop :=
  E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ E.field.toSubgroup

/-- **Total ramification**: the degree image of the base is contained in the
degree image of the field
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:377`]
[Yamaguchi2026]). -/
def IsTotallyRamified (E : AbstractExtension G) (D : DegreeData G) : Prop :=
  E.base.toSubgroup.map D.degree.toMonoidHom ≤
    E.field.toSubgroup.map D.degree.toMonoidHom

/-- Unramifiedness is the inertia containment. -/
theorem isUnramified_iff_inertia_le (E : AbstractExtension G) (D : DegreeData G) :
    E.IsUnramified D ↔
      E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ E.field.toSubgroup :=
  Iff.rfl

/-- Total ramification is the image containment. -/
theorem isTotallyRamified_iff_image_le (E : AbstractExtension G)
    (D : DegreeData G) :
    E.IsTotallyRamified D ↔
      E.base.toSubgroup.map D.degree.toMonoidHom ≤
        E.field.toSubgroup.map D.degree.toMonoidHom :=
  Iff.rfl

/-- An unramified extension has cardinal ramification index one. -/
theorem relativeRamificationIndexCardinal_eq_one_of_isUnramified
    (E : AbstractExtension G) (D : DegreeData G) (hE : E.IsUnramified D) :
    E.relativeRamificationIndexCardinal D = 1 := by
  have heq :
      E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker =
        E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker := by
    apply le_antisymm
    · exact inf_le_inf E.below le_rfl
    · intro x hx
      exact ⟨hE hx, hx.2⟩
  change
    intersectionIndexCardinal
      (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker)
      (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) = 1
  rw [heq]
  exact relativeIndexCardinal_self _

/-- A totally ramified extension has cardinal residue degree one. -/
theorem relativeResidueDegreeCardinal_eq_one_of_isTotallyRamified
    (E : AbstractExtension G) (D : DegreeData G)
    (hE : E.IsTotallyRamified D) :
    E.relativeResidueDegreeCardinal D = 1 := by
  have heq :
      E.field.toSubgroup.map D.degree.toMonoidHom =
        E.base.toSubgroup.map D.degree.toMonoidHom :=
    le_antisymm (Subgroup.map_mono (f := D.degree.toMonoidHom) E.below) hE
  change
    intersectionIndexCardinal
      (E.field.toSubgroup.map D.degree.toMonoidHom)
      (E.base.toSubgroup.map D.degree.toMonoidHom) = 1
  rw [heq]
  exact relativeIndexCardinal_self _

/-- An unramified extension's cardinal degree is its lifted residue degree. -/
theorem degreeCardinal_eq_lift_relativeResidueDegreeCardinal_of_isUnramified
    (E : AbstractExtension G) (D : DegreeData G) (hE : E.IsUnramified D) :
    E.degreeCardinal =
      Cardinal.lift.{u} (E.relativeResidueDegreeCardinal D) := by
  rw [E.degreeCardinal_eq_relativeResidueDegreeCardinal_mul_relativeRamificationIndexCardinal
      D,
    E.relativeRamificationIndexCardinal_eq_one_of_isUnramified D hE, mul_one]

/-- A totally ramified extension's cardinal degree is its ramification
cardinal. -/
theorem degreeCardinal_eq_relativeRamificationIndexCardinal_of_isTotallyRamified
    (E : AbstractExtension G) (D : DegreeData G)
    (hE : E.IsTotallyRamified D) :
    E.degreeCardinal = E.relativeRamificationIndexCardinal D := by
  rw [E.degreeCardinal_eq_relativeResidueDegreeCardinal_mul_relativeRamificationIndexCardinal
      D,
    E.relativeResidueDegreeCardinal_eq_one_of_isTotallyRamified D hE]
  simp

end AbstractExtension

/-- **A tower of abstract extensions**: three closed subgroups and the two
adjacent containments
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:302`]
[Yamaguchi2026]). -/
structure Tower (G : Type*) [Group G] [TopologicalSpace G] where
  /-- The closed subgroup representing the top field. -/
  top : ClosedSubgroup G
  /-- The closed subgroup representing the middle field. -/
  middle : ClosedSubgroup G
  /-- The closed subgroup representing the base field. -/
  base : ClosedSubgroup G
  /-- Contravariant containment for the top-to-middle extension. -/
  top_le_middle : top.toSubgroup ≤ middle.toSubgroup
  /-- Contravariant containment for the middle-to-base extension. -/
  middle_le_base : middle.toSubgroup ≤ base.toSubgroup

namespace Tower

variable (T : Tower G)

/-- The upper extension in a tower. -/
def topExtension : AbstractExtension G where
  field := T.top
  base := T.middle
  below := T.top_le_middle

/-- The lower extension in a tower. -/
def baseExtension : AbstractExtension G where
  field := T.middle
  base := T.base
  below := T.middle_le_base

/-- The composite extension in a tower. -/
def totalExtension : AbstractExtension G where
  field := T.top
  base := T.base
  below := T.top_le_middle.trans T.middle_le_base

/-- **Cardinal degrees multiply in a tower**
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:326`]
[Yamaguchi2026]). -/
theorem degreeCardinal_mul :
    T.topExtension.degreeCardinal * T.baseExtension.degreeCardinal =
      T.totalExtension.degreeCardinal :=
  relativeIndexCardinal_mul T.top_le_middle T.middle_le_base

/-- Cardinal residue degrees multiply in a tower. -/
theorem relativeResidueDegreeCardinal_mul (D : DegreeData G) :
    T.topExtension.relativeResidueDegreeCardinal D *
        T.baseExtension.relativeResidueDegreeCardinal D =
      T.totalExtension.relativeResidueDegreeCardinal D :=
  relativeIndexCardinal_mul
    (Subgroup.map_mono (f := D.degree.toMonoidHom) T.top_le_middle)
    (Subgroup.map_mono (f := D.degree.toMonoidHom) T.middle_le_base)

/-- Cardinal ramification indices multiply in a tower. -/
theorem relativeRamificationIndexCardinal_mul (D : DegreeData G) :
    T.topExtension.relativeRamificationIndexCardinal D *
        T.baseExtension.relativeRamificationIndexCardinal D =
      T.totalExtension.relativeRamificationIndexCardinal D :=
  relativeIndexCardinal_mul
    (show T.top.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤
      T.middle.toSubgroup ⊓ D.degree.toMonoidHom.ker from
        inf_le_inf T.top_le_middle le_rfl)
    (show T.middle.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤
      T.base.toSubgroup ⊓ D.degree.toMonoidHom.ker from
        inf_le_inf T.middle_le_base le_rfl)

end Tower

end Atlas.Knowledge
