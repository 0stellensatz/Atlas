import Mathlib
import Atlas.Knowledge.DegreeData

/-!
# abstract field of finite residue degree

An abstract field bundled with finiteness of its residue quotient, so that its
absolute residue degree is a genuinely positive natural — the boundary at which
the engine's cardinal residue data becomes the `f_K : ℕ+` the valuation axiom's
`norm_range` quantifies over (#104).

## Main definitions

* `FiniteResidueAbstractField` — the field with its finiteness certificate, and
  `FiniteResidueAbstractField.ofField` to bundle one.
* `FiniteResidueAbstractField.residueDegree` — the positive residue degree.

## Main statements

* `FiniteResidueAbstractField.residueDegree_coe` — its natural value is the
  quotient's `Nat.card`; proved.
* `FiniteResidueAbstractField.residueDegreeCardinal_eq_coe` — the cardinal
  specializes to it at the finite boundary; proved.

## Implementation notes

The source marks `toSubgroup` `@[implicit_reducible]` — Lean core's
instances-transparency attribute; it is dropped here because no Atlas consumer
unfolds through the projection yet, and it can be restored at the consumer that
first needs it.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **An abstract field of finite residue degree**: the field together with
finiteness of its residue quotient, making the numerical residue degree
genuinely positive (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Fields.lean:163`). -/
structure FiniteResidueAbstractField (D : DegreeData G) where
  /-- The closed subgroup representing the abstract field. -/
  field : ClosedSubgroup G
  /-- The field's residue quotient is finite. -/
  finiteResidueQuotient : Finite (D.residueQuotient field)

namespace FiniteResidueAbstractField

variable {D : DegreeData G}

/-- Bundle a field whose residue quotient is known finite. -/
def ofField (D : DegreeData G) (K : ClosedSubgroup G)
    [hfinite : Finite (D.residueQuotient K)] :
    FiniteResidueAbstractField D where
  field := K
  finiteResidueQuotient := hfinite

/-- The underlying subgroup. -/
def toSubgroup (K : FiniteResidueAbstractField D) : Subgroup G :=
  K.field.toSubgroup

/-- The bundled field supplies finiteness of its residue quotient. -/
instance (K : FiniteResidueAbstractField D) :
    Finite (D.residueQuotient K.field) :=
  K.finiteResidueQuotient

/-- **The positive absolute residue degree**
(Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Fields.lean:192`). -/
noncomputable def residueDegree (K : FiniteResidueAbstractField D) : ℕ+ := by
  letI : Nonempty (D.residueQuotient K.field) := ⟨QuotientGroup.mk 1⟩
  exact ⟨Nat.card (D.residueQuotient K.field), Nat.card_pos⟩

/-- The natural value of the residue degree is the quotient's `Nat.card`. -/
@[simp] theorem residueDegree_coe (K : FiniteResidueAbstractField D) :
    (K.residueDegree : ℕ) = Nat.card (D.residueQuotient K.field) :=
  rfl

/-- The cardinal residue degree specializes at the finite boundary. -/
@[simp] theorem residueDegreeCardinal_eq_coe
    (K : FiniteResidueAbstractField D) :
    D.residueDegreeCardinal K.field = ((K.residueDegree : ℕ) : Cardinal) := by
  change Cardinal.mk (D.residueQuotient K.field) =
    (Nat.card (D.residueQuotient K.field) : Cardinal)
  exact Nat.cast_card.symm

end FiniteResidueAbstractField

end Atlas.Knowledge
