import Mathlib

/-!
# fixed subgroup of an ambient coefficient module

The elements of a coefficient module fixed pointwise by a closed subgroup of the
ambient group: `A^H` as an additive subgroup of the representation's carrier. In the
reciprocity engine (#104) the ambient group is an absolute Galois group, a closed
subgroup is an abstract field, and this subgroup is the field's own multiplicative
module `A_K = A^{G_K}` — the carrier on which the engine's valuation and norm data
live.

## Main definitions

* `ambientFixedAddSubgroup` — the fixed vectors of a closed subgroup.

## Main statements

* `mem_ambientFixedAddSubgroup_iff` — membership is pointwise invariance; proved.

## Implementation notes

The subgroup is defined by its carrier rather than through
`Representation.invariants`: over `ℤ` the invariants route hits the integer-module
diamond — the carrier's `AddCommGroup.toIntModule` is not the `Rep`'s own `A.hV2`
instance — and the explicit carrier avoids the friction. The closedness of `H` is
not used by the definition; it is carried because the engine's fields are closed
subgroups and every consumer supplies one.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

/-- **The fixed subgroup of a coefficient module**: the elements invariant under
every member of a closed subgroup — `M^G = {m ∈ M | gm = m}`
([Milne 2020, Chap. II, §1, p.60][MilneCFT]; Yamaguchi 2026,
`KummerTheory/Abstract/KummerDelta.lean:26`). -/
def ambientFixedAddSubgroup {G : Type*} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (H : ClosedSubgroup G) : AddSubgroup A.V where
  carrier := {a | ∀ h : H.toSubgroup, A.ρ h.1 a = a}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb h
    rw [map_add, ha h, hb h]
  neg_mem' := by
    intro a ha h
    rw [map_neg, ha h]

/-- Membership in the fixed subgroup is pointwise invariance. -/
@[simp]
theorem mem_ambientFixedAddSubgroup_iff {G : Type*} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (H : ClosedSubgroup G) (a : A.V) :
    a ∈ ambientFixedAddSubgroup A H ↔ ∀ h : H.toSubgroup, A.ρ h.1 a = a :=
  Iff.rfl

end Atlas.Knowledge
