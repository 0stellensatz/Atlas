import Mathlib

/-!
# fixed subgroup of one element's action

The elements of a coefficient module fixed by a single group element
acting through a representation: `ker(ρ(g) − 1)` read as fixed points,
an additive subgroup of the carrier. The one-element companion of
`Atlas.Knowledge.ambientFixedAddSubgroup`, and the universe-free
reading of the cycles object of Mathlib's finite-cyclic
norm-vs-difference complex: the cycles of
`Rep.FiniteCyclicGroup.normHomCompSub` are exactly this subgroup, but
that spelling lives in the complex's one-universe `{k G : Type u}`
block, which at `ℤ` coefficients would force the acting group into
`Type 0`, where the elementwise spelling leaves it free (#104).

## Main definitions

* `elementFixedAddSubgroup` — the fixed vectors of one group element.

## Main statements

* `mem_elementFixedAddSubgroup_iff` — membership is invariance under
  the element; proved.
* `mem_elementFixedAddSubgroup_iff_cycles` — membership is vanishing
  under the `ρ(g) − 1` map of Mathlib's finite-cyclic complex; proved.

## Implementation notes

The subgroup is defined by its carrier, like its ambient companion and
for the same reason: over `ℤ` the submodule routes hit the
integer-module diamond. Only `Monoid G` is asked — additivity of
`ρ(g)` is all the closure proofs use — and the coefficient ring `ℤ` is
not load-bearing either, the body elaborating at any semiring; it is
kept to match the ambient companion. The identification with the
cycles of `Rep.FiniteCyclicGroup.normHomCompSub` is recorded as a
theorem rather than left to prose, in the complex's own `{G : Type}`,
`CommGroup`, and `Fintype` binders, so the build keeps the claim
honest while the definition itself stays universe-free.
-/

namespace Atlas.Knowledge

/-- **The fixed subgroup of one element's action**: the vectors of the
carrier invariant under a single group element acting through the
representation — `ker(ρ(g) − 1)` read as fixed points. -/
def elementFixedAddSubgroup {G : Type*} [Monoid G] (M : Rep ℤ G)
    (g : G) : AddSubgroup M.V where
  carrier := {x | M.ρ g x = x}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change M.ρ g (a + b) = a + b
    rw [map_add, show M.ρ g a = a from ha, show M.ρ g b = b from hb]
  neg_mem' := by
    intro a ha
    change M.ρ g (-a) = -a
    rw [map_neg, show M.ρ g a = a from ha]

/-- Membership in the fixed subgroup is invariance under the element. -/
@[simp]
theorem mem_elementFixedAddSubgroup_iff {G : Type*} [Monoid G]
    (M : Rep ℤ G) (g : G) (x : M.V) :
    x ∈ elementFixedAddSubgroup M g ↔ M.ρ g x = x :=
  Iff.rfl

/-- Membership in the fixed subgroup is vanishing under the second map
of Mathlib's finite-cyclic norm-vs-difference complex: the fixed
subgroup is its cycles object, read elementwise. -/
theorem mem_elementFixedAddSubgroup_iff_cycles
    {G : Type} [CommGroup G] [Fintype G] (M : Rep ℤ G) (g : G) (x : M.V) :
    x ∈ elementFixedAddSubgroup M g ↔
      (Rep.FiniteCyclicGroup.normHomCompSub M g).g.hom x = 0 :=
  sub_eq_zero.symm

end Atlas.Knowledge
