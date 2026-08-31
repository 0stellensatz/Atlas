import Mathlib

/-!
# coefficient module of an abstract Galois extension

The coefficient module `A_L` of an abstract Galois extension `L | K` as a module
over its Galois group: restrict the ambient representation to `G_K`, take
`G_L`-fixed vectors, and descend the action to the quotient `G_K ⧸ G_L`. In the
reciprocity engine (#104) this is the object whose Tate cohomology the class field
axiom constrains, level by level.

## Main definitions

* `extensionFixedRepresentation` — `A_L` as a representation of `G_K ⧸ G_L`.

## Implementation notes

The containment `G_L ≤ G_K` enters only as a semantic guard — the construction
reads `G_L` inside `G_K` through Mathlib's `Subgroup.subgroupOf`, which is
well-defined regardless — and normality of the induced subgroup is what carries the
quotient action, through Mathlib's `Rep.quotientToInvariants`. The source's
`extensionSubgroup` abbreviation is deliberately not ported: it is definitionally
`Subgroup.subgroupOf`, which this layer spells directly. The ambient group stays in
an arbitrary universe; only the engine's own instantiation pins it to `Type 0`.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

/-- **The coefficient module of an abstract Galois extension** `L | K`: the
`G_L`-fixed vectors of the restriction to `G_K`, with the descended `G_K ⧸ G_L`
action — the module `A_L` of the extension, as acted on by its Galois group
([Milne 2020, Chap. II, §1, p.60][MilneCFT] — the `(−)^G` functor;
[Yamaguchi 2026, `CyclicCohomology/NormKernelVanishing.lean:53`][Yamaguchi2026]). -/
noncomputable def extensionFixedRepresentation {G : Type*} [Group G]
    [TopologicalSpace G] (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (_hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) :
    Rep ℤ (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) := by
  letI := hnormal
  exact Rep.quotientToInvariants
    (Rep.res K.toSubgroup.subtype A)
    (L.toSubgroup.subgroupOf K.toSubgroup)

end Atlas.Knowledge
