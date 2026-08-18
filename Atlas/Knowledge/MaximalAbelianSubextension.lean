import Mathlib

/-!
# maximal abelian subextension

The maximal abelian subextension of a field extension, as the supremum of its abelian
Galois intermediate fields: the `M` of the norm limitation theorem — the largest piece of
`L/K` that abelian class field theory can see, and the exact extent to which norm subgroups
of the idele class group forget the non-abelian part. The definition asks for nothing
beyond a field extension; that the supremum is itself abelian over `K` is a fact its
consumers may need and this item deliberately does not assert.

## Main definitions

* `maximalAbelianSubextension` — `sSup {M : IntermediateField K L | IsAbelianGalois K M}`.

## Implementation notes

Defined by the lattice supremum rather than as a fixed field of the commutator, so that no
Galois hypothesis on `L/K` enters: Milne's norm limitation (Chap. VIII, Thm. 4.8) takes an
arbitrary finite extension, and the compositum-of-abelian-is-abelian fact that makes the
supremum deserve its name is the standard one, not this definition's burden. The source
works instead inside a chosen normal closure
(`AlgebraicNumberTheory/Galois/MaximalAbelianSubextension.lean:47`), fixing the commutator
together with the fixing subgroup of the embedded field — the same subfield through its
Galois-closed model.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

variable (K : Type*) [Field K]

/-- The **maximal abelian subextension** of `L / K`: the supremum of the abelian Galois
intermediate fields ([Milne 2020, Chap. VIII, §4, Thm. 4.8, p.242][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/Galois/MaximalAbelianSubextension.lean:47`]
[Yamaguchi2026]). -/
noncomputable def maximalAbelianSubextension (L : Type*) [Field L] [Algebra K L] :
    IntermediateField K L :=
  sSup {M : IntermediateField K L | IsAbelianGalois K M}

end Atlas.Knowledge
