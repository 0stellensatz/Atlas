import Mathlib
import Atlas.Knowledge.PrincipalIdele

/-!
# idele class group

The idele class group of a number field: `C_K = 𝕀_K / K^×`, the ideles modulo the principal
ideles. This is the group global class field theory is about — the reciprocity map of the
later phases is a map out of it, its identity component is the kernel of that map, and its
norm-one part is compact. The item is the quotient itself; it is a topological group by
instance search, the quotient of the idele topology by a subgroup of a commutative group,
with the openness `Fact` of `Atlas.Knowledge.IdeleGroup` doing the topological work.

## Main definitions

* `IdeleClassGroup` — `𝕀_K ⧸ range (principalIdele)`.

## Implementation notes

The quotient is by `Atlas.Knowledge.principalIdeleSubgroup`, normal because the ideles are
commutative; every topological instance on the quotient synthesizes from the `Fact` recorded
with the idele group, and nothing here needs stating by hand — the definition is one line,
and that is the point: the vocabulary was already Mathlib's. Milne's `C` maps onto the ideal
class group; that comparison map is later-phase vocabulary, deliberately not this item's.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open scoped NumberField
open NumberField

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

/-- The **idele class group** `C_K = 𝕀_K / K^×`: the ideles modulo the principal ideles
([Milne 2020, Chap. V, §4, p.171][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/Idele/PrincipalCore.lean:71`). -/
abbrev IdeleClassGroup : Type _ :=
  IdeleGroup K ⧸ principalIdeleSubgroup K

end Atlas.Knowledge
