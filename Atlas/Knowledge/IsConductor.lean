import Mathlib
import Atlas.Knowledge.RayClassGroup

/-!
# conductor

The conductor of a subgroup of the idele class group, as a characterization: a modulus is
*defining* for `H` when its congruence subgroup sits inside `H`, and the conductor is a
least defining modulus. Stating the conductor as a predicate rather than constructing it
keeps the item choice-free and junk-free — no `Nat.find` over an emptiness-dependent set,
no default value when `H` admits no defining modulus at all — and the statements of
`Atlas.Knowledge.RayClassField` consume the predicate as a slot. Existence of a conductor
for a subgroup that has any defining modulus is the recorded claim.

## Main definitions

* `IsDefiningModulus` — `congruenceSubgroup m ≤ H`.
* `IsConductor` — a defining modulus below every defining modulus.

## Main statements

* `exists_isConductor` — a subgroup with a defining modulus has a conductor; recorded
  ahead of its proof.

## Implementation notes

Uniqueness of the conductor is antisymmetry of the modulus order and deliberately not
restated. The source constructs its conductor pointwise by `Nat.find`
(`GlobalClassFieldTheory/GlobalClassFields/Conductor.lean:90`) on a subtype that carries
the defining-modulus existence (`Conductor.lean:34, :42, :119`,
`ConductorInfinitePart.lean:241`); the characterization here is that construction's
defining property, freed of the choice.

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

/-- A **defining modulus** for a subgroup of the idele class group: its congruence
subgroup is contained in `H` ([Milne 2020, Chap. V, §3, Rem. 3.8, p.158][MilneCFT];
Yamaguchi 2026, `GlobalClassFieldTheory/GlobalClassFields/Conductor.lean:34`). -/
def IsDefiningModulus (H : Subgroup (IdeleClassGroup K)) (m : Modulus K) : Prop :=
  congruenceSubgroup K m ≤ H

/-- The **conductor**: a defining modulus dividing every defining modulus — the least
modulus through which `H`'s condition factors
([Milne 2020, Chap. V, §3, Rem. 3.8, p.158][MilneCFT]; Yamaguchi 2026,
`GlobalClassFieldTheory/GlobalClassFields/ConductorInfinitePart.lean:241`). -/
def IsConductor (H : Subgroup (IdeleClassGroup K)) (f : Modulus K) : Prop :=
  IsDefiningModulus K H f ∧ ∀ m, IsDefiningModulus K H m → f ≤ m

/-- A subgroup with any defining modulus has a conductor. Claim recorded ahead of its
proof ([Milne 2020, Chap. V, §3, Rem. 3.8, p.158][MilneCFT]; Yamaguchi 2026,
`GlobalClassFieldTheory/GlobalClassFields/Conductor.lean:119`). -/
theorem exists_isConductor (H : Subgroup (IdeleClassGroup K))
    (h : ∃ m, IsDefiningModulus K H m) : ∃ f, IsConductor K H f := by
  sorry

end Atlas.Knowledge
