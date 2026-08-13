import Mathlib
import Atlas.Knowledge.ShiftT

/-!
# e-star of a shift

For a shift `ρ` whose `Atlas.Knowledge.ShiftT` is finite, `e_star` is `max (T ρ) + 1`—one past the
largest positive integer the shift misses, and so the point beyond which `ρ` misses nothing.

The finiteness hypothesis is carried as an explicit argument rather than as a typeclass or a
hypothesis on the structure, because it is exactly the dividing condition of the theory: shifts
with infinite `T` are the ones belonging to local fields of characteristic `p`, and they are not
excluded from `Atlas.Knowledge.Shift` for the sake of this definition. The nonemptiness the `max'`
needs is discharged from `Shift.T_nonempty` and never becomes a hypothesis.

## Main definitions

* `Shift.e_star` — one more than the largest element of `T ρ`.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open Set

namespace Shift

/-- For a shift `ρ` with `T ρ` finite, `e_star` is `max (T ρ) + 1`
([Pagano 2022, §2, p.415][Pagano2022]). -/
noncomputable def e_star (ρ : Shift) (hρ : (T ρ).Finite) :=
  (Finite.toFinset hρ).max' (by simp only [Finite.toFinset_nonempty]; apply T_nonempty ρ) + 1

end Shift

end Atlas.Knowledge
