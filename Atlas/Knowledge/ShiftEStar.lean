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

## Main statements

* `Shift.e_star_notMem_T` — `e_star` itself is not missed by the shift, sitting past the
  maximum of what is.

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

/-- `e_star` is not in `T ρ`: it sits one past the maximum, so membership would exceed the
maximum by itself. -/
theorem e_star_notMem_T (ρ : Shift) (hρ : (T ρ).Finite) : e_star ρ hρ ∉ T ρ := by
  intro hmem
  have hle : e_star ρ hρ ≤ hρ.toFinset.max'
      (by simp only [Finite.toFinset_nonempty]; exact T_nonempty ρ) :=
    Finset.le_max' _ _ (hρ.mem_toFinset.mpr hmem)
  have : hρ.toFinset.max' _ + 1 ≤ hρ.toFinset.max' _ := hle
  exact absurd this (by simp)

end Shift

end Atlas.Knowledge
