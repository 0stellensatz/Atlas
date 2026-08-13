import Mathlib
import Atlas.Knowledge.Shift

/-!
# T of a shift

For a shift `ρ`, the set `T ρ` is the complement `ℕ+ ∖ ρ '' ℕ+` of its image—the positive
integers `ρ` misses. It is the set the whole jump-set apparatus is indexed by, and it is never
empty: `1 < ρ 1` and monotonicity put every value of `ρ` above `1`, so `1` is always missed.

Whether `T ρ` is *finite* is the dividing question. When it is,
`Atlas.Knowledge.ShiftEStar` is defined and the shift is one of those relevant to local fields;
`Atlas.Knowledge.TRhoEP` is where that finiteness is established for the shifts that
matter.

## Main definitions

* `Shift.T` — the complement of the image of a shift.

## Main statements

* `Shift.T_nonempty` — `T ρ` always contains `1`, so it is never empty.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open Set

namespace Shift

/-- The set `T ρ` of positive integers missed by the shift `ρ`, that is `ℕ+ ∖ ρ '' ℕ+`
([Pagano 2022, §2, p.415][Pagano2022]). -/
abbrev T (ρ : Shift) : Set ℕ+ := univ \ (ρ.shift_map) '' univ

/-- `T ρ` is nonempty: every value of `ρ` exceeds `1`, so `1` is missed. -/
lemma T_nonempty (ρ : Shift) : (T ρ).Nonempty := by
  use 1
  simp only [mem_sdiff, mem_univ, image_univ, mem_range, not_exists, true_and]
  intro x hx
  have hlt : ρ.shift_map x > 1 := calc
    ρ.shift_map x ≥ ρ.shift_map 1 := by
      have hx' : 1 ≤ x := by apply one_le
      exact ρ.strict_mono.monotone hx'
    ρ.shift_map 1 > 1 := ρ.one_lt_shift_one
  have : ρ.shift_map x ≠ 1 := by exact Ne.symm (ne_of_lt hlt)
  contradiction

end Shift

end Atlas.Knowledge
