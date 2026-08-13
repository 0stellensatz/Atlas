import Mathlib
import Atlas.Knowledge.ShiftEStar

/-!
# T-star of a shift

For a shift `ρ` whose `Atlas.Knowledge.ShiftT` is finite, `T_star` is `T ρ` enlarged by the single
point `Atlas.Knowledge.ShiftEStar`. It is the index set of the *extended* jump sets: an extended
jump set for `ρ` is `Atlas.Knowledge.IsJumpSet` with `S = T_star ρ hρ` where a plain jump set
takes `S = T ρ`, and that substitution is the entire difference between the two notions.

## Main definitions

* `Shift.T_star` — `T ρ ∪ {e_star ρ hρ}`.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

namespace Shift

/-- For a shift `ρ` with `T ρ` finite, `T_star` is `T ρ ∪ {e_star ρ hρ}`, written `T*_ρ` in the
source ([Pagano 2022, Def. 2.2, p.416][Pagano2022]). -/
def T_star (ρ : Shift) (hρ : (T ρ).Finite) : Set ℕ+ := T ρ ∪ {e_star ρ hρ}

end Shift

end Atlas.Knowledge
