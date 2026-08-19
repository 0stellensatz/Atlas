import Mathlib
import Atlas.Knowledge.Shift

/-!
# rho-p

The shift `ρ_p p : i ↦ p * i`, for `p` a prime. This is the `e = ∞` member of the family
`Atlas.Knowledge.ShiftRhoEP`—`min (p * i) (i + e)` is `p * i` once `e` is large enough at every
`i`—and it is the shift belonging to local fields of characteristic `p`.

Its `T` is infinite, being the positive integers not divisible by `p`, so
`Atlas.Knowledge.ShiftEStar` does not apply to it. That is the structural difference between the
two characteristics rather than a gap in what is formalized here.

## Main definitions

* `ρ_p` — the shift `i ↦ p * i`.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

/-- The shift `i ↦ p * i`, for `p` a prime—the `e = ∞` case of `ρ_ep`, belonging to local fields
of characteristic `p` ([Pagano 2022, Example 2.1, p.415][Pagano2022]). -/
def ρ_p (p : ℕ+) (hp : 1 < p) : Shift where
  shift_map := fun i ↦ p * i
  strict_mono := by
    intro _ _ hij
    simp only [mul_lt_mul_iff_left]
    exact hij
  one_lt_shift_one := by
    exact lt_mul_of_one_lt_left' 1 hp

/-- Iterating `ρ_p` is scaling by the corresponding power of `p`, which is how the jump order
along this shift compares points: `m` steps multiply by `p ^ m`. -/
theorem ρ_p_iterate (p : ℕ+) (hp : 1 < p) (m : ℕ) (i : ℕ+) :
    (⇑(ρ_p p hp))^[m] i = p ^ m * i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    change p * (p ^ m * i) = p ^ (m + 1) * i
    rw [← mul_assoc, ← pow_succ']

end Atlas.Knowledge
