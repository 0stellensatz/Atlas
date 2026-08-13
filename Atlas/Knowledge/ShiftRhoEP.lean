import Mathlib
import Atlas.Knowledge.Shift

/-!
# rho-e-p

The shift `ρ_ep e p : i ↦ min (p * i) (i + e)`, for `p` a prime and `e` a positive integer. This is
the family of shifts relevant to local fields: for `K` local of residue characteristic `p` and
`e = v_K (p)`, it is the shift along which `p`-powering moves the higher unit filtration, in the
sense that `U i ^ p ⊆ U (ρ i)` (`Atlas.Knowledge.HigherUnitGroup`).

The source states the family over `e ∈ ℤ_{>0} ∪ {∞}`; the two cases are separate definitions here,
since `ℕ+` has no `∞`. This file is the finite case, which belongs to local fields of
characteristic `0`; `Atlas.Knowledge.ShiftRhoP` is the case `e = ∞`.

What `T` and `e_star` come to for this shift is `Atlas.Knowledge.TRhoEP`.

## Main definitions

* `ρ_ep` — the shift `i ↦ min (p * i) (i + e)`.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

/-- The shift `i ↦ min (p * i) (i + e)`, for `p` a prime and `e` a positive integer—the family of
shifts relevant to local fields of characteristic `0`
([Pagano 2022, Example 2.1, p.415][Pagano2022]). -/
def ρ_ep (e : ℕ+) (p : ℕ+) (hp : 1 < p) : Shift where
  shift_map := fun i ↦ min (p * i) (i + e)
  strict_mono := by
    intro i j hij
    refine min_lt_min ?_ ?_
    · exact mul_lt_mul_right hij p
    · exact (add_lt_add_iff_right e).mpr hij
  one_lt_shift_one := by
    apply lt_min
    · rw [mul_one]
      exact one_lt_of_gt hp
    · exact PNat.lt_add_right 1 e

end Atlas.Knowledge
