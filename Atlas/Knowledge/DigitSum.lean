import Mathlib

/-!
# digit sum

The sum of the base-`p` digits of a natural number, written `s_p (n)` where the literature
wants a symbol for it. It measures how far `n` is from being a power of `p`, and it is the
correction term in Legendre's formula for the `p`-adic valuation of a factorial
(`Atlas.Knowledge.LegendreFormula`).

This is a name over Mathlib's `Nat.digits`, which returns the digits little-endian and gives
the empty list at `0`. Two consequences are worth stating rather than discovering: the sum at
`0` is `0`, and for `p ≤ 1` the underlying `Nat.digits` degenerates and so does this. The
definition is left total and unconditional anyway, and the statements about it carry the
primality of `p` where they need it—a hypothesis on a definition would propagate into every
statement mentioning it for the sake of the two cases nothing asks about.

## Main definitions

* `digitSum` — the sum of the base-`p` digits of `n`.

## Main statements

* `digitSum.le_self` — the digit sum never exceeds the number itself.
-/

namespace Atlas.Knowledge

/-- The sum of the base-`p` digits of `n`, written `s_p (n)`. -/
def digitSum (p n : ℕ) : ℕ := (p.digits n).sum

namespace digitSum

@[simp]
theorem zero (p : ℕ) : digitSum p 0 = 0 := by
  simp [digitSum]

/-- The base-`p` digit sum of `n` never exceeds `n` (Mathlib's `Nat.digit_sum_le`). -/
theorem le_self (p n : ℕ) : digitSum p n ≤ n :=
  Nat.digit_sum_le p n

end digitSum

end Atlas.Knowledge
