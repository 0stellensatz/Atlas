import Mathlib

/-!
# Questions posed on August 13, 2026: Legendre's formula

Two questions about Legendre's formula for the `p`-adic valuation of a factorial, asked in the
form that keeps the right-hand side closed—`n` less the sum of the base-`p` digits of `n`,
rather than a sum over powers of `p` with a bound to choose.

The first asks for the formula itself. The second asks for the case `n = p ^ k`, where the
digit sum is `1` and the right-hand side should collapse to `p ^ k - 1`; it is really a
question about base-`p` digits, and the valuation is along for the ride.

## Implementation notes

Stated in Mathlib's vocabulary throughout—`(p.digits n).sum` rather than the knowledge layer's
name for it—so this file stands alone against Mathlib and clones nothing.

What the answers are about: `Atlas.Knowledge.LegendreFormula`, which carries the formula over
`Atlas.Knowledge.DigitSum`. The second question needs what neither of those has, the digit
expansion of a prime power, which would be `Atlas.Knowledge.DigitsOfPrimePow`.
-/

namespace AtlasChallenge.«20260813LegendreFormula»

/-- Legendre's formula: `(p - 1)` times the `p`-adic valuation of `n !` is `n` less the sum of
the base-`p` digits of `n`. -/
theorem question_a (p n : ℕ) [Fact p.Prime] :
    (p - 1) * padicValNat p n.factorial = n - (p.digits n).sum := sorry

/-- The prime-power case: the base-`p` digits of `p ^ k` sum to `1`, so Legendre's formula should
collapse to `p ^ k - 1` on the right. -/
theorem question_b (p k : ℕ) [Fact p.Prime] :
    (p - 1) * padicValNat p (p ^ k).factorial = p ^ k - 1 := sorry

end AtlasChallenge.«20260813LegendreFormula»
