import Mathlib
import Atlas.Knowledge.LegendreFormula

/-!
# Questions posed on August 13, 2026: Legendre's formula, answered

The statements, what they are about, and the knowledge items they draw on are in
`Challenge.lean` and are not repeated here. This file carries the same declaration list
with the bodies filled in, and `__check__.py` is what keeps the two lists identical.
-/

namespace AtlasChallenge.«20260813LegendreFormula»

/-- Legendre's formula: `(p - 1)` times the `p`-adic valuation of `n !` is `n` less the sum of
the base-`p` digits of `n`. -/
theorem question_a (p n : ℕ) [Fact p.Prime] :
    (p - 1) * padicValNat p n.factorial = n - (p.digits n).sum :=
  Atlas.Knowledge.legendre_factorial p n

/-- The prime-power case: the base-`p` digits of `p ^ k` sum to `1`, so Legendre's formula should
collapse to `p ^ k - 1` on the right. -/
theorem question_b (p k : ℕ) [Fact p.Prime] :
    (p - 1) * padicValNat p (p ^ k).factorial = p ^ k - 1 := sorry

end AtlasChallenge.«20260813LegendreFormula»
