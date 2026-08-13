import Mathlib
import Atlas.Knowledge.DigitSum

/-!
# Legendre's formula

Legendre's formula for the `p`-adic valuation of a factorial, in the digit-sum form: for a
prime `p`,

`(p - 1) * padicValNat p (n !) = n - digitSum p n`.

The reason to keep it in this form rather than as the sum `∑ i, n / p ^ i` is that the
right-hand side is closed—no bound to choose and no sum to evaluate—so a question about
`padicValNat p (n !)` reduces to a question about `Atlas.Knowledge.DigitSum`, which is
arithmetic in base `p` and nothing more.

Both forms are Mathlib's, and this item is the identification rather than a reproof: what it
adds is the name, the digit-sum vocabulary, and the record that the two are one statement.
Where the sum form is wanted it is `padicValNat_factorial` directly.

## Main statements

* `legendre_factorial` — Legendre's formula in digit-sum form.
* `padicValNat_factorial_lt` — the strict bound it yields for `n ≠ 0`.

## Implementation notes

The names here deliberately avoid Mathlib's own. A declaration of the enclosing namespace
takes precedence over one reached by `open`, so an item named exactly after the lemma it
restates would shadow that lemma inside its own file and delegate to itself; the failure is a
recursion error at best and a silent self-reference at worst. Naming the restatement for the
mathematician rather than for the shape of the statement removes the question.
-/

open Nat

namespace Atlas.Knowledge

/-- **Legendre's formula.** For a prime `p`, `(p - 1)` times the `p`-adic valuation of `n !`
is `n` less the sum of the base-`p` digits of `n`. This is Mathlib's
`sub_one_mul_padicValNat_factorial`, restated over `digitSum`. -/
theorem legendre_factorial (p n : ℕ) [Fact p.Prime] :
    (p - 1) * padicValNat p (n !) = n - digitSum p n :=
  sub_one_mul_padicValNat_factorial n

/-- The `p`-adic valuation of `n !` is strictly less than `n`, for `n ≠ 0`. This is Mathlib's
`padicValNat_factorial_lt_of_ne_zero`. -/
theorem padicValNat_factorial_lt {p n : ℕ} [Fact p.Prime] (hn : n ≠ 0) :
    padicValNat p (n !) < n :=
  padicValNat_factorial_lt_of_ne_zero p hn

end Atlas.Knowledge
