import Mathlib

/-!
# strongly Eisenstein polynomial

The Eisenstein polynomials whose linear coefficient is a uniformizer: `v (a_1) = 1`. These are
the source's most tightly constrained class—away from `(p, j) = (2, 0)`, being strongly
Eisenstein is equivalent to the cut-out field's invariant being the extremal jump pair, the
statement recorded in this tranche's identification phase—and the class of polynomials giving
the most likely jump set in the source's counting.

## Main definitions

* `IsStronglyEisenstein` — the linear coefficient has valuation one.

## Implementation notes

The valuation is `IsDiscreteValuationRing.addVal`, and the equation is stated in `ℕ∞`, where
`1` is the coercion; a zero linear coefficient has valuation `⊤` and is correctly excluded.
Nothing here asks the polynomial to be Eisenstein—the predicate is total, as with
`Atlas.Knowledge.eisensteinGraph`—and the statements that consume it hypothesize it.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The **strongly Eisenstein** polynomials: the linear coefficient is a uniformizer, its
valuation exactly one ([Pagano 2022, Def. 10.2, p.470][Pagano2022]). -/
def IsStronglyEisenstein (g : Polynomial R) : Prop :=
  (addVal R) (g.coeff 1) = 1

end Atlas.Knowledge
