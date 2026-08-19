import Mathlib

/-!
# strongly separable Eisenstein polynomial

The Eisenstein polynomials cutting out strongly separable extensions, by the source's
coefficient criterion: some coefficient at an index prime to `p` has valuation below that of
`p` itself. The source defines strong separability for an extension—the different's valuation
below that of `p`—calls an Eisenstein polynomial strongly separable when the extension it
gives rise to is, and proves the coefficient criterion; the criterion is taken here as the
polynomial-side definition, which needs no extension and no different. Under it the jump pair
`Atlas.Knowledge.eisensteinJumpPair` lands in the finite-`T` world of
`Atlas.Knowledge.ShiftRhoEP` and identifies with the field-side invariant, the claims of
`Atlas.Knowledge.EisensteinFieldInvariant`.

## Main definitions

* `IsStronglySeparablePolynomial` — the coefficient criterion.

## Implementation notes

The source's `(i, p) = 1` is spelled `¬ p ∣ i`, the two agreeing at a prime, and `p` enters
the ring through the cast, so the comparison `v (a_i) < v (p)` is stated by
`IsDiscreteValuationRing.addVal` alone. In residue characteristic `p` the cast's valuation is
the absolute ramification index; nothing here fixes the characteristic. At a `p` invertible in
`R` the right side is `0` and the predicate is unsatisfiable, which junks in the safe
direction; at `p = 0` it degenerates the other way, to the existence of a nonzero coefficient
in degrees `1, …, deg g`—permissive rather than safe, and excluded wherever a consumer
hypothesizes a prime.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The **strongly separable** Eisenstein polynomials, by the source's coefficient criterion:
some index `1 ≤ i ≤ deg g` prime to `p` carries a coefficient of valuation strictly below
that of `p` ([Pagano 2022, Prop. 1.10, p.409][Pagano2022], the criterion;
[Pagano 2022, Def. 1.9, p.408][Pagano2022], the notion for an extension, transferred to the
polynomial in the text after the proposition). -/
def IsStronglySeparablePolynomial (p : ℕ) (g : Polynomial R) : Prop :=
  ∃ i, 1 ≤ i ∧ i ≤ g.natDegree ∧ ¬ p ∣ i ∧ (addVal R) (g.coeff i) < (addVal R) (p : R)

end Atlas.Knowledge
