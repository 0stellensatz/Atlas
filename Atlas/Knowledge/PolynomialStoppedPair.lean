import Mathlib

/-!
# stopped pair of an Eisenstein polynomial

The pair of the source's stopping game `σ̃_j (g)`: each monomial of an Eisenstein polynomial
carries the weight `deg g · v (a_α) + α`, the game visits the weights in increasing order
shooting with length `v_p (α)`, and the pair collects the records—the monomials whose index
has strictly smaller `p`-adic valuation than every lighter one—at the level dividing the
`p`-part out of the weight, truncated at the stop `e`. The source computes this pair by its
Procedure, an explicit search along the coefficients; as everywhere in this layer the
computed structure is taken as the definition, the Procedure being exactly the record
extraction. Which part of the cut-out field's invariant this computes is the source's
Theorem 10.1, recorded in `Atlas.Knowledge.FieldJumpsBelowE`.

## Main definitions

* `polynomialStoppedPair` — the records of the weight-ordered monomials, as a graph.

## Implementation notes

A weight determines its monomial: `deg g · v + α` with `1 ≤ α ≤ deg g` is division with
remainder, so the increasing arrangement has no ties and the record condition quantifies over
strictly lighter monomials without a tie rule. The index range starts at `1`, dropping the
source's constant term: under Eisenstein the constant's weight ties with the leading
monomial's—the one tie the range removes—its index has no `p`-adic valuation to shoot with,
and Mathlib's `padicValNat p 0 = 0` would otherwise install a spurious competitor blocking
every record. Exactness of the division by the `p`-part of the index is a membership
conjunct so that the definition stays honest off the Eisenstein locus; on it the conjunct is
automatic at every record, the leading monomial being the strict weight minimum, so a record
off the leading index has `p`-adic valuation below the degree's and its `p`-part divides the
weight—the argument of `Atlas.Knowledge.EisensteinGraph`. The leading monomial always
contributes the first record, its weight least and its coefficient a unit. At level zero the
records recover the minimal points of the coefficient graph, the record condition and
`≤_ρ`-minimality agreeing on a tie-free graph—the identification by which the source's §10
subsumes its introduction's recipe. The definition is total; the statements about it
hypothesize Eisenstein and the level's base field.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

open Classical in
/-- The **stopped pair of an Eisenstein polynomial**: the records of the weight-ordered
monomials up to the stop `e`, each at the level dividing the `p`-part out of its weight, with
one more than the `p`-adic valuation of its index—the pair of the source's stopping game
`σ̃_j (g)`, its Procedure taken as the record extraction it computes
([Pagano 2022, §10, pp.468–469][Pagano2022]). -/
noncomputable def polynomialStoppedPair (p : ℕ) (e : ℕ+) (g : Polynomial R) :
    Finset (ℕ+ × ℕ+) :=
  ((Finset.Icc 1 g.natDegree).filter fun α =>
      g.coeff α ≠ 0 ∧
      g.natDegree * ((addVal R) (g.coeff α)).toNat + α ≤ (e : ℕ) ∧
      p ^ padicValNat p α ∣ g.natDegree * ((addVal R) (g.coeff α)).toNat + α ∧
      ∀ α' ∈ Finset.Icc 1 g.natDegree, g.coeff α' ≠ 0 →
        g.natDegree * ((addVal R) (g.coeff α')).toNat + α' <
          g.natDegree * ((addVal R) (g.coeff α)).toNat + α →
        padicValNat p α < padicValNat p α').image fun α =>
    (((g.natDegree * ((addVal R) (g.coeff α)).toNat + α) / p ^ padicValNat p α).toPNat',
      ⟨padicValNat p α + 1, Nat.succ_pos _⟩)

end Atlas.Knowledge
