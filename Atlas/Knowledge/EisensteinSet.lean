import Mathlib

/-!
# Eisenstein polynomials of a local field

The source's `Eis (h, F)`: the degree-`h` Eisenstein polynomials of a local field—monic, with
coefficients in the integer ring, reducing to `x^h` modulo the maximal ideal, constant term
outside its square. This is the sample space of the source's probabilistic reading of
Eisenstein polynomials, over which the mass formula's proof runs, and the generation notion by
which `Atlas.Knowledge.SerreMass` carves the totally ramified extensions out of a fixed
algebraic closure.

## Main definitions

* `eisensteinSet` — `Eis (h, F)` as a set of polynomials over the integer ring.

## Implementation notes

Reduction to `x^h` modulo the maximal ideal is monicity together with membership of every
lower coefficient, which with the constant term's exclusion from the square is exactly
Mathlib's `Polynomial.IsEisensteinAt` at the maximal ideal; the definition conjoins it with
monicity and the degree, and no valuative structure enters beyond the integer ring.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open ValuativeRel

/-- The source's `Eis (h, F)`: monic degree-`h` polynomials over the integer ring, Eisenstein
at the maximal ideal ([Pagano 2022, §9, p.460][Pagano2022]). -/
def eisensteinSet (F : Type*) [Field F] [ValuativeRel F] (h : ℕ+) :
    Set (Polynomial ↥𝒪[F]) :=
  {g | g.Monic ∧ g.natDegree = (h : ℕ) ∧
    g.IsEisensteinAt (IsLocalRing.maximalIdeal ↥𝒪[F])}

end Atlas.Knowledge
