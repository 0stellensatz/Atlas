import Mathlib

/-!
# valuation of a root of unity

A root of unity has valuation one: the valuation of an `n`-th root of unity is an `n`-th root
of `1` in the value group, and the value group of a valued field is torsion-free away from
zero. The fact is generic, on any valued field with no local-field hypothesis, and two items
of the tame formula chain consume it: `Atlas.Knowledge.LocalHilbertSymbolTameFormula`, for
the injectivity of reduction on tame roots of unity and the divisibility `n ∣ q - 1`, and
`Atlas.Knowledge.LocalHilbertSymbolUnitUniformizer`, to put the symbol `(u, ϖ)`, itself an
`n`-th root of unity, in the integer ring. The second is a prerequisite of the first, so the
lemma lives below both rather than in either.

## Main statements

* `valuation_eq_one_of_pow_eq_one` — `ζ ^ n = 1` with `n ≠ 0` gives `valuation K ζ = 1`;
  proved.

## Implementation notes

The proof is `map_pow` followed by Mathlib's `pow_eq_one_iff` in the value group, a linearly
ordered commutative group with zero. The item is stated over any valued field, as
`Atlas.Knowledge.HigherUnitGroup` is; Serre's Lemma 1 records the fact as `μ_n ⊂ U_K` for a
discretely valued field, which is the case the two consumers are in.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K]

/-- Roots of unity have valuation one: the value group is torsion-free away from zero
([Serre 1979, Chap. XIV, §3, Lemma 1, p.210][Serre1979]). -/
theorem valuation_eq_one_of_pow_eq_one {ζ : K} {n : ℕ} (hn : n ≠ 0) (hζ : ζ ^ n = 1) :
    valuation K ζ = 1 := by
  have h : (valuation K ζ) ^ n = 1 := by rw [← map_pow, hζ, map_one]
  exact (pow_eq_one_iff.mp h).resolve_right hn

end Atlas.Knowledge
