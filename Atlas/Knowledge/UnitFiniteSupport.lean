import Mathlib

/-!
# unit finite support

The valuation support of a global unit: the finite places of a number field at which a
given `a : Kˣ` is not a local unit, as a `Finset` — the `S` in every `S`-unit statement,
and the set the classical reciprocity hypotheses trim away. The set is the honest one,
`{v | v.valuation K a ≠ 1}` behind its finiteness proof; membership is the defining
condition. Everything here is proved.

## Main definitions

* `unitFiniteSupport` — `{v | v.valuation K a ≠ 1}` as a `Finset`.

## Main statements

* `mem_unitFiniteSupport` — membership is nontriviality of the valuation.

## Implementation notes

Finiteness is by numerator and denominator: write `a = x/y` over `𝓞 K`, bound the support
by the prime divisors of `(x)` and `(y)` through `Ideal.finite_factors`, and off both the
valuation is `1/1`. The source works with a chosen superset instead — a `Classical.choose`
of some finite set outside which the unit is integral
(`KummerTheory/Concrete/SUnitPreparation/FiniteRadicalSupport.lean:86`) — where this set
is canonical.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open NumberField IsDedekindDomain

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

private theorem valuation_support_finite (a : Kˣ) :
    {v : HeightOneSpectrum (𝓞 K) | v.valuation K (a : K) ≠ 1}.Finite := by
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (𝓞 K) (a : K)
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    intro hx0
    apply a.ne_zero
    rw [← hxy, hx0, map_zero, zero_div]
  apply ((Ideal.finite_factors (I := Ideal.span {x})
      (by
        rw [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
        exact hx0)).union
    (Ideal.finite_factors (I := Ideal.span {y})
      (by
        rw [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
        exact hy0))).subset
  intro v hv
  rw [Set.mem_setOf_eq] at hv
  by_contra hmem
  rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq, not_or,
    Ideal.dvd_span_singleton, Ideal.dvd_span_singleton] at hmem
  apply hv
  rw [← hxy, map_div₀, v.valuation_eq_one_iff_notMem.mpr hmem.1,
    v.valuation_eq_one_iff_notMem.mpr hmem.2, one_div_one]

/-- The **valuation support** of a global unit: the finite places at which it is not a
local unit ([Milne 2020, Chap. VIII, §5, p.244][MilneCFT]; Yamaguchi 2026,
`KummerTheory/Concrete/SUnitPreparation/FiniteRadicalSupport.lean:86`, a chosen
superset where this set is canonical). -/
noncomputable def unitFiniteSupport (a : Kˣ) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (valuation_support_finite K a).toFinset

/-- Membership in the support is nontriviality of the valuation
([Milne 2020, Chap. VIII, §5, p.244][MilneCFT]). -/
@[simp]
theorem mem_unitFiniteSupport (a : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ unitFiniteSupport K a ↔ v.valuation K (a : K) ≠ 1 :=
  Set.Finite.mem_toFinset _

end Atlas.Knowledge
