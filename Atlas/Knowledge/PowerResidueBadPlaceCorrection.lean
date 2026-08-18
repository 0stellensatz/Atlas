import Mathlib
import Atlas.Knowledge.InfinitePlaceHilbertSymbol

/-!
# power residue bad place correction

The correction term of power-residue reciprocity: the product of all infinite-place
Hilbert factors and all finite-place factors at the primes dividing the exponent — the
`∏_{v∈S} (b,a)_v` of Milne's Power Reciprocity Law, with `S` read to include the infinite
primes. Alongside it, the finite sets the law's hypotheses speak through: the exponent
places (primes over `n`), the valuation support of a global unit, and their union, the
bad places outside of which every local factor of a pair is trivial. The finite-place
factors are a symbol family argument, matching the characterization-only finite-place
layer; everything here is proved.

## Main definitions

* `powerResidueExponentFinitePlaces` — the primes dividing `n`, as a `Finset`.
* `unitFiniteSupport` — the finite places where a global unit has nontrivial valuation.
* `powerResidueBadFinitePlaces` — the supports of the two arguments and the exponent
  places.
* `powerResidueBadPlaceCorrection` — the correction term, parametric in the symbol
  family.

## Implementation notes

The unit support is the honest set `{v | v.valuation K a ≠ 1}` behind its finiteness
proof — numerator and denominator against `Ideal.finite_factors` — replacing the
source's chosen `S`-unit support
(`KummerTheory/Concrete/SUnitPreparation/FiniteRadicalSupport.lean:86`) with a canonical
one; the exponent places and the correction are the source's shape
(`GlobalClassFieldTheory/Reciprocity/PowerResidueReciprocity.lean:506, :1207, :1216`).
Milne's `S` in Theorem 5.11 is literally a set of prime ideals, but with `S` finite-only
the theorem fails at `K = ℚ`, `a = b = -1`, `n = 2` — the left side is `1`, the right
side `(-1,-1)_2 = -1` — and its proof uses the product formula over all places together
with the real-place evaluation, so the infinite factors belong to the correction; the
source spells them out and this item follows it.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open NumberField IsDedekindDomain

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

/-- The **exponent places**: the finitely many primes dividing `n` — Milne's `S`
([Milne 2020, Chap. VIII, §5, p.244][MilneCFT];
[Yamaguchi 2026, `GlobalClassFieldTheory/Reciprocity/PowerResidueReciprocity.lean:506`]
[Yamaguchi2026]). -/
noncomputable def powerResidueExponentFinitePlaces (n : ℕ) (hn : n ≠ 0) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (Ideal.finite_factors (I := Ideal.span {(n : 𝓞 K)})
    (by
      rw [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.mpr hn)).toFinset

/-- Membership in the exponent places is divisibility by the exponent ideal
([Milne 2020, Chap. VIII, §5, p.244][MilneCFT]). -/
@[simp]
theorem mem_powerResidueExponentFinitePlaces (n : ℕ) (hn : n ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ powerResidueExponentFinitePlaces K n hn ↔
      v.asIdeal ∣ Ideal.span {(n : 𝓞 K)} :=
  Set.Finite.mem_toFinset _

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
local unit ([Milne 2020, Chap. VIII, §5, p.244][MilneCFT];
[Yamaguchi 2026, `KummerTheory/Concrete/SUnitPreparation/FiniteRadicalSupport.lean:86`,
a chosen superset where this set is canonical][Yamaguchi2026]). -/
noncomputable def unitFiniteSupport (a : Kˣ) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (valuation_support_finite K a).toFinset

/-- Membership in the support is nontriviality of the valuation
([Milne 2020, Chap. VIII, §5, p.244][MilneCFT]). -/
@[simp]
theorem mem_unitFiniteSupport (a : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ unitFiniteSupport K a ↔ v.valuation K (a : K) ≠ 1 :=
  Set.Finite.mem_toFinset _

open scoped Classical in
/-- The **bad places** of a pair: the supports of the two arguments and the exponent
places — outside them, every finite-place Hilbert factor of the pair is trivial
([Milne 2020, Chap. VIII, §5, p.244 and Thm. 5.11, p.247][MilneCFT];
[Yamaguchi 2026, `GlobalClassFieldTheory/Reciprocity/PowerResidueReciprocity.lean:1207`]
[Yamaguchi2026]). -/
noncomputable def powerResidueBadFinitePlaces (n : ℕ) (hn : n ≠ 0) (a b : Kˣ) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (unitFiniteSupport K a ∪ unitFiniteSupport K b) ∪
    powerResidueExponentFinitePlaces K n hn

/-- The **bad-place correction** of power-residue reciprocity: all infinite-place
factors and the finite-place factors at the exponent places — Milne's `∏_{v∈S} (b,a)_v`
with the infinite primes included in `S`, parametric in the finite-place symbol family
([Milne 2020, Chap. VIII, §5, Thm. 5.11, p.247][MilneCFT];
[Yamaguchi 2026, `GlobalClassFieldTheory/Reciprocity/PowerResidueReciprocity.lean:1216`]
[Yamaguchi2026]). -/
noncomputable def powerResidueBadPlaceCorrection (n : ℕ) (hn : n ≠ 0)
    (h : ∀ _v : HeightOneSpectrum (𝓞 K), Kˣ → Kˣ → Kˣ) (a b : Kˣ) : Kˣ :=
  (∏ v : InfinitePlace K, infinitePlaceHilbertSymbol K n v a b) *
    ∏ v ∈ powerResidueExponentFinitePlaces K n hn, h v a b

end Atlas.Knowledge
