import Mathlib
import Atlas.Knowledge.IsFinitePlaceHilbertSymbol
import Atlas.Knowledge.PrimeIdealPowerResidueSymbol
import Atlas.Knowledge.IdealPowerResidueSymbol
import Atlas.Knowledge.PowerResidueBadPlaceCorrection

/-!
# power residue reciprocity

The general power reciprocity law of a number field containing the `n`-th roots of unity,
and the tame identification it rests on. The identification is Milne's 5.8: at a place
prime to `n` where the first argument is a unit, the finite-place Hilbert symbol *is* the
prime power residue symbol raised to the valuation of the second argument — the statement
that welds the characterization-only Hilbert layer to the constructive power-residue
layer. The law is Milne's Theorem 5.11 in the source's spelling: the symbol of `a` over
`(b)` equals the inverse of the bad-place correction times the symbol of `b` over `(a)`.
Both are recorded ahead of their proofs.

## Main statements

* `IsFinitePlaceHilbertSymbol.tame_eq` — the tame evaluation; recorded ahead of its
  proof.
* `powerResidueReciprocity` — the law with bad-place correction; recorded ahead of its
  proof.

## Implementation notes

The two ideal symbols force the hypothesis set: norms of the primes under each
denominator prime to `n`, and each numerator avoiding the other's primes — together they
say the supports of `a` and `b` are disjoint and away from `n`, which is Milne's
`S(a) ∩ S(b) = S`; the source carries the away-from-`n` condition a second time in the
exponent-place spelling (`GlobalClassFieldTheory/Reciprocity/PowerResidueReciprocity.lean:1617`),
equivalent to the norm-coprimality already present, and Atlas drops the duplicate. The
field units of `a` and `b` that feed the correction enter as pinned units — quantified
`Kˣ` elements with their values prescribed — rather than by an embedded nonzero-lift.
Milne writes the correction as `∏_{v∈S} (b,a)_v`; the spelling here inverts the
family's `(a,b)`-factors instead, equal by skew-symmetry, and the infinite primes are in
the correction as `Atlas.Knowledge.powerResidueBadPlaceCorrection` records. The tame
claim's future proof runs through `Atlas.Knowledge.LocalHilbertSymbolTameFormula` and the
reduction injectivity of `Atlas.Knowledge.PrimeIdealPowerResidueSymbol`; the law's is the
source's, from the product formula (`:1601`, law at `:1617`).

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open NumberField IsDedekindDomain

namespace Atlas.Knowledge

variable {K : Type*} [Field K] [NumberField K]

/-- The **tame evaluation** of the finite-place Hilbert symbol: at a place prime to `n`
with the first argument a local unit, the symbol is the prime power residue symbol raised
to the valuation of the second argument — `(a,b)_v = (a/𝔭_v)^{ord_v(b)}`. Claim recorded
ahead of its proof ([Milne 2020, Chap. VIII, §5, 5.8, p.246][MilneCFT];
[Yamaguchi 2026, `GlobalClassFieldTheory/Reciprocity/PowerResidueReciprocity.lean:1017`]
[Yamaguchi2026]). -/
theorem IsFinitePlaceHilbertSymbol.tame_eq {n : ℕ} (hn : n ≠ 0)
    (hmu : (primitiveRoots n K).Nonempty) {v : HeightOneSpectrum (𝓞 K)}
    {h : Kˣ → Kˣ → Kˣ} (hh : IsFinitePlaceHilbertSymbol K n v h)
    (hcoprime : (Ideal.absNorm v.asIdeal).Coprime n)
    (a b : 𝓞 K) (ha : a ∉ v.asIdeal) (ua ub : Kˣ)
    (hua : (ua : K) = algebraMap (𝓞 K) K a) (hub : (ub : K) = algebraMap (𝓞 K) K b) :
    h ua ub =
      Units.map (algebraMap (𝓞 K) K).toMonoidHom
        ((primeIdealPowerResidueSymbol K v hn hmu hcoprime a ha ^
          (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {b})).factors :
            rootsOfUnity n (𝓞 K)) : (𝓞 K)ˣ) := by
  sorry

/-- The **power reciprocity law**: for `a` and `b` with disjoint supports away from `n`,
the symbol of `a` over `(b)` is the inverse of the bad-place correction times the symbol
of `b` over `(a)` — Milne's `(a/b)(b/a)⁻¹ = ∏_{v∈S}(b,a)_v`, the correction inverted
against the family's `(a,b)`-factors by skew-symmetry. Claim recorded ahead of its proof
([Milne 2020, Chap. VIII, §5, Thm. 5.11, p.247][MilneCFT];
[Yamaguchi 2026, `GlobalClassFieldTheory/Reciprocity/PowerResidueReciprocity.lean:1617`]
[Yamaguchi2026]). -/
theorem powerResidueReciprocity {n : ℕ} (hn : n ≠ 0)
    (hmu : (primitiveRoots n K).Nonempty)
    (h : ∀ _v : HeightOneSpectrum (𝓞 K), Kˣ → Kˣ → Kˣ)
    (hh : ∀ v, IsFinitePlaceHilbertSymbol K n v (h v))
    (a b : 𝓞 K) (hIa : Ideal.span {a} ≠ 0) (hIb : Ideal.span {b} ≠ 0)
    (hcoprimeA : ∀ P : HeightOneSpectrum (𝓞 K), P.asIdeal ∣ Ideal.span {a} →
      (Ideal.absNorm P.asIdeal).Coprime n)
    (hcoprimeB : ∀ P : HeightOneSpectrum (𝓞 K), P.asIdeal ∣ Ideal.span {b} →
      (Ideal.absNorm P.asIdeal).Coprime n)
    (haB : ∀ P : HeightOneSpectrum (𝓞 K), P.asIdeal ∣ Ideal.span {b} → a ∉ P.asIdeal)
    (hbA : ∀ P : HeightOneSpectrum (𝓞 K), P.asIdeal ∣ Ideal.span {a} → b ∉ P.asIdeal)
    (ua ub : Kˣ)
    (hua : (ua : K) = algebraMap (𝓞 K) K a) (hub : (ub : K) = algebraMap (𝓞 K) K b) :
    Units.map (algebraMap (𝓞 K) K).toMonoidHom
        ((idealPowerResidueSymbol K (Ideal.span {b}) hIb hn hmu a hcoprimeB haB :
          rootsOfUnity n (𝓞 K)) : (𝓞 K)ˣ) =
      (powerResidueBadPlaceCorrection K n hn h ua ub)⁻¹ *
        Units.map (algebraMap (𝓞 K) K).toMonoidHom
          ((idealPowerResidueSymbol K (Ideal.span {a}) hIa hn hmu b hcoprimeA hbA :
            rootsOfUnity n (𝓞 K)) : (𝓞 K)ˣ) := by
  sorry

end Atlas.Knowledge
