import Mathlib
import Atlas.Knowledge.IsFinitePlaceHilbertSymbol
import Atlas.Knowledge.InfinitePlaceHilbertSymbol

/-!
# Hilbert product formula

The product formula for the Hilbert symbols of a number field containing the `n`-th roots
of unity: over all places, archimedean and finite, the symbols of two global units
multiply to one — `∏_v (a, b)_v = 1`, global reciprocity read on a principal idele. The
finite-place factors are any family satisfying
`Atlas.Knowledge.IsFinitePlaceHilbertSymbol`, each factor pinned by its characterization,
so the formula quantifies over the family rather than over a constructed symbol; the
archimedean factors are `Atlas.Knowledge.infinitePlaceHilbertSymbol`. Both statements —
that only finitely many finite places contribute, and the formula itself — are recorded
ahead of their proofs.

## Main statements

* `hilbertSymbol_mulSupport_finite` — a symbol family is `1` at all but finitely many
  places; recorded ahead of its proof.
* `hilbertProductFormula` — the all-places product is `1`; recorded ahead of its proof.

## Implementation notes

The finite part is a `finprod`, which is the whole of why the support statement is a
separate claim: over an infinite support the `finprod` is `1` by convention, and the
formula would hold vacuously — the support claim is what makes it say something. The
support itself is Milne's tame triviality: outside the places dividing `n` and the
supports of the two arguments, both arguments are units at an unramified place, so the
symbol dies. The formula's future proof is the source's: map the product of local Artin
factors of a principal idele through the Kummer root character
(`GlobalClassFieldTheory/Reciprocity/HilbertProductFormula.lean:172`, support at
`GlobalClassFieldTheory/Reciprocity/GlobalHilbertSymbol/FinitePlaceFiniteSupport.lean:29`)
— the idèle-class machinery enters there, not in the statement.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open NumberField IsDedekindDomain

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

/-- A finite-place Hilbert symbol family evaluates to `1` at all but finitely many
places: away from the divisors of `n` and the supports of the two arguments, the symbol
is tame with unit arguments. Claim recorded ahead of its proof
([Milne 2020, Chap. VIII, §5, 5.8, p.246][MilneCFT];
[Yamaguchi 2026,
`GlobalClassFieldTheory/Reciprocity/GlobalHilbertSymbol/FinitePlaceFiniteSupport.lean:29`]
[Yamaguchi2026]). -/
theorem hilbertSymbol_mulSupport_finite (n : ℕ) (hn : n ≠ 0)
    (hmu : (primitiveRoots n K).Nonempty)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), Kˣ → Kˣ → Kˣ)
    (hh : ∀ v, IsFinitePlaceHilbertSymbol K n v (h v)) (a b : Kˣ) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => h v a b).Finite := by
  sorry

/-- The **Hilbert product formula**: over all places of a number field containing the
`n`-th roots of unity, the Hilbert symbols of two global units multiply to one. Claim
recorded ahead of its proof
([Milne 2020, Chap. VIII, §5, 5.10, p.247][MilneCFT];
[Yamaguchi 2026, `GlobalClassFieldTheory/Reciprocity/HilbertProductFormula.lean:172`]
[Yamaguchi2026]). -/
theorem hilbertProductFormula (n : ℕ) (hn : n ≠ 0)
    (hmu : (primitiveRoots n K).Nonempty)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), Kˣ → Kˣ → Kˣ)
    (hh : ∀ v, IsFinitePlaceHilbertSymbol K n v (h v)) (a b : Kˣ) :
    (∏ v : InfinitePlace K, infinitePlaceHilbertSymbol K n v a b) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), h v a b = 1 := by
  sorry

end Atlas.Knowledge
