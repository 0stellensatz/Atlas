import Mathlib
import Atlas.Knowledge.InfinitePlaceHilbertSymbol
import Atlas.Knowledge.IsFinitePlaceHilbertSymbol
import Atlas.Knowledge.UnitFiniteSupport

/-!
# power residue bad place correction

The correction term of power-residue reciprocity: the product of all infinite-place
Hilbert factors and all finite-place factors at the primes dividing the exponent — the
`∏_{v∈S} (b,a)_v` of Milne's Power Reciprocity Law, with `S` read to include the infinite
primes. Alongside it, the sets that bound where a pair's local factors live: the exponent
places (primes over `n`) and, joined with the supports of the two arguments from
`Atlas.Knowledge.UnitFiniteSupport`, the bad places — outside which every finite-place
Hilbert factor of the pair is trivial, the one recorded claim here. The finite-place
factors are a symbol family argument, matching the characterization-only finite-place
layer; the definitions are proved.

## Main definitions

* `powerResidueExponentFinitePlaces` — the primes dividing `n`, as a `Finset`.
* `powerResidueBadFinitePlaces` — the supports of the two arguments and the exponent
  places.
* `powerResidueBadPlaceCorrection` — the correction term, parametric in the symbol
  family.

## Main statements

* `mem_powerResidueExponentFinitePlaces` — membership is divisibility by the exponent
  ideal.
* `IsFinitePlaceHilbertSymbol.eq_one_of_notMem_powerResidueBadFinitePlaces` — off the
  bad places the symbol dies; recorded ahead of its proof.

## Implementation notes

The exponent places and the correction are the source's shape
(`GlobalClassFieldTheory/Reciprocity/PowerResidueReciprocity.lean:506, :1207, :1216`),
the supports the canonical ones. Milne's `S` in Theorem 5.11 is literally a set of prime
ideals, but with `S` finite-only the theorem fails at `K = ℚ`, `a = b = -1`, `n = 2` —
the left side is `1`, the right side `(-1,-1)_2 = -1` — and its proof uses the product
formula over all places together with the real-place evaluation, so the infinite factors
belong to the correction; the source spells them out and this item follows it. The
triviality off the bad places is what makes the correction the *whole* correction — it is
the support half of Milne's proof of 5.11 — and its future proof is the tame evaluation
of `Atlas.Knowledge.PowerResidueReciprocity` with unit arguments.

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

open scoped Classical in
/-- The **bad places** of a pair: the supports of the two arguments and the exponent
places ([Milne 2020, Chap. VIII, §5, p.244 and Thm. 5.11, p.247][MilneCFT];
[Yamaguchi 2026, `GlobalClassFieldTheory/Reciprocity/PowerResidueReciprocity.lean:1207`]
[Yamaguchi2026]). -/
noncomputable def powerResidueBadFinitePlaces (n : ℕ) (hn : n ≠ 0) (a b : Kˣ) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (unitFiniteSupport K a ∪ unitFiniteSupport K b) ∪
    powerResidueExponentFinitePlaces K n hn

/-- Off the bad places of a pair, its finite-place Hilbert factor is trivial: both
arguments are local units at an unramified place prime to the exponent. Claim recorded
ahead of its proof ([Milne 2020, Chap. VIII, §5, 5.8, p.246][MilneCFT];
[Yamaguchi 2026, `GlobalClassFieldTheory/Reciprocity/PowerResidueReciprocity.lean:1236`]
[Yamaguchi2026]). -/
theorem IsFinitePlaceHilbertSymbol.eq_one_of_notMem_powerResidueBadFinitePlaces
    {n : ℕ} (hn : n ≠ 0) (hmu : (primitiveRoots n K).Nonempty)
    {v : HeightOneSpectrum (𝓞 K)} {h : Kˣ → Kˣ → Kˣ}
    (hh : IsFinitePlaceHilbertSymbol K n v h) (a b : Kˣ)
    (hv : v ∉ powerResidueBadFinitePlaces K n hn a b) : h a b = 1 := by
  sorry

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
