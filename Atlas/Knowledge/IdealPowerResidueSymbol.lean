import Mathlib
import Atlas.Knowledge.PrimeIdealPowerResidueSymbol

/-!
# ideal power residue symbol

The power residue symbol with an integral ideal in the denominator: for `𝔟 = ∏ 𝔭^{r_𝔭}`
away from `n` and from the numerator, `(a/𝔟) = ∏ (a/𝔭)^{r_𝔭}` — the multiplicative
extension of `Atlas.Knowledge.PrimeIdealPowerResidueSymbol` from primes to ideals, the
form power-residue reciprocity is stated in. The multiplicities are Mathlib's associates
counts, the product runs over the finite set of prime divisors, and the place-indexed
factor — the prime power extended by `1` off the divisors — carries the finite support
that lets the symbol enter `finprod` identities. Everything here is proved.

## Main definitions

* `idealPrimeDivisors` — the prime divisors of a nonzero ideal, as a `Finset`.
* `idealPowerResidueSymbol` — `(a/𝔟)`, valued in `μₙ(𝓞 K)`.
* `idealPowerResidueFactor` — the factor at one place, `1` off the divisors.

## Main statements

* `mem_idealPrimeDivisors` — membership is divisibility.
* `idealPowerResidueFactor_mulSupport_finite` — only divisors contribute.

## Implementation notes

The hypotheses — norms prime to `n`, numerator avoiding the primes — quantify over the
divisors of the denominator only, which is what lets the reciprocity statement instantiate
them from coprimality; the multiplicity is spelled as Mathlib's
`(Associates.mk P.asIdeal).count (Associates.mk I).factors` with no wrapper. The product
is an `attach`ed `Finset` product so each factor sees its own divisibility proof. The
source carries the same three layers with a named multiplicity function
(`AlgebraicNumberTheory/PowerResidueSymbols/Ideal.lean:264`, symbol at `:323`, factor at
`:347`, support at `:369`).

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

/-- The prime divisors of a nonzero integral ideal, as a `Finset`
([Milne 2020, Chap. VIII, §5, p.244][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/PowerResidueSymbols/Ideal.lean:300`). -/
noncomputable def idealPrimeDivisors (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (Ideal.finite_factors hI).toFinset

/-- Membership in the prime-divisor set is ordinary ideal divisibility. -/
@[simp]
theorem mem_idealPrimeDivisors (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (P : HeightOneSpectrum (𝓞 K)) :
    P ∈ idealPrimeDivisors K I hI ↔ P.asIdeal ∣ I :=
  Set.Finite.mem_toFinset _

/-- The **ideal power residue symbol** `(a/𝔟) = ∏ (a/𝔭)^{v_𝔭(𝔟)}`: the prime symbols of
the divisors of the denominator, each raised to its multiplicity
([Milne 2020, Chap. VIII, §5, p.244][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/PowerResidueSymbols/Ideal.lean:323`). -/
noncomputable def idealPowerResidueSymbol (I : Ideal (𝓞 K)) (hI : I ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hmu : (primitiveRoots n K).Nonempty) (a : 𝓞 K)
    (hcoprime : ∀ P : HeightOneSpectrum (𝓞 K), P.asIdeal ∣ I →
      (Ideal.absNorm P.asIdeal).Coprime n)
    (ha : ∀ P : HeightOneSpectrum (𝓞 K), P.asIdeal ∣ I → a ∉ P.asIdeal) :
    rootsOfUnity n (𝓞 K) :=
  ∏ P ∈ (idealPrimeDivisors K I hI).attach,
    primeIdealPowerResidueSymbol K P.1 hn hmu
        (hcoprime P.1 ((mem_idealPrimeDivisors K I hI P.1).mp P.2)) a
        (ha P.1 ((mem_idealPrimeDivisors K I hI P.1).mp P.2)) ^
      (Associates.mk P.1.asIdeal).count (Associates.mk I).factors

open scoped Classical in
/-- The prime-by-prime factor of the ideal symbol, extended by `1` away from the
divisors of the denominator ([Milne 2020, Chap. VIII, §5, p.244][MilneCFT];
Yamaguchi 2026, `AlgebraicNumberTheory/PowerResidueSymbols/Ideal.lean:347`). -/
noncomputable def idealPowerResidueFactor (I : Ideal (𝓞 K)) {n : ℕ} (hn : n ≠ 0)
    (hmu : (primitiveRoots n K).Nonempty) (a : 𝓞 K)
    (hcoprime : ∀ P : HeightOneSpectrum (𝓞 K), P.asIdeal ∣ I →
      (Ideal.absNorm P.asIdeal).Coprime n)
    (ha : ∀ P : HeightOneSpectrum (𝓞 K), P.asIdeal ∣ I → a ∉ P.asIdeal)
    (P : HeightOneSpectrum (𝓞 K)) : rootsOfUnity n (𝓞 K) :=
  if hP : P.asIdeal ∣ I then
    primeIdealPowerResidueSymbol K P hn hmu (hcoprime P hP) a (ha P hP) ^
      (Associates.mk P.asIdeal).count (Associates.mk I).factors
  else
    1

/-- Only divisors of the denominator contribute a nontrivial factor
(Yamaguchi 2026,
`AlgebraicNumberTheory/PowerResidueSymbols/Ideal.lean:369`). -/
theorem idealPowerResidueFactor_mulSupport_finite (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    {n : ℕ} (hn : n ≠ 0) (hmu : (primitiveRoots n K).Nonempty) (a : 𝓞 K)
    (hcoprime : ∀ P : HeightOneSpectrum (𝓞 K), P.asIdeal ∣ I →
      (Ideal.absNorm P.asIdeal).Coprime n)
    (ha : ∀ P : HeightOneSpectrum (𝓞 K), P.asIdeal ∣ I → a ∉ P.asIdeal) :
    (Function.mulSupport (idealPowerResidueFactor K I hn hmu a hcoprime ha)).Finite := by
  apply (Ideal.finite_factors hI).subset
  intro P hP
  rw [Function.mem_mulSupport] at hP
  by_contra hPdvd
  rw [Set.mem_setOf_eq] at hPdvd
  exact hP (by simp only [idealPowerResidueFactor, dif_neg hPdvd])

end Atlas.Knowledge
