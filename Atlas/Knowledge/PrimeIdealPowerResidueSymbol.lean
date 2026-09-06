import Mathlib
import Atlas.Knowledge.FiniteFieldPowerResidueSymbol

/-!
# prime-ideal power residue symbol

The `n`-th power residue symbol `(a/𝔭)` of a number field containing the `n`-th roots of
unity, at a prime ideal whose norm is prime to `n`: reduction modulo `𝔭` identifies the
integral `n`-th roots of unity with those of the residue field, and the symbol is the
finite-field character `a ↦ a^{(N𝔭−1)/n}` of
`Atlas.Knowledge.FiniteFieldPowerResidueSymbol` pulled back along that identification.
Everything here is proved: the divisibility `n ∣ N𝔭 − 1`, the reduction equivalence, the
congruence characterizing the symbol, the power criterion, and multiplicativity.

## Main definitions

* `rootsOfUnityQuotientEquiv` — `μₙ(𝓞 K) ≃* μₙ(𝓞 K ⧸ 𝔭)` away from `n`.
* `primeIdealResidueUnit` — an integer prime to `𝔭` as a residue-field unit.
* `primeIdealPowerResidueSymbol` — `(a/𝔭)`, valued in `μₙ(𝓞 K)`.

## Main statements

* `dvd_absNorm_sub_one_of_primitiveRoots` — `n ∣ N𝔭 − 1` at every prime away from `n`.
* `rootsOfUnityQuotientEquiv_primeIdealPowerResidueSymbol` — reduction sends `(a/𝔭)` to
  `a^{(N𝔭−1)/n}`, the literature's defining congruence.
* `primeIdealPowerResidueSymbol_eq_one_iff` — `(a/𝔭) = 1` iff `a` is an `n`-th power
  mod `𝔭`.
* `primeIdealPowerResidueSymbol_mul` — multiplicativity in the numerator.

## Implementation notes

The reduction homomorphism is Mathlib's `Ideal.rootsOfUnityMapQuot` with codomain
restricted to the residue roots of unity; injectivity is Mathlib's, and surjectivity is
the cardinality count — `μₙ(𝓞 K)` has exactly `n` elements by the primitive root, the
residue side at most `n` — so the equivalence costs one `Fintype` comparison. The residue
field structure enters through `Ideal.Quotient.field` as a local instance, and its
`Fintype` is `Fintype.ofFinite`, both confined to this file: no downstream statement
mentions them. The source builds the same chain with a hand-rolled reduction map
(`AlgebraicNumberTheory/PowerResidueSymbols/Ideal.lean:35`, equivalence at `:94`, symbol
at `:174`).

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open NumberField IsDedekindDomain

namespace Atlas.Knowledge

attribute [local instance] Ideal.Quotient.field

variable (K : Type*) [Field K] [NumberField K]

noncomputable local instance (P : HeightOneSpectrum (𝓞 K)) :
    Fintype (𝓞 K ⧸ P.asIdeal) :=
  Fintype.ofFinite _

/-- The residue field at a prime has the absolute norm as cardinality
([Milne 2020, Chap. VIII, §5, p.244][MilneCFT]). -/
theorem card_quotient_eq_absNorm (P : HeightOneSpectrum (𝓞 K)) :
    Fintype.card (𝓞 K ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
  rw [← Nat.card_eq_fintype_card, Ideal.absNorm_apply, Submodule.cardQuot_apply]

/-- If `K` contains the `n`-th roots of unity, then `n` divides `N𝔭 − 1` at every prime
`𝔭` away from `n` ([Milne 2020, Chap. VIII, §5, p.244][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/PowerResidueSymbols/Ideal.lean:66`). -/
theorem dvd_absNorm_sub_one_of_primitiveRoots (P : HeightOneSpectrum (𝓞 K)) {n : ℕ}
    (hn : n ≠ 0) (hmu : (primitiveRoots n K).Nonempty)
    (hcoprime : (Ideal.absNorm P.asIdeal).Coprime n) :
    n ∣ Ideal.absNorm P.asIdeal - 1 := by
  haveI : NeZero n := ⟨hn⟩
  obtain ⟨zeta, hzeta⟩ := hmu
  have hzetaK : IsPrimitiveRoot zeta n := (mem_primitiveRoots (Nat.pos_of_ne_zero hn)).1 hzeta
  have hcard : Nat.card (rootsOfUnity n (𝓞 K)) = n :=
    hzetaK.toInteger_isPrimitiveRoot.card_rootsOfUnity
  have hdvd := Subgroup.card_dvd_of_injective (Ideal.rootsOfUnityMapQuot P.asIdeal n)
    (Ideal.rootsOfUnityMapQuot_injective n
      (Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top) hcoprime)
  rw [hcard, Nat.card_units] at hdvd
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact hdvd

private noncomputable def rootsOfUnityQuotientHom (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    rootsOfUnity n (𝓞 K) →* rootsOfUnity n (𝓞 K ⧸ P.asIdeal) :=
  (Ideal.rootsOfUnityMapQuot P.asIdeal n).codRestrict _ fun z => by
    rw [mem_rootsOfUnity, ← map_pow]
    have hz : z ^ n = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, OneMemClass.coe_one]
      exact z.2
    rw [hz, map_one]

private theorem rootsOfUnityQuotientHom_bijective (P : HeightOneSpectrum (𝓞 K)) {n : ℕ}
    (hn : n ≠ 0) (hmu : (primitiveRoots n K).Nonempty)
    (hcoprime : (Ideal.absNorm P.asIdeal).Coprime n) :
    Function.Bijective (rootsOfUnityQuotientHom K P n) := by
  haveI : NeZero n := ⟨hn⟩
  letI : Fintype (rootsOfUnity n (𝓞 K)) := Fintype.ofFinite _
  letI : Fintype (rootsOfUnity n (𝓞 K ⧸ P.asIdeal)) := Fintype.ofFinite _
  have hinjective : Function.Injective (rootsOfUnityQuotientHom K P n) := by
    intro z w hzw
    exact Ideal.rootsOfUnityMapQuot_injective n
      (Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top) hcoprime
      (congrArg Subtype.val hzw)
  have hsource : Fintype.card (rootsOfUnity n (𝓞 K)) = n := by
    obtain ⟨zeta, hzeta⟩ := hmu
    have hzetaK : IsPrimitiveRoot zeta n :=
      (mem_primitiveRoots (Nat.pos_of_ne_zero hn)).1 hzeta
    rw [← Nat.card_eq_fintype_card]
    exact hzetaK.toInteger_isPrimitiveRoot.card_rootsOfUnity
  have htarget_le : Fintype.card (rootsOfUnity n (𝓞 K ⧸ P.asIdeal)) ≤ n := by
    rw [← Nat.card_eq_fintype_card]
    exact card_rootsOfUnity (𝓞 K ⧸ P.asIdeal) n
  have hsource_le := Fintype.card_le_of_injective _ hinjective
  exact (Fintype.bijective_iff_injective_and_card _).2 ⟨hinjective, by omega⟩

/-- Away from `n`, reduction identifies the integral `n`-th roots of unity with those of
the residue field — Milne's bijection `μₙ(K) → μₙ(𝒪_K/𝔭)`
([Milne 2020, Chap. VIII, §5, p.244][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/PowerResidueSymbols/Ideal.lean:94`). -/
noncomputable def rootsOfUnityQuotientEquiv (P : HeightOneSpectrum (𝓞 K)) {n : ℕ}
    (hn : n ≠ 0) (hmu : (primitiveRoots n K).Nonempty)
    (hcoprime : (Ideal.absNorm P.asIdeal).Coprime n) :
    rootsOfUnity n (𝓞 K) ≃* rootsOfUnity n (𝓞 K ⧸ P.asIdeal) :=
  MulEquiv.ofBijective (rootsOfUnityQuotientHom K P n)
    (rootsOfUnityQuotientHom_bijective K P hn hmu hcoprime)

/-- The reduction equivalence acts by reduction modulo the prime. -/
@[simp]
theorem rootsOfUnityQuotientEquiv_apply (P : HeightOneSpectrum (𝓞 K)) {n : ℕ}
    (hn : n ≠ 0) (hmu : (primitiveRoots n K).Nonempty)
    (hcoprime : (Ideal.absNorm P.asIdeal).Coprime n) (z : rootsOfUnity n (𝓞 K)) :
    (rootsOfUnityQuotientEquiv K P hn hmu hcoprime z : (𝓞 K ⧸ P.asIdeal)ˣ) =
      Ideal.rootsOfUnityMapQuot P.asIdeal n z :=
  rfl

/-- An algebraic integer prime to `𝔭`, regarded as a unit of the residue field
([Milne 2020, Chap. VIII, §5, p.244][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/PowerResidueSymbols/Ideal.lean:152`). -/
noncomputable def primeIdealResidueUnit (P : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K)
    (ha : a ∉ P.asIdeal) : (𝓞 K ⧸ P.asIdeal)ˣ :=
  Units.mk0 (Ideal.Quotient.mk P.asIdeal a) (by
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact ha)

@[simp]
theorem primeIdealResidueUnit_mul (P : HeightOneSpectrum (𝓞 K)) (a b : 𝓞 K)
    (ha : a ∉ P.asIdeal) (hb : b ∉ P.asIdeal) (hab : a * b ∉ P.asIdeal) :
    primeIdealResidueUnit K P (a * b) hab =
      primeIdealResidueUnit K P a ha * primeIdealResidueUnit K P b hb := by
  apply Units.ext
  exact map_mul (Ideal.Quotient.mk P.asIdeal) a b

/-- The **prime-ideal power residue symbol** `(a/𝔭)`, valued in the integral `n`-th roots
of unity: the finite-field character of the residue of `a`, pulled back along the
reduction equivalence ([Milne 2020, Chap. VIII, §5, p.244][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/PowerResidueSymbols/Ideal.lean:174`). -/
noncomputable def primeIdealPowerResidueSymbol (P : HeightOneSpectrum (𝓞 K)) {n : ℕ}
    (hn : n ≠ 0) (hmu : (primitiveRoots n K).Nonempty)
    (hcoprime : (Ideal.absNorm P.asIdeal).Coprime n) (a : 𝓞 K) (ha : a ∉ P.asIdeal) :
    rootsOfUnity n (𝓞 K) :=
  (rootsOfUnityQuotientEquiv K P hn hmu hcoprime).symm
    (finiteFieldPowerResidueSymbol (𝓞 K ⧸ P.asIdeal) n
      (by
        rw [card_quotient_eq_absNorm]
        exact dvd_absNorm_sub_one_of_primitiveRoots K P hn hmu hcoprime)
      (primeIdealResidueUnit K P a ha))

/-- Reduction sends `(a/𝔭)` to `a^{(N𝔭−1)/n}` — the defining congruence
`(a/𝔭) ≡ a^{(N𝔭−1)/n} mod 𝔭` ([Milne 2020, Chap. VIII, §5, p.244][MilneCFT];
Yamaguchi 2026,
`AlgebraicNumberTheory/PowerResidueSymbols/Ideal.lean:190`). -/
theorem rootsOfUnityQuotientEquiv_primeIdealPowerResidueSymbol
    (P : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : n ≠ 0)
    (hmu : (primitiveRoots n K).Nonempty)
    (hcoprime : (Ideal.absNorm P.asIdeal).Coprime n) (a : 𝓞 K) (ha : a ∉ P.asIdeal)
    (hdvd : n ∣ Fintype.card (𝓞 K ⧸ P.asIdeal) - 1) :
    rootsOfUnityQuotientEquiv K P hn hmu hcoprime
        (primeIdealPowerResidueSymbol K P hn hmu hcoprime a ha) =
      finiteFieldPowerResidueSymbol (𝓞 K ⧸ P.asIdeal) n hdvd
        (primeIdealResidueUnit K P a ha) := by
  rw [primeIdealPowerResidueSymbol]
  exact (rootsOfUnityQuotientEquiv K P hn hmu hcoprime).apply_symm_apply _

/-- The prime-ideal symbol is one exactly when `a` is an `n`-th power modulo `𝔭`
([Milne 2020, Chap. VIII, §5, 5.2, p.244][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/PowerResidueSymbols/Ideal.lean:208`). -/
theorem primeIdealPowerResidueSymbol_eq_one_iff (P : HeightOneSpectrum (𝓞 K)) {n : ℕ}
    (hn : n ≠ 0) (hmu : (primitiveRoots n K).Nonempty)
    (hcoprime : (Ideal.absNorm P.asIdeal).Coprime n) (a : 𝓞 K) (ha : a ∉ P.asIdeal) :
    primeIdealPowerResidueSymbol K P hn hmu hcoprime a ha = 1 ↔
      ∃ u : (𝓞 K ⧸ P.asIdeal)ˣ, u ^ n = primeIdealResidueUnit K P a ha := by
  have hdvd : n ∣ Fintype.card (𝓞 K ⧸ P.asIdeal) - 1 := by
    rw [card_quotient_eq_absNorm]
    exact dvd_absNorm_sub_one_of_primitiveRoots K P hn hmu hcoprime
  rw [← finiteFieldPowerResidueSymbol_eq_one_iff n hdvd]
  constructor
  · intro h
    have hred := congrArg (rootsOfUnityQuotientEquiv K P hn hmu hcoprime) h
    rwa [rootsOfUnityQuotientEquiv_primeIdealPowerResidueSymbol, map_one] at hred
  · intro h
    apply (rootsOfUnityQuotientEquiv K P hn hmu hcoprime).injective
    rwa [rootsOfUnityQuotientEquiv_primeIdealPowerResidueSymbol, map_one]

/-- Multiplicativity of `(a/𝔭)` in the numerator
([Milne 2020, Chap. VIII, §5, 5.1, p.244][MilneCFT];
Yamaguchi 2026,
`AlgebraicNumberTheory/PowerResidueSymbols/Ideal.lean:238`). -/
theorem primeIdealPowerResidueSymbol_mul (P : HeightOneSpectrum (𝓞 K)) {n : ℕ}
    (hn : n ≠ 0) (hmu : (primitiveRoots n K).Nonempty)
    (hcoprime : (Ideal.absNorm P.asIdeal).Coprime n) (a b : 𝓞 K) (ha : a ∉ P.asIdeal)
    (hb : b ∉ P.asIdeal) (hab : a * b ∉ P.asIdeal) :
    primeIdealPowerResidueSymbol K P hn hmu hcoprime (a * b) hab =
      primeIdealPowerResidueSymbol K P hn hmu hcoprime a ha *
        primeIdealPowerResidueSymbol K P hn hmu hcoprime b hb := by
  apply (rootsOfUnityQuotientEquiv K P hn hmu hcoprime).injective
  have hdvd : n ∣ Fintype.card (𝓞 K ⧸ P.asIdeal) - 1 := by
    rw [card_quotient_eq_absNorm]
    exact dvd_absNorm_sub_one_of_primitiveRoots K P hn hmu hcoprime
  rw [map_mul,
    rootsOfUnityQuotientEquiv_primeIdealPowerResidueSymbol K P hn hmu hcoprime _ _ hdvd,
    rootsOfUnityQuotientEquiv_primeIdealPowerResidueSymbol K P hn hmu hcoprime _ _ hdvd,
    rootsOfUnityQuotientEquiv_primeIdealPowerResidueSymbol K P hn hmu hcoprime _ _ hdvd,
    primeIdealResidueUnit_mul K P a b ha hb hab, map_mul]

end Atlas.Knowledge
