import Mathlib
import Atlas.Knowledge.StandardLubinTateSeries

/-!
# standard Lubin–Tate polynomial

The division-polynomial layer of the standard Lubin–Tate tower: the polynomial
`X ^ q + π X` underlying the standard series, its compositional iterates `f^[n]`, and the
primitive part `Qₙ = (f^[n])^(q−1) + π`, with the purely polynomial factorization
`f^[n+1] = f^[n] · Qₙ` — the identity that makes the level tower a chain of simple
extensions. Monicity, degrees, and the Eisenstein-side constant coefficient are proved;
no root, irreducibility, or extension claim is made here — that is
`Atlas.Knowledge.standardLubinTateLevelField`'s business. Everything here is proved.

## Main definitions

* `standardLubinTatePolynomial` — `X ^ q + π X`.
* `standardLubinTatePolynomialIterate` — the `n`-fold composition iterate.
* `standardLubinTatePrimitivePolynomial` — `(f^[n])^(q−1) + π`.

## Main statements

* `standardLubinTatePolynomialIterate_succ_factor` — `f^[n+1] = f^[n] · Qₙ`.
* `standardLubinTatePrimitivePolynomial_natDegree`, `_monic`, `_coeff_zero` — the
  Eisenstein-side data.

## Implementation notes

The ambient is the layer's abstract discrete valuation ring, with the finite residue
field entering only where `q ≥ 2` is needed; the polynomial is the standard series'
polynomial (`standardLubinTatePolynomial_coe` states the identification against
`Atlas.Knowledge.standardLubinTateSeries`, with the summands in the series' order). The
source keeps the same three layers and the same factorization
(`LubinTate/FiniteLevel/DivisionPolynomial.lean:43, :124, :191`).

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open Polynomial

namespace Atlas.Knowledge

variable (A : Type*) [CommRing A] [IsLocalRing A] (π : A)

/-- The polynomial `X ^ q + π X` underlying the standard Lubin–Tate series
([Milne 2020, Chap. I, §2, Ex. 2.10 (a), p.32][MilneCFT]; Yamaguchi 2026,
`LubinTate/FiniteLevel/DivisionPolynomial.lean:43`). -/
noncomputable def standardLubinTatePolynomial : Polynomial A :=
  Polynomial.X ^ Nat.card (IsLocalRing.ResidueField A) + Polynomial.C π * Polynomial.X

/-- The `n`-fold compositional iterate of the standard polynomial, from `X`
([Milne 2020, Chap. I, §3, p.36][MilneCFT]; Yamaguchi 2026,
`LubinTate/FiniteLevel/DivisionPolynomial.lean:124`). -/
noncomputable def standardLubinTatePolynomialIterate (n : ℕ) : Polynomial A :=
  ((standardLubinTatePolynomial A π).comp)^[n] Polynomial.X

/-- The primitive quotient polynomial at level `n + 1`, `(f^[n])^(q−1) + π`
([Milne 2020, Chap. I, §3, pp.38–39][MilneCFT]; Yamaguchi 2026,
`LubinTate/FiniteLevel/DivisionPolynomial.lean:191`). -/
noncomputable def standardLubinTatePrimitivePolynomial (n : ℕ) : Polynomial A :=
  standardLubinTatePolynomialIterate A π n ^
      (Nat.card (IsLocalRing.ResidueField A) - 1) +
    Polynomial.C π

/-- The polynomial is the standard series, summand for summand. -/
theorem standardLubinTatePolynomial_coe {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)] {π : A}
    (hπ : Irreducible π) :
    (standardLubinTatePolynomial A π : PowerSeries A) =
      (standardLubinTateSeries hπ).toPowerSeries := by
  rw [standardLubinTatePolynomial, standardLubinTateSeries_toPowerSeries,
    Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_mul, Polynomial.coe_C,
    Polynomial.coe_X, add_comm]

@[simp]
theorem standardLubinTatePolynomialIterate_zero :
    standardLubinTatePolynomialIterate A π 0 = Polynomial.X :=
  rfl

theorem standardLubinTatePolynomialIterate_succ (n : ℕ) :
    standardLubinTatePolynomialIterate A π (n + 1) =
      (standardLubinTatePolynomial A π).comp
        (standardLubinTatePolynomialIterate A π n) :=
  Function.iterate_succ_apply' _ n _

/-- The tower factorization `f^[n+1] = f^[n] · Qₙ` — purely polynomial
([Milne 2020, Chap. I, §3, pp.38–39][MilneCFT]; Yamaguchi 2026,
`LubinTate/FiniteLevel/DivisionPolynomial.lean:267`,
`standardLubinTatePolynomialIterate_succ_factor`). -/
theorem standardLubinTatePolynomialIterate_succ_factor
    [Finite (IsLocalRing.ResidueField A)] (n : ℕ) :
    standardLubinTatePolynomialIterate A π (n + 1) =
      standardLubinTatePolynomialIterate A π n *
        standardLubinTatePrimitivePolynomial A π n := by
  have hq : 1 ≤ Nat.card (IsLocalRing.ResidueField A) :=
    le_of_lt (Finite.one_lt_card (α := IsLocalRing.ResidueField A))
  rw [standardLubinTatePolynomialIterate_succ, standardLubinTatePolynomial,
    Polynomial.add_comp, Polynomial.X_pow_comp, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.X_comp, standardLubinTatePrimitivePolynomial]
  have hpow : standardLubinTatePolynomialIterate A π n ^
      Nat.card (IsLocalRing.ResidueField A) =
      standardLubinTatePolynomialIterate A π n *
        standardLubinTatePolynomialIterate A π n ^
          (Nat.card (IsLocalRing.ResidueField A) - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hpow]
  ring

/-- The standard polynomial is monic of degree `q`. -/
theorem standardLubinTatePolynomial_monic [Finite (IsLocalRing.ResidueField A)] :
    (standardLubinTatePolynomial A π).Monic := by
  apply Polynomial.monic_X_pow_add
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_le π) ?_
  exact_mod_cast Finite.one_lt_card (α := IsLocalRing.ResidueField A)

theorem standardLubinTatePolynomial_natDegree [Finite (IsLocalRing.ResidueField A)] :
    (standardLubinTatePolynomial A π).natDegree =
      Nat.card (IsLocalRing.ResidueField A) := by
  apply Polynomial.natDegree_eq_of_degree_eq_some
  rw [standardLubinTatePolynomial,
    Polynomial.degree_add_eq_left_of_degree_lt, Polynomial.degree_X_pow]
  rw [Polynomial.degree_X_pow]
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_le π) ?_
  exact_mod_cast Finite.one_lt_card (α := IsLocalRing.ResidueField A)

theorem standardLubinTatePolynomialIterate_natDegree
    [Finite (IsLocalRing.ResidueField A)] [IsDomain A] (n : ℕ) :
    (standardLubinTatePolynomialIterate A π n).natDegree =
      Nat.card (IsLocalRing.ResidueField A) ^ n := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [standardLubinTatePolynomialIterate_succ, Polynomial.natDegree_comp,
      standardLubinTatePolynomial_natDegree, IH, pow_succ']

theorem standardLubinTatePolynomialIterate_monic
    [Finite (IsLocalRing.ResidueField A)] [IsDomain A] (n : ℕ) :
    (standardLubinTatePolynomialIterate A π n).Monic := by
  induction n with
  | zero => exact Polynomial.monic_X
  | succ n IH =>
    rw [standardLubinTatePolynomialIterate_succ]
    refine (standardLubinTatePolynomial_monic A π).comp IH ?_
    rw [standardLubinTatePolynomialIterate_natDegree]
    exact pow_ne_zero n (by
      have := Finite.one_lt_card (α := IsLocalRing.ResidueField A)
      omega)

theorem standardLubinTatePolynomialIterate_eval_zero
    [Finite (IsLocalRing.ResidueField A)] (n : ℕ) :
    Polynomial.eval 0 (standardLubinTatePolynomialIterate A π n) = 0 := by
  have hq : Nat.card (IsLocalRing.ResidueField A) ≠ 0 := by
    have := Finite.one_lt_card (α := IsLocalRing.ResidueField A)
    omega
  induction n with
  | zero => simp
  | succ n IH =>
    rw [standardLubinTatePolynomialIterate_succ, Polynomial.eval_comp, IH,
      standardLubinTatePolynomial]
    simp [hq]

/-- The primitive part is monic. -/
theorem standardLubinTatePrimitivePolynomial_monic
    [Finite (IsLocalRing.ResidueField A)] [IsDomain A] (n : ℕ) :
    (standardLubinTatePrimitivePolynomial A π n).Monic := by
  refine Polynomial.Monic.add_of_left
    ((standardLubinTatePolynomialIterate_monic A π n).pow _) ?_
  refine lt_of_le_of_lt Polynomial.degree_C_le ?_
  rw [Polynomial.degree_eq_natDegree
    (((standardLubinTatePolynomialIterate_monic A π n).pow _).ne_zero),
    ((standardLubinTatePolynomialIterate_monic A π n).natDegree_pow _),
    standardLubinTatePolynomialIterate_natDegree]
  have hq : 1 < Nat.card (IsLocalRing.ResidueField A) :=
    Finite.one_lt_card (α := IsLocalRing.ResidueField A)
  have hqpos : 0 < Nat.card (IsLocalRing.ResidueField A) := by omega
  exact_mod_cast Nat.mul_pos (by omega) (Nat.pow_pos hqpos)

/-- The primitive part has degree `(q − 1) · qⁿ`. -/
theorem standardLubinTatePrimitivePolynomial_natDegree
    [Finite (IsLocalRing.ResidueField A)] [IsDomain A] (n : ℕ) :
    (standardLubinTatePrimitivePolynomial A π n).natDegree =
      (Nat.card (IsLocalRing.ResidueField A) - 1) *
        Nat.card (IsLocalRing.ResidueField A) ^ n := by
  have hq : 1 < Nat.card (IsLocalRing.ResidueField A) :=
    Finite.one_lt_card (α := IsLocalRing.ResidueField A)
  have hqpos : 0 < Nat.card (IsLocalRing.ResidueField A) := by omega
  have hposdeg : 0 < (Nat.card (IsLocalRing.ResidueField A) - 1) *
      Nat.card (IsLocalRing.ResidueField A) ^ n :=
    Nat.mul_pos (by omega) (Nat.pow_pos hqpos)
  apply Polynomial.natDegree_eq_of_degree_eq_some
  rw [standardLubinTatePrimitivePolynomial, Polynomial.degree_add_eq_left_of_degree_lt]
  · rw [Polynomial.degree_eq_natDegree
      (((standardLubinTatePolynomialIterate_monic A π n).pow _).ne_zero),
      ((standardLubinTatePolynomialIterate_monic A π n).natDegree_pow _),
      standardLubinTatePolynomialIterate_natDegree]
  · refine lt_of_le_of_lt Polynomial.degree_C_le ?_
    rw [Polynomial.degree_eq_natDegree
      (((standardLubinTatePolynomialIterate_monic A π n).pow _).ne_zero),
      ((standardLubinTatePolynomialIterate_monic A π n).natDegree_pow _),
      standardLubinTatePolynomialIterate_natDegree]
    exact_mod_cast hposdeg

/-- The Eisenstein-side constant coefficient: `Qₙ(0) = π`
(Yamaguchi 2026,
`LubinTate/FiniteLevel/DivisionPolynomial.lean:255`). -/
theorem standardLubinTatePrimitivePolynomial_coeff_zero
    [Finite (IsLocalRing.ResidueField A)] (n : ℕ) :
    (standardLubinTatePrimitivePolynomial A π n).coeff 0 = π := by
  have hq : 1 < Nat.card (IsLocalRing.ResidueField A) :=
    Finite.one_lt_card (α := IsLocalRing.ResidueField A)
  rw [standardLubinTatePrimitivePolynomial, Polynomial.coeff_add,
    Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow,
    standardLubinTatePolynomialIterate_eval_zero,
    zero_pow (by omega : Nat.card (IsLocalRing.ResidueField A) - 1 ≠ 0),
    Polynomial.coeff_C_zero, zero_add]

end Atlas.Knowledge
