import Mathlib
import Atlas.Knowledge.StandardLubinTatePolynomial

/-!
# standard Lubin–Tate level field

The level tower of the standard Lubin–Tate construction: over the fraction field `K` of
the layer's discrete valuation ring, the primitive division polynomial `Qₙ` is Eisenstein
at `π` — its reduction is a power of `X` because the iterate reduces to the `qⁿ`-power
Frobenius — hence irreducible, and separable because its derivative is a product of
nonzero factors, `(f^[n])′(0) = πⁿ` and `q − 1 ≠ 0` in `K`. A root is chosen in the
separable closure, and the level field is the simple extension it generates, of degree
`(q−1)·qⁿ`. Everything here is proved — the choice is `Classical.choose` of a proved
existence, not a recorded claim.

## Main definitions

* `standardLubinTatePrimitivePolynomialOverField` — `Qₙ` over `K`.
* `chosenStandardLubinTatePrimitiveRoot` — a chosen root in `SeparableClosure K`.
* `standardLubinTateLevelField` — the simple extension it generates.
* `standardLubinTateLevelGenerator` — the root as an element of its level field.

## Main statements

* `standardLubinTatePrimitivePolynomialOverField_irreducible`, `_separable` — the
  Eisenstein and derivative arguments.
* `standardLubinTatePrimitivePolynomialOverField_eq_minpoly` — the minimal polynomial of
  the chosen root.
* `standardLubinTateLevelField_finrank` — degree `(q−1)·qⁿ`.

## Implementation notes

The ambient is the pair `(A, K)` with `[IsFractionRing A K]` — the source's
fraction-field setup with its bundled local field unbundled to Mathlib vocabulary
(`LubinTate/FiniteLevel/PrimitiveRoot.lean:258`). `q − 1 ≠ 0` in `K` holds with no
characteristic assumption: were it zero, `(q : A)` would be a unit mapped to `1`, while
`π` divides `(q : A)` because the residue field kills its own cardinality — so `π` would
divide `1`. The level fields are intermediate fields of one fixed `SeparableClosure K`,
the source's own idiom, so that different levels can later be compared inside one
ambient field.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open Polynomial

namespace Atlas.Knowledge

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Finite (IsLocalRing.ResidueField A)]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

/-- The primitive division polynomial over the fraction field
([Milne 2020, Chap. I, §3, p.36][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveRoot.lean:65`][Yamaguchi2026]). -/
noncomputable def standardLubinTatePrimitivePolynomialOverField (π : A) (n : ℕ) :
    Polynomial K :=
  (standardLubinTatePrimitivePolynomial A π n).map (algebraMap A K)

variable {A}

private theorem q_pos : 0 < Nat.card (IsLocalRing.ResidueField A) := by
  have := Finite.one_lt_card (α := IsLocalRing.ResidueField A)
  omega

omit [Finite (IsLocalRing.ResidueField A)] in
/-- The reduction of the iterate is the `qⁿ`-power Frobenius. -/
private theorem map_residue_iterate {π : A} (hπ : Irreducible π) (n : ℕ) :
    (standardLubinTatePolynomialIterate A π n).map (IsLocalRing.residue A) =
      Polynomial.X ^ Nat.card (IsLocalRing.ResidueField A) ^ n := by
  induction n with
  | zero => simp
  | succ n IH =>
    have hπ0 : IsLocalRing.residue A π = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self π
    rw [standardLubinTatePolynomialIterate_succ, Polynomial.map_comp, IH,
      standardLubinTatePolynomial]
    rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, hπ0, map_zero, zero_mul, add_zero, Polynomial.X_pow_comp,
      ← pow_mul, mul_comm, pow_succ, mul_comm (Nat.card (IsLocalRing.ResidueField A) ^ n)]

/-- `Qₙ` is Eisenstein at the maximal ideal. -/
private theorem isEisensteinAt_primitive {π : A} (hπ : Irreducible π) (n : ℕ) :
    (standardLubinTatePrimitivePolynomial A π n).IsEisensteinAt
      (Ideal.span {π}) := by
  have hq : 1 < Nat.card (IsLocalRing.ResidueField A) :=
    Finite.one_lt_card (α := IsLocalRing.ResidueField A)
  have hmonic := standardLubinTatePrimitivePolynomial_monic A π n
  constructor
  · rw [hmonic.leadingCoeff]
    intro h1
    exact hπ.not_isUnit (isUnit_of_dvd_one (Ideal.mem_span_singleton.mp h1))
  · intro i hi
    rw [← hπ.maximalIdeal_eq, ← IsLocalRing.residue_eq_zero_iff]
    have hcoeff : IsLocalRing.residue A
        ((standardLubinTatePrimitivePolynomial A π n).coeff i) =
        ((standardLubinTatePrimitivePolynomial A π n).map
          (IsLocalRing.residue A)).coeff i := by
      rw [Polynomial.coeff_map]
    rw [hcoeff, standardLubinTatePrimitivePolynomial, Polynomial.map_add,
      Polynomial.map_pow, map_residue_iterate hπ, Polynomial.map_C]
    have hπ0 : IsLocalRing.residue A π = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self π
    rw [hπ0, map_zero, add_zero, ← pow_mul, Polynomial.coeff_X_pow, if_neg]
    intro hieq
    rw [standardLubinTatePrimitivePolynomial_natDegree] at hi
    rw [hieq, Nat.mul_comm] at hi
    exact lt_irrefl _ hi
  · rw [standardLubinTatePrimitivePolynomial_coeff_zero]
    intro hmem
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have h1 : π * 1 = π * (π * c) := by
      rw [mul_one, ← mul_assoc, ← sq, ← hc]
    have h2 := mul_left_cancel₀ hπ.ne_zero h1
    exact hπ.not_isUnit (isUnit_of_dvd_one ⟨c, h2⟩)

/-- `Qₙ` is irreducible over the fraction field: Eisenstein at `π`
([Milne 2020, Chap. I, §3, p.36][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveRoot.lean:161`][Yamaguchi2026]). -/
theorem standardLubinTatePrimitivePolynomialOverField_irreducible {π : A}
    (hπ : Irreducible π) (n : ℕ) :
    Irreducible (standardLubinTatePrimitivePolynomialOverField A K π n) := by
  rw [standardLubinTatePrimitivePolynomialOverField,
    ← (standardLubinTatePrimitivePolynomial_monic A π
      n).irreducible_iff_irreducible_map_fraction_map]
  refine (isEisensteinAt_primitive hπ n).irreducible ?_ ?_ ?_
  · exact (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ.prime
  · exact (standardLubinTatePrimitivePolynomial_monic A π n).isPrimitive
  · rw [standardLubinTatePrimitivePolynomial_natDegree]
    have hq : 1 < Nat.card (IsLocalRing.ResidueField A) :=
      Finite.one_lt_card (α := IsLocalRing.ResidueField A)
    exact Nat.mul_pos (by omega) (Nat.pow_pos (by omega))

private theorem card_sub_one_cast_ne_zero {π : A} (hπ : Irreducible π) :
    ((Nat.card (IsLocalRing.ResidueField A) - 1 : ℕ) : K) ≠ 0 := by
  classical
  have hq : 1 < Nat.card (IsLocalRing.ResidueField A) :=
    Finite.one_lt_card (α := IsLocalRing.ResidueField A)
  intro h
  rw [Nat.cast_sub (by omega), Nat.cast_one, sub_eq_zero] at h
  letI : Fintype (IsLocalRing.ResidueField A) := Fintype.ofFinite _
  have hcard0 : ((Nat.card (IsLocalRing.ResidueField A) : ℕ) :
      IsLocalRing.ResidueField A) = 0 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  have hdvd : π ∣ ((Nat.card (IsLocalRing.ResidueField A) : ℕ) : A) := by
    rw [← Ideal.mem_span_singleton, ← hπ.maximalIdeal_eq,
      ← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact hcard0
  have h1 : ((Nat.card (IsLocalRing.ResidueField A) : ℕ) : A) = 1 := by
    apply IsFractionRing.injective A K
    rw [map_natCast, map_one]
    exact h
  rw [h1] at hdvd
  exact hπ.not_isUnit (isUnit_of_dvd_one hdvd)

/-- The iterate's derivative evaluates to `πⁿ` at zero. -/
private theorem derivative_iterate_eval_zero (π : A) (n : ℕ) :
    Polynomial.eval 0 (Polynomial.derivative
      (standardLubinTatePolynomialIterate A π n)) = π ^ n := by
  have hq : 1 < Nat.card (IsLocalRing.ResidueField A) :=
    Finite.one_lt_card (α := IsLocalRing.ResidueField A)
  induction n with
  | zero => simp
  | succ n IH =>
    rw [standardLubinTatePolynomialIterate_succ, Polynomial.derivative_comp,
      Polynomial.eval_mul, IH, Polynomial.eval_comp,
      standardLubinTatePolynomialIterate_eval_zero, standardLubinTatePolynomial]
    have hq1 : Nat.card (IsLocalRing.ResidueField A) - 1 ≠ 0 := by omega
    simp only [Polynomial.derivative_add, Polynomial.derivative_X_pow,
      Polynomial.derivative_C_mul, Polynomial.derivative_X, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      mul_one]
    rw [zero_pow hq1, mul_zero, zero_add, pow_succ]

/-- `Qₙ` over `K` is separable: its derivative is a product of nonzero factors
([Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveRoot.lean:180`][Yamaguchi2026]). -/
theorem standardLubinTatePrimitivePolynomialOverField_separable {π : A}
    (hπ : Irreducible π) (n : ℕ) :
    (standardLubinTatePrimitivePolynomialOverField A K π n).Separable := by
  rw [separable_iff_derivative_ne_zero
    (standardLubinTatePrimitivePolynomialOverField_irreducible K hπ n)]
  rw [standardLubinTatePrimitivePolynomialOverField,
    standardLubinTatePrimitivePolynomial, Polynomial.map_add, Polynomial.map_C,
    Polynomial.derivative_add, Polynomial.derivative_C, add_zero, Polynomial.map_pow,
    Polynomial.derivative_pow]
  have hg : (standardLubinTatePolynomialIterate A π n).map (algebraMap A K) ≠ 0 :=
    ((standardLubinTatePolynomialIterate_monic A π n).map _).ne_zero
  have hg' : Polynomial.derivative
      ((standardLubinTatePolynomialIterate A π n).map (algebraMap A K)) ≠ 0 := by
    rw [Polynomial.derivative_map]
    intro h0
    have heval := congrArg (Polynomial.eval (0 : K)) h0
    rw [Polynomial.eval_map, Polynomial.eval₂_at_zero,
      Polynomial.coeff_zero_eq_eval_zero, derivative_iterate_eval_zero,
      Polynomial.eval_zero] at heval
    have : (π ^ n : A) = 0 := by
      apply IsFractionRing.injective A K
      rw [map_zero]
      exact heval
    exact pow_ne_zero n hπ.ne_zero this
  refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ hg)) hg'
  rw [Ne, Polynomial.C_eq_zero]
  exact_mod_cast card_sub_one_cast_ne_zero K hπ

/-- The primitive polynomial has a root in the separable closure. -/
theorem exists_standardLubinTatePrimitiveRoot {π : A} (hπ : Irreducible π) (n : ℕ) :
    ∃ x : SeparableClosure K,
      ((standardLubinTatePrimitivePolynomialOverField A K π n).map
        (algebraMap K (SeparableClosure K))).IsRoot x := by
  apply IsSepClosed.exists_root
  · have hq : 1 < Nat.card (IsLocalRing.ResidueField A) :=
      Finite.one_lt_card (α := IsLocalRing.ResidueField A)
    have hmonic : ((standardLubinTatePrimitivePolynomialOverField A K π n).map
        (algebraMap K (SeparableClosure K))).Monic :=
      ((standardLubinTatePrimitivePolynomial_monic A π n).map _).map _
    have hnd : ((standardLubinTatePrimitivePolynomialOverField A K π n).map
        (algebraMap K (SeparableClosure K))).natDegree =
        (Nat.card (IsLocalRing.ResidueField A) - 1) *
          Nat.card (IsLocalRing.ResidueField A) ^ n := by
      rw [standardLubinTatePrimitivePolynomialOverField,
        ((standardLubinTatePrimitivePolynomial_monic A π n).map
          (algebraMap A K)).natDegree_map,
        (standardLubinTatePrimitivePolynomial_monic A π n).natDegree_map,
        standardLubinTatePrimitivePolynomial_natDegree]
    intro hdeg0
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hnd] at hdeg0
    have hpos : 0 < (Nat.card (IsLocalRing.ResidueField A) - 1) *
        Nat.card (IsLocalRing.ResidueField A) ^ n :=
      Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
    exact absurd hdeg0 (by exact_mod_cast hpos.ne')
  · exact (standardLubinTatePrimitivePolynomialOverField_separable K hπ n).map

/-- A **chosen primitive root** of level `n + 1` in the separable closure
([Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveRoot.lean:212`][Yamaguchi2026]). -/
noncomputable def chosenStandardLubinTatePrimitiveRoot {π : A} (hπ : Irreducible π)
    (n : ℕ) : SeparableClosure K :=
  Classical.choose (exists_standardLubinTatePrimitiveRoot K hπ n)

theorem chosenStandardLubinTatePrimitiveRoot_isRoot {π : A} (hπ : Irreducible π)
    (n : ℕ) :
    ((standardLubinTatePrimitivePolynomialOverField A K π n).map
      (algebraMap K (SeparableClosure K))).IsRoot
        (chosenStandardLubinTatePrimitiveRoot K hπ n) :=
  Classical.choose_spec (exists_standardLubinTatePrimitiveRoot K hπ n)

theorem chosenStandardLubinTatePrimitiveRoot_isIntegral {π : A} (hπ : Irreducible π)
    (n : ℕ) : IsIntegral K (chosenStandardLubinTatePrimitiveRoot K hπ n) := by
  refine ⟨standardLubinTatePrimitivePolynomialOverField A K π n,
    (standardLubinTatePrimitivePolynomial_monic A π n).map _, ?_⟩
  have := chosenStandardLubinTatePrimitiveRoot_isRoot K hπ n
  rwa [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at this

/-- The **standard Lubin–Tate level field**: the simple extension of the chosen
primitive level-`n + 1` root inside the separable closure
([Milne 2020, Chap. I, §3, p.36][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveRoot.lean:258`][Yamaguchi2026]). -/
noncomputable def standardLubinTateLevelField {π : A} (hπ : Irreducible π) (n : ℕ) :
    IntermediateField K (SeparableClosure K) :=
  IntermediateField.adjoin K {chosenStandardLubinTatePrimitiveRoot K hπ n}

/-- The chosen root as an element of its level field
([Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveUniformizer.lean:131`]
[Yamaguchi2026]). -/
noncomputable def standardLubinTateLevelGenerator {π : A} (hπ : Irreducible π)
    (n : ℕ) : standardLubinTateLevelField K hπ n :=
  ⟨chosenStandardLubinTatePrimitiveRoot K hπ n,
    IntermediateField.mem_adjoin_simple_self K _⟩

instance {π : A} (hπ : Irreducible π) (n : ℕ) :
    FiniteDimensional K (standardLubinTateLevelField K hπ n) :=
  IntermediateField.adjoin.finiteDimensional
    (chosenStandardLubinTatePrimitiveRoot_isIntegral K hπ n)

/-- The primitive polynomial is the minimal polynomial of the chosen root
([Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveRoot.lean:243`][Yamaguchi2026]). -/
theorem standardLubinTatePrimitivePolynomialOverField_eq_minpoly {π : A}
    (hπ : Irreducible π) (n : ℕ) :
    standardLubinTatePrimitivePolynomialOverField A K π n =
      minpoly K (chosenStandardLubinTatePrimitiveRoot K hπ n) := by
  refine minpoly.eq_of_irreducible_of_monic
    (standardLubinTatePrimitivePolynomialOverField_irreducible K hπ n) ?_
    ((standardLubinTatePrimitivePolynomial_monic A π n).map _)
  have := chosenStandardLubinTatePrimitiveRoot_isRoot K hπ n
  rwa [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at this

/-- The level-`n + 1` extension has degree `(q − 1) · qⁿ`
([Milne 2020, Chap. I, §3, Thm. 3.6 (a), p.38][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveRoot.lean:283`][Yamaguchi2026]). -/
theorem standardLubinTateLevelField_finrank {π : A} (hπ : Irreducible π) (n : ℕ) :
    Module.finrank K (standardLubinTateLevelField K hπ n) =
      (Nat.card (IsLocalRing.ResidueField A) - 1) *
        Nat.card (IsLocalRing.ResidueField A) ^ n := by
  rw [standardLubinTateLevelField, IntermediateField.adjoin.finrank
    (chosenStandardLubinTatePrimitiveRoot_isIntegral K hπ n),
    ← standardLubinTatePrimitivePolynomialOverField_eq_minpoly K hπ n,
    standardLubinTatePrimitivePolynomialOverField,
    (standardLubinTatePrimitivePolynomial_monic A π n).natDegree_map,
    standardLubinTatePrimitivePolynomial_natDegree]

end Atlas.Knowledge
