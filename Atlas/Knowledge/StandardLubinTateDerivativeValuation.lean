import Mathlib
import Atlas.Knowledge.StandardLubinTatePrimitiveValuation

/-!
# standard Lubin–Tate derivative valuation

The exact value of the primitive polynomial's derivative at a primitive root:
`ν(Φ′(x)) = (q − 2) qⁿ ν(x) + n ν(π)` over any carrier extension — at the level field,
where `ν(x) = 1` and `ν(π) = (q − 1) qⁿ`, the exponent `(n + 1) d − qⁿ` of the
root-product comparison ahead. The engine is the chain rule down the iterates: each step
multiplies by `q t_i^{q−1} + π`, which factors as `π` times a principal unit because `q`
lies in the maximal ideal downstairs and the iterate values stay in the maximal ideal
upstairs, so the derivative of the `i`-th iterate has value exactly `i ν(π)`; the
`q − 1` head of the primitive polynomial's own derivative is a unit, and the iterate
valuations of `Atlas.Knowledge.integerValuation_aeval_standardLubinTatePolynomialIterate`
finish the count.

## Main statements

* `standardLubinTateDerivativeValuation` — `ν(Φ′(x)) = (q − 2) qⁿ ν(x) + n ν(π)`;
  proved.

## Implementation notes

The statement is abstract-carrier, like the torsion and valuation items it extends; the
transfer to an arbitrary root of the mapped polynomial — the source proves every root
has the same derivative value, through a `K`-automorphism moving the distinguished root
— is deferred to the Krasner step that consumes it, where
`Atlas.Knowledge.valuation_algEquiv` already waits. The derivative iterate's
nonvanishing rides inside the induction's conjunction rather than as a separate lemma;
the factor's nonvanishing is a separate short step — its value equals `ν(π)`, and
zero would junk-value to `0 < ν(π)`.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

section Derivative

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]
variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [Algebra K E]
  [ValuativeExtension K E] [IsMixedCharLocalField E]
variable {π : ↥𝒪[K]} (hπ : Irreducible π) {n : ℕ} {x : ↥𝒪[E]}

omit [TopologicalSpace E] [IsMixedCharLocalField E] in
/-- The chain rule for the evaluated iterate derivative. -/
private theorem aeval_derivative_iterate_succ (i : ℕ) :
    Polynomial.aeval x (Polynomial.derivative
        (standardLubinTatePolynomialIterate ↥𝒪[K] π (i + 1))) =
      ((Nat.card 𝓀[K] : ↥𝒪[E]) *
          Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π i) ^
            (Nat.card 𝓀[K] - 1) +
        algebraMap ↥𝒪[K] ↥𝒪[E] π) *
      Polynomial.aeval x (Polynomial.derivative
        (standardLubinTatePolynomialIterate ↥𝒪[K] π i)) := by
  rw [standardLubinTatePolynomialIterate_succ, Polynomial.derivative_comp,
    Polynomial.aeval_mul, Polynomial.aeval_comp, standardLubinTatePolynomial]
  rw [Polynomial.derivative_add, Polynomial.derivative_pow, Polynomial.derivative_X,
    Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_X]
  simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    map_natCast, map_one, map_zero]
  ring

/-- The residue cardinality vanishes in the residue field. -/
private theorem natCast_card_residue_eq_zero : (Nat.card 𝓀[K] : 𝓀[K]) = 0 := by
  letI := Fintype.ofFinite 𝓀[K]
  rw [Nat.card_eq_fintype_card]
  exact Nat.cast_card_eq_zero 𝓀[K]

/-- The residue-cardinality cast lies in the maximal ideal downstairs. -/
private theorem natCast_card_mem_maximalIdeal :
    (Nat.card 𝓀[K] : ↥𝒪[K]) ∈ 𝓂[K] := by
  rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
  exact natCast_card_residue_eq_zero K

/-- The residue-cardinality predecessor is a unit downstairs. -/
private theorem isUnit_natCast_card_sub_one :
    IsUnit ((Nat.card 𝓀[K] - 1 : ℕ) : ↥𝒪[K]) := by
  rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, map_natCast,
    Nat.cast_sub (le_of_lt Finite.one_lt_card), natCast_card_residue_eq_zero K]
  simp

include hπ in
/-- Iterate values at a primitive root stay in the maximal ideal. -/
private theorem aeval_iterate_mem_maximalIdeal
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0)
    (i : ℕ) :
    Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π i) ∈ 𝓂[E] := by
  induction i with
  | zero =>
    simpa [standardLubinTatePolynomialIterate_zero] using
      mem_maximalIdeal_of_aeval_primitive K E hπ hroot
  | succ i ih =>
    rw [standardLubinTatePolynomialIterate_succ, Polynomial.aeval_comp,
      standardLubinTatePolynomial]
    rw [map_add, map_pow, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ ih)
    have hq : Nat.card 𝓀[K] ≠ 0 := by
      have : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
      omega
    exact Ideal.pow_mem_of_mem _ ih _ (Nat.pos_of_ne_zero hq)

include hπ in
/-- The derivative factor `q t_i^{q−1} + π` has the value of the uniformizer. -/
private theorem integerValuation_derivative_factor
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0)
    (i : ℕ) :
    integerValuation E ((Nat.card 𝓀[K] : ↥𝒪[E]) *
        Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π i) ^
          (Nat.card 𝓀[K] - 1) +
      algebraMap ↥𝒪[K] ↥𝒪[E] π) =
      integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π) := by
  -- the residue cardinality is a multiple of the uniformizer downstairs
  obtain ⟨c, hc⟩ : π ∣ (Nat.card 𝓀[K] : ↥𝒪[K]) := by
    rw [← Ideal.mem_span_singleton,
      ← (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ]
    exact natCast_card_mem_maximalIdeal K
  -- the unit cofactor
  have hzmem : algebraMap ↥𝒪[K] ↥𝒪[E] c *
      Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π i) ^
        (Nat.card 𝓀[K] - 1) ∈ 𝓂[E] := by
    have hq : Nat.card 𝓀[K] - 1 ≠ 0 := by
      have : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
      omega
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _
      (aeval_iterate_mem_maximalIdeal K E hπ hroot i) _ (Nat.pos_of_ne_zero hq))
  have hunit : IsUnit (1 + algebraMap ↥𝒪[K] ↥𝒪[E] c *
      Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π i) ^
        (Nat.card 𝓀[K] - 1)) := by
    have h := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
      ((IsLocalRing.mem_maximalIdeal _).mp (neg_mem hzmem))
    rwa [sub_neg_eq_add] at h
  -- factor and take values
  have hfactor : (Nat.card 𝓀[K] : ↥𝒪[E]) *
      Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π i) ^
        (Nat.card 𝓀[K] - 1) +
      algebraMap ↥𝒪[K] ↥𝒪[E] π =
      algebraMap ↥𝒪[K] ↥𝒪[E] π * (1 + algebraMap ↥𝒪[K] ↥𝒪[E] c *
        Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π i) ^
          (Nat.card 𝓀[K] - 1)) := by
    have hq : (Nat.card 𝓀[K] : ↥𝒪[E]) = algebraMap ↥𝒪[K] ↥𝒪[E] π *
        algebraMap ↥𝒪[K] ↥𝒪[E] c := by
      rw [← map_mul, ← hc, map_natCast]
    rw [hq]
    ring
  rw [hfactor, integerValuation_mul E (algebraMap_pi_ne_zero K E hπ) hunit.ne_zero,
    integerValuation_eq_zero_of_isUnit E hunit, add_zero]

include hπ in
/-- The evaluated iterate derivative is nonvanishing with value `i ν(π)`. -/
private theorem integerValuation_aeval_derivative_iterate
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0)
    (i : ℕ) :
    Polynomial.aeval x (Polynomial.derivative
        (standardLubinTatePolynomialIterate ↥𝒪[K] π i)) ≠ 0 ∧
      integerValuation E (Polynomial.aeval x (Polynomial.derivative
          (standardLubinTatePolynomialIterate ↥𝒪[K] π i))) =
        i * integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π) := by
  have hπE : algebraMap ↥𝒪[K] ↥𝒪[E] π ≠ 0 := algebraMap_pi_ne_zero K E hπ
  have hπpos : 0 < integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π) :=
    (integerValuation_pos_iff E hπE).mpr
      (algebraMap_irreducible_mem_maximalIdeal K E hπ)
  induction i with
  | zero =>
    constructor
    · simp [standardLubinTatePolynomialIterate_zero]
    · simp [standardLubinTatePolynomialIterate_zero]
  | succ i ih =>
    obtain ⟨ihne, ihval⟩ := ih
    have hfacval := integerValuation_derivative_factor K E hπ hroot i
    have hfacne : (Nat.card 𝓀[K] : ↥𝒪[E]) *
        Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π i) ^
          (Nat.card 𝓀[K] - 1) +
        algebraMap ↥𝒪[K] ↥𝒪[E] π ≠ 0 := by
      intro h0
      rw [h0, integerValuation_zero] at hfacval
      omega
    constructor
    · rw [aeval_derivative_iterate_succ K E]
      exact mul_ne_zero hfacne ihne
    · rw [aeval_derivative_iterate_succ K E,
        integerValuation_mul E hfacne ihne, hfacval, ihval]
      push_cast
      ring

include hπ in
/-- **The derivative valuation at a primitive root**: the primitive polynomial's
derivative takes value `(q − 2) qⁿ ν(x) + n ν(π)` — at the level field, where
`ν(x) = 1` and `ν(π) = (q − 1) qⁿ`, this is the source's derivative exponent
`(n + 1) d − qⁿ` for `d = (q − 1) qⁿ`
([Yamaguchi 2026, `LubinTate/FiniteLevel/HigherUnitLevelEquiv.lean:294`]
[Yamaguchi2026] — the source computes at the level; the abstract-carrier form is this
layer's statement policy). -/
theorem standardLubinTateDerivativeValuation
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0) :
    integerValuation E (Polynomial.aeval x (Polynomial.derivative
        (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n))) =
      ((Nat.card 𝓀[K] : ℤ) - 2) * (Nat.card 𝓀[K] : ℤ) ^ n * integerValuation E x +
        n * integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π) := by
  have hq2 : 2 ≤ Nat.card 𝓀[K] := Finite.one_lt_card
  have htn : Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π n) ≠ 0 :=
    aeval_standardLubinTatePolynomialIterate_ne_zero K E hπ hroot
  obtain ⟨hDne, hDval⟩ := integerValuation_aeval_derivative_iterate K E hπ hroot n
  -- unfold the derivative of `Φ = (f^[n])^{q−1} + C π`
  rw [standardLubinTatePrimitivePolynomial, Polynomial.derivative_add,
    Polynomial.derivative_C, add_zero, Polynomial.derivative_pow]
  rw [map_mul, map_mul, Polynomial.aeval_C, map_natCast, map_pow]
  -- the `q − 1` head is a unit
  have hcast : ((Nat.card 𝓀[K] - 1 : ℕ) : ↥𝒪[E]) =
      algebraMap ↥𝒪[K] ↥𝒪[E] ((Nat.card 𝓀[K] - 1 : ℕ) : ↥𝒪[K]) := by
    rw [map_natCast]
  have hheadunit : IsUnit ((Nat.card 𝓀[K] - 1 : ℕ) : ↥𝒪[E]) := by
    rw [hcast]
    exact (isUnit_natCast_card_sub_one K).map _
  have hpowne : Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π n) ^
      (Nat.card 𝓀[K] - 1 - 1) ≠ 0 := pow_ne_zero _ htn
  rw [integerValuation_mul E (mul_ne_zero hheadunit.ne_zero hpowne) hDne,
    integerValuation_mul E hheadunit.ne_zero hpowne,
    integerValuation_eq_zero_of_isUnit E hheadunit,
    integerValuation_pow E _ (Nat.card 𝓀[K] - 1 - 1),
    integerValuation_aeval_standardLubinTatePolynomialIterate K E hπ hroot le_rfl,
    hDval]
  have hexp : ((Nat.card 𝓀[K] - 1 - 1 : ℕ) : ℤ) = (Nat.card 𝓀[K] : ℤ) - 2 := by
    omega
  rw [hexp]
  ring

end Derivative

end Atlas.Knowledge
