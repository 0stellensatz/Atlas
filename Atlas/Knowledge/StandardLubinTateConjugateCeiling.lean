import Mathlib
import Atlas.Knowledge.StandardLubinTateDisplacement
import Atlas.Knowledge.StandardLubinTateSplitting

/-!
# standard Lubin–Tate conjugate ceiling

Any root of the primitive polynomial other than a given primitive root sits at value at
most `qⁿ ν(x)` from it — the ceiling that the strict Krasner gap of
`Atlas.Knowledge.standardLubinTateRootProximity_lt` beats. Every root is an orbit point
by `Atlas.Knowledge.exists_unit_lubinTateSMul_of_mem_roots`, the orbit scalar's depth
is at most `n` because a deeper scalar acts trivially through the annihilator, and the
displacement spectrum of
`Atlas.Knowledge.integerValuation_standardLubinTateSMul_sub_self` reads off the
distance.

## Main statements

* `standardLubinTateConjugateCeiling` — `ν(x − r) ≤ qⁿ ν(x)` for any other root `r`;
  proved.

## Implementation notes

The other root enters as an `aeval` primitive root, the vocabulary of the arc, and is
converted to roots-membership internally; no Galois group appears — the source states
the ceiling for level-field automorphisms, and the Krasner consumer converts an
automorphism image into a root before reaching for this bound. The depth extraction is
the DVR normal form `v − 1 = πʲ w` of the displacement item, with `j ≤ n` forced by
`Atlas.Knowledge.standardLubinTateSMul_eq_iff`.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

section Ceiling

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]
variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [Algebra K E]
  [ValuativeExtension K E] [IsMixedCharLocalField E]
variable {π : ↥𝒪[K]} (hπ : Irreducible π) {n : ℕ} {x : ↥𝒪[E]}

include hπ in
/-- **The conjugate ceiling**: any root of the primitive polynomial other than a given
primitive root sits at value at most `qⁿ ν(x)` from it — the bound the Krasner gap
strictly beats (Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveDisplacement.lean:905`
— the source's Galois form; the orbit form here needs no automorphism). -/
theorem standardLubinTateConjugateCeiling
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0)
    {r : ↥𝒪[E]}
    (hr : Polynomial.aeval r (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0)
    (hne : r ≠ x) :
    integerValuation E (x - r) ≤ (Nat.card 𝓀[K] : ℤ) ^ n * integerValuation E x := by
  have hx : x ∈ 𝓂[E] := mem_maximalIdeal_of_aeval_primitive K E hπ hroot
  have hmonic : ((standardLubinTatePrimitivePolynomial ↥𝒪[K] π n).map
      (algebraMap ↥𝒪[K] ↥𝒪[E])).Monic :=
    (standardLubinTatePrimitivePolynomial_monic ↥𝒪[K] π n).map _
  have hrmem : r ∈ ((standardLubinTatePrimitivePolynomial ↥𝒪[K] π n).map
      (algebraMap ↥𝒪[K] ↥𝒪[E])).roots := by
    rw [Polynomial.mem_roots hmonic.ne_zero, Polynomial.IsRoot, Polynomial.eval_map,
      ← Polynomial.aeval_def]
    exact hr
  obtain ⟨v, rfl⟩ := exists_unit_lubinTateSMul_of_mem_roots K E hπ hroot hrmem
  -- the scalar's distance from one has a depth `j ≤ n`, since `r ≠ x`
  have hvne : (v : ↥𝒪[K]) - 1 ≠ 0 := by
    intro h0
    refine hne ?_
    have hv1 : (v : ↥𝒪[K]) = 1 := by linear_combination h0
    rw [hv1, lubinTateSMul_one]
  obtain ⟨j, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hvne hπ
  have hju : (v : ↥𝒪[K]) - 1 = π ^ j * (w : ↥𝒪[K]) := by
    rw [hw]
    ring
  have hjn : j ≤ n := by
    by_contra hgt
    refine hne ?_
    have hmem : (v : ↥𝒪[K]) - 1 ∈ (𝓂[K] ^ (n + 1) : Ideal ↥𝒪[K]) := by
      rw [hju, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
        Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact Dvd.dvd.mul_right (pow_dvd_pow π (by omega)) _
    have heq := (standardLubinTateSMul_eq_iff K E hπ hx hroot (↑v) 1).mpr
      (by simpa using hmem)
    rw [heq, lubinTateSMul_one]
  -- the displacement spectrum
  have hspec := integerValuation_standardLubinTateSMul_sub_self K E hπ hx hroot
    hjn w.isUnit hju
  have hneg : integerValuation E
      (x - lubinTateSMul K E hπ (standardLubinTateSeries hπ) (↑v) x) =
      integerValuation E
        (lubinTateSMul K E hπ (standardLubinTateSeries hπ) (↑v) x - x) := by
    rw [show x - lubinTateSMul K E hπ (standardLubinTateSeries hπ) (↑v) x =
      -(lubinTateSMul K E hπ (standardLubinTateSeries hπ) (↑v) x - x) by ring,
      integerValuation_neg]
  rw [hneg, hspec]
  have hq : (2 : ℤ) ≤ (Nat.card 𝓀[K] : ℤ) := by
    exact_mod_cast (Finite.one_lt_card : 1 < Nat.card 𝓀[K])
  have hxnn := integerValuation_nonneg E x
  have hpow : (Nat.card 𝓀[K] : ℤ) ^ j ≤ (Nat.card 𝓀[K] : ℤ) ^ n :=
    pow_le_pow_right₀ (by omega) hjn
  exact mul_le_mul_of_nonneg_right hpow hxnn

end Ceiling

end Atlas.Knowledge
