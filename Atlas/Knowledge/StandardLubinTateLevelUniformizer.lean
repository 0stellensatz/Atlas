import Mathlib
import Atlas.Knowledge.RamificationBound
import Atlas.Knowledge.StandardLubinTateGaloisDescription
import Atlas.Knowledge.StandardLubinTatePrimitiveValuation

/-!
# standard Lubin–Tate level uniformizer

The level generator is a uniformizer: at level `n + 1` its integer valuation is one,
so it is irreducible in the level integers, and the base uniformizer's value is exactly
the degree `(q − 1) qⁿ` — the level tower is totally ramified. The proof is the squeeze
this arc was built for: `Atlas.Knowledge.standardLubinTatePrimitiveValuation` gives
`(q − 1) qⁿ ν(λ) = ν(π)`, `Atlas.Knowledge.ramificationBound` caps `ν(π)` by the degree,
and `Atlas.Knowledge.standardLubinTateLevelField_finrank` says the degree is `(q − 1) qⁿ`
— so `ν(λ) = 1` with everything else forced. The Eisenstein facts themselves — the
irreducibility of the primitive polynomial and the level degree — were already recorded
in `Atlas.Knowledge.StandardLubinTateLevelField`; this item adds the valuation readings
the derivative computation ahead consumes.

## Main statements

* `integerValuation_levelGeneratorInteger` — `ν(λ) = 1`; proved.
* `levelGeneratorInteger_irreducible` — the level generator is irreducible in `𝒪[Lₙ]`;
  proved.
* `integerValuation_algebraMap_levelField` — `ν(π) = (q − 1) qⁿ` at the level: total
  ramification; proved.

## Implementation notes

The local-field structure on the level field is hypothesized, as in
`Atlas.Knowledge.StandardLubinTateGaloisDescription`, and the statements are consumed
after obtaining it from `Atlas.Knowledge.exists_extension_isMixedCharLocalField`. Two
instance seams are handled by hand: `FiniteDimensional` comes from the adjoin power
basis by `letI`, and the nonvanishing of images routes through the injectivity of the
field-level `algebraMap` — `FaithfulSMul` between the integer rings does not synthesize
at the level field.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]
variable {π : ↥𝒪[K]} (hπ : Irreducible π) (n : ℕ)
variable [ValuativeRel ↥(standardLubinTateLevelField K hπ n)]
  [TopologicalSpace ↥(standardLubinTateLevelField K hπ n)]
  [ValuativeExtension K ↥(standardLubinTateLevelField K hπ n)]
  [IsMixedCharLocalField ↥(standardLubinTateLevelField K hπ n)]

omit [TopologicalSpace ↥(standardLubinTateLevelField K hπ n)]
  [IsMixedCharLocalField ↥(standardLubinTateLevelField K hπ n)] in
/-- Evaluation of the iterate at zero vanishes. -/
private theorem aeval_zero_iterate (m : ℕ) :
    Polynomial.aeval (0 : ↥𝒪[↥(standardLubinTateLevelField K hπ n)])
      (standardLubinTatePolynomialIterate ↥𝒪[K] π m) = 0 := by
  induction m with
  | zero => simp [standardLubinTatePolynomialIterate_zero]
  | succ m ih =>
    rw [standardLubinTatePolynomialIterate_succ, Polynomial.aeval_comp,
      standardLubinTatePolynomial]
    rw [map_add, map_pow, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, ih]
    have hq : Nat.card 𝓀[K] ≠ 0 := by
      have : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
      omega
    simp [hq]

omit [TopologicalSpace ↥(standardLubinTateLevelField K hπ n)]
  [IsMixedCharLocalField ↥(standardLubinTateLevelField K hπ n)] in
/-- The level generator is a nonzero integer. -/
private theorem levelGeneratorInteger_ne_zero :
    levelGeneratorInteger K hπ n ≠ 0 := by
  intro h0
  have hroot := aeval_levelGeneratorInteger K hπ n
  rw [h0, standardLubinTatePrimitivePolynomial, map_add, map_pow, Polynomial.aeval_C,
    aeval_zero_iterate K hπ n] at hroot
  have hq : Nat.card 𝓀[K] - 1 ≠ 0 := by
    have : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
    omega
  rw [zero_pow hq, zero_add] at hroot
  refine hπ.ne_zero ?_
  have h1 : algebraMap K ↥(standardLubinTateLevelField K hπ n) (π : K) = 0 := by
    have hcoe : ((algebraMap ↥𝒪[K] ↥𝒪[↥(standardLubinTateLevelField K hπ n)] π :
        ↥𝒪[↥(standardLubinTateLevelField K hπ n)]) :
          ↥(standardLubinTateLevelField K hπ n)) =
        algebraMap K ↥(standardLubinTateLevelField K hπ n) (π : K) := rfl
    rw [← hcoe, hroot, ZeroMemClass.coe_zero]
  have h2 : (π : K) = 0 := by
    refine (algebraMap K ↥(standardLubinTateLevelField K hπ n)).injective ?_
    rw [h1, map_zero]
  exact Subtype.ext h2

/-- **The level generator is a uniformizer**: its integer valuation is one — the
squeeze of `Atlas.Knowledge.standardLubinTatePrimitiveValuation` against
`Atlas.Knowledge.ramificationBound` at the level degree
([Milne 2020, Chap. I, §3, Summary 3.7, p.39][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveUniformizer.lean:749`][Yamaguchi2026]). -/
theorem integerValuation_levelGeneratorInteger :
    integerValuation ↥(standardLubinTateLevelField K hπ n)
      (levelGeneratorInteger K hπ n) = 1 := by
  have hroot := aeval_levelGeneratorInteger K hπ n
  have hid := standardLubinTatePrimitiveValuation K
    ↥(standardLubinTateLevelField K hπ n) hπ hroot
  letI : FiniteDimensional K ↥(standardLubinTateLevelField K hπ n) := by
    rw [standardLubinTateLevelField]
    exact IntermediateField.adjoin.finiteDimensional
      (chosenStandardLubinTatePrimitiveRoot_isIntegral K hπ n)
  have hbound := ramificationBound K ↥(standardLubinTateLevelField K hπ n) hπ
  have hrank := standardLubinTateLevelField_finrank (A := ↥𝒪[K]) (K := K) hπ n
  rw [hrank] at hbound
  have hpos : (0 : ℤ) < ((Nat.card 𝓀[K] : ℤ) - 1) * (Nat.card 𝓀[K] : ℤ) ^ n := by
    have hq : (2 : ℤ) ≤ (Nat.card 𝓀[K] : ℤ) := by
      exact_mod_cast (Finite.one_lt_card : 1 < Nat.card 𝓀[K])
    exact mul_pos (by omega) (pow_pos (by omega) n)
  have hge : 1 ≤ integerValuation ↥(standardLubinTateLevelField K hπ n)
      (levelGeneratorInteger K hπ n) := by
    have hmem := mem_maximalIdeal_of_aeval_primitive K
      ↥(standardLubinTateLevelField K hπ n) hπ hroot
    have := (integerValuation_pos_iff ↥(standardLubinTateLevelField K hπ n)
      (levelGeneratorInteger_ne_zero K hπ n)).mpr hmem
    omega
  -- the squeeze: `D · ν(λ) = ν(π) ≤ D` with `ν(λ) ≥ 1` and `D > 0`
  have hq1 : 1 ≤ Nat.card 𝓀[K] := le_of_lt Finite.one_lt_card
  have hbound' : integerValuation ↥(standardLubinTateLevelField K hπ n)
      (algebraMap ↥𝒪[K] ↥𝒪[↥(standardLubinTateLevelField K hπ n)] π) ≤
      ((Nat.card 𝓀[K] : ℤ) - 1) * (Nat.card 𝓀[K] : ℤ) ^ n := by
    refine le_trans hbound (le_of_eq ?_)
    push_cast [Nat.cast_sub hq1]
    ring
  have h1 : (((Nat.card 𝓀[K] : ℤ) - 1) * (Nat.card 𝓀[K] : ℤ) ^ n) *
      integerValuation ↥(standardLubinTateLevelField K hπ n)
        (levelGeneratorInteger K hπ n) ≤
      (((Nat.card 𝓀[K] : ℤ) - 1) * (Nat.card 𝓀[K] : ℤ) ^ n) * 1 := by
    rw [mul_one]
    calc (((Nat.card 𝓀[K] : ℤ) - 1) * (Nat.card 𝓀[K] : ℤ) ^ n) *
        integerValuation ↥(standardLubinTateLevelField K hπ n)
          (levelGeneratorInteger K hπ n) =
        integerValuation ↥(standardLubinTateLevelField K hπ n)
          (algebraMap ↥𝒪[K] ↥𝒪[↥(standardLubinTateLevelField K hπ n)] π) := hid
      _ ≤ _ := hbound'
  have hle := le_of_mul_le_mul_left h1 hpos
  omega

/-- **The level generator is irreducible in the level integers** — the uniformizer
statement in ring form ([Milne 2020, Chap. I, §3, Summary 3.7, p.39][MilneCFT] —
`𝔪 = (π_n)` in the tower diagram;
[Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveUniformizer.lean:824`][Yamaguchi2026]). -/
theorem levelGeneratorInteger_irreducible :
    Irreducible (levelGeneratorInteger K hπ n) :=
  irreducible_of_integerValuation_eq_one _
    (integerValuation_levelGeneratorInteger K hπ n)

/-- **The level tower is totally ramified**: the base uniformizer's value at level
`n + 1` is exactly the degree `(q − 1) qⁿ`
([Milne 2020, Chap. I, §3, Thm. 3.6 (a), pp.38–39][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveUniformizer.lean:760`][Yamaguchi2026]). -/
theorem integerValuation_algebraMap_levelField :
    integerValuation ↥(standardLubinTateLevelField K hπ n)
      (algebraMap ↥𝒪[K] ↥𝒪[↥(standardLubinTateLevelField K hπ n)] π) =
      ((Nat.card 𝓀[K] : ℤ) - 1) * (Nat.card 𝓀[K] : ℤ) ^ n := by
  have hid := standardLubinTatePrimitiveValuation K
    ↥(standardLubinTateLevelField K hπ n) hπ (aeval_levelGeneratorInteger K hπ n)
  rw [integerValuation_levelGeneratorInteger K hπ n, mul_one] at hid
  exact hid.symm

end Atlas.Knowledge
