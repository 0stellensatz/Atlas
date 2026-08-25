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
after obtaining it from `Atlas.Knowledge.exists_extension_isMixedCharLocalField`. The
proof consumes the two halves the arc prepared: the lower bound is
`Atlas.Knowledge.le_integerValuation_algebraMap_pi`, the upper is
`Atlas.Knowledge.ramificationBound` at the level degree, and cancellation leaves
`ν(λ) = 1`. A consumer needing the generator's nonvanishing reads it off
`levelGeneratorInteger_irreducible` as `.ne_zero`.

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
  have hlow := le_integerValuation_algebraMap_pi K
    ↥(standardLubinTateLevelField K hπ n) hπ hroot
  have hbound := ramificationBound K ↥(standardLubinTateLevelField K hπ n) hπ
  rw [standardLubinTateLevelField_finrank (A := ↥𝒪[K]) (K := K) hπ n] at hbound
  have hq1 : 1 ≤ Nat.card 𝓀[K] := le_of_lt Finite.one_lt_card
  rw [Nat.cast_mul, Nat.cast_sub hq1, Nat.cast_pow, Nat.cast_one] at hbound
  have hpos : (0 : ℤ) < ((Nat.card 𝓀[K] : ℤ) - 1) * (Nat.card 𝓀[K] : ℤ) ^ n := by
    have hq : (2 : ℤ) ≤ (Nat.card 𝓀[K] : ℤ) := by
      exact_mod_cast (Finite.one_lt_card : 1 < Nat.card 𝓀[K])
    exact mul_pos (by omega) (pow_pos (by omega) n)
  refine le_antisymm (le_of_mul_le_mul_left ?_ hpos) (le_of_mul_le_mul_left ?_ hpos)
  · rw [mul_one, hid]
    omega
  · rw [mul_one, hid]
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
[Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveUniformizer.lean:760` and `:811`]
[Yamaguchi2026]). -/
theorem integerValuation_algebraMap_levelField :
    integerValuation ↥(standardLubinTateLevelField K hπ n)
      (algebraMap ↥𝒪[K] ↥𝒪[↥(standardLubinTateLevelField K hπ n)] π) =
      ((Nat.card 𝓀[K] : ℤ) - 1) * (Nat.card 𝓀[K] : ℤ) ^ n := by
  have hid := standardLubinTatePrimitiveValuation K
    ↥(standardLubinTateLevelField K hπ n) hπ (aeval_levelGeneratorInteger K hπ n)
  rw [integerValuation_levelGeneratorInteger K hπ n, mul_one] at hid
  exact hid.symm

end Atlas.Knowledge
