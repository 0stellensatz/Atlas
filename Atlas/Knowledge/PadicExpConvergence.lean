import Mathlib
import Atlas.Knowledge.AbsoluteRamificationIndex
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.ResidueCharacteristic

/-!
# convergence threshold of the p-adic exponential

The exponential series `∑ xⁿ / n!` on a mixed-characteristic local field converges exactly above
the threshold `e / (p - 1)`: for an integer `x`, the series is summable if and only if the
valuation of `x` exceeds `e / (p - 1)`, that is, if and only if `x` lies in
`𝓂 ^ (⌊e / (p - 1)⌋ + 1)`. The threshold is the point of contact between the exponential and the
jump-set arithmetic of the layer: `e / (p - 1)` is the `e'` of the shift
`Atlas.Knowledge.ShiftRhoEP` in the sense of `Atlas.Knowledge.ShiftEPrime`, the index at which
`p`-powering of the higher unit filtration `Atlas.Knowledge.HigherUnitGroup` switches from the
regime `i ↦ p * i` to the stable regime `i ↦ i + e`—and above it the exponential inverts the
filtration into its additive counterpart, which is `Atlas.Knowledge.PadicExpIsomorphism`.

## Main statements

* `padicExpConvergence` — summability of the exponential series at an integer `x` is equivalent
  to membership of `x` in the ideal power one past the threshold. Claim recorded ahead of its
  proof.

## Implementation notes

The series is spelled `(n ! : ℚ)⁻¹ • x ^ n`, which is term-by-term the application of Mathlib's
`NormedSpace.expSeries ℚ K` (by `NormedSpace.expSeries_apply_eq`), so the claim is about the
series whose sum is `NormedSpace.exp`—the layer introduces no second exponential. The threshold
index is the floor division `e / (p - 1) + 1` of the invariants
`Atlas.Knowledge.AbsoluteRamificationIndex` and `Atlas.Knowledge.ResidueCharacteristic`: an
integer valuation exceeds the rational `e / (p - 1)` exactly when it reaches `⌊e / (p - 1)⌋ + 1`,
so the ideal membership carries the sharp bound without rational arithmetic. The statement
quantifies over integers of `K` only: off the integers the valuation is negative and divergence
is subsumed by the classical statement, while the filtration the layer cares about lives inside
`𝒪[K]`. The `synthInstance.maxHeartbeats` bump is scoped to the declaration and covers the
instance search on the ideal power, as in `Atlas.Knowledge.HigherUnitGroup`.

## References

* [FesenkoVostokov2002] I. B. Fesenko, S. V. Vostokov, *Local fields and their extensions*,
  Translations of Mathematical Monographs **121**, American Mathematical Society, second
  edition, 2002.
* [Koblitz1984] N. Koblitz, *p-adic numbers, p-adic analysis, and zeta-functions*, Graduate
  Texts in Mathematics **58**, Springer New York, 1984.
* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

open ValuativeRel
open scoped Nat

namespace Atlas.Knowledge

set_option synthInstance.maxHeartbeats 40000 in
-- The instance search on the ideal power `𝓂[K] ^ _` does not fit the default budget, as in
-- `Atlas.Knowledge.HigherUnitGroup`.
/-- The exponential series `∑ xⁿ / n!` at an integer `x` of a mixed-characteristic local field
is summable exactly above the threshold `e / (p - 1)`: summability is equivalent to membership
of `x` in `𝓂 ^ (e / (p - 1) + 1)`, the floor division marking the least integer valuation
exceeding the threshold. The threshold is the `e'` of the shift `ρ_ep`
of `Atlas.Knowledge.ShiftRhoEP`. Claim recorded ahead of its proof
([Fesenko–Vostokov 2002, Chap. VI, (1.4), pp.211–212][FesenkoVostokov2002];
[Koblitz 1984, Chap. IV, §1, p.79][Koblitz1984]; [Pagano 2022, §5, p.442][Pagano2022]). -/
theorem padicExpConvergence (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (x : ↥𝒪[K]) :
    Summable (fun n : ℕ => (n ! : ℚ)⁻¹ • ((x : K) ^ n)) ↔
      x ∈ (𝓂[K] ^ (absoluteRamificationIndex K / (residueCharacteristic K - 1) + 1) :
        Ideal ↥𝒪[K]) := by
  sorry

end Atlas.Knowledge
