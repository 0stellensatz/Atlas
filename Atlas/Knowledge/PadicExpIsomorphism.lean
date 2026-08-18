import Mathlib
import Atlas.Knowledge.AbsoluteRamificationIndex
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.PadicLogarithm
import Atlas.Knowledge.ResidueCharacteristic

/-!
# exp/log isomorphism above the threshold

Above the threshold `e / (p - 1)`, the exponential and the logarithm are mutually inverse
isomorphisms between the higher unit groups and their additive counterparts: for `i` with
`(p - 1) * i > e`, the exponential maps `𝓂 ^ i` bijectively onto `U i (K)` of
`Atlas.Knowledge.HigherUnitGroup`, addition goes to multiplication, and
`Atlas.Knowledge.PadicLogarithm` inverts it in both orders. This is the level-by-level
sharpening of the classical statement that `exp` and `log` are inverse isomorphisms between
the convergence disc and its multiplicative translate, and it is what makes the deep unit
groups additive objects—the mechanism behind `Atlas.Knowledge.DeepUnitGroup` and the free-rank
computations it gates.

## Main statements

All are claims recorded ahead of their proofs.

* `padicExpIsomorphism` — the exponential is a bijection of `𝓂 ^ i` onto `U i (K)` above the
  threshold.
* `PadicExpIsomorphism.exp_add` — on `𝓂 ^ i` above the threshold, the exponential turns
  addition into multiplication.
* `PadicExpIsomorphism.padicLogarithm_exp` — the logarithm inverts the exponential on `𝓂 ^ i`.
* `PadicExpIsomorphism.exp_padicLogarithm` — the exponential inverts the logarithm on
  `U i (K)`.

## Implementation notes

The exponential is Mathlib's `NormedSpace.exp`, whose value at `x` is the sum of the series
`∑ xⁿ / n!` through the `ℚ`-algebra structure of `K`—unique in characteristic `0`, so the
`Classical.choice` in Mathlib's definition picks the standard one—and whose convergence on the
stated domain is `Atlas.Knowledge.PadicExpConvergence`. The isomorphism is stated unbundled: a
`Set.BijOn` between the images of `𝓂 ^ i` and of `U i (K)` in `K`, plus the homomorphism
identity and the two inversion identities. A bundled `MulEquiv` would be a definition, and a
definition may not carry a `sorry`; the unbundled quadruple records the same content as claims
and lets the bundling be built downstream once the proofs land. The threshold hypothesis is the
integer inequality `e < (p - 1) * i`, the same spelling as the membership bound of
`Atlas.Knowledge.PadicExpConvergence`; on that range the value of the exponential lands on a
unit because its series has first term `1` and the tail falls in the maximal ideal, which is
what membership of the value in the image of `U i (K)` encodes. No claim is made at or below
the threshold, where the series diverges and the value of `NormedSpace.exp` is junk.

## References

* [FesenkoVostokov2002] I. B. Fesenko, S. V. Vostokov, *Local fields and their extensions*,
  Translations of Mathematical Monographs **121**, American Mathematical Society, second
  edition, 2002.
* [Koblitz1984] N. Koblitz, *p-adic numbers, p-adic analysis, and zeta-functions*, Graduate
  Texts in Mathematics **58**, Springer New York, 1984.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

open ValuativeRel

namespace Atlas.Knowledge

set_option synthInstance.maxHeartbeats 40000 in
-- The instance search on the ideal power `𝓂[K] ^ _` does not fit the default budget, as in
-- `Atlas.Knowledge.HigherUnitGroup`.
/-- Above the threshold `e / (p - 1)`, the exponential is a bijection of the ideal power onto
the higher unit group: for `(p - 1) * i > e`, `NormedSpace.exp` maps the image of `𝓂 ^ i` in
`K` bijectively onto the image of `U i (K)`. With `PadicExpIsomorphism.exp_add` and the two
inversion identities, this is the statement that `exp` and `log` are mutually inverse
isomorphisms between `𝓂 ^ i` and `U i (K)`. Claim recorded ahead of its proof
([Fesenko–Vostokov 2002, Chap. VI, (1.4), p.212][FesenkoVostokov2002];
[Koblitz 1984, Chap. IV, §1, Prop., p.81][Koblitz1984]; [Hyeon 2025, §4, p.17][Hyeon2025]). -/
theorem padicExpIsomorphism (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (i : ℕ+)
    (hi : absoluteRamificationIndex K < (residueCharacteristic K - 1) * (i : ℕ)) :
    Set.BijOn NormedSpace.exp
      (((↑) : ↥𝒪[K] → K) '' ((𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) : Set ↥𝒪[K]))
      (((↑) : Kˣ → K) '' (higherUnitGroup K i : Set Kˣ)) := by
  sorry

namespace PadicExpIsomorphism

set_option synthInstance.maxHeartbeats 40000 in
-- The instance search on the ideal power `𝓂[K] ^ _` does not fit the default budget, as in
-- `Atlas.Knowledge.HigherUnitGroup`.
/-- Above the threshold, the exponential turns addition into multiplication: for `x`, `y` in
`𝓂 ^ i` with `(p - 1) * i > e`, `exp (x + y) = exp x * exp y`. Claim recorded ahead of its
proof ([Koblitz 1984, Chap. IV, §1, p.80][Koblitz1984];
[Fesenko–Vostokov 2002, Chap. VI, (1.2) and (1.5), pp.208, 212][FesenkoVostokov2002]). -/
theorem exp_add (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (i : ℕ+)
    (hi : absoluteRamificationIndex K < (residueCharacteristic K - 1) * (i : ℕ))
    (x y : ↥𝒪[K]) (hx : x ∈ (𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]))
    (hy : y ∈ (𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K])) :
    NormedSpace.exp ((x : K) + (y : K)) = NormedSpace.exp (x : K) * NormedSpace.exp (y : K) := by
  sorry

set_option synthInstance.maxHeartbeats 40000 in
-- The instance search on the ideal power `𝓂[K] ^ _` does not fit the default budget, as in
-- `Atlas.Knowledge.HigherUnitGroup`.
/-- The logarithm inverts the exponential on the ideal power above the threshold:
`log (exp x) = x` for `x ∈ 𝓂 ^ i` with `(p - 1) * i > e`. Claim recorded ahead of its proof
([Koblitz 1984, Chap. IV, §1, p.81][Koblitz1984];
[Fesenko–Vostokov 2002, Chap. VI, (1.4), p.212][FesenkoVostokov2002]). -/
theorem padicLogarithm_exp (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (i : ℕ+)
    (hi : absoluteRamificationIndex K < (residueCharacteristic K - 1) * (i : ℕ))
    (x : ↥𝒪[K]) (hx : x ∈ (𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K])) :
    padicLogarithm K (NormedSpace.exp (x : K)) = x := by
  sorry

/-- The exponential inverts the logarithm on the higher unit group above the threshold:
`exp (log u) = u` for `u ∈ U i (K)` with `(p - 1) * i > e`. Claim recorded ahead of its proof
([Koblitz 1984, Chap. IV, §1, p.81][Koblitz1984];
[Fesenko–Vostokov 2002, Chap. VI, (1.4), p.212][FesenkoVostokov2002];
[Hyeon 2025, §4, p.17][Hyeon2025]). -/
theorem exp_padicLogarithm (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (i : ℕ+)
    (hi : absoluteRamificationIndex K < (residueCharacteristic K - 1) * (i : ℕ))
    (u : Kˣ) (hu : u ∈ higherUnitGroup K i) :
    NormedSpace.exp (padicLogarithm K (u : K)) = (u : K) := by
  sorry

end PadicExpIsomorphism

end Atlas.Knowledge
