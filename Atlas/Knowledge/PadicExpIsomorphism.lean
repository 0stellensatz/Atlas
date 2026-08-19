import Mathlib
import Atlas.Knowledge.AbsoluteRamificationIndex
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.PadicExpConvergence
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
* `PadicExpIsomorphism.exp_add` — on the convergence ideal, the exponential turns addition
  into multiplication.
* `PadicExpIsomorphism.padicLogarithm_exp` — the logarithm inverts the exponential on the
  convergence ideal.
* `PadicExpIsomorphism.exp_padicLogarithm` — the exponential inverts the logarithm on
  `U i (K)`.

Of the four, `PadicExpIsomorphism.exp_add` is proved; the other three are claims recorded ahead
of their proofs.

## Implementation notes

The exponential is Mathlib's `NormedSpace.exp`, whose value at `x` is the sum of the series
`∑ xⁿ / n!` through the `ℚ`-algebra structure of `K`—unique in characteristic `0`, so the
`Classical.choice` in Mathlib's definition picks the standard one—and whose convergence on the
stated domain is `Atlas.Knowledge.PadicExpConvergence`. The isomorphism is stated unbundled: a
`Set.BijOn` between the images of `𝓂 ^ i` and of `U i (K)` in `K`, plus the homomorphism
identity and the two inversion identities. A bundled `MulEquiv` would be a definition, and a
definition may not carry a `sorry`; the unbundled quadruple records the same content as claims
and lets the bundling be built downstream once the proofs land. The bijection and the log-side
inversion are per level, under the integer guard `e < (p - 1) * i`; the two identities
`exp_add` and `padicLogarithm_exp` are instead stated once, on the convergence ideal
`𝓂 ^ (e / (p - 1) + 1)` of `Atlas.Knowledge.PadicExpConvergence`, which contains every deeper
level, so their per-level forms follow by inclusion. On these domains the value of the
exponential lands on a unit because its series has first term `1` and the tail falls in the
maximal ideal, which is what membership of the value in the image of `U i (K)` encodes. No
claim is made at or below the threshold, where the series diverges and the value of
`NormedSpace.exp` is junk.

`exp_add` is the Cauchy product and nothing more. `NormedSpace.exp_eq_tsum_rat` spells the
exponential as exactly the `tsum` this layer writes, and on the convergence ideal the series is
*absolutely* summable—`Atlas.Knowledge.PadicExpConvergence.summable_norm_expSeries`, which is
the "if" half of the threshold theorem factored out for this purpose—so
`tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm` turns the product of the two sums into
a sum over antidiagonals, and what remains is the binomial identity one `n` at a time:
`(n !)⁻¹ * (n.choose i) = (i !)⁻¹ * (j !)⁻¹` for `i + j = n`, which is
`Nat.add_choose_mul_factorial_mul_factorial` cast into `K`. Nothing about the nonarchimedean
structure enters beyond the absolute summability, which is why this one claim of the four is
reachable while the two inversion identities are not: those need the functional equation of
`PowerSeries.log`, which Mathlib does not have at this revision.

The cited sources state the inverse-isomorphism pair on the whole
convergence ball—Koblitz over `ℂ_p`, from which the restriction to `K` is immediate—and the
per-level bijection is the standard refinement: above the threshold the exponential and the
logarithm preserve the valuation, so the ball bijection cuts to each level; the level
statement of the third source is the instance the layer's consumers use.

## References

* [FesenkoVostokov2002] I. B. Fesenko, S. V. Vostokov, *Local fields and their extensions*,
  Translations of Mathematical Monographs **121**, American Mathematical Society, second
  edition, 2002.
* [Koblitz1984] N. Koblitz, *p-adic numbers, p-adic analysis, and zeta-functions*, Graduate
  Texts in Mathematics **58**, Springer New York, 1984.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

open ValuativeRel Finset.HasAntidiagonal
open scoped Nat

namespace Atlas.Knowledge

namespace PadicExpIsomorphism

/-- The binomial identity behind `exp_add`, one `n` at a time: the `n`th term of the
exponential series at `x + y` is the antidiagonal sum of the products of the `i`th term at `x`
and the `j`th term at `y`, because `(n !)⁻¹ * (n.choose i) = (i !)⁻¹ * (j !)⁻¹`. -/
private theorem expTerm_add (K : Type*) [Field K] [CharZero K] (x y : K) (n : ℕ) :
    ((n ! : ℚ)⁻¹) • (x + y) ^ n
      = ∑ kl ∈ antidiagonal n, (((kl.1 ! : ℚ)⁻¹) • x ^ kl.1) * (((kl.2 ! : ℚ)⁻¹) • y ^ kl.2) := by
  rw [(Commute.all x y).add_pow', Finset.smul_sum]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [mem_antidiagonal] at hkl
  subst hkl
  have h1 : ((kl.1 ! : ℕ) : K) ≠ 0 := by exact_mod_cast kl.1.factorial_ne_zero
  have h2 : ((kl.2 ! : ℕ) : K) ≠ 0 := by exact_mod_cast kl.2.factorial_ne_zero
  have h3 : ((((kl.1 + kl.2)! : ℕ)) : K) ≠ 0 := by exact_mod_cast (kl.1 + kl.2).factorial_ne_zero
  have hkey : (((kl.1 + kl.2).choose kl.1 : ℕ) : K) * ((kl.1 ! : ℕ) : K) * ((kl.2 ! : ℕ) : K)
      = (((kl.1 + kl.2)! : ℕ) : K) := by
    have h := Nat.add_choose_mul_factorial_mul_factorial kl.2 kl.1
    rw [Nat.add_comm kl.2 kl.1] at h
    exact_mod_cast congrArg (fun m : ℕ => (m : K)) (by linarith [h] : (kl.1 + kl.2).choose kl.1 *
      kl.1 ! * kl.2 ! = (kl.1 + kl.2)!)
  rw [Rat.smul_def, Rat.smul_def, Rat.smul_def, nsmul_eq_mul]
  push_cast
  field_simp
  linear_combination (x ^ kl.1 * y ^ kl.2) * hkey

end PadicExpIsomorphism


/-- Above the threshold `e / (p - 1)`, the exponential is a bijection of the ideal power onto
the higher unit group: for `(p - 1) * i > e`, `NormedSpace.exp` maps the image of `𝓂 ^ i` in
`K` bijectively onto the image of `U i (K)`. With `PadicExpIsomorphism.exp_add` and the two
inversion identities, this is the statement that `exp` and `log` are mutually inverse
isomorphisms between `𝓂 ^ i` and `U i (K)`. Claim recorded ahead of its proof
([Fesenko–Vostokov 2002, Chap. VI, (1.4), p.212][FesenkoVostokov2002] and
[Koblitz 1984, Chap. IV, §1, Prop., p.81][Koblitz1984] for the pair on the whole convergence
ball; [Hyeon 2025, §4, p.17][Hyeon2025] for the restriction to a level; the per-level form is
the standard refinement, per the implementation notes). -/
theorem padicExpIsomorphism (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (i : ℕ+)
    (hi : absoluteRamificationIndex K < (residueCharacteristic K - 1) * (i : ℕ)) :
    Set.BijOn NormedSpace.exp
      (((↑) : ↥𝒪[K] → K) '' ((𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) : Set ↥𝒪[K]))
      (((↑) : Kˣ → K) '' (higherUnitGroup K i : Set Kˣ)) := by
  sorry

namespace PadicExpIsomorphism

set_option synthInstance.maxHeartbeats 80000 in
-- The ideal arithmetic on `↥𝒪[K]` does not fit the default instance budget.
/-- On the convergence ideal, the exponential turns addition into multiplication:
`exp (x + y) = exp x * exp y` for `x`, `y` in `𝓂 ^ (e / (p - 1) + 1)`—hence on every deeper
level by inclusion ([Koblitz 1984, Chap. IV, §1, p.80][Koblitz1984];
[Fesenko–Vostokov 2002, Chap. VI, (1.2) and (1.5), pp.208, 212][FesenkoVostokov2002]). -/
theorem exp_add (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (x y : ↥𝒪[K])
    (hx : x ∈ (𝓂[K] ^ (absoluteRamificationIndex K / (residueCharacteristic K - 1) + 1) :
      Ideal ↥𝒪[K]))
    (hy : y ∈ (𝓂[K] ^ (absoluteRamificationIndex K / (residueCharacteristic K - 1) + 1) :
      Ideal ↥𝒪[K])) :
    NormedSpace.exp ((x : K) + (y : K)) = NormedSpace.exp (x : K) * NormedSpace.exp (y : K) := by
  have hp : (residueCharacteristic K).Prime := residueCharacteristic_prime K
  -- Rebuild the normed structure; its topology is the given one.
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  haveI : CompleteSpace K := inferInstance
  have hc : ∀ z : K, ‖z‖ ≤ 1 ↔ valuation K z ≤ 1 := fun z => Valued.toNormedField.norm_le_one_iff
  have hpe := span_residueCharacteristic_eq_maximalIdeal_pow K
  rw [NormedSpace.exp_eq_tsum_rat]
  simp only
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (PadicExpConvergence.summable_norm_expSeries hc hp hpe hx)
    (PadicExpConvergence.summable_norm_expSeries hc hp hpe hy)]
  exact tsum_congr fun n => expTerm_add K _ _ n

/-- The logarithm inverts the exponential on the convergence ideal: `log (exp x) = x` for
`x ∈ 𝓂 ^ (e / (p - 1) + 1)`—hence on every deeper level by inclusion. Claim recorded ahead of
its proof ([Koblitz 1984, Chap. IV, §1, p.81][Koblitz1984];
[Fesenko–Vostokov 2002, Chap. VI, (1.4), p.212][FesenkoVostokov2002]). -/
theorem padicLogarithm_exp (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (x : ↥𝒪[K])
    (hx : x ∈ (𝓂[K] ^ (absoluteRamificationIndex K / (residueCharacteristic K - 1) + 1) :
      Ideal ↥𝒪[K])) :
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
