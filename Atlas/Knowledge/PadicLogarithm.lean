import Mathlib
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.RationalIntegerValuation
import Atlas.Knowledge.ResidueCharacteristic

/-!
# p-adic logarithm

The logarithm series `log x = ∑ (-1)ⁿ / (n + 1) • (x - 1) ^ (n + 1)`, as a total function on a
topological field of characteristic `0`, together with the two facts that make it the standing map
of the layer on a mixed-characteristic local field: the series converges on every principal unit,
and there it turns multiplication into addition. The exponential needs no counterpart definition,
because Mathlib's `NormedSpace.exp` is the same series construction for the inverse direction;
`Atlas.Knowledge.PadicExpConvergence` states its convergence threshold, and
`Atlas.Knowledge.PadicExpIsomorphism` states the mutual inversion of the two maps above that
threshold. The logarithm is the mechanism by which the multiplicative structure of the higher
unit groups `Atlas.Knowledge.HigherUnitGroup` becomes additive—the step every free-rank
computation of the anabelian layer routes through, as in
`Atlas.Knowledge.DeepUnitGroup` and, downstream, `Atlas.Knowledge.AbsoluteGaloisInvariance`.

## Main definitions

* `padicLogarithm` — the logarithm series at `x`, expanded around `1`, as a `tsum`.

## Main statements

* `PadicLogarithm.summable` — the series converges on every principal unit.
* `PadicLogarithm.log_mul` — on principal units the logarithm turns multiplication into addition.
  Claim recorded ahead of its proof.

## Implementation notes

The definition is a bare `tsum`, so it is total: off the summable locus it takes the junk value
`0`, and every claim about it carries the membership hypothesis that puts it on the honest locus.
The coefficients are rational and act through the `ℚ`-module structure that `CharZero` provides,
which is the unique one on a field of characteristic `0`—the same route Mathlib's
`NormedSpace.exp` takes for the exponential series. The definition asks only for a topological
field of characteristic `0`, the minimal signature under which the series makes sense; the two
claims are about a mixed-characteristic local field, which is where the sources state them and
where the layer consumes them. Convergence on all principal units is what distinguishes the
logarithm from the exponential, whose series converges only above the threshold of
`Atlas.Knowledge.PadicExpConvergence`; the image of a principal unit under the logarithm can
nonetheless fall outside the maximal ideal when the ramification is large, so no claim about
where the values land is made here—above the threshold that is
`Atlas.Knowledge.PadicExpIsomorphism`'s business.

Convergence is proved by *absolute* convergence, which is available here even though the field is
nonarchimedean and the sharper ultrametric criterion would also serve: the term at `n` has norm
`‖(n + 1 : K)‖⁻¹ * r ^ (n + 1)` with `r < 1`, and the reciprocal norm of a rational integer grows
only polynomially—`Atlas.Knowledge.RationalIntegerValuation.exists_norm_natCast_inv_le`—so the
real series of norms converges by comparison with a polynomial-times-geometric one.

The statements mention no norm and no uniformity: `K` carries its valuative relation and the
topology of the local-field class, nothing more, and the normed structure is rebuilt inside the
proof from the local-field hypotheses—the same discipline as
`Atlas.Knowledge.IntegralClosureDVR`, and for the same reason, that the auxiliary uniformity must
not escape into the statement. `Summable` depends only on the topology, and the topology the
rebuilt norm induces is the given one definitionally, so the conclusion is about the field as the
layer carries it.

## References

* [FesenkoVostokov2002] I. B. Fesenko, S. V. Vostokov, *Local fields and their extensions*,
  Translations of Mathematical Monographs **121**, American Mathematical Society, second
  edition, 2002.
* [Koblitz1984] N. Koblitz, *p-adic numbers, p-adic analysis, and zeta-functions*, Graduate
  Texts in Mathematics **58**, Springer New York, 1984.
-/

open ValuativeRel

namespace Atlas.Knowledge

/-- The **p-adic logarithm**: the series `∑ (-1)ⁿ / (n + 1) • (x - 1) ^ (n + 1)`, the expansion
of `log` around `1`, total by the junk-value convention of `tsum`
([Fesenko–Vostokov 2002, Chap. VI, (1.2), p.208][FesenkoVostokov2002];
[Koblitz 1984, Chap. IV, §1, pp.78–79][Koblitz1984]). -/
noncomputable def padicLogarithm (K : Type*) [Field K] [TopologicalSpace K] [CharZero K]
    (x : K) : K :=
  ∑' n : ℕ, ((-1) ^ n / (n + 1) : ℚ) • (x - 1) ^ (n + 1)

namespace PadicLogarithm

open RationalIntegerValuation

/-- The logarithm series converges on every principal unit of a mixed-characteristic local
field: for `u` in the first higher unit group, the series of `padicLogarithm` at `u` is
summable ([Fesenko–Vostokov 2002, Chap. VI, (1.4), p.212][FesenkoVostokov2002];
[Koblitz 1984, Chap. IV, §1, pp.78–79][Koblitz1984]). -/
theorem summable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (u : Kˣ) (hu : u ∈ higherUnitGroup K 1) :
    Summable fun n : ℕ => ((-1) ^ n / (n + 1) : ℚ) • ((u : K) - 1) ^ (n + 1) := by
  -- Rebuild the normed structure from the local-field hypotheses; its topology is the given one.
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  haveI : CompleteSpace K := inferInstance
  have hc : ∀ x : K, ‖x‖ ≤ 1 ↔ valuation K x ≤ 1 := fun x => Valued.toNormedField.norm_le_one_iff
  obtain ⟨N, -, hN⟩ := exists_norm_natCast_inv_le hc (residueCharacteristic_prime K)
  -- A principal unit sits at distance strictly less than one from `1`.
  have hr : ‖(u : K) - 1‖ < 1 := by
    obtain ⟨y, hy⟩ := hu
    have hy1 : ((y : ↥𝒪[K]) : K) = (u : K) - 1 := by rw [← hy]; ring
    rw [norm_lt_one_iff_valuation_lt_one hc, ← hy1]
    exact valuation_lt_one_of_mem_maximalIdeal _ (Ideal.pow_le_self one_ne_zero y.2)
  -- Termwise the norm is `‖(n + 1 : K)‖⁻¹ * r ^ (n + 1)`.
  have key : ∀ n : ℕ, ‖((-1) ^ n / (n + 1) : ℚ) • ((u : K) - 1) ^ (n + 1)‖
      = ‖((n + 1 : ℕ) : K)‖⁻¹ * ‖(u : K) - 1‖ ^ (n + 1) := by
    intro n
    rw [Rat.smul_def, norm_mul, norm_pow]
    congr 1
    push_cast
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, inv_eq_one_div]
  apply Summable.of_norm
  simp only [key]
  refine (_root_.summable_nat_add_iff
    (f := fun m : ℕ => ‖((m : ℕ) : K)‖⁻¹ * ‖(u : K) - 1‖ ^ m) 1).mpr ?_
  have hgeo : Summable fun m : ℕ => (m : ℝ) ^ N * ‖(u : K) - 1‖ ^ m :=
    summable_pow_mul_geometric_of_norm_lt_one N
      (r := ‖(u : K) - 1‖) (by rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)])
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hgeo
  exact mul_le_mul_of_nonneg_right (hN m) (by positivity)

/-- On principal units the p-adic logarithm turns multiplication into addition:
`log (u * v) = log u + log v` for `u`, `v` in the first higher unit group. Claim recorded ahead
of its proof ([Koblitz 1984, Chap. IV, §1, p.80][Koblitz1984];
[Fesenko–Vostokov 2002, Chap. VI, (1.2) and (1.5), pp.208, 212][FesenkoVostokov2002]). -/
theorem log_mul (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (u v : Kˣ) (hu : u ∈ higherUnitGroup K 1)
    (hv : v ∈ higherUnitGroup K 1) :
    padicLogarithm K ((u : K) * v) = padicLogarithm K (u : K) + padicLogarithm K (v : K) := by
  sorry

end PadicLogarithm

end Atlas.Knowledge
