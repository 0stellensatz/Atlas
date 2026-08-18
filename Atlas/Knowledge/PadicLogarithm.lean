import Mathlib
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.IsMixedCharLocalField

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

Both are claims recorded ahead of their proofs.

* `PadicLogarithm.summable` — the series converges on every principal unit.
* `PadicLogarithm.log_mul` — on principal units the logarithm turns multiplication into addition.

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

/-- The logarithm series converges on every principal unit of a mixed-characteristic local
field: for `u` in the first higher unit group, the series of `padicLogarithm` at `u` is
summable. Claim recorded ahead of its proof
([Fesenko–Vostokov 2002, Chap. VI, (1.4), p.212][FesenkoVostokov2002];
[Koblitz 1984, Chap. IV, §1, pp.78–79][Koblitz1984]). -/
theorem summable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (u : Kˣ) (hu : u ∈ higherUnitGroup K 1) :
    Summable fun n : ℕ => ((-1) ^ n / (n + 1) : ℚ) • ((u : K) - 1) ^ (n + 1) := by
  sorry

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
