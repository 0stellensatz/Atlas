import Mathlib
import Atlas.Knowledge.AbsoluteDegree
import Atlas.Knowledge.AbsoluteRamificationIndex
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.ResidueCharacteristic

/-!
# deep unit group

The higher unit groups above the threshold `e / (p - 1)`—the deep unit groups—are free
`ℤ_p`-modules of rank the absolute degree: for `(p - 1) * i > e`, `U i (K)` of
`Atlas.Knowledge.HigherUnitGroup` is topologically isomorphic to `d` copies of `ℤ_[p]`, for
`d = e * f` the absolute degree `Atlas.Knowledge.AbsoluteDegree`. The exp/log pair of
`Atlas.Knowledge.PadicExpIsomorphism` does the work: it identifies `U i (K)` with the ideal
power `𝓂 ^ i`, a free module of rank `d` over `ℤ_p`. This is the free-rank engine of the
anabelian layer—reading the rank `d` off a deep open subgroup of the unit group is how the
absolute degree becomes group-theoretic, which is what the recovery claims of
`Atlas.Knowledge.AbsoluteGaloisInvariance` consume through local class field theory.

## Main statements

* `deepUnitGroup_continuousMulEquiv` — a deep unit group is topologically isomorphic to
  `Multiplicative (Fin d → ℤ_[p])`. Claim recorded ahead of its proof.

## Implementation notes

The free `ℤ_p`-module structure is encoded as a topological group isomorphism onto
`Multiplicative (Fin d → ℤ_[p])`: on a pro-`p` abelian topological group the `ℤ_p`-action is the
continuous extension of the `ℤ`-power maps, so the topological group structure already
determines the module structure and a `≃ₜ*` carries the full statement without a module
instance on a subgroup of `Kˣ`. The prime enters as a variable `p` pinned to
`Atlas.Knowledge.ResidueCharacteristic` by an equation, because the notation `ℤ_[p]` requires a
`Fact p.Prime` instance that a projection like `residueCharacteristic K` cannot carry by
itself. Deepness is the same integer inequality `e < (p - 1) * i` as in
`Atlas.Knowledge.PadicExpIsomorphism`; it is also what makes the group torsion-free, a `p`-th
root of unity having valuation exactly the threshold and therefore lying in no deep level. The
structure of the full principal-unit group `U 1 (K)`—the free part of rank `d` against its
torsion—is the filtered-module business of the arithmetic tranche and is deliberately not
recorded here.

## References

* [FesenkoVostokov2002] I. B. Fesenko, S. V. Vostokov, *Local fields and their extensions*,
  Translations of Mathematical Monographs **121**, American Mathematical Society, second
  edition, 2002.
* [Mochizuki1997] S. Mochizuki, *A version of the Grothendieck conjecture for p-adic local
  fields*, Int. J. Math. **8** (1997), 499–506.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

open ValuativeRel

namespace Atlas.Knowledge

/-- A **deep unit group** is free of rank the absolute degree: for `(p - 1) * i > e`, the higher
unit group `U i (K)`, in its subspace topology, is topologically isomorphic to
`Multiplicative (Fin d → ℤ_[p])` for `d = e * f` the absolute degree—the exp/log pair
identifying it with `𝓂 ^ i`, a free `ℤ_p`-module of rank `d`. Claim recorded ahead of its proof
([Fesenko–Vostokov 2002, Chap. I, (6.1) and (6.5), pp.17–20][FesenkoVostokov2002];
[Mochizuki 1997, §1, p.501][Mochizuki1997]; [Hyeon 2025, §4, p.17][Hyeon2025]). -/
theorem deepUnitGroup_continuousMulEquiv (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsMixedCharLocalField K] (p : ℕ) [Fact p.Prime]
    (hp : residueCharacteristic K = p) (i : ℕ+)
    (hi : absoluteRamificationIndex K < (p - 1) * (i : ℕ)) :
    Nonempty (↥(higherUnitGroup K i) ≃ₜ* Multiplicative (Fin (absoluteDegree K) → ℤ_[p])) := by
  sorry

end Atlas.Knowledge
