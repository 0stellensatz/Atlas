import Mathlib
import Atlas.Knowledge.AbsoluteInertiaDegree
import Atlas.Knowledge.AbsoluteRamificationIndex
import Atlas.Knowledge.IsUnitFiltration
import Atlas.Knowledge.QuasiFreeFiltered
import Atlas.Knowledge.ShiftRhoEP
import Atlas.Knowledge.TRhoEP

/-!
# quasi-freeness of the unit filtration

The unit filtration of a mixed-characteristic local field is `(f_K, ρ_K)`-quasi-free: for
`ρ_K = ρ_ep e_K p_K` the shift of `Atlas.Knowledge.ShiftRhoEP` at the absolute ramification
index and the residue characteristic, and `f_K` the absolute inertia degree, every unit
filtration of `Atlas.Knowledge.IsUnitFiltration` satisfies the three conditions of
`Atlas.Knowledge.QuasiFreeFiltered`. This is where the arithmetic of the field meets the
filtered-module combinatorics: the graded pieces are residue-field vector spaces of dimension
`f_K`, `p`-powering moves the chain along `ρ_K`, and the defects concentrate—at most
one-dimensionally—at the critical index. Its consequence, the classification of the unit
filtration by extended jump pairs, is `Atlas.Knowledge.UnitFiltrationClassification`.

## Main statements

* `unitFiltration_isQuasiFree` — the unit filtration is `(f_K, ρ_K)`-quasi-free. Claim
  recorded ahead of its proof.

## Implementation notes

The shift parameters enter as `ℕ+` variables pinned to `Atlas.Knowledge.ResidueCharacteristic`,
`Atlas.Knowledge.AbsoluteRamificationIndex`, and `Atlas.Knowledge.AbsoluteInertiaDegree` by
equations, `ρ_ep` and `ℤ_[p]` asking for different carriers of the same numbers; `1 < p` is a
hypothesis rather than a derivation from primality for the same reason. The uniformizer of
`ℤ_[p]` at which the defects are read is `p` itself, whose irreducibility is Mathlib's
`PadicInt.irreducible_p`. The source states the proposition for any local field; the
mixed-characteristic hypothesis matches the layer's standing vocabulary, whose shifts with
finite `T` are the `ρ_ep` of characteristic `0`—the equal-characteristic case runs along
`Atlas.Knowledge.ShiftRhoP` and is not stated here.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

open ValuativeRel

namespace Atlas.Knowledge

/-- The unit filtration of a mixed-characteristic local field is `(f_K, ρ_K)`-quasi-free, for
`ρ_K` the shift `ρ_ep` at the absolute ramification index and the residue characteristic and
`f_K` the absolute inertia degree. Claim recorded ahead of its proof
([Pagano 2022, Prop. 5.1, p.442][Pagano2022]). -/
theorem unitFiltration_isQuasiFree (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (p e f : ℕ+) [Fact (p : ℕ).Prime] (hp1 : 1 < p)
    (hp : (p : ℕ) = residueCharacteristic K)
    (he : (e : ℕ) = absoluteRamificationIndex K)
    (hf : (f : ℕ) = absoluteInertiaDegree K)
    [Module ℤ_[(p : ℕ)] (Additive ↥(higherUnitGroup K 1))]
    (F : FilteredModule ℤ_[(p : ℕ)] (Additive ↥(higherUnitGroup K 1)))
    (hF : IsUnitFiltration K (p : ℕ) F) :
    IsQuasiFree (ρ_ep e p hp1) (T_ρ_ep_finite e p hp1) f PadicInt.irreducible_p F := by
  sorry

end Atlas.Knowledge
