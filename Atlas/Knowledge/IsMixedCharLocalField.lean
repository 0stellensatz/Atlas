import Mathlib

/-!
# mixed-characteristic local field

A **mixed-characteristic local field** is a nonarchimedean local field of characteristic `0`:
equivalently, a finite extension of `ℚ_[p]` for some prime `p`, which is how the sources
introduce it. This class is the carrier signature every item of the anabelian layer is stated
over, fixed once so that the invariants `Atlas.Knowledge.ResidueCharacteristic`,
`Atlas.Knowledge.AbsoluteRamificationIndex`, and their derived companions all speak about the
same object—and so that `Atlas.Knowledge.HigherUnitGroup`, which asks only for `Field` and
`ValuativeRel`, applies to it without translation.

## Main definitions

* `IsMixedCharLocalField` — a `ValuativeRel` field, locally compact in its valuation topology,
  of characteristic `0`.

## Implementation notes

The encoding extends Mathlib's `IsNonarchimedeanLocalField`, which packages the valuation-topology
compatibility, local compactness, and nontriviality, and derives discreteness of the valuation
and finiteness of the residue field. Adding `CharZero` is exactly the mixed-characteristic
condition: the residue field of a nonarchimedean local field is finite, so its characteristic is
already a prime `p`, and what remains free is the characteristic of the field itself—`0` here,
against `p` in the equal-characteristic case. No `ℚ_[p]`-algebra structure is carried: the
sources' "finite extension of `ℚ_[p]`" is a theorem about this class, not data in it, and the
`ValuativeRel` signature is what the rest of the layer already assumes.

## References

* [Mochizuki1997] S. Mochizuki, *A version of the Grothendieck conjecture for p-adic local
  fields*, Int. J. Math. **8** (1997), 499–506.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

/-- A **mixed-characteristic local field**: a nonarchimedean local field of characteristic `0`,
equivalently a finite extension of `ℚ_[p]`
([Mochizuki 1997, §1, p.500][Mochizuki1997]; [Hyeon 2025, §1, p.3][Hyeon2025]). -/
class IsMixedCharLocalField (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] :
    Prop extends IsNonarchimedeanLocalField K, CharZero K

end Atlas.Knowledge
