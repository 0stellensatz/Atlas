import Mathlib
import Atlas.Knowledge.GroupAbsoluteDegree
import Atlas.Knowledge.GroupAbsoluteInertiaDegree

/-!
# group-theoretic absolute ramification index

The **group-theoretic absolute ramification index** `e(G)` of an abelian group: the quotient
`d(G) / f(G)` of the group-theoretic absolute degree `Atlas.Knowledge.GroupAbsoluteDegree` by
the group-theoretic absolute inertia degree `Atlas.Knowledge.GroupAbsoluteInertiaDegree`. This
is the fundamental identity `d = e * f` run backwards, exactly as the source defines it; for
`G` of MLF^ab-type it recovers the absolute ramification index
`Atlas.Knowledge.AbsoluteRamificationIndex` of the field, as
`Atlas.Knowledge.AbelianizedGaloisRecovery` records.

## Main definitions

* `groupAbsoluteRamificationIndex` — the natural-number quotient `d(G) / f(G)`.

## Implementation notes

The division is `Nat` division, taking the junk value `0` when `f(G) = 0`; for a group of
MLF^ab-type `f(G) ≥ 1` and `f(G)` divides `d(G)`, so the quotient is exact there.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

/-- The **group-theoretic absolute ramification index** of an abelian group: the quotient of
the group-theoretic absolute degree by the group-theoretic absolute inertia degree
([Hyeon 2025, §3, p.10][Hyeon2025]). -/
noncomputable def groupAbsoluteRamificationIndex (G : Type*) [CommGroup G] : ℕ :=
  groupAbsoluteDegree G / groupAbsoluteInertiaDegree G

end Atlas.Knowledge
