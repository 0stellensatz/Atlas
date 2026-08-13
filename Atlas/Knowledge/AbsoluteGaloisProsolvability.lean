import Mathlib
import Atlas.Knowledge.ClosedDerivedSeries
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.IsProsolvable

/-!
# prosolvability of the absolute Galois group

The absolute Galois group of a mixed-characteristic local field is prosolvable
`Atlas.Knowledge.IsProsolvable` but not solvable: its closed derived series
`Atlas.Knowledge.ClosedDerivedSeries` has trivial infimum yet no trivial term, so the series is
strictly decreasing forever. Prosolvability comes from the tower of unramified, tamely
ramified, and wildly ramified pieces; the non-solvability comes from the wild inertia subgroup
of `G_{ℚ_p}` being a free pro-`p` group of countably infinite rank. Together these make the
solvability degree `Atlas.Knowledge.SolvabilityDegree` of `G_K^m` exactly `m`.

## Main statements

All three are claims recorded ahead of their proofs.

* `isProsolvable_absoluteGaloisGroup` — `G_K` is prosolvable.
* `iInf_closedDerivedSeries_absoluteGaloisGroup` — `⨅ m, closedDerivedSeries (G_K) m = ⊥`.
* `closedDerivedSeries_absoluteGaloisGroup_ne_bot` — no term of the series is trivial.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

/-- The absolute Galois group of a mixed-characteristic local field is prosolvable. Claim
recorded ahead of its proof ([Hyeon 2025, Rem. 2.4 (1), p.9][Hyeon2025]). -/
theorem isProsolvable_absoluteGaloisGroup : IsProsolvable (Field.absoluteGaloisGroup K) := by
  sorry

/-- The closed derived series of the absolute Galois group of a mixed-characteristic local
field has trivial infimum—the group-level trace of prosolvability. Claim recorded ahead of its
proof ([Hyeon 2025, Rem. 2.4 (1), p.9][Hyeon2025]). -/
theorem iInf_closedDerivedSeries_absoluteGaloisGroup :
    ⨅ m : ℕ, closedDerivedSeries (Field.absoluteGaloisGroup K) m = ⊥ := by
  sorry

/-- No term of the closed derived series of the absolute Galois group of a
mixed-characteristic local field is trivial: `G_K` is prosolvable but not solvable, the wild
inertia of `G_{ℚ_p}` being free pro-`p` of infinite rank. Claim recorded ahead of its proof
([Hyeon 2025, Rem. 2.4 (1), p.9][Hyeon2025]). -/
theorem closedDerivedSeries_absoluteGaloisGroup_ne_bot (m : ℕ) :
    closedDerivedSeries (Field.absoluteGaloisGroup K) m ≠ ⊥ := by
  sorry

end Atlas.Knowledge
