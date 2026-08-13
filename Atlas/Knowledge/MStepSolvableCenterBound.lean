import Mathlib
import Atlas.Knowledge.ClosedDerivedSeries
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.MStepSolvableQuotient

/-!
# localization of the center of the m-step solvable quotients

The center of the maximal `(m + 1)`-step solvable quotient
`Atlas.Knowledge.MStepSolvableQuotient` of the absolute Galois group of a mixed-characteristic
local field lies inside the Galois group of the top step of the tower: inside
`Gal(K^{m+1} / K^m)`, the image of the `m`-th closed derived subgroup in the quotient. This is
the source's Lemma A.2, the first half of the center-freeness
`Atlas.Knowledge.MStepSolvableCenterFree`: a central element acts trivially on `G_K^{m}`'s
worth of the tower by local class field theory, so all that remains of it lives in the last
step. Unlike center-freeness itself this holds for every `m ≥ 0`.

## Main statements

* `center_mStepSolvableQuotient_le` — `Z (G_K^{m+1}) ≤ Gal(K^{m+1} / K^m)`, the right side
  encoded as the image of `closedDerivedSeries (G_K) m` under the projection. Claim recorded
  ahead of its proof.

## Implementation notes

The subgroup `Gal(K^{m+1} / K^m)` of `G_K^{m+1}` is the kernel of the projection
`G_K^{m+1} →* G_K^m`, which is the image of `closedDerivedSeries (G_K) m` under
`QuotientGroup.mk'`—the encoding used here, keeping the statement inside the group layer with
no mention of the field tower `Atlas.Knowledge.MStepSolvableExtension`.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

/-- The center of the maximal `(m + 1)`-step solvable quotient of the absolute Galois group of
a mixed-characteristic local field lies inside the image of the `m`-th closed derived
subgroup—inside `Gal(K^{m+1} / K^m)`. Claim recorded ahead of its proof
([Hyeon 2025, Lem. A.2, p.23][Hyeon2025]). -/
theorem center_mStepSolvableQuotient_le (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsMixedCharLocalField K] (m : ℕ) :
    Subgroup.center (mStepSolvableQuotient (Field.absoluteGaloisGroup K) (m + 1))
      ≤ (closedDerivedSeries (Field.absoluteGaloisGroup K) m).map
          (QuotientGroup.mk' (closedDerivedSeries (Field.absoluteGaloisGroup K) (m + 1))) := by
  sorry

end Atlas.Knowledge
