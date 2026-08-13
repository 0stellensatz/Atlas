import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.MStepSolvableQuotient

/-!
# center-freeness of the m-step solvable quotients

The maximal `(m + 1)`-step solvable quotient `Atlas.Knowledge.MStepSolvableQuotient` of the
absolute Galois group of a mixed-characteristic local field is center-free for every `m ≥ 1`.
This is the source's Proposition A.1, proved in its appendix from the localization of the
center recorded in `Atlas.Knowledge.MStepSolvableCenterBound` together with local class field
theory and Kummer theory; it is what makes the outer-automorphism formulation of the main
theorems equivalent to the isomorphism-of-fields one, and it fails for `m = 0`: `G_K^1` is
abelian, its own center.

## Main statements

* `center_mStepSolvableQuotient_eq_bot` — `Z (G_K^{m+1}) = ⊥` for `m ≥ 1`. Claim recorded
  ahead of its proof.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

/-- The maximal `(m + 1)`-step solvable quotient of the absolute Galois group of a
mixed-characteristic local field is center-free for `m ≥ 1`. Claim recorded ahead of its proof
([Hyeon 2025, Prop. A.1, p.23][Hyeon2025]). -/
theorem center_mStepSolvableQuotient_eq_bot (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsMixedCharLocalField K] {m : ℕ} (hm : 1 ≤ m) :
    Subgroup.center (mStepSolvableQuotient (Field.absoluteGaloisGroup K) (m + 1)) = ⊥ := by
  sorry

end Atlas.Knowledge
