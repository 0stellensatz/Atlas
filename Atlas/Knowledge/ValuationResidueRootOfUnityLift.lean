import Mathlib

/-!
# lifting residue roots of unity

Every root of unity in the residue field of a valuation subring of an algebraically closed
field lifts to a root of unity of the same specified exponent. The polynomial `X ^ m - 1`
splits in the valuation ring because all its roots are integral; reduction maps its roots
onto the residue roots.

## Main statements

* `valuationResidueRootOfUnityLift` — lift a root of unity through the residue map.
-/

namespace Atlas.Knowledge

/-- Residue roots of unity lift over a valuation ring in an algebraically closed field. -/
theorem valuationResidueRootOfUnityLift
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω)
    {m : ℕ} (hm : m ≠ 0) (z : IsLocalRing.ResidueField A) (hz : z ^ m = 1) :
    ∃ a : A, a ^ m = 1 ∧ IsLocalRing.residue A a = z := by
  classical
  let p : Polynomial A := Polynomial.X ^ m - Polynomial.C 1
  have hp : p.Monic := Polynomial.monic_X_pow_sub_C 1 hm
  have hs : p.Splits := by
    apply Polynomial.Splits.of_splits_map_of_injective
      (show Function.Injective (algebraMap A Ω) from Subtype.val_injective)
      (IsAlgClosed.splits _)
    intro a ha
    have hpa : a ^ m = 1 := by
      have h := (Polynomial.mem_roots ((hp.map (algebraMap A Ω)).ne_zero)).mp ha
      simpa [p, Polynomial.IsRoot, sub_eq_zero] using h
    exact IsIntegrallyClosed.algebraMap_eq_of_integral
      (show IsIntegral A a from
        ⟨Polynomial.X ^ m - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hm,
          by simp [hpa]⟩)
  have hzroot : z ∈ (p.map (IsLocalRing.residue A)).roots := by
    apply (Polynomial.mem_roots (hp.map (IsLocalRing.residue A)).ne_zero).mpr
    simp [p, Polynomial.IsRoot, hz]
  rw [hs.roots_map_of_ne_zero (hp.map (IsLocalRing.residue A)).ne_zero] at hzroot
  obtain ⟨a, ha, hred⟩ := Multiset.mem_map.mp hzroot
  refine ⟨a, ?_, hred⟩
  have h := (Polynomial.mem_roots hp.ne_zero).mp ha
  simpa only [p, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using h

end Atlas.Knowledge
