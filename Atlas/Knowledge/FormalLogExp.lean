import Mathlib

/-!
# formal inversion of exp by log

The identity `log (exp X) = X` in `A⟦X⟧` for a `ℚ`-algebra `A`: the logarithm series composed
with the exponential series is the identity, as an identity of formal power series and before
any question of convergence. It is the coefficient-level fact behind the two inversion
identities of `Atlas.Knowledge.PadicExpIsomorphism`—each of those is this identity evaluated at
a point where both series converge, and neither can be proved without it. The additivity
`Atlas.Knowledge.PadicLogarithm.log_mul` is *not* behind it: that claim lives on all the
principal units, the exponential converges only above the threshold `e / (p - 1)`, and the
formal identity the additivity runs on instead is the power law of
`Atlas.Knowledge.FormalLogPow`.

## Main definitions

* `formalGeom` — the geometric series `∑ (-1)ⁿ Xⁿ`, which is the derivative of `log (1 + X)`.

## Main statements

* `formalLogOf_exp` — `log (exp X) = X`.
* `formalGeom_mul` — `formalGeom * (1 + X) = 1`, the formal inverse relation the chain rule needs.

## Implementation notes

Mathlib carries `PowerSeries.exp` and `PowerSeries.log` with their coefficients, orders and
derivatives, and it carries the chain rule `PowerSeries.derivative_subst` and the uniqueness
principle `PowerSeries.derivative.ext`—but **no functional equation relating exp and log**: no
`log_mul`, no `log_exp`, no `exp_log`. This item supplies the one that the `p`-adic side of the
layer needs. It is stated for a general `ℚ`-algebra rather than for `ℚ`, since the consumers
substitute into rings of characteristic zero and the proof costs nothing extra.

The proof is the calculus one, made formal. Differentiating `log (exp X)` by the chain rule gives
`(d log) ∘ (exp - 1) * d (exp - 1)`, which is `formalGeom ∘ (exp - 1) * exp`; substituting
`exp - 1` into `formalGeom * (1 + X) = 1` and using that substitution is a ring homomorphism
turns `1 + (exp - 1) = exp` into the statement that this product is `1`. So both sides have
derivative `1` and constant coefficient `0`, and `PowerSeries.derivative.ext` closes it—the
`IsAddTorsionFree` hypothesis being what that principle needs to divide by the exponent.

`formalGeom * (1 + X) = 1` is not proved coefficientwise: it is Mathlib's
`PowerSeries.mk_one_mul_one_sub_eq_one` pushed through the ring homomorphism
`PowerSeries.rescale (-1)`, which turns `1 - X` into `1 + X` and `∑ Xⁿ` into `∑ (-1)ⁿ Xⁿ`.

**What this item does not do is transfer the identity to a convergent evaluation.** Mathlib's
`PowerSeries.aeval` cannot: it evaluates at a topologically nilpotent point of a *linearly
topologized* ring, a field's linear ring topology is discrete, and the valuation ring—which is
linearly topologized—is not a `ℚ`-algebra, `p` being a nonunit in it. The transfer has to be
done by hand, by expanding `(exp x - 1) ^ d` as an iterated Cauchy product and exchanging the
double sum by absolute convergence. That is what the consumers still wait on; this item removes
the other half of the obstruction.

## References

* [Koblitz1984] N. Koblitz, *p-adic numbers, p-adic analysis, and zeta-functions*, Graduate
  Texts in Mathematics **58**, Springer New York, 1984.
-/

open PowerSeries

namespace Atlas.Knowledge

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The geometric series `∑ (-1)ⁿ Xⁿ`: the termwise derivative of the logarithm series
`log (1 + X) = ∑ (-1)ⁿ⁺¹ Xⁿ / n` of [Koblitz 1984, Chap. IV, §1, p.78][Koblitz1984]. -/
noncomputable def formalGeom : PowerSeries A := mk fun n => (-1 : A) ^ n

namespace FormalLogExp

omit [Algebra ℚ A] in
/-- `formalGeom` is `∑ Xⁿ` rescaled at `-1`. -/
theorem formalGeom_eq_rescale : formalGeom A = rescale (-1 : A) (mk 1) := by
  ext n
  simp [formalGeom, coeff_rescale]

/-- `formalGeom` is the derivative of `log (1 + X)`. -/
theorem derivative_log_eq : d⁄dX A (log A) = formalGeom A := by
  rw [deriv_log]
  ext n
  simp [formalGeom]

end FormalLogExp

omit [Algebra ℚ A] in
/-- `formalGeom * (1 + X) = 1`: the geometric series is the formal inverse of `1 + X`. -/
theorem formalGeom_mul : formalGeom A * (1 + X) = 1 := by
  have h := congrArg (rescale (-1 : A)) (mk_one_mul_one_sub_eq_one A)
  rw [map_mul, map_one, map_sub, map_one, rescale_X] at h
  rw [FormalLogExp.formalGeom_eq_rescale]
  convert h using 2
  simp

open FormalLogExp in
/-- **The formal logarithm inverts the formal exponential**: `log (exp X) = X` in `A⟦X⟧` for a
`ℚ`-algebra `A`. This is the coefficient-level identity behind every convergent statement that
`exp` and `log` are mutually inverse ([Koblitz 1984, Chap. IV, §1, pp.80–81][Koblitz1984]). -/
theorem formalLogOf_exp [IsAddTorsionFree A] : logOf (exp A) = (X : PowerSeries A) := by
  refine derivative.ext ?_ ?_
  · rw [logOf_eq, derivative_subst A HasSubst.exp_sub_one, derivative_log_eq, derivative_X]
    have hd : d⁄dX A (exp A - 1) = exp A := by
      rw [map_sub, derivative_exp, Derivation.map_one_eq_zero, sub_zero]
    have hone : subst (exp A - 1) (1 : PowerSeries A) = (1 : PowerSeries A) := by
      rw [← coe_substAlgHom (HasSubst.exp_sub_one (A := A)), map_one]
    have hs : subst (exp A - 1) (formalGeom A * (1 + X)) = (1 : PowerSeries A) := by
      rw [formalGeom_mul, hone]
    rw [subst_mul HasSubst.exp_sub_one, subst_add HasSubst.exp_sub_one,
      subst_X HasSubst.exp_sub_one, hone,
      show (1 : PowerSeries A) + (exp A - 1) = exp A by ring] at hs
    rw [hd]
    exact hs
  · rw [constantCoeff_logOf constantCoeff_exp]
    simp

end Atlas.Knowledge
