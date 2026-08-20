import Mathlib
import Atlas.Knowledge.FormalLogExp

/-!
# formal power law of the logarithm

The identity `log ((1 + X) ^ n) = n • log (1 + X)` in `A⟦X⟧` for a `ℚ`-algebra `A`: the
logarithm series at the `n`th power of `1 + X` is `n` times the logarithm series, as an
identity of formal power series and before any question of convergence. This is the
coefficient-level fact behind `Atlas.Knowledge.PadicLogarithm.log_mul`: the additivity of the
logarithm on the deep unit levels descends to all principal units through `p`-power descent,
`p ^ k • log u = log (u ^ (p ^ k))`, and the descent is this law evaluated at a principal
unit through `Atlas.Knowledge.PowerSeriesCompositionValue`.

## Main statements

* `formalLogOf_pow` — `log ((1 + X) ^ n) = n • log (1 + X)`.

## Implementation notes

The sources state the two-variable addition law `log ((1 + X)(1 + Y)) = log (1 + X) +
log (1 + Y)` in `ℚ⟦X, Y⟧` and specialize it; the layer records the one-variable `n`-fold
specialization instead, because it is what the descent consumes and it stays inside
`PowerSeries`, where Mathlib's substitution calculus lives—`MvPowerSeries` substitution would
buy the two-variable law at the price of a second evaluation theory the layer would then need
to build.

The proof is the calculus one, as in `Atlas.Knowledge.FormalLogExp` and with its `formalGeom`:
both sides have derivative `n • formalGeom` and constant coefficient `0`, and
`PowerSeries.derivative.ext` closes—the `IsAddTorsionFree` hypothesis being what that
principle needs. The derivative computation never divides by `1 + X` and never writes
`n - 1`: the relation `d ((1 + X) ^ n) * (1 + X) = n • (1 + X) ^ n` holds for every `n`
including `0`, so after the chain rule both sides are multiplied by the unit `1 + X` and
compared against the substituted inverse relation
`subst ((1 + X) ^ n - 1) formalGeom * (1 + X) ^ n = 1` on one side and
`Atlas.Knowledge.formalGeom_mul` on the other.

## References

* [Koblitz1984] N. Koblitz, *p-adic numbers, p-adic analysis, and zeta-functions*, Graduate
  Texts in Mathematics **58**, Springer New York, 1984.
* [FesenkoVostokov2002] I. B. Fesenko, S. V. Vostokov, *Local fields and their extensions*,
  Translations of Mathematical Monographs **121**, American Mathematical Society, second
  edition, 2002.
-/

open PowerSeries

namespace Atlas.Knowledge

namespace FormalLogPow

variable (A : Type*) [CommRing A]

/-- `(1 + X) ^ n - 1` has zero constant coefficient, so substitution into it is defined. -/
theorem hasSubst_pow_sub_one (n : ℕ) : HasSubst ((1 + X : PowerSeries A) ^ n - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp)

/-- The substituted geometric series inverts `(1 + X) ^ n`: substituting `(1 + X) ^ n - 1`
into `formalGeom * (1 + X) = 1` and rewriting `1 + ((1 + X) ^ n - 1)` back to `(1 + X) ^ n`. -/
theorem subst_formalGeom_mul (n : ℕ) :
    subst ((1 + X : PowerSeries A) ^ n - 1) (formalGeom A) * (1 + X) ^ n = 1 := by
  have hsub := hasSubst_pow_sub_one A n
  have hone : subst ((1 + X : PowerSeries A) ^ n - 1) (1 : PowerSeries A) = 1 := by
    rw [← coe_substAlgHom hsub, map_one]
  have h := congrArg (subst ((1 + X : PowerSeries A) ^ n - 1)) (formalGeom_mul A)
  rw [subst_mul hsub, subst_add hsub, subst_X hsub, hone,
    show (1 : PowerSeries A) + ((1 + X : PowerSeries A) ^ n - 1) = (1 + X) ^ n by ring] at h
  exact h

/-- `d ((1 + X) ^ n) * (1 + X) = n • (1 + X) ^ n`: the derivative of the power, multiplied
back to the full exponent so that no `n - 1` appears and `n = 0` needs no separate case
downstream. -/
theorem derivative_pow_mul (n : ℕ) :
    d⁄dX A ((1 + X : PowerSeries A) ^ n) * (1 + X) = n • (1 + X : PowerSeries A) ^ n := by
  have hd : d⁄dX A (1 + X : PowerSeries A) = 1 := by
    rw [map_add, Derivation.map_one_eq_zero, derivative_X, zero_add]
  cases n with
  | zero => simp
  | succ m =>
      rw [derivative_pow, hd, mul_one, Nat.succ_sub_one, mul_assoc, ← pow_succ,
        nsmul_eq_mul]

end FormalLogPow

open FormalLogPow in
/-- **The formal power law of the logarithm**: `log ((1 + X) ^ n) = n • log (1 + X)` in
`A⟦X⟧` for a `ℚ`-algebra `A`. The `n`-fold specialization of the sources' two-variable
addition law, recorded in one variable per the implementation notes
([Koblitz 1984, Chap. IV, §1, pp.79–80][Koblitz1984], the formal identity in `ℚ⟦X, Y⟧` at the
foot of p.79 and the additivity it yields on p.80;
[Fesenko–Vostokov 2002, Chap. VI, (1.2), p.208][FesenkoVostokov2002]). -/
theorem formalLogOf_pow (A : Type*) [CommRing A] [Algebra ℚ A] [IsAddTorsionFree A] (n : ℕ) :
    logOf ((1 + X : PowerSeries A) ^ n) = n • log A := by
  have hsub := hasSubst_pow_sub_one A n
  have hunit : IsUnit (1 + X : PowerSeries A) :=
    IsUnit.of_mul_eq_one (formalGeom A) (by rw [mul_comm]; exact formalGeom_mul A)
  refine derivative.ext ?_ ?_
  · rw [logOf_eq, derivative_subst A hsub, FormalLogExp.derivative_log_eq, map_nsmul,
      FormalLogExp.derivative_log_eq,
      show d⁄dX A ((1 + X : PowerSeries A) ^ n - 1) = d⁄dX A ((1 + X : PowerSeries A) ^ n) by
        rw [map_sub, Derivation.map_one_eq_zero, sub_zero]]
    refine hunit.mul_right_cancel ?_
    calc subst ((1 + X : PowerSeries A) ^ n - 1) (formalGeom A)
          * d⁄dX A ((1 + X : PowerSeries A) ^ n) * (1 + X)
        = subst ((1 + X : PowerSeries A) ^ n - 1) (formalGeom A)
            * (d⁄dX A ((1 + X : PowerSeries A) ^ n) * (1 + X)) := mul_assoc _ _ _
      _ = subst ((1 + X : PowerSeries A) ^ n - 1) (formalGeom A)
            * (n • (1 + X : PowerSeries A) ^ n) := by rw [derivative_pow_mul]
      _ = n • (subst ((1 + X : PowerSeries A) ^ n - 1) (formalGeom A)
            * (1 + X : PowerSeries A) ^ n) := mul_smul_comm n _ _
      _ = n • (1 : PowerSeries A) := by rw [subst_formalGeom_mul]
      _ = n • (formalGeom A * (1 + X)) := by rw [formalGeom_mul]
      _ = n • formalGeom A * (1 + X) := (smul_mul_assoc n _ _).symm
  · rw [constantCoeff_logOf (by simp), map_nsmul, constantCoeff_log, smul_zero]

end Atlas.Knowledge
