import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.ResidueCharacteristic

/-!
# valuation of a rational integer

On a mixed-characteristic local field the valuation of a nonzero natural number `m` is the
valuation of the residue characteristic raised to the `p`-adic valuation of `m`: the rational
integers meet `𝒪[K]` in the localization of `ℤ` at `p`, and the valuation restricted to them is
the `p`-adic one, rescaled by `v (p)`. Everything the analytic items of the layer need about the
coefficients of a power series comes from this—the coefficients of the logarithm are `1 / (n + 1)`
and those of the exponential are `1 / n !`, and both are rational integers inverted.

## Main statements

* `valuation_natCast_eq_one` — a natural number prime to the residue characteristic is a unit.
* `valuation_natCast` — the valuation of a nonzero natural number, in terms of `v (p)`.
* `RationalIntegerValuation.norm_natCast_eq_pow` — the same statement for a rank-one norm.
* `RationalIntegerValuation.exists_norm_natCast_inv_le` — the reciprocal norm of a rational
  integer is bounded by a fixed power of it, which is what makes a series with rational-integer
  denominators converge absolutely against a geometric one.

## Implementation notes

The public statements are valuative: `K` carries its valuative relation and nothing more, so
nothing here forces a norm or a uniformity on a consumer. The norm statements live in a
scaffolding namespace that takes the normed field as a *variable* together with the hypothesis
`hc` comparing its unit ball to the valuation's—the pattern of
`Atlas.Knowledge.IntegralClosureDVR`, and for the same reason: a consumer rebuilds the normed
structure inside its own proof from the local-field hypotheses and passes `hc`, so the auxiliary
uniformity never escapes into a statement. `Field` is deliberately absent from the scaffolding's
binders, since `NormedField` already carries it and listing both makes an instance diamond.

The polynomial bound of `exists_norm_natCast_inv_le` is stated with an unspecified exponent
rather than the sharp `log_p`-derived one, because no consumer needs sharpness and the
unspecified form is what survives `Valuation.RankOne.hom` being fixed by an arbitrary choice:
the norm is determined only up to a power, so any statement pinning the exponent would be about
the choice rather than about `K`. What is used is that *some* exponent works, which follows from
`p ^ padicValNat p m ≤ m` together with any `N` making `‖(p : K)‖⁻¹ ≤ p ^ N`.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [Koblitz1984] N. Koblitz, *p-adic numbers, p-adic analysis, and zeta-functions*, Graduate
  Texts in Mathematics **58**, Springer New York, 1984.
-/

open ValuativeRel

namespace Atlas.Knowledge

section Valuative

variable {K : Type*} [Field K] [ValuativeRel K]

set_option synthInstance.maxHeartbeats 80000 in
-- `IsLocalRing ↥𝒪[K]`, which the residue-field rewrites go through, does not fit the default
-- instance budget.
/-- A natural number is a unit of `𝒪[K]` exactly when it is prime to the residue
characteristic—the residue field has characteristic `p_K`, so a natural number's residue is
nonzero exactly when `p_K` does not divide it
([Serre 1979, Chap. II, §5, p.36][Serre1979]). -/
theorem isUnit_natCast_iff (m : ℕ) :
    IsUnit (m : ↥𝒪[K]) ↔ ¬ (residueCharacteristic K) ∣ m := by
  haveI := ringChar.charP 𝓀[K]
  rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, map_natCast,
    CharP.cast_eq_zero_iff 𝓀[K] (ringChar 𝓀[K]) m]
  rfl

/-- A natural number prime to the residue characteristic has valuation one
([Koblitz 1984, Chap. I, §2, p.2][Koblitz1984]). -/
theorem valuation_natCast_eq_one (m : ℕ) (hm : ¬ (residueCharacteristic K) ∣ m) :
    valuation K (m : K) = 1 := by
  have hu : IsUnit (m : ↥𝒪[K]) := (isUnit_natCast_iff m).mpr hm
  rw [(Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one] at hu
  simpa using hu

/-- The residue characteristic has valuation strictly less than one: it lies in the maximal
ideal ([Serre 1979, Chap. II, §5, p.36][Serre1979], "since p goes to zero in K̄, one has
v(p) ≥ 1", where Serre's v is additive and that inequality is this statement written
additively). -/
theorem valuation_residueCharacteristic_lt_one :
    valuation K ((residueCharacteristic K : ℕ) : K) < 1 := by
  have hnu : ¬ IsUnit ((residueCharacteristic K : ℕ) : ↥𝒪[K]) := by
    rw [isUnit_natCast_iff]; simp
  rw [(Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one] at hnu
  have hle : valuation K ((residueCharacteristic K : ℕ) : K) ≤ 1 := by
    simpa using (Valuation.integer.integers (valuation K)).map_le_one
      ((residueCharacteristic K : ℕ) : ↥𝒪[K])
  exact lt_of_le_of_ne hle (by simpa using hnu)

set_option synthInstance.maxHeartbeats 80000 in
-- The `𝓂[K]` in the hypothesis unfolds through `IsLocalRing ↥𝒪[K]`, which does not fit the
-- default instance budget.
/-- An element of the maximal ideal has valuation strictly less than one. -/
theorem valuation_lt_one_of_mem_maximalIdeal (y : ↥𝒪[K]) (hy : y ∈ 𝓂[K]) :
    valuation K (y : K) < 1 := by
  have hnu : ¬ IsUnit y := by rw [← IsLocalRing.notMem_maximalIdeal, not_not]; exact hy
  rw [(Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one] at hnu
  exact lt_of_le_of_ne ((Valuation.integer.integers (valuation K)).map_le_one _) hnu

end Valuative

/-- Split the `p`-part off a nonzero natural number: `m = p ^ padicValNat p m * m'` with `m'`
prime to `p`. -/
theorem exists_eq_pow_padicValNat_mul {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : m ≠ 0) :
    ∃ m', ¬ p ∣ m' ∧ m = p ^ padicValNat p m * m' := by
  obtain ⟨m', hm'⟩ : p ^ padicValNat p m ∣ m := pow_padicValNat_dvd
  refine ⟨m', ?_, hm'⟩
  intro ⟨c, hc⟩
  exact pow_succ_padicValNat_not_dvd hm ⟨c, by rw [pow_succ, mul_assoc, ← hc, ← hm']⟩

/-- The valuation of a nonzero natural number is `v (p)` raised to its `p`-adic valuation
([Koblitz 1984, Chap. I, §2, p.2][Koblitz1984], the definition `|x|_p = 1 / p ^ ord_p x`
rescaled by `v (p)`). -/
theorem valuation_natCast {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (m : ℕ) (hm : m ≠ 0) :
    valuation K (m : K) =
      valuation K ((residueCharacteristic K : ℕ) : K) ^
        padicValNat (residueCharacteristic K) m := by
  haveI : Fact (residueCharacteristic K).Prime := ⟨residueCharacteristic_prime K⟩
  obtain ⟨m', hm'dvd, hm'⟩ := exists_eq_pow_padicValNat_mul (p := residueCharacteristic K) hm
  nth_rewrite 1 [hm']
  push_cast
  rw [map_mul, map_pow, valuation_natCast_eq_one m' hm'dvd, mul_one]

namespace RationalIntegerValuation

variable {K : Type*} [NormedField K] [ValuativeRel K]
  (hc : ∀ x : K, ‖x‖ ≤ 1 ↔ valuation K x ≤ 1)

include hc

/-- The comparison of unit balls, above one. -/
theorem one_lt_norm_iff_one_lt_valuation (x : K) : 1 < ‖x‖ ↔ 1 < valuation K x := by
  simpa using not_congr (hc x)

/-- The comparison of unit balls, below one: obtained from the "above one" form at `x⁻¹`. -/
theorem norm_lt_one_iff_valuation_lt_one (x : K) : ‖x‖ < 1 ↔ valuation K x < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h1 : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
    have h2 : (0 : ValueGroupWithZero K) < valuation K x := zero_lt_iff.mpr (by simpa using hx)
    have e1 : ‖x‖ < 1 ↔ 1 < ‖x‖⁻¹ := by rw [one_lt_inv_iff₀]; simp [h1]
    have e2 : valuation K x < 1 ↔ 1 < (valuation K x)⁻¹ := by rw [one_lt_inv_iff₀]; simp [h2]
    rw [e1, e2, ← norm_inv, ← map_inv₀]
    exact one_lt_norm_iff_one_lt_valuation hc x⁻¹

/-- A natural number has norm at most one: it lies in the valuation ring. -/
theorem norm_natCast_le_one (m : ℕ) : ‖(m : K)‖ ≤ 1 := by
  rw [hc]
  have h : ((m : ↥𝒪[K]) : K) = (m : K) := by push_cast; rfl
  rw [← h]
  exact (m : ↥𝒪[K]).2

/-- The comparison of unit balls, on the unit sphere. -/
theorem norm_eq_one_iff_valuation_eq_one (x : K) : ‖x‖ = 1 ↔ valuation K x = 1 := by
  constructor
  · intro h
    exact le_antisymm ((hc x).mp h.le)
      (not_lt.mp fun hlt => absurd ((norm_lt_one_iff_valuation_lt_one hc x).mpr hlt) (by simp [h]))
  · intro h
    exact le_antisymm ((hc x).mpr h.le)
      (not_lt.mp fun hlt => absurd ((norm_lt_one_iff_valuation_lt_one hc x).mp hlt) (by simp [h]))

variable (hp : (residueCharacteristic K).Prime)

include hp

/-- The norm of a nonzero natural number is the norm of the residue characteristic raised to
its `p`-adic valuation ([Koblitz 1984, Chap. I, §2, p.2][Koblitz1984]). -/
theorem norm_natCast_eq_pow (m : ℕ) (hm : m ≠ 0) :
    ‖(m : K)‖ =
      ‖((residueCharacteristic K : ℕ) : K)‖ ^ padicValNat (residueCharacteristic K) m := by
  haveI : Fact (residueCharacteristic K).Prime := ⟨hp⟩
  obtain ⟨m', hm'dvd, hm'⟩ := exists_eq_pow_padicValNat_mul (p := residueCharacteristic K) hm
  nth_rewrite 1 [hm']
  push_cast
  rw [norm_mul, norm_pow,
    (norm_eq_one_iff_valuation_eq_one hc _).mpr (valuation_natCast_eq_one m' hm'dvd), mul_one]

variable [CharZero K]

/-- The reciprocal norm of a rational integer is bounded by a fixed power of it: the `p`-adic
valuation of `m` is at most `Nat.log p m`, so `‖(m : K)‖⁻¹` grows only polynomially. -/
theorem exists_norm_natCast_inv_le :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ m : ℕ, ‖(m : K)‖⁻¹ ≤ (m : ℝ) ^ N := by
  haveI : Fact (residueCharacteristic K).Prime := ⟨hp⟩
  set p := residueCharacteristic K with hpdef
  set c : ℝ := ‖((p : ℕ) : K)‖ with hcdef
  have hpge : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hc0 : 0 < c := by
    rw [hcdef, norm_pos_iff, Ne, Nat.cast_eq_zero]
    exact hp.ne_zero
  obtain ⟨N, hN⟩ : ∃ N : ℕ, c⁻¹ < (p : ℝ) ^ N :=
    pow_unbounded_of_one_lt _ (by exact_mod_cast hp.one_lt)
  have hcinv : c⁻¹ ≤ (p : ℝ) ^ (N + 1) := hN.le.trans (by
    rw [pow_succ]
    nlinarith [pow_nonneg (le_trans zero_le_one hpge) N])
  refine ⟨N + 1, Nat.le_add_left 1 N, fun m => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · have hdvd : p ^ padicValNat p m ≤ m :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hm) pow_padicValNat_dvd
    rw [norm_natCast_eq_pow hc hp m hm, ← inv_pow]
    calc (c⁻¹) ^ padicValNat p m
        ≤ ((p : ℝ) ^ (N + 1)) ^ padicValNat p m := pow_le_pow_left₀ (by positivity) hcinv _
      _ = ((p : ℝ) ^ padicValNat p m) ^ (N + 1) := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ (m : ℝ) ^ (N + 1) := pow_le_pow_left₀ (by positivity) (by exact_mod_cast hdvd) _

end RationalIntegerValuation

end Atlas.Knowledge
