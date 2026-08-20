import Mathlib

/-!
# value of a composition of power series

Substitution of formal power series is compatible with evaluation: if `g` has zero constant
coefficient and its terms at `x` are dominated by a summable weight, and the coefficients of `f`
grow at most polynomially in the norm, then the series of `subst g f` at `x` sums to
`∑ (coeff d f) • (value of g at x) ^ d`—the value of the composition is the composition of the
values. This is the transfer principle that turns the formal functional equations of
`Atlas.Knowledge.FormalLogExp` into identities between convergent sums, and it is the piece
whose absence blocked the inversion identities of `Atlas.Knowledge.PadicExpIsomorphism` and the
additivity `Atlas.Knowledge.PadicLogarithm.log_mul`.

## Main definitions

* `PowerSeriesCompositionValue.value` — the sum `∑ (coeff m g) • x ^ m` of a rational power
  series at a point, total by the junk-value convention of `tsum`.
* `PowerSeriesCompositionValue.Dominates` — a weight `t : ℕ → ℝ` dominates the series of `g`
  at `x` when `‖(coeff m g) • x ^ m‖ ≤ t m` for every `m`.

## Main statements

* `PowerSeriesCompositionValue.value_subst` — the value of `subst g f` at `x` is
  `∑ (coeff d f) • (value x g) ^ d`.
* `PowerSeriesCompositionValue.value_mul` — the value of a product is the product of the
  values, on dominated series.

## Implementation notes

The source states the composition principle for a local number field and proves it by the
double-sum estimate; here the signature is the minimal one under which that argument runs—a
complete normed field whose metric is ultrametric—and the convergence data is carried by an
explicit weight `t` rather than by a radius, because the two consumers hold their estimates in
exactly that form: the exponential weight `c ^ (w * m) / c ^ (e * v_p (m !))` of
`Atlas.Knowledge.PadicExpConvergence.exists_norm_term_eq` above the threshold, and the
geometric weight `‖x‖ ^ m` for a series with integral coefficients on the maximal ideal. The
weight is asked to be submultiplicative (`t i * t j ≤ t (i + j)`), which is what the ultrametric
bound on `coeff_mul`'s antidiagonal needs, and to remain summable against every polynomial,
which is what the double-sum exchange needs: the inner index never exceeds the outer one, since
`g ^ d` has no coefficients below `d`, so the polynomial slack absorbs the coefficient growth
of `f`. The exchange itself is absolute convergence over `ℕ × ℕ` and two applications of
Fubini—the same discipline as `Atlas.Knowledge.PadicExpConvergence`, which likewise runs on
absolute convergence because Mathlib has no ultrametric summability criterion at this revision.

Mathlib's own evaluation, `PowerSeries.aeval`, is not usable here: it evaluates at a
topologically nilpotent point of a linearly topologized ring, a field's linear ring topology is
discrete, and the valuation ring—which is linearly topologized—is not a `ℚ`-algebra. The
by-hand `value` and this file's exchange are the workaround, recorded once for both consumers.

## References

* [FesenkoVostokov2002] I. B. Fesenko, S. V. Vostokov, *Local fields and their extensions*,
  Translations of Mathematical Monographs **121**, American Mathematical Society, second
  edition, 2002.
-/

open PowerSeries

namespace Atlas.Knowledge

namespace PowerSeriesCompositionValue

variable {K : Type*} [NormedField K] [CharZero K]

/-- The **value** of a rational power series at a point: the sum `∑ (coeff m g) • x ^ m`,
total by the junk-value convention of `tsum`
([Fesenko–Vostokov 2002, Chap. VI, (1.4), p.211][FesenkoVostokov2002]). -/
noncomputable def value (x : K) (g : PowerSeries ℚ) : K :=
  ∑' m : ℕ, coeff m g • x ^ m

/-- A weight `t` **dominates** the series of `g` at `x` when it bounds the term norms:
`‖(coeff m g) • x ^ m‖ ≤ t m` for every `m`. The convergence data of
[Fesenko–Vostokov 2002, Chap. VI, (1.4), p.211][FesenkoVostokov2002], carried as an explicit
bound rather than as a radius. -/
def Dominates (t : ℕ → ℝ) (x : K) (g : PowerSeries ℚ) : Prop :=
  ∀ m : ℕ, ‖coeff m g • x ^ m‖ ≤ t m

variable {t : ℕ → ℝ} {x : K}

/-- The constant series `1` is dominated by any weight with `1 ≤ t 0` and nonnegative tail. -/
theorem Dominates.one (htnn : ∀ m, 0 ≤ t m) (ht0 : 1 ≤ t 0) : Dominates t x 1 := by
  intro m
  rcases eq_or_ne m 0 with rfl | hm
  · simpa [coeff_one] using ht0
  · simpa [coeff_one, hm] using htnn m

/-- Domination is stable under products, for a submultiplicative weight: the coefficient of the
product is an antidiagonal sum, the ultrametric bounds it by the largest term, and
submultiplicativity closes. -/
theorem Dominates.mul [IsUltrametricDist K] (htnn : ∀ m, 0 ≤ t m)
    (htmul : ∀ i j, t i * t j ≤ t (i + j)) {g h : PowerSeries ℚ}
    (hg : Dominates t x g) (hh : Dominates t x h) : Dominates t x (g * h) := by
  intro m
  rw [coeff_mul, Finset.sum_smul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (htnn m) ?_
  rintro ⟨i, j⟩ hij
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  calc ‖(coeff i g * coeff j h) • x ^ m‖
      = ‖(coeff i g • x ^ i) * (coeff j h • x ^ j)‖ := by
        rw [smul_mul_smul_comm, ← pow_add, hij]
    _ = ‖coeff i g • x ^ i‖ * ‖coeff j h • x ^ j‖ := norm_mul _ _
    _ ≤ t i * t j := mul_le_mul (hg i) (hh j) (norm_nonneg _) (htnn i)
    _ ≤ t m := hij ▸ htmul i j

/-- Domination is stable under powers. -/
theorem Dominates.pow [IsUltrametricDist K] (htnn : ∀ m, 0 ≤ t m) (ht0 : 1 ≤ t 0)
    (htmul : ∀ i j, t i * t j ≤ t (i + j)) {g : PowerSeries ℚ} (hg : Dominates t x g) :
    ∀ d : ℕ, Dominates t x (g ^ d)
  | 0 => by rw [pow_zero]; exact Dominates.one htnn ht0
  | d + 1 => by
      rw [pow_succ]
      exact (Dominates.pow htnn ht0 htmul hg d).mul htnn htmul hg

/-- The term norms of a dominated series are summable against a summable weight. -/
theorem Dominates.summable_norm (hts : Summable t) {g : PowerSeries ℚ}
    (hg : Dominates t x g) : Summable fun m : ℕ => ‖coeff m g • x ^ m‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hg hts

/-- Domination is stable under subtracting `1`: only the constant coefficient moves, and the
ultrametric bounds the difference by the larger of the two norms. -/
theorem Dominates.sub_one [IsUltrametricDist K] (ht0 : 1 ≤ t 0) {g : PowerSeries ℚ}
    (hg : Dominates t x g) : Dominates t x (g - 1) := by
  intro m
  rcases eq_or_ne m 0 with rfl | hm
  · rw [map_sub, sub_smul, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hg 0) ?_)
    rw [norm_neg]
    simpa [coeff_one] using ht0
  · have h1 : coeff m (1 : PowerSeries ℚ) = 0 := by simp [coeff_one, hm]
    rw [map_sub, h1, sub_zero]
    exact hg m

/-- The value of a rational multiple is the multiple of the value. -/
theorem value_smul (q : ℚ) (g : PowerSeries ℚ) : value x (q • g) = q • value x g := by
  rw [value, value, Rat.smul_def, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [map_smul, smul_eq_mul, mul_smul, Rat.smul_def]

/-- The value of the constant series `1` is `1`. -/
theorem value_one : value x (1 : PowerSeries ℚ) = 1 := by
  rw [value, tsum_eq_single 0 (fun m hm => by simp [coeff_one, hm])]
  simp

/-- The value of `X` is the point itself. -/
theorem value_X : value x (X : PowerSeries ℚ) = x := by
  rw [value, tsum_eq_single 1 (fun m hm => by simp [coeff_X, hm])]
  simp

/-- The value of `g - 1` is the value of `g` less `1`, for a summably dominated `g`. -/
theorem value_sub_one [CompleteSpace K] (hts : Summable t) {g : PowerSeries ℚ}
    (hg : Dominates t x g) : value x (g - 1) = value x g - 1 := by
  have h1 : Summable fun m : ℕ => coeff m g • x ^ m := (hg.summable_norm hts).of_norm
  have h2 : Summable fun m : ℕ => coeff m (1 : PowerSeries ℚ) • x ^ m :=
    summable_of_ne_finset_zero (s := {0}) fun m hm => by
      rw [Finset.mem_singleton] at hm
      simp [coeff_one, hm]
  have hsplit : value x (g - 1)
      = ∑' m : ℕ, (coeff m g • x ^ m - coeff m (1 : PowerSeries ℚ) • x ^ m) :=
    tsum_congr fun m => by rw [map_sub, sub_smul]
  rw [hsplit, h1.tsum_sub h2, ← value, ← value, value_one]

/-- The value of a product of dominated series is the product of the values: the Cauchy
product, available by absolute convergence
([Fesenko–Vostokov 2002, Chap. VI, (1.5), p.212][FesenkoVostokov2002], the operation `×`). -/
theorem value_mul [CompleteSpace K] (hts : Summable t) {g h : PowerSeries ℚ}
    (hg : Dominates t x g) (hh : Dominates t x h) :
    value x (g * h) = value x g * value x h := by
  rw [value, value, value,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      (hg.summable_norm hts) (hh.summable_norm hts)]
  refine tsum_congr fun m => ?_
  rw [coeff_mul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  rw [smul_mul_smul_comm, ← pow_add, hij]

/-- The value of a power of a dominated series is the power of the value. -/
theorem value_pow [IsUltrametricDist K] [CompleteSpace K] (htnn : ∀ m, 0 ≤ t m)
    (ht0 : 1 ≤ t 0) (htmul : ∀ i j, t i * t j ≤ t (i + j)) (hts : Summable t)
    {g : PowerSeries ℚ} (hg : Dominates t x g) :
    ∀ d : ℕ, value x (g ^ d) = value x g ^ d
  | 0 => by rw [pow_zero, pow_zero, value_one]
  | d + 1 => by
      rw [pow_succ, pow_succ,
        value_mul hts (hg.pow htnn ht0 htmul d) hg,
        value_pow htnn ht0 htmul hts hg d]

/-- A power series with zero constant coefficient has no coefficients below the exponent in
its powers. -/
theorem coeff_pow_eq_zero {g : PowerSeries ℚ} (hg0 : constantCoeff g = 0)
    {m d : ℕ} (hmd : m < d) : coeff m (g ^ d) = 0 :=
  X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hg0) d) m hmd

/-- **The value of a composition is the composition of the values**: for `g` dominated with
zero constant coefficient and `f` with polynomially growing coefficients, the series of
`subst g f` at `x` sums to `∑ (coeff d f) • (value x g) ^ d`. The double sum converges
absolutely because `g ^ d` has no coefficients below `d`, so the inner index bounds the outer
one and the weight's polynomial slack absorbs the growth of `f`; two applications of Fubini
exchange the two orders of summation
([Fesenko–Vostokov 2002, Chap. VI, (1.5), Prop., p.212][FesenkoVostokov2002], specialized from
`F̂ᵘʳ` to the field itself, with the radius data carried by the weight). -/
theorem value_subst [IsUltrametricDist K] [CompleteSpace K] (htnn : ∀ m, 0 ≤ t m)
    (ht0 : 1 ≤ t 0) (htmul : ∀ i j, t i * t j ≤ t (i + j))
    (htpoly : ∀ N : ℕ, Summable fun m : ℕ => ((m : ℝ) + 1) ^ N * t m)
    {g f : PowerSeries ℚ} (hg : Dominates t x g) (hg0 : constantCoeff g = 0)
    {N : ℕ} (hf : ∀ d : ℕ, ‖coeff d f • (1 : K)‖ ≤ ((d : ℝ) + 1) ^ N) :
    value x (subst g f) = ∑' d : ℕ, coeff d f • value x g ^ d := by
  have hsub : HasSubst g := HasSubst.of_constantCoeff_zero' hg0
  have hts : Summable t := by simpa using htpoly 0
  set F : ℕ × ℕ → K := fun md => coeff md.2 f • (coeff md.1 (g ^ md.2) • x ^ md.1) with hF
  have hsmul_norm : ∀ (q : ℚ) (y : K), ‖q • y‖ = ‖q • (1 : K)‖ * ‖y‖ := fun q y => by
    rw [Rat.smul_def, Rat.smul_def, mul_one, norm_mul]
  have hFzero : ∀ m d : ℕ, m < d → F (m, d) = 0 := fun m d h => by
    simp [hF, coeff_pow_eq_zero hg0 h]
  have hFbound : ∀ m d : ℕ, ‖F (m, d)‖ ≤ ((d : ℝ) + 1) ^ N * t m := fun m d =>
    calc ‖F (m, d)‖
        = ‖coeff d f • (1 : K)‖ * ‖coeff m (g ^ d) • x ^ m‖ := hsmul_norm _ _
      _ ≤ ((d : ℝ) + 1) ^ N * t m :=
          mul_le_mul (hf d) (hg.pow htnn ht0 htmul d m) (norm_nonneg _) (by positivity)
  -- absolute convergence over the product index
  have hnorm_sum : Summable fun md : ℕ × ℕ => ‖F md‖ := by
    rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
    constructor
    · intro m
      refine summable_of_ne_finset_zero (s := Finset.range (m + 1)) fun d hd => ?_
      rw [Finset.mem_range, not_lt] at hd
      rw [hFzero m d (by omega), norm_zero]
    · refine Summable.of_nonneg_of_le (fun m => tsum_nonneg fun d => norm_nonneg _)
        (fun m => ?_) (htpoly (N + 1))
      have hsum_eq : ∑' d : ℕ, ‖F (m, d)‖ = ∑ d ∈ Finset.range (m + 1), ‖F (m, d)‖ := by
        refine tsum_eq_sum fun d hd => ?_
        rw [Finset.mem_range, not_lt] at hd
        rw [hFzero m d (by omega), norm_zero]
      rw [hsum_eq]
      calc ∑ d ∈ Finset.range (m + 1), ‖F (m, d)‖
          ≤ (Finset.range (m + 1)).card • (((m : ℝ) + 1) ^ N * t m) := by
            refine Finset.sum_le_card_nsmul _ _ _ fun d hd => ?_
            rw [Finset.mem_range] at hd
            refine (hFbound m d).trans (mul_le_mul_of_nonneg_right ?_ (htnn m))
            have hdm : (d : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr (by omega)
            exact pow_le_pow_left₀ (by positivity) (by linarith) N
        _ = ((m : ℝ) + 1) ^ (N + 1) * t m := by
            rw [Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
  have hFsum : Summable F := Summable.of_norm hnorm_sum
  -- the two iterated sums agree with the double sum
  have hswap : ∑' m : ℕ, ∑' d : ℕ, F (m, d) = ∑' d : ℕ, ∑' m : ℕ, F (m, d) :=
    (Summable.tsum_comm (f := fun m d => F (m, d)) hFsum).symm
  -- the left iterated sum is the value of the composition
  have hL : value x (subst g f) = ∑' m : ℕ, ∑' d : ℕ, F (m, d) := by
    rw [value]
    refine tsum_congr fun m => ?_
    have hsupp : (Function.support fun d : ℕ => coeff d f • coeff m (g ^ d))
        ⊆ (Finset.range (m + 1) : Finset ℕ) := by
      intro d hd
      simp only [Function.mem_support] at hd
      by_contra hdm
      rw [Finset.coe_range, Set.mem_Iio, not_lt] at hdm
      exact hd (by rw [coeff_pow_eq_zero hg0 (by omega), smul_zero])
    rw [coeff_subst' hsub, finsum_eq_sum_of_support_subset _ hsupp,
      tsum_eq_sum (s := Finset.range (m + 1)) (fun d hd => by
        rw [Finset.mem_range, not_lt] at hd
        exact hFzero m d (by omega)),
      Finset.sum_smul]
    exact Finset.sum_congr rfl fun d _ => by rw [smul_eq_mul, mul_smul]
  -- the right iterated sum is the composition of the values
  have hR : ∀ d : ℕ, ∑' m : ℕ, F (m, d) = coeff d f • value x g ^ d := fun d => by
    have hFd : ∀ m : ℕ, F (m, d) = ((coeff d f : ℚ) : K) * (coeff m (g ^ d) • x ^ m) :=
      fun m => by simp only [hF]; rw [Rat.smul_def]
    simp only [hFd]
    rw [tsum_mul_left, ← Rat.smul_def, ← value,
      value_pow htnn ht0 htmul hts hg d]
  rw [hL, hswap]
  exact tsum_congr hR

end PowerSeriesCompositionValue

end Atlas.Knowledge
