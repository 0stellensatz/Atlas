import Mathlib
import Atlas.Knowledge.FormalLogPow
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.PowerSeriesCompositionValue
import Atlas.Knowledge.RationalIntegerValuation
import Atlas.Knowledge.ResidueCharacteristic

/-!
# p-adic logarithm

The logarithm series `log x = ∑ (-1)ⁿ / (n + 1) • (x - 1) ^ (n + 1)`, as a total function on a
topological field of characteristic `0`, together with the two facts that make it the standing map
of the layer on a mixed-characteristic local field: the series converges on every principal unit,
and there it turns multiplication into addition. The exponential needs no counterpart definition,
because Mathlib's `NormedSpace.exp` is the same series construction for the inverse direction;
`Atlas.Knowledge.PadicExpConvergence` states its convergence threshold, and
`Atlas.Knowledge.PadicExpIsomorphism` states the mutual inversion of the two maps above that
threshold. The logarithm is the mechanism by which the multiplicative structure of the higher
unit groups `Atlas.Knowledge.HigherUnitGroup` becomes additive—the step every free-rank
computation of the anabelian layer routes through, as in
`Atlas.Knowledge.DeepUnitGroup` and, downstream, `Atlas.Knowledge.AbsoluteGaloisInvariance`.

## Main definitions

* `padicLogarithm` — the logarithm series at `x`, expanded around `1`, as a `tsum`.

## Main statements

* `PadicLogarithm.summable` — the series converges on every principal unit.
* `PadicLogarithm.log_mul` — on principal units the logarithm turns multiplication into addition.

## Implementation notes

The definition is a bare `tsum`, so it is total: off the summable locus it takes the junk value
`0`, and every claim about it carries the membership hypothesis that puts it on the honest locus.
The coefficients are rational and act through the `ℚ`-module structure that `CharZero` provides,
which is the unique one on a field of characteristic `0`—the same route Mathlib's
`NormedSpace.exp` takes for the exponential series. The definition asks only for a topological
field of characteristic `0`, the minimal signature under which the series makes sense; the two
claims are about a mixed-characteristic local field, which is where the sources state them and
where the layer consumes them. Convergence on all principal units is what distinguishes the
logarithm from the exponential, whose series converges only above the threshold of
`Atlas.Knowledge.PadicExpConvergence`; the image of a principal unit under the logarithm can
nonetheless fall outside the maximal ideal when the ramification is large, so no claim about
where the values land is made here—above the threshold that is
`Atlas.Knowledge.PadicExpIsomorphism`'s business.

Convergence is proved by *absolute* convergence, which is available here even though the field is
nonarchimedean and the sharper ultrametric criterion would also serve: the term at `n` has norm
`‖(n + 1 : K)‖⁻¹ * r ^ (n + 1)` with `r < 1`, and the reciprocal norm of a rational integer grows
only polynomially—`Atlas.Knowledge.RationalIntegerValuation.exists_norm_natCast_inv_le`—so the
real series of norms converges by comparison with a polynomial-times-geometric one.

The additivity is proved without the exponential, which cannot reach it: `log_mul` lives on all
the principal units and the exponential converges only above the threshold. The route is
`p`-power descent. The power law `PadicLogarithm.log_pow`—the formal
`Atlas.Knowledge.formalLogOf_pow` evaluated through
`Atlas.Knowledge.PowerSeriesCompositionValue` with the geometric weight, no threshold
involved—scales the additivity deviation `log (uv) - log u - log v` by exactly `‖p‖ ^ k` when
`u` and `v` are replaced by their `p ^ k`th powers. Those powers sink into the filtration at
one level per step at first and then at `e` levels per step
(`PadicLogarithm.norm_pow_residueChar_sub_one_le`, the binomial expansion with every middle
coefficient divisible by `p`), and once the pair is deep the deviation is *second order*:
`PadicLogarithm.norm_log_mul_sub_le` bounds it by `ρ ^ 2 / ‖p‖` at depth `ρ`, the `d = 1` term
of the deviation series being exactly `(u - 1)(v - 1)` and every deeper term paying `ρ` per
degree against at most `‖p‖⁻¹` per power of `p` in its denominator. Deep depth squares while
the scaling is linear, so the deviation is smaller than every power of `‖p‖` and vanishes. The
sources instead specialize a two-variable formal addition law; the descent stays inside one
variable, per the implementation notes of `Atlas.Knowledge.FormalLogPow`.

The statements mention no norm and no uniformity: `K` carries its valuative relation and the
topology of the local-field class, nothing more, and the normed structure is rebuilt inside the
proof from the local-field hypotheses—the same discipline as
`Atlas.Knowledge.IntegralClosureDVR`, and for the same reason, that the auxiliary uniformity must
not escape into the statement. `Summable` depends only on the topology, and the topology the
rebuilt norm induces is the given one definitionally, so the conclusion is about the field as the
layer carries it.

## References

* [FesenkoVostokov2002] I. B. Fesenko, S. V. Vostokov, *Local fields and their extensions*,
  Translations of Mathematical Monographs **121**, American Mathematical Society, second
  edition, 2002.
* [Koblitz1984] N. Koblitz, *p-adic numbers, p-adic analysis, and zeta-functions*, Graduate
  Texts in Mathematics **58**, Springer New York, 1984.
-/

open ValuativeRel

namespace Atlas.Knowledge

/-- The **p-adic logarithm**: the series `∑ (-1)ⁿ / (n + 1) • (x - 1) ^ (n + 1)`, the expansion
of `log` around `1`, total by the junk-value convention of `tsum`
([Fesenko–Vostokov 2002, Chap. VI, (1.2), p.208][FesenkoVostokov2002];
[Koblitz 1984, Chap. IV, §1, pp.78–79][Koblitz1984]). -/
noncomputable def padicLogarithm (K : Type*) [Field K] [TopologicalSpace K] [CharZero K]
    (x : K) : K :=
  ∑' n : ℕ, ((-1) ^ n / (n + 1) : ℚ) • (x - 1) ^ (n + 1)

namespace PadicLogarithm

open RationalIntegerValuation

/-- The logarithm as a composition value: `padicLogarithm K y` is the value, in the sense of
`Atlas.Knowledge.PowerSeriesCompositionValue`, of the formal `log` series at `y - 1`. Pure
reindexing between the layer's `(n + 1)`-indexed spelling and the coefficient spelling of
`PowerSeries.log`, with no convergence hypothesis—off the summable locus the two sides junk
together. -/
theorem padicLogarithm_eq_value {K : Type*} [NormedField K] [CharZero K] (y : K) :
    padicLogarithm K y = PowerSeriesCompositionValue.value (y - 1) (PowerSeries.log ℚ) := by
  rw [padicLogarithm, PowerSeriesCompositionValue.value]
  refine ((Function.Injective.tsum_eq (g := Nat.succ) Nat.succ_injective ?_).symm.trans
    (tsum_congr fun n => ?_)).symm
  · intro d hd
    rcases d with _ | n
    · exact absurd (by simp [PowerSeries.coeff_log]) hd
    · exact ⟨n, rfl⟩
  · congr 1
    simp only [PowerSeries.coeff_log, Nat.succ_ne_zero, if_false, Algebra.algebraMap_self,
      RingHom.id_apply, Nat.succ_eq_add_one, pow_succ]
    push_cast
    ring

/-- The logarithm series converges on every principal unit of a mixed-characteristic local
field: for `u` in the first higher unit group, the series of `padicLogarithm` at `u` is
summable ([Fesenko–Vostokov 2002, Chap. VI, (1.4), p.212][FesenkoVostokov2002];
[Koblitz 1984, Chap. IV, §1, pp.78–79][Koblitz1984]). -/
theorem summable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (u : Kˣ) (hu : u ∈ higherUnitGroup K 1) :
    Summable fun n : ℕ => ((-1) ^ n / (n + 1) : ℚ) • ((u : K) - 1) ^ (n + 1) := by
  -- Rebuild the normed structure from the local-field hypotheses; its topology is the given one.
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  haveI : CompleteSpace K := inferInstance
  have hc : ∀ x : K, ‖x‖ ≤ 1 ↔ valuation K x ≤ 1 := fun x => Valued.toNormedField.norm_le_one_iff
  obtain ⟨N, -, hN⟩ := exists_norm_natCast_inv_le hc (residueCharacteristic_prime K)
  -- A principal unit sits at distance strictly less than one from `1`.
  have hr : ‖(u : K) - 1‖ < 1 := by
    obtain ⟨y, hy⟩ := hu
    have hy1 : ((y : ↥𝒪[K]) : K) = (u : K) - 1 := by rw [← hy]; ring
    rw [norm_lt_one_iff_valuation_lt_one hc, ← hy1]
    exact valuation_lt_one_of_mem_maximalIdeal _ (Ideal.pow_le_self one_ne_zero y.2)
  -- Termwise the norm is `‖(n + 1 : K)‖⁻¹ * r ^ (n + 1)`.
  have key : ∀ n : ℕ, ‖((-1) ^ n / (n + 1) : ℚ) • ((u : K) - 1) ^ (n + 1)‖
      = ‖((n + 1 : ℕ) : K)‖⁻¹ * ‖(u : K) - 1‖ ^ (n + 1) := by
    intro n
    rw [Rat.smul_def, norm_mul, norm_pow]
    congr 1
    push_cast
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, inv_eq_one_div]
  apply Summable.of_norm
  simp only [key]
  refine (_root_.summable_nat_add_iff
    (f := fun m : ℕ => ‖((m : ℕ) : K)‖⁻¹ * ‖(u : K) - 1‖ ^ m) 1).mpr ?_
  have hgeo : Summable fun m : ℕ => (m : ℝ) ^ N * ‖(u : K) - 1‖ ^ m :=
    summable_pow_mul_geometric_of_norm_lt_one N
      (r := ‖(u : K) - 1‖) (by rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)])
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hgeo
  exact mul_le_mul_of_nonneg_right (hN m) (by positivity)

section Normed

open PowerSeriesCompositionValue PowerSeries

variable {K : Type*} [NormedField K] [CharZero K] [ValuativeRel K]
  (hc : ∀ x : K, ‖x‖ ≤ 1 ↔ valuation K x ≤ 1)
  (hp : (residueCharacteristic K).Prime)

omit [ValuativeRel K] in
/-- The norm of the `d`th coefficient of the log series, read in `K`: `‖(d : K)‖⁻¹`. -/
theorem norm_coeff_log_smul_one {d : ℕ} (hd : d ≠ 0) :
    ‖PowerSeries.coeff d (PowerSeries.log ℚ) • (1 : K)‖ = ‖(d : K)‖⁻¹ := by
  rw [PowerSeries.coeff_log, if_neg hd, Algebra.algebraMap_self, RingHom.id_apply,
    Rat.smul_def, mul_one]
  push_cast
  rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div]

include hc hp in
/-- The coefficients of the log series grow at most polynomially in norm—the growth hypothesis
of the composition-value exchange, supplied once for both consumers of the log series. -/
theorem exists_norm_coeff_log_smul_le :
    ∃ N : ℕ, ∀ d : ℕ,
      ‖PowerSeries.coeff d (PowerSeries.log ℚ) • (1 : K)‖ ≤ ((d : ℝ) + 1) ^ N := by
  obtain ⟨N, -, hN⟩ := exists_norm_natCast_inv_le hc hp
  refine ⟨N, fun d => ?_⟩
  rcases eq_or_ne d 0 with rfl | hd
  · simp [PowerSeries.coeff_log]
  · rw [norm_coeff_log_smul_one hd]
    calc ‖(d : K)‖⁻¹ ≤ (d : ℝ) ^ N := hN d
      _ ≤ ((d : ℝ) + 1) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N

include hc hp in
/-- The log series is absolutely summable inside the open unit ball. -/
theorem summable_norm_logSeries {w : K} (hw : ‖w‖ < 1) :
    Summable fun d : ℕ => ‖PowerSeries.coeff d (PowerSeries.log ℚ) • w ^ d‖ := by
  obtain ⟨N, hN⟩ := exists_norm_coeff_log_smul_le hc hp
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun d => ?_)
    (summable_add_one_pow_mul_geometric (norm_nonneg w) hw N)
  rw [norm_rat_smul, norm_pow]
  exact mul_le_mul_of_nonneg_right (hN d) (by positivity)

include hc hp in
/-- **The power law of the logarithm** on the open unit ball around `1`:
`log (y ^ n) = n • log y`. The formal power law `Atlas.Knowledge.formalLogOf_pow` evaluated
through the composition-value exchange, with the geometric weight `‖y - 1‖ ^ m`—available on
the whole ball because `(1 + X) ^ n` has integral coefficients, with no threshold in sight
([Koblitz 1984, Chap. IV, §1, p.80][Koblitz1984], the corollary
`p^m log_p (1 + x) = log_p (1 + x) ^ (p^m)` drawn there from additivity; here proved directly
and *feeding* additivity instead, per the implementation notes). -/
theorem log_pow [IsUltrametricDist K] [CompleteSpace K] {y : K} (hy : ‖y - 1‖ < 1) (n : ℕ) :
    padicLogarithm K (y ^ n) = (n : ℚ) • padicLogarithm K y := by
  have h0 : (0 : ℝ) ≤ ‖y - 1‖ := norm_nonneg _
  have htnn : ∀ m : ℕ, (0 : ℝ) ≤ ‖y - 1‖ ^ m := fun m => by positivity
  have ht0 : (1 : ℝ) ≤ ‖y - 1‖ ^ 0 := by simp
  have htmul : ∀ i j : ℕ, ‖y - 1‖ ^ i * ‖y - 1‖ ^ j ≤ ‖y - 1‖ ^ (i + j) :=
    fun i j => (pow_add ‖y - 1‖ i j).symm.le
  have htpoly : ∀ N : ℕ, Summable fun m : ℕ => ((m : ℝ) + 1) ^ N * ‖y - 1‖ ^ m :=
    fun N => summable_add_one_pow_mul_geometric h0 hy N
  have hts : Summable fun m : ℕ => ‖y - 1‖ ^ m := by simpa using htpoly 0
  have hdomX : Dominates (fun m => ‖y - 1‖ ^ m) (y - 1) (1 + X : PowerSeries ℚ) :=
    dominates_one_add_X.geometric (y - 1)
  have hdompow : Dominates (fun m => ‖y - 1‖ ^ m) (y - 1) ((1 + X : PowerSeries ℚ) ^ n) :=
    (dominates_one_add_X.pow (fun _ => zero_le_one) le_rfl
      (fun i j => (one_mul (1 : ℝ)).le) n).geometric (y - 1)
  have hdom : Dominates (fun m => ‖y - 1‖ ^ m) (y - 1) ((1 + X : PowerSeries ℚ) ^ n - 1) :=
    hdompow.sub_one ht0
  have hg0 : PowerSeries.constantCoeff ((1 + X : PowerSeries ℚ) ^ n - 1) = 0 := by simp
  obtain ⟨N, hlog⟩ := exists_norm_coeff_log_smul_le hc hp
  have hval1 : value (y - 1) (1 + X : PowerSeries ℚ) = y := by
    rw [value, tsum_eq_sum (s := Finset.range 2) (fun m hm => by
      rw [Finset.mem_range, not_lt] at hm
      have h1 : PowerSeries.coeff m (1 + X : PowerSeries ℚ) = 0 := by
        rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_X,
          if_neg (by omega), if_neg (by omega), add_zero]
      rw [h1, zero_smul])]
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp [PowerSeries.coeff_one, PowerSeries.coeff_X]
  have hvF : value (y - 1) ((1 + X : PowerSeries ℚ) ^ n - 1) = y ^ n - 1 := by
    rw [value_sub_one hts hdompow, value_pow htnn ht0 htmul hts hdomX n, hval1]
  calc padicLogarithm K (y ^ n)
      = value (y ^ n - 1) (PowerSeries.log ℚ) := padicLogarithm_eq_value _
    _ = ∑' d : ℕ, PowerSeries.coeff d (PowerSeries.log ℚ)
          • value (y - 1) ((1 + X : PowerSeries ℚ) ^ n - 1) ^ d := by
        rw [← hvF, value]
    _ = value (y - 1)
          (PowerSeries.subst ((1 + X : PowerSeries ℚ) ^ n - 1) (PowerSeries.log ℚ)) :=
        (value_subst htnn ht0 htmul htpoly hdom hg0 hlog).symm
    _ = value (y - 1) ((n : ℚ) • PowerSeries.log ℚ) := by
        rw [← PowerSeries.logOf_eq, formalLogOf_pow,
          ← Nat.cast_smul_eq_nsmul ℚ n (PowerSeries.log ℚ)]
    _ = (n : ℚ) • value (y - 1) (PowerSeries.log ℚ) := value_smul _ _
    _ = (n : ℚ) • padicLogarithm K y := by rw [← padicLogarithm_eq_value]

omit [CharZero K] in
include hc hp in
/-- One `p`-power step deepens a principal unit: `‖y ^ p - 1‖` is at most the larger of
`‖p‖ * ‖y - 1‖` and `‖y - 1‖ ^ p`—the binomial expansion, every middle coefficient divisible
by `p` ([Fesenko–Vostokov 2002, Chap. I, (5.7), pp.14–15][FesenkoVostokov2002], the two
regimes of `p`-powering on the unit filtration). -/
theorem norm_pow_residueChar_sub_one_le [IsUltrametricDist K] {y : K} (hy : ‖y - 1‖ ≤ 1) :
    ‖y ^ (residueCharacteristic K) - 1‖
      ≤ max (‖((residueCharacteristic K : ℕ) : K)‖ * ‖y - 1‖)
          (‖y - 1‖ ^ (residueCharacteristic K)) := by
  set p := residueCharacteristic K with hpdef
  have hexp : y ^ p - 1
      = ∑ k ∈ Finset.range p, (y - 1) ^ (k + 1) * ((p.choose (k + 1) : ℕ) : K) := by
    have h1 : y = (y - 1) + 1 := by ring
    nth_rewrite 1 [h1]
    rw [add_pow]
    simp only [one_pow, mul_one]
    rw [Finset.sum_range_succ']
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul]
    rw [add_sub_cancel_right]
  rw [hexp]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (le_max_iff.mpr (Or.inl (by positivity))) ?_
  intro k hk
  rw [Finset.mem_range] at hk
  rw [norm_mul, norm_pow]
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hk) with hkp | hkp
  · -- the top term `(y - 1) ^ p`
    have hkp' : k + 1 = p := hkp
    rw [hkp', Nat.choose_self]
    simp
  · -- a middle term: the coefficient is divisible by `p`
    obtain ⟨c, hcc⟩ := hp.dvd_choose_self (Nat.succ_ne_zero k) hkp
    have hC : ‖((p.choose (k + 1) : ℕ) : K)‖ ≤ ‖((p : ℕ) : K)‖ := by
      rw [hcc]
      push_cast
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (RationalIntegerValuation.norm_natCast_le_one hc c)
    refine le_max_of_le_left ?_
    rw [mul_comm (‖((p : ℕ) : K)‖) _]
    exact mul_le_mul (pow_le_of_le_one (norm_nonneg _) hy (by omega)) hC (norm_nonneg _)
      (norm_nonneg _)

/-- The arithmetic behind the deep-pair estimate: if `p ^ v ≤ m` with `v ≥ 1` and `m ≥ 2`,
then `(p - 1) * (v - 1) ≤ m - 2`. -/
private theorem sub_one_mul_padicVal_le {p v m : ℕ} (hp2 : 2 ≤ p) (hv : 1 ≤ v)
    (hm : p ^ v ≤ m) (hm2 : 2 ≤ m) : (p - 1) * (v - 1) ≤ m - 2 := by
  have h2v : v ≤ 2 ^ (v - 1) := by
    have := Nat.lt_two_pow_self (n := v - 1)
    omega
  have hpv : 2 ^ (v - 1) ≤ p ^ (v - 1) := Nat.pow_le_pow_left hp2 _
  have hvp : v * p ≤ p ^ v := by
    calc v * p ≤ p ^ (v - 1) * p := Nat.mul_le_mul_right p (le_trans h2v hpv)
      _ = p ^ v := by rw [← pow_succ]; congr 1; omega
  have hvpm : v * p ≤ m := le_trans hvp hm
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 2 := ⟨p - 2, by omega⟩
  obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
  have e1 : p' + 2 - 1 = p' + 1 := by omega
  have e2 : v' + 1 - 1 = v' := by omega
  rw [e1, e2]
  have hx : (p' + 1) * v' + 2 ≤ (v' + 1) * (p' + 2) := by nlinarith
  omega

include hc hp in
/-- **The deep-pair estimate**: for `y`, `z` within `ρ` of `1`, with `ρ ^ (p - 1) ≤ ‖p‖`, the
additivity deviation `log (y * z) - log y - log z` has norm at most `ρ ^ 2 / ‖p‖`. The `d = 1`
term of the deviation series is exactly `(y - 1)(z - 1)`; every deeper term pays `ρ` per
degree and recovers at most `‖p‖⁻¹` per power of `p` in its denominator, and the hypothesis
prices the trade. -/
theorem norm_log_mul_sub_le [IsUltrametricDist K] [CompleteSpace K] {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1)
    (hρπ : ρ ^ (residueCharacteristic K - 1) ≤ ‖((residueCharacteristic K : ℕ) : K)‖)
    {y z : K} (hy : ‖y - 1‖ ≤ ρ) (hz : ‖z - 1‖ ≤ ρ) :
    ‖padicLogarithm K (y * z) - padicLogarithm K y - padicLogarithm K z‖
      ≤ ρ ^ 2 / ‖((residueCharacteristic K : ℕ) : K)‖ := by
  set p := residueCharacteristic K with hpdef
  set π : ℝ := ‖((p : ℕ) : K)‖ with hπdef
  have hπ0 : (0 : ℝ) < π := by
    rw [hπdef, norm_pos_iff]
    exact_mod_cast hp.ne_zero
  have hπle1 : π ≤ 1 := by
    rw [hπdef]
    exact RationalIntegerValuation.norm_natCast_le_one hc p
  have hyz1 : ‖y * z - 1‖ ≤ ρ := by
    have h1 : y * z - 1 = (y - 1) + (z - 1) + (y - 1) * (z - 1) := by ring
    rw [h1]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le
      (le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le hy hz)) ?_)
    rw [norm_mul]
    calc ‖y - 1‖ * ‖z - 1‖ ≤ ρ * 1 :=
          mul_le_mul hy (le_trans hz hρ1.le) (norm_nonneg _) hρ0.le
      _ = ρ := mul_one ρ
  have hsyz : Summable fun d : ℕ =>
      PowerSeries.coeff d (PowerSeries.log ℚ) • (y * z - 1) ^ d :=
    (summable_norm_logSeries hc hp (lt_of_le_of_lt hyz1 hρ1)).of_norm
  have hsy : Summable fun d : ℕ => PowerSeries.coeff d (PowerSeries.log ℚ) • (y - 1) ^ d :=
    (summable_norm_logSeries hc hp (lt_of_le_of_lt hy hρ1)).of_norm
  have hsz : Summable fun d : ℕ => PowerSeries.coeff d (PowerSeries.log ℚ) • (z - 1) ^ d :=
    (summable_norm_logSeries hc hp (lt_of_le_of_lt hz hρ1)).of_norm
  have hD : padicLogarithm K (y * z) - padicLogarithm K y - padicLogarithm K z
      = ∑' d : ℕ, PowerSeries.coeff d (PowerSeries.log ℚ)
          • ((y * z - 1) ^ d - (y - 1) ^ d - (z - 1) ^ d) := by
    rw [padicLogarithm_eq_value (y * z), padicLogarithm_eq_value y, padicLogarithm_eq_value z,
      PowerSeriesCompositionValue.value, PowerSeriesCompositionValue.value,
      PowerSeriesCompositionValue.value, ← hsyz.tsum_sub hsy, ← (hsyz.sub hsy).tsum_sub hsz]
    exact tsum_congr fun d => by rw [← smul_sub, ← smul_sub]
  rw [hD]
  refine le_trans (IsUltrametricDist.norm_tsum_le _) (ciSup_le fun d => ?_)
  have hthree : ∀ X Y Z : K, ‖X - Y - Z‖ ≤ max ‖X‖ (max ‖Y‖ ‖Z‖) := fun X Y Z => by
    rw [sub_sub, sub_eq_add_neg]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le_max le_rfl ?_)
    rw [norm_neg]
    exact IsUltrametricDist.norm_add_le_max _ _
  rcases d with _ | d
  · have h0 : PowerSeries.coeff 0 (PowerSeries.log ℚ) = 0 := by
      simp [PowerSeries.coeff_log]
    rw [h0, zero_smul, norm_zero]
    exact div_nonneg (by positivity) hπ0.le
  rcases d with _ | d
  · -- degree one: the deviation is exactly `(y - 1)(z - 1)`
    have hc1 : PowerSeries.coeff 1 (PowerSeries.log ℚ) = 1 := by
      rw [PowerSeries.coeff_log]
      norm_num
    have h1 : (y * z - 1) ^ 1 - (y - 1) ^ 1 - (z - 1) ^ 1 = (y - 1) * (z - 1) := by ring
    rw [hc1, one_smul, h1, norm_mul]
    calc ‖y - 1‖ * ‖z - 1‖ ≤ ρ * ρ := mul_le_mul hy hz (norm_nonneg _) hρ0.le
      _ = ρ ^ 2 := (sq ρ).symm
      _ ≤ ρ ^ 2 / π := (le_div_iff₀ hπ0).mpr (mul_le_of_le_one_right (by positivity) hπle1)
  · -- degree at least two
    set m := d + 2 with hmdef
    have hm0 : m ≠ 0 := by omega
    have hpows : ‖(y * z - 1) ^ m - (y - 1) ^ m - (z - 1) ^ m‖ ≤ ρ ^ m := by
      refine le_trans (hthree _ _ _) (max_le ?_ (max_le ?_ ?_)) <;>
        rw [norm_pow] <;> exact pow_le_pow_left₀ (norm_nonneg _) (by assumption) m
    rw [norm_rat_smul, norm_coeff_log_smul_one hm0,
      RationalIntegerValuation.norm_natCast_eq_pow hc hp m hm0, ← hpdef, ← hπdef]
    set v := padicValNat p m with hvdef
    rcases Nat.eq_zero_or_pos v with hv0 | hv1
    · rw [hv0, pow_zero, inv_one, one_mul]
      calc ‖(y * z - 1) ^ m - (y - 1) ^ m - (z - 1) ^ m‖ ≤ ρ ^ m := hpows
        _ ≤ ρ ^ 2 := pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)
        _ ≤ ρ ^ 2 / π :=
            (le_div_iff₀ hπ0).mpr (mul_le_of_le_one_right (by positivity) hπle1)
    · have hpvm : p ^ v ≤ m := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
      have harith : (p - 1) * (v - 1) ≤ m - 2 :=
        sub_one_mul_padicVal_le hp.two_le hv1 hpvm (by omega)
      have hkey : ρ ^ (m - 2) ≤ π ^ (v - 1) :=
        calc ρ ^ (m - 2) ≤ ρ ^ ((p - 1) * (v - 1)) :=
              pow_le_pow_of_le_one hρ0.le hρ1.le harith
          _ = (ρ ^ (p - 1)) ^ (v - 1) := pow_mul ρ (p - 1) (v - 1)
          _ ≤ π ^ (v - 1) := pow_le_pow_left₀ (by positivity) hρπ _
      calc (π ^ v)⁻¹ * ‖(y * z - 1) ^ m - (y - 1) ^ m - (z - 1) ^ m‖
          ≤ (π ^ v)⁻¹ * ρ ^ m :=
            mul_le_mul_of_nonneg_left hpows (by positivity)
        _ = ρ ^ m / π ^ v := inv_mul_eq_div _ _
        _ ≤ ρ ^ 2 / π := by
            rw [div_le_div_iff₀ (by positivity) hπ0]
            calc ρ ^ m * π = ρ ^ 2 * ρ ^ (m - 2) * π := by
                  rw [← pow_add, show 2 + (m - 2) = m from by omega]
              _ ≤ ρ ^ 2 * π ^ (v - 1) * π := by
                  refine mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hkey (by positivity)) hπ0.le
              _ = ρ ^ 2 * π ^ v := by
                  rw [mul_assoc, ← pow_succ, show v - 1 + 1 = v from by omega]

end Normed

/-- On principal units the p-adic logarithm turns multiplication into addition:
`log (u * v) = log u + log v` for `u`, `v` in the first higher unit group
([Koblitz 1984, Chap. IV, §1, p.80][Koblitz1984];
[Fesenko–Vostokov 2002, Chap. VI, (1.2) and (1.5), pp.208, 212][FesenkoVostokov2002]). -/
theorem log_mul (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (u v : Kˣ) (hu : u ∈ higherUnitGroup K 1)
    (hv : v ∈ higherUnitGroup K 1) :
    padicLogarithm K ((u : K) * v) = padicLogarithm K (u : K) + padicLogarithm K (v : K) := by
  have hp : (residueCharacteristic K).Prime := residueCharacteristic_prime K
  -- Rebuild the normed structure; its topology is the given one.
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  haveI : CompleteSpace K := inferInstance
  haveI : IsUltrametricDist K := inferInstance
  have hc : ∀ x : K, ‖x‖ ≤ 1 ↔ valuation K x ≤ 1 := fun x => Valued.toNormedField.norm_le_one_iff
  -- membership at level one puts a unit inside the open unit ball around `1`
  have hnorm1 : ∀ w : Kˣ, w ∈ higherUnitGroup K 1 → ‖(w : K) - 1‖ < 1 := by
    intro w hw
    obtain ⟨yy, hyy⟩ := hw
    have h1 : ((yy : ↥𝒪[K]) : K) = (w : K) - 1 := by rw [← hyy]; ring
    rw [norm_lt_one_iff_valuation_lt_one hc, ← h1]
    exact valuation_lt_one_of_mem_maximalIdeal _ (Ideal.pow_le_self one_ne_zero yy.2)
  have hyu := hnorm1 u hu
  have hyv := hnorm1 v hv
  have hyuv : ‖(u : K) * (v : K) - 1‖ < 1 := by
    have := hnorm1 (u * v) (mul_mem hu hv)
    rwa [Units.val_mul] at this
  set p := residueCharacteristic K with hpdef
  set π : ℝ := ‖((p : ℕ) : K)‖ with hπdef
  have hπ0 : (0 : ℝ) < π := by
    rw [hπdef, norm_pos_iff]
    exact_mod_cast hp.ne_zero
  have hπ1 : π < 1 := by
    rw [hπdef, norm_lt_one_iff_valuation_lt_one hc]
    exact valuation_residueCharacteristic_lt_one
  -- the deviation whose vanishing is the claim
  set D := padicLogarithm K ((u : K) * v) - padicLogarithm K (u : K) - padicLogarithm K (v : K)
    with hDdef
  suffices hD0 : D = 0 by
    rw [hDdef] at hD0
    linear_combination hD0
  -- phase one: `p`-powering strictly deepens, with ratio `s`
  set s : ℝ := max π (max ‖(u : K) - 1‖ ‖(v : K) - 1‖) with hsdef
  have hs1 : s < 1 := max_lt hπ1 (max_lt hyu hyv)
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le hπ0 (le_max_left _ _)
  have hstep : ∀ (w : K) (ρ' : ℝ), ‖w - 1‖ ≤ ρ' → ρ' ≤ 1 →
      ‖w ^ p - 1‖ ≤ max (π * ρ') (ρ' ^ p) := by
    intro w ρ' hw hρ'
    refine le_trans (norm_pow_residueChar_sub_one_le hc hp (le_trans hw hρ')) ?_
    exact max_le_max (mul_le_mul_of_nonneg_left hw hπ0.le)
      (pow_le_pow_left₀ (norm_nonneg _) hw p)
  have hphaseA : ∀ k : ℕ, ‖(u : K) ^ p ^ k - 1‖ ≤ s ^ (k + 1)
      ∧ ‖(v : K) ^ p ^ k - 1‖ ≤ s ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
        simp only [pow_zero, pow_one, zero_add]
        exact ⟨le_trans (le_max_left _ _) (le_max_right _ _),
          le_trans (le_max_right _ _) (le_max_right _ _)⟩
    | succ k ih =>
        have hs1' : s ^ (k + 1) ≤ 1 := pow_le_one₀ hs0.le hs1.le
        have hnext : ∀ w : K, ‖w - 1‖ ≤ s ^ (k + 1) → ‖w ^ p - 1‖ ≤ s ^ (k + 1 + 1) := by
          intro w hw
          refine le_trans (hstep w (s ^ (k + 1)) hw hs1') (max_le ?_ ?_)
          · calc π * s ^ (k + 1) ≤ s * s ^ (k + 1) :=
                  mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hs0.le _)
              _ = s ^ (k + 1 + 1) := by rw [pow_succ]; ring
          · rw [← pow_mul]
            refine pow_le_pow_of_le_one hs0.le hs1.le ?_
            have := hp.two_le
            nlinarith
        refine ⟨?_, ?_⟩
        · rw [pow_succ, pow_mul]
          exact hnext _ ih.1
        · rw [pow_succ, pow_mul]
          exact hnext _ ih.2
  -- a depth from which every further step gains a full factor of `π`
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, s ^ k₀ < π := exists_pow_lt_of_lt_one hπ0 hs1
  set ρ₀ : ℝ := s ^ (k₀ + 1) with hρ₀def
  have hρ₀0 : (0 : ℝ) < ρ₀ := by positivity
  have hρ₀π : ρ₀ ≤ π := by
    rw [hρ₀def, pow_succ]
    exact le_trans (mul_le_of_le_one_right (by positivity) hs1.le) hk₀.le
  have hphaseB : ∀ j : ℕ, ‖(u : K) ^ p ^ (k₀ + j) - 1‖ ≤ π ^ j * ρ₀
      ∧ ‖(v : K) ^ p ^ (k₀ + j) - 1‖ ≤ π ^ j * ρ₀ := by
    intro j
    induction j with
    | zero =>
        simpa [hρ₀def] using hphaseA k₀
    | succ j ih =>
        have hρj1 : π ^ j * ρ₀ ≤ 1 :=
          le_trans (mul_le_of_le_one_right (by positivity) (le_trans hρ₀π hπ1.le))
            (pow_le_one₀ hπ0.le hπ1.le)
        have hρjπ : π ^ j * ρ₀ ≤ π :=
          le_trans (mul_le_mul_of_nonneg_right (pow_le_one₀ hπ0.le hπ1.le) hρ₀0.le)
            (by rw [one_mul]; exact hρ₀π)
        have hnext : ∀ w : K, ‖w - 1‖ ≤ π ^ j * ρ₀ →
            ‖w ^ p - 1‖ ≤ π ^ (j + 1) * ρ₀ := by
          intro w hw
          refine le_trans (hstep w (π ^ j * ρ₀) hw hρj1) (max_le ?_ ?_)
          · rw [pow_succ, mul_comm (π ^ j) π, mul_assoc]
          · calc (π ^ j * ρ₀) ^ p ≤ (π ^ j * ρ₀) ^ 2 :=
                  pow_le_pow_of_le_one (by positivity) hρj1 hp.two_le
              _ = (π ^ j * ρ₀) * (π ^ j * ρ₀) := sq _
              _ ≤ π * (π ^ j * ρ₀) :=
                  mul_le_mul_of_nonneg_right hρjπ (by positivity)
              _ = π ^ (j + 1) * ρ₀ := by rw [pow_succ]; ring
        refine ⟨?_, ?_⟩
        · rw [show k₀ + (j + 1) = (k₀ + j) + 1 by omega, pow_succ, pow_mul]
          exact hnext _ ih.1
        · rw [show k₀ + (j + 1) = (k₀ + j) + 1 by omega, pow_succ, pow_mul]
          exact hnext _ ih.2
  -- the deviation scales exactly by `π` per step, but shrinks like `π ^ 2`
  have hDk : ∀ k : ℕ, ‖D‖ * π ^ k
      = ‖padicLogarithm K (((u : K) * (v : K)) ^ p ^ k)
          - padicLogarithm K ((u : K) ^ p ^ k) - padicLogarithm K ((v : K) ^ p ^ k)‖ := by
    intro k
    have hsmul : ((p ^ k : ℕ) : ℚ) • D
        = padicLogarithm K (((u : K) * (v : K)) ^ p ^ k)
          - padicLogarithm K ((u : K) ^ p ^ k) - padicLogarithm K ((v : K) ^ p ^ k) := by
      rw [hDdef, smul_sub, smul_sub, ← log_pow hc hp hyuv (p ^ k), ← log_pow hc hp hyu (p ^ k),
        ← log_pow hc hp hyv (p ^ k)]
    rw [← hsmul, PowerSeriesCompositionValue.norm_rat_smul, Rat.smul_def, mul_one]
    have hcast : ‖((((p ^ k : ℕ) : ℚ)) : K)‖ = π ^ k := by
      rw [hπdef]
      push_cast
      rw [norm_pow]
    rw [hcast, mul_comm]
  have hbound : ∀ j : ℕ, ‖D‖ ≤ π ^ j * (ρ₀ ^ 2 / π / π ^ k₀) := by
    intro j
    obtain ⟨hU, hV⟩ := hphaseB j
    have hρj0 : (0 : ℝ) < π ^ j * ρ₀ := by positivity
    have hρj1 : π ^ j * ρ₀ < 1 :=
      lt_of_le_of_lt (le_trans (mul_le_mul_of_nonneg_right
        (pow_le_one₀ hπ0.le hπ1.le) hρ₀0.le) (by rw [one_mul]; exact hρ₀π)) hπ1
    have hρjπ' : (π ^ j * ρ₀) ^ (p - 1) ≤ π := by
      refine le_trans (pow_le_of_le_one hρj0.le hρj1.le ?_) ?_
      · have := hp.two_le; omega
      · exact le_trans (mul_le_mul_of_nonneg_right (pow_le_one₀ hπ0.le hπ1.le) hρ₀0.le)
          (by rw [one_mul]; exact hρ₀π)
    have hdeep := norm_log_mul_sub_le hc hp hρj0 hρj1 hρjπ'
      (y := (u : K) ^ p ^ (k₀ + j)) (z := (v : K) ^ p ^ (k₀ + j)) hU hV
    rw [← mul_pow, ← hpdef, ← hπdef, ← hDk (k₀ + j)] at hdeep
    have hπk : (0 : ℝ) < π ^ (k₀ + j) := by positivity
    rw [← le_div_iff₀ hπk] at hdeep
    refine le_trans hdeep (le_of_eq ?_)
    field_simp
    ring
  have htend : Filter.Tendsto (fun j : ℕ => π ^ j * (ρ₀ ^ 2 / π / π ^ k₀))
      Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hπ0.le hπ1).mul_const (ρ₀ ^ 2 / π / π ^ k₀)
  have hle0 : ‖D‖ ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds htend (Filter.Eventually.of_forall hbound)
  exact norm_le_zero_iff.mp hle0

end PadicLogarithm

end Atlas.Knowledge
