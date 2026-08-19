import Mathlib
import Atlas.Knowledge.AbsoluteRamificationIndex
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.RationalIntegerValuation
import Atlas.Knowledge.ResidueCharacteristic

/-!
# convergence threshold of the p-adic exponential

The exponential series `∑ xⁿ / n!` on a mixed-characteristic local field converges exactly above
the threshold `e / (p - 1)`: for an integer `x`, the series is summable if and only if the
valuation of `x` exceeds `e / (p - 1)`, that is, if and only if `x` lies in
`𝓂 ^ (⌊e / (p - 1)⌋ + 1)`. The threshold is the point of contact between the exponential and the
jump-set arithmetic of the layer: `p`-powering of the higher unit filtration
`Atlas.Knowledge.HigherUnitGroup` moves by `i ↦ p * i` at and below `e / (p - 1)` and by the
stable `i ↦ i + e` above it, and the `e'` of the shift `Atlas.Knowledge.ShiftRhoEP` in the sense
of `Atlas.Knowledge.ShiftEPrime` is the ceiling `⌈e / (p - 1)⌉`—the threshold itself exactly when
`p - 1` divides `e`, which is the standing hypothesis of the source's §5 and the case its
`e'_ρ = e / (p - 1)` is printed in. Above the threshold the exponential inverts the filtration
into its additive counterpart, which is `Atlas.Knowledge.PadicExpIsomorphism`.

## Main statements

* `padicExpConvergence` — summability of the exponential series at an integer `x` is equivalent
  to membership of `x` in the ideal power one past the threshold.

## Implementation notes

The series is spelled `(n ! : ℚ)⁻¹ • x ^ n`, which is term-by-term the application of Mathlib's
`NormedSpace.expSeries ℚ K` (by `NormedSpace.expSeries_apply_eq`), so the claim is about the
series whose sum is `NormedSpace.exp`—the layer introduces no second exponential. The threshold
index is the floor division `e / (p - 1) + 1` of the invariants
`Atlas.Knowledge.AbsoluteRamificationIndex` and `Atlas.Knowledge.ResidueCharacteristic`: an
integer valuation exceeds the rational `e / (p - 1)` exactly when it reaches `⌊e / (p - 1)⌋ + 1`,
so the ideal membership carries the sharp bound without rational arithmetic. The statement
quantifies over integers of `K` only: off the integers the valuation is negative and divergence
is subsumed by the classical statement, while the filtration the layer cares about lives inside
`𝒪[K]`.

Both directions run on one computation. Writing `x = u * ϖ ^ w` for a uniformizer `ϖ`, the term
at `n` has norm `c ^ (w * n) / c ^ (e * v_p (n !))` with `c = ‖ϖ‖ < 1`, and the whole question is
whether the exponent `w * n - e * v_p (n !)` runs to infinity. Legendre's bound
`(p - 1) * v_p (n !) ≤ n` turns that exponent into at least `n / (p - 1)` once
`(p - 1) * w ≥ e + 1`, which is exactly the threshold, so the terms are dominated by a geometric
series and *absolute* convergence settles the "if". Below the threshold the same computation run
along `n = p ^ j`, where `(p - 1) * v_p ((p ^ j)!) + 1 = p ^ j` exactly, pins the exponent below
`e / (p - 1)`; the terms then stay bounded away from zero along a subsequence, and
`Summable.tendsto_atTop_zero` settles the "only if". Neither direction needs an ultrametric
summability criterion, which Mathlib does not have at this revision.

The identification `p • 𝒪[K] = 𝓂[K] ^ e` is what lets `e` be read as a valuation at all; it is
`Atlas.Knowledge.AbsoluteRamificationIndex.span_residueCharacteristic_eq_maximalIdeal_pow`, and
without it the threshold in the statement would be about a length rather than about the
ramification. The statements mention no norm and no uniformity: the normed structure is rebuilt
inside the proof from the local-field hypotheses, as in `Atlas.Knowledge.IntegralClosureDVR`.

## References

* [FesenkoVostokov2002] I. B. Fesenko, S. V. Vostokov, *Local fields and their extensions*,
  Translations of Mathematical Monographs **121**, American Mathematical Society, second
  edition, 2002.
* [Koblitz1984] N. Koblitz, *p-adic numbers, p-adic analysis, and zeta-functions*, Graduate
  Texts in Mathematics **58**, Springer New York, 1984.
* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

open ValuativeRel Atlas.Knowledge.RationalIntegerValuation
open scoped Nat

namespace Atlas.Knowledge

namespace PadicExpConvergence

section Arith

variable {p : ℕ} [hp : Fact p.Prime]

/-- Legendre's bound: `(p - 1) * v_p (n !) ≤ n`. -/
private theorem factorial_bound (n : ℕ) : (p - 1) * padicValNat p (n !) ≤ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · exact (sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hn).le

/-- The valuation of `(p ^ j)!` is exact: `(p - 1) * v_p ((p ^ j)!) + 1 = p ^ j`, the geometric
sum `1 + p + ⋯ + p ^ (j - 1)` written without subtraction. -/
private theorem factorial_pow (j : ℕ) : (p - 1) * padicValNat p ((p ^ j)!) + 1 = p ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hpow : p ^ (j + 1) = p * p ^ j := by ring
      rw [hpow, padicValNat_factorial_mul, Nat.mul_add]
      have h1 : 1 ≤ p ^ j := Nat.one_le_pow _ _ hp.out.pos
      have h2 : 2 ≤ p := hp.out.two_le
      have h3 : p * p ^ j = p ^ j + (p - 1) * p ^ j := by
        cases p with
        | zero => omega
        | succ q => simp; ring
      omega

omit hp in
/-- Above the threshold, `(p - 1) * w` clears `e`. -/
private theorem div_bound {e w : ℕ} (hp2 : 2 ≤ p) (h : e / (p - 1) + 1 ≤ w) :
    e + 1 ≤ (p - 1) * w := by
  have := Nat.div_add_mod e (p - 1)
  have := Nat.mod_lt e (show 0 < p - 1 by omega)
  nlinarith [Nat.mul_le_mul_left (p - 1) h]

omit hp in
/-- Below the threshold, `(p - 1) * w` does not. -/
private theorem div_bound' {e w : ℕ} (h : w < e / (p - 1) + 1) : (p - 1) * w ≤ e := by
  have h1 : w ≤ e / (p - 1) := by omega
  calc (p - 1) * w ≤ (p - 1) * (e / (p - 1)) := Nat.mul_le_mul_left _ h1
    _ = e / (p - 1) * (p - 1) := Nat.mul_comm _ _
    _ ≤ e := Nat.div_mul_le_self e (p - 1)

end Arith

section Ideal

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

set_option synthInstance.maxHeartbeats 80000 in
-- The ideal arithmetic on `↥𝒪[K]` does not fit the default instance budget.
/-- Membership of `u * ϖ ^ w` in a power of the maximal ideal is a comparison of exponents. -/
private theorem mem_pow_iff {ϖ : ↥𝒪[K]} (hϖ : Irreducible ϖ) {u : (↥𝒪[K])ˣ} {w k : ℕ} :
    ((u : ↥𝒪[K]) * ϖ ^ w) ∈ (𝓂[K] ^ k : Ideal ↥𝒪[K]) ↔ k ≤ w := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    IsUnit.dvd_mul_left u.isUnit]
  exact pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit

end Ideal

end PadicExpConvergence

set_option synthInstance.maxHeartbeats 80000 in
-- The ideal arithmetic on `↥𝒪[K]` does not fit the default instance budget.
open PadicExpConvergence in
/-- The exponential series `∑ xⁿ / n!` at an integer `x` of a mixed-characteristic local field
is summable exactly above the threshold `e / (p - 1)`: summability is equivalent to membership
of `x` in `𝓂 ^ (e / (p - 1) + 1)`, the floor division marking the least integer valuation
exceeding the threshold. The `e'` of the shift `ρ_ep` of `Atlas.Knowledge.ShiftRhoEP` is
`⌈e / (p - 1)⌉`, the threshold itself exactly when `p - 1` divides `e`
([Fesenko–Vostokov 2002, Chap. VI, (1.4), pp.211–212][FesenkoVostokov2002];
[Koblitz 1984, Chap. IV, §1, p.79][Koblitz1984]; [Pagano 2022, §5, p.442][Pagano2022]). -/
theorem padicExpConvergence (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (x : ↥𝒪[K]) :
    Summable (fun n : ℕ => (n ! : ℚ)⁻¹ • ((x : K) ^ n)) ↔
      x ∈ (𝓂[K] ^ (absoluteRamificationIndex K / (residueCharacteristic K - 1) + 1) :
        Ideal ↥𝒪[K]) := by
  haveI : Fact (residueCharacteristic K).Prime := ⟨residueCharacteristic_prime K⟩
  have hp2 : 2 ≤ residueCharacteristic K := (residueCharacteristic_prime K).two_le
  -- Rebuild the normed structure; its topology is the given one.
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  haveI : CompleteSpace K := inferInstance
  have hc : ∀ y : K, ‖y‖ ≤ 1 ↔ valuation K y ≤ 1 := fun y => Valued.toNormedField.norm_le_one_iff
  have hunit : ∀ v : (↥𝒪[K])ˣ, ‖((v : ↥𝒪[K]) : K)‖ = 1 := by
    intro v
    refine (norm_eq_one_iff_valuation_eq_one hc _).mpr ?_
    have h2 : valuation K ((algebraMap (↥𝒪[K]) K) (v : ↥𝒪[K])) = 1 :=
      (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mp v.isUnit
    exact h2
  -- The degenerate point is in every ideal power and its series has finite support.
  rcases eq_or_ne x 0 with rfl | hx0
  · refine ⟨fun _ => Ideal.zero_mem _, fun _ => summable_of_ne_finset_zero (s := {0}) ?_⟩
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [zero_pow hn]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (↥𝒪[K])
  obtain ⟨w, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  set c : ℝ := ‖((ϖ : ↥𝒪[K]) : K)‖ with hcdef
  have hc0 : 0 < c := by
    rw [hcdef, norm_pos_iff]
    simpa using hϖ.ne_zero
  have hc1 : c < 1 := by
    rw [hcdef, norm_lt_one_iff_valuation_lt_one hc]
    exact valuation_lt_one_of_mem_maximalIdeal _
      (by rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ)
  -- the norm of `x`, of `p`, and of `n !`
  have hxnorm : ‖(x : K)‖ = c ^ w := by
    rw [hu]
    push_cast
    rw [norm_mul, norm_pow, hunit u, one_mul]
  have hpnorm : ‖((residueCharacteristic K : ℕ) : K)‖ = c ^ absoluteRamificationIndex K := by
    obtain ⟨v, hv⟩ : Associated ((residueCharacteristic K : ℕ) : ↥𝒪[K])
        (ϖ ^ absoluteRamificationIndex K) := by
      rw [← Ideal.span_singleton_eq_span_singleton, ← Ideal.span_singleton_pow,
        ← hϖ.maximalIdeal_eq]
      exact span_residueCharacteristic_eq_maximalIdeal_pow K
    have := congrArg (fun z : ↥𝒪[K] => ‖(z : K)‖) hv
    simpa [hunit v] using this
  have hfact : ∀ n : ℕ, ‖((n ! : ℕ) : K)‖
      = c ^ (absoluteRamificationIndex K * padicValNat (residueCharacteristic K) (n !)) := by
    intro n
    rw [norm_natCast_eq_pow hc (residueCharacteristic_prime K) _ n.factorial_ne_zero, hpnorm,
      ← pow_mul]
  have hterm : ∀ n : ℕ, ‖(n ! : ℚ)⁻¹ • ((x : K) ^ n)‖
      = c ^ (w * n) / c ^ (absoluteRamificationIndex K *
          padicValNat (residueCharacteristic K) (n !)) := by
    intro n
    rw [Rat.smul_def, norm_mul, norm_pow, hxnorm, ← pow_mul, div_eq_mul_inv, mul_comm]
    congr 1
    push_cast
    rw [norm_inv, hfact n]
  have hmem : ∀ k : ℕ, x ∈ (𝓂[K] ^ k : Ideal ↥𝒪[K]) ↔ k ≤ w := by
    intro k; rw [hu]; exact mem_pow_iff hϖ
  rw [hmem]
  set D : ℕ := residueCharacteristic K - 1 with hDdef
  set e : ℕ := absoluteRamificationIndex K with hedef
  set v : ℕ → ℕ := fun n => padicValNat (residueCharacteristic K) (n !) with hvdef
  set d : ℝ := (D : ℝ) with hddef
  have hd0 : 0 < d := by rw [hddef, hDdef]; exact_mod_cast Nat.sub_pos_of_lt (by omega)
  have hrpow : ∀ n : ℕ, ‖(n ! : ℚ)⁻¹ • ((x : K) ^ n)‖
      = c ^ (((w * n : ℕ) : ℝ) - ((e * v n : ℕ) : ℝ)) := by
    intro n
    rw [hterm n, Real.rpow_sub hc0, Real.rpow_natCast, Real.rpow_natCast]
  constructor
  · -- Summable forces the threshold: below it the terms along `n = p ^ j` do not vanish.
    intro hsum
    by_contra hlt
    push Not at hlt
    have hdw : D * w ≤ e := div_bound' hlt
    have hB : (0 : ℝ) < c ^ ((e : ℝ) / d) := Real.rpow_pos_of_pos hc0 _
    have hge : ∀ j : ℕ, c ^ ((e : ℝ) / d) ≤
        ‖((residueCharacteristic K ^ j)! : ℚ)⁻¹ • ((x : K) ^ (residueCharacteristic K ^ j))‖ := by
      intro j
      rw [hrpow]
      refine Real.rpow_le_rpow_of_exponent_ge hc0 hc1.le ?_
      have hnat : D * (w * residueCharacteristic K ^ j)
          ≤ D * (e * v (residueCharacteristic K ^ j)) + e := by
        have hfp : D * v (residueCharacteristic K ^ j) + 1 = residueCharacteristic K ^ j :=
          factorial_pow j
        calc D * (w * residueCharacteristic K ^ j)
            = residueCharacteristic K ^ j * (D * w) := by ring
          _ ≤ residueCharacteristic K ^ j * e := Nat.mul_le_mul_left _ hdw
          _ = e * (D * v (residueCharacteristic K ^ j)) + e := by
              conv_lhs => rw [← hfp]
              ring
          _ = D * (e * v (residueCharacteristic K ^ j)) + e := by ring
      have hcast : d * ((w * residueCharacteristic K ^ j : ℕ) : ℝ)
          ≤ d * ((e * v (residueCharacteristic K ^ j) : ℕ) : ℝ) + (e : ℝ) := by
        rw [hddef]; exact_mod_cast hnat
      rw [le_div_iff₀ hd0, sub_mul, mul_comm _ d, mul_comm _ d]
      linarith
    have h0 : Filter.Tendsto (fun n : ℕ => ‖(n ! : ℚ)⁻¹ • ((x : K) ^ n)‖) Filter.atTop (nhds 0) :=
      by simpa using hsum.tendsto_atTop_zero.norm
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h0.eventually (gt_mem_nhds hB))
    obtain ⟨j, hj⟩ : ∃ j : ℕ, N < residueCharacteristic K ^ j :=
      pow_unbounded_of_one_lt _ (by omega)
    exact absurd (hN _ hj.le) (not_lt.mpr (hge j))
  · -- Above the threshold the terms are dominated by a geometric series.
    intro hk
    have hdw : e + 1 ≤ D * w := div_bound hp2 hk
    have hr0 : (0 : ℝ) ≤ c ^ ((1 : ℝ) / d) := Real.rpow_nonneg hc0.le _
    have hr1 : c ^ ((1 : ℝ) / d) < 1 := Real.rpow_lt_one hc0.le hc1 (by positivity)
    have hbound : ∀ n : ℕ, ‖(n ! : ℚ)⁻¹ • ((x : K) ^ n)‖ ≤ (c ^ ((1 : ℝ) / d)) ^ n := by
      intro n
      have hnat : D * (e * v n) + n ≤ D * (w * n) := by
        calc D * (e * v n) + n = e * (D * v n) + n := by ring
          _ ≤ e * n + n := Nat.add_le_add_right (Nat.mul_le_mul_left e (factorial_bound n)) n
          _ = n * (e + 1) := by ring
          _ ≤ n * (D * w) := Nat.mul_le_mul_left n hdw
          _ = D * (w * n) := by ring
      have hcast : d * ((e * v n : ℕ) : ℝ) + (n : ℝ) ≤ d * ((w * n : ℕ) : ℝ) := by
        rw [hddef]; exact_mod_cast hnat
      have hexp : (n : ℝ) / d ≤ ((w * n : ℕ) : ℝ) - ((e * v n : ℕ) : ℝ) := by
        rw [div_le_iff₀ hd0, sub_mul, mul_comm _ d, mul_comm _ d]
        linarith
      rw [hrpow n]
      calc c ^ (((w * n : ℕ) : ℝ) - ((e * v n : ℕ) : ℝ))
          ≤ c ^ ((n : ℝ) / d) := Real.rpow_le_rpow_of_exponent_ge hc0 hc1.le hexp
        _ = (c ^ ((1 : ℝ) / d)) ^ n := by
            rw [← Real.rpow_natCast (c ^ ((1 : ℝ) / d)) n, ← Real.rpow_mul hc0.le]
            ring_nf
    exact Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound
      (summable_geometric_of_lt_one hr0 hr1))

end Atlas.Knowledge
