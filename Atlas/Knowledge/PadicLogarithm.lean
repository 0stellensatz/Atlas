import Mathlib
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.IsMixedCharLocalField
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
  Claim recorded ahead of its proof.

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
only polynomially, so the real series of norms converges by comparison with a
polynomial-times-geometric one. The polynomial bound is the arithmetic core, and it is sharp
enough to be cheap: writing `m = p ^ k * m'` with `m'` prime to `p` gives `‖(m : K)‖ = ‖(p : K)‖ ^
k`, and choosing `N` with `‖(p : K)‖⁻¹ ≤ p ^ N` turns `p ^ k ≤ m` into `‖(m : K)‖⁻¹ ≤ m ^ N`. No
normalization of the valuation is needed for this—only that some rank-one hom exists—which is why
the route survives the fact that `Valuation.RankOne.hom` is fixed by an arbitrary choice.

The statements mention no norm and no uniformity: `K` carries its valuative relation and the
topology of the local-field class, nothing more, and the normed structure is rebuilt inside the
proof from the local-field hypotheses—the same discipline as
`Atlas.Knowledge.IntegralClosureDVR`, and for the same reason, that the auxiliary uniformity must
not escape into the statement. `Summable` depends only on the topology, and the topology the
rebuilt norm induces is the given one definitionally, so the conclusion is about the field as the
layer carries it. The scaffolding lemmas below stay `private`: they are the arithmetic of a
rational integer's valuation, and until a second item needs them they are this file's business.

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

section Scaffolding

variable {K : Type*} [Field K] [ValuativeRel K]

set_option synthInstance.maxHeartbeats 80000 in
-- `IsLocalRing ↥𝒪[K]`, which the residue-field rewrites go through, does not fit the default
-- instance budget.
private theorem isUnit_natCast_iff (m : ℕ) :
    IsUnit (m : ↥𝒪[K]) ↔ ¬ (residueCharacteristic K) ∣ m := by
  haveI := ringChar.charP 𝓀[K]
  rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, map_natCast,
    CharP.cast_eq_zero_iff 𝓀[K] (ringChar 𝓀[K]) m]
  rfl

private theorem valuation_natCast_eq_one (m : ℕ) (hm : ¬ (residueCharacteristic K) ∣ m) :
    valuation K (m : K) = 1 := by
  have hu : IsUnit (m : ↥𝒪[K]) := (isUnit_natCast_iff m).mpr hm
  rw [(Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one] at hu
  simpa using hu

private theorem valuation_residueCharacteristic_lt_one :
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
private theorem valuation_lt_one_of_mem_maximalIdeal (y : ↥𝒪[K]) (hy : y ∈ 𝓂[K]) :
    valuation K (y : K) < 1 := by
  have hnu : ¬ IsUnit y := by rw [← IsLocalRing.notMem_maximalIdeal, not_not]; exact hy
  rw [(Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one] at hnu
  exact lt_of_le_of_ne ((Valuation.integer.integers (valuation K)).map_le_one _) hnu

end Scaffolding

/-- Split the `p`-part off a nonzero natural number: `m = p ^ padicValNat p m * m'` with `m'`
prime to `p`. -/
private theorem exists_eq_pow_padicValNat_mul {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : m ≠ 0) :
    ∃ m', ¬ p ∣ m' ∧ m = p ^ padicValNat p m * m' := by
  obtain ⟨m', hm'⟩ : p ^ padicValNat p m ∣ m := pow_padicValNat_dvd
  refine ⟨m', ?_, hm'⟩
  intro ⟨c, hc⟩
  exact pow_succ_padicValNat_not_dvd hm ⟨c, by rw [pow_succ, mul_assoc, ← hc, ← hm']⟩

section Normed

variable {K : Type*} [NormedField K] [CharZero K] [ValuativeRel K]
  (hc : ∀ x : K, ‖x‖ ≤ 1 ↔ valuation K x ≤ 1)

include hc

omit [CharZero K] in
private theorem one_lt_norm_iff_one_lt_valuation (x : K) : 1 < ‖x‖ ↔ 1 < valuation K x := by
  simpa using not_congr (hc x)

omit [CharZero K] in
private theorem norm_lt_one_iff_valuation_lt_one (x : K) : ‖x‖ < 1 ↔ valuation K x < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h1 : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
    have h2 : (0 : ValueGroupWithZero K) < valuation K x := zero_lt_iff.mpr (by simpa using hx)
    have e1 : ‖x‖ < 1 ↔ 1 < ‖x‖⁻¹ := by rw [one_lt_inv_iff₀]; simp [h1]
    have e2 : valuation K x < 1 ↔ 1 < (valuation K x)⁻¹ := by rw [one_lt_inv_iff₀]; simp [h2]
    rw [e1, e2, ← norm_inv, ← map_inv₀]
    exact one_lt_norm_iff_one_lt_valuation hc x⁻¹

omit [CharZero K] in
private theorem norm_eq_one_iff_valuation_eq_one (x : K) : ‖x‖ = 1 ↔ valuation K x = 1 := by
  constructor
  · intro h
    exact le_antisymm ((hc x).mp h.le)
      (not_lt.mp fun hlt => absurd ((norm_lt_one_iff_valuation_lt_one hc x).mpr hlt) (by simp [h]))
  · intro h
    exact le_antisymm ((hc x).mpr h.le)
      (not_lt.mp fun hlt => absurd ((norm_lt_one_iff_valuation_lt_one hc x).mp hlt) (by simp [h]))

variable (hp : (residueCharacteristic K).Prime)

include hp

omit [CharZero K] in
private theorem norm_natCast_eq_pow (m : ℕ) (hm : m ≠ 0) :
    ‖(m : K)‖ =
      ‖((residueCharacteristic K : ℕ) : K)‖ ^ padicValNat (residueCharacteristic K) m := by
  haveI : Fact (residueCharacteristic K).Prime := ⟨hp⟩
  obtain ⟨m', hm'dvd, hm'⟩ := exists_eq_pow_padicValNat_mul (p := residueCharacteristic K) hm
  nth_rewrite 1 [hm']
  push_cast
  rw [norm_mul, norm_pow,
    (norm_eq_one_iff_valuation_eq_one hc _).mpr (valuation_natCast_eq_one m' hm'dvd), mul_one]

/-- The reciprocal norm of a rational integer is bounded by a fixed power of it: the `p`-adic
valuation of `m` is at most `Nat.log p m`, so `‖(m : K)‖⁻¹` grows only polynomially. -/
private theorem exists_norm_natCast_inv_le :
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

end Normed

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

/-- On principal units the p-adic logarithm turns multiplication into addition:
`log (u * v) = log u + log v` for `u`, `v` in the first higher unit group. Claim recorded ahead
of its proof ([Koblitz 1984, Chap. IV, §1, p.80][Koblitz1984];
[Fesenko–Vostokov 2002, Chap. VI, (1.2) and (1.5), pp.208, 212][FesenkoVostokov2002]). -/
theorem log_mul (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (u v : Kˣ) (hu : u ∈ higherUnitGroup K 1)
    (hv : v ∈ higherUnitGroup K 1) :
    padicLogarithm K ((u : K) * v) = padicLogarithm K (u : K) + padicLogarithm K (v : K) := by
  sorry

end PadicLogarithm

end Atlas.Knowledge
