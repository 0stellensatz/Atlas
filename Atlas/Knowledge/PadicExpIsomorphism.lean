import Mathlib
import Atlas.Knowledge.AbsoluteRamificationIndex
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.PadicExpConvergence
import Atlas.Knowledge.PadicLogarithm
import Atlas.Knowledge.ResidueCharacteristic

/-!
# exp/log isomorphism above the threshold

Above the threshold `e / (p - 1)`, the exponential and the logarithm are mutually inverse
isomorphisms between the higher unit groups and their additive counterparts: for `i` with
`(p - 1) * i > e`, the exponential maps `𝓂 ^ i` bijectively onto `U i (K)` of
`Atlas.Knowledge.HigherUnitGroup`, addition goes to multiplication, and
`Atlas.Knowledge.PadicLogarithm` inverts it in both orders. This is the level-by-level
sharpening of the classical statement that `exp` and `log` are inverse isomorphisms between
the convergence disc and its multiplicative translate, and it is what makes the deep unit
groups additive objects—the mechanism behind `Atlas.Knowledge.DeepUnitGroup` and the free-rank
computations it gates.

## Main statements

All are claims recorded ahead of their proofs.

* `padicExpIsomorphism` — the exponential is a bijection of `𝓂 ^ i` onto `U i (K)` above the
  threshold.
* `PadicExpIsomorphism.exp_add` — on the convergence ideal, the exponential turns addition
  into multiplication.
* `PadicExpIsomorphism.padicLogarithm_exp` — the logarithm inverts the exponential on the
  convergence ideal.
* `PadicExpIsomorphism.exp_padicLogarithm` — the exponential inverts the logarithm on
  `U i (K)`.

Of the four, `padicExpIsomorphism` and `PadicExpIsomorphism.exp_add` are proved; the two
inversion identities are claims recorded ahead of their proofs.

## Implementation notes

The exponential is Mathlib's `NormedSpace.exp`, whose value at `x` is the sum of the series
`∑ xⁿ / n!` through the `ℚ`-algebra structure of `K`—unique in characteristic `0`, so the
`Classical.choice` in Mathlib's definition picks the standard one—and whose convergence on the
stated domain is `Atlas.Knowledge.PadicExpConvergence`. The isomorphism is stated unbundled: a
`Set.BijOn` between the images of `𝓂 ^ i` and of `U i (K)` in `K`, plus the homomorphism
identity and the two inversion identities. A bundled `MulEquiv` would be a definition, and a
definition may not carry a `sorry`; the unbundled quadruple records the same content as claims
and lets the bundling be built downstream once the proofs land. The bijection and the log-side
inversion are per level, under the integer guard `e < (p - 1) * i`; the two identities
`exp_add` and `padicLogarithm_exp` are instead stated once, on the convergence ideal
`𝓂 ^ (e / (p - 1) + 1)` of `Atlas.Knowledge.PadicExpConvergence`, which contains every deeper
level, so their per-level forms follow by inclusion. On these domains the value of the
exponential lands on a unit because its series has first term `1` and the tail falls in the
maximal ideal, which is what membership of the value in the image of `U i (K)` encodes. No
claim is made at or below the threshold, where the series diverges and the value of
`NormedSpace.exp` is junk.

`exp_add` is the Cauchy product and nothing more. `NormedSpace.exp_eq_tsum_rat` spells the
exponential as exactly the `tsum` this layer writes, and on the convergence ideal the series is
*absolutely* summable—`Atlas.Knowledge.PadicExpConvergence.summable_norm_expSeries`, which is
the "if" half of the threshold theorem factored out for this purpose—so
`tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm` turns the product of the two sums into
a sum over antidiagonals, and what remains is the binomial identity one `n` at a time:
`(n !)⁻¹ * (n.choose i) = (i !)⁻¹ * (j !)⁻¹` for `i + j = n`, which is
`Nat.add_choose_mul_factorial_mul_factorial` cast into `K`. Nothing about the nonarchimedean
structure enters beyond the absolute summability, which is why this one claim of the four is
reachable while the two inversion identities are not: those need the functional equation of
`PowerSeries.log`, which Mathlib does not have at this revision.

`padicExpIsomorphism` does **not** need the logarithm either, which is the departure from how
the sources prove it. The two estimates of `PadicExpIsomorphism.norm_exp_estimates` carry all
three parts. `MapsTo` is `‖exp x - 1‖ = ‖x‖` plus `‖exp x‖ = 1`. `InjOn` is `exp_add` and the
same equality, which turns `exp (x - y) = 1` into `‖x - y‖ = 0`. `SurjOn` is successive
approximation on the filtration: given `u ∈ U i (K)` and an approximant `z` with
`‖exp z - u‖ ≤ c ^ (i + k)`, put `T = u⁻¹ * exp z - 1` and replace `z` by `z - T`; the algebra
collapses—`exp z - u * exp T = -u * (exp T - 1 - T)`, because `u * T` is exactly `exp z - u`—so
the new error is the *second-order* term alone, one level deeper. The approximants are Cauchy
because `exp` preserves norms of differences, `K` is complete, and the limit is the preimage.
No continuity lemma for `NormedSpace.exp`, no radius-of-convergence argument, and no
logarithm enters.

The cited sources state the inverse-isomorphism pair on the whole
convergence ball—Koblitz over `ℂ_p`, from which the restriction to `K` is immediate—and the
per-level bijection is the standard refinement: above the threshold the exponential and the
logarithm preserve the valuation, so the ball bijection cuts to each level; the level
statement of the third source is the instance the layer's consumers use.

## References

* [FesenkoVostokov2002] I. B. Fesenko, S. V. Vostokov, *Local fields and their extensions*,
  Translations of Mathematical Monographs **121**, American Mathematical Society, second
  edition, 2002.
* [Koblitz1984] N. Koblitz, *p-adic numbers, p-adic analysis, and zeta-functions*, Graduate
  Texts in Mathematics **58**, Springer New York, 1984.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

open ValuativeRel Finset.HasAntidiagonal
open Atlas.Knowledge.PadicExpConvergence Atlas.Knowledge.RationalIntegerValuation
open scoped Nat

namespace Atlas.Knowledge

namespace PadicExpIsomorphism

/-- The binomial identity behind `exp_add`, one `n` at a time: the `n`th term of the
exponential series at `x + y` is the antidiagonal sum of the products of the `i`th term at `x`
and the `j`th term at `y`, because `(n !)⁻¹ * (n.choose i) = (i !)⁻¹ * (j !)⁻¹`. -/
private theorem expTerm_add (K : Type*) [Field K] [CharZero K] (x y : K) (n : ℕ) :
    ((n ! : ℚ)⁻¹) • (x + y) ^ n
      = ∑ kl ∈ antidiagonal n, (((kl.1 ! : ℚ)⁻¹) • x ^ kl.1) * (((kl.2 ! : ℚ)⁻¹) • y ^ kl.2) := by
  rw [(Commute.all x y).add_pow', Finset.smul_sum]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [mem_antidiagonal] at hkl
  subst hkl
  have h1 : ((kl.1 ! : ℕ) : K) ≠ 0 := by exact_mod_cast kl.1.factorial_ne_zero
  have h2 : ((kl.2 ! : ℕ) : K) ≠ 0 := by exact_mod_cast kl.2.factorial_ne_zero
  have h3 : ((((kl.1 + kl.2)! : ℕ)) : K) ≠ 0 := by exact_mod_cast (kl.1 + kl.2).factorial_ne_zero
  have hkey : (((kl.1 + kl.2).choose kl.1 : ℕ) : K) * ((kl.1 ! : ℕ) : K) * ((kl.2 ! : ℕ) : K)
      = (((kl.1 + kl.2)! : ℕ) : K) := by
    have h := Nat.add_choose_mul_factorial_mul_factorial kl.2 kl.1
    rw [Nat.add_comm kl.2 kl.1] at h
    exact_mod_cast congrArg (fun m : ℕ => (m : K)) (by linarith [h] : (kl.1 + kl.2).choose kl.1 *
      kl.1 ! * kl.2 ! = (kl.1 + kl.2)!)
  rw [Rat.smul_def, Rat.smul_def, Rat.smul_def, nsmul_eq_mul]
  push_cast
  field_simp
  linear_combination (x ^ kl.1 * y ^ kl.2) * hkey


theorem tail_exponent {D e w v n : ℕ} (hD : 1 ≤ D) (hv : D * v + 1 ≤ n) (hw : e + 1 ≤ D * w)
    (hn : 2 ≤ n) : e * v + w + 1 ≤ w * n := by
  have h1 : (D : ℤ) * v + 1 ≤ (n : ℤ) := by exact_mod_cast hv
  have h2 : (e : ℤ) + 1 ≤ (D : ℤ) * w := by exact_mod_cast hw
  have h3 : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have h4 : (0 : ℤ) ≤ (e : ℤ) := Int.natCast_nonneg e
  have hD' : (1 : ℤ) ≤ (D : ℤ) := by exact_mod_cast hD
  have key : (1 : ℤ) ≤ (D : ℤ) * ((w : ℤ) * n - (e : ℤ) * v - (w : ℤ)) := by
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ (n : ℤ) - 1)
      (by linarith : (0:ℤ) ≤ (D : ℤ) * w - (e : ℤ))]
  have hT : (1 : ℤ) ≤ (w : ℤ) * n - (e : ℤ) * v - (w : ℤ) := by nlinarith
  have : ((e * v + w + 1 : ℕ) : ℤ) ≤ ((w * n : ℕ) : ℤ) := by push_cast; linarith
  exact_mod_cast this

section Normed

variable {K : Type*} [NormedField K] [CharZero K] [ValuativeRel K] [IsUltrametricDist K]
  [CompleteSpace K] [IsDiscreteValuationRing ↥𝒪[K]]
  (hc : ∀ y : K, ‖y‖ ≤ 1 ↔ valuation K y ≤ 1)
  (hp : (residueCharacteristic K).Prime)
  (hpe : Ideal.span {((residueCharacteristic K : ℕ) : ↥𝒪[K])}
    = 𝓂[K] ^ absoluteRamificationIndex K)

include hc hp hpe

omit [CharZero K] [IsUltrametricDist K] [CompleteSpace K] [IsDiscreteValuationRing ↥𝒪[K]] hc
  hpe in
/-- The guard `e < (p - 1) * i` puts `i` at or past the convergence threshold, so every claim
proved on the threshold ideal applies at level `i`. -/
private theorem threshold_le {i : ℕ}
    (hi : absoluteRamificationIndex K < (residueCharacteristic K - 1) * i) :
    absoluteRamificationIndex K / (residueCharacteristic K - 1) + 1 ≤ i := by
  have hD : 0 < residueCharacteristic K - 1 := by have := hp.two_le; omega
  have := (Nat.div_lt_iff_lt_mul hD).mpr (by rw [Nat.mul_comm] at hi; exact hi)
  omega

set_option synthInstance.maxHeartbeats 80000 in
-- The ideal arithmetic on `↥𝒪[K]` does not fit the default instance budget.
theorem norm_exp_estimates {ϖ : ↥𝒪[K]} (hϖ : Irreducible ϖ) {i : ℕ}
    (hi : absoluteRamificationIndex K < (residueCharacteristic K - 1) * i)
    {x : ↥𝒪[K]} (hx : x ∈ (𝓂[K] ^ i : Ideal ↥𝒪[K])) :
    ‖NormedSpace.exp (x : K) - 1 - (x : K)‖ ≤ ‖((ϖ : ↥𝒪[K]) : K)‖ * ‖(x : K)‖ ∧
      ‖NormedSpace.exp (x : K) - 1‖ = ‖(x : K)‖ := by
  haveI : Fact (residueCharacteristic K).Prime := ⟨hp⟩
  have hxth : x ∈ (𝓂[K] ^ (absoluteRamificationIndex K / (residueCharacteristic K - 1) + 1) :
      Ideal ↥𝒪[K]) := Ideal.pow_le_pow_right (PadicExpIsomorphism.threshold_le hp hi) hx
  have hsummable : Summable (fun n : ℕ => (n ! : ℚ)⁻¹ • ((x : K) ^ n)) :=
    Summable.of_norm (summable_norm_expSeries hc hp hpe hxth)
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  obtain ⟨w, hc0, hc1, hterm, hmem⟩ := exists_norm_term_eq hc hp hpe hϖ hx0
  set c : ℝ := ‖((ϖ : ↥𝒪[K]) : K)‖ with hcϖ
  set f : ℕ → K := fun n => (n ! : ℚ)⁻¹ • ((x : K) ^ n) with hf
  have e0 : f 0 = 1 := by simp [hf]
  have e1 : f 1 = (x : K) := by simp [hf]
  have hxw : ‖(x : K)‖ = c ^ w := by
    have h := hterm 1
    simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_smul, pow_one, mul_one,
      padicValNat_one_right, Nat.mul_zero, pow_zero, div_one] at h
    exact h
  have hiw : i ≤ w := (hmem i).mp hx
  have hDw : absoluteRamificationIndex K + 1 ≤ (residueCharacteristic K - 1) * w :=
    le_trans (by omega) (Nat.mul_le_mul_left _ hiw)
  -- every term past the first is at most `c ^ (w + 1)`
  have htail : ∀ n : ℕ, 2 ≤ n → ‖f n‖ ≤ c ^ (w + 1) := by
    intro n hn
    have hv : (residueCharacteristic K - 1) *
        padicValNat (residueCharacteristic K) (n !) + 1 ≤ n :=
      sub_one_mul_padicValNat_factorial_lt_of_ne_zero _ (by omega)
    have hexp := tail_exponent (D := residueCharacteristic K - 1) (by have := hp.two_le; omega)
      hv hDw hn
    rw [hf]
    simp only
    rw [hterm n, div_le_iff₀ (by positivity), ← pow_add]
    exact pow_le_pow_of_le_one hc0.le hc1.le (by omega)
  have hs1 : Summable (fun n : ℕ => f (n + 1)) := (summable_nat_add_iff 1).mpr hsummable
  have hs2 : Summable (fun n : ℕ => f (n + 2)) := (summable_nat_add_iff 2).mpr hsummable
  have hsplit : NormedSpace.exp (x : K) - 1 = (x : K) + ∑' n : ℕ, f (n + 2) := by
    have h1 : NormedSpace.exp (x : K) = ∑' n : ℕ, f n := by
      rw [NormedSpace.exp_eq_tsum_rat]
    rw [h1, hsummable.tsum_eq_zero_add, e0, hs1.tsum_eq_zero_add]
    simp only [zero_add]
    rw [e1]
    ring
  have hbound : ‖∑' n : ℕ, f (n + 2)‖ ≤ c ^ (w + 1) :=
    (IsUltrametricDist.norm_tsum_le _).trans (ciSup_le fun n => htail _ (by omega))
  have hlt : c ^ (w + 1) < c ^ w := pow_lt_pow_right_of_lt_one₀ hc0 hc1 (by omega)
  refine ⟨?_, ?_⟩
  · have hsub : NormedSpace.exp (x : K) - 1 - (x : K) = ∑' n : ℕ, f (n + 2) := by
      rw [hsplit]; ring
    rw [hsub, hxw, ← hcϖ, pow_succ] at *
    calc ‖∑' n : ℕ, f (n + 2)‖ ≤ c ^ w * c := hbound
      _ = c * c ^ w := by ring
  · rw [hsplit, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by
      rw [hxw]; exact fun h => absurd (h ▸ hbound) (by simpa using hlt.not_ge)), hxw]
    exact max_eq_left (le_trans hbound hlt.le)

end Normed

end PadicExpIsomorphism

namespace PadicExpIsomorphism


set_option synthInstance.maxHeartbeats 80000 in
-- The ideal arithmetic on `↥𝒪[K]` does not fit the default instance budget.
/-- On the convergence ideal, the exponential turns addition into multiplication:
`exp (x + y) = exp x * exp y` for `x`, `y` in `𝓂 ^ (e / (p - 1) + 1)`—hence on every deeper
level by inclusion ([Koblitz 1984, Chap. IV, §1, p.80][Koblitz1984];
[Fesenko–Vostokov 2002, Chap. VI, (1.2) and (1.5), pp.208, 212][FesenkoVostokov2002]). -/
theorem exp_add (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (x y : ↥𝒪[K])
    (hx : x ∈ (𝓂[K] ^ (absoluteRamificationIndex K / (residueCharacteristic K - 1) + 1) :
      Ideal ↥𝒪[K]))
    (hy : y ∈ (𝓂[K] ^ (absoluteRamificationIndex K / (residueCharacteristic K - 1) + 1) :
      Ideal ↥𝒪[K])) :
    NormedSpace.exp ((x : K) + (y : K)) = NormedSpace.exp (x : K) * NormedSpace.exp (y : K) := by
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
  have hc : ∀ z : K, ‖z‖ ≤ 1 ↔ valuation K z ≤ 1 := fun z => Valued.toNormedField.norm_le_one_iff
  have hpe := span_residueCharacteristic_eq_maximalIdeal_pow K
  rw [NormedSpace.exp_eq_tsum_rat]
  simp only
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (PadicExpConvergence.summable_norm_expSeries hc hp hpe hx)
    (PadicExpConvergence.summable_norm_expSeries hc hp hpe hy)]
  exact tsum_congr fun n => expTerm_add K _ _ n

end PadicExpIsomorphism

/-- Above the threshold `e / (p - 1)`, the exponential is a bijection of the ideal power onto
the higher unit group: for `(p - 1) * i > e`, `NormedSpace.exp` maps the image of `𝓂 ^ i` in
`K` bijectively onto the image of `U i (K)`. With `PadicExpIsomorphism.exp_add` and the two
inversion identities, this is the statement that `exp` and `log` are mutually inverse
isomorphisms between `𝓂 ^ i` and `U i (K)`
([Fesenko–Vostokov 2002, Chap. VI, (1.4), p.212][FesenkoVostokov2002] and
[Koblitz 1984, Chap. IV, §1, Prop., p.81][Koblitz1984] for the pair on the whole convergence
ball; [Hyeon 2025, §4, p.17][Hyeon2025] for the restriction to a level; the per-level form is
the standard refinement, per the implementation notes). -/
theorem padicExpIsomorphism (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (i : ℕ+)
    (hi : absoluteRamificationIndex K < (residueCharacteristic K - 1) * (i : ℕ)) :
    Set.BijOn NormedSpace.exp
      (((↑) : ↥𝒪[K] → K) '' ((𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) : Set ↥𝒪[K]))
      (((↑) : Kˣ → K) '' (higherUnitGroup K i : Set Kˣ)) := by
  have hp : (residueCharacteristic K).Prime := residueCharacteristic_prime K
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  haveI : CompleteSpace K := inferInstance
  haveI : IsUltrametricDist K := inferInstance
  have hc : ∀ z : K, ‖z‖ ≤ 1 ↔ valuation K z ≤ 1 := fun z => Valued.toNormedField.norm_le_one_iff
  have hpe := span_residueCharacteristic_eq_maximalIdeal_pow K
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (↥𝒪[K])
  have hkey : ∀ {z : ↥𝒪[K]}, z ∈ (𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) →
      ‖NormedSpace.exp (z : K) - 1‖ = ‖(z : K)‖ :=
    fun {z} hz => (PadicExpIsomorphism.norm_exp_estimates hc hp hpe hϖ hi hz).2
  have hc0 : 0 < ‖((ϖ : ↥𝒪[K]) : K)‖ := by
    rw [norm_pos_iff]; simpa using hϖ.ne_zero
  have hc1 : ‖((ϖ : ↥𝒪[K]) : K)‖ < 1 := by
    rw [RationalIntegerValuation.norm_lt_one_iff_valuation_lt_one hc]
    exact valuation_lt_one_of_mem_maximalIdeal _
      (by rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ)
  have hmn := PadicExpConvergence.mem_pow_iff_norm_le hc hϖ hc0 hc1
  -- membership in the maximal ideal forces norm below one
  have hlt1 : ∀ {z : ↥𝒪[K]}, z ∈ (𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) → ‖(z : K)‖ < 1 := by
    intro z hz
    rw [RationalIntegerValuation.norm_lt_one_iff_valuation_lt_one hc]
    exact valuation_lt_one_of_mem_maximalIdeal _
      (Ideal.pow_le_self i.pos.ne' hz)
  -- the exponential of such a point is a unit of norm one
  have hnormexp : ∀ {z : ↥𝒪[K]}, z ∈ (𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) →
      ‖NormedSpace.exp (z : K)‖ = 1 := by
    intro z hz
    have h1 : NormedSpace.exp (z : K) = 1 + (NormedSpace.exp (z : K) - 1) := by ring
    rw [h1, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by
      rw [norm_one, hkey hz]; exact fun h => absurd h.symm (hlt1 hz).ne)]
    simp [hkey hz, (hlt1 hz).le]
  have hth : ∀ {z : ↥𝒪[K]}, z ∈ (𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) →
      z ∈ (𝓂[K] ^ (absoluteRamificationIndex K / (residueCharacteristic K - 1) + 1) :
        Ideal ↥𝒪[K]) :=
    fun {z} hz => Ideal.pow_le_pow_right (PadicExpIsomorphism.threshold_le hp hi) hz
  refine ⟨?_, ?_, ?_⟩
  · -- `exp` lands in the higher unit group
    rintro _ ⟨z, hz, rfl⟩
    have hne : NormedSpace.exp ((z : ↥𝒪[K]) : K) ≠ 0 := by
      intro h
      have := hnormexp hz
      rw [h, norm_zero] at this
      exact zero_ne_one this
    have hint : NormedSpace.exp ((z : ↥𝒪[K]) : K) - 1 ∈ 𝒪[K] := by
      have : ‖NormedSpace.exp ((z : ↥𝒪[K]) : K) - 1‖ ≤ 1 := by
        rw [hkey hz]; exact (hlt1 hz).le
      exact (hc _).mp this
    refine ⟨Units.mk0 _ hne, ⟨⟨⟨_, hint⟩, ?_⟩, ?_⟩, rfl⟩
    · rw [hmn]
      rw [hkey hz]
      exact (hmn z (i : ℕ)).mp hz
    · simp
  · -- injectivity
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    have hd : (a - b) ∈ (𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) := sub_mem ha hb
    have hbne : NormedSpace.exp ((b : ↥𝒪[K]) : K) ≠ 0 := by
      intro h
      have := hnormexp hb
      rw [h, norm_zero] at this
      exact zero_ne_one this
    have hsum : ((a - b : ↥𝒪[K]) : K) + ((b : ↥𝒪[K]) : K) = ((a : ↥𝒪[K]) : K) := by
      push_cast; ring
    have hprod := PadicExpIsomorphism.exp_add K (a - b) b (hth hd) (hth hb)
    rw [hsum, hab] at hprod
    have hone : NormedSpace.exp ((a - b : ↥𝒪[K]) : K) = 1 := by
      apply mul_right_cancel₀ hbne
      rw [one_mul]
      exact hprod.symm
    have hnd := hkey hd
    rw [hone, sub_self, norm_zero] at hnd
    have : ((a - b : ↥𝒪[K]) : K) = 0 := by
      simpa using norm_eq_zero.mp hnd.symm
    push_cast at this
    exact sub_eq_zero.mp this
  · -- surjectivity, by successive approximation on the filtration
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨y0, hy0⟩ := hu
    have hunorm : ‖(u : K)‖ = 1 := by
      have h1 : (u : K) = 1 + ((y0 : ↥𝒪[K]) : K) := hy0.symm
      have h2 : ‖((y0 : ↥𝒪[K]) : K)‖ < 1 := hlt1 y0.2
      rw [h1, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by
        rw [norm_one]; exact fun h => absurd h.symm h2.ne)]
      simp [h2.le]
    have hune : (u : K) ≠ 0 := u.ne_zero
    -- the approximation step
    have happrox : ∀ k : ℕ, ∃ z : ↥𝒪[K], z ∈ (𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) ∧
        ‖NormedSpace.exp (z : K) - (u : K)‖ ≤ ‖((ϖ : ↥𝒪[K]) : K)‖ ^ ((i : ℕ) + k) := by
      intro k
      induction k with
      | zero =>
          refine ⟨0, Ideal.zero_mem _, ?_⟩
          have : NormedSpace.exp ((0 : ↥𝒪[K]) : K) - (u : K) = -(((y0 : ↥𝒪[K]) : K)) := by
            push_cast
            rw [NormedSpace.exp_zero, ← hy0]
            ring
          rw [this, norm_neg, Nat.add_zero]
          exact (hmn _ _).mp y0.2
      | succ k ih =>
          obtain ⟨z, hz, hzk⟩ := ih
          have hTnorm : ‖(u : K)⁻¹ * NormedSpace.exp (z : K) - 1‖
              ≤ ‖((ϖ : ↥𝒪[K]) : K)‖ ^ ((i : ℕ) + k) := by
            have : (u : K)⁻¹ * NormedSpace.exp (z : K) - 1
                = (u : K)⁻¹ * (NormedSpace.exp (z : K) - (u : K)) := by
              field_simp
            rw [this, norm_mul, norm_inv, hunorm, inv_one, one_mul]
            exact hzk
          have hTint : (u : K)⁻¹ * NormedSpace.exp (z : K) - 1 ∈ 𝒪[K] :=
            (hc _).mp (le_trans hTnorm (pow_le_one₀ hc0.le hc1.le))
          set T : ↥𝒪[K] := ⟨_, hTint⟩ with hT
          have hTmem : T ∈ (𝓂[K] ^ ((i : ℕ) + k) : Ideal ↥𝒪[K]) := (hmn _ _).mpr hTnorm
          have hTi : T ∈ (𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) :=
            Ideal.pow_le_pow_right (by omega) hTmem
          refine ⟨z - T, sub_mem hz hTi, ?_⟩
          have hTne : NormedSpace.exp ((T : ↥𝒪[K]) : K) ≠ 0 := by
            intro h
            have := hnormexp hTi
            rw [h, norm_zero] at this
            exact zero_ne_one this
          have hTdef : (u : K) * ((T : ↥𝒪[K]) : K)
              = NormedSpace.exp ((z : ↥𝒪[K]) : K) - (u : K) := by
            change (u : K) * ((u : K)⁻¹ * NormedSpace.exp ((z : ↥𝒪[K]) : K) - 1) = _
            field_simp
          have hzT : ((z - T : ↥𝒪[K]) : K) + ((T : ↥𝒪[K]) : K) = ((z : ↥𝒪[K]) : K) := by
            push_cast; ring
          have hsplit := PadicExpIsomorphism.exp_add K (z - T) T (hth (sub_mem hz hTi)) (hth hTi)
          rw [hzT] at hsplit
          have halg : NormedSpace.exp ((z - T : ↥𝒪[K]) : K) - (u : K)
              = -((u : K) * (NormedSpace.exp ((T : ↥𝒪[K]) : K) - 1 - ((T : ↥𝒪[K]) : K)))
                * (NormedSpace.exp ((T : ↥𝒪[K]) : K))⁻¹ := by
            rw [eq_comm, ← div_eq_mul_inv, div_eq_iff hTne]
            linear_combination hTdef + hsplit
          rw [halg, norm_mul, norm_neg, norm_mul, norm_inv, hnormexp hTi, hunorm,
            inv_one, one_mul, mul_one]
          calc ‖NormedSpace.exp ((T : ↥𝒪[K]) : K) - 1 - ((T : ↥𝒪[K]) : K)‖
              ≤ ‖((ϖ : ↥𝒪[K]) : K)‖ * ‖((T : ↥𝒪[K]) : K)‖ :=
                (PadicExpIsomorphism.norm_exp_estimates hc hp hpe hϖ hi hTi).1
            _ ≤ ‖((ϖ : ↥𝒪[K]) : K)‖ * ‖((ϖ : ↥𝒪[K]) : K)‖ ^ ((i : ℕ) + k) := by
                exact mul_le_mul_of_nonneg_left ((hmn _ _).mp hTmem) hc0.le
            _ = ‖((ϖ : ↥𝒪[K]) : K)‖ ^ ((i : ℕ) + (k + 1)) := by ring
    choose X hXmem hXbound using happrox
    set c : ℝ := ‖((ϖ : ↥𝒪[K]) : K)‖ with hcdef
    have hXne : ∀ n : ℕ, NormedSpace.exp ((X n : ↥𝒪[K]) : K) ≠ 0 := by
      intro n h
      have := hnormexp (hXmem n)
      rw [h, norm_zero] at this
      exact zero_ne_one this
    -- `exp` is norm-preserving on differences, so the approximants are Cauchy
    have hdist : ∀ a b : ↥𝒪[K], a ∈ (𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) →
        b ∈ (𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) → NormedSpace.exp ((b : ↥𝒪[K]) : K) ≠ 0 →
        ‖NormedSpace.exp ((a : ↥𝒪[K]) : K) - NormedSpace.exp ((b : ↥𝒪[K]) : K)‖
          = ‖((a : ↥𝒪[K]) : K) - ((b : ↥𝒪[K]) : K)‖ := by
      intro a b ha hb hbne
      have hd : a - b ∈ (𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) := sub_mem ha hb
      have hsum : ((a - b : ↥𝒪[K]) : K) + ((b : ↥𝒪[K]) : K) = ((a : ↥𝒪[K]) : K) := by
        push_cast; ring
      have hs := PadicExpIsomorphism.exp_add K (a - b) b (hth hd) (hth hb)
      rw [hsum] at hs
      have heq : NormedSpace.exp ((a - b : ↥𝒪[K]) : K) - 1
          = (NormedSpace.exp ((a : ↥𝒪[K]) : K) - NormedSpace.exp ((b : ↥𝒪[K]) : K))
            * (NormedSpace.exp ((b : ↥𝒪[K]) : K))⁻¹ := by
        rw [eq_comm, ← div_eq_mul_inv, div_eq_iff hbne]
        linear_combination hs
      have := hkey hd
      rw [heq, norm_mul, norm_inv, hnormexp hb, inv_one, mul_one] at this
      rw [this]
      push_cast
      ring_nf
    have hpair : ∀ m n : ℕ, ‖((X m : ↥𝒪[K]) : K) - ((X n : ↥𝒪[K]) : K)‖
        ≤ max (c ^ ((i : ℕ) + m)) (c ^ ((i : ℕ) + n)) := by
      intro m n
      rw [← hdist _ _ (hXmem m) (hXmem n) (hXne n)]
      have heq : NormedSpace.exp ((X m : ↥𝒪[K]) : K) - NormedSpace.exp ((X n : ↥𝒪[K]) : K)
          = (NormedSpace.exp ((X m : ↥𝒪[K]) : K) - (u : K))
            + ((u : K) - NormedSpace.exp ((X n : ↥𝒪[K]) : K)) := by ring
      rw [heq]
      refine le_trans (IsUltrametricDist.norm_add_le_max _ _) ?_
      exact max_le_max (hXbound m) (by rw [norm_sub_rev]; exact hXbound n)
    have hcauchy : CauchySeq (fun n => ((X n : ↥𝒪[K]) : K)) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ : ∃ N : ℕ, c ^ N < ε := exists_pow_lt_of_lt_one hε hc1
      refine ⟨N, fun m hm n hn => ?_⟩
      rw [dist_eq_norm]
      refine lt_of_le_of_lt (le_trans (hpair m n) ?_) hN
      exact max_le (pow_le_pow_of_le_one hc0.le hc1.le (by omega))
        (pow_le_pow_of_le_one hc0.le hc1.le (by omega))
    obtain ⟨xl, hxl⟩ := cauchySeq_tendsto_of_complete hcauchy
    have hxlnorm : ‖xl‖ ≤ c ^ (i : ℕ) :=
      le_of_tendsto hxl.norm (Filter.Eventually.of_forall fun n => (hmn _ _).mp (hXmem n))
    have hxlint : xl ∈ 𝒪[K] := (hc _).mp (le_trans hxlnorm (pow_le_one₀ hc0.le hc1.le))
    set L : ↥𝒪[K] := ⟨xl, hxlint⟩ with hL
    have hLmem : L ∈ (𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) := (hmn _ _).mpr hxlnorm
    refine ⟨((L : ↥𝒪[K]) : K), ⟨L, hLmem, rfl⟩, ?_⟩
    have hbnd : ∀ n : ℕ, ‖NormedSpace.exp ((L : ↥𝒪[K]) : K) - (u : K)‖
        ≤ max (‖((L : ↥𝒪[K]) : K) - ((X n : ↥𝒪[K]) : K)‖) (c ^ ((i : ℕ) + n)) := by
      intro n
      have heq : NormedSpace.exp ((L : ↥𝒪[K]) : K) - (u : K)
          = (NormedSpace.exp ((L : ↥𝒪[K]) : K) - NormedSpace.exp ((X n : ↥𝒪[K]) : K))
            + (NormedSpace.exp ((X n : ↥𝒪[K]) : K) - (u : K)) := by ring
      rw [heq]
      refine le_trans (IsUltrametricDist.norm_add_le_max _ _) ?_
      exact max_le_max (le_of_eq (hdist _ _ hLmem (hXmem n) (hXne n))) (hXbound n)
    have htend : Filter.Tendsto
        (fun n : ℕ => max (‖((L : ↥𝒪[K]) : K) - ((X n : ↥𝒪[K]) : K)‖) (c ^ ((i : ℕ) + n)))
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => ‖((L : ↥𝒪[K]) : K) - ((X n : ↥𝒪[K]) : K)‖)
          Filter.atTop (nhds 0) := by
        have hsub : Filter.Tendsto (fun n : ℕ => ((L : ↥𝒪[K]) : K) - ((X n : ↥𝒪[K]) : K))
            Filter.atTop (nhds 0) := by
          have hLxl : ((L : ↥𝒪[K]) : K) = xl := rfl
          simpa [hLxl] using (tendsto_const_nhds (α := ℕ)
            (x := ((L : ↥𝒪[K]) : K)) (f := Filter.atTop)).sub hxl
        simpa using hsub.norm
      have h2 : Filter.Tendsto (fun n : ℕ => c ^ ((i : ℕ) + n)) Filter.atTop (nhds 0) := by
        simpa [pow_add] using
          (tendsto_pow_atTop_nhds_zero_of_lt_one hc0.le hc1).const_mul (c ^ (i : ℕ))
      simpa using h1.max h2
    have hle0 : ‖NormedSpace.exp ((L : ↥𝒪[K]) : K) - (u : K)‖ ≤ 0 :=
      le_of_tendsto_of_tendsto tendsto_const_nhds htend (Filter.Eventually.of_forall hbnd)
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hle0 (norm_nonneg _)))

namespace PadicExpIsomorphism

/-- The logarithm inverts the exponential on the convergence ideal: `log (exp x) = x` for
`x ∈ 𝓂 ^ (e / (p - 1) + 1)`—hence on every deeper level by inclusion. Claim recorded ahead of
its proof ([Koblitz 1984, Chap. IV, §1, p.81][Koblitz1984];
[Fesenko–Vostokov 2002, Chap. VI, (1.4), p.212][FesenkoVostokov2002]). -/
theorem padicLogarithm_exp (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (x : ↥𝒪[K])
    (hx : x ∈ (𝓂[K] ^ (absoluteRamificationIndex K / (residueCharacteristic K - 1) + 1) :
      Ideal ↥𝒪[K])) :
    padicLogarithm K (NormedSpace.exp (x : K)) = x := by
  sorry

/-- The exponential inverts the logarithm on the higher unit group above the threshold:
`exp (log u) = u` for `u ∈ U i (K)` with `(p - 1) * i > e`. Claim recorded ahead of its proof
([Koblitz 1984, Chap. IV, §1, p.81][Koblitz1984];
[Fesenko–Vostokov 2002, Chap. VI, (1.4), p.212][FesenkoVostokov2002];
[Hyeon 2025, §4, p.17][Hyeon2025]). -/
theorem exp_padicLogarithm (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (i : ℕ+)
    (hi : absoluteRamificationIndex K < (residueCharacteristic K - 1) * (i : ℕ))
    (u : Kˣ) (hu : u ∈ higherUnitGroup K i) :
    NormedSpace.exp (padicLogarithm K (u : K)) = (u : K) := by
  sorry

end PadicExpIsomorphism

end Atlas.Knowledge
