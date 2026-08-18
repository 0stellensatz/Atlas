import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField

/-!
# p-adic numbers as mixed-characteristic local field

The first exhibited model of the carrier signature: `ℚ_[p]` is a mixed-characteristic local field.
Everything but one link is already in Mathlib — `ValuativeRel ℚ_[p]` induced by `Padic.mulValuation`
with its compatibility certificate, `CharZero ℚ_[p]`, `LocallyCompactSpace ℚ_[p]`,
`ValuativeRel.IsNontrivial ℚ_[p]` — and the missing link is `IsValuativeTopology ℚ_[p]`: that the
norm topology of `ℚ_[p]` is the topology of its valuative relation. This item supplies it by
matching the metric balls with the valuation balls through the dictionary
`‖z‖ = (p : ℝ) ^ (-z.valuation)`, and then packages the certificate instances, so that
`Atlas.Knowledge.IsMixedCharLocalField ℚ_[p]` synthesizes.

## Main statements

* `mulValuation_lt_exp_iff_norm_lt` — the ball dictionary: `Padic.mulValuation z < exp k` if and
  only if `‖z‖ < (p : ℝ) ^ k`.
* `padic_isValuativeTopology` — the norm topology on `ℚ_[p]` is the valuative topology.
* `padic_isMixedCharLocalField` — `ℚ_[p]` is a mixed-characteristic local field.

## Implementation notes

The derivation goes through Mathlib's own constructor
`IsValuativeTopology.of_mem_nhds_zero_iff_vle`, which asks for the neighborhoods of zero to be
exactly the balls of a single compatible valuation — here `Padic.mulValuation`, the valuation that
induces `ValuativeRel ℚ_[p]`. No `Valued ℚ_[p] ℤᵐ⁰` instance is installed on the way: `Valued`
extends `UniformSpace`, `ℚ_[p]`'s uniformity is the metric one, and a second uniformity instance
would be a diamond. The constructor takes the valuation directly, so the bridge needs no such
structure.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel WithZero

namespace Atlas.Knowledge

variable {p : ℕ} [hp : Fact p.Prime]

/-- The ball dictionary between `Padic.mulValuation` and the `p`-adic norm: the valuation ball of
radius `exp k` is the norm ball of radius `(p : ℝ) ^ k`, because `‖z‖ = (p : ℝ) ^ (-z.valuation)`
sets the two scales against each other ([Serre 1979, Chap. II, §1, p.26][Serre1979]). -/
lemma mulValuation_lt_exp_iff_norm_lt (z : ℚ_[p]) (k : ℤ) :
    Padic.mulValuation z < exp k ↔ ‖z‖ < (p : ℝ) ^ k := by
  rcases eq_or_ne z 0 with rfl | hz
  · have h1 : (0 : ℤᵐ⁰) < exp k := zero_lt_iff.mpr exp_ne_zero
    have h2 : (0 : ℝ) < (p : ℝ) ^ k := zpow_pos (mod_cast hp.out.pos) k
    simp [h1, h2]
  · rw [Padic.mulValuation_toFun, if_neg hz, exp_lt_exp, Padic.norm_eq_zpow_neg_valuation hz,
      zpow_lt_zpow_iff_right₀ (show (1 : ℝ) < p by exact_mod_cast hp.out.one_lt)]

/-- The norm topology on `ℚ_[p]` is the topology of its valuative relation: the valuation balls form
a base of the neighborhoods of zero ([Serre 1979, Chap. II, §1, pp.26–27][Serre1979]). -/
instance padic_isValuativeTopology : IsValuativeTopology ℚ_[p] := by
  refine IsValuativeTopology.of_mem_nhds_zero_iff_vle Padic.mulValuation
    fun {s} ↦ ⟨fun hs ↦ ?_, fun ⟨γ, hγ⟩ ↦ ?_⟩
  · obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hs
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε
      (inv_lt_one_of_one_lt₀ (show (1 : ℝ) < p by exact_mod_cast hp.out.one_lt))
    have hpn : Padic.mulValuation ((p : ℚ_[p]) ^ n) = exp (-(n : ℤ)) := by
      rw [map_pow, Padic.mulValuation_toFun,
        if_neg (Nat.cast_ne_zero.mpr hp.out.ne_zero), Padic.valuation_p, ← exp_nsmul]
      simp
    have h0 : Padic.mulValuation.restrict ((p : ℚ_[p]) ^ n) ≠ 0 := by
      rw [Ne, Valuation.restrict_eq_zero_iff, hpn]
      exact exp_ne_zero
    refine ⟨Units.mk0 _ h0, fun z hz ↦ hεs ?_⟩
    rw [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff, hpn,
      mulValuation_lt_exp_iff_norm_lt] at hz
    have hεn : (p : ℝ) ^ (-(n : ℤ)) = ((p : ℝ)⁻¹) ^ n := by
      rw [zpow_neg, zpow_natCast, inv_pow]
    exact mem_ball_zero_iff.mpr ((hεn ▸ hz).trans hn)
  · refine Filter.mem_of_superset (Metric.ball_mem_nhds 0
      (zpow_pos (show (0 : ℝ) < p by exact_mod_cast hp.out.pos)
        (log (MonoidWithZeroHom.ValueGroup₀.embedding γ.val))))
      fun z hz ↦ hγ ?_
    rw [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding,
      ← exp_log (show MonoidWithZeroHom.ValueGroup₀.embedding γ.val ≠ 0 by simp),
      mulValuation_lt_exp_iff_norm_lt]
    exact mem_ball_zero_iff.mp hz

/-- `ℚ_[p]` is a nonarchimedean local field: its topology is the valuative one, it is locally
compact, and the valuation is nontrivial ([Serre 1979, Chap. II, §1, pp.26–27][Serre1979]). -/
instance padic_isNonarchimedeanLocalField : IsNonarchimedeanLocalField ℚ_[p] where

/-- `ℚ_[p]` is a mixed-characteristic local field — the base model of the carrier signature
([Serre 1979, Chap. II, §1, p.27][Serre1979]). -/
instance padic_isMixedCharLocalField : IsMixedCharLocalField ℚ_[p] where

end Atlas.Knowledge
