import Mathlib
import Atlas.Knowledge.RealLowerRamificationGroup

/-!
# Herbrand function φ

The Herbrand function of a finite Galois extension of local fields: the piecewise-linear
homeomorphism `φ (u) = ∫ t in 0..u, dt / (G_0 : G_t)` of the real line that converts the lower
numbering of the ramification filtration into the upper numbering. This file defines `φ` as an
interval integral through `Atlas.Knowledge.realLowerRamificationGroup`, proves the calculus
facts that make it a change of numbering—`φ (0) = 0`, strict monotonicity, continuity,
bijectivity—and records **Herbrand's theorem**, the statement the function exists for: the
image of `G_u` in a quotient of the Galois group is the ramification group of the quotient at
index `φ (u)`, the index computed over the intermediate field. The inverse function is
`Atlas.Knowledge.HerbrandPsi`, and the numbering `φ` produces is
`Atlas.Knowledge.UpperRamificationGroup`.

## Main definitions

* `herbrandPhi` — `φ (u) = ∫ t in 0..u, Nat.card (G_t) / Nat.card (G_0)`.

## Main statements

* `herbrandPhi_zero`, `herbrandPhi_strictMono`, `herbrandPhi_continuous`,
  `herbrandPhi_bijective` — the calculus API, the last three under `FiniteDimensional K L`.
* `map_realLowerRamificationGroup` — Herbrand's theorem, recorded ahead of its proof.
* `herbrandPhi_comp` — transitivity in a tower, recorded ahead of its proof.

## Implementation notes

The source integrates `1 / (G_0 : G_t)` with a convention for `t ∈ [-1, 0]`; here the
integrand is the ratio `Nat.card (G_⌈t⌉) / Nat.card (G_0)`, which equals `1 / (G_0 : G_t)` on
`t ≥ 0` where `G_t ≤ G_0`, equals `1` on `(-1, 0]` as the source's convention demands, and
differs from the source's point convention only at `t = -1` itself, invisible to the integral.
The function is total on `ℝ`: below `u = -1` the source defines nothing and the integrand's
value `Nat.card (G) / Nat.card (G_0)` is junk—kept `≥ 1`, so bijectivity survives. Without
`FiniteDimensional K L` the cardinalities vanish and `φ` collapses to `0`; every statement
beyond the definition therefore assumes finiteness. Herbrand's theorem and transitivity are
stated over an abstract tower `K ⊆ E ⊆ L` with `ValuativeExtension K E` carrying the
compatibility of valuations; over a complete base that compatibility pins the valuation of `E`
to the canonical extension, which is what the recorded claims are about.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] (L : Type*) [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L]

/-- The **Herbrand function** `φ` of `L` over `K`:
`φ (u) = ∫ t in 0..u, Nat.card (G_t) / Nat.card (G_0)`, the integral of the reciprocal index
`1 / (G_0 : G_t)` through the real-indexed lower ramification filtration
([Serre 1979, Chap. IV, §3, p.73][Serre1979]). -/
noncomputable def herbrandPhi (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..u,
    (Nat.card (realLowerRamificationGroup K L t) : ℝ) /
      (Nat.card (lowerRamificationGroup K L 0) : ℝ)

/-- `φ (0) = 0` ([Serre 1979, Chap. IV, §3, Prop. 12, p.73][Serre1979]). -/
@[simp]
theorem herbrandPhi_zero : herbrandPhi K L 0 = 0 :=
  intervalIntegral.integral_same

section Finite

variable [FiniteDimensional K L]

private theorem integrand_antitone :
    Antitone (fun t : ℝ =>
      (Nat.card (realLowerRamificationGroup K L t) : ℝ) /
        (Nat.card (lowerRamificationGroup K L 0) : ℝ)) := by
  intro t t' h
  have hcard : Nat.card (realLowerRamificationGroup K L t') ≤
      Nat.card (realLowerRamificationGroup K L t) :=
    Nat.card_le_card_of_injective _
      (Subgroup.inclusion_injective (realLowerRamificationGroup_antitone K L h))
  dsimp only
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

private theorem integrand_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        (Nat.card (realLowerRamificationGroup K L t) : ℝ) /
          (Nat.card (lowerRamificationGroup K L 0) : ℝ))
      MeasureTheory.volume a b :=
  (integrand_antitone K L).intervalIntegrable

private theorem integrand_pos (t : ℝ) :
    0 < (Nat.card (realLowerRamificationGroup K L t) : ℝ) /
      (Nat.card (lowerRamificationGroup K L 0) : ℝ) := by
  have h1 : 0 < Nat.card (realLowerRamificationGroup K L t) := Nat.card_pos
  have h2 : 0 < Nat.card (lowerRamificationGroup K L 0) := Nat.card_pos
  positivity

private theorem le_integrand (t : ℝ) :
    1 / (Nat.card (lowerRamificationGroup K L 0) : ℝ) ≤
      (Nat.card (realLowerRamificationGroup K L t) : ℝ) /
        (Nat.card (lowerRamificationGroup K L 0) : ℝ) := by
  have h1 : 0 < Nat.card (realLowerRamificationGroup K L t) := Nat.card_pos
  gcongr
  exact_mod_cast h1

/-- The Herbrand function is strictly increasing
([Serre 1979, Chap. IV, §3, Prop. 12, p.73][Serre1979]). -/
theorem herbrandPhi_strictMono : StrictMono (herbrandPhi K L) := by
  intro u v huv
  have key := intervalIntegral.integral_add_adjacent_intervals
    (integrand_intervalIntegrable K L 0 u) (integrand_intervalIntegrable K L u v)
  have hpos : 0 < ∫ t in u..v,
      (Nat.card (realLowerRamificationGroup K L t) : ℝ) /
        (Nat.card (lowerRamificationGroup K L 0) : ℝ) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (integrand_intervalIntegrable K L u v) (fun t _ => integrand_pos K L t) huv
  have : herbrandPhi K L u + _ = herbrandPhi K L v := key
  linarith [this]

/-- The Herbrand function is continuous
([Serre 1979, Chap. IV, §3, Prop. 12, p.73][Serre1979]). -/
theorem herbrandPhi_continuous : Continuous (herbrandPhi K L) :=
  intervalIntegral.continuous_primitive (integrand_intervalIntegrable K L) 0

/-- The Herbrand function is a bijection of the real line: strictly increasing, continuous,
and of at least linear growth on either side
([Serre 1979, Chap. IV, §3, Prop. 12, p.73][Serre1979]). -/
theorem herbrandPhi_bijective : Function.Bijective (herbrandPhi K L) := by
  refine ⟨(herbrandPhi_strictMono K L).injective, ?_⟩
  have hc : 0 < (Nat.card (lowerRamificationGroup K L 0) : ℝ) := by
    exact_mod_cast (Nat.card_pos :
      0 < Nat.card (lowerRamificationGroup K L 0))
  have hbound_top : ∀ u : ℝ, 0 ≤ u →
      u / (Nat.card (lowerRamificationGroup K L 0) : ℝ) ≤ herbrandPhi K L u := by
    intro u hu
    have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hu
      (intervalIntegrable_const) (integrand_intervalIntegrable K L 0 u)
      (fun t _ => le_integrand K L t)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one_div] at hmono
    exact hmono
  have hbound_bot : ∀ u : ℝ, u ≤ 0 →
      herbrandPhi K L u ≤ u / (Nat.card (lowerRamificationGroup K L 0) : ℝ) := by
    intro u hu
    have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hu
      (intervalIntegrable_const) (integrand_intervalIntegrable K L u 0)
      (fun t _ => le_integrand K L t)
    rw [intervalIntegral.integral_const, smul_eq_mul, zero_sub, neg_mul, mul_one_div] at hmono
    have hsymm : herbrandPhi K L u = -∫ t in u..(0 : ℝ),
        (Nat.card (realLowerRamificationGroup K L t) : ℝ) /
          (Nat.card (lowerRamificationGroup K L 0) : ℝ) := by
      rw [herbrandPhi, intervalIntegral.integral_symm]
    rw [hsymm]
    linarith
  apply (herbrandPhi_continuous K L).surjective
  · refine Filter.tendsto_atTop_mono' Filter.atTop ?_
      ((Filter.tendsto_id.atTop_div_const hc))
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with u hu
    exact hbound_top u hu
  · refine Filter.tendsto_atBot_mono' Filter.atBot ?_
      ((Filter.tendsto_id.atBot_div_const hc))
    filter_upwards [Filter.eventually_le_atBot (0 : ℝ)] with u hu
    exact hbound_bot u hu

end Finite

section Tower

variable (E : Type*) [Field E] [ValuativeRel E] [Algebra K E] [Algebra E L]
  [IsScalarTower K E L] [ValuativeExtension K E] [Algebra.IsAlgebraic E L]

/-- **Herbrand's theorem**: for a normal subextension `E` of a finite Galois extension `L` of
a mixed-characteristic local field `K`, the image of the real-indexed lower ramification group
`G_u` under restriction to `E` is the ramification group of `E` over `K` at index
`φ_{L/E} (u)`—the Herbrand function computed over the intermediate field. Claim recorded ahead
of its proof ([Serre 1979, Chap. IV, §3, Lem. 5, p.75][Serre1979]). -/
theorem map_realLowerRamificationGroup [TopologicalSpace K] [IsMixedCharLocalField K]
    [FiniteDimensional K L] [IsGalois K L] [Normal K E] (u : ℝ) :
    Subgroup.map (AlgEquiv.restrictNormalHom E) (realLowerRamificationGroup K L u) =
      realLowerRamificationGroup K E (herbrandPhi E L u) := by
  sorry

/-- Transitivity of the Herbrand function in a tower: `φ_{L/K} = φ_{E/K} ∘ φ_{L/E}`. Claim
recorded ahead of its proof ([Serre 1979, Chap. IV, §3, Prop. 15, p.74][Serre1979]). -/
theorem herbrandPhi_comp [TopologicalSpace K] [IsMixedCharLocalField K]
    [FiniteDimensional K L] [IsGalois K L] [Normal K E] (u : ℝ) :
    herbrandPhi K L u = herbrandPhi K E (herbrandPhi E L u) := by
  sorry

end Tower

end Atlas.Knowledge
