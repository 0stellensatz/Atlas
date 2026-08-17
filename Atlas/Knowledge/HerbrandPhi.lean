import Mathlib
import Atlas.Knowledge.RealLowerRamificationGroup
import Atlas.Knowledge.RamificationNumber

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
`Atlas.Knowledge.UpperRamificationGroup`. The file also carries the evaluation of `φ` at
integer arguments and its equivalent form as a sum of truncated ramification numbers `i_G`.

## Main definitions

* `herbrandPhi` — `φ (u) = ∫ t in 0..u, Nat.card (G_t) / Nat.card (G_0)`.

## Main statements

* `herbrandPhi_zero`, `herbrandPhi_strictMono`, `herbrandPhi_continuous`,
  `herbrandPhi_bijective` — the calculus API, the last three under `FiniteDimensional K L`.
* `herbrandPhi_eq_add_of_mem_Icc` — `φ` is affine on `[n, n + 1]`, slope `1 / (G_0 : G_{n+1})`.
* `herbrandPhi_natCast` — the evaluation at integers: `φ (n) = (g_0 + ⋯ + g_{n}) / g_0 - 1`.
* `sum_toNat_min_ramificationNumber` — the `i_G` form: `Σ_σ min (i_G σ, n + 1) = g_0 (φ (n) + 1)`.
* `map_realLowerRamificationGroup` — Herbrand's theorem, recorded ahead of its proof.
* `herbrandPhi_comp` — transitivity in a tower, recorded ahead of its proof.

## Implementation notes

The source integrates `1 / (G_0 : G_t)` with a convention for `t ∈ [-1, 0]`; here the
integrand is the ratio `Nat.card (G_⌈t⌉) / Nat.card (G_0)`, which equals `1 / (G_0 : G_t)` on
`t ≥ 0` where `G_t ≤ G_0`, equals `1` on `(-1, 0]`, and at `t = -1`, where the source's
convention reads `(G_0 : G_t) = (G_{-1} : G_0)⁻¹`, equals that reciprocal as well—the
encoding matches the source at every point of `[-1, 0]`.
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
([Serre 1979, Chap. IV, §3, p.73][Serre1979]). -/
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
and of at least linear growth on either side—the source's homeomorphism of `[-1, +∞)`,
extended over the junk region by design ([Serre 1979, Chap. IV, §3, p.73][Serre1979]). -/
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

/-- The Herbrand function is affine on each interval `[n, n + 1]`, of slope
`1 / (G_0 : G_{n+1})`—the explicit piecewise-linear description of `φ`, whose display the
source states for positive `n`; `n = 0` is admitted here
([Serre 1979, Chap. IV, §3, p.73][Serre1979]). -/
theorem herbrandPhi_eq_add_of_mem_Icc {n : ℕ} {u : ℝ} (h1 : (n : ℝ) ≤ u) (h2 : u ≤ n + 1) :
    herbrandPhi K L u = herbrandPhi K L n +
      (u - n) * ((Nat.card (lowerRamificationGroup K L (n + 1)) : ℝ) /
        (Nat.card (lowerRamificationGroup K L 0) : ℝ)) := by
  have key := intervalIntegral.integral_add_adjacent_intervals
    (integrand_intervalIntegrable K L 0 n) (integrand_intervalIntegrable K L n u)
  have hcongr : (∫ t in (n : ℝ)..u,
      (Nat.card (realLowerRamificationGroup K L t) : ℝ) /
        (Nat.card (lowerRamificationGroup K L 0) : ℝ)) =
      ∫ t in (n : ℝ)..u,
        (Nat.card (lowerRamificationGroup K L ((n : ℤ) + 1)) : ℝ) /
          (Nat.card (lowerRamificationGroup K L 0) : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t ht
    rw [Set.uIoc_of_le h1] at ht
    rw [realLowerRamificationGroup_eq K L (i := (n : ℤ) + 1)
      (by push_cast; linarith [ht.1]) (by push_cast; linarith [ht.2])]
  rw [hcongr, intervalIntegral.integral_const, smul_eq_mul] at key
  have key' : herbrandPhi K L n + (u - (n : ℝ)) *
      ((Nat.card (lowerRamificationGroup K L ((n : ℤ) + 1)) : ℝ) /
        (Nat.card (lowerRamificationGroup K L 0) : ℝ)) = herbrandPhi K L u := key
  linarith [key']

/-- The evaluation of the Herbrand function at a natural number:
`φ (n) + 1 = (g_0 + g_1 + ⋯ + g_n) / g_0` for `g_i = Nat.card (G_i)`—the source's displayed
formula, stated there for positive `n`; `n = 0` is admitted here, both sides reading `0`
([Serre 1979, Chap. IV, §3, p.73][Serre1979]). -/
theorem herbrandPhi_natCast (n : ℕ) :
    herbrandPhi K L n =
      (∑ i ∈ Finset.range (n + 1), (Nat.card (lowerRamificationGroup K L i) : ℝ)) /
        (Nat.card (lowerRamificationGroup K L 0) : ℝ) - 1 := by
  have h0 : (Nat.card (lowerRamificationGroup K L 0) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := lowerRamificationGroup K L 0)).ne'
  induction n with
  | zero => simp
  | succ n ih =>
    have key := herbrandPhi_eq_add_of_mem_Icc K L (n := n) (u := (n : ℝ) + 1)
      (by linarith) le_rfl
    rw [Finset.sum_range_succ]
    push_cast
    rw [key, ih]
    field_simp
    ring

/-- The integer-argument form of the source's Lemma 3, phrased through
`Atlas.Knowledge.ramificationNumber`: the truncated ramification numbers `min (i_G (σ), n + 1)`
sum over the Galois group to `g_0 (φ (n) + 1)`
([Serre 1979, Chap. IV, §3, Lem. 3, p.74][Serre1979]). -/
theorem sum_toNat_min_ramificationNumber (n : ℕ) :
    (∑ σ : L ≃ₐ[K] L, ((min (ramificationNumber K L σ) (n + 1 : ℕ∞)).toNat : ℝ)) =
      (Nat.card (lowerRamificationGroup K L 0) : ℝ) * (herbrandPhi K L n + 1) := by
  classical
  have hnat : (∑ σ : L ≃ₐ[K] L, (min (ramificationNumber K L σ) ((n : ℕ∞) + 1)).toNat) =
      ∑ i ∈ Finset.range (n + 1), Nat.card (lowerRamificationGroup K L i) := by
    have hσ : ∀ σ : L ≃ₐ[K] L,
        (min (ramificationNumber K L σ) ((n : ℕ∞) + 1)).toNat =
          ((Finset.range (n + 1)).filter
            fun i : ℕ => σ ∈ lowerRamificationGroup K L (i : ℤ)).card := by
      intro σ
      have hfin : min (ramificationNumber K L σ) ((n : ℕ∞) + 1) ≠ ⊤ :=
        ne_top_of_le_ne_top (by exact_mod_cast ENat.coe_ne_top (n + 1)) (min_le_right _ _)
      have hrange : ((Finset.range (n + 1)).filter
          fun i : ℕ => σ ∈ lowerRamificationGroup K L (i : ℤ)) =
          Finset.range ((min (ramificationNumber K L σ) ((n : ℕ∞) + 1)).toNat) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range]
        rw [show ((i : ℤ)) = ((i + 1 : ℕ) : ℤ) - 1 by push_cast; ring,
          mem_lowerRamificationGroup_sub_one_iff]
        constructor
        · rintro ⟨hin, hle⟩
          have h2 : ((i + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) + 1 := by
            have : i + 1 ≤ n + 1 := by omega
            exact_mod_cast this
          have hmin := le_min hle h2
          rw [← ENat.coe_toNat hfin] at hmin
          have : i + 1 ≤ (min (ramificationNumber K L σ) ((n : ℕ∞) + 1)).toNat := by
            exact_mod_cast hmin
          omega
        · intro hi
          have hmin : ((i + 1 : ℕ) : ℕ∞) ≤
              min (ramificationNumber K L σ) ((n : ℕ∞) + 1) := by
            rw [← ENat.coe_toNat hfin]
            have : i + 1 ≤ (min (ramificationNumber K L σ) ((n : ℕ∞) + 1)).toNat := by
              omega
            exact_mod_cast this
          refine ⟨?_, hmin.trans (min_le_left _ _)⟩
          have h2 := hmin.trans (min_le_right _ _)
          have : i + 1 ≤ n + 1 := by exact_mod_cast h2
          omega
      rw [hrange, Finset.card_range]
    calc ∑ σ : L ≃ₐ[K] L, (min (ramificationNumber K L σ) ((n : ℕ∞) + 1)).toNat
        = ∑ σ : L ≃ₐ[K] L, ((Finset.range (n + 1)).filter
            fun i : ℕ => σ ∈ lowerRamificationGroup K L (i : ℤ)).card :=
          Finset.sum_congr rfl fun σ _ => hσ σ
      _ = ∑ σ : L ≃ₐ[K] L, ∑ i ∈ Finset.range (n + 1),
            if σ ∈ lowerRamificationGroup K L (i : ℤ) then 1 else 0 := by
          simp only [Finset.card_filter]
      _ = ∑ i ∈ Finset.range (n + 1), ∑ σ : L ≃ₐ[K] L,
            if σ ∈ lowerRamificationGroup K L (i : ℤ) then 1 else 0 := Finset.sum_comm
      _ = ∑ i ∈ Finset.range (n + 1), Nat.card (lowerRamificationGroup K L i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.card_filter, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h0 : (Nat.card (lowerRamificationGroup K L 0) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := lowerRamificationGroup K L 0)).ne'
  have hcast := congrArg (fun m : ℕ => (m : ℝ)) hnat
  push_cast at hcast
  rw [hcast, herbrandPhi_natCast K L n]
  field_simp
  ring

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
