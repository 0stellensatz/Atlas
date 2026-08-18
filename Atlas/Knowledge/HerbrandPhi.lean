import Mathlib
import Atlas.Knowledge.MapMaximalIdealEqPowCardInertia
import Atlas.Knowledge.RamificationNumber
import Atlas.Knowledge.RamificationNumberFiberSum
import Atlas.Knowledge.RamificationNumberRestrictScalars
import Atlas.Knowledge.RealLowerRamificationGroup
import Atlas.Knowledge.RestrictScalarsHomRangeEqKer

/-!
# Herbrand function φ

The Herbrand function of a finite Galois extension of local fields: the piecewise-linear
homeomorphism `φ (u) = ∫ t in 0..u, dt / (G_0 : G_t)` of the real line that converts the lower
numbering of the ramification filtration into the upper numbering. This file defines `φ` as an
interval integral through `Atlas.Knowledge.realLowerRamificationGroup`, proves the calculus
facts that make it a change of numbering—`φ (0) = 0`, strict monotonicity, continuity,
bijectivity—and proves **Herbrand's theorem**, the statement the function exists for: the
image of `G_u` in a quotient of the Galois group is the ramification group of the quotient at
index `φ (u)`, the index computed over the intermediate field, together with the transitivity
`φ_{L/K} = φ_{E/K} ∘ φ_{L/E}` it entails. The inverse function is `Atlas.Knowledge.HerbrandPsi`,
and the numbering `φ` produces is `Atlas.Knowledge.UpperRamificationGroup`. The file also carries
the evaluation of `φ` at integer arguments and its equivalent form as a sum of truncated
ramification numbers `i_G`.

## Main definitions

* `herbrandPhi` — `φ (u) = ∫ t in 0..u, Nat.card (G_t) / Nat.card (G_0)`.

## Main statements

* `herbrandPhi_zero`, `herbrandPhi_strictMono`, `herbrandPhi_continuous`,
  `herbrandPhi_bijective` — the calculus API, the last three under `FiniteDimensional K L`.
* `herbrandPhi_eq_add_of_mem_Icc` — `φ` is affine on `[n, n + 1]`, slope `1 / (G_0 : G_{n+1})`.
* `herbrandPhi_natCast` — the evaluation at integers: `φ (n) = (g_0 + ⋯ + g_{n}) / g_0 - 1`.
* `sum_toNat_min_ramificationNumber` — the `i_G` form: `Σ_σ min (i_G σ, n + 1) = g_0 (φ (n) + 1)`.
* `ramificationNumber_restrictNormal_sub_one_eq_herbrandPhi` — Lemma 4: the ramification
  number of a quotient automorphism through `φ`, at a lift of maximal ramification number.
* `map_realLowerRamificationGroup` — Herbrand's theorem.
* `card_lowerRamificationGroup_eq_card_mul_card_map` — the order of `G_i` as the order of the
  filtration over `E` times the order of the image of `G_i` under restriction, the counting
  step of the transitivity proof.
* `herbrandPhi_comp` — transitivity in a tower: `φ_{L/K} = φ_{E/K} ∘ φ_{L/E}`.

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
to the canonical extension, which is what the two statements are about. The source proves the
transitivity by comparing derivatives; the proof here is derivative-free: both sides are
piecewise affine with the same value at `0`, and on each `[n, n + 1]` their slopes agree by
Herbrand's theorem combined with the counting identity
`card_lowerRamificationGroup_eq_card_mul_card_map`.

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

/-- The Herbrand function is affine on `[n, n + 1]` for every integer `n`, of slope
`1 / (G_0 : G_{n+1})`—the piecewise-linear description of `φ`, extended from the source's
nonnegative range over every integer, the junk region below `-1` included
([Serre 1979, Chap. IV, §3, p.73][Serre1979]). -/
theorem herbrandPhi_eq_add_of_mem_Icc_int {n : ℤ} {u : ℝ} (h1 : (n : ℝ) ≤ u) (h2 : u ≤ n + 1) :
    herbrandPhi K L u = herbrandPhi K L n +
      (u - n) * ((Nat.card (lowerRamificationGroup K L (n + 1)) : ℝ) /
        (Nat.card (lowerRamificationGroup K L 0) : ℝ)) := by
  have key := intervalIntegral.integral_add_adjacent_intervals
    (integrand_intervalIntegrable K L 0 n) (integrand_intervalIntegrable K L n u)
  have hcongr : (∫ t in (n : ℝ)..u,
      (Nat.card (realLowerRamificationGroup K L t) : ℝ) /
        (Nat.card (lowerRamificationGroup K L 0) : ℝ)) =
      ∫ t in (n : ℝ)..u,
        (Nat.card (lowerRamificationGroup K L (n + 1)) : ℝ) /
          (Nat.card (lowerRamificationGroup K L 0) : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t ht
    rw [Set.uIoc_of_le h1] at ht
    rw [realLowerRamificationGroup_eq K L (i := n + 1)
      (by push_cast; linarith [ht.1]) (by push_cast; linarith [ht.2])]
  rw [hcongr, intervalIntegral.integral_const, smul_eq_mul] at key
  have key' : herbrandPhi K L n + (u - (n : ℝ)) *
      ((Nat.card (lowerRamificationGroup K L (n + 1)) : ℝ) /
        (Nat.card (lowerRamificationGroup K L 0) : ℝ)) = herbrandPhi K L u := key
  linarith [key']

/-- The Herbrand function is affine on each interval `[n, n + 1]`, of slope
`1 / (G_0 : G_{n+1})`—the explicit piecewise-linear description of `φ`, whose display the
source states for positive `n`; `n = 0` is admitted here
([Serre 1979, Chap. IV, §3, p.73][Serre1979]). -/
theorem herbrandPhi_eq_add_of_mem_Icc {n : ℕ} {u : ℝ} (h1 : (n : ℝ) ≤ u) (h2 : u ≤ n + 1) :
    herbrandPhi K L u = herbrandPhi K L n +
      (u - n) * ((Nat.card (lowerRamificationGroup K L (n + 1)) : ℝ) /
        (Nat.card (lowerRamificationGroup K L 0) : ℝ)) := by
  exact_mod_cast herbrandPhi_eq_add_of_mem_Icc_int K L (n := (n : ℤ))
    (by exact_mod_cast h1) (by exact_mod_cast h2)

/-- `φ (-1) = -1`: the left endpoint of the slope-one segment of `φ` on `[-1, 0]`
([Serre 1979, Chap. IV, §3, p.73][Serre1979]). -/
@[simp]
theorem herbrandPhi_neg_one : herbrandPhi K L (-1) = -1 := by
  have h0 : (Nat.card (lowerRamificationGroup K L 0) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := lowerRamificationGroup K L 0)).ne'
  have key := herbrandPhi_eq_add_of_mem_Icc_int K L (n := -1) (u := 0)
    (by norm_num) (by norm_num)
  rw [herbrandPhi_zero] at key
  norm_num [div_self h0] at key
  linarith [key]

/-- For `u ≤ -1` also `φ (u) ≤ -1`—the source's homeomorphism of `[-1, +∞)` onto itself never
maps the junk region into the working range
([Serre 1979, Chap. IV, §3, p.73][Serre1979]). -/
theorem herbrandPhi_le_neg_one {u : ℝ} (hu : u ≤ -1) : herbrandPhi K L u ≤ -1 := by
  rw [← herbrandPhi_neg_one K L]
  exact (herbrandPhi_strictMono K L).monotone hu

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

omit [ValuativeRel K] [Algebra.IsAlgebraic K L] [ValuativeRel E] [ValuativeExtension K E]
  [Algebra.IsAlgebraic E L] in
/-- The subgroup of `L ≃ₐ[K] L` fixing `E` pointwise—the range of
`AlgEquiv.restrictScalarsHom K`—is normal, being the kernel of the restriction
`AlgEquiv.restrictNormalHom E` through `Atlas.Knowledge.restrictScalarsHom_range_eq_ker`; a
theorem to apply by `haveI` where a proof needs it rather than a global instance
([Serre 1979, Chap. IV, §1, proof of Prop. 3, p.63][Serre1979]). -/
theorem restrictScalarsHom_range_normal [Normal K E] :
    ((AlgEquiv.restrictScalarsHom (S := E) (A := L) K).range).Normal :=
  restrictScalarsHom_range_eq_ker K E L ▸ MonoidHom.normal_ker _

omit [ValuativeRel E] [ValuativeExtension K E] [Algebra.IsAlgebraic E L] in
/-- Every fiber of the restriction `AlgEquiv.restrictNormalHom E` contains a representative
of maximal ramification number—the element Serre takes with `i_G (s) = j (σ)`, the coset
statement `Atlas.Knowledge.exists_maximal_ramificationNumber_representative` read on a fiber
of the restriction to a normal subextension
([Serre 1979, Chap. IV, §3, proof of Lem. 4, pp.74–75][Serre1979]). -/
theorem exists_maximal_ramificationNumber_restrictNormalHom_representative
    [FiniteDimensional K L] [IsGalois K L] [Normal K E] (σ' : E ≃ₐ[K] E) :
    ∃ σ : L ≃ₐ[K] L, AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E σ = σ' ∧
      ∀ γ : L ≃ₐ[K] L, AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E γ = σ' →
        ramificationNumber K L γ ≤ ramificationNumber K L σ := by
  have hne : Nonempty
      {σ : L ≃ₐ[K] L // AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E σ = σ'} := by
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) L σ'
    exact ⟨⟨σ, hσ⟩⟩
  obtain ⟨⟨σ, hσ⟩, hmax⟩ := Finite.exists_max
    (fun γ : {σ : L ≃ₐ[K] L // AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E σ = σ'} =>
      ramificationNumber K L (γ : L ≃ₐ[K] L))
  exact ⟨σ, hσ, fun γ hγ => hmax ⟨γ, hγ⟩⟩

/-- For a lift `σ` of maximal ramification number in the fiber of the restriction to `E` above
`σ' ≠ 1`, the ramification number of `σ'` less one is the value of the Herbrand function of
`L` over `E` at the ramification number of `σ` less one—both numbers finite away from the
identity, read into `ℝ` where `herbrandPhi` lives
([Serre 1979, Chap. IV, §3, Lem. 4, pp.74–75][Serre1979]). -/
theorem ramificationNumber_restrictNormal_sub_one_eq_herbrandPhi
    [TopologicalSpace K] [IsMixedCharLocalField K] [FiniteDimensional K L]
    [IsGalois K L] [Normal K E] {σ : L ≃ₐ[K] L} {σ' : E ≃ₐ[K] E}
    (hσ : AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E σ = σ')
    (hmax : ∀ γ : L ≃ₐ[K] L, AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E γ = σ' →
      ramificationNumber K L γ ≤ ramificationNumber K L σ)
    (hσ' : σ' ≠ 1) :
    ((ramificationNumber K E σ').toNat : ℝ) - 1 =
      herbrandPhi E L (((ramificationNumber K L σ).toNat : ℝ) - 1) := by
  classical
  haveI : FiniteDimensional K E := FiniteDimensional.left K E L
  haveI : FiniteDimensional E L := Module.Finite.right K E L
  haveI : IsGalois E L := IsGalois.tower_top_of_isGalois K E L
  haveI := restrictScalarsHom_range_normal K L E
  -- maximality in the coset form `ramificationNumber_mul_eq_min_of_maximal` consumes
  have hmax' : ∀ γ : L ≃ₐ[K] L,
      QuotientGroup.mk' (AlgEquiv.restrictScalarsHom (S := E) (A := L) K).range γ =
        QuotientGroup.mk' (AlgEquiv.restrictScalarsHom (S := E) (A := L) K).range σ →
      ramificationNumber K L γ ≤ ramificationNumber K L σ := by
    intro γ hγ
    refine hmax γ ?_
    have hker : γ⁻¹ * σ ∈ (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker := by
      rw [← restrictScalarsHom_range_eq_ker K E L]
      exact QuotientGroup.eq.mp hγ
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hker
    exact hker.trans hσ
  -- Tate's fiber sum at the inertia-order exponent, reindexed over the automorphisms over `E`
  have hsum := ramificationNumber_fiber_sum K L E
    (map_maximalIdeal_eq_pow_card_inertia K L E) σ'
  have himg : (∑ s ∈ Finset.univ.image
        (fun t : L ≃ₐ[E] L => σ * AlgEquiv.restrictScalars K t), ramificationNumber K L s) =
      ∑ t : L ≃ₐ[E] L, ramificationNumber K L (σ * AlgEquiv.restrictScalars K t) :=
    Finset.sum_image fun t₁ _ t₂ _ h =>
      AlgEquiv.restrictScalarsHom_injective K (mul_left_cancel h)
  rw [restrictNormalHom_fiber_eq K E L σ σ' hσ, himg] at hsum
  -- Serre's "in either case": every summand truncates at the maximal representative
  have hterm : ∀ t : L ≃ₐ[E] L,
      ramificationNumber K L (σ * t.restrictScalars K) =
        min (ramificationNumber E L t) (ramificationNumber K L σ) := by
    intro t
    rw [ramificationNumber_restrictScalars K L E t]
    exact ramificationNumber_mul_eq_min_of_maximal K L hmax' ⟨t.restrictScalars K, t, rfl⟩
  rw [Finset.sum_congr rfl fun t _ => hterm t] at hsum
  -- both ramification numbers are finite away from the identity
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    exact hσ' (hσ.symm.trans (map_one _))
  have hmtop : ramificationNumber K L σ ≠ ⊤ := fun h =>
    hσ1 ((ramificationNumber_eq_top_iff K L).mp h)
  have hitop : ramificationNumber K E σ' ≠ ⊤ := fun h =>
    hσ' ((ramificationNumber_eq_top_iff K E).mp h)
  set m : ℕ := (ramificationNumber K L σ).toNat
  set i' : ℕ := (ramificationNumber K E σ').toNat
  have hmcast : ((m : ℕ) : ℕ∞) = ramificationNumber K L σ := ENat.coe_toNat hmtop
  have hicast : ((i' : ℕ) : ℕ∞) = ramificationNumber K E σ' := ENat.coe_toNat hitop
  rw [← hicast, ← hmcast] at hsum
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · -- `j (σ) = 0`: the sum vanishes termwise, forcing `i_{G/H} (σ') = 0`, both sides read `-1`
    have hzero : (∑ t : L ≃ₐ[E] L, min (ramificationNumber E L t) ((m : ℕ) : ℕ∞)) = 0 := by
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [hm0, Nat.cast_zero]
      exact min_eq_right zero_le
    rw [hzero, nsmul_eq_mul, mul_eq_zero] at hsum
    have hi0 : i' = 0 := by
      rcases hsum with h | h
      · exact absurd (by exact_mod_cast h)
          (Nat.card_pos (α := lowerRamificationGroup E L 0)).ne'
      · exact_mod_cast h
    rw [hi0, hm0]
    norm_num [herbrandPhi_neg_one E L]
  · -- `j (σ) ≥ 1`: the summands are finite, and Lemma 3 over the base `E` reads off the sum
    have hfin : ∀ t : L ≃ₐ[E] L, min (ramificationNumber E L t) ((m : ℕ) : ℕ∞) ≠ ⊤ :=
      fun t => ne_top_of_le_ne_top (ENat.coe_ne_top m) (min_le_right _ _)
    have hnat : Nat.card (lowerRamificationGroup E L 0) * i' =
        ∑ t : L ≃ₐ[E] L, (min (ramificationNumber E L t) ((m : ℕ) : ℕ∞)).toNat := by
      have hcast : ((∑ t : L ≃ₐ[E] L,
            (min (ramificationNumber E L t) ((m : ℕ) : ℕ∞)).toNat : ℕ) : ℕ∞) =
          ∑ t : L ≃ₐ[E] L, min (ramificationNumber E L t) ((m : ℕ) : ℕ∞) := by
        rw [Nat.cast_sum]
        exact Finset.sum_congr rfl fun t _ => ENat.coe_toNat (hfin t)
      have h2 : ((Nat.card (lowerRamificationGroup E L 0) * i' : ℕ) : ℕ∞) =
          ((∑ t : L ≃ₐ[E] L,
            (min (ramificationNumber E L t) ((m : ℕ) : ℕ∞)).toNat : ℕ) : ℕ∞) := by
        rw [hcast, Nat.cast_mul, ← nsmul_eq_mul]
        exact hsum
      exact_mod_cast h2
    have hkey := sum_toNat_min_ramificationNumber E L (m - 1)
    rw [show ((m - 1 : ℕ) : ℕ∞) + 1 = ((m : ℕ) : ℕ∞) from by
        exact_mod_cast Nat.sub_add_cancel hm1] at hkey
    have hreal : (Nat.card (lowerRamificationGroup E L 0) : ℝ) * (i' : ℝ) =
        (Nat.card (lowerRamificationGroup E L 0) : ℝ) *
          (herbrandPhi E L ((m - 1 : ℕ) : ℝ) + 1) := by
      rw [← hkey]
      exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hnat
    have hcard0 : (Nat.card (lowerRamificationGroup E L 0) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := lowerRamificationGroup E L 0)).ne'
    have hii : (i' : ℝ) = herbrandPhi E L ((m - 1 : ℕ) : ℝ) + 1 :=
      mul_left_cancel₀ hcard0 hreal
    rw [show ((m : ℕ) : ℝ) - 1 = ((m - 1 : ℕ) : ℝ) from by
        rw [Nat.cast_sub hm1, Nat.cast_one]]
    linarith [hii]

/-- **Herbrand's theorem**: for a normal subextension `E` of a finite Galois extension `L` of
a mixed-characteristic local field `K`, the image of the real-indexed lower ramification group
`G_u` under restriction to `E` is the ramification group of `E` over `K` at index
`φ_{L/E} (u)`—the Herbrand function computed over the intermediate field
([Serre 1979, Chap. IV, §3, Lem. 5, p.75][Serre1979]). -/
theorem map_realLowerRamificationGroup [TopologicalSpace K] [IsMixedCharLocalField K]
    [FiniteDimensional K L] [IsGalois K L] [Normal K E] (u : ℝ) :
    Subgroup.map (AlgEquiv.restrictNormalHom E) (realLowerRamificationGroup K L u) =
      realLowerRamificationGroup K E (herbrandPhi E L u) := by
  classical
  haveI : FiniteDimensional K E := FiniteDimensional.left K E L
  haveI : FiniteDimensional E L := Module.Finite.right K E L
  haveI : IsGalois E L := IsGalois.tower_top_of_isGalois K E L
  by_cases hu : u ≤ -1
  · -- below `-1` both filtrations are everything, and restriction is surjective
    have hL : realLowerRamificationGroup K L u = ⊤ := by
      rw [realLowerRamificationGroup]
      exact lowerRamificationGroup_eq_top K L (Int.ceil_le.mpr (by exact_mod_cast hu))
    have hE : realLowerRamificationGroup K E (herbrandPhi E L u) = ⊤ := by
      rw [realLowerRamificationGroup]
      exact lowerRamificationGroup_eq_top K E
        (Int.ceil_le.mpr (by exact_mod_cast herbrandPhi_le_neg_one E L hu))
    rw [hL, hE, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr fun σ' =>
      AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) L σ'
  push Not at hu
  ext σ'
  simp only [Subgroup.mem_map]
  by_cases hσ' : σ' = 1
  · subst hσ'
    exact iff_of_true ⟨1, one_mem _, map_one _⟩ (one_mem _)
  obtain ⟨σ, hσ, hmax⟩ :=
    exists_maximal_ramificationNumber_restrictNormalHom_representative K L E σ'
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    exact hσ' (hσ.symm.trans (map_one _))
  have hmtop : ramificationNumber K L σ ≠ ⊤ := fun h =>
    hσ1 ((ramificationNumber_eq_top_iff K L).mp h)
  have hitop : ramificationNumber K E σ' ≠ ⊤ := fun h =>
    hσ' ((ramificationNumber_eq_top_iff K E).mp h)
  have hlem4 := ramificationNumber_restrictNormal_sub_one_eq_herbrandPhi K L E hσ hmax hσ'
  set m : ℕ := (ramificationNumber K L σ).toNat
  set i' : ℕ := (ramificationNumber K E σ').toNat
  have hmcast : ((m : ℕ) : ℕ∞) = ramificationNumber K L σ := ENat.coe_toNat hmtop
  have hicast : ((i' : ℕ) : ℕ∞) = ramificationNumber K E σ' := ENat.coe_toNat hitop
  have hceilu : 0 ≤ ⌈u⌉ := by
    have h1 : (-1 : ℤ) < ⌈u⌉ := Int.lt_ceil.mpr (by exact_mod_cast hu)
    omega
  have hceilφ : 0 ≤ ⌈herbrandPhi E L u⌉ := by
    have h1 : (-1 : ℝ) < herbrandPhi E L u := by
      rw [← herbrandPhi_neg_one E L]
      exact herbrandPhi_strictMono E L hu
    have h2 : (-1 : ℤ) < ⌈herbrandPhi E L u⌉ := Int.lt_ceil.mpr (by exact_mod_cast h1)
    omega
  calc (∃ γ ∈ realLowerRamificationGroup K L u,
        AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E γ = σ')
      ↔ σ ∈ realLowerRamificationGroup K L u := by
        constructor
        · rintro ⟨γ, hγmem, hγ⟩
          rw [realLowerRamificationGroup,
            mem_lowerRamificationGroup_iff_le_ramificationNumber] at hγmem ⊢
          exact hγmem.trans (hmax γ hγ)
        · exact fun h => ⟨σ, h, hσ⟩
    _ ↔ u ≤ (m : ℝ) - 1 := by
        rw [realLowerRamificationGroup, mem_lowerRamificationGroup_iff_le_ramificationNumber,
          ← hmcast, Nat.cast_le,
          show (⌈u⌉ + 1).toNat ≤ m ↔ ⌈u⌉ ≤ (m : ℤ) - 1 from by omega, Int.ceil_le]
        push_cast
        exact Iff.rfl
    _ ↔ herbrandPhi E L u ≤ (i' : ℝ) - 1 := by
        rw [hlem4]
        exact ((herbrandPhi_strictMono E L).le_iff_le).symm
    _ ↔ σ' ∈ realLowerRamificationGroup K E (herbrandPhi E L u) := by
        rw [realLowerRamificationGroup, mem_lowerRamificationGroup_iff_le_ramificationNumber,
          ← hicast, Nat.cast_le,
          show (⌈herbrandPhi E L u⌉ + 1).toNat ≤ i' ↔
            ⌈herbrandPhi E L u⌉ ≤ (i' : ℤ) - 1 from by omega, Int.ceil_le]
        push_cast
        exact Iff.rfl

/-- The counting identity of the transitivity proof: the order of `G_i` is the order of
`H_i`—the same filtration computed over `E`—times the order of the image of `G_i` under the
restriction to `E`. This is the first isomorphism theorem for `AlgEquiv.restrictNormalHom E`
cut down to `G_i`, whose kernel `Atlas.Knowledge.lowerRamificationGroup_map_restrictScalarsHom`
identifies with `H_i`
([Serre 1979, Chap. IV, §3, proof of Prop. 15, p.75][Serre1979]). -/
theorem card_lowerRamificationGroup_eq_card_mul_card_map [TopologicalSpace K]
    [IsMixedCharLocalField K] [FiniteDimensional K L] [Normal K E] (i : ℤ) :
    Nat.card (lowerRamificationGroup K L i) =
      Nat.card (lowerRamificationGroup E L i) *
        Nat.card (Subgroup.map (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E)
          (lowerRamificationGroup K L i)) := by
  classical
  set f := (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).comp
    (lowerRamificationGroup K L i).subtype with hf
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have hrange : f.range = Subgroup.map (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E)
      (lowerRamificationGroup K L i) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card f.ker = Nat.card (lowerRamificationGroup E L i) := by
    have h1 : f.ker = ((AlgEquiv.restrictScalarsHom (S := E) (A := L) K).range ⊓
        lowerRamificationGroup K L i).subgroupOf (lowerRamificationGroup K L i) := by
      rw [Subgroup.inf_subgroupOf_right, hf, ← MonoidHom.comap_ker,
        ← restrictScalarsHom_range_eq_ker K E L]
      rfl
    have h2 : Nat.card (((AlgEquiv.restrictScalarsHom (S := E) (A := L) K).range ⊓
        lowerRamificationGroup K L i).subgroupOf (lowerRamificationGroup K L i)) =
        Nat.card (((AlgEquiv.restrictScalarsHom (S := E) (A := L) K).range ⊓
          lowerRamificationGroup K L i : Subgroup (L ≃ₐ[K] L))) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have h3 : (AlgEquiv.restrictScalarsHom (S := E) (A := L) K).range ⊓
        lowerRamificationGroup K L i =
        Subgroup.map (AlgEquiv.restrictScalarsHom K) (lowerRamificationGroup E L i) := by
      rw [lowerRamificationGroup_map_restrictScalarsHom K L E i, inf_comm]
    rw [h1, h2, h3]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _
      (AlgEquiv.restrictScalarsHom_injective K)).toEquiv).symm
  rw [hcard, Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hker]
  exact mul_comm _ _

/-- The composite `φ_{E/K} ∘ φ_{L/E}` is affine on `[n, n + 1]`, its slope the product of the
slope of `φ_{L/E}` there and the slope of `φ_{E/K}` on the image interval: `herbrandPhi E L`
maps `[n, n + 1]` onto an interval on whose interior the integrand of `herbrandPhi K E` is the
constant that Herbrand's theorem `Atlas.Knowledge.map_realLowerRamificationGroup` computes
from the image of `G_{n + 1}`
([Serre 1979, Chap. IV, §3, proof of Prop. 15, p.75][Serre1979]). -/
theorem herbrandPhi_herbrandPhi_eq_add_of_mem_Icc_int [TopologicalSpace K]
    [IsMixedCharLocalField K] [FiniteDimensional K L] [IsGalois K L] [Normal K E]
    {n : ℤ} {u : ℝ} (h1 : (n : ℝ) ≤ u) (h2 : u ≤ n + 1) :
    herbrandPhi K E (herbrandPhi E L u) = herbrandPhi K E (herbrandPhi E L n) +
      (u - n) * ((Nat.card (lowerRamificationGroup E L (n + 1)) : ℝ) /
        (Nat.card (lowerRamificationGroup E L 0) : ℝ)) *
      ((Nat.card (Subgroup.map (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E)
          (lowerRamificationGroup K L (n + 1))) : ℝ) /
        (Nat.card (lowerRamificationGroup K E 0) : ℝ)) := by
  classical
  haveI : FiniteDimensional K E := FiniteDimensional.left K E L
  haveI : FiniteDimensional E L := Module.Finite.right K E L
  have hab : herbrandPhi E L n ≤ herbrandPhi E L u := (herbrandPhi_strictMono E L).monotone h1
  have key := intervalIntegral.integral_add_adjacent_intervals
    (integrand_intervalIntegrable K E 0 (herbrandPhi E L n))
    (integrand_intervalIntegrable K E (herbrandPhi E L n) (herbrandPhi E L u))
  have hcongr : (∫ x in (herbrandPhi E L n)..(herbrandPhi E L u),
      (Nat.card (realLowerRamificationGroup K E x) : ℝ) /
        (Nat.card (lowerRamificationGroup K E 0) : ℝ)) =
      ∫ x in (herbrandPhi E L n)..(herbrandPhi E L u),
        (Nat.card (Subgroup.map (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E)
            (lowerRamificationGroup K L (n + 1))) : ℝ) /
          (Nat.card (lowerRamificationGroup K E 0) : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    have hs : herbrandPhi E L (Function.invFun (herbrandPhi E L) x) = x :=
      Function.rightInverse_invFun (herbrandPhi_bijective E L).surjective x
    set s := Function.invFun (herbrandPhi E L) x with hsdef
    have hs1 : (n : ℝ) < s := by
      by_contra hc
      push Not at hc
      have hle : herbrandPhi E L s ≤ herbrandPhi E L n :=
        (herbrandPhi_strictMono E L).monotone hc
      rw [hs] at hle
      exact absurd hx.1 (not_lt.mpr hle)
    have hs2 : s ≤ (n : ℝ) + 1 := by
      by_contra hc
      push Not at hc
      have hlt : herbrandPhi E L ((n : ℝ) + 1) < herbrandPhi E L s :=
        herbrandPhi_strictMono E L hc
      rw [hs] at hlt
      have hub : herbrandPhi E L u ≤ herbrandPhi E L ((n : ℝ) + 1) :=
        (herbrandPhi_strictMono E L).monotone h2
      exact absurd hx.2 (not_le.mpr (lt_of_le_of_lt hub hlt))
    have herb := map_realLowerRamificationGroup K L E s
    rw [hs, realLowerRamificationGroup_eq K L (i := n + 1)
      (by push_cast; linarith) (by push_cast; linarith)] at herb
    rw [← herb]
  rw [hcongr, intervalIntegral.integral_const, smul_eq_mul] at key
  have key' : herbrandPhi K E (herbrandPhi E L n) +
      (herbrandPhi E L u - herbrandPhi E L n) *
        ((Nat.card (Subgroup.map (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E)
            (lowerRamificationGroup K L (n + 1))) : ℝ) /
          (Nat.card (lowerRamificationGroup K E 0) : ℝ)) =
      herbrandPhi K E (herbrandPhi E L u) := key
  have hEL := herbrandPhi_eq_add_of_mem_Icc_int E L (n := n) h1 h2
  rw [← key', hEL]
  ring

/-- Transitivity of the Herbrand function in a tower: `φ_{L/K} = φ_{E/K} ∘ φ_{L/E}`
([Serre 1979, Chap. IV, §3, Prop. 15, p.74][Serre1979]). -/
theorem herbrandPhi_comp [TopologicalSpace K] [IsMixedCharLocalField K]
    [FiniteDimensional K L] [IsGalois K L] [Normal K E] (u : ℝ) :
    herbrandPhi K L u = herbrandPhi K E (herbrandPhi E L u) := by
  classical
  haveI : FiniteDimensional K E := FiniteDimensional.left K E L
  haveI : FiniteDimensional E L := Module.Finite.right K E L
  -- the image of `G_0` downstairs is the whole zeroth group of `E` over `K`
  have hmap0 : Subgroup.map (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E)
      (lowerRamificationGroup K L 0) = lowerRamificationGroup K E 0 := by
    have h := map_realLowerRamificationGroup K L E 0
    simp only [herbrandPhi_zero, realLowerRamificationGroup, Int.ceil_zero] at h
    exact h
  -- Serre's slope identity, from the counting identity at `j` and at `0`
  have hslope : ∀ j : ℤ,
      (Nat.card (lowerRamificationGroup K L j) : ℝ) /
        (Nat.card (lowerRamificationGroup K L 0) : ℝ) =
      (Nat.card (lowerRamificationGroup E L j) : ℝ) /
        (Nat.card (lowerRamificationGroup E L 0) : ℝ) *
      ((Nat.card (Subgroup.map (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E)
          (lowerRamificationGroup K L j)) : ℝ) /
        (Nat.card (lowerRamificationGroup K E 0) : ℝ)) := by
    intro j
    have hj := card_lowerRamificationGroup_eq_card_mul_card_map K L E j
    have h0 := card_lowerRamificationGroup_eq_card_mul_card_map K L E 0
    rw [hmap0] at h0
    have hj' : (Nat.card (lowerRamificationGroup K L j) : ℝ) =
        (Nat.card (lowerRamificationGroup E L j) : ℝ) *
          (Nat.card (Subgroup.map (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E)
            (lowerRamificationGroup K L j)) : ℝ) := by exact_mod_cast hj
    have h0' : (Nat.card (lowerRamificationGroup K L 0) : ℝ) =
        (Nat.card (lowerRamificationGroup E L 0) : ℝ) *
          (Nat.card (lowerRamificationGroup K E 0) : ℝ) := by exact_mod_cast h0
    rw [hj', h0', div_mul_div_comm]
  -- the step across `[n, n + 1]`, both sides
  have hstep : ∀ n : ℤ,
      herbrandPhi K L ((n + 1 : ℤ) : ℝ) - herbrandPhi K L (n : ℝ) =
        herbrandPhi K E (herbrandPhi E L ((n + 1 : ℤ) : ℝ)) -
          herbrandPhi K E (herbrandPhi E L (n : ℝ)) := by
    intro n
    have hL := herbrandPhi_eq_add_of_mem_Icc_int K L (n := n) (u := ((n + 1 : ℤ) : ℝ))
      (by push_cast; linarith) (by push_cast; linarith)
    have hC := herbrandPhi_herbrandPhi_eq_add_of_mem_Icc_int K L E (n := n)
      (u := ((n + 1 : ℤ) : ℝ)) (by push_cast; linarith) (by push_cast; linarith)
    rw [hL, hC, hslope (n + 1)]
    ring
  -- transitivity at the integers, by two-sided induction from `φ (0) = 0`
  have hint : ∀ n : ℤ, herbrandPhi K L (n : ℝ) = herbrandPhi K E (herbrandPhi E L (n : ℝ)) := by
    intro n
    induction n with
    | zero => simp
    | succ k ih => linarith [hstep (k : ℤ), ih]
    | pred k ih =>
      have h := hstep (-(k : ℤ) - 1)
      rw [show (-(k : ℤ) - 1 + 1 : ℤ) = -(k : ℤ) by omega] at h
      linarith [h, ih]
  -- an arbitrary point, placed on `[⌈u⌉ - 1, ⌈u⌉]`
  have h1 : ((⌈u⌉ - 1 : ℤ) : ℝ) ≤ u := by
    push_cast
    linarith [Int.ceil_lt_add_one u]
  have h2 : u ≤ ((⌈u⌉ - 1 : ℤ) : ℝ) + 1 := by
    push_cast
    linarith [Int.le_ceil u]
  have hL := herbrandPhi_eq_add_of_mem_Icc_int K L (n := ⌈u⌉ - 1) h1 h2
  have hC := herbrandPhi_herbrandPhi_eq_add_of_mem_Icc_int K L E (n := ⌈u⌉ - 1) h1 h2
  rw [hL, hC, hint (⌈u⌉ - 1), hslope (⌈u⌉ - 1 + 1)]
  ring

end Tower

end Atlas.Knowledge
