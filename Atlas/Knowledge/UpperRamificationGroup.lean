import Mathlib
import Atlas.Knowledge.HerbrandPsi

/-!
# upper-numbering ramification group

The ramification filtration of a finite Galois extension of local fields in the upper
numbering: `G^v = G_{ψ (v)}`, the lower filtration read through the inverse Herbrand function
`Atlas.Knowledge.HerbrandPsi`. The lower numbering is adapted to subgroups—`H_i = G_i ∩ H`—and
the upper numbering to quotients: the ramification groups of a quotient are the images of the
`G^v`, which is the compatibility proved here and the reason the filtration of an infinite
Galois group, `Atlas.Knowledge.RamificationFiltration`, is defined in the upper numbering.

## Main definitions

* `upperRamificationGroup` — `G^v = G_{ψ (v)}` as a subgroup of `L ≃ₐ[K] L`.

## Main statements

* `upperRamificationGroup_zero` — `G^0 = G_0`, the inertia end of the filtration.
* `upperRamificationGroup_antitone` — the family decreases in `v`.
* `map_upperRamificationGroup` — compatibility with quotients.
* `herbrandPsi_eq_integral` — the source's direct description
  `ψ (v) = ∫ w in 0..v, (G^0 : G^w)`.

## Implementation notes

`G^v` is `Atlas.Knowledge.realLowerRamificationGroup` at `ψ (v)` by definition, so the junk
regions of the two ingredients compose: below `v = -1` the value is the whole group, and
without `FiniteDimensional K L` the function `ψ` is junk and the numbering with it—the
statements beyond the definition assume finiteness. The quotient compatibility is stated over
an abstract tower `K ⊆ E ⊆ L`, with `ValuativeExtension K E` pinning the valuation of `E`, as
in `Atlas.Knowledge.HerbrandPhi`. The integral description is proved the way this project
proves every statement about the piecewise-affine Herbrand functions, derivative-free: across
the image under `herbrandPhi K L` of an integer step the integrand is constant—the index of
`lowerRamificationGroup K L (n + 1)` in `lowerRamificationGroup K L 0` as a ratio of
cardinalities, the reciprocal of the slope of `herbrandPhi K L` there—so the integral out to
the image of `u` grows by exactly `u - n` across the step; two-sided induction from
`herbrandPhi_zero` pins the integer breakpoints, and any `v` lands in some step through
`herbrandPsi K L v`.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic
  local fields*, J. London Math. Soc. **112** (2025), e70402.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] (L : Type*) [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L]

/-- The **upper-numbering ramification group** `G^v = G_{ψ (v)}`: the lower filtration
renumbered through the inverse Herbrand function
([Serre 1979, Chap. IV, §3, p.74][Serre1979]). -/
noncomputable def upperRamificationGroup (v : ℝ) : Subgroup (L ≃ₐ[K] L) :=
  realLowerRamificationGroup K L (herbrandPsi K L v)

instance (v : ℝ) : (upperRamificationGroup K L v).Normal :=
  inferInstanceAs ((realLowerRamificationGroup K L (herbrandPsi K L v)).Normal)

variable [FiniteDimensional K L]

/-- At `v = 0` the two numberings agree: `G^0 = G_0` is the inertia end of the filtration
([Serre 1979, Chap. IV, §3, p.74][Serre1979]). -/
theorem upperRamificationGroup_zero :
    upperRamificationGroup K L 0 = lowerRamificationGroup K L 0 := by
  rw [upperRamificationGroup, herbrandPsi_zero, realLowerRamificationGroup, Int.ceil_zero]

/-- The upper-numbering ramification groups decrease in `v`
([Serre 1979, Chap. IV, §3, p.74][Serre1979]). -/
theorem upperRamificationGroup_antitone : Antitone (upperRamificationGroup K L) :=
  fun _ _ h =>
    realLowerRamificationGroup_antitone K L ((herbrandPsi_strictMono K L).monotone h)

section Tower

variable (E : Type*) [Field E] [ValuativeRel E] [Algebra K E] [Algebra E L]
  [IsScalarTower K E L] [ValuativeExtension K E] [Algebra.IsAlgebraic E L]

/-- Compatibility of the upper numbering with quotients: for a normal subextension `E` of a
finite Galois extension `L` of a mixed-characteristic local field `K`, the image of `G^v`
under restriction to `E` is the `v`th upper-numbering ramification group of `E` over
`K`—same index, no renumbering; this is what the upper numbering is for. Herbrand's theorem
at `ψ_{L/K} (v)`, the index unwound by the transitivity of `ψ`
([Serre 1979, Chap. IV, §3, Prop. 14, p.74][Serre1979];
[Hyeon 2025, §2, (2), p.7][Hyeon2025]). -/
theorem map_upperRamificationGroup [TopologicalSpace K] [IsMixedCharLocalField K]
    [IsGalois K L] [Normal K E] (v : ℝ) :
    Subgroup.map (AlgEquiv.restrictNormalHom E) (upperRamificationGroup K L v) =
      upperRamificationGroup K E v := by
  haveI : FiniteDimensional K E := FiniteDimensional.left K E L
  haveI : FiniteDimensional E L := Module.Finite.right K E L
  rw [upperRamificationGroup, upperRamificationGroup, map_realLowerRamificationGroup K L E,
    herbrandPsi_comp K L E, herbrandPhi_herbrandPsi]

end Tower

private theorem upper_integrand_monotone :
    Monotone (fun w : ℝ =>
      (Nat.card (upperRamificationGroup K L 0) : ℝ) /
        (Nat.card (upperRamificationGroup K L w) : ℝ)) := by
  intro w w' h
  have hcard : Nat.card (upperRamificationGroup K L w') ≤
      Nat.card (upperRamificationGroup K L w) :=
    Nat.card_le_card_of_injective _
      (Subgroup.inclusion_injective (upperRamificationGroup_antitone K L h))
  have h0 : 0 < Nat.card (upperRamificationGroup K L w') := Nat.card_pos
  dsimp only
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by exact_mod_cast h0)
    (by exact_mod_cast hcard)

private theorem upper_integrand_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable
      (fun w : ℝ =>
        (Nat.card (upperRamificationGroup K L 0) : ℝ) /
          (Nat.card (upperRamificationGroup K L w) : ℝ))
      MeasureTheory.volume a b :=
  (upper_integrand_monotone K L).intervalIntegrable

/-- For `u` between `n` and `n + 1`, the integral of the reciprocal upper index out to
`herbrandPhi K L u` exceeds its value at `herbrandPhi K L n` by exactly `u - n`: the integrand
is constant on the image of the step, the reciprocal of the slope of `herbrandPhi K L`. -/
private theorem integral_upper_integrand_eq (n : ℤ) {u : ℝ} (h1 : (n : ℝ) ≤ u)
    (h2 : u ≤ n + 1) :
    (∫ w in (0 : ℝ)..(herbrandPhi K L u),
      (Nat.card (upperRamificationGroup K L 0) : ℝ) /
        (Nat.card (upperRamificationGroup K L w) : ℝ)) =
      (∫ w in (0 : ℝ)..(herbrandPhi K L n),
        (Nat.card (upperRamificationGroup K L 0) : ℝ) /
          (Nat.card (upperRamificationGroup K L w) : ℝ)) + (u - n) := by
  have hphi : herbrandPhi K L n ≤ herbrandPhi K L u := (herbrandPhi_strictMono K L).monotone h1
  have key := intervalIntegral.integral_add_adjacent_intervals
    (upper_integrand_intervalIntegrable K L 0 (herbrandPhi K L n))
    (upper_integrand_intervalIntegrable K L (herbrandPhi K L n) (herbrandPhi K L u))
  have hcongr : (∫ w in (herbrandPhi K L n)..(herbrandPhi K L u),
      (Nat.card (upperRamificationGroup K L 0) : ℝ) /
        (Nat.card (upperRamificationGroup K L w) : ℝ)) =
      ∫ w in (herbrandPhi K L n)..(herbrandPhi K L u),
        (Nat.card (lowerRamificationGroup K L 0) : ℝ) /
          (Nat.card (lowerRamificationGroup K L (n + 1)) : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro w hw
    rw [Set.uIoc_of_le hphi] at hw
    have hψ1 : (n : ℝ) < herbrandPsi K L w := by
      have h := herbrandPsi_strictMono K L hw.1
      rwa [herbrandPsi_herbrandPhi] at h
    have hψ2 : herbrandPsi K L w ≤ (n : ℝ) + 1 := by
      have hw2 : w ≤ herbrandPhi K L ((n : ℝ) + 1) :=
        hw.2.trans ((herbrandPhi_strictMono K L).monotone h2)
      have h := (herbrandPsi_strictMono K L).monotone hw2
      rwa [herbrandPsi_herbrandPhi] at h
    rw [upperRamificationGroup_zero, upperRamificationGroup,
      realLowerRamificationGroup_eq K L (i := n + 1) (by push_cast; linarith)
        (by push_cast; linarith)]
  rw [hcongr, intervalIntegral.integral_const, smul_eq_mul] at key
  have hstep := herbrandPhi_eq_add_of_mem_Icc_int K L (n := n) h1 h2
  have hc1 : (Nat.card (lowerRamificationGroup K L (n + 1)) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := lowerRamificationGroup K L (n + 1))).ne'
  have hc0 : (Nat.card (lowerRamificationGroup K L 0) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := lowerRamificationGroup K L 0)).ne'
  have hmul : (herbrandPhi K L u - herbrandPhi K L n) *
      ((Nat.card (lowerRamificationGroup K L 0) : ℝ) /
        (Nat.card (lowerRamificationGroup K L (n + 1)) : ℝ)) = u - n := by
    rw [hstep]
    field_simp
    ring
  linarith [key, hmul]

/-- The integral of the reciprocal upper index out to `herbrandPhi K L n` is `n`, by
two-sided induction along the breakpoints from `herbrandPhi_zero`. -/
private theorem integral_upper_integrand_intCast (n : ℤ) :
    (∫ w in (0 : ℝ)..(herbrandPhi K L n),
      (Nat.card (upperRamificationGroup K L 0) : ℝ) /
        (Nat.card (upperRamificationGroup K L w) : ℝ)) = n := by
  induction n with
  | zero =>
    rw [Int.cast_zero, herbrandPhi_zero]
    simp
  | succ k ih =>
    have key := integral_upper_integrand_eq K L (n := (k : ℤ)) (u := (((k : ℤ) + 1 : ℤ) : ℝ))
      (by push_cast; linarith) (by push_cast; linarith)
    rw [ih] at key
    push_cast at key ⊢
    linarith [key]
  | pred k ih =>
    have key := integral_upper_integrand_eq K L (n := -(k : ℤ) - 1) (u := ((-(k : ℤ) : ℤ) : ℝ))
      (by push_cast; linarith) (by push_cast; linarith)
    rw [ih] at key
    push_cast at key ⊢
    linarith [key]

/-- The source's direct description of the inverse Herbrand function through the upper
numbering: `ψ (v) = ∫ w in 0..v, (G^0 : G^w)`, the index rendered as a ratio of cardinalities
([Serre 1979, Chap. IV, §3, p.74][Serre1979]). -/
theorem herbrandPsi_eq_integral (v : ℝ) :
    herbrandPsi K L v = ∫ w in (0 : ℝ)..v,
      (Nat.card (upperRamificationGroup K L 0) : ℝ) /
        (Nat.card (upperRamificationGroup K L w) : ℝ) := by
  have hv : herbrandPhi K L (herbrandPsi K L v) = v := herbrandPhi_herbrandPsi K L v
  set u := herbrandPsi K L v with hu
  have h1 : ((⌈u⌉ - 1 : ℤ) : ℝ) ≤ u := by
    push_cast
    linarith [Int.ceil_lt_add_one u]
  have h2 : u ≤ ((⌈u⌉ - 1 : ℤ) : ℝ) + 1 := by
    push_cast
    linarith [Int.le_ceil u]
  have key := integral_upper_integrand_eq K L (n := ⌈u⌉ - 1) h1 h2
  rw [hv, integral_upper_integrand_intCast K L (⌈u⌉ - 1)] at key
  rw [key]
  push_cast
  ring

end Atlas.Knowledge
