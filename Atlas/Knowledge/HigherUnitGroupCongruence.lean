import Mathlib
import Atlas.Knowledge.HigherUnitGroup

/-!
# congruence modulo the maximal ideal in the first higher unit group

The first higher unit group `U₁ = 1 + 𝓂` read as a congruence: a unit lies in it iff it is
congruent to `1` modulo the maximal ideal, and two elements of valuation one are congruent
iff their ratio lies in it. This is the bridge that lets a congruence
`valuation K (x - y) < 1` between units be carried as a subgroup membership `x⁻¹ * y ∈ U₁`,
where products, inverses and powers of congruences are the subgroup's closure — the form in
which `Atlas.Knowledge.LocalHilbertSymbolTameFormula` assembles the tame formula from its
unit-uniformizer case.

## Main statements

* `mem_higherUnitGroup_one_iff` — `x ∈ higherUnitGroup K 1 ↔ valuation K ((x : K) - 1) < 1`;
  proved.
* `inv_mul_mem_higherUnitGroup_one_iff` — for `x` of valuation one,
  `x⁻¹ * y ∈ higherUnitGroup K 1 ↔ valuation K ((x : K) - y) < 1`; proved.

## Implementation notes

The first lemma carries no valuation hypothesis: a unit whose valuation is not `1` is off
`U₁` and off the congruence alike, since `x - 1` then has the valuation of `x` or of `1`,
whichever is larger. The forward direction unwinds `Atlas.Knowledge.mem_higherUnitGroup_iff`
to an integer unit and reads the maximal-ideal membership as a nonunit, hence valuation not
`1`; the reverse builds the integer unit from valuation one, which
`Valuation.map_add_eq_of_lt_right` extracts from the congruence. The second lemma is the
first at `x⁻¹ * y` with `Valuation.map_sub_swap`. The item is stated over any valued field,
as `Atlas.Knowledge.HigherUnitGroup` is.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K]

/-- A unit lies in `U₁ = 1 + 𝓂` iff it is congruent to `1` modulo the maximal ideal, with no
hypothesis on its valuation: off the valuation-one units both sides fail. -/
theorem mem_higherUnitGroup_one_iff (x : Kˣ) :
    x ∈ higherUnitGroup K 1 ↔ valuation K ((x : K) - 1) < 1 := by
  rw [mem_higherUnitGroup_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [PNat.one_coe, pow_one (𝓂[K] : Ideal 𝒪[K])] at hu
    have hne : valuation K (((u : 𝒪[K]) - 1 : 𝒪[K]) : K) ≠ 1 := fun heq =>
      (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hu))
        ((Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mpr heq)
    have hle : valuation K (((u : 𝒪[K]) - 1 : 𝒪[K]) : K) ≤ 1 :=
      (Valuation.mem_integer_iff _ _).mp ((u : 𝒪[K]) - 1).2
    exact lt_of_le_of_ne hle hne
  · intro hlt
    have hx1 : valuation K (x : K) = 1 := by
      have h1 : valuation K (x : K) = valuation K (((x : K) - 1) + 1) := by rw [sub_add_cancel]
      rw [h1, Valuation.map_add_eq_of_lt_right _ (by rw [map_one]; exact hlt), map_one]
    have hxint : (x : K) ∈ 𝒪[K] := (Valuation.mem_integer_iff _ _).mpr hx1.le
    have hxunit : IsUnit (⟨(x : K), hxint⟩ : 𝒪[K]) := by
      rw [(Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one]
      exact hx1
    obtain ⟨u, hu⟩ := hxunit
    refine ⟨u, ?_, ?_⟩
    · rw [PNat.one_coe, pow_one (𝓂[K] : Ideal 𝒪[K]), IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one]
      rw [hu]
      exact hlt.ne
    · ext
      rw [Units.coe_map, hu]
      rfl

/-- Two elements of valuation one are congruent modulo the maximal ideal iff their ratio lies
in `U₁`: `x⁻¹ y - 1 = x⁻¹ (y - x)`, and `x⁻¹` has valuation one. -/
theorem inv_mul_mem_higherUnitGroup_one_iff (x y : Kˣ) (hx : valuation K (x : K) = 1) :
    x⁻¹ * y ∈ higherUnitGroup K 1 ↔ valuation K ((x : K) - y) < 1 := by
  rw [mem_higherUnitGroup_one_iff]
  have h1 : ((x⁻¹ * y : Kˣ) : K) - 1 = ((x : K))⁻¹ * ((y : K) - x) := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_sub, inv_mul_cancel₀ x.ne_zero]
  rw [h1, map_mul, map_inv₀, hx, inv_one, one_mul, Valuation.map_sub_swap]

end Atlas.Knowledge
