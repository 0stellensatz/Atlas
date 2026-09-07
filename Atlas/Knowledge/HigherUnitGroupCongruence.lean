import Mathlib
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.RationalIntegerValuation

/-!
# congruence modulo the maximal ideal in the first higher unit group

The first higher unit group `U 1 (K) = 1 + 𝓂[K]` read as a congruence: a unit lies in it iff
it is congruent to `1` modulo the maximal ideal, and for `x` of valuation one, `y` is
congruent to `x` iff `x⁻¹ * y` lies in it. This is the bridge that lets a congruence
`valuation K (x - y) < 1` between units be carried as a subgroup membership
`x⁻¹ * y ∈ U 1 (K)`, where products, inverses and powers of congruences are the subgroup's
closure — the form in which `Atlas.Knowledge.LocalHilbertSymbolTameFormula` assembles the
tame formula from its unit-uniformizer case.

## Main statements

* `mem_higherUnitGroup_one_iff` — `x ∈ higherUnitGroup K 1 ↔ valuation K ((x : K) - 1) < 1`;
  proved.
* `inv_mul_mem_higherUnitGroup_one_iff` — for `x` of valuation one,
  `x⁻¹ * y ∈ higherUnitGroup K 1 ↔ valuation K ((x : K) - y) < 1`; proved.

## Implementation notes

The first lemma carries no valuation hypothesis: a unit whose valuation is not `1` is off
`U 1 (K)` and off the congruence alike, since `x - 1` then has the valuation of `x` or of
`1`, whichever is larger. The forward direction reads the carrier element `x - 1` of the
maximal ideal through `Atlas.Knowledge.valuation_lt_one_of_mem_maximalIdeal`; the reverse
unwinds `Atlas.Knowledge.mem_higherUnitGroup_iff` and builds the integer unit from valuation
one, which `Valuation.map_add_eq_of_lt_right` extracts from the congruence. The second lemma
is the first at `x⁻¹ * y` with `Valuation.map_sub_swap`; only `x` needs valuation one, since
when `y` has another valuation both sides fail. The item is stated over any valued field, as
`Atlas.Knowledge.HigherUnitGroup` is.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K]

/-- A unit lies in `U 1 (K) = 1 + 𝓂[K]` iff it is congruent to `1` modulo the maximal ideal,
with no hypothesis on its valuation: off the valuation-one units both sides fail. -/
theorem mem_higherUnitGroup_one_iff (x : Kˣ) :
    x ∈ higherUnitGroup K 1 ↔ valuation K ((x : K) - 1) < 1 := by
  constructor
  · rintro ⟨y, hy⟩
    have h1 : ((y : ↥𝒪[K]) : K) = (x : K) - 1 := by rw [← hy]; ring
    rw [← h1]
    exact valuation_lt_one_of_mem_maximalIdeal _ (Ideal.pow_le_self one_ne_zero y.2)
  · intro hlt
    rw [mem_higherUnitGroup_iff]
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

/-- An element `y` is congruent to an element `x` of valuation one modulo the maximal ideal
iff `x⁻¹ * y` lies in `U 1 (K)`: `x⁻¹ y - 1 = x⁻¹ (y - x)`, and `x⁻¹` has valuation one. `y`
carries no hypothesis, both sides failing when its valuation is not one. -/
theorem inv_mul_mem_higherUnitGroup_one_iff (x y : Kˣ) (hx : valuation K (x : K) = 1) :
    x⁻¹ * y ∈ higherUnitGroup K 1 ↔ valuation K ((x : K) - y) < 1 := by
  rw [mem_higherUnitGroup_one_iff]
  have h1 : ((x⁻¹ * y : Kˣ) : K) - 1 = ((x : K))⁻¹ * ((y : K) - x) := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_sub, inv_mul_cancel₀ x.ne_zero]
  rw [h1, map_mul, map_inv₀, hx, inv_one, one_mul, Valuation.map_sub_swap]

end Atlas.Knowledge
