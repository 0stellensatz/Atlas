import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField

/-!
# integer higher unit group

The higher unit filtration on the integer units: `1 + 𝔪ⁿ` as a subgroup of `𝒪[K]ˣ` — the
unit-parameter side of the level tower's Galois description, and the group whose
quotients `Atlas.Knowledge.integerHigherUnitCount` counts. The subgroup is on integer
units where `Atlas.Knowledge.higherUnitGroup` is on field units — the two sit on
opposite sides of `𝒪ˣ → Kˣ`, and this item does not identify them.

## Main definitions

* `integerHigherUnitGroup` — `1 + 𝔪ⁿ` as a subgroup of `𝒪[K]ˣ`.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open scoped ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/-- The **integer higher unit group** `1 + 𝔪ⁿ` as a subgroup of `𝒪[K]ˣ` — the
unit-parameter side of the level tower's Galois description
([Milne 2020, Chap. I, §3, Prop. 3.4 and Thm. 3.6 (b), p.38][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/FiniteParameters.lean:35`][Yamaguchi2026]). -/
def integerHigherUnitGroup (n : ℕ) : Subgroup 𝒪[K]ˣ where
  carrier := {u | (u : 𝒪[K]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[K] ^ n}
  one_mem' := by
    simp
  mul_mem' := by
    intro u v hu hv
    have key : ((u * v : 𝒪[K]ˣ) : 𝒪[K]) - 1 =
        (u : 𝒪[K]) * ((v : 𝒪[K]) - 1) + ((u : 𝒪[K]) - 1) := by
      push_cast
      ring
    rw [Set.mem_setOf_eq, key]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hv) hu
  inv_mem' := by
    intro u hu
    have key : ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) - 1 =
        -(((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * ((u : 𝒪[K]) - 1)) := by
      have hinv : ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * (u : 𝒪[K]) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [mul_sub, hinv, mul_one]
      ring
    rw [Set.mem_setOf_eq, key]
    exact neg_mem (Ideal.mul_mem_left _ _ hu)

end Atlas.Knowledge
