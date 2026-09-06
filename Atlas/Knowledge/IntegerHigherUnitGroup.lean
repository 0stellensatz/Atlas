import Mathlib
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.IsMixedCharLocalField

/-!
# integer higher unit group

The higher unit filtration on the integer units: `1 + 𝔪ⁿ` as a subgroup of `𝒪[K]ˣ` — the
unit-parameter side of the level tower's Galois description, and the group whose
quotients `Atlas.Knowledge.integerHigherUnitCount` counts. The subgroup is on integer
units where `Atlas.Knowledge.higherUnitGroup` is on field units — the two sit on
opposite sides of `𝒪ˣ → Kˣ`, and this item records the identification: the field-side
filtration is exactly the image of this subgroup, in a `ℕ+`-shaped form and in the
`ℕ`-shaped form whose left side is what consumer goals spell.

## Main definitions

* `integerHigherUnitGroup` — `1 + 𝔪ⁿ` as a subgroup of `𝒪[K]ˣ`.

## Main statements

* `higherUnitGroup_eq_map_integerHigherUnitGroup` /
  `map_integerHigherUnitGroup_eq_higherUnitGroup` — the two spellings of `U^{(i)}` in
  `Kˣ` are one subgroup; proved.
* `sub_mem_iff_div_mem_integerHigherUnitGroup` — the multiplicative–additive congruence
  bridge; proved.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open scoped ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/-- The **integer higher unit group** `1 + 𝔪ⁿ` as a subgroup of `𝒪[K]ˣ` — the
unit-parameter side of the level tower's Galois description
([Milne 2020, Chap. I, §3, Prop. 3.4 and Thm. 3.6 (b), p.38][MilneCFT];
Yamaguchi 2026, `LubinTate/FiniteLevel/FiniteParameters.lean:35`). -/
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

/-- **The filtration is the image of the integer higher units**: the translate-set
subgroup of `Atlas.Knowledge.higherUnitGroup` and the mapped subgroup here are one
subgroup of `Kˣ` (Yamaguchi 2026,
`LocalFieldTheory/NonarchimedeanLocalField/PrincipalUnits.lean:18` — the source keeps
the filtration on the integer side, so the `Kˣ`-level identity is the bridging this
layer adds). -/
theorem higherUnitGroup_eq_map_integerHigherUnitGroup (i : ℕ+) :
    higherUnitGroup K i =
      (integerHigherUnitGroup K (i : ℕ)).map
        (Units.map (algebraMap 𝒪[K] K).toMonoidHom) := by
  ext x
  rw [mem_higherUnitGroup_iff]
  rfl

/-- **The identification in the `ℕ`-shaped orientation** consumers rewrite with: the
integer side on the left, at a nonzero natural level (Yamaguchi 2026,
`LocalFieldTheory/NonarchimedeanLocalField/PrincipalUnits.lean:18`). -/
theorem map_integerHigherUnitGroup_eq_higherUnitGroup (n : ℕ) (hn : n ≠ 0) :
    (integerHigherUnitGroup K n).map
        (Units.map (algebraMap 𝒪[K] K).toMonoidHom) =
      higherUnitGroup K ⟨n, Nat.pos_of_ne_zero hn⟩ :=
  (higherUnitGroup_eq_map_integerHigherUnitGroup K ⟨n, Nat.pos_of_ne_zero hn⟩).symm

/-- Multiplicative–additive bridge for the higher unit congruence: two integer units
are congruent modulo `𝔪 ^ m` exactly when their ratio is a higher unit. -/
theorem sub_mem_iff_div_mem_integerHigherUnitGroup (m : ℕ) (u v : 𝒪[K]ˣ) :
    ((u : ↥𝒪[K]) - v ∈ (𝓂[K] ^ m : Ideal ↥𝒪[K])) ↔
      u⁻¹ * v ∈ integerHigherUnitGroup K m := by
  have hmem : u⁻¹ * v ∈ integerHigherUnitGroup K m ↔
      ((u⁻¹ * v : 𝒪[K]ˣ) : ↥𝒪[K]) - 1 ∈ (𝓂[K] ^ m : Ideal ↥𝒪[K]) := Iff.rfl
  have key : ((u⁻¹ * v : 𝒪[K]ˣ) : ↥𝒪[K]) - 1 =
      ((u⁻¹ : 𝒪[K]ˣ) : ↥𝒪[K]) * ((v : ↥𝒪[K]) - (u : ↥𝒪[K])) := by
    have hinv : ((u⁻¹ : 𝒪[K]ˣ) : ↥𝒪[K]) * (u : ↥𝒪[K]) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    push_cast
    rw [mul_sub, hinv]
  rw [hmem, key, Ideal.unit_mul_mem_iff_mem _ (u⁻¹).isUnit, ← neg_sub, neg_mem_iff]

end Atlas.Knowledge
