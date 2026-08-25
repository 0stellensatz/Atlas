import Mathlib

/-!
# higher unit group

For `K` a field with a valuation, the `i`-th **higher unit group** is
`U i (K) = 1 + 𝓂[K] ^ i`, a subgroup of `Kˣ`. These are the terms of the filtration whose
behaviour under `p`-powering the shifts of `Atlas.Knowledge.ShiftRhoEP` encode: for `K` local of
residue characteristic `p` and `e = v_K (p)`, one has `U i ^ p ⊆ U (ρ_ep e p i)`, which is what
makes those shifts the ones relevant to local fields.

## Main definitions

* `higherUnitGroup` — `U i (K) = 1 + 𝓂[K] ^ i` as a `Subgroup Kˣ`.

## Main statements

* `higherUnitGroup_antitone` — the family decreases in `i`, which is what "filtration" means and
  what the real-indexed wrapper `Atlas.Knowledge.RealHigherUnitGroup` passes along.
* `mem_higherUnitGroup_iff` — membership through the units of the integer ring: the
  translate-set carrier identified with the mapped-subgroup presentation.

## Implementation notes

Closure under inverses is the only condition with content. An element `1 + y` with `y` in the
maximal ideal is a unit of the valuation ring, since `1 - (-y)` is a unit whenever `-y` is a
nonunit, and its inverse is again of the form `1 + y'` with `y' = -y * u⁻¹` still in `𝓂[K] ^ i`—
membership being preserved because the ideal absorbs multiplication.

The `synthInstance.maxHeartbeats` bump is scoped to the definition and is there for the instance
search on the subtype `↥(𝓂[K] ^ i : Ideal ↥𝒪[K])`, which is the expensive step.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

set_option synthInstance.maxHeartbeats 40000 in
-- The instance search on the subtype `↥(𝓂[K] ^ i : Ideal ↥𝒪[K])`, which the carrier is a set of
-- translates of, is the expensive step and does not fit the default budget.
/-- The `i`-th higher unit group `U i (K) = 1 + 𝓂[K] ^ i` of a valued field `K`, as a subgroup of
`Kˣ` ([Pagano 2022, §2, p.415][Pagano2022]). -/
noncomputable def higherUnitGroup (K : Type*) [Field K] [ValuativeRel K] (i : ℕ+) :
    Subgroup Kˣ where
  carrier := {(1 : K) + x | x : (𝓂[K] ^ ↑i : Ideal ↥𝒪[K])}
  mul_mem' := by
    rintro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul]
    simp only [Set.mem_setOf_eq] at ha hb
    obtain ⟨xa, hxa⟩ := ha
    obtain ⟨xb, hxb⟩ := hb
    use (xa + xb + xa * xb)
    rw [← hxa, ← hxb]
    simp only [Submodule.coe_add, MulMemClass.coe_mul, Subring.coe_add]
    ring
  one_mem' := by
    use 0
    simp only [ZeroMemClass.coe_zero, add_zero, Units.val_one]
  inv_mem' := by
    rintro x ⟨y, hy⟩
    have hym : (y : ↥𝒪[K]) ∈ 𝓂[K] := Ideal.pow_le_self i.pos.ne' y.2
    obtain ⟨u, hu⟩ : IsUnit (1 + (y : ↥𝒪[K])) := by
      simpa using IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(y : ↥𝒪[K]))
        ((IsLocalRing.mem_maximalIdeal _).mp (neg_mem hym))
    refine ⟨⟨-(y : ↥𝒪[K]) * ↑u⁻¹, Ideal.mul_mem_right _ _ (neg_mem y.2)⟩, ?_⟩
    rw [Units.val_inv_eq_inv_val]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hy]
    have : ((1 : ↥𝒪[K]) + -(y : ↥𝒪[K]) * ↑u⁻¹) * (1 + (y : ↥𝒪[K])) = 1 := by
      linear_combination ((y : ↥𝒪[K]) * ↑u⁻¹) * hu - (y : ↥𝒪[K]) * u.inv_mul
    exact_mod_cast this

/-- The higher unit groups decrease: `U j (K) ≤ U i (K)` whenever `i ≤ j`, the inclusion of
ideal powers `𝓂[K] ^ j ≤ 𝓂[K] ^ i` doing all the work
([Pagano 2022, §2, p.415][Pagano2022]). -/
theorem higherUnitGroup_antitone (K : Type*) [Field K] [ValuativeRel K] :
    Antitone fun i : ℕ+ => higherUnitGroup K i := by
  intro i j h x hx
  obtain ⟨y, hy⟩ := hx
  exact ⟨⟨(y : ↥𝒪[K]), Ideal.pow_le_pow_right (Nat.cast_le.mpr h) y.2⟩, hy⟩

set_option synthInstance.maxHeartbeats 40000 in
-- The instance search on the subtype `↥(𝓂[K] ^ i : Ideal ↥𝒪[K])` is again the expensive step
-- and does not fit the default budget.
/-- Membership in the higher unit group through the units of the integer ring: `x ∈ U i (K)`
iff some unit `u` of `𝒪[K]` congruent to `1` modulo `𝓂[K] ^ i` maps to `x` under the
inclusion `𝒪[K]ˣ → Kˣ` — the translate-set carrier identified with the mapped-subgroup
presentation of the principal units
([Yamaguchi 2026,
`LocalFieldTheory/NonarchimedeanLocalField/PrincipalUnits.lean:18`][Yamaguchi2026]). -/
theorem mem_higherUnitGroup_iff (K : Type*) [Field K] [ValuativeRel K] (i : ℕ+) (x : Kˣ) :
    x ∈ higherUnitGroup K i ↔
      ∃ u : (↥𝒪[K])ˣ,
        ((u : ↥𝒪[K]) - 1) ∈ (𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) ∧
          Units.map (𝒪[K].subtype : ↥𝒪[K] →* K) u = x := by
  constructor
  · rintro ⟨y, hy⟩
    have hym : (y : ↥𝒪[K]) ∈ 𝓂[K] := Ideal.pow_le_self i.pos.ne' y.2
    obtain ⟨u, hu⟩ : IsUnit ((1 : ↥𝒪[K]) + (y : ↥𝒪[K])) := by
      simpa using IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(y : ↥𝒪[K]))
        ((IsLocalRing.mem_maximalIdeal _).mp (neg_mem hym))
    refine ⟨u, ?_, ?_⟩
    · rw [hu]
      simp
    · ext
      rw [Units.coe_map]
      simp only [MonoidHom.coe_coe, Subring.coe_subtype]
      rw [hu]
      push_cast
      exact hy
  · rintro ⟨u, hu1, rfl⟩
    refine ⟨⟨(u : ↥𝒪[K]) - 1, hu1⟩, ?_⟩
    push_cast
    rw [Units.coe_map]
    simp

end Atlas.Knowledge
