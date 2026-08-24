import Mathlib

/-!
# existence of a valuative extension

The valuative relation of a field prolongs to any field extension: on `L` over `K` there is a
valuative relation whose restriction along `algebraMap K L` is the relation of `K`—the
structure `ValuativeExtension K L` asks for, produced rather than assumed.
This is what lets the tower statements of `Atlas.Knowledge.HerbrandPhi` and
`Atlas.Knowledge.UpperRamificationGroup`, which hypothesize `[ValuativeRel E]` and
`[ValuativeExtension K E]` on an abstract middle field, apply to an intermediate field of a
concrete extension, where no valuative structure comes supplied:
`Atlas.Knowledge.RamificationFiltration` and `Atlas.Knowledge.WildInertiaSubgroup` consume it
at every finite Galois subextension.

## Main statements

* `exists_valuativeExtension` — a valuative relation extending that of `K` exists on any
  field extension of `K`.

## Implementation notes

The statement records the existence half only; the uniqueness half of the source's corollary
is deliberately not recorded, as no consumer compares two structures—the same division
`Atlas.Knowledge.FiniteExtensionIsMixedCharLocalField` makes for the full carrier signature,
whose existence form (with the topology conjoined) remains a recorded claim there. The
statement is broader than the source's: the proof is not the source's completeness argument
but Chevalley's extension theorem, which needs neither completeness nor finiteness nor a
discrete value group, so the item is recorded in that generality and the source is cited for
the classical case that motivates it. Mathlib carries the theorem as
`LocalSubring.exists_le_valuationSubring`: the image of `𝒪[K]` in `L` is a local subring,
some valuation subring `B` of `L` dominates it, and domination forces the trace of `B` on
`K` to be `𝒪[K]`—a valuation ring is maximal under domination in its fraction field,
rendered here elementwise: an `x` with `1 < valuation K x` puts `x⁻¹` in the maximal ideal
of the image, hence in the maximal ideal of `B` by locality of the inclusion, and
`algebraMap K L x ∈ B` would make the image of `x⁻¹` a unit of `B`. The valuative relation
of `B.valuation` then restricts to that of `K` by comparing `a / b` against the unit ball on
both sides.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

/-- The valuative relation of a field prolongs to any field extension: a valuative relation
on `L` restricting along `algebraMap K L` to the relation of `K` exists—Chevalley's extension
theorem, of which the source states the finite-extension case over a complete discretely
valued field ([Serre 1979, Chap. II, §2, Cor. 2, p.29][Serre1979]). -/
theorem exists_valuativeExtension (K : Type*) [Field K] [ValuativeRel K] (L : Type*)
    [Field L] [Algebra K L] :
    ∃ _ : ValuativeRel L, ValuativeExtension K L := by
  have hinj : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  -- the image of `𝒪[K]` in `L` as a local subring, and a valuation subring dominating it
  let f : 𝒪[K] →+* L := (algebraMap K L).comp (Subring.subtype 𝒪[K])
  obtain ⟨B, hle, hloc⟩ := (LocalSubring.range f).exists_le_valuationSubring
  -- domination pins the trace of `B` on `K` to `𝒪[K]`
  have hmem : ∀ x : K, algebraMap K L x ∈ B ↔ valuation K x ≤ 1 := by
    intro x
    constructor
    · intro hx
      by_contra hv
      push Not at hv
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [map_zero] at hv
        exact absurd hv (not_lt.mpr zero_le)
      have hxinv : valuation K x⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact le_of_lt ((inv_lt_one₀ (zero_lt_one.trans hv)).mpr hv)
      -- the image of `x⁻¹` is a nonunit of the image of `𝒪[K]`
      have hz : algebraMap K L x⁻¹ ∈ (LocalSubring.range f).toSubring :=
        ⟨⟨x⁻¹, hxinv⟩, rfl⟩
      have hnonunit : ¬IsUnit (⟨algebraMap K L x⁻¹, hz⟩ :
          (LocalSubring.range f).toSubring) := by
        intro hunit
        obtain ⟨z', hz'⟩ := isUnit_iff_exists_inv.mp hunit
        obtain ⟨⟨y, hy⟩, hy'⟩ := z'.2
        have hval : algebraMap K L x⁻¹ * (z' : L) = 1 := by
          simpa using congrArg Subtype.val hz'
        rw [← hy'] at hval
        have hxy : x⁻¹ * y = 1 := by
          apply hinj
          rw [map_mul, map_one]
          exact hval
        have hyx : y = x := by
          rw [← one_mul y, ← mul_inv_cancel₀ hx0, mul_assoc, hxy, mul_one]
        have hxmem : valuation K x ≤ 1 := hyx ▸ hy
        exact absurd hxmem (not_le.mpr hv)
      -- but locality of the domination and `x ∈ B` make it a unit
      have hunit : IsUnit (Subring.inclusion hle (⟨algebraMap K L x⁻¹, hz⟩ :
          (LocalSubring.range f).toSubring)) := by
        refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K L x, hx⟩, ?_⟩
        apply Subtype.ext
        change algebraMap K L x⁻¹ * algebraMap K L x = 1
        rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
      exact hnonunit (hloc.map_nonunit _ hunit)
    · intro hx
      exact hle ⟨⟨x, hx⟩, rfl⟩
  -- the relation of `B.valuation`, and the comparison of the two unit balls
  letI vrel : ValuativeRel L := .ofValuation B.valuation
  haveI hcompat : B.valuation.Compatible := Valuation.Compatible.ofValuation B.valuation
  refine ⟨vrel, ⟨fun a b => ?_⟩⟩
  rw [Valuation.Compatible.vle_iff_le (v := B.valuation),
    Valuation.Compatible.vle_iff_le (v := valuation K)]
  rcases eq_or_ne b 0 with rfl | hb
  · simp [map_eq_zero_iff (algebraMap K L) hinj]
  · have hb' : algebraMap K L b ≠ 0 := fun h => hb (hinj (h.trans (map_zero _).symm))
    have hvb : B.valuation (algebraMap K L b) ≠ 0 := (Valuation.ne_zero_iff _).mpr hb'
    have hKb : valuation K b ≠ 0 := (Valuation.ne_zero_iff _).mpr hb
    have hdiv : algebraMap K L a / algebraMap K L b = algebraMap K L (a / b) :=
      (map_div₀ (algebraMap K L) a b).symm
    rw [← div_le_one₀ (zero_lt_iff.mpr hvb), ← map_div₀, hdiv, B.valuation_le_one_iff,
      hmem, map_div₀, div_le_one₀ (zero_lt_iff.mpr hKb)]

end Atlas.Knowledge
