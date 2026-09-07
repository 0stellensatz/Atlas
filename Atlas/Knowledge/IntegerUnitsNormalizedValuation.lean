import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.NormalizedValuation

/-!
# integer units and the normalized valuation

The unit group of the integers of a mixed-characteristic local field, read inside `Kˣ` as the
range of `Units.map 𝒪[K].subtype`, is exactly the kernel of the normalized valuation: a unit
of `𝒪[K]` and its inverse both have valuation at most `1`, so exactly `1`, and an element of
valuation `1` is a unit of `𝒪[K]` with its inverse. This is the `U^0` of the unit filtration,
in the spelling the recorded ramification statements use for it, identified with the spelling
the valuation lemmas use.

## Main statements

* `range_units_map_subtype_eq_ker` — `U^0 = ker (normalizedValuationHom K)`.

## Implementation notes

`Atlas.Knowledge.ker_normalizedValuationHom` already identifies the kernel with
`𝒪[K].toSubmonoid.units`; the range of `Units.map 𝒪[K].subtype` is the same subgroup in the
form the inertia endpoint of `Atlas.Knowledge.ArtinRamificationCompatibility` and the `U^0`
cutoff of `Atlas.Knowledge.ConductorExponent` are stated with, and the identification is
proved directly rather than through a units-of-submonoid dictionary.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

/-- **The integer units are the kernel of the normalized valuation**: `x ∈ Kˣ` is the image
of a unit of `𝒪[K]` iff its valuation is `1` ([Serre 1979, Chap. I, §1, p.5][Serre1979]). -/
theorem range_units_map_subtype_eq_ker :
    MonoidHom.range (Units.map (𝒪[K].subtype : ↥𝒪[K] →* K)) = (normalizedValuationHom K).ker := by
  ext x
  rw [mem_ker_normalizedValuationHom]
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : valuation K ((Units.map (𝒪[K].subtype : ↥𝒪[K] →* K) u : Kˣ) : K) ≤ 1 :=
      (Valuation.mem_integer_iff _ _).mp (u : ↥𝒪[K]).2
    have h2 : valuation K (((Units.map (𝒪[K].subtype : ↥𝒪[K] →* K) u)⁻¹ : Kˣ) : K) ≤ 1 := by
      rw [← map_inv]
      exact (Valuation.mem_integer_iff _ _).mp ((u⁻¹ : (↥𝒪[K])ˣ) : ↥𝒪[K]).2
    have hmul : valuation K ((Units.map (𝒪[K].subtype : ↥𝒪[K] →* K) u : Kˣ) : K) *
        valuation K (((Units.map (𝒪[K].subtype : ↥𝒪[K] →* K) u)⁻¹ : Kˣ) : K) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    exact le_antisymm h1 (by
      calc (1 : ValueGroupWithZero K) = _ := hmul.symm
        _ ≤ valuation K ((Units.map (𝒪[K].subtype : ↥𝒪[K] →* K) u : Kˣ) : K) * 1 :=
          mul_le_mul_right h2 _
        _ = _ := mul_one _)
  · intro hx
    have hx' : valuation K ((x⁻¹ : Kˣ) : K) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
    refine ⟨⟨⟨(x : K), (Valuation.mem_integer_iff _ _).mpr hx.le⟩,
      ⟨((x⁻¹ : Kˣ) : K), (Valuation.mem_integer_iff _ _).mpr hx'.le⟩,
      Subtype.ext (by simp), Subtype.ext (by simp)⟩, ?_⟩
    exact Units.ext rfl

end Atlas.Knowledge
