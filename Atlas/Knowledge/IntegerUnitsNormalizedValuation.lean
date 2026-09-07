import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.NormalizedValuation

/-!
# integer units and the normalized valuation

The unit group of the integers of a mixed-characteristic local field, read inside `Kˣ` as the
range of `Units.map 𝒪[K].subtype`, is exactly the kernel of the normalized valuation. This is
the `U^0` of the unit filtration, in the spelling the recorded ramification statements use
for it, identified with the spelling the valuation lemmas use:
`Atlas.Knowledge.ker_normalizedValuationHom` has the kernel as the units of the submonoid
`𝒪[K]`, and a unit of a submonoid is exactly what `Units.map` of its inclusion hits.

## Main statements

* `range_units_map_subtype_eq_ker` — `U^0 = ker (normalizedValuationHom K)`.

## Implementation notes

The item is `Atlas.Knowledge.ker_normalizedValuationHom` in the `Units.map` spelling — the
form the inertia endpoint of `Atlas.Knowledge.ArtinRamificationCompatibility` and the `U^0`
cutoff of `Atlas.Knowledge.ConductorExponent` are stated with. The proof is the dictionary
between the two spellings and nothing else: a unit of the submonoid `𝒪[K]` is an element of
`Kˣ` lying in `𝒪[K]` together with its inverse, and that pair is a unit of `𝒪[K]` mapped
down; no valuation is computed.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

/-- **The integer units are the kernel of the normalized valuation**: `x ∈ Kˣ` is the image
of a unit of `𝒪[K]` iff `valuation K (x : K) = 1` —
`Atlas.Knowledge.ker_normalizedValuationHom` with the units of the submonoid `𝒪[K]` unpacked
into `Units.map` of its inclusion ([Serre 1979, Chap. I, §1, p.5][Serre1979]). -/
theorem range_units_map_subtype_eq_ker :
    MonoidHom.range (Units.map (𝒪[K].subtype : ↥𝒪[K] →* K)) = (normalizedValuationHom K).ker := by
  rw [ker_normalizedValuationHom]
  ext x
  exact ⟨fun ⟨u, hu⟩ => hu ▸ ⟨(u : ↥𝒪[K]).2, ((u⁻¹ : (↥𝒪[K])ˣ) : ↥𝒪[K]).2⟩,
    fun ⟨h1, h2⟩ => ⟨⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩,
      Units.ext rfl⟩⟩

end Atlas.Knowledge
