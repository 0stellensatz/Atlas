import Mathlib
import Atlas.Knowledge.ShiftEStar

/-!
# e-rho of a shift

For a shift `ρ` with finite `Atlas.Knowledge.ShiftT`, the source writes `e_ρ` for
`ρ⁻¹ (e_star ρ)`—the preimage under `ρ` of the value one past the largest missed integer. It is
written `e'` here, `ρ` being the argument rather than a subscript.

`ρ` is injective (`Shift.inj`), so the preimage is well defined wherever it exists; the definition
goes through `Function.invFun`, which is total. The preimage does exist: `e_star ρ` sits one past
the maximum of what the shift misses, so it is hit, and `Shift.apply_e'` records the genuineness
that `invFun` alone would leave open.

## Main definitions

* `Shift.e'` — the preimage under `ρ` of `e_star ρ`.

## Main statements

* `Shift.apply_e'` — the preimage is genuine: `ρ (e' ρ) = e_star ρ`. What `Function.invFun`
  leaves open in general closes here, because `e_star` sits past the maximum of what the
  shift misses and so is hit.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open Set

namespace Shift

/-- For a shift `ρ` with `T ρ` finite, `e'` is `ρ⁻¹ (e_star ρ)`, written `e_ρ` in the source
([Pagano 2022, §2, p.415][Pagano2022]). -/
noncomputable def e' {ρ : Shift} (hρ : (T ρ).Finite) := (⇑ρ).invFun (e_star ρ hρ)

/-- The preimage is genuine: `e_star` is not missed by the shift, so `Function.invFun` finds
a real preimage and `ρ (e' ρ) = e_star ρ`. -/
theorem apply_e' (ρ : Shift) (hρ : (T ρ).Finite) : ρ (Shift.e' hρ) = e_star ρ hρ := by
  have hmem : e_star ρ hρ ∈ (ρ.shift_map) '' Set.univ := by
    by_contra h
    exact e_star_notMem_T ρ hρ ⟨Set.mem_univ _, h⟩
  obtain ⟨z, -, hz⟩ := hmem
  have hz' : ρ z = e_star ρ hρ := hz
  rw [Shift.e', ← hz']
  exact congrArg ρ (Function.leftInverse_invFun ρ.inj z)

end Shift

end Atlas.Knowledge
