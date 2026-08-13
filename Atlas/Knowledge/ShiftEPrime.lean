import Mathlib
import Atlas.Knowledge.ShiftEStar

/-!
# e-rho of a shift

For a shift `ρ` with finite `Atlas.Knowledge.ShiftT`, the source writes `e_ρ` for
`ρ⁻¹ (e_star ρ)`—the preimage under `ρ` of the value one past the largest missed integer. It is
written `e'` here, `ρ` being the argument rather than a subscript.

`ρ` is injective (`Shift.inj`), so the preimage is well defined wherever it exists; the definition
goes through `Function.invFun`, which is total and therefore says nothing about the case where
`e_star ρ` is itself missed by `ρ`. A statement about `e'` that needs the preimage to be genuine
has to supply that, which is why nothing here is claimed about it.

## Main definitions

* `Shift.e'` — the preimage under `ρ` of `e_star ρ`.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open Set

namespace Shift

/-- For a shift `ρ` with `T ρ` finite, `e'` is `ρ⁻¹ (e_star ρ)`, written `e_ρ` in the source
([Pagano 2022, §2, p.415][Pagano2022]). -/
noncomputable def e' {ρ : Shift} (hρ : (T ρ).Finite) := (⇑ρ).invFun (e_star ρ hρ)

end Shift

end Atlas.Knowledge
