import Mathlib
import Atlas.Knowledge.FilteredDefect
import Atlas.Knowledge.FilteredComplete
import Atlas.Knowledge.ShiftEPrime

/-!
# quasi-free filtered module

The `(f, ρ)`-quasi-free filtered modules: one step more complicated than the `(f, ρ)`-free ones
of `Atlas.Knowledge.FreeFiltered`, and exactly complicated enough. Every graded piece has
dimension `f`, every defect and codefect vanishes away from the single critical index
`e_ρ' = ρ⁻¹ (e_ρ^*)` of `Atlas.Knowledge.ShiftEPrime`, and the defect there is at most one.
These are the filtered modules the source's classification is *for*: the unit filtration of a
local field is one, and `Atlas.Knowledge.FiltOrd` is the machinery that will attach to each of
them the extended jump set that determines it.

## Main definitions

* `IsQuasiFree` — the predicate, as a bundle of the source's conditions (a), (b), (c) over the
  standing hypotheses complete, `ρ`-bounded, strictly linear.

## Implementation notes

The source states condition (c)—the defect bound at `e_ρ'`—under "if `T_ρ` is finite"; the
finiteness is a standing hypothesis of this tranche, carried as the argument `hρ` that
`Shift.e'` needs anyway, so the conditional form collapses. The uniformizer is a parameter as
in the source ("we fix a uniformizer"), the defects not depending on the choice.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The **`(f, ρ)`-quasi-free** filtered modules: complete, strictly linear members of `C_ρ`
whose graded pieces all have dimension `f`, whose defects and codefects vanish away from the
critical index `e_ρ'`, and whose defect there is at most one
([Pagano 2022, Def. 3.26, p.428][Pagano2022]). -/
structure IsQuasiFree (ρ : Shift) (hρ : (Shift.T ρ).Finite) (f : ℕ+) {π : R}
    (hπ : Irreducible π) (F : FilteredModule R M) : Prop where
  complete : F.IsComplete
  rhoBounded : F.RhoBounded ρ
  strictlyLinear : F.IsStrictlyLinear
  fDim_eq : ∀ i, F.fDim strictlyLinear.1 i = (f : ℕ)
  defect_eq_zero : ∀ i, i ≠ Shift.e' hρ → FilteredModule.defect strictlyLinear hπ i = 0
  codefect_eq_zero : ∀ i, i ≠ Shift.e' hρ → FilteredModule.codefect strictlyLinear hπ i = 0
  defect_le_one : FilteredModule.defect strictlyLinear hπ (Shift.e' hρ) ≤ 1

end Atlas.Knowledge
