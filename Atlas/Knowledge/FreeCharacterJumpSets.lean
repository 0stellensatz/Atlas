import Mathlib
import Atlas.Knowledge.IsFilteredCharacter
import Atlas.Knowledge.FreeFiltered
import Atlas.Knowledge.IsJumpSet
import Atlas.Knowledge.ShiftTStar

/-!
# jump sets of characters of a free model

The source's computation of `𝒥` on the free models: the sets of jumps of characters of
`M_ρ^f` are exactly the `ρ`-jump sets, and those of the presenting model
`M_ρ^{f - 1} ⊕ M_ρ^*` are exactly the extended `ρ`-jump sets. This is the character-side
analogue of the orbit classification `Atlas.Knowledge.FiltOrd` records for vectors—in both
cases jump sets parametrize, there orbits, here sets of jumps—and the base the exclusion
criterion `Atlas.Knowledge.CharacterExclusion` cuts against on a quasi-free module.

## Main statements

Both are claims recorded ahead of their proofs.

* `characterJumpSets_freeIndex` — `𝒥_{M_ρ^f} = Jump_ρ`.
* `characterJumpSets_starIndex` — `𝒥_{M_ρ^{f-1} ⊕ M_ρ^*} = Jump*_ρ`.

## Main definitions

* `jumpSetFamily` — the `ρ`-jump sets relative to an index set, as a collection of sets: the
  source's `Jump_ρ` and `Jump*_ρ` in the shape `𝒥` takes its values.

## Implementation notes

The members of `𝒥` are sets of positive integers while the layer's jump sets are `Finset`s,
so the right side of each equality is the collection of coercions of jump sets—`jumpSetFamily`,
which exists so that the two claims and the exclusion criterion spell the same object the same
way. Finiteness of every member of the left side is part of what the claims assert. The source
states the free half for any shift and the star half under finite `T_ρ`; the layer's models
exist only at finite `T_ρ`, so both claims carry the finiteness, the free half thereby
narrower than the source's.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

/-- The `ρ`-jump sets relative to an index set, as a collection of sets of positive integers:
the source's `Jump_ρ` (at `S = T_ρ`) and `Jump*_ρ` (at `S = T*_ρ`) in the shape the invariant
`𝒥` takes its values ([Pagano 2022, Def. 2.2, p.416][Pagano2022]). -/
def jumpSetFamily (ρ : Shift) (S : Set ℕ+) : Set (Set ℕ+) :=
  {A | ∃ B : Finset ℕ+, IsJumpSet ρ S B ∧ A = ↑B}

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The jump sets of characters of the free model are exactly the `ρ`-jump sets:
`𝒥_{M_ρ^f} = Jump_ρ`. Claim recorded ahead of its proof
([Pagano 2022, Thm. 4.5, p.437][Pagano2022]). -/
theorem characterJumpSets_freeIndex (ρ : Shift) (hρ : (Shift.T ρ).Finite) (f : ℕ+) :
    characterJumpSets (freeFiltered (R := R) ρ (Shift.freeIndex hρ f)) =
      jumpSetFamily ρ (Shift.T ρ) := by
  sorry

/-- The jump sets of characters of the presenting model are exactly the extended `ρ`-jump
sets: `𝒥_{M_ρ^{f-1} ⊕ M_ρ^*} = Jump*_ρ`. Claim recorded ahead of its proof
([Pagano 2022, Thm. 4.5, p.437][Pagano2022]). -/
theorem characterJumpSets_starIndex (ρ : Shift) (hρ : (Shift.T ρ).Finite) (f : ℕ+) :
    characterJumpSets (freeFiltered (R := R) ρ (Shift.starIndex hρ f)) =
      jumpSetFamily ρ (Shift.T_star ρ hρ) := by
  sorry

end Atlas.Knowledge
