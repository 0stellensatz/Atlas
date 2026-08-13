import Mathlib

/-!
# jump multiplicity

The **multiplicity map** of a finite set `A` of positive integers: `jumpMultiplicity A i` counts
the elements of `A` at or above `i`. On the index set of a jump set `Atlas.Knowledge.IsJumpSet`
this is the map the source writes `β_A : i ↦ |[i, ∞) ∩ A|`, the second component of the pair
`(I_A, β_A)` that `Atlas.Knowledge.JumpPairOf` assembles; the counting formula makes sense at
every `i`, so the map is stated totally and no junk value is involved—off the index set it simply
keeps counting, and the lemmas below hold everywhere.

## Main definitions

* `jumpMultiplicity` — the number of elements of `A` at or above `i`.

## Main statements

* `jumpMultiplicity_antitone` — counting from higher up finds no more.
* `jumpMultiplicity_lt_of_lt` — counting from strictly above a member finds strictly fewer.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

/-- The **multiplicity map** of `A`: the number of elements of `A` at or above `i`. On the index
set `A \ ρ '' A` of a jump set this is the map written `β_A` in the source
([Pagano 2022, Def. 2.2, p.416][Pagano2022]). -/
def jumpMultiplicity (A : Finset ℕ+) (i : ℕ+) : ℕ := (A.filter fun b => i ≤ b).card

theorem jumpMultiplicity_pos {A : Finset ℕ+} {i : ℕ+} (hi : i ∈ A) : 0 < jumpMultiplicity A i :=
  Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, le_refl i⟩⟩

theorem jumpMultiplicity_antitone (A : Finset ℕ+) : Antitone (jumpMultiplicity A) := by
  intro i j hij
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, le_trans hij hx.2⟩

theorem jumpMultiplicity_lt_of_lt {A : Finset ℕ+} {i j : ℕ+} (hi : i ∈ A) (hij : i < j) :
    jumpMultiplicity A j < jumpMultiplicity A i := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨i, Finset.mem_filter.mpr ⟨hi, le_refl i⟩, by
      simp only [Finset.mem_filter, not_and]
      exact fun _ => not_le.mpr hij⟩
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, le_trans (le_of_lt hij) hx.2⟩

end Atlas.Knowledge
