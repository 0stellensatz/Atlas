import Mathlib
import Atlas.Knowledge.FreeCharacterJumpSets
import Atlas.Knowledge.IsStarQuotient
import Atlas.Knowledge.JumpOrder
import Atlas.Knowledge.JumpSetOf
import Atlas.Knowledge.JumpSetVector
import Atlas.Knowledge.QuasiFreeFiltered

/-!
# exclusion criterion for character jump sets

Which extended jump sets are *not* sets of jumps of characters of a quasi-free module: the
source's combinatorial criterion comparing a candidate pair with the pair presenting the
module. The containment `𝒥_{M_•} ⊆ Jump*_ρ` always holds; the complement is cut out by the
`Max` set of the comparison—the levels common to both pairs where the candidate's multiplicity
exceeds the presenting one's by the largest margin—through two conditions whose exact shape
depends on whether the residue field is `𝔽_2`. Everything is stated against the presentation
`Atlas.Knowledge.IsStarQuotient`, whose pair is the invariant `(I_{M_•}, β_{M_•})` by the
uniqueness of `Atlas.Knowledge.UnitFiltrationClassification`'s layer.

## Main definitions

* `exclusionMax` — the source's `Max`: the common levels of largest positive multiplicity
  excess.
* `exclusionPoint`, `ExclusionCondition` — the adjoined point and the maximality condition
  the criterion tests it with.

## Main statements

All are claims recorded ahead of their proofs.

* `characterJumpSets_subset_of_isQuasiFree` — `𝒥_{M_•} ⊆ Jump*_ρ` on a quasi-free module.
* `notMem_characterJumpSets_iff_of_ne_two` — the exclusion criterion away from residue
  field `𝔽_2`.
* `notMem_characterJumpSets_iff_of_eq_two` — the exclusion criterion at residue field `𝔽_2`.

## Implementation notes

Multiplicities are read off the graphs by `Atlas.Knowledge.jumpSetVector.beta`, and the
excess `β (i) - β_{M} (i)` lives in truncated natural subtraction, which agrees with the
source's integer reading wherever the criterion consults it: the membership condition demands
a positive excess, and against it a truncated-to-zero competitor compares correctly. The
maximality of the adjoined point is spelled through `Atlas.Knowledge.JumpOrder` over the
candidate's graph with the point inserted, and the point's multiplicity is
`β (j) - β_M (j) + β_M (i)`, exact and positive on the levels consulted. Two slips of the
source's print are corrected silently, both forced by well-formedness: condition (b.1) closes
an unopened parenthesis after `Max`, and condition (b.2) writes `β (i)` for a level `i` where
only `β_M (i)` is defined, the display two lines below carrying the intended `β_M (i)`. The
residue-field size is `Nat.card` of `IsLocalRing.ResidueField`, the dichotomy `≠ 2` / `= 2`
of the source's `|R ⧸ m_R|`.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {M : Type*} [AddCommGroup M] [Module R M]

open Classical in
/-- The source's `Max` for a candidate pair `P` against the presenting pair `Q`: the levels
common to both whose multiplicity excess is positive and largest
([Pagano 2022, Thm. 4.8, p.439][Pagano2022]). -/
noncomputable def exclusionMax (P Q : Finset (ℕ+ × ℕ+)) : Finset ℕ+ :=
  ((P.image Prod.fst) ∩ (Q.image Prod.fst)).filter fun i =>
    jumpSetVector.beta Q i < jumpSetVector.beta P i ∧
      ∀ j ∈ (P.image Prod.fst) ∩ (Q.image Prod.fst),
        jumpSetVector.beta P j - jumpSetVector.beta Q j ≤
          jumpSetVector.beta P i - jumpSetVector.beta Q i

/-- The point the exclusion criterion adjoins to the candidate graph: level `i` with
multiplicity `β (j) - β_M (j) + β_M (i)`. -/
noncomputable def exclusionPoint (P Q : Finset (ℕ+ × ℕ+)) (j i : ℕ+) : ℕ+ × ℕ+ :=
  (i, (jumpSetVector.beta P j - jumpSetVector.beta Q j + jumpSetVector.beta Q i).toPNat')

/-- The maximality condition of the exclusion criterion: for every witness level `j` of `Max`
and every level of the presenting pair missing from the candidate, the adjoined point is
`≤_ρ`-maximal in the candidate graph with the point inserted
([Pagano 2022, Thm. 4.8, p.439][Pagano2022]). -/
def ExclusionCondition (ρ : Shift) (P Q : Finset (ℕ+ × ℕ+)) : Prop :=
  ∀ j ∈ exclusionMax P Q, ∀ i ∈ (Q.image Prod.fst) \ (P.image Prod.fst),
    ∀ r ∈ insert (exclusionPoint P Q j i) P,
      JumpOrder ρ (exclusionPoint P Q j i) r → r = exclusionPoint P Q j i

/-- On a quasi-free module every set of jumps of a character is an extended jump set:
`𝒥_{M_•} ⊆ Jump*_ρ`. Claim recorded ahead of its proof
([Pagano 2022, Prop. 4.6, p.438][Pagano2022]). -/
theorem characterJumpSets_subset_of_isQuasiFree (ρ : Shift) (hρ : (Shift.T ρ).Finite)
    (f : ℕ+) {π : R} (hπ : Irreducible π) {F : FilteredModule R M}
    (hqf : IsQuasiFree ρ hρ f hπ F) :
    characterJumpSets F ⊆ jumpSetFamily ρ (Shift.T_star ρ hρ) := by
  sorry

/-- The exclusion criterion away from residue field `𝔽_2`: a candidate extended jump set is
not a set of jumps of a character exactly when its `Max` against the presenting pair is a
singleton—forced to `{e_ρ^*}` at `f > 1`—and the adjoined points are maximal. Claim recorded
ahead of its proof ([Pagano 2022, Thm. 4.8 (a), p.439][Pagano2022]). -/
theorem notMem_characterJumpSets_iff_of_ne_two (ρ : Shift) (hρ : (Shift.T ρ).Finite)
    (f : ℕ+) {π : R} (hπ : Irreducible π) {Q : Finset (ℕ+ × ℕ+)} {F : FilteredModule R M}
    (hqf : IsQuasiFree ρ hρ f hπ F) (hnf : ¬ IsFree ρ hρ f F)
    (hQP : IsJumpPair ρ (Shift.T_star ρ hρ) Q) (hQ : IsStarQuotient ρ hρ f hπ Q F)
    (hcard : Nat.card (IsLocalRing.ResidueField R) ≠ 2)
    {P : Finset (ℕ+ × ℕ+)} (hP : IsJumpPair ρ (Shift.T_star ρ hρ) P) :
    ↑(jumpSetOf ρ P) ∉ characterJumpSets F ↔
      (exclusionMax P Q).card = 1 ∧ (1 < f → exclusionMax P Q = {Shift.e_star ρ hρ}) ∧
        ExclusionCondition ρ P Q := by
  sorry

/-- The exclusion criterion at residue field `𝔽_2`: as away from it, with the singleton
condition relaxed to odd cardinality. Claim recorded ahead of its proof
([Pagano 2022, Thm. 4.8 (b), p.439][Pagano2022]). -/
theorem notMem_characterJumpSets_iff_of_eq_two (ρ : Shift) (hρ : (Shift.T ρ).Finite)
    (f : ℕ+) {π : R} (hπ : Irreducible π) {Q : Finset (ℕ+ × ℕ+)} {F : FilteredModule R M}
    (hqf : IsQuasiFree ρ hρ f hπ F) (hnf : ¬ IsFree ρ hρ f F)
    (hQP : IsJumpPair ρ (Shift.T_star ρ hρ) Q) (hQ : IsStarQuotient ρ hρ f hπ Q F)
    (hcard : Nat.card (IsLocalRing.ResidueField R) = 2)
    {P : Finset (ℕ+ × ℕ+)} (hP : IsJumpPair ρ (Shift.T_star ρ hρ) P) :
    ↑(jumpSetOf ρ P) ∉ characterJumpSets F ↔
      (exclusionMax P Q).card % 2 = 1 ∧ (1 < f → exclusionMax P Q = {Shift.e_star ρ hρ}) ∧
        ExclusionCondition ρ P Q := by
  sorry

end Atlas.Knowledge
