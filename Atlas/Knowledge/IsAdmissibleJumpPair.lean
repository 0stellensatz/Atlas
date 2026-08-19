import Mathlib
import Atlas.Knowledge.IsJumpPair
import Atlas.Knowledge.ShiftTStar

/-!
# admissible jump pair

The **admissible** extended jump pairs: those whose minimal level, pushed along `ρ` as many
times as its multiplicity, lands exactly on `e_ρ^*`. These are the extended jump sets that
parametrize the `(f, ρ)`-quasi-free filtered modules that are not free—the image of the
presentation `(I, β) ↦ M_ρ^{f - 1} ⊕ M_ρ^* ⧸ R v_{(I, β)}` recorded over
`Atlas.Knowledge.IsStarQuotient`—and the hypothesis under which the realizability claim of
`Atlas.Knowledge.JumpSetRealization` produces a local field.

## Main definitions

* `IsAdmissibleJumpPair` — an extended jump pair whose minimal level reaches `e_ρ^*`.

## Implementation notes

The source's condition is `ρ^{β (min I)} (min I) = e_ρ^*`, whose `min I` presupposes `I`
nonempty; the `∃`-form here carries that presupposition, so the empty pair is not admissible.
The pair is carried as its graph, as everywhere in the jump-set layer, and the minimal level is
the point whose first component is below every other—unique, the levels of a jump pair being
distinct.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

/-- The **admissible** extended jump pairs for a shift `ρ` with finite `T_ρ`: the extended jump
pairs with a minimal level that, iterated along `ρ` as many times as its multiplicity, lands
exactly on `e_ρ^*` ([Pagano 2022, §3.3.6, p.434][Pagano2022], "We call these jump sets
admissible"). -/
def IsAdmissibleJumpPair (ρ : Shift) (hρ : (Shift.T ρ).Finite) (P : Finset (ℕ+ × ℕ+)) : Prop :=
  IsJumpPair ρ (Shift.T_star ρ hρ) P ∧
    ∃ p ∈ P, (∀ q ∈ P, p.1 ≤ q.1) ∧ (⇑ρ)^[(p.2 : ℕ)] p.1 = Shift.e_star ρ hρ

end Atlas.Knowledge
