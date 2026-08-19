import Mathlib
import Atlas.Knowledge.CharacterGraph
import Atlas.Knowledge.FiltAut
import Atlas.Knowledge.FreeFiltered
import Atlas.Knowledge.JumpSetExtremal
import Atlas.Knowledge.JumpSetOf

/-!
# regularization of a character

The two steps by which the source reads the jumps of a character of a free model off its
graph. A filtered automorphism of the model carries the graph
`Atlas.Knowledge.CharacterGraph` onto its `≤_ρ`-maximal points, which
`Atlas.Knowledge.JumpSetExtremal` knows to be a jump-pair graph; and once the graph is a
jump-pair graph, the jumps of the character are exactly the jump set it generates. Together
they reduce `Atlas.Knowledge.characterJumpSets` of the free models to jump-set combinatorics,
which is what `Atlas.Knowledge.FreeCharacterJumpSets` records.

## Main statements

Both are claims recorded ahead of their proofs.

* `exists_filtAut_characterGraph_eq_jumpMax` — some filtered automorphism regularizes the
  graph to its maximal points.
* `characterJumps_eq_jumpSetOf` — when the graph is a jump-pair graph, the jumps of the
  character are its jump set.

## Implementation notes

The source states both for the models `M_ρ^f` and `M_ρ^{f - 1} ⊕ M_ρ^*`; the claims here are
over an arbitrary finite index, a deliberate widening recorded as in
`Atlas.Knowledge.IsStarQuotient`: the arguments—coordinate transformations erasing dominated
points, and the decay of block orders along the shift's orbits—see only the levels and
multiplicities of the index, never membership of the levels in `T_ρ`, so the model's shape
does not enter. The jump-pair hypothesis of the second claim is stated over unconstrained
levels, `Set.univ`, the weakest form under which the conclusion's right side is the intended
object; the composition with a filtered automorphism is composition with its underlying linear
map.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Some filtered automorphism of the model regularizes the graph of a character to its
maximal points: the source's transformation erasing the dominated points of `(A_χ, b_χ)` one
at a time. Claim recorded ahead of its proof ([Pagano 2022, Prop. 4.3, p.436][Pagano2022]). -/
theorem exists_filtAut_characterGraph_eq_jumpMax (ρ : Shift) (D : Finset (ℕ+ × ℕ)) {π : R}
    (hπ : Irreducible π) (χ : (↥D → R) →ₗ[R] fractionQuotient R) :
    ∃ e ∈ (freeFiltered (R := R) ρ D).filtAut,
      characterGraph hπ (χ ∘ₗ (e : (↥D → R) ≃ₗ[R] (↥D → R)).toLinearMap) =
        jumpMax ρ (characterGraph hπ χ) := by
  sorry

/-- When the graph of a character is a jump-pair graph, the jumps of the character are the
jump set the pair generates: the source's `J_χ = J_{(A_χ, b_χ)}`, through the order formula
for the character on the chain. Claim recorded ahead of its proof
([Pagano 2022, Prop. 4.4, p.437][Pagano2022]). -/
theorem characterJumps_eq_jumpSetOf (ρ : Shift) (D : Finset (ℕ+ × ℕ)) {π : R}
    (hπ : Irreducible π) (χ : (↥D → R) →ₗ[R] fractionQuotient R)
    (hP : IsJumpPair ρ Set.univ (characterGraph hπ χ)) :
    characterJumps (freeFiltered (R := R) ρ D) χ = ↑(jumpSetOf ρ (characterGraph hπ χ)) := by
  sorry

end Atlas.Knowledge
