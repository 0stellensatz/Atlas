import Mathlib

/-!
# ℓ-adic representation

An **`ℓ`-adic representation** of a profinite group `G`: a finite-dimensional vector space over
`ℚ_[ℓ]` on which `G` acts linearly and continuously. This is the coefficient system of the
source's Section 5, whose Hodge–Tate machinery is applied to the `m`-step solvable
representations `Atlas.Knowledge.IsMStepSolvableRep`; the twist of a representation by a
character is `Atlas.Knowledge.CharacterTwist`.

## Main definitions

* `IsLadicRepresentation` — the predicate on a Mathlib `Representation ℚ_[ℓ] G V` packaging
  finite-dimensionality and continuity of the action.

## Implementation notes

Mathlib's `Representation` carries no topology, so the carrier `V` is asked for one as an
instance and the predicate pins it down: `V` is a Hausdorff topological vector space over
`ℚ_[ℓ]`, finite-dimensional, and the two-variable action map is continuous. On a
finite-dimensional space over a complete nontrivially normed field the Hausdorff vector-space
topology is unique, so the instance carries no genuine freedom—the fields of the structure
exclude the degenerate choices rather than parameterize honest ones.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

variable {ℓ : ℕ} [Fact ℓ.Prime] {G V : Type*} [Group G] [TopologicalSpace G]
  [AddCommGroup V] [Module ℚ_[ℓ] V] [TopologicalSpace V]

/-- An **`ℓ`-adic representation** of a topological group: a continuous linear action on a
finite-dimensional Hausdorff topological vector space over `ℚ_[ℓ]`
([Hyeon 2025, §5, p.18][Hyeon2025]). -/
structure IsLadicRepresentation (ρ : Representation ℚ_[ℓ] G V) : Prop where
  finiteDimensional : FiniteDimensional ℚ_[ℓ] V
  isTopologicalAddGroup : IsTopologicalAddGroup V
  continuousSMul : ContinuousSMul ℚ_[ℓ] V
  t2Space : T2Space V
  continuous : Continuous fun p : G × V ↦ ρ p.1 p.2

end Atlas.Knowledge
