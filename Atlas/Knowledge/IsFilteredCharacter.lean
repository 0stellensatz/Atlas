import Mathlib
import Atlas.Knowledge.FilteredModule

/-!
# character of a filtered module

The characters of the source's §4: continuous `R`-linear maps from a filtered module into
`Q(R) ⧸ R`, the fraction field modulo the ring, carrying the discrete topology. Continuity for
the filtration topology of `Atlas.Knowledge.FilteredModule` against a discrete target is
openness of the kernel, which is the kernel containing a filtration step—the form taken as the
definition, so that no topology enters the layer. The jumps of a character are the indices
where the image of the chain moves, and the collection of jump sets `𝒥_{M_•}` over all
characters is the invariant the source's §4 computes: on the free models it is the jump sets
of `Atlas.Knowledge.FreeFiltered`'s shift, and on a quasi-free module its complement inside
the extended jump sets is cut out by the criterion of `Atlas.Knowledge.CharacterExclusion`.

## Main definitions

* `fractionQuotient` — `Q(R) ⧸ R` as an `R`-module.
* `IsFilteredCharacter` — the kernel contains a filtration step.
* `characterJumps` — the indices where the image of the chain moves: the source's `J_χ`.
* `characterJumpSets` — the sets of jumps of characters: the source's `𝒥_{M_•}`.

## Implementation notes

The target is the module quotient of the fraction field by the range of the algebra map,
Mathlib's `FractionRing` playing the source's `Q(R)`. The source's characters are continuous
for the filtration topology on `M₁` and the discrete topology on the target; a linear map to a
discrete target is continuous exactly when its kernel is open, and an open submodule in the
filtration topology is one containing a step, so the predicate quantifies over the step and no
topological structure is formed. The jumps are stated on images of the chain under the
character, `χ (M_i) ≠ χ (M_{i+1})` as submodules; nothing asks the character to be nonzero,
and the zero character has empty jump set, which is a member of `𝒥_{M_•}` as the source
intends.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

variable {R : Type*} [CommRing R] [IsDomain R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The `R`-module `Q(R) ⧸ R`: the fraction field modulo the image of the ring, the target of
the source's characters ([Pagano 2022, Def. 4.1, p.435][Pagano2022]). -/
abbrev fractionQuotient (R : Type*) [CommRing R] [IsDomain R] :=
  FractionRing R ⧸ LinearMap.range (Algebra.linearMap R (FractionRing R))

/-- A **character** of a filtered module: an `R`-linear map into `Q(R) ⧸ R` whose kernel
contains a filtration step—continuity for the filtration topology against the discrete target,
taken in its algebraic form ([Pagano 2022, Def. 4.1, p.435][Pagano2022]). -/
def IsFilteredCharacter (F : FilteredModule R M) (χ : M →ₗ[R] fractionQuotient R) : Prop :=
  ∃ i, F.filt i ≤ LinearMap.ker χ

/-- The **jumps** of a character: the indices where the image of the chain moves—the source's
`J_χ`, the set of `i` with `χ (M_i) ≠ χ (M_{i+1})`
([Pagano 2022, Def. 4.1, p.435][Pagano2022]). -/
noncomputable def characterJumps (F : FilteredModule R M)
    (χ : M →ₗ[R] fractionQuotient R) : Set ℕ+ :=
  {i | Submodule.map χ (F.filt i) ≠ Submodule.map χ (F.filt (i + 1))}

/-- The **jump sets of the characters** of a filtered module: the source's `𝒥_{M_•}`, the
collection of `J_χ` as `χ` ranges over the characters
([Pagano 2022, Def. 4.1, p.435][Pagano2022]). -/
def characterJumpSets (F : FilteredModule R M) : Set (Set ℕ+) :=
  {A | ∃ χ : M →ₗ[R] fractionQuotient R, IsFilteredCharacter F χ ∧ A = characterJumps F χ}

end Atlas.Knowledge
