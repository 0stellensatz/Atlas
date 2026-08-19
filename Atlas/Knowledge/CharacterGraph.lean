import Mathlib
import Atlas.Knowledge.IsFilteredCharacter

/-!
# graph of a character of a free model

The pair `(A_χ, b_χ)` the source attaches to a character of a free model, carried as its graph
like every pair of the jump-set layer: `A_χ` is the set of levels whose block the character
does not kill, and `b_χ` sends such a level to the least power of the uniformizer killing the
character on its block. On these graphs the source's regularization
`Atlas.Knowledge.CharacterRegularization` operates: a filtered automorphism carries the graph
onto its maximal points, a jump-pair graph, and the jumps of the character are then read off
it.

## Main definitions

* `blockSubmodule` — the vectors of a model supported on one level.
* `characterOrder` — `b_χ`: the least positive power of the uniformizer killing the character
  on a block.
* `characterGraph` — the graph of `(A_χ, b_χ)`.

## Implementation notes

A block of the index `D` is the submodule of vectors vanishing off one level, the reading of
the source's `proj_i`-images that needs no decomposition of the model; it needs no valuation,
so it is stated over a domain, while the order and the graph bind the discrete valuation ring
explicitly—a `variable` block would drop the unmentioned instance, and away from it the `sInf`
below loses its meaning. The order is an `sInf` over the positive `r` with `π ^ r` killing the
character's block image; over a discrete valuation ring every element of `Q(R) ⧸ R` is killed
by a power of the uniformizer and a block is finitely generated, so the set is nonempty at
*every* block and the `sInf` genuine—at a killed block the value is `1`, which the graph never
reads, its filter keeping exactly the unkilled levels. The uniformizer is guarded by
irreducibility as in `Atlas.Knowledge.IsStarQuotient`; the value does not depend on the
choice, two uniformizers differing by a unit. `Nat.toPNat'` on the order is exact on the
graph, the order being at least `1` wherever the set is nonempty.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The **block** of a level in a free model: the submodule of vectors supported on the
indices of that level—the image of the source's `proj_i`
([Pagano 2022, Def. 4.2, p.436][Pagano2022]). -/
def blockSubmodule (D : Finset (ℕ+ × ℕ)) (i : ℕ+) : Submodule R (↥D → R) where
  carrier := {v | ∀ j : ↥D, (j : ℕ+ × ℕ).1 ≠ i → v j = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun ha hb j hj => by simp [ha j hj, hb j hj]
  smul_mem' := fun c v hv j hj => by simp [hv j hj]

set_option linter.unusedVariables false in
-- The guard `hπ` is not consumed by the formula—the value is independent of the choice of
-- uniformizer—but the notion is the source's only at one, and the guard keeps junk scalars
-- unstatable.
/-- The **order** `b_χ` of a character at a level: the least positive power of the uniformizer
killing the character on the block—`sInf` of the killing exponents, a nonempty set over a
discrete valuation ring, with value `1` at a killed block, which the graph never reads
([Pagano 2022, Def. 4.2, p.436][Pagano2022]). -/
noncomputable def characterOrder [IsDiscreteValuationRing R] {D : Finset (ℕ+ × ℕ)} {π : R}
    (hπ : Irreducible π) (χ : (↥D → R) →ₗ[R] fractionQuotient R) (a : ℕ+) : ℕ :=
  sInf {r : ℕ | 1 ≤ r ∧ ∀ v ∈ blockSubmodule D a, π ^ r • χ v = 0}

open Classical in
/-- The **graph of a character** of a free model: one point per level whose block the
character does not kill, paired with its order—the source's `(A_χ, b_χ)`, carried as a graph
([Pagano 2022, Def. 4.2, p.436][Pagano2022]). -/
noncomputable def characterGraph [IsDiscreteValuationRing R] {D : Finset (ℕ+ × ℕ)} {π : R}
    (hπ : Irreducible π) (χ : (↥D → R) →ₗ[R] fractionQuotient R) : Finset (ℕ+ × ℕ+) :=
  ((D.image Prod.fst).filter fun i => Submodule.map χ (blockSubmodule D i) ≠ ⊥).image
    fun a => (a, (characterOrder hπ χ a).toPNat')

end Atlas.Knowledge
