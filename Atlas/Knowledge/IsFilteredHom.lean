import Mathlib
import Atlas.Knowledge.FilteredModule

/-!
# filtered morphism

A **morphism of filtered modules** is a linear map carrying each filtration step into the
corresponding step of the target. The notion is a predicate on `M →ₗ[R] N` rather than a bundled
structure: everything the source does with a filtered morphism—the graded maps of
`Atlas.Knowledge.FilteredGradedPiece`, the criteria of
`Atlas.Knowledge.FilteredGradedCriterion`—consumes a linear map together with this property, and
identities and compositions stay the plain ones of `LinearMap`.

## Main definitions

* `IsFilteredHom` — the predicate: `f` maps `F.filt i` into `G.filt i` for every `i`.

## Main statements

* `IsFilteredHom.weight_le` — a filtered morphism does not decrease weights.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

variable {R : Type*} [CommRing R] {M N P : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- A **filtered morphism** from `F` to `G`: a linear map sending each `F.filt i` into `G.filt i`
([Pagano 2022, Def. 3.2, p.419][Pagano2022]). -/
def IsFilteredHom (F : FilteredModule R M) (G : FilteredModule R N) (f : M →ₗ[R] N) : Prop :=
  ∀ i : ℕ+, ∀ x ∈ F.filt i, f x ∈ G.filt i

namespace IsFilteredHom

variable {F : FilteredModule R M} {G : FilteredModule R N} {H : FilteredModule R P}

theorem id (F : FilteredModule R M) : IsFilteredHom F F LinearMap.id := fun _ _ hx => hx

theorem comp {g : N →ₗ[R] P} {f : M →ₗ[R] N} (hg : IsFilteredHom G H g)
    (hf : IsFilteredHom F G f) : IsFilteredHom F H (g ∘ₗ f) :=
  fun i x hx => hg i _ (hf i x hx)

/-- A filtered morphism does not decrease weights: `w_F x ≤ w_G (f x)`. This is how the source
uses the condition throughout §3 ([Pagano 2022, §3.2, p.419][Pagano2022]). -/
theorem weight_le {f : M →ₗ[R] N} (hf : IsFilteredHom F G f) (x : M) :
    F.weight x ≤ G.weight (f x) :=
  FilteredModule.le_of_forall_coe_le fun i hi =>
    G.le_weight_iff.mpr (hf i x (F.le_weight_iff.mp hi))

end IsFilteredHom

end Atlas.Knowledge
