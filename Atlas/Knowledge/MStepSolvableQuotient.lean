import Mathlib
import Atlas.Knowledge.ClosedDerivedSeries
import Atlas.Knowledge.IsMStepSolvable

/-!
# maximal m-step solvable quotient

The **maximal `m`-step solvable quotient** `G^m` of a topological group: the quotient of `G` by
the `m`-th term of its closed derived series `Atlas.Knowledge.ClosedDerivedSeries`. For `m = 1`
this is Mathlib's `TopologicalAbelianization`. For `G` an absolute Galois group it is the Galois
group of the maximal `m`-step solvable extension `Atlas.Knowledge.MStepSolvableExtension`, and it
is the group both main anabelian theorems take as input.

## Main definitions

* `mStepSolvableQuotient` — the quotient group `G ⧸ closedDerivedSeries G m`, with its quotient
  topology.
* `mStepSolvableQuotient.map` — the homomorphism a continuous homomorphism induces between the
  quotients, the functoriality of `G ↦ G^m`.

## Main statements

* `mStepSolvableQuotient.isMStepSolvable` — over a compact Hausdorff group the quotient is
  itself `m`-step solvable, its closed derived series being the image of the series of `G`.

## Implementation notes

The quotient map is Mathlib's own, `QuotientGroup.mk' (closedDerivedSeries G m)`, so no bespoke
projection is defined here. Maximality—every continuous morphism to an `m`-step solvable group
factors through `G^m`—is the universal property of that quotient map and is deferred until
something needs it stated. The `CommGroup` instance at `m = 1` is found through the
definitional equality with Mathlib's `TopologicalAbelianization`, which the sources' notation
`G^ab` for `G^1` presupposes.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The **maximal `m`-step solvable quotient** of a topological group: the quotient by the `m`-th
term of the closed derived series ([Hyeon 2025, §2, p.8][Hyeon2025]). -/
def mStepSolvableQuotient (m : ℕ) : Type _ :=
  G ⧸ closedDerivedSeries G m

namespace mStepSolvableQuotient

variable (m : ℕ)

instance : Group (mStepSolvableQuotient G m) :=
  inferInstanceAs (Group (G ⧸ closedDerivedSeries G m))

instance : TopologicalSpace (mStepSolvableQuotient G m) :=
  inferInstanceAs (TopologicalSpace (G ⧸ closedDerivedSeries G m))

instance : IsTopologicalGroup (mStepSolvableQuotient G m) :=
  inferInstanceAs (IsTopologicalGroup (G ⧸ closedDerivedSeries G m))

/-- The maximal `1`-step solvable quotient is the topological abelianization, and in particular
abelian—the source writes `G^ab` for `G^1` ([Hyeon 2025, §2, p.8][Hyeon2025]). -/
instance : CommGroup (mStepSolvableQuotient G 1) :=
  inferInstanceAs (CommGroup (TopologicalAbelianization G))

variable {G} {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The homomorphism a continuous homomorphism induces between the maximal `m`-step solvable
quotients—the functoriality of `G ↦ G^m`. -/
def map (f : G →* H) (hf : Continuous f) :
    mStepSolvableQuotient G m →* mStepSolvableQuotient H m :=
  QuotientGroup.map _ _ f (Subgroup.map_le_iff_le_comap.mp (map_closedDerivedSeries_le f hf m))

theorem map_surjective (f : G →* H) (hf : Continuous f) (hsurj : Function.Surjective f) :
    Function.Surjective (map m f hf) := by
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (closedDerivedSeries H m) x
  obtain ⟨g, rfl⟩ := hsurj y
  exact ⟨QuotientGroup.mk g, rfl⟩

variable (G)

/-- Over a compact Hausdorff group the maximal `m`-step solvable quotient is itself `m`-step
solvable: its closed derived series is the image of the series of `G`, whose `m`-th term is
exactly the kernel of the quotient map ([Hyeon 2025, §2, p.8][Hyeon2025]). -/
theorem isMStepSolvable [CompactSpace G] [T2Space G] :
    IsMStepSolvable (mStepSolvableQuotient G m) m := by
  haveI : IsClosed ((closedDerivedSeries G m : Subgroup G) : Set G) :=
    isClosed_closedDerivedSeries G m
  haveI hTG : IsTopologicalGroup (mStepSolvableQuotient G m) :=
    inferInstanceAs (IsTopologicalGroup (G ⧸ closedDerivedSeries G m))
  haveI : T2Space (mStepSolvableQuotient G m) :=
    inferInstanceAs (T2Space (G ⧸ closedDerivedSeries G m))
  have hcont : Continuous (QuotientGroup.mk' (closedDerivedSeries G m) :
      G →* mStepSolvableQuotient G m) := continuous_quotient_mk'
  -- The `@`-application hands `hTG` over directly: instance search does not connect
  -- `mStepSolvableQuotient G m` with `G ⧸ closedDerivedSeries G m` under the assignment of `H`.
  have h := @map_closedDerivedSeries G _ _ _ (mStepSolvableQuotient G m) _ _ hTG
    (QuotientGroup.mk' (closedDerivedSeries G m)) hcont hcont.isClosedMap
    (QuotientGroup.mk'_surjective _) m
  have hbot : Subgroup.map (QuotientGroup.mk' (closedDerivedSeries G m))
      (closedDerivedSeries G m) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact h.symm.trans hbot

end mStepSolvableQuotient

end Atlas.Knowledge
