import Mathlib

/-!
# filtered profinite group

A **filtered profinite group** is a profinite group carrying a *filtration*: a family of closed
normal subgroups indexed by the nonnegative reals, decreasing as the index grows. Both anabelian
source papers state their main theorems on this structure—there the group is an absolute Galois
group and the filtration is its upper-numbering ramification filtration—and the isomorphisms the
theorems are about are the filtration-preserving ones, `Atlas.Knowledge.FilteredIso`, taken
modulo inner automorphisms in `Atlas.Knowledge.OutFilt`.

## Main definitions

* `FilteredProfiniteGroup` — a `ProfiniteGrp` bundled with an antitone `ℝ≥0`-indexed family of
  closed normal subgroups.

## Implementation notes

The sources differ on the index set: the filtration ranges over the positive reals in
[Mochizuki 1997, Def. 2.3, p.503][Mochizuki1997] and over `[0, +∞)` in
[Hyeon 2025, §2, p.6][Hyeon2025]. The index here is `ℝ≥0`, following the latter, which loses
nothing: a filtration in the former's sense is recovered by ignoring the value at `0`, and for
the ramification filtrations both papers intend, the value at `0` is the inertia subgroup and is
worth keeping.

The group is bundled, extending Mathlib's `ProfiniteGrp`, because the outer-isomorphism set
`Atlas.Knowledge.OutFilt` is indexed by *pairs* of filtered groups, which wants each of the pair
to be a term. The filtration lands in plain `Subgroup`s, with closedness and normality as
separate fields rather than bundled into the carrier's type, keeping the whole `Subgroup` API
applicable to its terms.

## References

* [Mochizuki1997] S. Mochizuki, *A version of the Grothendieck conjecture for p-adic local
  fields*, Int. J. Math. **8** (1997), 499–506.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

open scoped NNReal

namespace Atlas.Knowledge

universe u

/-- A **filtered profinite group**: a profinite group together with an antitone family of closed
normal subgroups indexed by `ℝ≥0`
([Mochizuki 1997, Def. 2.3, p.503][Mochizuki1997]; [Hyeon 2025, §2, p.6][Hyeon2025]). -/
structure FilteredProfiniteGroup extends ProfiniteGrp.{u} where
  filt : ℝ≥0 → Subgroup toProfiniteGrp
  isClosed_filt : ∀ v, IsClosed (filt v : Set toProfiniteGrp)
  normal_filt : ∀ v, (filt v).Normal
  antitone_filt : Antitone filt

namespace FilteredProfiniteGroup

instance : CoeSort FilteredProfiniteGroup.{u} (Type u) :=
  ⟨fun G ↦ G.toProfiniteGrp⟩

instance (G : FilteredProfiniteGroup) (v : ℝ≥0) : (G.filt v).Normal :=
  G.normal_filt v

end FilteredProfiniteGroup

end Atlas.Knowledge
