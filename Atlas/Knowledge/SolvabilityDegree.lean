import Mathlib
import Atlas.Knowledge.IsMLFType
import Atlas.Knowledge.IsMStepSolvable

/-!
# solvability degree

The **solvability degree** of a topological group: the least `m` for which the group is
`m`-step solvable `Atlas.Knowledge.IsMStepSolvable`. The source introduces it for a group of
MLF^m-type (`IsMLFmType`, in `Atlas.Knowledge.IsMLFType`), where it recovers the exponent:
`solvabilityDegree G = m`, so that the `m` in "MLF^m-type" is determined by the group and not
part of the data. That recovery is the first group-theoretic reconstruction of the paper, and
the reason its main theorems can quantify over groups rather than over pairs of a group and a
level.

## Main definitions

* `solvabilityDegree` — `sInf` of the set of `m` with `IsMStepSolvable G m`.

## Main statements

* `IsMLFmType.isMStepSolvable` — a group of MLF^m-type is `m`-step solvable; with
  `solvabilityDegree_le` this bounds `solvabilityDegree G ≤ m`. Proved by computing the closed
  derived series of the quotient through `Atlas.Knowledge.MStepSolvableQuotient`.
* `IsMLFmType.solvabilityDegree_eq` — `solvabilityDegree G = m` on the nose. Claim recorded
  ahead of its proof: the missing half is that `G_K` is not solvable, which is the
  wild-inertia part of `Atlas.Knowledge.AbsoluteGaloisProsolvability`.

## Implementation notes

The `sInf` is over `ℕ` and takes the junk value `0` when no term of the closed derived series
is trivial—`solvabilityDegree` of a group that is not solvable at any level is `0`, as is that
of the trivial group. The source only ever applies the degree to groups of MLF^m-type, where
the set is nonempty and the infimum is honest.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

universe u

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The **solvability degree** of a topological group: the least `m` for which the `m`-th term
of the closed derived series is trivial ([Hyeon 2025, §2 Rem. (2), p.9][Hyeon2025]). -/
noncomputable def solvabilityDegree : ℕ :=
  sInf {m | IsMStepSolvable G m}

variable {G}

theorem solvabilityDegree_le {m : ℕ} (h : IsMStepSolvable G m) : solvabilityDegree G ≤ m :=
  Nat.sInf_le h

/-- A group of MLF^m-type is `m`-step solvable: the closed derived series of `G_K^m` is the
image of the series of `G_K`, whose `m`-th term is the kernel of the projection
([Hyeon 2025, §2 Rem. (2), p.9][Hyeon2025]). -/
theorem IsMLFmType.isMStepSolvable {m : ℕ} (h : IsMLFmType.{u} G m) : IsMStepSolvable G m := by
  obtain ⟨K, _, _, _, _, ⟨e⟩⟩ := h
  haveI : IsGalois K (AlgebraicClosure K) := ⟨⟩
  haveI : CompactSpace (Field.absoluteGaloisGroup K) :=
    inferInstanceAs (CompactSpace (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
  haveI : T2Space (Field.absoluteGaloisGroup K) :=
    inferInstanceAs (T2Space (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
  exact (mStepSolvableQuotient.isMStepSolvable (Field.absoluteGaloisGroup K) m).congr e.symm

/-- The solvability degree of a group of MLF^m-type is exactly `m`, so the level is determined
by the group. Claim recorded ahead of its proof: what is missing is that the series of `G_K`
does not reach `⊥` at any finite stage ([Hyeon 2025, §2 Rem. (2), p.9][Hyeon2025]). -/
theorem IsMLFmType.solvabilityDegree_eq {m : ℕ} (h : IsMLFmType.{u} G m) :
    solvabilityDegree G = m := by
  sorry

end Atlas.Knowledge
