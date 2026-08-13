import Mathlib

/-!
# closed derived series

The **closed derived series** of a topological group `G`: the descending sequence of closed
normal subgroups starting at `G` itself, each next term the topological closure of the commutator
subgroup of the previous. It differs from Mathlib's `derivedSeries` in taking the closure at
every step, which is what makes each term a closed subgroup—for a profinite `G` the objects that
correspond to subextensions under the Galois correspondence. Its vanishing defines
`Atlas.Knowledge.IsMStepSolvable`, and the quotient by its `m`-th term is the maximal `m`-step
solvable quotient `Atlas.Knowledge.MStepSolvableQuotient`.

## Main definitions

* `closedDerivedSeries` — the series `G = G^[0] ⊇ G^[1] ⊇ ⋯`, with
  `G^[m + 1] = closure ⁅G^[m], G^[m]⁆`.

## Main statements

* `isClosed_closedDerivedSeries`, `closedDerivedSeries_normal` — each term is closed and normal.
* `closedDerivedSeries_antitone` — the series descends.
* `derivedSeries_le_closedDerivedSeries` — it lies above Mathlib's `derivedSeries` termwise.
* `closedDerivedSeries_one` — its first term is the subgroup Mathlib's
  `TopologicalAbelianization` quotients by, definitionally.

## Implementation notes

The definition asks for a topological group but not for profiniteness or Hausdorffness: closure
and normality need neither. The source also notes each term is characteristic; that is deferred
until something needs it, since for a topological group the right statement (invariance under
*continuous* automorphisms) is weaker than `Subgroup.Characteristic`.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The **closed derived series** of a topological group: `closedDerivedSeries G 0 = ⊤`, and each
following term is the topological closure of the commutator subgroup of the previous
([Hyeon 2025, §2, p.8][Hyeon2025]). -/
def closedDerivedSeries : ℕ → Subgroup G
  | 0 => ⊤
  | m + 1 => (⁅closedDerivedSeries m, closedDerivedSeries m⁆).topologicalClosure

@[simp]
theorem closedDerivedSeries_zero : closedDerivedSeries G 0 = ⊤ :=
  rfl

theorem closedDerivedSeries_succ (m : ℕ) :
    closedDerivedSeries G (m + 1)
      = (⁅closedDerivedSeries G m, closedDerivedSeries G m⁆).topologicalClosure :=
  rfl

/-- The first term of the closed derived series is the closure of the commutator subgroup—the
subgroup Mathlib's `TopologicalAbelianization` is the quotient by. -/
theorem closedDerivedSeries_one :
    closedDerivedSeries G 1 = (commutator G).topologicalClosure :=
  rfl

theorem isClosed_closedDerivedSeries (m : ℕ) :
    IsClosed (closedDerivedSeries G m : Set G) := by
  cases m with
  | zero => simp
  | succ m => exact Subgroup.isClosed_topologicalClosure _

instance closedDerivedSeries_normal (m : ℕ) : (closedDerivedSeries G m).Normal := by
  induction m with
  | zero =>
    rw [closedDerivedSeries_zero]
    infer_instance
  | succ m ih =>
    haveI := ih
    exact Subgroup.is_normal_topologicalClosure _

theorem closedDerivedSeries_succ_le (m : ℕ) :
    closedDerivedSeries G (m + 1) ≤ closedDerivedSeries G m :=
  Subgroup.topologicalClosure_minimal _ (Subgroup.commutator_le_self _)
    (isClosed_closedDerivedSeries G m)

theorem closedDerivedSeries_antitone : Antitone (closedDerivedSeries G) :=
  antitone_nat_of_succ_le (closedDerivedSeries_succ_le G)

/-- The closed derived series lies above the abstract derived series termwise; for a discrete
group the two coincide. -/
theorem derivedSeries_le_closedDerivedSeries (m : ℕ) :
    derivedSeries G m ≤ closedDerivedSeries G m := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    exact (Subgroup.commutator_mono ih ih).trans (Subgroup.le_topologicalClosure _)

end Atlas.Knowledge
