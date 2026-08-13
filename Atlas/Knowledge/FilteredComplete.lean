import Mathlib
import Atlas.Knowledge.FilteredModule

/-!
# complete filtered module

Completeness of a filtered module, stated without a metric. The source puts a metric
`d (x, y) = c ^ w (x - y)` on a filtered module and speaks of completeness of that metric space;
a sequence is Cauchy for it exactly when its tails are eventually constant modulo each
filtration step, and it converges to `y` exactly when `y` agrees with it modulo each step. The
definition here says just that—every *coherent* sequence of approximations has a limit—which is
the only face of completeness the source's arguments use, and it keeps the knowledge layer free
of the topology that the metric would drag in. The statement consuming this is part (a) of
`Atlas.Knowledge.FilteredGradedCriterion`.

## Main definitions

* `FilteredModule.IsComplete` — every sequence `x` with `x j - x i ∈ filt i` for `i ≤ j` admits
  `y` with `y - x i ∈ filt i` for all `i`.

## Main statements

* `FilteredModule.limit_unique` — such a `y` is unique, the filtration being separated; this is
  the Hausdorff half of the source's metric picture and needs no completeness.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

namespace FilteredModule

/-- A filtered module is **complete** when every coherent sequence of approximations has a
limit: `x j - x i ∈ filt i` for `i ≤ j` yields a `y` with `y - x i ∈ filt i` for every `i`. This
is completeness for the source's filtration metric, without the metric
([Pagano 2022, §3.2.2, p.420][Pagano2022]). -/
def IsComplete (F : FilteredModule R M) : Prop :=
  ∀ x : ℕ+ → M, (∀ i j, i ≤ j → x j - x i ∈ F.filt i) → ∃ y, ∀ i, y - x i ∈ F.filt i

/-- Limits of coherent sequences are unique: the filtration is separated
([Pagano 2022, §3.2.2, p.420][Pagano2022]). -/
theorem limit_unique (F : FilteredModule R M) {x : ℕ+ → M} {y y' : M}
    (hy : ∀ i, y - x i ∈ F.filt i) (hy' : ∀ i, y' - x i ∈ F.filt i) : y = y' := by
  have hmem : y - y' ∈ ⨅ i, F.filt i := by
    refine Submodule.mem_iInf _ |>.mpr fun i => ?_
    have h := (F.filt i).sub_mem (hy i) (hy' i)
    simpa using h
  rw [F.iInf_filt_eq_bot, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hmem

end FilteredModule

end Atlas.Knowledge
