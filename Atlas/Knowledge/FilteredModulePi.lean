import Mathlib
import Atlas.Knowledge.FilteredModule

/-!
# product of filtered modules

The direct product of a family of filtered modules: the product module, filtered step by step by
the products of the steps. It is the categorical direct product in the source's category of
filtered modules, and over a finite index—the only case this tranche of the source ever
needs—it coincides with the direct sum, so no separate sum construction is carried. The free
models `Atlas.Knowledge.FreeFiltered` on which the source's classification runs are finite
products of standard modules `Atlas.Knowledge.StandardFiltered` built exactly this way.

## Main definitions

* `FilteredModule.pi` — the product filtration on `Π j, M j`.

## Main statements

* `FilteredModule.mem_pi_filt` — membership, componentwise.
* `FilteredModule.weight_pi` — over a finite index, the weight of a vector is the least weight
  of its components.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

variable {R : Type*} [CommRing R] {ι : Type*} {M : ι → Type*} [∀ j, AddCommGroup (M j)]
  [∀ j, Module R (M j)]

namespace FilteredModule

/-- The **direct product** of a family of filtered modules, filtered by the products of the
steps ([Pagano 2022, §3.2.1, p.419][Pagano2022]). -/
def pi (F : ∀ j, FilteredModule R (M j)) : FilteredModule R (∀ j, M j) where
  filt i := Submodule.pi Set.univ fun j => (F j).filt i
  filt_one := by
    simp [FilteredModule.filt_one, Submodule.pi_top]
  antitone_filt := fun i j hij x hx k hk => (F k).antitone_filt hij (hx k hk)
  iInf_filt_eq_bot := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_iInf] at hx
    have hj : ∀ j, x j = 0 := by
      intro j
      have hmem : x j ∈ ⨅ i, (F j).filt i :=
        Submodule.mem_iInf _ |>.mpr fun i => hx i j (Set.mem_univ j)
      rwa [(F j).iInf_filt_eq_bot, Submodule.mem_bot] at hmem
    exact Submodule.mem_bot _ |>.mpr (funext hj)

theorem mem_pi_filt {F : ∀ j, FilteredModule R (M j)} {x : ∀ j, M j} {i : ℕ+} :
    x ∈ (pi F).filt i ↔ ∀ j, x j ∈ (F j).filt i := by
  simp [pi, Submodule.mem_pi]

/-- Over a finite index the weight of a vector in the product is the least weight of its
components—the product metric is the sup metric, said in weights
([Pagano 2022, §3.2.1, p.419][Pagano2022]). -/
theorem weight_pi [Fintype ι] (F : ∀ j, FilteredModule R (M j)) (x : ∀ j, M j) :
    (pi F).weight x = Finset.univ.inf fun j => (F j).weight (x j) := by
  refine le_antisymm ?_ ?_
  · refine le_of_forall_coe_le fun i hi => ?_
    refine Finset.le_inf fun j _ => ?_
    exact (F j).le_weight_iff.mpr (mem_pi_filt.mp ((pi F).le_weight_iff.mp hi) j)
  · refine le_of_forall_coe_le fun i hi => ?_
    refine (pi F).le_weight_iff.mpr (mem_pi_filt.mpr fun j => ?_)
    exact (F j).le_weight_iff.mp (hi.trans (Finset.inf_le (Finset.mem_univ j)))

end FilteredModule

end Atlas.Knowledge
