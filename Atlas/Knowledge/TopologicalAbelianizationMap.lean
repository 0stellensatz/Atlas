import Mathlib

/-!
# map on topological abelianizations

A continuous group homomorphism descends through the closures of the commutator subgroups.
The descended map is continuous and evaluates on representatives by the original map.

## Main definitions

* `topologicalAbelianizationMap` — the induced homomorphism of topological abelianizations.

## Main statements

* `topologicalAbelianizationMap_mk` — evaluation on a representative.
* `topologicalAbelianizationMap_continuous` — continuity of the descended map.
-/

namespace Atlas.Knowledge

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]

/-- A continuous homomorphism induces a map on topological abelianizations. -/
noncomputable def topologicalAbelianizationMap (f : G →* H) (hf : Continuous f) :
    TopologicalAbelianization G →* TopologicalAbelianization H := by
  let q := QuotientGroup.mk' (commutator H).topologicalClosure
  have hcomm : commutator G ≤ Subgroup.comap f (commutator H).topologicalClosure := by
    intro g hg
    exact (QuotientGroup.eq_one_iff (f g)).mp
      (Abelianization.commutator_subset_ker (q.comp f) hg)
  have hclosure : (commutator G).topologicalClosure ≤
      Subgroup.comap f (commutator H).topologicalClosure :=
    Subgroup.topologicalClosure_minimal _ hcomm
      ((Subgroup.isClosed_topologicalClosure (commutator H)).preimage hf)
  exact QuotientGroup.lift (commutator G).topologicalClosure (q.comp f)
    (fun g hg => (QuotientGroup.eq_one_iff (f g)).mpr (hclosure hg))

/-- The induced map evaluates by applying the original homomorphism to a representative. -/
@[simp]
theorem topologicalAbelianizationMap_mk (f : G →* H) (hf : Continuous f) (g : G) :
    topologicalAbelianizationMap f hf (QuotientGroup.mk g) = QuotientGroup.mk (f g) := rfl

/-- The descended map of topological abelianizations is continuous. -/
theorem topologicalAbelianizationMap_continuous (f : G →* H) (hf : Continuous f) :
    Continuous (topologicalAbelianizationMap f hf) := by
  apply (QuotientGroup.isQuotientMap_mk (commutator G).topologicalClosure).continuous_iff.2
  exact QuotientGroup.continuous_mk.comp hf

end Atlas.Knowledge
