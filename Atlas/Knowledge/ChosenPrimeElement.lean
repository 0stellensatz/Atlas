import Mathlib
import Atlas.Knowledge.PrimeElement

/-!
# chosen prime elements

The reciprocity construction's fixed choice: surjectivity of the normalized
valuation supplies a prime element in every finite abstract field, and the
construction picks one once. Any two prime elements differ by a unit —
additively, their difference has value zero — which is what the later
independence arguments run on (#104).

## Main definitions

* `ValuationData.chosenPrimeElement` — the chosen prime element of a finite
  abstract field.

## Main statements

* `ValuationData.valuationAt_chosenPrimeElement` — the choice has value `1`;
  proved.
* `ValuationData.sub_mem_unitAddSubgroup_of_prime` — two prime elements
  differ by a unit; proved.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

/-- **The chosen prime element of a finite abstract field**, from the
surjectivity of the normalized valuation; the later independence lemmas show
the reciprocity class does not depend on this choice ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/PrimeChoice.lean:27`]
[Yamaguchi2026]). -/
def chosenPrimeElement (v : ValuationData D A) (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field :=
  Classical.choose (v.normalizedValuation_surjective K v.oneValue)

/-- The chosen prime element has value `1` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/PrimeChoice.lean:33`]
[Yamaguchi2026]). -/
@[simp]
theorem valuationAt_chosenPrimeElement (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    v.valuationAt K (v.chosenPrimeElement K) = v.oneValue :=
  Classical.choose_spec (v.normalizedValuation_surjective K v.oneValue)

/-- The chosen prime element is prime. -/
theorem chosenPrimeElement_isPrime (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    v.IsPrimeElement K (v.chosenPrimeElement K) :=
  v.valuationAt_chosenPrimeElement K

/-- **Two prime elements differ by a unit**, in additive notation
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/PrimeChoice.lean:45`]
[Yamaguchi2026]). -/
theorem sub_mem_unitAddSubgroup_of_prime
    (v : ValuationData D A) (K : FiniteAbstractField G)
    {π π' : ambientFixedAddSubgroup A K.field}
    (hπ : v.IsPrimeElement K π) (hπ' : v.IsPrimeElement K π') :
    π' - π ∈ v.unitAddSubgroup K := by
  rw [v.mem_unitAddSubgroup_iff, map_sub, hπ, hπ']
  exact sub_self _

/-- A prime element differs from the chosen one by a unit
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/PrimeChoice.lean:54`]
[Yamaguchi2026]). -/
theorem sub_chosenPrimeElement_mem_unitAddSubgroup
    (v : ValuationData D A) (K : FiniteAbstractField G)
    {π : ambientFixedAddSubgroup A K.field}
    (hπ : v.IsPrimeElement K π) :
    π - v.chosenPrimeElement K ∈ v.unitAddSubgroup K :=
  v.sub_mem_unitAddSubgroup_of_prime
    K (v.chosenPrimeElement_isPrime K) hπ

end ValuationData

end

end Atlas.Knowledge
