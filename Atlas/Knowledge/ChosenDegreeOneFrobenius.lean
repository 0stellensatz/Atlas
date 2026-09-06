import Mathlib
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusExponent
import Atlas.Knowledge.ProfiniteInteger

/-!
# Chosen degree-one Frobenius element

Surjectivity of the normalized degree supplies a Frobenius-semigroup
element of exponent one; the chosen object and its specification are
kept together, so the multiplicativity proof can consume a named choice
boundary (#104).

## Main definitions

* `DegreeData.chosenDegreeOneFrobeniusElement` — the chosen degree-one
  element of `G(L̃/K)`.

## Main statements

* `DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusElement` — its
  Frobenius exponent is one; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
`ZHat` is `ProfiniteInteger`, and `proCIntegerOne_pow_nat_injective` is
the layer's `ProfiniteInteger.ofAdd_one_pow_injective`.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **A chosen degree-one element of `G(L̃/K)`, packaged as an element of
the Frobenius semigroup** (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/ChosenDegreeOneFrobenius.lean:25`). -/
noncomputable def chosenDegreeOneFrobeniusElement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    D.FrobeniusElements K L hLK := by
  let hsurj := D.extensionNormalizedDegreeContinuous_surjective K L hLK
    (Multiplicative.ofAdd (1 : ProfiniteInteger))
  refine ⟨Classical.choose hsurj, 1, Nat.one_pos, ?_⟩
  rw [pow_one, ← D.extensionNormalizedDegreeContinuous_apply]
  exact Classical.choose_spec hsurj

/-- **The chosen element's Frobenius exponent is one** (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/ChosenDegreeOneFrobenius.lean:41`). -/
@[simp]
theorem frobeniusExponent_chosenDegreeOneFrobeniusElement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    D.frobeniusExponent K L hLK
        (D.chosenDegreeOneFrobeniusElement K L hLK) = 1 := by
  apply ProfiniteInteger.ofAdd_one_pow_injective
  calc
    (Multiplicative.ofAdd (1 : ProfiniteInteger)) ^
        D.frobeniusExponent K L hLK
          (D.chosenDegreeOneFrobeniusElement K L hLK) =
      D.extensionNormalizedDegree K L hLK
        (D.chosenDegreeOneFrobeniusElement K L hLK).1 :=
      (D.extensionNormalizedDegree_frobenius_eq_pow K L hLK
        (D.chosenDegreeOneFrobeniusElement K L hLK)).symm
    _ = Multiplicative.ofAdd (1 : ProfiniteInteger) := by
      rw [← D.extensionNormalizedDegreeContinuous_apply]
      change D.extensionNormalizedDegreeContinuous K L hLK
        (Classical.choose
          (D.extensionNormalizedDegreeContinuous_surjective K L hLK
            (Multiplicative.ofAdd (1 : ProfiniteInteger)))) =
          Multiplicative.ofAdd (1 : ProfiniteInteger)
      exact Classical.choose_spec
        (D.extensionNormalizedDegreeContinuous_surjective K L hLK
          (Multiplicative.ofAdd (1 : ProfiniteInteger)))
    _ = (Multiplicative.ofAdd (1 : ProfiniteInteger)) ^ (1 : ℕ) := by simp

end DegreeData

end

end Atlas.Knowledge
