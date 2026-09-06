import Mathlib

/-!
# maximal abelian extension

The maximal abelian extension of a number field, as the fixed field inside the algebraic
closure of the closed commutator subgroup of the absolute Galois group: `K^ab` is what the
global reciprocity map of `Atlas.Knowledge.IsGlobalArtinMap` maps onto, and its finite
subextensions are the abelian extensions the class-field correspondence enumerates. Both
structure facts are proved here, not recorded: the extension is Galois — the commutator
closure is normal — and its Galois group is commutative. So is the *algebraic*
identification of that Galois group with Mathlib's
`Field.absoluteGaloisGroupAbelianization`, the vocabulary Phase 2's local layer speaks;
only its upgrade to a homeomorphism is the recorded claim.

## Main definitions

* `maximalAbelianExtension` — the fixed field of the closed commutator subgroup.

## Main statements

* `IsGalois` and `IsAbelianGalois` instances — proved.
* `nonempty_mulEquiv_absoluteGaloisGroupAbelianization` — `Gal (K^ab/K)` is the
  topological abelianization of the absolute Galois group, as groups; proved.
* `nonempty_continuousMulEquiv_absoluteGaloisGroupAbelianization` — the homeomorphism
  upgrade; recorded ahead of its proof.

## Implementation notes

The closure is taken in `AlgebraicClosure K` directly — the field is char-zero, so no
separable-closure detour is needed, and Mathlib's `Field.absoluteGaloisGroup` is
transparently the automorphism group of the closure. The `IsAbelianGalois` proof routes
through `InfiniteGalois.normalAutEquivQuotient` against the commutative
`Field.absoluteGaloisGroupAbelianization`, and the same equivalence proves the algebraic
identification outright; the source instead transports commutativity through a
compactness homeomorphism
(`AlgebraicNumberTheory/Galois/AbsoluteAbelianization.lean:83`, supporting chain
`:53`–`:107`, against which this file's whole route is about a third the length); the
source also carries the same object at `:37`, over the separable closure.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [NeukirchEtAl2008] J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of number fields*,
  Grundlehren der mathematischen Wissenschaften **323**, Springer Berlin Heidelberg, 2008.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

noncomputable section

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

/-- The **maximal abelian extension** `K^ab`: the fixed field of the topological closure of
the commutator subgroup of the absolute Galois group
([Milne 2020, Introduction, pp.11–12][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/Galois/AbsoluteAbelianization.lean:37`). -/
noncomputable def maximalAbelianExtension : IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.fixedField
    (Subgroup.topologicalClosure (commutator (Field.absoluteGaloisGroup K)))

instance : IsGalois K (maximalAbelianExtension K) := by
  apply (InfiniteGalois.normal_iff_isGalois (maximalAbelianExtension K)).1
  change (IntermediateField.fixedField
    (⟨(commutator (Field.absoluteGaloisGroup K)).topologicalClosure,
      Subgroup.isClosed_topologicalClosure _⟩ :
        ClosedSubgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)).toSubgroup
    ).fixingSubgroup.Normal
  rw [InfiniteGalois.fixingSubgroup_fixedField]
  exact Field.absoluteGaloisGroup.commutator_closure_isNormal K

instance : IsAbelianGalois K (maximalAbelianExtension K) where
  is_comm := ⟨fun σ τ => by
    let H : ClosedSubgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :=
      ⟨(commutator (Field.absoluteGaloisGroup K)).topologicalClosure,
        Subgroup.isClosed_topologicalClosure _⟩
    haveI : H.Normal := Field.absoluteGaloisGroup.commutator_closure_isNormal K
    have e : Field.absoluteGaloisGroupAbelianization K ≃*
        (maximalAbelianExtension K ≃ₐ[K] maximalAbelianExtension K) :=
      InfiniteGalois.normalAutEquivQuotient (k := K) (K := AlgebraicClosure K) H
    exact e.symm.injective (by
      rw [map_mul, map_mul]
      exact mul_comm (e.symm σ) (e.symm τ))⟩

/-- The Galois group of the maximal abelian extension is the topological abelianization of
the absolute Galois group, as groups — the identification that makes this item's
`Gal (K^ab/K)` and the local layer's `Field.absoluteGaloisGroupAbelianization` the same
vocabulary, proved by the same normal-quotient equivalence as the instances above
([Neukirch–Schmidt–Wingberg 2008, p.157 and Chap. VIII, p.425][NeukirchEtAl2008]). -/
theorem nonempty_mulEquiv_absoluteGaloisGroupAbelianization :
    Nonempty ((maximalAbelianExtension K ≃ₐ[K] maximalAbelianExtension K) ≃*
      Field.absoluteGaloisGroupAbelianization K) := by
  let H : ClosedSubgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :=
    ⟨(commutator (Field.absoluteGaloisGroup K)).topologicalClosure,
      Subgroup.isClosed_topologicalClosure _⟩
  haveI : H.Normal := Field.absoluteGaloisGroup.commutator_closure_isNormal K
  exact ⟨(InfiniteGalois.normalAutEquivQuotient (k := K) (K := AlgebraicClosure K) H).symm⟩

/-- The identification upgrades to a homeomorphism: the two topological groups are
isomorphic as such. Claim recorded ahead of its proof — the algebraic half is
`nonempty_mulEquiv_absoluteGaloisGroupAbelianization`, and only continuity remains
([Neukirch–Schmidt–Wingberg 2008, p.157 and Chap. VIII, p.425][NeukirchEtAl2008]). -/
theorem nonempty_continuousMulEquiv_absoluteGaloisGroupAbelianization :
    Nonempty ((maximalAbelianExtension K ≃ₐ[K] maximalAbelianExtension K) ≃ₜ*
      Field.absoluteGaloisGroupAbelianization K) := by
  sorry

end Atlas.Knowledge

end
