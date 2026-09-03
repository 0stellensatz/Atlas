import Mathlib

/-!
# absolute finite quotient equivalence

Every open normal subgroup `N` of the abelianized absolute Galois group
of a characteristic-zero field cuts out a finite abelian Galois
subextension of the algebraic closure — the fixed field of its pullback
— and the quotient by `N` is canonically, as a topological group, the
actual Galois group of that subextension: the open-subgroup side of the
dictionary between finite quotients of
`Field.absoluteGaloisGroupAbelianization K` and finite abelian
subextensions, on the target side of the absolute Artin map (#104).

## Main definitions

* `absoluteFiniteQuotientPreimage` — the pullback of `N` to the
  absolute Galois group, an open normal subgroup.
* `absoluteFiniteQuotientField` — the fixed field of the pullback.
* `absoluteFiniteQuotientMulEquiv` — the quotient by `N` as the Galois
  group of the fixed field.
* `absoluteFiniteQuotientEquiv` — its topological upgrade.

## Main statements

* `absoluteFiniteQuotientPreimage_map_eq` — pushing the pullback
  forward recovers `N`; proved.
* `absoluteFiniteQuotientMulEquiv_mk_mk`,
  `absoluteFiniteQuotientEquiv_mk_mk` — on representatives the
  identifications are restriction to the fixed field; proved.
* `absoluteFiniteQuotientField_isGalois`,
  `absoluteFiniteQuotientField_finiteDimensional`,
  `absoluteFiniteQuotientField_isAbelianGalois` — the fixed field is a
  finite abelian Galois subextension; proved.

## Implementation notes

The ambient conversion of the arc: the source works over its pinned
`SeparableClosure K`, the layer over `AlgebraicClosure K` with
`[CharZero K]` — the hypothesis that makes the closure Galois, which
the infinite Galois correspondence needs; the pullbacks with their
normality, the containment and pushforward lemmas, and the bare
fixed-field definition are stated without it, the two lemmas moved
ahead of the fixed field — the source states them after the finiteness
instances — so the hypothesis enters once. The source's `ProfiniteGrp`
bundling is dropped: `localAbsoluteAbelianProfinite` and its
`local instance` `CommGroup` have no counterparts — open normal
subgroups are taken directly on Mathlib's topological group
`Field.absoluteGaloisGroupAbelianization K`, whose `CommGroup` instance
Mathlib supplies; nothing below needs the bundle's compactness or
Hausdorffness, and the transitions brick can re-bundle if its limits
do. The source's named quotient map
`localAbsoluteAbelianizationQuotientMap` is inlined to the layer's
established spelling
`QuotientGroup.mk' (commutator (Field.absoluteGaloisGroup K)).topologicalClosure`,
the one `Atlas.Knowledge.IsLocalReciprocity` speaks; with it the
containment lemma is renamed
`commutator_topologicalClosure_le_absoluteFiniteQuotientPreimage`, and
`finiteQuotientPreimage_map_eq` takes the file's stem. The closed
pullback is typed at the automorphism-group spelling
`AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K`, since instance search
does not unfold the `Field.absoluteGaloisGroup` definition, and the
finiteness proof reads openness on `carrier`, where the source's `Set`
ascription does not elaborate across that seam; the source's
`absoluteFiniteQuotientPreimageMap_normal` is dropped, Mathlib's
`QuotientGroup.map_normal` supplying it by search.
`absoluteFiniteQuotientEquiv_mk_mk` is `rfl` — every link of the
composite is definitional on representatives in current Mathlib — where
the source runs a rewrite chain, and the `IsAbelianGalois` instance
takes commutativity of the quotient from Mathlib's `CommGroup` instance
where the source rebuilds it by hand under its local instance. The
fixed field of the pullback together with
`absoluteFiniteQuotientPreimage_map_eq` is the dictionary whose
existential form `Atlas.Knowledge.IsLocalReciprocity` proves privately
on the way to uniqueness. Everything else ports token-for-token up to
proof shape — normality fields left to the structure's autoParam, a
`change` made vacuous by the inlined quotient map, term mode for the
topological upgrade — and the file is the source's
`LocalClassFieldTheory/Infinite/AbsoluteFiniteQuotients.lean` whole.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable (K : Type*) [Field K]

/-- The open normal pullback in the absolute Galois group of an open
normal subgroup of its topological abelianization ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteFiniteQuotients.lean:45`]
[Yamaguchi2026]). -/
def absoluteFiniteQuotientPreimage
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    OpenNormalSubgroup (Field.absoluteGaloisGroup K) where
  toSubgroup := N.toSubgroup.comap
    (QuotientGroup.mk' (commutator (Field.absoluteGaloisGroup K)).topologicalClosure)
  isOpen' := N.isOpen'.preimage QuotientGroup.continuous_mk

/-- The same pullback, packaged as a closed subgroup for the infinite
Galois correspondence — at the automorphism-group spelling
([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteFiniteQuotients.lean:55`]
[Yamaguchi2026]). -/
def absoluteFiniteQuotientClosedPreimage
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    ClosedSubgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) where
  toSubgroup := (absoluteFiniteQuotientPreimage K N).toSubgroup
  isClosed' := Subgroup.isClosed_of_isOpen _
    (absoluteFiniteQuotientPreimage K N).isOpen'

/-- The closed pullback of an open normal subgroup of the
abelianization is normal ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteFiniteQuotients.lean:63`]
[Yamaguchi2026]). -/
instance absoluteFiniteQuotientClosedPreimage_normal
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    (absoluteFiniteQuotientClosedPreimage K N).Normal :=
  (absoluteFiniteQuotientPreimage K N).isNormal'

/-- The topological commutator closure is contained in every
pulled-back open normal subgroup ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteFiniteQuotients.lean:106`]
[Yamaguchi2026]). -/
theorem commutator_topologicalClosure_le_absoluteFiniteQuotientPreimage
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    (commutator (Field.absoluteGaloisGroup K)).topologicalClosure ≤
      (absoluteFiniteQuotientPreimage K N).toSubgroup := by
  intro σ hσ
  change QuotientGroup.mk'
    (commutator (Field.absoluteGaloisGroup K)).topologicalClosure σ ∈ N
  have hmk : QuotientGroup.mk'
      (commutator (Field.absoluteGaloisGroup K)).topologicalClosure σ = 1 :=
    (QuotientGroup.eq_one_iff σ).2 hσ
  rw [hmk]
  exact N.one_mem

/-- Pullback followed by image under the abelianization quotient map
recovers the original open normal subgroup ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteFiniteQuotients.lean:119`]
[Yamaguchi2026]). -/
theorem absoluteFiniteQuotientPreimage_map_eq
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    (absoluteFiniteQuotientPreimage K N).toSubgroup.map
        (QuotientGroup.mk' (commutator (Field.absoluteGaloisGroup K)).topologicalClosure) =
      N.toSubgroup :=
  Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective
      (commutator (Field.absoluteGaloisGroup K)).topologicalClosure)
    N.toSubgroup

/-- The finite subextension cut out by an open normal subgroup of the
abelianized absolute Galois group: the fixed field of its pullback
([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteFiniteQuotients.lean:71`]
[Yamaguchi2026]). -/
def absoluteFiniteQuotientField
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.fixedField (absoluteFiniteQuotientPreimage K N).toSubgroup

variable [CharZero K]

/-- The fixed field attached to an open normal subgroup of the
abelianization is Galois over the base ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteFiniteQuotients.lean:78`]
[Yamaguchi2026]). -/
instance absoluteFiniteQuotientField_isGalois
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    IsGalois K (absoluteFiniteQuotientField K N) := by
  apply (InfiniteGalois.normal_iff_isGalois (absoluteFiniteQuotientField K N)).1
  change (IntermediateField.fixedField
    (absoluteFiniteQuotientClosedPreimage K N).toSubgroup).fixingSubgroup.Normal
  rw [InfiniteGalois.fixingSubgroup_fixedField
    (absoluteFiniteQuotientClosedPreimage K N)]
  infer_instance

/-- The fixed field attached to an open normal subgroup of the
abelianization is finite-dimensional over the base ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteFiniteQuotients.lean:91`]
[Yamaguchi2026]). -/
instance absoluteFiniteQuotientField_finiteDimensional
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    FiniteDimensional K (absoluteFiniteQuotientField K N) := by
  apply (InfiniteGalois.isOpen_iff_finite (absoluteFiniteQuotientField K N)).1
  change IsOpen (IntermediateField.fixedField
    (absoluteFiniteQuotientClosedPreimage K N).toSubgroup).fixingSubgroup.carrier
  rw [InfiniteGalois.fixingSubgroup_fixedField
    (absoluteFiniteQuotientClosedPreimage K N)]
  exact (absoluteFiniteQuotientPreimage K N).isOpen'

/-- The algebraic finite quotient identification, from the third
isomorphism theorem and the infinite Galois correspondence
([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteFiniteQuotients.lean:142`]
[Yamaguchi2026]). -/
def absoluteFiniteQuotientMulEquiv
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    Field.absoluteGaloisGroupAbelianization K ⧸ N.toSubgroup ≃*
      (absoluteFiniteQuotientField K N ≃ₐ[K] absoluteFiniteQuotientField K N) :=
  (QuotientGroup.quotientMulEquivOfEq (absoluteFiniteQuotientPreimage_map_eq K N).symm).trans
    ((QuotientGroup.quotientQuotientEquivQuotient
      (commutator (Field.absoluteGaloisGroup K)).topologicalClosure
      (absoluteFiniteQuotientPreimage K N).toSubgroup
      (commutator_topologicalClosure_le_absoluteFiniteQuotientPreimage K N)).trans
        (InfiniteGalois.normalAutEquivQuotient
          (absoluteFiniteQuotientClosedPreimage K N)))

/-- On representatives, the algebraic finite quotient identification is
literal restriction to the corresponding fixed field — the algebraic
reading of the topological representative formula ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteFiniteQuotients.lean:171`]
[Yamaguchi2026]). -/
@[simp]
theorem absoluteFiniteQuotientMulEquiv_mk_mk
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K))
    (σ : Field.absoluteGaloisGroup K) :
    absoluteFiniteQuotientMulEquiv K N
        (QuotientGroup.mk
          (QuotientGroup.mk σ : Field.absoluteGaloisGroupAbelianization K)) =
      AlgEquiv.restrictNormalHom (absoluteFiniteQuotientField K N) σ :=
  rfl

/-- The canonical topological finite quotient identification: both
sides are discrete, the quotient because `N` is open and the Galois
group because the fixed field is finite-dimensional ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteFiniteQuotients.lean:156`]
[Yamaguchi2026]). -/
def absoluteFiniteQuotientEquiv
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    Field.absoluteGaloisGroupAbelianization K ⧸ N.toSubgroup ≃ₜ*
      (absoluteFiniteQuotientField K N ≃ₐ[K] absoluteFiniteQuotientField K N) :=
  letI : DiscreteTopology
      (Field.absoluteGaloisGroupAbelianization K ⧸ N.toSubgroup) :=
    QuotientGroup.discreteTopology N.isOpen'
  { absoluteFiniteQuotientMulEquiv K N with
    continuous_toFun := continuous_of_discreteTopology
    continuous_invFun := continuous_of_discreteTopology }

/-- On representatives, the finite quotient identification is literal
restriction to the corresponding fixed field ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteFiniteQuotients.lean:171`]
[Yamaguchi2026]). -/
@[simp]
theorem absoluteFiniteQuotientEquiv_mk_mk
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K))
    (σ : Field.absoluteGaloisGroup K) :
    absoluteFiniteQuotientEquiv K N
        (QuotientGroup.mk
          (QuotientGroup.mk σ : Field.absoluteGaloisGroupAbelianization K)) =
      AlgEquiv.restrictNormalHom (absoluteFiniteQuotientField K N) σ :=
  rfl

/-- The fixed field attached to an open normal subgroup of the
abelianization is abelian Galois: its Galois group is a quotient of the
commutative abelianization ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteFiniteQuotients.lean:199`]
[Yamaguchi2026]). -/
instance absoluteFiniteQuotientField_isAbelianGalois
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    IsAbelianGalois K (absoluteFiniteQuotientField K N) where
  is_comm := ⟨fun σ τ => (absoluteFiniteQuotientMulEquiv K N).symm.injective (by
    rw [map_mul, map_mul]
    exact mul_comm _ _)⟩

end

end Atlas.Knowledge
