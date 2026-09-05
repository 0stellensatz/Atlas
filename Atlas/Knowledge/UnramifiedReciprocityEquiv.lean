import Mathlib
import Atlas.Knowledge.AbstractExtension
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.ChosenPrimeElement
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractExtension
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteAbstractFieldExtension
import Atlas.Knowledge.FiniteFieldUnitMaps
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FiniteReciprocityHom
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.PrimeElement
import Atlas.Knowledge.ReciprocityMap
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.UnitCohomologyAxiom
import Atlas.Knowledge.UnramifiedFrobeniusFixedField
import Atlas.Knowledge.UnramifiedNormQuotient
import Atlas.Knowledge.ValuationData

/-!
# Unramified reciprocity equivalence

The generator-and-order argument closing the finite reciprocity
equivalence in the unramified case: any homomorphism sending arithmetic
Frobenius to the prime class is bijective, the finite reciprocity
homomorphism does exactly that, and it is therefore promoted to the
unramified norm-quotient equivalence (#104).

## Main definitions

* `ValuationData.unramifiedReciprocity_equiv_of_generator` — the
  generator criterion's equivalence.
* `ValuationData.unramifiedReciprocityEquiv` — the unramified
  norm-quotient equivalence.

## Main statements

* `ValuationData.unramifiedReciprocity_bijective_of_generator` — the
  generator-and-order argument; proved.
* `ValuationData.unramifiedReciprocity_equiv_of_generator_apply` — the
  criterion's evaluation; proved.
* `ValuationData.unramifiedReciprocity_frobenius_image` — the generator
  calculation; proved.
* `ValuationData.unramifiedReciprocityEquiv_apply` — the equivalence's
  evaluation; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
and the ambient group is `Type u` since the #104 hoist. The degree
positivity is the layer's `degree.pos` for the source's
`degree.property`, the index identity the layer's
`subgroup_index_eq_degree`, and the extension bundle the layer's
top-level `AbstractExtension`. The generator calculation drops the
source's enrichment `letI` re-anchor — the `FiniteFieldUnitMaps`
transport instance stands in — and every declaration sheds dead
topology binders to the lint's fixpoint: the generator-criterion trio
its `[IsTopologicalGroup G]`, `[CompactSpace G]`, and `[T2Space G]`,
all simply unused, so those statements are strictly more general than
the source's; the other three their `[T2Space G]`, which was redundant
— Hausdorff synthesizes from the topological-group and
totally-disconnected binders they keep, so those statements are equally
applicable. The `FiniteFieldUnitMaps` import is referenced by no name,
carrying the transport instances above. The citations name this file by
bare basename; it lives at
`AbstractClassFieldTheory/Reciprocity/Construction/` in the source. The
source's `open`s go — the layer keeps everything in one namespace.

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

/-- **Any homomorphism sending the arithmetic Frobenius generator to
the prime class is bijective** — the prime class generates the norm
quotient, and both finite groups have order `[L : K]`
([Yamaguchi 2026, `MainFiniteReciprocity.lean:1003`][Yamaguchi2026]). -/
theorem unramifiedReciprocity_bijective_of_generator
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hUnramified :
      (AbstractExtension.mk L K.field hLK).IsUnramified D)
    (f : Additive
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup) →+
      FiniteNormQuotient A K.field L hLK)
    (hf : f (Additive.ofMul (D.unramifiedFrobenius
        (K.toFiniteResidueAbstractField D) L hLK)) =
      finiteNormClass A K.field L hLK (v.chosenPrimeElement K)) :
    Function.Bijective f := by
  let e := v.unramifiedReciprocity_valuationEquiv
    hAxiom K L hLK hUnramified
  let E : FiniteAbstractFieldExtension G :=
    FiniteAbstractFieldExtension.ofInclusion L K hLK
  letI : NeZero (E.degree : ℕ) := ⟨E.degree.pos.ne'⟩
  letI : Finite (FiniteNormQuotient A K.field L hLK) :=
    Finite.of_equiv (ZMod (E.degree : ℕ)) e.symm
  have hsurj : Function.Surjective f := by
    rw [← AddMonoidHom.range_eq_top]
    apply top_unique
    rw [← v.primeClass_zmultiples_eq_top hAxiom K L hLK
      hUnramified (v.chosenPrimeElement K) (v.chosenPrimeElement_isPrime K)]
    rw [AddSubgroup.zmultiples_le]
    exact ⟨Additive.ofMul (D.unramifiedFrobenius
      (K.toFiniteResidueAbstractField D) L hLK), hf⟩
  apply (Nat.bijective_iff_surjective_and_card f).2
  refine ⟨hsurj, ?_⟩
  calc
    Nat.card (Additive
        (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)) =
        Nat.card
          (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup) :=
      Nat.card_congr Additive.toMul
    _ = (L.toSubgroup.subgroupOf K.field.toSubgroup).index :=
      (Subgroup.index_eq_card _).symm
    _ = (E.degree : ℕ) := by
      exact E.toFiniteAbstractExtension.subgroup_index_eq_degree
    _ = Nat.card (ZMod (E.degree : ℕ)) :=
      (Nat.card_zmod _).symm
    _ = Nat.card (FiniteNormQuotient A K.field L hLK) :=
      (Nat.card_congr e.toEquiv).symm

/-- **The additive-equivalence form of the generator criterion**: a
homomorphism with the required Frobenius value is canonically promoted
to an equivalence, independently of the particular construction
([Yamaguchi 2026, `MainFiniteReciprocity.lean:1054`][Yamaguchi2026]). -/
noncomputable def unramifiedReciprocity_equiv_of_generator
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hUnramified :
      (AbstractExtension.mk L K.field hLK).IsUnramified D)
    (f : Additive
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup) →+
      FiniteNormQuotient A K.field L hLK)
    (hf : f (Additive.ofMul (D.unramifiedFrobenius
        (K.toFiniteResidueAbstractField D) L hLK)) =
      finiteNormClass A K.field L hLK (v.chosenPrimeElement K)) :
    Additive (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup) ≃+
      FiniteNormQuotient A K.field L hLK :=
  AddEquiv.ofBijective f
    (v.unramifiedReciprocity_bijective_of_generator hAxiom
      K L hLK hUnramified f hf)

/-- **The generator-dependent equivalence evaluates as its homomorphism**
([Yamaguchi 2026, `MainFiniteReciprocity.lean:1078`][Yamaguchi2026]). -/
@[simp]
theorem unramifiedReciprocity_equiv_of_generator_apply
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hUnramified :
      (AbstractExtension.mk L K.field hLK).IsUnramified D)
    (f : Additive
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup) →+
      FiniteNormQuotient A K.field L hLK)
    (hf : f (Additive.ofMul (D.unramifiedFrobenius
        (K.toFiniteResidueAbstractField D) L hLK)) =
      finiteNormClass A K.field L hLK (v.chosenPrimeElement K))
    (q : Additive
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)) :
    v.unramifiedReciprocity_equiv_of_generator hAxiom K L hLK
      hUnramified f hf q = f q :=
  rfl

/-- **The finite reciprocity homomorphism sends arithmetic Frobenius to
the class of a prime element when `L | K` is unramified** — the
generator calculation
([Yamaguchi 2026, `MainFiniteReciprocity.lean:1101`][Yamaguchi2026]). -/
theorem unramifiedReciprocity_frobenius_image
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hUnramified :
      (AbstractExtension.mk L K.field hLK).IsUnramified D) :
    D.finiteReciprocityHom A v hAxiom K L hLK
        (Additive.ofMul (D.unramifiedFrobenius
          (K.toFiniteResidueAbstractField D) L hLK)) =
      finiteNormClass A K.field L hLK (v.chosenPrimeElement K) := by
  let KR := K.toFiniteResidueAbstractField D
  let σ := D.chosenUnramifiedFrobeniusLift KR L hLK
  let S := D.frobeniusFixedField KR L hLK σ
  let hSK := D.frobeniusFixedField_le KR L hLK σ
  letI hSfinite : Finite
      (K.field.toSubgroup ⧸ S.toSubgroup.subgroupOf K.field.toSubgroup) :=
    D.frobeniusFixedField_finite KR L hLK σ
  letI hSabsolute : Finite ((baseField G).toSubgroup ⧸
      S.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ
  let Sigma : FiniteAbstractField G := ⟨S, hSabsolute⟩
  let π : ambientFixedAddSubgroup A S :=
    fixedFieldInclusion A K.field S hSK (v.chosenPrimeElement K)
  have hπ : v.IsPrimeElement Sigma π := by
    simpa [σ, S, hSK, π] using
      v.unramifiedFrobenius_includedPrime_isPrime K L hLK hUnramified
  rw [D.finiteReciprocityHom_apply_eq_primeNormClass
    A v hAxiom K L hLK
      (Additive.ofMul (D.unramifiedFrobenius KR L hLK)) σ
      (by rfl) π hπ]
  rw [show relativeNorm A K.field S hSK π = v.chosenPrimeElement K by
    simpa [σ, S, hSK, π] using
      v.unramifiedFrobenius_primeNorm K L hLK hUnramified]

/-- **The unramified norm-quotient equivalence**: for a finite
unramified Galois extension, the finite reciprocity homomorphism is an
additive equivalence
([Yamaguchi 2026, `MainFiniteReciprocity.lean:1143`][Yamaguchi2026]). -/
noncomputable def unramifiedReciprocityEquiv
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hUnramified :
      (AbstractExtension.mk L K.field hLK).IsUnramified D) :
    Additive (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup) ≃+
      FiniteNormQuotient A K.field L hLK :=
  v.unramifiedReciprocity_equiv_of_generator hAxiom K L hLK hUnramified
    (D.finiteReciprocityHom A v hAxiom K L hLK)
    (v.unramifiedReciprocity_frobenius_image hAxiom
      K L hLK hUnramified)

/-- **The equivalence evaluates as the reciprocity homomorphism**
([Yamaguchi 2026, `MainFiniteReciprocity.lean:1162`][Yamaguchi2026]). -/
@[simp]
theorem unramifiedReciprocityEquiv_apply
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hUnramified :
      (AbstractExtension.mk L K.field hLK).IsUnramified D)
    (q : Additive
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)) :
    v.unramifiedReciprocityEquiv hAxiom K L hLK hUnramified q =
      D.finiteReciprocityHom A v hAxiom K L hLK q :=
  rfl

end ValuationData

end

end Atlas.Knowledge
