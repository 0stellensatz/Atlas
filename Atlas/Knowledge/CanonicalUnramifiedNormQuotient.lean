import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteAbstractFieldExtension
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FiniteUnramifiedCyclicExtension
import Atlas.Knowledge.NormalizedValuationLaws
import Atlas.Knowledge.PrimeElement
import Atlas.Knowledge.ProfiniteInteger
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.UnitCohomologyAxiom
import Atlas.Knowledge.UnramifiedQuotientGenerator
import Atlas.Knowledge.ValuationData

/-!
# Canonical unramified norm quotient

The canonical form of the unramified norm-quotient equivalence: the
reduction inherited from `Z ⊆ ℤ̂` — not an arbitrary isomorphism with
`ℤ/nℤ` — induces the identification of `A_K / N_{L/K} A_L` with
`ℤ/[L:K]ℤ`, with the same unit argument supplying injectivity (#104).

## Main statements

* `ValuationData.canonicalUnramifiedNormQuotientValuation_injective` —
  the canonical valuation separates norm classes; proved.

## Main definitions

* `ValuationData.canonicalUnramifiedNormQuotientEquiv` — the canonical
  valuation isomorphism.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
`ZHat` is `ProfiniteInteger` with `zHatReduction` the layer's
`ProfiniteInteger.reduction` under `NeZero`, positivity projections read
`.pos` for the source's `.property`, and the small canonical
apparatus runs on `NeZero` instances instead of the source's positivity
arguments throughout. The injectivity proof draws the norm preimage
directly from the elementwise unit-cohomology axiom's first component
(#135) where the source derived Tate vanishing and fed a never-ported
eliminator, and two `let`s re-anchor the preimage's summands over the
top field — both as in the sibling `UnramifiedNormQuotient` item. The
source's universe-device import is dropped, the ambient group is
`Type`, two `dsimp only`s with nothing left to unfold go, and the
coset evaluation rule states its left side with the coercion, as the
unit representation's rule does, for the simp-normal-form linter.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

/-- Reduction modulo `n` restricted to the actual value subgroup
`Z ⊆ ℤ̂` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CanonicalUnramifiedNormQuotient.lean:30`]
[Yamaguchi2026]). -/
def canonicalValueReduction
    (v : ValuationData D A) (n : ℕ) [NeZero n] :
    v.valueGroup →+ ZMod n :=
  v.valueModulo n

/-- The canonical value reduction sends the one-value to one ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CanonicalUnramifiedNormQuotient.lean:37`]
[Yamaguchi2026]). -/
@[simp]
theorem canonicalValueReduction_one
    (v : ValuationData D A) (n : ℕ) [NeZero n] :
    v.canonicalValueReduction n v.oneValue = 1 := by
  change ProfiniteInteger.reduction n (1 : ProfiniteInteger) = 1
  rfl

/-- The canonical value reduction is surjective ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CanonicalUnramifiedNormQuotient.lean:44`]
[Yamaguchi2026]). -/
theorem canonicalValueReduction_surjective
    (v : ValuationData D A) (n : ℕ) [NeZero n] :
    Function.Surjective (v.canonicalValueReduction n) :=
  v.valueModulo_surjective n

/-- Canonical reduction descended to `Z/nZ` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CanonicalUnramifiedNormQuotient.lean:50`]
[Yamaguchi2026]). -/
def canonicalValueQuotientHom
    (v : ValuationData D A) (n : ℕ) [NeZero n] :
    (v.valueGroup ⧸ nsmulWithin v.valueGroup n) →+ ZMod n :=
  v.canonicalQuotientMap n

/-- The quotient homomorphism evaluates on a coset through canonical
value reduction. -/
@[simp]
theorem canonicalValueQuotientHom_mk
    (v : ValuationData D A) (n : ℕ) [NeZero n]
    (z : v.valueGroup) :
    v.canonicalValueQuotientHom n
      (z : v.valueGroup ⧸ nsmulWithin v.valueGroup n) =
        v.canonicalValueReduction n z := by
  rfl

/-- The induced canonical value map on the quotient is surjective ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CanonicalUnramifiedNormQuotient.lean:66`]
[Yamaguchi2026]). -/
theorem canonicalValueQuotientHom_surjective
    (v : ValuationData D A) (n : ℕ) [NeZero n] :
    Function.Surjective (v.canonicalValueQuotientHom n) :=
  (v.canonical_value_quotient_bijective n).2

/-- The canonical isomorphism `Z/nZ ≃ ℤ/nℤ` from the valuation-quotient
axiom ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CanonicalUnramifiedNormQuotient.lean:72`]
[Yamaguchi2026]). -/
def canonicalValueQuotientEquiv
    (v : ValuationData D A) (n : ℕ) [NeZero n] :
    (v.valueGroup ⧸ nsmulWithin v.valueGroup n) ≃+ ZMod n :=
  v.cyclic_value_quotients n

/-- Canonical valuation modulo `[L : K]` on `A_K` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CanonicalUnramifiedNormQuotient.lean:78`]
[Yamaguchi2026]). -/
def canonicalUnramifiedValuationHom
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G) :
    ambientFixedAddSubgroup A E.base.field →+ ZMod (E.degree : ℕ) :=
  letI : NeZero (E.degree : ℕ) := ⟨E.degree.pos.ne'⟩
  (v.canonicalValueReduction (E.degree : ℕ)).comp
    (v.valuationAt E.base)

/- Norms die under the canonical valuation ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CanonicalUnramifiedNormQuotient.lean:84`]
[Yamaguchi2026]). -/
private theorem finiteNormSubgroup_le_canonicalUnramifiedValuationHom_ker
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hUnramified : E.IsUnramified D) :
    finiteNormSubgroup A E.base.field E.field.field E.below ≤
      (v.canonicalUnramifiedValuationHom E).ker := by
  rintro _ ⟨a, rfl⟩
  let n := (E.degree : ℕ)
  letI : NeZero n := ⟨E.degree.pos.ne'⟩
  have htower := v.normalizedValuation_tower E a
  have hresidueDegree :
      ((E.toFiniteResidueAbstractExtension D).residueDegree : ℕ) =
        (E.degree : ℕ) := by
    exact E.residueDegree_eq_degree_of_isUnramified D hUnramified
  rw [hresidueDegree] at htower
  have htower' :
      n • ((v.valuationAt E.field a : v.valueGroup) : ProfiniteInteger) =
        ((v.valuationAt E.base
          (relativeNorm A E.base.field E.field.field E.below a) :
          v.valueGroup) : ProfiniteInteger) := by
    simpa [n] using htower
  change ProfiniteInteger.reduction n
      (v.valuationAt E.base
        (relativeNorm A E.base.field E.field.field E.below a) : ProfiniteInteger) = 0
  rw [← htower', map_nsmul]
  simp [n]

/-- The canonical valuation induced on the finite unramified norm
quotient ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CanonicalUnramifiedNormQuotient.lean:113`]
[Yamaguchi2026]). -/
def canonicalUnramifiedNormQuotientValuation
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hUnramified : E.IsUnramified D) :
    FiniteNormQuotient A E.base.field E.field.field E.below →+
      ZMod (E.degree : ℕ) :=
  finiteNormQuotientLift A E.base.field E.field.field E.below
    (v.canonicalUnramifiedValuationHom E)
    (v.finiteNormSubgroup_le_canonicalUnramifiedValuationHom_ker
      E hUnramified)

/-- Valuation sends a finite norm class to its canonical unramified
quotient value. -/
@[simp]
theorem canonicalUnramifiedNormQuotientValuation_finiteNormClass
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hUnramified : E.IsUnramified D)
    (a : ambientFixedAddSubgroup A E.base.field) :
    v.canonicalUnramifiedNormQuotientValuation E hUnramified
      (finiteNormClass A E.base.field E.field.field E.below a) =
        v.canonicalUnramifiedValuationHom E a := by
  rfl

/-- The valuation map from the unramified norm quotient is surjective ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CanonicalUnramifiedNormQuotient.lean:135`]
[Yamaguchi2026]). -/
theorem canonicalUnramifiedNormQuotientValuation_surjective
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hUnramified : E.IsUnramified D) :
    Function.Surjective
      (v.canonicalUnramifiedNormQuotientValuation E hUnramified) := by
  intro z
  let n := (E.degree : ℕ)
  letI : NeZero n := ⟨E.degree.pos.ne'⟩
  obtain ⟨w, hw⟩ := v.canonicalValueReduction_surjective n z
  obtain ⟨a, ha⟩ := v.normalizedValuation_surjective E.base w
  refine ⟨finiteNormClass A E.base.field E.field.field E.below a, ?_⟩
  rw [v.canonicalUnramifiedNormQuotientValuation_finiteNormClass]
  change v.canonicalValueReduction n (v.valuationAt E.base a) = z
  rw [ha]
  exact hw

/-- **The valuation map separates classes in the unramified norm
quotient** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CanonicalUnramifiedNormQuotient.lean:152`]
[Yamaguchi2026]). -/
theorem canonicalUnramifiedNormQuotientValuation_injective
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (E.field.field.toSubgroup.subgroupOf
      E.base.field.toSubgroup).Normal)
    (hUnramified : E.IsUnramified D) :
    Function.Injective
      (v.canonicalUnramifiedNormQuotientValuation E hUnramified) := by
  letI := hnormal
  let n := (E.degree : ℕ)
  letI : NeZero n := ⟨E.degree.pos.ne'⟩
  have hkernel : ∀ q : FiniteNormQuotient A E.base.field
      E.field.field E.below,
      v.canonicalUnramifiedNormQuotientValuation E hUnramified q = 0 →
        q = 0 := by
    intro q
    refine FiniteNormQuotient.induction_on A E.base.field E.field.field
      E.below q ?_
    intro a ha
    change v.canonicalValueReduction n (v.valuationAt E.base a) = 0 at ha
    have hqValue :
        (QuotientAddGroup.mk' (nsmulWithin v.valueGroup n)
          (v.valuationAt E.base a)) = 0 := by
      apply (v.canonicalValueQuotientEquiv n).injective
      change v.canonicalValueQuotientHom n
          (QuotientAddGroup.mk' (nsmulWithin v.valueGroup n)
            (v.valuationAt E.base a)) =
        v.canonicalValueQuotientHom n 0
      rw [QuotientAddGroup.mk'_apply, v.canonicalValueQuotientHom_mk,
        ha, map_zero]
    obtain ⟨z, haz⟩ :=
      (QuotientAddGroup.eq_zero_iff (v.valuationAt E.base a)).1 hqValue
    have haz' : v.valuationAt E.base a = n • z := haz.symm
    obtain ⟨b, hb⟩ := v.normalizedValuation_surjective E.field z
    let normb : ambientFixedAddSubgroup A E.base.field :=
      relativeNorm A E.base.field E.field.field E.below b
    have htower := v.normalizedValuation_tower E b
    have hresidueDegree :
        ((E.toFiniteResidueAbstractExtension D).residueDegree : ℕ) =
          (E.degree : ℕ) := by
      exact E.residueDegree_eq_degree_of_isUnramified D hUnramified
    rw [hresidueDegree] at htower
    have hnormb : v.valuationAt E.base normb = n • z := by
      apply Subtype.ext
      calc
        ((v.valuationAt E.base normb : v.valueGroup) : ProfiniteInteger) =
            n • ((v.valuationAt E.field b : v.valueGroup) : ProfiniteInteger) := htower.symm
        _ = n • ((z : v.valueGroup) : ProfiniteInteger) := by rw [hb]
        _ = (((n • z : v.valueGroup)) : ProfiniteInteger) := rfl
    let u : v.unitAddSubgroup E.base :=
      ⟨a - normb, by
        rw [v.mem_unitAddSubgroup_iff, map_sub, haz', hnormb, sub_self]⟩
    let KR := E.base.toFiniteResidueAbstractField D
    letI hnormalKR :
        (E.field.field.toSubgroup.subgroupOf KR.field.toSubgroup).Normal := by
      change (E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal
      exact hnormal
    letI hfiniteKR : Finite
        (KR.field.toSubgroup ⧸
          E.field.field.toSubgroup.subgroupOf KR.field.toSubgroup) := by
      change Finite (E.base.field.toSubgroup ⧸
        E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup)
      exact E.finiteQuotient
    obtain ⟨g, hg⟩ :=
      D.exists_quotient_generator_of_unramified
        KR E.field.field E.below hUnramified
    letI : Fintype (E.base.field.toSubgroup ⧸
        E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup) :=
      Fintype.ofFinite _
    let Euc : FiniteUnramifiedCyclicExtension D E.base :=
      { field := E.field.field
        below := E.below
        normal := hnormal
        finite := E.finiteQuotient
        generator := g
        generates := hg
        unramified := by
          change E.IsUnramified D
          exact hUnramified }
    obtain ⟨ε, hε⟩ := (hAxiom E.base Euc).1 u
    change v.unitAddSubgroup E.field at ε
    change relativeNorm A E.base.field E.field.field E.below ε.1 = u.1 at hε
    apply (finiteNormClass_eq_zero_iff A E.base.field E.field.field
      E.below a).2
    let bL : ambientFixedAddSubgroup A E.field.field := b
    let εL : ambientFixedAddSubgroup A E.field.field := ε.1
    have hεL :
        relativeNorm A E.base.field E.field.field E.below εL = u.1 := hε
    refine ⟨bL + εL, ?_⟩
    rw [map_add, hεL]
    change normb + (a - normb) = a
    abel
  intro x y hxy
  apply sub_eq_zero.mp
  apply hkernel
  rw [map_sub, hxy, sub_self]

/-- **Canonical form of the valuation isomorphism in the unramified
norm-quotient equivalence** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CanonicalUnramifiedNormQuotient.lean:256`]
[Yamaguchi2026]). -/
def canonicalUnramifiedNormQuotientEquiv
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (E.field.field.toSubgroup.subgroupOf
      E.base.field.toSubgroup).Normal)
    (hUnramified : E.IsUnramified D) :
    FiniteNormQuotient A E.base.field E.field.field E.below ≃+
      ZMod (E.degree : ℕ) :=
  AddEquiv.ofBijective
    (v.canonicalUnramifiedNormQuotientValuation E hUnramified)
    ⟨v.canonicalUnramifiedNormQuotientValuation_injective
      hAxiom E hnormal hUnramified,
     v.canonicalUnramifiedNormQuotientValuation_surjective
      E hUnramified⟩

end ValuationData

end

end Atlas.Knowledge
