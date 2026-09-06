import Mathlib
import Atlas.Knowledge.AbstractExtension
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteAbstractFieldExtension
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FiniteUnramifiedCyclicExtension
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusExponent
import Atlas.Knowledge.NormalizedDegree
import Atlas.Knowledge.NormalizedValuationLaws
import Atlas.Knowledge.PrimeElement
import Atlas.Knowledge.ProfiniteInteger
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.UnitCohomologyAxiom
import Atlas.Knowledge.UnramifiedQuotientGenerator
import Atlas.Knowledge.ValuationData

/-!
# Unramified norm quotient

For a finite unramified Galois extension `L / K`, the normalized
valuation identifies the norm quotient `A_K / N_{L/K} A_L` with
`ℤ/[L:K]ℤ`: the chosen degree-one lift restricts to the arithmetic
Frobenius generating the Galois quotient, the reduced valuation kills
norms and is surjective, and the unit-cohomology axiom supplies
injectivity — with the prime class of exact order `[L:K]` generating the
quotient (#104).

## Main definitions

* `DegreeData.unramifiedFrobenius` — the arithmetic Frobenius.
* `ValuationData.unramifiedReciprocity_valuationEquiv` — the equivalence
  `A_K / N_{L/K} A_L ≃ ℤ/[L:K]ℤ`.

## Main statements

* `DegreeData.unramifiedFrobenius_generates` — the arithmetic Frobenius
  generates the Galois quotient; proved.
* `ValuationData.unramifiedNormQuotientValuation_injective` — the unit
  argument; proved.
* `ValuationData.primeClass_addOrderOf` — the prime class has exact
  order `[L:K]`; proved.
* `ValuationData.primeClass_zmultiples_eq_top` — the prime class
  generates; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
`ZHat` is `ProfiniteInteger` with `zHatReduction n hn` the layer's
`ProfiniteInteger.reduction n` under `NeZero`,
`proCIntegerOne_pow_nat_injective` is
`ProfiniteInteger.ofAdd_one_pow_injective`, positivity projections read
`.pos` for the source's `.property`, and the whole `valueModulo`
apparatus likewise runs on `NeZero` instances rather than the source's
positivity arguments — each big proof registers the degree's instance
once. `AbstractExtension` sits at the layer's top level, and the
injectivity proof draws the norm preimage directly from the elementwise
unit-cohomology axiom's first component (#135), where the source derived
Tate vanishing and fed a never-ported eliminator — the `Euc` bundle
literal is the source's own, and two `let`s re-anchor the norm
preimage's summands over `L` — the axiom types them through the
enrichment bundle, definitionally the same field, but `map_add` matches
syntactically. Both halves sit at the source's `Type u`, the valuation
half since the #104 hoist unpinned the chain it draws on.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

section unramifiedFrobenius

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The degree-one lift `φ_K` used in the unramified norm-quotient
equivalence (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean:31`). -/
def chosenUnramifiedFrobeniusLift
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    D.FrobeniusElements K L hLK := by
  let φ : K.field.toSubgroup := Classical.choose
    (D.normalizedDegree_surjective K
      (Multiplicative.ofAdd (1 : ProfiniteInteger)))
  have hφ : D.normalizedDegree K φ =
      Multiplicative.ofAdd (1 : ProfiniteInteger) :=
    Classical.choose_spec
      (D.normalizedDegree_surjective K
        (Multiplicative.ofAdd (1 : ProfiniteInteger)))
  refine ⟨QuotientGroup.mk φ, 1, Nat.zero_lt_one, ?_⟩
  rw [D.extensionNormalizedDegree_mk K L hLK φ, hφ, pow_one]

/-- The chosen lift has Frobenius exponent one (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean:53`). -/
@[simp]
theorem chosenUnramifiedFrobeniusLift_exponent
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    D.frobeniusExponent K L hLK
      (D.chosenUnramifiedFrobeniusLift K L hLK) = 1 := by
  apply ProfiniteInteger.ofAdd_one_pow_injective
  calc
    (Multiplicative.ofAdd (1 : ProfiniteInteger)) ^
        D.frobeniusExponent K L hLK
          (D.chosenUnramifiedFrobeniusLift K L hLK) =
      D.extensionNormalizedDegree K L hLK
        (D.chosenUnramifiedFrobeniusLift K L hLK).1 :=
      (D.extensionNormalizedDegree_frobenius_eq_pow K L hLK
        (D.chosenUnramifiedFrobeniusLift K L hLK)).symm
    _ = Multiplicative.ofAdd (1 : ProfiniteInteger) := by
      change D.normalizedDegree K
          (Classical.choose
            (D.normalizedDegree_surjective K
              (Multiplicative.ofAdd (1 : ProfiniteInteger)))) = _
      exact Classical.choose_spec
        (D.normalizedDegree_surjective K
          (Multiplicative.ofAdd (1 : ProfiniteInteger)))
    _ = (Multiplicative.ofAdd (1 : ProfiniteInteger)) ^ 1 := (pow_one _).symm

/-- **The arithmetic Frobenius `φ_{L/K}`, obtained by restricting `φ_K`**
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean:80`). -/
def unramifiedFrobenius
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup :=
  D.frobeniusRestriction K L hLK
    (D.chosenUnramifiedFrobeniusLift K L hLK)

/-- **In an unramified extension, arithmetic Frobenius generates the finite
Galois quotient** (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean:91`). -/
theorem unramifiedFrobenius_generates
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hUnramified :
      (AbstractExtension.mk L K.field hLK).IsUnramified D) :
    ∀ x : K.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf K.field.toSubgroup,
      x ∈ Subgroup.zpowers (D.unramifiedFrobenius K L hLK) := by
  let φ : K.field.toSubgroup := Classical.choose
    (D.normalizedDegree_surjective K
      (Multiplicative.ofAdd (1 : ProfiniteInteger)))
  have hφ : D.normalizedDegree K φ =
      Multiplicative.ofAdd (1 : ProfiniteInteger) :=
    Classical.choose_spec
      (D.normalizedDegree_surjective K
        (Multiplicative.ofAdd (1 : ProfiniteInteger)))
  simpa only [unramifiedFrobenius, chosenUnramifiedFrobeniusLift, φ,
    frobeniusRestriction, extensionRestriction_mk] using
    D.quotient_generator_of_unramified_degree_one
      K L hLK hUnramified φ hφ

/-- Additive form of the generator statement, matching the domain of the
reciprocity homomorphism in the finite reciprocity equivalence
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean:116`). -/
theorem unramifiedFrobenius_zmultiples_eq_top
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hUnramified :
      (AbstractExtension.mk L K.field hLK).IsUnramified D) :
    AddSubgroup.zmultiples
      (Additive.ofMul (D.unramifiedFrobenius K L hLK)) = ⊤ := by
  ext x
  constructor
  · intro _
    exact AddSubgroup.mem_top x
  · intro _
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
      (D.unramifiedFrobenius_generates K L hLK hUnramified x.toMul)
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨m, ?_⟩
    change Additive.ofMul
      ((D.unramifiedFrobenius K L hLK) ^ m) = x
    exact congrArg Additive.ofMul hm

end DegreeData

end unramifiedFrobenius

section valuationQuotient

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

/- Zero modulo `n` means an `n`-fold value (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean:151`). -/
private theorem valueModulo_eq_zero_iff
    (v : ValuationData D A) (n : ℕ) [NeZero n]
    (z : v.valueGroup) :
    v.valueModulo n z = 0 ↔ ∃ w : v.valueGroup, z = n • w := by
  constructor
  · intro hz
    have hq :
        (QuotientAddGroup.mk' (nsmulWithin v.valueGroup n)) z = 0 := by
      apply (v.cyclic_value_quotients n).injective
      change v.valueModulo n z = v.valueModulo n 0
      rw [hz, map_zero]
    obtain ⟨w, hw⟩ :=
      (QuotientAddGroup.eq_zero_iff z).1 hq
    exact ⟨w, hw.symm⟩
  · rintro ⟨w, rfl⟩
    have hq :
        (QuotientAddGroup.mk' (nsmulWithin v.valueGroup n)) (n • w) = 0 := by
      apply (QuotientAddGroup.eq_zero_iff _).2
      exact ⟨w, rfl⟩
    change (v.cyclic_value_quotients n)
        ((QuotientAddGroup.mk' (nsmulWithin v.valueGroup n)) (n • w)) = 0
    rw [hq, map_zero]

/- The valuation reduced modulo the degree (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean:174`). -/
private def unramifiedValuationHom
    (v : ValuationData D A) (K : FiniteAbstractField G)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)] :
    ambientFixedAddSubgroup A K.field →+
      ZMod ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ) :=
  letI : NeZero
      ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ) :=
    ⟨(FiniteAbstractFieldExtension.ofInclusion L K hLK).degree.pos.ne'⟩
  (v.valueModulo
      ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ)).comp
    (v.valuationAt K)

/- Norms die modulo the degree — the norm–valuation tower read through
unramifiedness (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean:186`). -/
private theorem finiteNormSubgroup_le_unramifiedValuationHom_ker
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hUnramified :
      (AbstractExtension.mk L K.field hLK).IsUnramified D) :
    finiteNormSubgroup A K.field L hLK ≤
      (v.unramifiedValuationHom K L hLK).ker := by
  rintro _ ⟨a, rfl⟩
  let E := FiniteAbstractFieldExtension.ofInclusion L K hLK
  let n := (E.degree : ℕ)
  letI : NeZero n := ⟨E.degree.pos.ne'⟩
  have hUn : E.IsUnramified D := by
    change (AbstractExtension.mk L K.field hLK).IsUnramified D
    exact hUnramified
  have htower := v.normalizedValuation_tower E a
  change (E.residueDegree D : ℕ) • _ = _ at htower
  rw [E.residueDegree_eq_degree_of_isUnramified D hUn] at htower
  have hval : v.valuationAt K (relativeNorm A K.field L hLK a) =
      n • v.valuationAt E.field a := by
    apply Subtype.ext
    exact htower.symm
  change v.valueModulo n
      (v.valuationAt K (relativeNorm A K.field L hLK a)) = 0
  rw [hval]
  exact (v.valueModulo_eq_zero_iff n _).2
    ⟨v.valuationAt E.field a, rfl⟩

/-- The valuation map induced on the finite norm quotient
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean:215`). -/
def unramifiedNormQuotientValuation
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hUnramified :
      (AbstractExtension.mk L K.field hLK).IsUnramified D) :
    FiniteNormQuotient A K.field L hLK →+
      ZMod ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ) :=
  finiteNormQuotientLift A K.field L hLK
    (v.unramifiedValuationHom K L hLK)
    (v.finiteNormSubgroup_le_unramifiedValuationHom_ker K L hLK hUnramified)

/-- The induced valuation computes on classes. -/
@[simp]
theorem unramifiedNormQuotientValuation_finiteNormClass
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hUnramified :
      (AbstractExtension.mk L K.field hLK).IsUnramified D)
    (a : ambientFixedAddSubgroup A K.field) :
    v.unramifiedNormQuotientValuation K L hLK hUnramified
        (finiteNormClass A K.field L hLK a) =
      v.unramifiedValuationHom K L hLK a :=
  rfl

/-- The induced valuation is surjective (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean:250`). -/
theorem unramifiedNormQuotientValuation_surjective
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hUnramified :
      (AbstractExtension.mk L K.field hLK).IsUnramified D) :
    Function.Surjective
      (v.unramifiedNormQuotientValuation K L hLK hUnramified) := by
  intro z
  let E := FiniteAbstractFieldExtension.ofInclusion L K hLK
  let n := (E.degree : ℕ)
  letI : NeZero n := ⟨E.degree.pos.ne'⟩
  obtain ⟨c, hc⟩ :=
    v.valueModulo_surjective n z
  obtain ⟨a, ha⟩ := v.normalizedValuation_surjective K c
  refine ⟨finiteNormClass A K.field L hLK a, ?_⟩
  rw [v.unramifiedNormQuotientValuation_finiteNormClass]
  change v.valueModulo n
      (v.valuationAt K a) = z
  rw [ha]
  exact hc

/-- **The unit argument**: modulo valuation, the unit-cohomology axiom
makes the remaining unit an actual norm (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean:274`). -/
theorem unramifiedNormQuotientValuation_injective
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hUnramified :
      (AbstractExtension.mk L K.field hLK).IsUnramified D) :
    Function.Injective
      (v.unramifiedNormQuotientValuation K L hLK hUnramified) := by
  let E := FiniteAbstractFieldExtension.ofInclusion L K hLK
  let n := (E.degree : ℕ)
  letI : NeZero n := ⟨E.degree.pos.ne'⟩
  have hUn : E.IsUnramified D := by
    change (AbstractExtension.mk L K.field hLK).IsUnramified D
    exact hUnramified
  have hkernel : ∀ q : FiniteNormQuotient A K.field L hLK,
      v.unramifiedNormQuotientValuation K L hLK hUnramified q = 0 → q = 0 := by
    intro q
    refine FiniteNormQuotient.induction_on A K.field L hLK q ?_
    intro a ha
    change v.unramifiedValuationHom K L hLK a = 0 at ha
    change v.valueModulo n
        (v.valuationAt K a) = 0 at ha
    obtain ⟨z, haz⟩ :=
      (v.valueModulo_eq_zero_iff n
        (v.valuationAt K a)).1 ha
    obtain ⟨b, hb⟩ := v.normalizedValuation_surjective E.field z
    let normb : ambientFixedAddSubgroup A K.field :=
      relativeNorm A K.field L hLK b
    have htower := v.normalizedValuation_tower E b
    change (E.residueDegree D : ℕ) • _ = _ at htower
    rw [E.residueDegree_eq_degree_of_isUnramified D hUn] at htower
    have hnormb : v.valuationAt K normb = n • z := by
      apply Subtype.ext
      calc
        ((v.valuationAt K normb : v.valueGroup) : ProfiniteInteger) =
            n • ((v.valuationAt E.field b : v.valueGroup) : ProfiniteInteger) := htower.symm
        _ = n • ((z : v.valueGroup) : ProfiniteInteger) := by rw [hb]
        _ = (((n • z : v.valueGroup)) : ProfiniteInteger) := rfl
    let u : v.unitAddSubgroup K :=
      ⟨a - normb, by
        rw [v.mem_unitAddSubgroup_iff, map_sub, haz, hnormb, sub_self]⟩
    let KR := K.toFiniteResidueAbstractField D
    letI : (L.toSubgroup.subgroupOf KR.field.toSubgroup).Normal := by
      change (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal
      exact hnormal
    letI : Finite
        (KR.field.toSubgroup ⧸ L.toSubgroup.subgroupOf KR.field.toSubgroup) := by
      change Finite
        (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)
      exact hfinite
    obtain ⟨g, hg⟩ :=
      D.exists_quotient_generator_of_unramified
        KR L hLK hUnramified
    let Euc : FiniteUnramifiedCyclicExtension D K :=
      { field := L
        below := hLK
        normal := hnormal
        finite := hfinite
        generator := g
        generates := hg
        unramified := hUnramified }
    obtain ⟨ε, hε⟩ := (hAxiom K Euc).1 u
    change v.unitAddSubgroup E.field at ε
    change relativeNorm A K.field L hLK ε.1 = u.1 at hε
    apply (finiteNormClass_eq_zero_iff A K.field L hLK a).2
    let bL : ambientFixedAddSubgroup A L := b
    let εL : ambientFixedAddSubgroup A L := ε.1
    have hεL : relativeNorm A K.field L hLK εL = u.1 := hε
    refine ⟨bL + εL, ?_⟩
    rw [map_add, hεL]
    change normb + (a - normb) = a
    abel
  intro x y hxy
  apply sub_eq_zero.mp
  apply hkernel
  rw [map_sub, hxy, sub_self]

/-- **The unramified norm-quotient equivalence**: for finite unramified
`L / K`, valuation induces `A_K / N_{L/K} A_L ≃ ℤ/[L:K]ℤ`
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean:365`). -/
def unramifiedReciprocity_valuationEquiv
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hUnramified :
      (AbstractExtension.mk L K.field hLK).IsUnramified D) :
    FiniteNormQuotient A K.field L hLK ≃+
      ZMod ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ) :=
  AddEquiv.ofBijective
    (v.unramifiedNormQuotientValuation K L hLK hUnramified)
    ⟨v.unramifiedNormQuotientValuation_injective hAxiom K L hLK
        hUnramified,
      v.unramifiedNormQuotientValuation_surjective K L hLK hUnramified⟩

/-- **A prime class has exact additive order `[L : K]` in an unramified
norm quotient**: the lower bound is read after reduction in `ℤ̂/nℤ̂`, the
upper bound is the norm of the included prime (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean:384`). -/
theorem primeClass_addOrderOf
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hUnramified :
      (AbstractExtension.mk L K.field hLK).IsUnramified D)
    (π : ambientFixedAddSubgroup A K.field) (hπ : v.IsPrimeElement K π) :
    addOrderOf
      (finiteNormClass A K.field L hLK π) =
      ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ) := by
  let E := FiniteAbstractFieldExtension.ofInclusion L K hLK
  let n := (E.degree : ℕ)
  letI : NeZero n := ⟨E.degree.pos.ne'⟩
  have hUn : E.IsUnramified D := by
    change (AbstractExtension.mk L K.field hLK).IsUnramified D
    exact hUnramified
  let g : FiniteNormQuotient A K.field L hLK :=
    finiteNormClass A K.field L hLK π
  have hng : n • g = 0 := by
    change n • finiteNormClass A K.field L hLK π = 0
    rw [← finiteNormClass_nsmul]
    apply (finiteNormClass_eq_zero_iff A K.field L hLK _).2
    refine ⟨fixedFieldInclusion A K.field L hLK π, ?_⟩
    have hnorm :=
      relativeNorm_fixedFieldInclusion A E.toFiniteAbstractExtension π
    change relativeNorm A K.field L hLK
        (fixedFieldInclusion A K.field L hLK π) = n • π at hnorm
    exact hnorm
  have hdiv : ∀ m : ℕ, m • g = 0 → n ∣ m := by
    intro m hm
    have hm' :
        finiteNormClass A K.field L hLK (m • π) = 0 := by
      simpa [g] using hm
    have hmNorm := (finiteNormClass_eq_zero_iff A K.field L hLK _).1 hm'
    obtain ⟨b, hb⟩ := hmNorm
    have htower := v.normalizedValuation_tower E b
    change (E.residueDegree D : ℕ) • _ = _ at htower
    rw [E.residueDegree_eq_degree_of_isUnramified D hUn] at htower
    have hval :
        n • ((v.valuationAt E.field b : v.valueGroup) : ProfiniteInteger) =
          m • (1 : ProfiniteInteger) := by
      calc
        n • ((v.valuationAt E.field b : v.valueGroup) : ProfiniteInteger) =
            ((v.valuationAt K (relativeNorm A K.field L hLK b) :
              v.valueGroup) : ProfiniteInteger) := htower
        _ = ((v.valuationAt K (m • π) : v.valueGroup) : ProfiniteInteger) := by
          rw [hb]
        _ = m • ((v.valuationAt K π : v.valueGroup) : ProfiniteInteger) := by
          exact congrArg Subtype.val (map_nsmul (v.valuationAt K) m π)
        _ = m • (1 : ProfiniteInteger) := by rw [hπ, v.oneValue_coe]
    have hred := congrArg (fun z : ProfiniteInteger => ProfiniteInteger.reduction n z) hval
    have hredOne : ProfiniteInteger.reduction n (1 : ProfiniteInteger) = 1 := rfl
    have hred' :
        n • ProfiniteInteger.reduction n
            ((v.valuationAt E.field b : v.valueGroup) : ProfiniteInteger) =
          m • (1 : ZMod n) := by
      simpa only [map_nsmul, hredOne] using hred
    have hmzero : (m : ZMod n) = 0 := by
      have hmzero' : m • (1 : ZMod n) = 0 := by
        rw [← hred']
        simp [nsmul_eq_mul]
      simpa using hmzero'
    exact (ZMod.natCast_eq_zero_iff m n).1 hmzero
  apply Nat.dvd_antisymm
  · exact (addOrderOf_dvd_iff_nsmul_eq_zero).2 hng
  · exact hdiv (addOrderOf g) (addOrderOf_nsmul_eq_zero g)

/-- **The prime class generates the full unramified norm quotient**
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean:454`). -/
theorem primeClass_zmultiples_eq_top
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hUnramified :
      (AbstractExtension.mk L K.field hLK).IsUnramified D)
    (π : ambientFixedAddSubgroup A K.field) (hπ : v.IsPrimeElement K π) :
    AddSubgroup.zmultiples
      (finiteNormClass A K.field L hLK π) = ⊤ := by
  let e := v.unramifiedReciprocity_valuationEquiv hAxiom K L hLK hUnramified
  let E := FiniteAbstractFieldExtension.ofInclusion L K hLK
  letI : NeZero (E.degree : ℕ) :=
    ⟨E.degree.pos.ne'⟩
  letI : Finite (FiniteNormQuotient A K.field L hLK) :=
    Finite.of_equiv (ZMod (E.degree : ℕ)) (by
      simpa [E] using e.symm.toEquiv)
  apply AddSubgroup.eq_top_of_card_eq
  rw [Nat.card_zmultiples,
    v.primeClass_addOrderOf K L hLK hUnramified π hπ]
  exact ((Nat.card_congr e.toEquiv).trans (Nat.card_zmod _)).symm

end ValuationData

end valuationQuotient

end

end Atlas.Knowledge
