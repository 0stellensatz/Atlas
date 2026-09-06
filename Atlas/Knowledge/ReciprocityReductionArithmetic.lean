import Mathlib
import Atlas.Knowledge.ClassFieldAxiom
import Atlas.Knowledge.FiniteAbstractExtension
import Atlas.Knowledge.FiniteAbstractFieldExtension
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.NormalizedValuationLaws
import Atlas.Knowledge.ProfiniteInteger
import Atlas.Knowledge.ReciprocityExactRows
import Atlas.Knowledge.RelativeNormLaws
import Atlas.Knowledge.TransferNormFrobeniusGeometry
import Atlas.Knowledge.TransferNormNaturality
import Atlas.Knowledge.ValuationData

/-!
# reciprocity reduction arithmetic

The order and valuation arguments behind the three reductions of the
abstract reciprocity proof: the canonical factorization of an additive
reciprocity map through the abelianization, the Sylow-argument identity
`N_{M/K} ∘ i = [M:K]`, the class-field-axiom order calculations that
upgrade surjectivity to bijectivity and make the cyclic-tower norm map
injective, and the totally ramified valuation endpoint that forces the
constructed exponent to vanish (#104).

## Main definitions

* `abstractReciprocityAbelianizationFactor` — the canonical
  factorization of an additive reciprocity map through the
  abelianization.

## Main statements

* `abstractReciprocity_cyclicTower_normMap_injective` — in a cyclic
  tower the first norm map of the lower exact row is injective; proved
  by the order calculation.
* `abstractReciprocity_totallyRamified_valuation_forces_exponent_zero`
  — the `k = 0` valuation endpoint of the totally ramified argument;
  proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
`DegreeData.FiniteAbstractExtension` is the layer's top-level
`FiniteAbstractExtension`, `ZHat` is `ProfiniteInteger` — which renames
`abstractReciprocity_zHat_nsmul_eq_natCast_forces_zero` to
`abstractReciprocity_profiniteInteger_nsmul_eq_natCast_forces_zero` and
turns `zHatReduction n hn` into `ProfiniteInteger.reduction n` under a
`NeZero` instance — `degree.property` is the layer's `degree.pos`, and
the calls to
`transferNormNaturality_intermediateExtension_normal K M L hMK` shed
the source's `hLM` the way the layer's slimmed form asks. One
`noncomputable section` holds everything at `Type u` since the #104
hoist merged its two ambient-group scopes, the way
`Atlas.Knowledge.ReciprocityExactRows` does: seven declarations come
first — the abelianization pair polymorphic in its own two groups and
mentioning no ambient one, the profinite-integer step mentioning no
group and no universe at all, the other four polymorphic in the ambient
group — while the two that consume `abstractReciprocityNormMap`, the
Sylow-argument identity and the cyclic-tower injectivity, keep the
place the former shadowing `variable` line gave them, after the
valuation endpoints relative to the source order. This completes
`Reciprocity/Core.lean`: the two exact rows are the layer's
`Atlas.Knowledge.ReciprocityExactRows`, and the `ValuationData` section
stays deliberately unprovided per the interface decision recorded in
`Atlas.Knowledge.ClassFieldAxiom`.

One proof step departs: the `htower'` bridge in the valuation identity
closes by `exact` where the source unfolds with a `simpa` — the layer's
`FiniteAbstractFieldExtension.degree` is definitionally the underlying
finite extension's degree, so nothing needs unfolding.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **An additive homomorphism from a (possibly noncommutative) Galois
group to an additive commutative group factors canonically through its
abelianization** — the factor map used in the first reduction once the
finite reciprocity equivalence supplies the reciprocity homomorphism
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:890`). -/
def abstractReciprocityAbelianizationFactor
    {Q : Type*} {B : Type*} [Group Q] [AddCommGroup B]
    (f : Additive Q →+ B) : Additive (Abelianization Q) →+ B := by
  let fMul : Q →* Multiplicative B :=
    { toFun := fun q => Multiplicative.ofAdd (f (Additive.ofMul q))
      map_one' := f.map_zero
      map_mul' := f.map_add }
  let fAb : Abelianization Q →* Multiplicative B :=
    Abelianization.lift fMul
  exact
    { toFun := fun q => Multiplicative.toAdd (fAb q.toMul)
      map_zero' := fAb.map_one
      map_add' := fAb.map_mul }

/-- The abelianization factor restricts to the original map on images of
`Abelianization.of` (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:909`). -/
@[simp]
theorem abstractReciprocityAbelianizationFactor_of
    {Q : Type*} {B : Type*} [Group Q] [AddCommGroup B]
    (f : Additive Q →+ B) (q : Q) :
    abstractReciprocityAbelianizationFactor f
        (Additive.ofMul (Abelianization.of q)) =
      f (Additive.ofMul q) := by
  exact Abelianization.lift_apply_of
    ({ toFun := fun q => Multiplicative.ofAdd (f (Additive.ofMul q))
       map_one' := f.map_zero
       map_mul' := f.map_add } : Q →* Multiplicative B) q

/-- Restriction also induces the canonical map on abelianizations
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:921`). -/
def abstractReciprocityAbelianizedRestriction
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    Abelianization
        (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) →*
      Abelianization (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
  Abelianization.map (abstractReciprocityRestriction K M L hLM hMK)

/-- In the cyclic case, the class-field axiom upgrades surjectivity of
the actual reciprocity-shaped homomorphism to bijectivity; the converse
is formal, and the forward implication uses the equality of the two
actual finite orders, not an assumed cardinality certificate
(Yamaguchi 2026, `AbstractClassFieldTheory/Reciprocity/Core.lean:982`). -/
theorem abstractReciprocity_cyclic_surjective_iff_bijective
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hKabsolute : Finite ((baseField G).toSubgroup ⧸
      K.toSubgroup.subgroupOf (baseField G).toSubgroup)]
    [hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (g : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
    (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (r : Additive (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) →+
      FiniteNormQuotient A K L hLK) :
    Function.Surjective r ↔ Function.Bijective r := by
  let E : FiniteAbstractExtension G :=
    FiniteAbstractExtension.ofInclusion L K hLK
  letI hEbaseAbsolute : Finite ((baseField G).toSubgroup ⧸
      E.base.toSubgroup.subgroupOf (baseField G).toSubgroup) := by
    simpa [E, FiniteAbstractExtension.ofInclusion] using hKabsolute
  letI : Finite (FiniteNormQuotient A K L hLK) :=
    finiteNormQuotient_finite_of_classFieldAxiom
      A hcf E hnormal g hg
  constructor
  · intro hr
    apply (Nat.bijective_iff_surjective_and_card r).2
    exact ⟨hr, cyclicReciprocity_card_equality
      A hcf E hnormal g hg⟩
  · exact fun hr => hr.2

/-- An elementary profinite-integer step: if `n z = k` in `ℤ̂`, with
`0 ≤ k < n`, then `k = 0` (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:1153`). -/
theorem abstractReciprocity_profiniteInteger_nsmul_eq_natCast_forces_zero
    (n k : ℕ) (hn : 0 < n) (hk : k < n) (z : ProfiniteInteger)
    (h : n • z =
      Int.castRingHom ProfiniteInteger (k : ℤ)) :
    k = 0 := by
  letI : NeZero n := ⟨hn.ne'⟩
  have hkmod : (k : ZMod n) = 0 := by
    have hkmodInt : ((k : ℤ) : ZMod n) = 0 := by
      calc
        ((k : ℤ) : ZMod n) = ProfiniteInteger.reduction n
          (Int.castRingHom ProfiniteInteger (k : ℤ)) :=
              (ProfiniteInteger.reduction_intCast n (k : ℤ)).symm
        _ =
          ProfiniteInteger.reduction n (n • z) :=
            congrArg (ProfiniteInteger.reduction n) h.symm
        _ = n • ProfiniteInteger.reduction n z :=
          map_nsmul (ProfiniteInteger.reduction n) n z
        _ = 0 := by simp
    simpa using hkmodInt
  exact Nat.eq_zero_of_dvd_of_lt
    ((ZMod.natCast_eq_zero_iff k n).1 hkmod) hk

/-- In a finite totally ramified extension, the normalized valuation of
an element from the lower field is multiplied by the extension degree
after inclusion into the upper field — the valuation identity used for
`M/M⁰` (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:1176`). -/
theorem abstractReciprocity_valuationAt_fixedFieldInclusion_of_totallyRamified
    {D : DegreeData G} {A : Rep ℤ G} (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hTot : E.IsTotallyRamified D)
    (x : ambientFixedAddSubgroup A E.base.field) :
    ((v.valuationAt E.field
      (fixedFieldInclusion A E.base.field E.field.field E.below x) :
      v.valueGroup) : ProfiniteInteger) =
      (E.degree : ℕ) •
        ((v.valuationAt E.base x : v.valueGroup) : ProfiniteInteger) := by
  let EF := E.toFiniteAbstractExtension
  letI hEFfinite : Finite
      (E.base.field.toSubgroup ⧸
        E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup) :=
    EF.finiteQuotient
  have htower := v.normalizedValuation_tower E
    (fixedFieldInclusion A E.base.field E.field.field E.below x)
  have hresidue : (E.residueDegree D : ℕ) = 1 :=
    EF.residueDegree_eq_one_of_isTotallyRamified D hTot
  change (E.residueDegree D : ℕ) •
      ((v.valuationAt E.field
        (fixedFieldInclusion A E.base.field E.field.field E.below x) :
          v.valueGroup) : ProfiniteInteger) =
    ((v.valuationAt E.base
      (relativeNorm A E.base.field E.field.field E.below
        (fixedFieldInclusion A E.base.field E.field.field E.below x)) :
          v.valueGroup) : ProfiniteInteger) at htower
  rw [hresidue, one_nsmul] at htower
  have hbelow : E.below = EF.below := Subsingleton.elim _ _
  rw [hbelow] at htower
  change
    ((v.valuationAt E.field
      (fixedFieldInclusion A EF.base EF.field EF.below x) :
        v.valueGroup) : ProfiniteInteger) =
      ((v.valuationAt E.base
        (relativeNorm A EF.base EF.field EF.below
          (fixedFieldInclusion A EF.base EF.field EF.below x)) :
            v.valueGroup) : ProfiniteInteger) at htower
  rw [relativeNorm_fixedFieldInclusion A EF x] at htower
  have hfixedFieldInclusion :
      fixedFieldInclusion A EF.base EF.field EF.below x =
        fixedFieldInclusion A E.base.field E.field.field E.below x := by
    apply Subtype.ext
    rfl
  rw [hfixedFieldInclusion] at htower
  have htower' :
      ((v.valuationAt E.field
        (fixedFieldInclusion A E.base.field E.field.field E.below x) :
          v.valueGroup) : ProfiniteInteger) =
        ((v.valuationAt E.base ((E.degree : ℕ) • x) :
          v.valueGroup) : ProfiniteInteger) := by
    exact htower
  calc
    ((v.valuationAt E.field
      (fixedFieldInclusion A E.base.field E.field.field E.below x) :
        v.valueGroup) : ProfiniteInteger) =
        ((v.valuationAt E.base ((E.degree : ℕ) • x) :
          v.valueGroup) : ProfiniteInteger) := htower'
    _ = (E.degree : ℕ) •
        ((v.valuationAt E.base x : v.valueGroup) : ProfiniteInteger) :=
      congrArg Subtype.val
        (map_nsmul (v.valuationAt E.base) (E.degree : ℕ) x)

/-- **The exact `k = 0` valuation endpoint of the totally ramified
argument**; here `K = M⁰`, `L = M`, and `x` is the element constructed
in the fixed subgroup (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:1241`). -/
theorem abstractReciprocity_totallyRamified_valuation_forces_exponent_zero
    {D : DegreeData G} {A : Rep ℤ G} (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hTot : E.IsTotallyRamified D)
    (k : ℕ) (hk : k < (E.degree : ℕ))
    (x : ambientFixedAddSubgroup A E.base.field)
    (hx :
      ((v.valuationAt E.field
        (fixedFieldInclusion A E.base.field E.field.field E.below x) :
        v.valueGroup) : ProfiniteInteger) =
        Int.castRingHom ProfiniteInteger (k : ℤ)) :
    k = 0 := by
  have hn : 0 < (E.degree : ℕ) := E.degree.pos
  apply abstractReciprocity_profiniteInteger_nsmul_eq_natCast_forces_zero
    (E.degree : ℕ) k hn hk
    (((v.valuationAt E.base x : v.valueGroup) : ProfiniteInteger))
  rw [← abstractReciprocity_valuationAt_fixedFieldInclusion_of_totallyRamified
    v E hTot]
  exact hx

/-- The identity `N_{M/K} ∘ i = [M:K]` used in the Sylow argument of the
first reduction; here `i` is the actual inclusion of finite norm
quotients constructed in transfer–norm naturality (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:937`). -/
theorem abstractReciprocity_normMap_comp_normQuotientInclusion
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (q : FiniteNormQuotient A K L (hLM.trans hMK)) :
    letI : (L.toSubgroup.subgroupOf M.toSubgroup).Normal :=
      transferNormNaturality_intermediateExtension_normal K M L hMK
    letI : Finite (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    abstractReciprocityNormMap A K M L hLM hMK
        (transferNormNaturalityNormQuotientInclusion A K M L hLM hMK q) =
      ((FiniteAbstractExtension.ofInclusion M K hMK).degree : ℕ) • q := by
  letI : (L.toSubgroup.subgroupOf M.toSubgroup).Normal :=
    transferNormNaturality_intermediateExtension_normal K M L hMK
  letI : Finite (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  letI : Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  refine FiniteNormQuotient.induction_on A K L (hLM.trans hMK) q ?_
  intro a
  rw [transferNormNaturality_normQuotientInclusion_finiteNormClass,
    abstractReciprocityNormMap_finiteNormClass]
  have hnorm :
      relativeNorm A K M hMK
          (fixedFieldInclusion A K M hMK a) =
          ((FiniteAbstractExtension.ofInclusion M K hMK).degree :
            ℕ) • a := by
    let E := FiniteAbstractExtension.ofInclusion M K hMK
    change relativeNorm A E.base E.field E.below
        (fixedFieldInclusion A E.base E.field E.below a) =
      (E.degree : ℕ) • a
    exact relativeNorm_fixedFieldInclusion A E a
  rw [hnorm, finiteNormClass_nsmul]

/-- **In a cyclic tower, the first norm map in the lower exact row is
injective** — the order calculation in the third reduction: the three
norm quotients have orders `[L:M]`, `[L:K]`, and `[M:K]`, and the tower
law cancels the last factor (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Core.lean:1015`). -/
theorem abstractReciprocity_cyclicTower_normMap_injective
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hKabsolute : Finite ((baseField G).toSubgroup ⧸
      K.toSubgroup.subgroupOf (baseField G).toSubgroup)]
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (gKL : K.toSubgroup ⧸
      L.toSubgroup.subgroupOf K.toSubgroup)
    (hgKL : ∀ q, q ∈ Subgroup.zpowers gKL)
    (gML :
      letI : (L.toSubgroup.subgroupOf M.toSubgroup).Normal :=
        transferNormNaturality_intermediateExtension_normal K M L hMK
      M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup)
    (hgML :
      letI : (L.toSubgroup.subgroupOf M.toSubgroup).Normal :=
        transferNormNaturality_intermediateExtension_normal K M L hMK
      ∀ q, q ∈ Subgroup.zpowers gML)
    (gKM : K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup)
    (hgKM : ∀ q, q ∈ Subgroup.zpowers gKM) :
    letI : Finite (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    Function.Injective (abstractReciprocityNormMap A K M L hLM hMK) := by
  letI hMLnormal : (L.toSubgroup.subgroupOf M.toSubgroup).Normal :=
    transferNormNaturality_intermediateExtension_normal K M L hMK
  letI hMLfinite : Finite
      (M.toSubgroup ⧸ L.toSubgroup.subgroupOf M.toSubgroup) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  letI hKMfinite : Finite
      (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  letI hMabsolute : Finite ((baseField G).toSubgroup ⧸
      M.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    relativeTowerQuotientFinite (baseField G) K M hMK (le_baseField K)
  let ELM : FiniteAbstractExtension G :=
    FiniteAbstractExtension.ofInclusion L M hLM
  let EMK : FiniteAbstractExtension G :=
    FiniteAbstractExtension.ofInclusion M K hMK
  let ELK : FiniteAbstractExtension G :=
    FiniteAbstractExtension.ofInclusion L K (hLM.trans hMK)
  letI hELMbaseAbsolute : Finite ((baseField G).toSubgroup ⧸
      ELM.base.toSubgroup.subgroupOf (baseField G).toSubgroup) := by
    simpa [ELM, FiniteAbstractExtension.ofInclusion] using hMabsolute
  letI hEMKbaseAbsolute : Finite ((baseField G).toSubgroup ⧸
      EMK.base.toSubgroup.subgroupOf (baseField G).toSubgroup) := by
    simpa [EMK, FiniteAbstractExtension.ofInclusion] using hKabsolute
  letI hELKbaseAbsolute : Finite ((baseField G).toSubgroup ⧸
      ELK.base.toSubgroup.subgroupOf (baseField G).toSubgroup) := by
    simpa [ELK, FiniteAbstractExtension.ofInclusion] using hKabsolute
  let f := abstractReciprocityNormMap A K M L hLM hMK
  let p := abstractReciprocityNormProjection A K M L hLM hMK
  letI : Finite (FiniteNormQuotient A M L hLM) :=
    finiteNormQuotient_finite_of_classFieldAxiom
      A hcf ELM hMLnormal gML hgML
  letI : Finite (FiniteNormQuotient A K L (hLM.trans hMK)) :=
    finiteNormQuotient_finite_of_classFieldAxiom
      A hcf ELK hLnormal gKL hgKL
  letI : Finite (FiniteNormQuotient A K M hMK) :=
    finiteNormQuotient_finite_of_classFieldAxiom
      A hcf EMK hMnormal gKM hgKM
  have hexact : p.ker = f.range :=
    (AddMonoidHom.exact_iff).1
      (abstractReciprocity_normQuotient_exact A K M L hLM hMK)
  have hpsurjective : Function.Surjective p :=
    abstractReciprocityNormProjection_surjective A K M L hLM hMK
  have hmiddle :
      Nat.card (FiniteNormQuotient A K L (hLM.trans hMK)) =
        Nat.card f.range *
          Nat.card (FiniteNormQuotient A K M hMK) := by
    calc
      Nat.card (FiniteNormQuotient A K L (hLM.trans hMK)) =
          Nat.card p.ker * p.ker.index :=
        (AddSubgroup.card_mul_index p.ker).symm
      _ = Nat.card f.range * Nat.card p.range := by
        rw [AddSubgroup.index_ker, hexact]
      _ = Nat.card f.range *
          Nat.card (FiniteNormQuotient A K M hMK) := by
        have hpRange : p.range = ⊤ :=
          (AddMonoidHom.range_eq_top).2 hpsurjective
        rw [hpRange]
        simp
  have hdegree :
      (ELM.degree : ℕ) * (EMK.degree : ℕ) = (ELK.degree : ℕ) := by
    rw [← ELM.relIndex_eq_degree, ← EMK.relIndex_eq_degree,
      ← ELK.relIndex_eq_degree]
    exact Subgroup.relIndex_mul_relIndex L.toSubgroup M.toSubgroup
      K.toSubgroup hLM hMK
  have hKMpositive : 0 < (EMK.degree : ℕ) := EMK.degree.pos
  have hcardML :
      Nat.card (FiniteNormQuotient A M L hLM) =
        (ELM.degree : ℕ) := by
    simpa [ELM, FiniteAbstractExtension.ofInclusion] using
      finiteNormQuotient_card_of_classFieldAxiom
        A hcf ELM hMLnormal gML hgML
  have hcardKL :
      Nat.card (FiniteNormQuotient A K L (hLM.trans hMK)) =
        (ELK.degree : ℕ) := by
    simpa [ELK, FiniteAbstractExtension.ofInclusion] using
      finiteNormQuotient_card_of_classFieldAxiom
        A hcf ELK hLnormal gKL hgKL
  have hcardKM :
      Nat.card (FiniteNormQuotient A K M hMK) =
        (EMK.degree : ℕ) := by
    simpa [EMK, FiniteAbstractExtension.ofInclusion] using
      finiteNormQuotient_card_of_classFieldAxiom
        A hcf EMK hMnormal gKM hgKM
  have hcardRange :
      Nat.card (FiniteNormQuotient A M L hLM) =
        Nat.card f.range := by
    apply Nat.mul_right_cancel hKMpositive
    calc
      Nat.card (FiniteNormQuotient A M L hLM) *
          (EMK.degree : ℕ) =
          (ELM.degree : ℕ) * (EMK.degree : ℕ) := by
        rw [hcardML]
      _ = (ELK.degree : ℕ) := hdegree
      _ = Nat.card (FiniteNormQuotient A K L (hLM.trans hMK)) := by
        rw [hcardKL]
      _ = Nat.card f.range *
          Nat.card (FiniteNormQuotient A K M hMK) := hmiddle
      _ = Nat.card f.range * (EMK.degree : ℕ) := by
        rw [hcardKM]
  have hRangeBijective : Function.Bijective f.rangeRestrict :=
    (Nat.bijective_iff_surjective_and_card f.rangeRestrict).2
      ⟨AddMonoidHom.rangeRestrict_surjective f, hcardRange⟩
  intro x y hxy
  apply hRangeBijective.1
  exact Subtype.ext hxy

end

end Atlas.Knowledge
