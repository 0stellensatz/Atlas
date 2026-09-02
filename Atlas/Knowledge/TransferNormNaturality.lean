import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.ChosenPrimeElement
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.ExtensionFixedRepresentation
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteAbstractFieldExtension
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FiniteReciprocityHom
import Atlas.Knowledge.FiniteResidueAbstractExtension
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.IntermediateGaloisTransfer
import Atlas.Knowledge.NormalizedValuationLaws
import Atlas.Knowledge.PrimeElement
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.TransferFrobeniusTerms
import Atlas.Knowledge.TransferNormArithmetic
import Atlas.Knowledge.TransferNormFrobeniusGeometry
import Atlas.Knowledge.UnitCohomologyAxiom
import Atlas.Knowledge.ValuationData

/-!
# Transfer-norm naturality

The endpoint of the transfer arc: the norm witness summing conjugates
over a right transversal, the norm identity of the right vertical
arrow, the descended inclusion of finite norm quotients, the
generator-square computation, and transfer–norm naturality itself —
for a finite Galois extension `L | K` and an intermediate `K'`,
reciprocity commutes with transfer (#104).

## Main definitions

* `transferNormNaturalityNormWitness` — the conjugate-summing witness.
* `transferNormNaturalityNormQuotientInclusion` — the right vertical
  arrow.

## Main statements

* `transferNormNaturality_norm_doubleCoset_formula` — the norm
  identity; proved.
* `transferNormNaturality_normQuotientInclusion_finiteNormClass` — the
  descended inclusion on classes; proved.
* `DegreeData.transferNormNaturality_generator_square` — the square on
  one Frobenius generator; proved.
* `DegreeData.transferNormNaturality` — transfer–norm naturality;
  proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
and the whole file is `Type` after the `Type`-pinned
`finiteReciprocityHom` chain. The call sites adapt to the layer's
slimmed transfer family: every `hLK'`-shaped containment the
`extensionSubgroup` abbrev consumed drops from the intermediate
inclusion, subgroup, identification, transfer, transversal, and
normality-restriction calls, while this file's own witness, inclusion
arrow, and privates keep theirs, which their statements still consume.
The source's two evaluation `rfl`-lemma citations inline to bare `rfl`:
the lemma they named lives in the source's Kummer assembly, outside the
ported region, and both uses close definitionally. The citations name this file by bare
basename; it lives at
`AbstractClassFieldTheory/Reciprocity/Construction/` in the source. The
source's namespace `open`s go, while `open MulAction` stays for the
orbit vocabulary.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

open MulAction

section Representation

variable {G : Type} [Group G] [TopologicalSpace G]

/- The quotient action on the invariant carrier agrees with the
relative coset action defining the norm
([Yamaguchi 2026, `MainTransfer.lean:619`][Yamaguchi2026]). -/
private theorem transferNormNaturality_relativeCosetAction_eq_extensionAction
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (a : (extensionFixedRepresentation A K L hLK hnormal).V)
    (q : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :
    relativeCosetAction A K L hLK
        (transferNormNaturalityExtensionFixedEquiv A K L hLK hnormal a) q =
      ((extensionFixedRepresentation A K L hLK hnormal).ρ q a).1 := by
  letI := hnormal
  refine QuotientGroup.induction_on q ?_
  intro k
  rw [relativeCosetAction_mk]
  change A.ρ k.1 a.1 =
    ((extensionFixedRepresentation A K L hLK hnormal).ρ
      (QuotientGroup.mk k) a).1
  rfl

/- Restricting the quotient action to `G(L|K')` agrees with the
relative coset action for `L | K'`
([Yamaguchi 2026, `MainTransfer.lean:640`][Yamaguchi2026]). -/
private theorem transferNormNaturality_relativeCosetAction_intermediate
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal]
    (a : (extensionFixedRepresentation A K L
      (hLK'.trans hK'K) hLnormal).V)
    (r : K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) :
    relativeCosetAction A K' L hLK'
        (transferNormNaturalityExtensionFixedEquiv A K L
          (hLK'.trans hK'K) hLnormal a) r =
      ((extensionFixedRepresentation A K L
        (hLK'.trans hK'K) hLnormal).ρ
          (transferNormNaturalityIntermediateInclusion K K' L hK'K r) a).1 := by
  refine QuotientGroup.induction_on r ?_
  intro k'
  rw [relativeCosetAction_mk, transferNormNaturalityIntermediateInclusion_mk]
  change A.ρ k'.1 a.1 =
    ((extensionFixedRepresentation A K L (hLK'.trans hK'K) hLnormal).ρ
      (QuotientGroup.mk (Subgroup.inclusion hK'K k')) a).1
  rfl

/-- **The element of `A_L` summing the conjugates over a right
transversal of `G(L|K')` in `G(L|K)`** — its `L | K'` norm is the
`L | K` norm of the original element
([Yamaguchi 2026, `MainTransfer.lean:667`][Yamaguchi2026]). -/
noncomputable def transferNormNaturalityNormWitness
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal]
    [Finite (K.toSubgroup ⧸
      L.toSubgroup.subgroupOf K.toSubgroup)]
    (a : ambientFixedAddSubgroup A L) :
    ambientFixedAddSubgroup A L := by
  let H := transferNormNaturalityIntermediateSubgroup K K' L hK'K
  let T := chosenTransferNormNaturalityRightTransversal K K' L hK'K
  letI : H.FiniteIndex := Subgroup.finiteIndex_of_finite
  letI : Fintype (T : Set (K.toSubgroup ⧸
      L.toSubgroup.subgroupOf K.toSubgroup)) :=
    T.2.finite_right.fintype
  let E := extensionFixedRepresentation A K L
    (hLK'.trans hK'K) hLnormal
  let eA := transferNormNaturalityExtensionFixedEquiv A K L
    (hLK'.trans hK'K) hLnormal
  exact eA (∑ t : (T : Set _), E.ρ t.1 (eA.symm a))

/- The decomposition splits the quotient action multiplicatively
([Yamaguchi 2026, `MainTransfer.lean:689`][Yamaguchi2026]). -/
private theorem transferNormNaturality_extensionAction_product
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal]
    (a : (extensionFixedRepresentation A K L
      (hLK'.trans hK'K) hLnormal).V)
    (r : K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup)
    (t : (chosenTransferNormNaturalityRightTransversal K K' L hK'K :
      Set (K.toSubgroup ⧸
        L.toSubgroup.subgroupOf K.toSubgroup))) :
    (extensionFixedRepresentation A K L
        (hLK'.trans hK'K) hLnormal).ρ
        (transferNormNaturalityRightCosetProductEquiv K K' L hK'K (r, t)) a =
      (extensionFixedRepresentation A K L
        (hLK'.trans hK'K) hLnormal).ρ
        (transferNormNaturalityIntermediateInclusion K K' L hK'K r)
        ((extensionFixedRepresentation A K L
          (hLK'.trans hK'K) hLnormal).ρ t.1 a) := by
  rw [transferNormNaturalityRightCosetProductEquiv_apply, map_mul]
  rfl

/-- **The norm identity of the right vertical arrow** — the additive
form of the product calculation
([Yamaguchi 2026, `MainTransfer.lean:713`][Yamaguchi2026]). -/
theorem transferNormNaturality_norm_doubleCoset_formula
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [Finite (K.toSubgroup ⧸
      L.toSubgroup.subgroupOf K.toSubgroup)]
    (a : ambientFixedAddSubgroup A L) :
    letI : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal :=
      transferNormNaturality_intermediateExtension_normal K K' L hK'K
    letI : Finite (K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) :=
      Finite.of_injective
        (transferNormNaturalityIntermediateInclusion K K' L hK'K)
        (transferNormNaturalityIntermediateInclusion_injective
          K K' L hK'K)
    fixedFieldInclusion A K K' hK'K
        (relativeNorm A K L (hLK'.trans hK'K) a) =
      relativeNorm A K' L hLK'
        (transferNormNaturalityNormWitness A K K' L hLK' hK'K a) := by
  letI hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal :=
    transferNormNaturality_intermediateExtension_normal K K' L hK'K
  letI hL'finite : Finite
      (K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) :=
    Finite.of_injective
      (transferNormNaturalityIntermediateInclusion K K' L hK'K)
      (transferNormNaturalityIntermediateInclusion_injective
        K K' L hK'K)
  letI : Fintype (K.toSubgroup ⧸
      L.toSubgroup.subgroupOf K.toSubgroup) := Fintype.ofFinite _
  letI : Fintype (K'.toSubgroup ⧸
      L.toSubgroup.subgroupOf K'.toSubgroup) := Fintype.ofFinite _
  let H := transferNormNaturalityIntermediateSubgroup K K' L hK'K
  let T := chosenTransferNormNaturalityRightTransversal K K' L hK'K
  letI : H.FiniteIndex := Subgroup.finiteIndex_of_finite
  letI : Fintype (T : Set (K.toSubgroup ⧸
      L.toSubgroup.subgroupOf K.toSubgroup)) :=
    T.2.finite_right.fintype
  let E := extensionFixedRepresentation A K L
    (hLK'.trans hK'K) hLnormal
  let eA := transferNormNaturalityExtensionFixedEquiv A K L
    (hLK'.trans hK'K) hLnormal
  let aE := eA.symm a
  let valHom : E.V →+ A.V :=
    (ambientFixedAddSubgroup A L).subtype.comp eA.toAddMonoidHom
  apply Subtype.ext
  simp only [fixedFieldInclusion_coe, relativeNorm_apply_coe,
    relativeNormValue]
  have ha : eA aE = a := eA.apply_symm_apply a
  have hwitness :
      eA.symm (transferNormNaturalityNormWitness A K K' L hLK' hK'K a) =
        ∑ t : (T : Set (K.toSubgroup ⧸
          L.toSubgroup.subgroupOf K.toSubgroup)), E.ρ t.1 aE := by
    simp [transferNormNaturalityNormWitness, T, E, eA, aE]
  have hE :
      (∑ q : K.toSubgroup ⧸
          L.toSubgroup.subgroupOf K.toSubgroup, E.ρ q aE) =
        ∑ r : K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup,
          E.ρ (transferNormNaturalityIntermediateInclusion K K' L hK'K r)
            (∑ t : (T : Set (K.toSubgroup ⧸
              L.toSubgroup.subgroupOf K.toSubgroup)), E.ρ t.1 aE) := by
    calc
      (∑ q : K.toSubgroup ⧸
          L.toSubgroup.subgroupOf K.toSubgroup, E.ρ q aE) =
          ∑ p : (K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) ×
              (T : Set (K.toSubgroup ⧸
                L.toSubgroup.subgroupOf K.toSubgroup)),
            E.ρ (transferNormNaturalityRightCosetProductEquiv
              K K' L hK'K p) aE :=
        (transferNormNaturalityRightCosetProductEquiv K K' L hK'K).sum_comp
          (fun q => E.ρ q aE) |>.symm
      _ = ∑ p : (K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) ×
              (T : Set (K.toSubgroup ⧸
                L.toSubgroup.subgroupOf K.toSubgroup)),
            E.ρ (transferNormNaturalityIntermediateInclusion
              K K' L hK'K p.1) (E.ρ p.2.1 aE) := by
        apply Fintype.sum_congr
        intro p
        exact transferNormNaturality_extensionAction_product
          A K K' L hLK' hK'K aE p.1 p.2
      _ = ∑ r : K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup,
            ∑ t : (T : Set (K.toSubgroup ⧸
              L.toSubgroup.subgroupOf K.toSubgroup)),
              E.ρ (transferNormNaturalityIntermediateInclusion
                K K' L hK'K r) (E.ρ t.1 aE) := by
        rw [Fintype.sum_prod_type]
      _ = ∑ r : K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup,
          E.ρ (transferNormNaturalityIntermediateInclusion K K' L hK'K r)
            (∑ t : (T : Set (K.toSubgroup ⧸
              L.toSubgroup.subgroupOf K.toSubgroup)), E.ρ t.1 aE) := by
        apply Fintype.sum_congr
        intro r
        rw [map_sum]
  calc
    (∑ q : K.toSubgroup ⧸
        L.toSubgroup.subgroupOf K.toSubgroup,
      relativeCosetAction A K L (hLK'.trans hK'K) a q) =
        ∑ q : K.toSubgroup ⧸
          L.toSubgroup.subgroupOf K.toSubgroup, (E.ρ q aE).1 := by
      apply Fintype.sum_congr
      intro q
      rw [← ha]
      exact transferNormNaturality_relativeCosetAction_eq_extensionAction
        A K L (hLK'.trans hK'K) hLnormal aE q
    _ = (∑ q : K.toSubgroup ⧸
        L.toSubgroup.subgroupOf K.toSubgroup, E.ρ q aE).1 := by
      change (∑ q, valHom (E.ρ q aE)) = valHom (∑ q, E.ρ q aE)
      rw [map_sum]
    _ = (∑ r : K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup,
        E.ρ (transferNormNaturalityIntermediateInclusion K K' L hK'K r)
          (∑ t : (T : Set (K.toSubgroup ⧸
            L.toSubgroup.subgroupOf K.toSubgroup)), E.ρ t.1 aE)).1 :=
      congrArg Subtype.val hE
    _ = ∑ r : K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup,
        (E.ρ (transferNormNaturalityIntermediateInclusion K K' L hK'K r)
          (∑ t : (T : Set (K.toSubgroup ⧸
            L.toSubgroup.subgroupOf K.toSubgroup)), E.ρ t.1 aE)).1 := by
      change valHom (∑ r,
          E.ρ (transferNormNaturalityIntermediateInclusion K K' L hK'K r)
            (∑ t : (T : Set (K.toSubgroup ⧸
              L.toSubgroup.subgroupOf K.toSubgroup)), E.ρ t.1 aE)) =
        ∑ r, valHom
          (E.ρ (transferNormNaturalityIntermediateInclusion K K' L hK'K r)
            (∑ t : (T : Set (K.toSubgroup ⧸
              L.toSubgroup.subgroupOf K.toSubgroup)), E.ρ t.1 aE))
      rw [map_sum]
    _ = ∑ r : K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup,
        relativeCosetAction A K' L hLK'
          (transferNormNaturalityNormWitness A K K' L hLK' hK'K a) r := by
      apply Fintype.sum_congr
      intro r
      rw [← hwitness]
      have hr := transferNormNaturality_relativeCosetAction_intermediate
        A K K' L hLK' hK'K
        (eA.symm (transferNormNaturalityNormWitness A K K' L hLK' hK'K a)) r
      calc
        _ = relativeCosetAction A K' L hLK'
            (eA (eA.symm
              (transferNormNaturalityNormWitness A K K' L hLK' hK'K a))) r := by
          simpa only [E, eA] using hr.symm
        _ = relativeCosetAction A K' L hLK'
            (transferNormNaturalityNormWitness A K K' L hLK' hK'K a) r := by
          rw [eA.apply_symm_apply]

/-- **The right vertical arrow of transfer–norm naturality**: the
inclusion `A_K → A_K'` descended to the finite norm quotients
([Yamaguchi 2026, `MainTransfer.lean:858`][Yamaguchi2026]). -/
def transferNormNaturalityNormQuotientInclusion
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal]
    [Finite (K.toSubgroup ⧸
      L.toSubgroup.subgroupOf K.toSubgroup)] :
    letI : Finite (K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) :=
      Finite.of_injective
        (transferNormNaturalityIntermediateInclusion K K' L hK'K)
        (transferNormNaturalityIntermediateInclusion_injective
          K K' L hK'K)
    FiniteNormQuotient A K L (hLK'.trans hK'K) →+
      FiniteNormQuotient A K' L hLK' := by
  letI hL'finite : Finite
      (K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) :=
    Finite.of_injective
      (transferNormNaturalityIntermediateInclusion K K' L hK'K)
      (transferNormNaturalityIntermediateInclusion_injective
        K K' L hK'K)
  let targetClass : ambientFixedAddSubgroup A K →+
      FiniteNormQuotient A K' L hLK' :=
    (finiteNormClassHom A K' L hLK').comp
      (fixedFieldInclusion A K K' hK'K)
  refine finiteNormQuotientLift A K L (hLK'.trans hK'K) targetClass ?_
  rintro _ ⟨a, rfl⟩
  apply (finiteNormClass_eq_zero_iff A K' L hLK' _).2
  refine ⟨transferNormNaturalityNormWitness A K K' L hLK' hK'K a, ?_⟩
  exact (transferNormNaturality_norm_doubleCoset_formula
    A K K' L hLK' hK'K a).symm

/-- **The descended inclusion carries a finite norm class to the class
of its fixed-field inclusion**
([Yamaguchi 2026, `MainTransfer.lean:892`][Yamaguchi2026]). -/
@[simp]
theorem transferNormNaturality_normQuotientInclusion_finiteNormClass
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [Finite (K.toSubgroup ⧸
      L.toSubgroup.subgroupOf K.toSubgroup)]
    (x : ambientFixedAddSubgroup A K) :
    letI : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal :=
      transferNormNaturality_intermediateExtension_normal K K' L hK'K
    letI : Finite (K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) :=
      Finite.of_injective
        (transferNormNaturalityIntermediateInclusion K K' L hK'K)
        (transferNormNaturalityIntermediateInclusion_injective
          K K' L hK'K)
    transferNormNaturalityNormQuotientInclusion A K K' L hLK' hK'K
        (finiteNormClass A K L (hLK'.trans hK'K) x) =
      finiteNormClass A K' L hLK'
        (fixedFieldInclusion A K K' hK'K x) := by
  letI hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal :=
    transferNormNaturality_intermediateExtension_normal K K' L hK'K
  letI hL'finite : Finite
      (K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) :=
    Finite.of_injective
      (transferNormNaturalityIntermediateInclusion K K' L hK'K)
      (transferNormNaturalityIntermediateInclusion_injective
        K K' L hK'K)
  unfold transferNormNaturalityNormQuotientInclusion
  rw [finiteNormQuotientLift_finiteNormClass]
  rfl

namespace DegreeData

/-- **Transfer–norm naturality on one Frobenius generator**: transfer
expands over double cosets, the reciprocity homomorphism evaluates
every positive Frobenius factor, and the prime norms are identified by
`transferNormNaturalityNorm_eq_sum_transferNorms`
([Yamaguchi 2026, `MainTransfer.lean:928`][Yamaguchi2026]). -/
theorem transferNormNaturality_generator_square
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (F : FiniteAbstractFieldExtension G) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ F.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf F.base.field.toSubgroup).Normal]
    [hLbasefinite : Finite (F.base.field.toSubgroup ⧸
      L.toSubgroup.subgroupOf F.base.field.toSubgroup)]
    (σ : D.FrobeniusElements
      (F.toFiniteResidueAbstractExtension D).base L
      (hL.trans F.below) (hLnormal := by
        change (L.toSubgroup.subgroupOf F.base.field.toSubgroup).Normal
        exact hLnormal)) :
    letI : (L.toSubgroup.subgroupOf F.field.field.toSubgroup).Normal :=
      transferNormNaturality_intermediateExtension_normal
        F.base.field F.field.field L F.below
    letI : Finite
        (F.field.field.toSubgroup ⧸
          L.toSubgroup.subgroupOf F.field.field.toSubgroup) :=
      Finite.of_injective
        (transferNormNaturalityIntermediateInclusion
          F.base.field F.field.field L F.below)
        (transferNormNaturalityIntermediateInclusion_injective
          F.base.field F.field.field L F.below)
    D.transferNormNaturalityAbelianizedReciprocity A v hAxiom
        F.field L hL
        (Additive.ofMul
          (transferNormNaturalityTransfer
            F.base.field F.field.field L F.below
            (Abelianization.of
              (D.frobeniusRestriction
                (F.base.toFiniteResidueAbstractField D) L
                (hL.trans F.below) σ)))) =
      transferNormNaturalityNormQuotientInclusion A
        F.base.field F.field.field L hL F.below
        (D.transferNormNaturalityAbelianizedReciprocity A v hAxiom
          F.base L (hL.trans F.below)
          (Additive.ofMul
            (Abelianization.of
              (D.frobeniusRestriction
                (F.base.toFiniteResidueAbstractField D) L
                (hL.trans F.below) σ)))) := by
  letI hL'normal : (L.toSubgroup.subgroupOf F.field.field.toSubgroup).Normal :=
    transferNormNaturality_intermediateExtension_normal
      F.base.field F.field.field L F.below
  letI hL'finite : Finite
      (F.field.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf F.field.field.toSubgroup) :=
    Finite.of_injective
      (transferNormNaturalityIntermediateInclusion
        F.base.field F.field.field L F.below)
      (transferNormNaturalityIntermediateInclusion_injective
        F.base.field F.field.field L F.below)
  let E := F.toFiniteResidueAbstractExtension D
  letI hLnormalE :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal := by
    change (L.toSubgroup.subgroupOf F.base.field.toSubgroup).Normal
    exact hLnormal
  letI hL'normalE : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal := by
    change (L.toSubgroup.subgroupOf F.field.field.toSubgroup).Normal
    exact hL'normal
  letI hLbasefiniteE : Finite (E.base.field.toSubgroup ⧸
      L.toSubgroup.subgroupOf E.base.field.toSubgroup) := by
    change Finite (F.base.field.toSubgroup ⧸
      L.toSubgroup.subgroupOf F.base.field.toSubgroup)
    exact hLbasefinite
  letI hL'finiteE : Finite (E.field.field.toSubgroup ⧸
      L.toSubgroup.subgroupOf E.field.field.toSubgroup) := by
    change Finite (F.field.field.toSubgroup ⧸
      L.toSubgroup.subgroupOf F.field.field.toSubgroup)
    exact hL'finite
  let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
  let hSK := D.frobeniusFixedField_le E.base L (hL.trans E.below) σ
  let hSKF : S.toSubgroup ≤ F.base.field.toSubgroup := by
    change S.toSubgroup ≤ E.base.field.toSubgroup
    exact hSK
  letI : Finite (E.base.field.toSubgroup ⧸
      S.toSubgroup.subgroupOf E.base.field.toSubgroup) :=
    D.frobeniusFixedField_finite E.base L (hL.trans E.below) σ
  letI hSbasefiniteF : Finite (F.base.field.toSubgroup ⧸
      S.toSubgroup.subgroupOf F.base.field.toSubgroup) := by
    change Finite (E.base.field.toSubgroup ⧸
      S.toSubgroup.subgroupOf E.base.field.toSubgroup)
    infer_instance
  let Sfinite : FiniteAbstractField G := {
    field := S
    finite := by
      simpa [E, S,
        FiniteAbstractFieldExtension.toFiniteResidueAbstractExtension,
        FiniteAbstractField.toFiniteResidueAbstractField] using
        D.frobeniusFixedField_absoluteFinite F.base L
          (hL.trans F.below) σ }
  let π : ambientFixedAddSubgroup A S := v.chosenPrimeElement Sfinite
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup
    E L hL
  letI : H.FiniteIndex :=
    D.transferNormNaturalityFrobeniusIntermediateFiniteIndex
      E L hL
  let Ω := Quotient (orbitRel (Subgroup.zpowers σ.1)
    ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
      (hL.trans E.below)) ⧸ H))
  letI : Fintype Ω := Fintype.ofFinite _
  let β (q : Ω) := D.transferNormNaturalityTransferFrobeniusLift
    E L hL σ q
  let tK (q : Ω) : E.base.field.toSubgroup := Quotient.out q.out.out
  let C (q : Ω) := conjugateClosedSubgroup S (tK q).1
  let Sβ (q : Ω) := D.frobeniusFixedField E.field L hL (β q)
  let hSβK' (q : Ω) :=
    D.frobeniusFixedField_le E.field L hL (β q)
  let hSβK'F (q : Ω) : (Sβ q).toSubgroup ≤
      F.field.field.toSubgroup := by
    change (Sβ q).toSubgroup ≤ E.field.field.toSubgroup
    exact hSβK' q
  let hSβC (q : Ω) : (Sβ q).toSubgroup ≤ (C q).toSubgroup :=
    D.transferNormNaturalityTransferFrobenius_fixedField_le_conjugate
      E L hL σ q
  let πβ (q : Ω) : ambientFixedAddSubgroup A (Sβ q) :=
    fixedFieldInclusion A (C q) (Sβ q) (hSβC q)
      (conjugateFixedElement A S (tK q).1 π)
  letI (q : Ω) : Finite
      (E.field.field.toSubgroup ⧸
        (Sβ q).toSubgroup.subgroupOf E.field.field.toSubgroup) :=
    D.frobeniusFixedField_finite E.field L hL (β q)
  letI (q : Ω) : Finite
      (F.field.field.toSubgroup ⧸
        (Sβ q).toSubgroup.subgroupOf F.field.field.toSubgroup) := by
    change Finite
      (E.field.field.toSubgroup ⧸
        (Sβ q).toSubgroup.subgroupOf E.field.field.toSubgroup)
    infer_instance
  letI (q : Ω) : Finite ((baseField G).toSubgroup ⧸
      (Sβ q).toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    D.frobeniusFixedField_absoluteFinite F.field L hL (β q)
  let Sβfinite (q : Ω) : FiniteAbstractField G := {
    field := Sβ q
    finite := inferInstance }
  have hPrime (q : Ω) : v.IsPrimeElement (Sβfinite q) (πβ q) := by
    exact D.transferNormNaturalityTransferFrobenius_conjugatePrime_isPrime
      A v F L hL σ q π
        (v.chosenPrimeElement_isPrime Sfinite)
  let M := E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup
  let ΩN := Quotient (orbitRel M
    (E.base.field.toSubgroup ⧸ S.toSubgroup.subgroupOf E.base.field.toSubgroup))
  let orbitEquiv : Ω ≃ ΩN :=
    D.transferNormNaturalityTransferNormOrbitEquiv E L hL σ
  letI : Fintype ΩN := Fintype.ofFinite _
  let f : ΩN → A.V := fun qN =>
    let q := orbitEquiv.symm qN
    ((relativeNorm A E.field.field (Sβ q) (hSβK' q) (πβ q) :
      ambientFixedAddSubgroup A E.field.field) : A.V)
  have hNorm0 := D.transferNormNaturalityNorm_eq_sum_transferNorms
    A F L hL σ π
  have hNorm :
      ((fixedFieldInclusion A E.base.field E.field.field E.below
          (relativeNorm A E.base.field S hSK π) :
            ambientFixedAddSubgroup A E.field.field) : A.V) =
        ∑ q : Ω, ((relativeNorm A E.field.field
          (Sβ q) (hSβK' q) (πβ q) :
            ambientFixedAddSubgroup A E.field.field) : A.V) := by
    calc
      _ = ∑ qN : ΩN, f qN := by
        simpa only [f, orbitEquiv, Sβ, hSβK', πβ, C, tK, β, S,
          hSK, E] using hNorm0
      _ = ∑ q : Ω, f (orbitEquiv q) :=
        (orbitEquiv.sum_comp f).symm
      _ = ∑ q : Ω, ((relativeNorm A E.field.field
          (Sβ q) (hSβK' q) (πβ q) :
            ambientFixedAddSubgroup A E.field.field) : A.V) := by
        apply Fintype.sum_congr
        intro q
        change ((relativeNorm A E.field.field
            (Sβ (orbitEquiv.symm (orbitEquiv q)))
            (hSβK' (orbitEquiv.symm (orbitEquiv q)))
            (πβ (orbitEquiv.symm (orbitEquiv q))) :
              ambientFixedAddSubgroup A E.field.field) : A.V) = _
        rw [orbitEquiv.symm_apply_apply]
  have hTransfer := D.transferNormNaturalityTransfer_frobenius_product
    E L hL σ
  change D.transferNormNaturalityAbelianizedReciprocity A v hAxiom
      F.field L hL
        (Additive.ofMul
          (transferNormNaturalityTransfer
            E.base.field E.field.field L E.below
            (Abelianization.of
              (D.frobeniusRestriction E.base L
                (hL.trans E.below) σ)))) = _
  rw [hTransfer]
  change D.transferNormNaturalityAbelianizedReciprocity A v hAxiom
      F.field L hL
        (∑ q : Ω, Additive.ofMul
          (Abelianization.of
            (D.frobeniusRestriction E.field L hL (β q)))) = _
  rw [map_sum]
  letI hLnormalF :
      (L.toSubgroup.subgroupOf F.base.field.toSubgroup).Normal :=
    hLnormal
  letI hL'normalF : (L.toSubgroup.subgroupOf F.field.field.toSubgroup).Normal :=
    hL'normal
  letI hLbasefiniteF : Finite (F.base.field.toSubgroup ⧸
      L.toSubgroup.subgroupOf F.base.field.toSubgroup) :=
    hLbasefinite
  letI hL'finiteF : Finite (F.field.field.toSubgroup ⧸
      L.toSubgroup.subgroupOf F.field.field.toSubgroup) :=
    hL'finite
  have hLeft :
      (∑ q : Ω,
        D.transferNormNaturalityAbelianizedReciprocity A v hAxiom
          F.field L hL
            (Additive.ofMul
              (Abelianization.of
                (D.frobeniusRestriction E.field L hL (β q))))) =
      ∑ q : Ω, finiteNormClass A F.field.field L hL
          (relativeNorm A F.field.field (Sβ q) (hSβK'F q) (πβ q)) := by
    apply Fintype.sum_congr
    intro q
    rw [D.transferNormNaturalityAbelianizedReciprocity_of]
    rw [D.finiteReciprocityHom_apply_eq_primeNormClass
      A v hAxiom F.field L hL
      (Additive.ofMul
        (D.frobeniusRestriction E.field L hL (β q)))
      (β q) rfl (πβ q) (by
        simpa [Sβfinite, Sβ, E,
          FiniteAbstractFieldExtension.toFiniteResidueAbstractExtension,
          FiniteAbstractField.toFiniteResidueAbstractField] using hPrime q)]
    simp [E, FiniteAbstractFieldExtension.toFiniteResidueAbstractExtension,
      FiniteAbstractField.toFiniteResidueAbstractField, Sβ]
    rfl
  rw [hLeft]
  rw [D.transferNormNaturalityAbelianizedReciprocity_of]
  rw [D.finiteReciprocityHom_apply_eq_primeNormClass
    A v hAxiom F.base L (hL.trans F.below)
    (Additive.ofMul
      (D.frobeniusRestriction (F.base.toFiniteResidueAbstractField D) L
        (hL.trans F.below) σ))
    σ rfl π (v.chosenPrimeElement_isPrime Sfinite)]
  rw [transferNormNaturality_normQuotientInclusion_finiteNormClass]
  have hNormSub :
      fixedFieldInclusion A E.base.field E.field.field E.below
          (relativeNorm A E.base.field S hSK π) =
        ∑ q : Ω,
          relativeNorm A E.field.field (Sβ q) (hSβK' q) (πβ q) := by
    apply Subtype.ext
    let valHom : ambientFixedAddSubgroup A E.field.field →+ A.V :=
      { toFun := fun x => x.1
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    change valHom (fixedFieldInclusion A E.base.field E.field.field E.below
        (relativeNorm A E.base.field S hSK π)) =
      valHom (∑ q : Ω,
        relativeNorm A E.field.field (Sβ q) (hSβK' q) (πβ q))
    rw [map_sum]
    exact hNorm
  have hNormSubF :
      fixedFieldInclusion A F.base.field F.field.field F.below
          (relativeNorm A F.base.field S hSKF π) =
        ∑ q : Ω,
          relativeNorm A F.field.field (Sβ q) (hSβK'F q) (πβ q) := by
    change fixedFieldInclusion A F.base.field F.field.field F.below
        (relativeNorm A F.base.field S hSKF π) =
      ∑ q : Ω,
        relativeNorm A F.field.field (Sβ q) (hSβK'F q) (πβ q) at hNormSub
    exact hNormSub
  have hNormClasses := congrArg
    (finiteNormClassHom A F.field.field L hL) hNormSubF
  rw [map_sum] at hNormClasses
  exact hNormClasses.symm

/-- **Transfer–norm naturality**: for a finite Galois extension
`L | K` and an intermediate `K'`, reciprocity commutes with transfer —
`r_{L|K'} ∘ Ver = inclusion ∘ r_{L|K}`
([Yamaguchi 2026, `MainTransfer.lean:1203`][Yamaguchi2026]). -/
theorem transferNormNaturality
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (F : FiniteAbstractFieldExtension G) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ F.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf F.base.field.toSubgroup).Normal]
    [hLbasefinite : Finite (F.base.field.toSubgroup ⧸
      L.toSubgroup.subgroupOf F.base.field.toSubgroup)] :
    letI : (L.toSubgroup.subgroupOf F.field.field.toSubgroup).Normal :=
      transferNormNaturality_intermediateExtension_normal
        F.base.field F.field.field L F.below
    letI : Finite
        (F.field.field.toSubgroup ⧸
          L.toSubgroup.subgroupOf F.field.field.toSubgroup) :=
      Finite.of_injective
        (transferNormNaturalityIntermediateInclusion
          F.base.field F.field.field L F.below)
        (transferNormNaturalityIntermediateInclusion_injective
          F.base.field F.field.field L F.below)
    (D.transferNormNaturalityAbelianizedReciprocity A v hAxiom
        F.field L hL).comp
      (MonoidHom.toAdditive
        (transferNormNaturalityTransfer
          F.base.field F.field.field L F.below)) =
      (transferNormNaturalityNormQuotientInclusion A
        F.base.field F.field.field L hL F.below).comp
        (D.transferNormNaturalityAbelianizedReciprocity A v hAxiom
          F.base L (hL.trans F.below)) := by
  letI hL'normal : (L.toSubgroup.subgroupOf F.field.field.toSubgroup).Normal :=
    transferNormNaturality_intermediateExtension_normal
      F.base.field F.field.field L F.below
  letI : Finite
      (F.field.field.toSubgroup ⧸ L.toSubgroup.subgroupOf F.field.field.toSubgroup) :=
    Finite.of_injective
      (transferNormNaturalityIntermediateInclusion
        F.base.field F.field.field L F.below)
      (transferNormNaturalityIntermediateInclusion_injective
        F.base.field F.field.field L F.below)
  apply AddMonoidHom.ext
  intro x
  change D.transferNormNaturalityAbelianizedReciprocity A v hAxiom
      F.field L hL
        (Additive.ofMul
          (transferNormNaturalityTransfer
            F.base.field F.field.field L F.below x.toMul)) =
    transferNormNaturalityNormQuotientInclusion A
      F.base.field F.field.field L hL F.below
      (D.transferNormNaturalityAbelianizedReciprocity A v hAxiom
        F.base L (hL.trans F.below) (Additive.ofMul x.toMul))
  refine QuotientGroup.induction_on x.toMul ?_
  intro q
  obtain ⟨σ, hσ⟩ := D.frobeniusRestriction_surjective
    (F.base.toFiniteResidueAbstractField D) L (hL.trans F.below) q
  rw [← hσ]
  exact D.transferNormNaturality_generator_square
    A v hAxiom F L hL σ

end DegreeData

end Representation

end

end Atlas.Knowledge
