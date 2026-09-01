import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteAbstractFieldExtension
import Atlas.Knowledge.FiniteFieldUnitMaps
import Atlas.Knowledge.FiniteIntermediateCompositum
import Atlas.Knowledge.FiniteIntermediateFieldRefinement
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusExponent
import Atlas.Knowledge.FrobeniusQuotientAction
import Atlas.Knowledge.FrobeniusQuotientDescent
import Atlas.Knowledge.InertiaQuotientDegreeKernel
import Atlas.Knowledge.InfiniteNormSubgroup
import Atlas.Knowledge.MaximalUnramifiedField
import Atlas.Knowledge.NormalizedValuationLaws
import Atlas.Knowledge.PrimeElement
import Atlas.Knowledge.ProfiniteInteger
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.UnitRepresentation
import Atlas.Knowledge.ValuationData

/-!
# Infinite-level unit descent

The finite-stage unit group `U_E = ⋃_M U_M` of an infinite algebraic
extension, with the stability the descent runs on: the Galois quotient
action, Frobenius power sums, and the maximal-unramified relative norm
all preserve finite-stage units, and a norm fixed by a degree-one
Frobenius lift descends to a genuine unit of `K` (#104).

## Main definitions

* `ValuationData.IsFiniteStageUnit` — unit at some finite intermediate
  stage.
* `ValuationData.infiniteUnitAddSubgroup` — the finite-stage unit group
  `U_E` inside `A_E`.

## Main statements

* `ValuationData.descend_maximalUnramified_fixed_unit_of_finiteSupport`
  — the unit-valued strengthening of finite-support descent; proved.
* `ValuationData.frobeniusQuotientAction_mem_infiniteUnitAddSubgroup` —
  the quotient action preserves finite-stage units; proved.
* `ValuationData.maximalUnramifiedNorm_mem_infiniteUnitAddSubgroup` —
  the included norm preserves finite-stage units; proved.
* `ValuationData.descend_maximalUnramifiedNorm_unit` — a Frobenius-fixed
  norm of a finite-stage unit descends to a unit of `K`; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling —
under it the two enrichment bundles at the head bind no containment
beyond their structure fields — `ZHat` is `ProfiniteInteger`,
`zHatMulNat_injective` with its positivity is
`ProfiniteInteger.nsmul_left_injective` with `.pos.ne'`,
`extensionSubgroup_maximalUnramifiedField_normal` is the layer's
`subgroupOf_maximalUnramifiedField_normal`, the finiteness of `L̃/K̃` is
#138's containment-free form, and the ambient group is `Type` because
the file leans on `Atlas.Knowledge.DegreeData.frobeniusQuotientAction`'s
descent siblings — though the first descent theorem sheds even that,
after #146 did; the source's no-op `open`s are dropped, a dead `let`
freed by the spelling goes, one `by exact` flattens to `from`, and the
finiteness-of-a-tower calls are #136's two-argument instance-supplied
form. One ascribed `obtain` anchors the descended element over `K.field`
— the enrichment's field is that field definitionally, but the rewrites
the valuation calculation runs need the anchor spelled.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- The canonical finite-field extension bundle carried by a finite
intermediate field over a bundled finite base ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitDescent.lean:30`]
[Yamaguchi2026]). -/
noncomputable def toFiniteAbstractFieldExtension
    {E : ClosedSubgroup G} (K : FiniteAbstractField G)
    (M : FiniteIntermediateField E K.field) :
    FiniteAbstractFieldExtension G := by
  letI : Finite
      (K.field.toSubgroup ⧸
        M.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
    M.finite
  exact FiniteAbstractFieldExtension.ofInclusion M.field K M.below

/-- The upper endpoint of the canonical finite-field extension bundle
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitDescent.lean:40`]
[Yamaguchi2026]). -/
noncomputable def toFiniteAbstractField
    {E : ClosedSubgroup G} (K : FiniteAbstractField G)
    (M : FiniteIntermediateField E K.field) : FiniteAbstractField G :=
  (M.toFiniteAbstractFieldExtension K).field

end FiniteIntermediateField

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- **Unit-valued strengthening of finite-support descent**: if the
chosen finite support is a unit, the descended `K`-rational element is a
unit as well ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitDescent.lean:54`]
[Yamaguchi2026]). -/
theorem descend_maximalUnramified_fixed_unit_of_finiteSupport
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hφ : D.frobeniusExponent
      (K.toFiniteResidueAbstractField D) L hLK φ = 1)
    (P : FiniteIntermediateField (D.maximalUnramifiedField L) K.field)
    [hPnormal : (P.field.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (aI : ambientFixedAddSubgroup A (D.maximalUnramifiedField K.field))
    (aP : v.unitAddSubgroup (P.toFiniteAbstractField K))
    (hsupport :
      fixedFieldInclusion A P.field (D.maximalUnramifiedField L)
          P.above aP.1 =
        fixedFieldInclusion A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK) aI)
    (hfixed :
      D.frobeniusQuotientAction A K.field L hLK φ.1
          (fixedFieldInclusion A (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK) aI) =
        fixedFieldInclusion A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK) aI) :
    ∃ aK : v.unitAddSubgroup K,
      fixedFieldInclusion A K.field (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField_le K.field) aK.1 = aI := by
  obtain ⟨bK, hbK⟩ :
      ∃ bK : ambientFixedAddSubgroup A K.field,
        fixedFieldInclusion A K.field (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField_le K.field) bK = aI :=
    D.descend_maximalUnramified_fixed_of_finiteSupport
      A (K.toFiniteResidueAbstractField D) L hLK φ hφ
        P aI aP.1 hsupport hfixed
  letI : Finite
      (K.field.toSubgroup ⧸
        P.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
    P.finite
  let EP := P.toFiniteAbstractFieldExtension K
  have hKP :
      fixedFieldInclusion A K.field P.field P.below bK = aP.1 := by
    apply Subtype.ext
    have hsupportVal := congrArg
      (fun z : ambientFixedAddSubgroup A (D.maximalUnramifiedField L) =>
        z.1)
      hsupport
    have hbKVal := congrArg
      (fun z : ambientFixedAddSubgroup A
        (D.maximalUnramifiedField K.field) => z.1)
      hbK
    exact hbKVal.trans hsupportVal.symm
  have htower := v.normalizedValuation_tower EP
    (fixedFieldInclusion A K.field P.field P.below bK)
  have hvalP :
      v.valuationAt EP.field
        (fixedFieldInclusion A K.field P.field P.below bK) = 0 := by
    rw [hKP]
    exact aP.2
  have hmul :
      (EP.degree : ℕ) •
        ((v.valuationAt K bK : v.valueGroup) : ProfiniteInteger) = 0 := by
    let ER := EP.toFiniteResidueAbstractExtension D
    change (ER.residueDegree : ℕ) •
        ((v.valuationAt EP.field
          (fixedFieldInclusion A K.field P.field P.below bK) :
            v.valueGroup) : ProfiniteInteger) =
      ((v.valuationAt K
        (relativeNorm A K.field P.field P.below
          (fixedFieldInclusion A K.field P.field P.below bK)) :
            v.valueGroup) : ProfiniteInteger) at htower
    rw [hvalP] at htower
    rw [show relativeNorm A K.field P.field P.below
        (fixedFieldInclusion A K.field P.field P.below bK) =
          (EP.degree : ℕ) • bK from
      relativeNorm_fixedFieldInclusion A EP.toFiniteAbstractExtension
        bK, map_nsmul] at htower
    simpa using htower.symm
  have hbKunit : bK ∈ v.unitAddSubgroup K := by
    rw [v.mem_unitAddSubgroup_iff]
    apply Subtype.ext
    apply ProfiniteInteger.nsmul_left_injective EP.degree.pos.ne'
    change (EP.degree : ℕ) •
        ((v.valuationAt K bK : v.valueGroup) : ProfiniteInteger) =
      (EP.degree : ℕ) • ((0 : v.valueGroup) : ProfiniteInteger)
    simpa using hmul
  exact ⟨⟨bK, hbKunit⟩, hbK⟩

/-- **Unit at some finite intermediate stage** — the literal
finite-support meaning of `U_E = ⋃_M U_M` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitDescent.lean:136`]
[Yamaguchi2026]). -/
def IsFiniteStageUnit
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A E) : Prop :=
  ∃ M : FiniteIntermediateField E K.field,
    ∃ u : v.unitAddSubgroup (M.toFiniteAbstractField K),
      fixedFieldInclusion A M.field E M.above u.1 = a

/-- **The actual finite-stage unit group `U_E` inside `A_E`**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitDescent.lean:145`]
[Yamaguchi2026]). -/
noncomputable def infiniteUnitAddSubgroup
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (hEK : E.toSubgroup ≤ K.field.toSubgroup) :
    AddSubgroup (ambientFixedAddSubgroup A E) where
  carrier := {a | v.IsFiniteStageUnit E K a}
  zero_mem' := by
    let M := FiniteIntermediateField.base E K.field hEK
    refine ⟨M, 0, ?_⟩
    rfl
  add_mem' := by
    intro a b ha hb
    rcases ha with ⟨M, u, hu⟩
    rcases hb with ⟨N, w, hw⟩
    let P := M.compositum N
    letI hPfinite : Finite
        (K.field.toSubgroup ⧸
          P.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
      P.finite
    let hPM : P.field.toSubgroup ≤ M.field.toSubgroup :=
      M.compositum_le_left N
    let hPN : P.field.toSubgroup ≤ N.field.toSubgroup :=
      M.compositum_le_right N
    letI hPMfinite : Finite
        (M.field.toSubgroup ⧸
          P.field.toSubgroup.subgroupOf M.field.toSubgroup) :=
      FiniteIntermediateField.finite_extension_of_le M.below hPM
    letI hPNfinite : Finite
        (N.field.toSubgroup ⧸
          P.field.toSubgroup.subgroupOf N.field.toSubgroup) :=
      FiniteIntermediateField.finite_extension_of_le N.below hPN
    letI : Finite
        ((M.toFiniteAbstractField K).field.toSubgroup ⧸
          P.field.toSubgroup.subgroupOf
            (M.toFiniteAbstractField K).field.toSubgroup) := by
      change Finite
        (M.field.toSubgroup ⧸
          P.field.toSubgroup.subgroupOf M.field.toSubgroup)
      exact hPMfinite
    letI : Finite
        ((N.toFiniteAbstractField K).field.toSubgroup ⧸
          P.field.toSubgroup.subgroupOf
            (N.toFiniteAbstractField K).field.toSubgroup) := by
      change Finite
        (N.field.toSubgroup ⧸
          P.field.toSubgroup.subgroupOf N.field.toSubgroup)
      exact hPNfinite
    let EMP : FiniteAbstractFieldExtension G :=
      FiniteAbstractFieldExtension.ofInclusion
        P.field (M.toFiniteAbstractField K) hPM
    let ENP : FiniteAbstractFieldExtension G :=
      FiniteAbstractFieldExtension.ofInclusion
        P.field (N.toFiniteAbstractField K) hPN
    let hEMPfield : EMP.field = P.toFiniteAbstractField K :=
      FiniteAbstractField.eq_of_field_eq _ _ rfl
    let hENPfield : ENP.field = P.toFiniteAbstractField K :=
      FiniteAbstractField.eq_of_field_eq _ _ rfl
    let uP : v.unitAddSubgroup (P.toFiniteAbstractField K) :=
      hEMPfield ▸ v.finiteUnitInclusion EMP u
    let wP : v.unitAddSubgroup (P.toFiniteAbstractField K) :=
      hENPfield ▸ v.finiteUnitInclusion ENP w
    refine ⟨P, uP + wP, ?_⟩
    apply Subtype.ext
    have huval : u.1.1 = a.1 :=
      congrArg (fun x : ambientFixedAddSubgroup A E => x.1) hu
    have hwval : w.1.1 = b.1 :=
      congrArg (fun x : ambientFixedAddSubgroup A E => x.1) hw
    change uP.1.1 + wP.1.1 = a.1 + b.1
    have huP : uP.1.1 = u.1.1 :=
      v.finiteUnitInclusion_transport_coe EMP
        (P.toFiniteAbstractField K) hEMPfield u
    have hwP : wP.1.1 = w.1.1 :=
      v.finiteUnitInclusion_transport_coe ENP
        (P.toFiniteAbstractField K) hENPfield w
    rw [huP, hwP, huval, hwval]
  neg_mem' := by
    intro a ha
    rcases ha with ⟨M, u, hu⟩
    refine ⟨M, -u, ?_⟩
    apply Subtype.ext
    exact congrArg Neg.neg (congrArg Subtype.val hu)

/-- Membership in the finite-stage unit group is the finite-stage
condition ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitDescent.lean:225`]
[Yamaguchi2026]). -/
@[simp]
theorem mem_infiniteUnitAddSubgroup_iff
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (hEK : E.toSubgroup ≤ K.field.toSubgroup)
    (a : ambientFixedAddSubgroup A E) :
    a ∈ v.infiniteUnitAddSubgroup E K hEK ↔
      v.IsFiniteStageUnit E K a :=
  Iff.rfl

/-- **The actual `G(L̃/K)`-action preserves the finite-stage unit group
`U_{L̃}`**: a unit is first moved to a finite Galois refinement of its
support; the refinement is stable under the chosen representative, so
the translated element still has finite unit support ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitDescent.lean:238`]
[Yamaguchi2026]). -/
theorem frobeniusQuotientAction_mem_infiniteUnitAddSubgroup
    (v : ValuationData D A) [IsTopologicalGroup G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (ha : a ∈ v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK)) :
    D.frobeniusQuotientAction A K.field L hLK q a ∈
      v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
        (D.maximalUnramifiedField_le_of_le hLK) := by
  let E := D.maximalUnramifiedField L
  letI hEnormal : (E.toSubgroup.subgroupOf K.field.toSubgroup).Normal :=
    D.subgroupOf_maximalUnramifiedField_normal K.field L hLK
  rcases ha with ⟨M, u, hu⟩
  let R := M.galoisRefinement
  have hRM : R.field.toSubgroup ≤ M.field.toSubgroup :=
    M.galoisRefinement_le_field
  letI hRfinite : Finite
      (K.field.toSubgroup ⧸
        R.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
    R.finite
  letI hRMfinite : Finite
      (M.field.toSubgroup ⧸
        R.field.toSubgroup.subgroupOf M.field.toSubgroup) :=
    FiniteIntermediateField.finite_extension_of_le M.below hRM
  letI : Finite
      ((M.toFiniteAbstractField K).field.toSubgroup ⧸
        R.field.toSubgroup.subgroupOf
          (M.toFiniteAbstractField K).field.toSubgroup) := by
    change Finite
      (M.field.toSubgroup ⧸
        R.field.toSubgroup.subgroupOf M.field.toSubgroup)
    exact hRMfinite
  let k : K.field.toSubgroup := Quotient.out q
  have hkq :
      (QuotientGroup.mk k :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) =
        q :=
    Quotient.out_eq' q
  let EMR : FiniteAbstractFieldExtension G :=
    FiniteAbstractFieldExtension.ofInclusion
      R.field (M.toFiniteAbstractField K) hRM
  let ER := R.toFiniteAbstractFieldExtension K
  let hEMRfield : EMR.field = R.toFiniteAbstractField K :=
    FiniteAbstractField.eq_of_field_eq _ _ rfl
  let uR : v.unitAddSubgroup (R.toFiniteAbstractField K) :=
    hEMRfield ▸ v.finiteUnitInclusion EMR u
  let uR' : v.unitAddSubgroup (R.toFiniteAbstractField K) :=
    v.unitActionLinearMap ER
      (inferInstance :
        (R.field.toSubgroup.subgroupOf K.field.toSubgroup).Normal) k uR
  refine ⟨R, uR', ?_⟩
  rw [← hkq]
  apply Subtype.ext
  have huval : u.1.1 = a.1 :=
    congrArg (fun z : ambientFixedAddSubgroup A E => z.1) hu
  change A.ρ k.1 uR.1.1 = A.ρ k.1 a.1
  have huR : uR.1.1 = u.1.1 :=
    v.finiteUnitInclusion_transport_coe EMR
      (R.toFiniteAbstractField K) hEMRfield u
  rw [huR, huval]

/-- The Frobenius power sum preserves the finite-stage unit group of the
maximal unramified extension ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitDescent.lean:299`]
[Yamaguchi2026]). -/
theorem frobeniusPowerSum_mem_infiniteUnit_universalNormDescent
    (v : ValuationData D A) [IsTopologicalGroup G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (n : ℕ)
    (x : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (hx : x ∈ v.infiniteUnitAddSubgroup
      (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK)) :
    D.frobeniusPowerSum A K.field L hLK φ n x ∈
      v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
        (D.maximalUnramifiedField_le_of_le hLK) := by
  unfold DegreeData.frobeniusPowerSum
  apply AddSubgroup.sum_mem
  intro i _
  exact v.frobeniusQuotientAction_mem_infiniteUnitAddSubgroup
    K L hLK (φ ^ i.1) x hx

/-- **The relative norm from `L̃` to `K̃`, included back in `A_{L̃}`,
preserves finite-stage units** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitDescent.lean:321`]
[Yamaguchi2026]). -/
theorem maximalUnramifiedNorm_mem_infiniteUnitAddSubgroup
    (v : ValuationData D A) [IsTopologicalGroup G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (ha : a ∈ v.infiniteUnitAddSubgroup
      (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK)) :
    letI : Finite
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          (D.maximalUnramifiedField L).toSubgroup.subgroupOf
            (D.maximalUnramifiedField K.field).toSubgroup) :=
      D.maximalUnramifiedExtension_finite K.field L
    fixedFieldInclusion A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_mono hLK)
        (relativeNorm A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK) a)
      ∈ v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
        (D.maximalUnramifiedField_le_of_le hLK) := by
  letI : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        (D.maximalUnramifiedField L).toSubgroup.subgroupOf
          (D.maximalUnramifiedField K.field).toSubgroup) :=
    D.maximalUnramifiedExtension_finite K.field L
  let I := D.maximalUnramifiedField K.field
  let E := D.maximalUnramifiedField L
  let hEI := D.maximalUnramifiedField_mono hLK
  let N := relativeNorm A I E hEI
  letI : Fintype
      (I.toSubgroup ⧸ E.toSubgroup.subgroupOf I.toSubgroup) :=
    Fintype.ofFinite _
  let qK (q : I.toSubgroup ⧸ E.toSubgroup.subgroupOf I.toSubgroup) :
      K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK :=
    let r : I.toSubgroup := Quotient.out q
    let k : K.field.toSubgroup :=
      ⟨r.1, (D.maximalUnramifiedField_le K.field) r.2⟩
    QuotientGroup.mk k
  let f (q : I.toSubgroup ⧸ E.toSubgroup.subgroupOf I.toSubgroup) :
      ambientFixedAddSubgroup A E :=
    D.frobeniusQuotientAction A K.field L hLK (qK q) a
  have hterm (q : I.toSubgroup ⧸ E.toSubgroup.subgroupOf I.toSubgroup) :
      f q ∈ v.infiniteUnitAddSubgroup E K
        (D.maximalUnramifiedField_le_of_le hLK) := by
    exact
      v.frobeniusQuotientAction_mem_infiniteUnitAddSubgroup
        K L hLK (qK q) a ha
  have hsum :
      ∑ q : I.toSubgroup ⧸ E.toSubgroup.subgroupOf I.toSubgroup, f q ∈
        v.infiniteUnitAddSubgroup E K
          (D.maximalUnramifiedField_le_of_le hLK) :=
    AddSubgroup.sum_mem _ (fun q _ => hterm q)
  have heq :
      fixedFieldInclusion A I E hEI (N a) =
        ∑ q : I.toSubgroup ⧸ E.toSubgroup.subgroupOf I.toSubgroup,
          f q := by
    apply Subtype.ext
    rw [fixedFieldInclusion_coe, relativeNorm_apply_coe]
    rw [relativeNormValue]
    change
      ∑ q : I.toSubgroup ⧸ E.toSubgroup.subgroupOf I.toSubgroup,
          relativeCosetAction A I E hEI a q =
        (AddSubgroup.subtype (ambientFixedAddSubgroup A E))
          (∑ q : I.toSubgroup ⧸ E.toSubgroup.subgroupOf I.toSubgroup,
            f q)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro q _
    let r : I.toSubgroup := Quotient.out q
    have hrq : (QuotientGroup.mk r :
        I.toSubgroup ⧸ E.toSubgroup.subgroupOf I.toSubgroup) = q :=
      Quotient.out_eq' q
    change relativeCosetAction A I E hEI a q = (f q).1
    calc
      relativeCosetAction A I E hEI a q =
          relativeCosetAction A I E hEI a (QuotientGroup.mk r) :=
        congrArg (relativeCosetAction A I E hEI a) hrq.symm
      _ = A.ρ r.1 a.1 := relativeCosetAction_mk A I E hEI a r
      _ = (f q).1 := by rfl
  rw [heq]
  exact hsum

/-- **A maximal-unramified norm of a finite-stage unit descends to a
genuine unit of `K` once it is fixed by a degree-one Frobenius lift**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitDescent.lean:406`]
[Yamaguchi2026]). -/
theorem descend_maximalUnramifiedNorm_unit
    (v : ValuationData D A) [IsTopologicalGroup G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (φ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hφ : D.frobeniusExponent
      (K.toFiniteResidueAbstractField D) L hLK φ = 1)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (ha : a ∈ v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK))
    (hfixed :
      letI : Finite
          ((D.maximalUnramifiedField K.field).toSubgroup ⧸
            (D.maximalUnramifiedField L).toSubgroup.subgroupOf
              (D.maximalUnramifiedField K.field).toSubgroup) :=
        D.maximalUnramifiedExtension_finite K.field L
      let N := relativeNorm A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
      let J := fixedFieldInclusion A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
      D.frobeniusQuotientAction A K.field L hLK φ.1 (J (N a)) =
        J (N a)) :
    letI : Finite
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          (D.maximalUnramifiedField L).toSubgroup.subgroupOf
            (D.maximalUnramifiedField K.field).toSubgroup) :=
      D.maximalUnramifiedExtension_finite K.field L
    ∃ aK : v.unitAddSubgroup K,
      fixedFieldInclusion A K.field (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField_le K.field) aK.1 =
        relativeNorm A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK) a := by
  letI : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        (D.maximalUnramifiedField L).toSubgroup.subgroupOf
          (D.maximalUnramifiedField K.field).toSubgroup) :=
    D.maximalUnramifiedExtension_finite K.field L
  let I := D.maximalUnramifiedField K.field
  let E := D.maximalUnramifiedField L
  let hEI := D.maximalUnramifiedField_mono hLK
  let N := relativeNorm A I E hEI
  let J := fixedFieldInclusion A I E hEI
  letI hEnormal : (E.toSubgroup.subgroupOf K.field.toSubgroup).Normal :=
    D.subgroupOf_maximalUnramifiedField_normal K.field L hLK
  have hmem : J (N a) ∈ v.infiniteUnitAddSubgroup E K
      (D.maximalUnramifiedField_le_of_le hLK) :=
    v.maximalUnramifiedNorm_mem_infiniteUnitAddSubgroup K L hLK a ha
  rcases hmem with ⟨Q, aQ, haQ⟩
  let R := Q.galoisRefinement
  let hRQ : R.field.toSubgroup ≤ Q.field.toSubgroup :=
    Q.galoisRefinement_le_field
  letI hQabsolute : Finite ((baseField G).toSubgroup ⧸
      Q.field.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    Q.absoluteFinite
  letI hRfinite : Finite
      (K.field.toSubgroup ⧸
        R.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
    R.finite
  letI hRQfinite : Finite
      (Q.field.toSubgroup ⧸
        R.field.toSubgroup.subgroupOf Q.field.toSubgroup) :=
    FiniteIntermediateField.finite_extension_of_le Q.below hRQ
  letI : Finite
      ((Q.toFiniteAbstractField K).field.toSubgroup ⧸
        R.field.toSubgroup.subgroupOf
          (Q.toFiniteAbstractField K).field.toSubgroup) := by
    change Finite
      (Q.field.toSubgroup ⧸
        R.field.toSubgroup.subgroupOf Q.field.toSubgroup)
    exact hRQfinite
  letI hRnormal :
      (R.field.toSubgroup.subgroupOf K.field.toSubgroup).Normal :=
    FiniteIntermediateField.galoisRefinement_normal Q
  let EQR : FiniteAbstractFieldExtension G :=
    FiniteAbstractFieldExtension.ofInclusion
      R.field (Q.toFiniteAbstractField K) hRQ
  let hEQRfield : EQR.field = R.toFiniteAbstractField K :=
    FiniteAbstractField.eq_of_field_eq _ _ rfl
  let aR : v.unitAddSubgroup (R.toFiniteAbstractField K) :=
    hEQRfield ▸ v.finiteUnitInclusion EQR aQ
  have haR : fixedFieldInclusion A R.field E R.above aR.1 = J (N a) := by
    apply Subtype.ext
    change aR.1.1 = (J (N a)).1
    have haRcoe : aR.1.1 = aQ.1.1 :=
      v.finiteUnitInclusion_transport_coe EQR
        (R.toFiniteAbstractField K) hEQRfield aQ
    rw [haRcoe]
    exact congrArg Subtype.val haQ
  exact v.descend_maximalUnramified_fixed_unit_of_finiteSupport
    K L hLK φ hφ R (N a) aR haR hfixed

end ValuationData

end

end Atlas.Knowledge
