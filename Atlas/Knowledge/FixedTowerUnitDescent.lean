import Mathlib
import Atlas.Knowledge.AbstractExtension
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.FiniteAbstractExtension
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteAbstractFieldExtension
import Atlas.Knowledge.FiniteFieldUnitMaps
import Atlas.Knowledge.FiniteUnramifiedCyclicExtension
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.FixedTowerUnitCorrection
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusExponent
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.FrobeniusFixedFieldAction
import Atlas.Knowledge.FrobeniusFixedFieldTower
import Atlas.Knowledge.FrobeniusPowerFixedField
import Atlas.Knowledge.FrobeniusQuotientAction
import Atlas.Knowledge.FrobeniusQuotientDescent
import Atlas.Knowledge.InertiaQuotientDegreeKernel
import Atlas.Knowledge.MaximalUnramifiedField
import Atlas.Knowledge.PrimeElement
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.UnitCohomologyAxiom
import Atlas.Knowledge.UnitRepresentation
import Atlas.Knowledge.UniversalNormDescent
import Atlas.Knowledge.ValuationData

/-!
# Unit descent on Frobenius fixed-field towers

The fixed-tower action and power correction packaged bundle-natively, the
unit-cohomology axiom applied in the exact power-fixed-field tower — the
barred unit lifts and the corrected upper unit — the norm-enumeration
identity behind the factor `z^n`, and the corrected universal
norm-descent equation on finite fixed-field towers (#104).

## Main definitions

* `ValuationData.fixedTowerUnitAction` — the stabilizing action on the
  upper unit group, on a tower bundle.
* `ValuationData.powerTowerCorrection` — the corrected upper unit of a
  power tower.

## Main statements

* `ValuationData.universalNormDescent_fixedTower_solution` — the axiom
  supplies the barred lifts and the corrected unit; proved.
* `ValuationData.maximalNorm_relativeNorm_fixedTower` — the
  maximal-unramified norm of a tower norm is the orbit sum; proved.
* `ValuationData.universalNormDescent_correctedEquation` — the corrected
  barred unit satisfies the original coinvariant equation after
  inclusion; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
`FiniteResidueAbstractField` and `AbstractExtension` sit at the layer's
top level, the ambient group is `Type u` since the #104 hoist, and the
source's no-op `open`s are dropped. The dead ambient binders are swept
unevenly, as their callees now demand: four declarations keep only
`IsTopologicalGroup`, the power correction also needs `T2Space` for the
#143 bundle map, and the solution theorem keeps compactness and total
disconnectedness for the power-fixed-field apparatus — its Hausdorff
binder is instance-derivable and goes. One coercion ascription steadies
the re-anchored generator calc. The one structural departure: where the
source phrases the axiom through Tate-cohomology vanishing and two
eliminator lemmas, the layer's
`ValuationData.SatisfiesUnramifiedUnitCohomology` is elementwise (#135),
so the solution theorem draws the barred lifts and the correction
directly from the axiom's two components — the `hA` vanishing pair, the
`hEunramified` transport it fed, and both eliminator calls collapse into
the two `obtain`s.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- **The stabilizing action on the upper unit group, expressed directly
on a fixed-field tower** — the bundle-native boundary used by the descent
construction (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FixedTowerUnitDescent.lean:33`). -/
noncomputable def fixedTowerUnitAction
    (v : ValuationData D A) [IsTopologicalGroup G]
    (T : DegreeData.FrobeniusFixedFieldTower D)
    (q : T.ambientBase.field.toSubgroup ⧸
      D.extensionInertiaWithin T.ambientBase.field T.ambient.field
        T.ambient.below)
    (hq : q * T.fieldFrobenius.1 = T.fieldFrobenius.1 * q) :
    v.unitAddSubgroup
        (DegreeData.FrobeniusFixedFieldTower.field (G := G) (D := D) T) →+
      v.unitAddSubgroup
        (DegreeData.FrobeniusFixedFieldTower.field (G := G) (D := D) T) := by
  let TF :=
    D.frobeniusFixedAbstractField T.ambientBase T.ambient.field
      T.ambient.below T.fieldFrobenius
  have hTF : TF = T.field := by
    apply FiniteAbstractField.eq_of_field_eq
    rfl
  exact hTF ▸
    v.frobeniusFixedFieldUnitAction T.ambientBase T.ambient.field
      T.ambient.below T.fieldFrobenius q hq

/-- **The corrected upper unit associated with a power-fixed-field
tower**: all fixed fields and finiteness witnesses come from `P`, so
callers no longer align independently constructed unit-group types
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FixedTowerUnitDescent.lean:59`). -/
noncomputable def powerTowerCorrection
    (v : ValuationData D A) [IsTopologicalGroup G] [T2Space G]
    (P : DegreeData.FrobeniusPowerFixedFieldTower D)
    {ι : Type v} (s : Finset ι)
    (τ : ι →
      (D.extensionNormalizedDegreeContinuous P.ambientBase P.ambient.field
        P.ambient.below).toMonoidHom.ker)
    (hτ : ∀ i, (τ i).1 * P.fieldFrobenius.1 =
      P.fieldFrobenius.1 * (τ i).1)
    (uBar : v.unitAddSubgroup
      (DegreeData.FrobeniusFixedFieldTower.field (G := G) (D := D)
        (DegreeData.FrobeniusPowerFixedFieldTower.toFrobeniusFixedFieldTower
          (G := G) (D := D) P)))
    (uBarᵢ : ι → v.unitAddSubgroup
      (DegreeData.FrobeniusFixedFieldTower.field (G := G) (D := D)
        (DegreeData.FrobeniusPowerFixedFieldTower.toFrobeniusFixedFieldTower
          (G := G) (D := D) P))) :
    v.unitAddSubgroup
      (DegreeData.FrobeniusFixedFieldTower.field (G := G) (D := D)
        (DegreeData.FrobeniusPowerFixedFieldTower.toFrobeniusFixedFieldTower
          (G := G) (D := D) P)) :=
  let T := DegreeData.FrobeniusPowerFixedFieldTower.toFrobeniusFixedFieldTower
    (G := G) (D := D) P
  v.fixedTowerUnitAction T P.frobenius.1 P.frobenius_commute_field uBar -
    uBar -
    ∑ i ∈ s,
      (v.fixedTowerUnitAction T (τ i).1 (hτ i) (uBarᵢ i) - uBarᵢ i)

/-- The cyclic generator selected on the lower fixed field acts on the
upper unit group as the concrete quotient element defining that field
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FixedTowerUnitDescent.lean:91`). -/
theorem unitRepresentation_generator_action_eq
    (v : ValuationData D A) [IsTopologicalGroup G]
    (T : DegreeData.FrobeniusFixedFieldTower D)
    (g : T.Representative)
    (y : v.unitAddSubgroup
      (DegreeData.FrobeniusFixedFieldTower.field (G := G) (D := D) T)) :
    v.fixedTowerUnitAction T T.baseFrobenius.1 T.commute y =
      ((v.unitRepresentation T.extension T.normal).ρ
          (QuotientGroup.mk g.element) y :
        v.unitAddSubgroup
          (DegreeData.FrobeniusFixedFieldTower.field
            (G := G) (D := D) T)) := by
  let gK : T.ambientBase.field.toSubgroup :=
    ⟨g.element.1, (D.frobeniusFixedField_le T.ambientBase T.ambient.field
      T.ambient.below T.baseFrobenius) g.element.2⟩
  have hgKσ :
      (QuotientGroup.mk gK :
        T.ambientBase.field.toSubgroup ⧸
          D.extensionInertiaWithin T.ambientBase.field T.ambient.field
            T.ambient.below) = T.baseFrobenius.1 := by
    exact congrArg Subtype.val g.mapsToFrobenius
  apply Subtype.ext
  apply Subtype.ext
  change A.ρ (Quotient.out T.baseFrobenius.1).1 y.1.1 =
    A.ρ g.element.1 y.1.1
  calc
    A.ρ (Quotient.out T.baseFrobenius.1).1 y.1.1 =
        A.ρ gK.1 y.1.1 := by
      calc
        A.ρ (Quotient.out T.baseFrobenius.1).1 y.1.1 =
            (D.frobeniusFixedFieldAction A T.ambientBase T.ambient.field
              T.ambient.below T.fieldFrobenius T.baseFrobenius.1
                T.commute y.1).1 := by
              rw [D.frobeniusFixedFieldAction_coe]
        _ = A.ρ gK.1 y.1.1 := by
          exact D.frobeniusFixedFieldAction_coe_of_mk
            A T.ambientBase T.ambient.field T.ambient.below
              T.fieldFrobenius T.baseFrobenius.1 T.commute gK hgKσ y.1
    _ = A.ρ g.element.1 y.1.1 := rfl

/-- **The unit-cohomology axiom supplies the barred unit lifts and the
corrected upper unit in the exact power-fixed-field tower used**
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FixedTowerUnitDescent.lean:134`). -/
theorem universalNormDescent_fixedTower_solution
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology)
    (P : DegreeData.FrobeniusPowerFixedFieldTower D)
    {ι : Type v} (s : Finset ι)
    (τ : ι →
      (D.extensionNormalizedDegreeContinuous P.ambientBase P.ambient.field
        P.ambient.below).toMonoidHom.ker)
    (hτσ : ∀ i, (τ i).1 * P.baseFrobenius.1 =
      P.baseFrobenius.1 * (τ i).1)
    (hτσn : ∀ i, (τ i).1 * P.fieldFrobenius.1 =
      P.fieldFrobenius.1 * (τ i).1)
    (u : v.unitAddSubgroup P.toFrobeniusFixedFieldTower.base)
    (uᵢ : ι → v.unitAddSubgroup P.toFrobeniusFixedFieldTower.base)
    (hstar :
      A.ρ (Quotient.out P.frobenius.1).1 u.1.1 - u.1.1 =
        ∑ i ∈ s,
          (A.ρ (Quotient.out (τ i).1).1 (uᵢ i).1.1 - (uᵢ i).1.1)) :
    let T : DegreeData.FrobeniusFixedFieldTower D :=
      DegreeData.FrobeniusPowerFixedFieldTower.toFrobeniusFixedFieldTower
        (G := G) (D := D) P
    ∃ (uBar : v.unitAddSubgroup
          (DegreeData.FrobeniusFixedFieldTower.field (G := G) (D := D) T))
        (uBarᵢ : ι → v.unitAddSubgroup
          (DegreeData.FrobeniusFixedFieldTower.field (G := G) (D := D) T))
        (yBar : v.unitAddSubgroup
          (DegreeData.FrobeniusFixedFieldTower.field (G := G) (D := D) T)),
      relativeNorm A T.extension.base.field T.extension.field.field
          T.extension.below uBar.1 = u.1 ∧
      (∀ i, relativeNorm A T.extension.base.field T.extension.field.field
        T.extension.below
        (uBarᵢ i).1 = (uᵢ i).1) ∧
      v.fixedTowerUnitAction T P.baseFrobenius.1 T.commute yBar - yBar =
        v.powerTowerCorrection P s τ hτσn uBar uBarᵢ := by
  dsimp only
  let K := P.ambientBase
  let L := P.ambient.field
  let hLK := P.ambient.below
  let φ := P.frobenius
  let hφ := P.exponent_one
  let n := P.n
  let hn := P.n_pos
  let σ := P.baseFrobenius
  let σn := P.fieldFrobenius
  let tower := P.toFrobeniusFixedFieldTower
  let S := tower.base.field
  let T := tower.field.field
  let SF := tower.base
  let TF := tower.field
  let hTS := tower.field_le_base
  let hTSnormal : (T.toSubgroup.subgroupOf S.toSubgroup).Normal :=
    tower.normal
  letI : Finite
      (K.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf K.field.toSubgroup) :=
    P.ambient.finite
  letI : Finite
      (S.toSubgroup ⧸ T.toSubgroup.subgroupOf S.toSubgroup) :=
    tower.finiteQuotient
  letI : (T.toSubgroup.subgroupOf S.toSubgroup).Normal := hTSnormal
  have hφσ : φ.1 * σ.1 = σ.1 * φ.1 :=
    P.frobenius_commute_base
  have hφσn : φ.1 * σn.1 = σn.1 * φ.1 :=
    P.frobenius_commute_field
  have hσσn : σ.1 * σn.1 = σn.1 * σ.1 :=
    tower.commute
  have hTSunramified : (AbstractExtension.mk T S hTS).IsUnramified D :=
    D.frobeniusPowerFixedField_isUnramified K L hLK φ hφ n n hn hn
  obtain ⟨gS, hgClosure, _hgDegree, hg⟩ :=
    D.frobeniusPowerFixedField_generator K L hLK φ hφ n n hn hn
  let generator : tower.CyclicGenerator :=
    { element := gS
      mapsToFrobenius := hgClosure
      generates := hg }
  let g : S.toSubgroup ⧸ T.toSubgroup.subgroupOf S.toSubgroup :=
    QuotientGroup.mk gS
  letI : Fintype (S.toSubgroup ⧸ T.toSubgroup.subgroupOf S.toSubgroup) :=
    Fintype.ofFinite _
  let Kuc : FiniteAbstractField G := SF
  let Euc : FiniteUnramifiedCyclicExtension D Kuc :=
    { field := T
      below := hTS
      normal := hTSnormal
      finite := tower.finiteQuotient
      generator := g
      generates := hg
      unramified := hTSunramified }
  let E : FiniteAbstractFieldExtension G := Euc.toFiniteAbstractFieldExtension
  have hEnormal :
      (E.field.field.toSubgroup.subgroupOf
        E.base.field.toSubgroup).Normal :=
    Euc.normal
  letI : (E.field.field.toSubgroup.subgroupOf
      E.base.field.toSubgroup).Normal :=
    hEnormal
  letI : Fintype
      (E.base.field.toSubgroup ⧸
        E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup) :=
    Fintype.ofFinite _
  obtain ⟨uBar, huBar⟩ := (hAxiom Kuc Euc).1 u
  have huBarᵢ_exists (i : ι) : ∃ z : v.unitAddSubgroup TF,
      relativeNorm A S T hTS z.1 = (uᵢ i).1 :=
    (hAxiom Kuc Euc).1 (uᵢ i)
  choose uBarᵢ huBarᵢ using huBarᵢ_exists
  let delta : v.unitAddSubgroup TF :=
    v.powerTowerCorrection P s τ hτσn uBar uBarᵢ
  have hfixedAction
      (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
      (hq : q * σn.1 = σn.1 * q)
      (z : v.unitAddSubgroup TF) :
      v.fixedTowerUnitAction tower q hq z =
        v.frobeniusFixedFieldUnitAction K L hLK σn q hq z := by
    apply Subtype.ext
    apply Subtype.ext
    change A.ρ (Quotient.out q).1 z.1.1 =
      A.ρ (Quotient.out q).1 z.1.1
    rfl
  have hdeltaRelativeNorm : relativeNorm A S T hTS delta.1 = 0 := by
    have hdeltaAmbient :
        delta.1 =
          (v.fixedTowerCorrection K L hLK σn s φ.1 hφσn
            (fun i => (τ i).1) hτσn uBar uBarᵢ).1 := by
      have hdeltaUnit :
          delta =
            v.fixedTowerCorrection K L hLK σn s φ.1 hφσn
              (fun i => (τ i).1) hτσn uBar uBarᵢ := by
        simp [delta, powerTowerCorrection,
          fixedTowerCorrection, tower, K, L, σn,
          Finset.sum_sub_distrib, hfixedAction]
        rfl
      exact congrArg Subtype.val hdeltaUnit
    rw [hdeltaAmbient]
    exact
      v.fixedTowerCorrection_relativeNorm_eq_zero K L hLK σ σn hTS
        s φ.1 hφσ hφσn (fun i => (τ i).1) hτσ hτσn
        u uᵢ uBar uBarᵢ huBar huBarᵢ hstar
  have hdeltaNorm : (Euc.unitRepresentation v).norm.hom delta = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    calc
      ((((Euc.unitRepresentation v).norm.hom delta).1 :
          ambientFixedAddSubgroup A T) : A.V) =
          ((relativeNorm A S T hTS delta.1 :
            ambientFixedAddSubgroup A S) : A.V) :=
        v.unitRepresentation_norm_coe E hEnormal delta
      _ = 0 := congrArg Subtype.val hdeltaRelativeNorm
      _ = (((0 : v.unitAddSubgroup TF).1 :
          ambientFixedAddSubgroup A T) : A.V) := rfl
  obtain ⟨yBar, hyBar⟩ := (hAxiom Kuc Euc).2 delta hdeltaNorm
  have haction :=
    v.unitRepresentation_generator_action_eq
      tower generator.toRepresentative yBar
  have haction' :
      v.fixedTowerUnitAction tower σ.1 hσσn yBar =
        (Euc.unitRepresentation v).ρ Euc.generator yBar := by
    apply Subtype.ext
    apply Subtype.ext
    calc
      (v.fixedTowerUnitAction tower σ.1 hσσn yBar).1.1 =
          (((v.unitRepresentation tower.extension tower.normal).ρ
            (QuotientGroup.mk generator.element) yBar).1.1 : A.V) :=
        congrArg (fun z : v.unitAddSubgroup TF => z.1.1) haction
      _ = (((Euc.unitRepresentation v).ρ Euc.generator yBar).1.1 :
          A.V) := by
        rfl
  refine ⟨uBar, uBarᵢ, yBar, huBar, huBarᵢ, ?_⟩
  rw [← haction'] at hyBar
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : v.unitAddSubgroup TF => z.1.1) hyBar

/-- **The maximal-unramified norm of a relative norm in the power-fixed
tower is the corresponding orbit sum** — the actual norm-enumeration
step behind the factor `z^n` (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FixedTowerUnitDescent.lean:316`). -/
theorem maximalNorm_relativeNorm_fixedTower
    [IsTopologicalGroup G] (v : ValuationData D A)
    (FT : DegreeData.FiniteAmbientFrobeniusFixedFieldTower D)
    (generator : FT.toFrobeniusFixedFieldTower.CyclicGenerator)
    (n : ℕ)
    (hcard : (FT.extension.degree : ℕ) = n)
    (a : v.unitAddSubgroup
      (DegreeData.FrobeniusFixedFieldTower.field (G := G) (D := D)
        FT.toFrobeniusFixedFieldTower)) :
    letI : Finite
        ((D.maximalUnramifiedField FT.ambientBase.field).toSubgroup ⧸
          (D.maximalUnramifiedField FT.ambient.field).toSubgroup.subgroupOf
            (D.maximalUnramifiedField FT.ambientBase.field).toSubgroup) :=
      D.maximalUnramifiedExtension_finite FT.ambientBase.field
        FT.ambient.field
    let Ext := FT.extension
    let S := Ext.base.field
    let T := Ext.field.field
    let I := D.maximalUnramifiedField FT.ambientBase.field
    let E := D.maximalUnramifiedField FT.ambient.field
    let hTE : E.toSubgroup ≤ T.toSubgroup := by
      change (D.maximalUnramifiedField FT.ambient.field).toSubgroup ≤
        (D.frobeniusFixedField FT.ambientBase FT.ambient.field
          FT.ambient.below FT.fieldFrobenius).toSubgroup
      rw [D.maximalUnramifiedField_eq_fieldInertia]
      exact D.fieldInertia_le_frobeniusFixedField FT.ambientBase
        FT.ambient.field FT.ambient.below FT.fieldFrobenius
    let hSE : E.toSubgroup ≤ S.toSubgroup := by
      change (D.maximalUnramifiedField FT.ambient.field).toSubgroup ≤
        (D.frobeniusFixedField FT.ambientBase FT.ambient.field
          FT.ambient.below FT.baseFrobenius).toSubgroup
      rw [D.maximalUnramifiedField_eq_fieldInertia]
      exact D.fieldInertia_le_frobeniusFixedField FT.ambientBase
        FT.ambient.field FT.ambient.below FT.baseFrobenius
    let hEI := D.maximalUnramifiedField_mono FT.ambient.below
    let N := relativeNorm A I E hEI
    let J := fixedFieldInclusion A I E hEI
    J (N (fixedFieldInclusion A S E hSE
        (relativeNorm A S T Ext.below a.1))) =
      D.frobeniusPowerSum A FT.ambientBase.field FT.ambient.field
        FT.ambient.below FT.baseFrobenius.1 n
        (J (N (fixedFieldInclusion A T E hTE a.1))) := by
  dsimp only
  let tower := FT.toFrobeniusFixedFieldTower
  let K := FT.ambientBase
  let L := FT.ambient.field
  let hLK := FT.ambient.below
  let σ := FT.baseFrobenius
  let σ' := FT.fieldFrobenius
  let hTS := FT.field_le_base
  let hTSnormal :
      (FT.field.field.toSubgroup.subgroupOf
        FT.base.field.toSubgroup).Normal :=
    FT.normal
  let gS := generator.element
  let hgClosure := generator.mapsToFrobenius
  let hg := generator.generates
  let hσσ' := FT.commute
  letI : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        (D.maximalUnramifiedField L).toSubgroup.subgroupOf
          (D.maximalUnramifiedField K.field).toSubgroup) :=
    D.maximalUnramifiedExtension_finite K.field L
  let S := FT.base.field
  let T := FT.field.field
  let SF := FT.base
  let TF := FT.field
  letI : Finite
      (S.toSubgroup ⧸ T.toSubgroup.subgroupOf S.toSubgroup) :=
    FT.finiteQuotient
  letI : (T.toSubgroup.subgroupOf S.toSubgroup).Normal := hTSnormal
  let I := D.maximalUnramifiedField K.field
  let E := D.maximalUnramifiedField L
  let hTE : E.toSubgroup ≤ T.toSubgroup := by
    change (D.maximalUnramifiedField L).toSubgroup ≤
      (D.frobeniusFixedField K L hLK σ').toSubgroup
    rw [D.maximalUnramifiedField_eq_fieldInertia]
    exact D.fieldInertia_le_frobeniusFixedField K L hLK σ'
  let hSE : E.toSubgroup ≤ S.toSubgroup := by
    change (D.maximalUnramifiedField L).toSubgroup ≤
      (D.frobeniusFixedField K L hLK σ).toSubgroup
    rw [D.maximalUnramifiedField_eq_fieldInertia]
    exact D.fieldInertia_le_frobeniusFixedField K L hLK σ
  let hEI := D.maximalUnramifiedField_mono hLK
  let N := relativeNorm A I E hEI
  let J := fixedFieldInclusion A I E hEI
  let Ext : FiniteAbstractFieldExtension G := FT.extension
  have hExtNormal :
      (Ext.field.field.toSubgroup.subgroupOf
        Ext.base.field.toSubgroup).Normal :=
    FT.normal
  letI : (Ext.field.field.toSubgroup.subgroupOf
      Ext.base.field.toSubgroup).Normal :=
    hExtNormal
  let U := v.unitRepresentation Ext hExtNormal
  let g : S.toSubgroup ⧸ T.toSubgroup.subgroupOf S.toSubgroup :=
    QuotientGroup.mk gS
  let f : v.unitAddSubgroup TF → v.unitAddSubgroup TF :=
    v.frobeniusFixedFieldUnitAction K L hLK σ' σ.1 hσσ'
  let F : v.unitAddSubgroup TF →+ ambientFixedAddSubgroup A E :=
    (J.comp N).comp
      ((fixedFieldInclusion A T E hTE).comp
        (v.unitAddSubgroup TF).subtype)
  let act : ambientFixedAddSubgroup A E → ambientFixedAddSubgroup A E :=
    D.frobeniusQuotientAction A K.field L hLK σ.1
  have hsemiconj : Function.Semiconj F f act := by
    intro z
    have hIncl := D.frobeniusFixedFieldAction_inclusion A K L hLK
      σ' σ.1 hσσ' z.1
    have hNorm := D.maximalUnramifiedNorm_frobeniusQuotientAction
      A K.field L hLK σ.1 (fixedFieldInclusion A T E hTE z.1)
    calc
      F (f z) = J (N (D.frobeniusQuotientAction A K.field L hLK σ.1
          (fixedFieldInclusion A T E hTE z.1))) := by
        apply congrArg (J.comp N)
        exact hIncl
      _ = D.frobeniusQuotientAction A K.field L hLK σ.1
          (J (N (fixedFieldInclusion A T E hTE z.1))) := hNorm
      _ = act (F z) := rfl
  letI : Fintype (S.toSubgroup ⧸ T.toSubgroup.subgroupOf S.toSubgroup) :=
    Fintype.ofFinite _
  letI : Fintype
      (Ext.base.field.toSubgroup ⧸
        Ext.field.field.toSubgroup.subgroupOf
          Ext.base.field.toSubgroup) := by
    change Fintype (S.toSubgroup ⧸ T.toSubgroup.subgroupOf S.toSubgroup)
    infer_instance
  have hcard' : Fintype.card
      (S.toSubgroup ⧸ T.toSubgroup.subgroupOf S.toSubgroup) = n := by
    calc
      Fintype.card (S.toSubgroup ⧸ T.toSubgroup.subgroupOf S.toSubgroup) =
          Nat.card (S.toSubgroup ⧸
            T.toSubgroup.subgroupOf S.toSubgroup) := by
        rw [Nat.card_eq_fintype_card]
      _ = (Ext.degree : ℕ) :=
        Ext.toFiniteAbstractExtension.degree_coe.symm
      _ = n := hcard
  have hgen (z : v.unitAddSubgroup TF) : U.ρ g z = f z :=
    (v.unitRepresentation_generator_action_eq
      tower generator.toRepresentative z).symm
  have hRep := rep_norm_eq_generatorIterateSum U g hg n hcard' f hgen a
  have hMapped : F (U.norm.hom a) =
      ∑ i : Fin n, F ((f^[i.1]) a) := by
    calc
      F (U.norm.hom a) = F (∑ i : Fin n, (f^[i.1]) a) :=
        congrArg F hRep
      _ = ∑ i : Fin n, F ((f^[i.1]) a) :=
        map_sum F (fun i : Fin n => (f^[i.1]) a) Finset.univ
  have hMapped' : F (U.norm.hom a) =
      ∑ i : Fin n, D.frobeniusQuotientAction A K.field L hLK
        (σ.1 ^ i.1) (F a) := by
    calc
      F (U.norm.hom a) = ∑ i : Fin n, F ((f^[i.1]) a) := hMapped
      _ = ∑ i : Fin n, (act^[i.1]) (F a) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hsemiconj.iterate_right i.1 a
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        let B := D.frobeniusQuotientRepresentation A K.field L hLK
        have hpow :=
          (rep_action_pow_eq_iterate B σ.1 i.1 (F a)).symm
        change
          ((D.frobeniusQuotientAction A K.field L hLK σ.1)^[i.1])
              (F a) =
            D.frobeniusQuotientAction A K.field L hLK
              (σ.1 ^ i.1) (F a) at hpow
        simpa only [act] using hpow
  have hLeft : F (U.norm.hom a) =
      J (N (fixedFieldInclusion A S E hSE
        (relativeNorm A S T hTS a.1))) := by
    apply congrArg (J.comp N)
    apply Subtype.ext
    exact v.unitRepresentation_norm_coe Ext hExtNormal a
  calc
    J (N (fixedFieldInclusion A S E hSE
        (relativeNorm A S T hTS a.1))) = F (U.norm.hom a) := hLeft.symm
    _ = ∑ i : Fin n, D.frobeniusQuotientAction A K.field L hLK
        (σ.1 ^ i.1) (F a) := hMapped'
    _ = D.frobeniusPowerSum A K.field L hLK σ.1 n
        (J (N (fixedFieldInclusion A T E hTE a.1))) := rfl

/-- **The corrected barred unit satisfies the original coinvariant
equation after inclusion into the maximal unramified field**
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FixedTowerUnitDescent.lean:495`). -/
theorem universalNormDescent_correctedEquation
    (v : ValuationData D A) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ σn : D.FrobeniusElements K L hLK)
    {ι : Type v} (s : Finset ι)
    (φ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hφσn : φ * σn.1 = σn.1 * φ)
    (τ : ι →
      K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hτσn : ∀ i, τ i * σn.1 = σn.1 * τ i)
    (hσσn : σ.1 * σn.1 = σn.1 * σ.1)
    [hTabsolute : Finite ((baseField G).toSubgroup ⧸
      (D.frobeniusFixedField K L hLK σn).toSubgroup.subgroupOf
        (baseField G).toSubgroup)]
    (n : ℕ)
    (hσpow : σ.1 = φ ^ n)
    (uBar : v.unitAddSubgroup
      (D.frobeniusFixedAbstractField K L hLK σn))
    (uBarᵢ : ι → v.unitAddSubgroup
      (D.frobeniusFixedAbstractField K L hLK σn))
    (yBar : v.unitAddSubgroup
      (D.frobeniusFixedAbstractField K L hLK σn))
    (hyBar :
      v.frobeniusFixedFieldUnitAction K L hLK σn σ.1 hσσn yBar - yBar =
        v.fixedTowerCorrection K L hLK σn s φ hφσn
          τ hτσn uBar uBarᵢ) :
    let E := D.maximalUnramifiedField L
    let hTE := D.fieldInertia_le_frobeniusFixedField K L hLK σn
    let uBarE := fixedFieldInclusion A
      (D.frobeniusFixedField K L hLK σn) E hTE uBar.1
    let uBarᵢE := fun i => fixedFieldInclusion A
      (D.frobeniusFixedField K L hLK σn) E hTE (uBarᵢ i).1
    let yBarE := fixedFieldInclusion A
      (D.frobeniusFixedField K L hLK σn) E hTE yBar.1
    let w := uBarE - D.frobeniusPowerSum A K.field L hLK φ n yBarE
    D.frobeniusQuotientAction A K.field L hLK φ w - w =
      ∑ i ∈ s,
        (D.frobeniusQuotientAction A K.field L hLK (τ i) (uBarᵢE i) -
          uBarᵢE i) := by
  dsimp only
  let T := D.frobeniusFixedField K L hLK σn
  let TF := D.frobeniusFixedAbstractField K L hLK σn
  let E := D.maximalUnramifiedField L
  let hTE := D.fieldInertia_le_frobeniusFixedField K L hLK σn
  let uBarE := fixedFieldInclusion A T E hTE uBar.1
  let uBarᵢE := fun i => fixedFieldInclusion A T E hTE (uBarᵢ i).1
  let yBarE := fixedFieldInclusion A T E hTE yBar.1
  let φny := D.frobeniusPowerSum A K.field L hLK φ n yBarE
  let w := uBarE - φny
  have hdeltaCoe := v.fixedTowerCorrection_coe K L hLK σn
    s φ hφσn τ hτσn uBar uBarᵢ
  have hyVal := congrArg (fun z : v.unitAddSubgroup TF => z.1.1) hyBar
  have hdeltaVal := congrArg
    (fun z : ambientFixedAddSubgroup A TF.field => z.1) hdeltaCoe
  have hdeltaVal' :
      (v.fixedTowerCorrection K L hLK σn s φ hφσn
        τ hτσn uBar uBarᵢ).1.1 =
        A.ρ (Quotient.out φ).1 uBar.1.1 - uBar.1.1 -
          ∑ i ∈ s,
            (A.ρ (Quotient.out (τ i)).1 (uBarᵢ i).1.1 -
              (uBarᵢ i).1.1) := by
    change
      (v.fixedTowerCorrection K L hLK σn s φ hφσn
        τ hτσn uBar uBarᵢ).1.1 =
        (AddSubgroup.subtype (ambientFixedAddSubgroup A TF.field))
          ((v.frobeniusFixedFieldUnitAction K L hLK σn
              φ hφσn uBar).1 -
            uBar.1 - ∑ i ∈ s,
              ((v.frobeniusFixedFieldUnitAction K L hLK σn
                (τ i) (hτσn i) (uBarᵢ i)).1 - (uBarᵢ i).1)) at hdeltaVal
    rw [map_sub, map_sub, map_sum] at hdeltaVal
    simp only [ValuationData.frobeniusFixedFieldUnitAction] at hdeltaVal
    exact hdeltaVal
  have hraw :
      A.ρ (Quotient.out σ.1).1 yBar.1.1 - yBar.1.1 =
        A.ρ (Quotient.out φ).1 uBar.1.1 - uBar.1.1 -
          ∑ i ∈ s,
            (A.ρ (Quotient.out (τ i)).1 (uBarᵢ i).1.1 -
              (uBarᵢ i).1.1) :=
    hyVal.trans hdeltaVal'
  have hcorrE :
      D.frobeniusQuotientAction A K.field L hLK σ.1 yBarE - yBarE =
        D.frobeniusQuotientAction A K.field L hLK φ uBarE - uBarE -
          ∑ i ∈ s,
            (D.frobeniusQuotientAction A K.field L hLK
              (τ i) (uBarᵢE i) - uBarᵢE i) := by
    apply Subtype.ext
    change
      (AddSubgroup.subtype (ambientFixedAddSubgroup A E))
          (D.frobeniusQuotientAction A K.field L hLK σ.1 yBarE -
            yBarE) =
        (AddSubgroup.subtype (ambientFixedAddSubgroup A E))
          (D.frobeniusQuotientAction A K.field L hLK φ uBarE - uBarE -
            ∑ i ∈ s,
              (D.frobeniusQuotientAction A K.field L hLK
                (τ i) (uBarᵢE i) - uBarᵢE i))
    rw [map_sub, map_sub, map_sum]
    simp_rw [map_sub]
    change
      (D.frobeniusQuotientAction A K.field L hLK σ.1 yBarE).1 -
          yBarE.1 =
        (D.frobeniusQuotientAction A K.field L hLK φ uBarE).1 -
            uBarE.1 -
          ∑ i ∈ s,
            ((D.frobeniusQuotientAction A K.field L hLK
              (τ i) (uBarᵢE i)).1 - (uBarᵢE i).1)
    simp_rw [D.frobeniusQuotientAction_coe_out]
    exact hraw
  have htel := D.frobeniusPowerSum_action_sub A K.field L hLK φ n yBarE
  rw [← hσpow] at htel
  have hw :
      D.frobeniusQuotientAction A K.field L hLK φ w - w =
        (D.frobeniusQuotientAction A K.field L hLK φ uBarE - uBarE) -
          (D.frobeniusQuotientAction A K.field L hLK φ φny - φny) := by
    dsimp [w]
    apply Subtype.ext
    change
      (AddSubgroup.subtype (ambientFixedAddSubgroup A E))
          (D.frobeniusQuotientAction A K.field L hLK φ (uBarE - φny) -
            (uBarE - φny)) =
        (AddSubgroup.subtype (ambientFixedAddSubgroup A E))
          ((D.frobeniusQuotientAction A K.field L hLK φ uBarE - uBarE) -
            (D.frobeniusQuotientAction A K.field L hLK φ φny - φny))
    rw [map_sub, map_sub, map_sub, map_sub]
    change
      (D.frobeniusQuotientAction A K.field L hLK φ (uBarE - φny)).1 -
          (uBarE.1 - φny.1) =
        ((D.frobeniusQuotientAction A K.field L hLK φ uBarE).1 -
            uBarE.1) -
          ((D.frobeniusQuotientAction A K.field L hLK φ φny).1 - φny.1)
    simp_rw [D.frobeniusQuotientAction_coe_out]
    change
      A.ρ (Quotient.out φ).1 (uBarE.1 - φny.1) -
          (uBarE.1 - φny.1) =
        (A.ρ (Quotient.out φ).1 uBarE.1 - uBarE.1) -
          (A.ρ (Quotient.out φ).1 φny.1 - φny.1)
    rw [map_sub]
    abel
  rw [hw, htel, hcorrE]
  abel

end ValuationData

end

end Atlas.Knowledge
