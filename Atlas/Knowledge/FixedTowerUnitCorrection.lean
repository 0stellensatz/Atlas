import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.FiniteFieldUnitMaps
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.FrobeniusFixedFieldAction
import Atlas.Knowledge.FrobeniusFixedFieldTower
import Atlas.Knowledge.PrimeElement
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.ValuationData

/-!
# Fixed-tower unit correction

The unit-valued correction term on the upper field of a Frobenius
fixed-field tower — the additive right-hand side of the corrected
equation — with its coefficient identity and the norm calculation that
sends it to zero, immediately before `Ĥ⁻¹ = 0` enters (#104).

## Main definitions

* `ValuationData.fixedTowerCorrection` — the unit-valued correction
  term.

## Main statements

* `ValuationData.fixedTowerCorrection_relativeNorm_eq_zero` — the lower
  norm kills the correction term; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
`FiniteResidueAbstractField` sits at the layer's top level, the ambient
group is `Type u` since the #104 hoist, and the source's no-op `open`s
are dropped, along with the ambient separation binders #140's slimming
left dead on all three declarations.

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

/-- **The unit-valued correction term on the upper Frobenius fixed field**
— the additive form of the right-hand side of the corrected equation
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FixedTowerUnitCorrection.lean:30`). -/
noncomputable def fixedTowerCorrection
    (v : ValuationData D A) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σn : D.FrobeniusElements K L hLK)
    [Finite ((baseField G).toSubgroup ⧸
      (D.frobeniusFixedField K L hLK σn).toSubgroup.subgroupOf
        (baseField G).toSubgroup)]
    {ι : Type v} (s : Finset ι)
    (φ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hφσn : φ * σn.1 = σn.1 * φ)
    (τ : ι → K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hτσn : ∀ i, τ i * σn.1 = σn.1 * τ i)
    (uBar :
      v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σn))
    (uBarᵢ : ι →
      v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σn)) :
    v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σn) :=
  v.frobeniusFixedFieldUnitAction K L hLK σn φ hφσn uBar -
    uBar -
    ∑ i ∈ s,
      (v.frobeniusFixedFieldUnitAction K L hLK σn
          (τ i) (hτσn i) (uBarᵢ i) - uBarᵢ i)

/-- The underlying fixed-tower correction is the Frobenius difference
minus the prescribed finite sum of correction terms (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FixedTowerUnitCorrection.lean:62`). -/
theorem fixedTowerCorrection_coe
    (v : ValuationData D A) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σn : D.FrobeniusElements K L hLK)
    [Finite ((baseField G).toSubgroup ⧸
      (D.frobeniusFixedField K L hLK σn).toSubgroup.subgroupOf
        (baseField G).toSubgroup)]
    {ι : Type v} (s : Finset ι)
    (φ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hφσn : φ * σn.1 = σn.1 * φ)
    (τ : ι → K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hτσn : ∀ i, τ i * σn.1 = σn.1 * τ i)
    (uBar :
      v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σn))
    (uBarᵢ : ι →
      v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σn)) :
    (v.fixedTowerCorrection K L hLK σn s φ hφσn
      τ hτσn uBar uBarᵢ).1 =
        (v.frobeniusFixedFieldUnitAction K L hLK σn
            φ hφσn uBar).1 -
          uBar.1 -
          ∑ i ∈ s,
            ((v.frobeniusFixedFieldUnitAction K L hLK σn
                (τ i) (hτσn i) (uBarᵢ i)).1 - (uBarᵢ i).1) := by
  apply Subtype.ext
  simp [fixedTowerCorrection,
    ValuationData.frobeniusFixedFieldUnitAction]

/-- **Applying the lower norm to the correction term gives zero** — the
norm calculation immediately before the use of `Ĥ⁻¹ = 0`
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FixedTowerUnitCorrection.lean:97`). -/
theorem fixedTowerCorrection_relativeNorm_eq_zero
    (v : ValuationData D A) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ σn : D.FrobeniusElements K L hLK)
    (hTS : (D.frobeniusFixedField K L hLK σn).toSubgroup ≤
      (D.frobeniusFixedField K L hLK σ).toSubgroup)
    [Finite ((D.frobeniusFixedField K L hLK σ).toSubgroup ⧸
      (D.frobeniusFixedField K L hLK σn).toSubgroup.subgroupOf
        (D.frobeniusFixedField K L hLK σ).toSubgroup)]
    [Finite ((baseField G).toSubgroup ⧸
      (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
        (baseField G).toSubgroup)]
    [Finite ((baseField G).toSubgroup ⧸
      (D.frobeniusFixedField K L hLK σn).toSubgroup.subgroupOf
        (baseField G).toSubgroup)]
    {ι : Type v} (s : Finset ι)
    (φ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hφσ : φ * σ.1 = σ.1 * φ)
    (hφσn : φ * σn.1 = σn.1 * φ)
    (τ : ι → K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hτσ : ∀ i, τ i * σ.1 = σ.1 * τ i)
    (hτσn : ∀ i, τ i * σn.1 = σn.1 * τ i)
    (u :
      v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σ))
    (uᵢ : ι →
      v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σ))
    (uBar :
      v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σn))
    (uBarᵢ : ι →
      v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σn))
    (huBar : relativeNorm A (D.frobeniusFixedField K L hLK σ)
      (D.frobeniusFixedField K L hLK σn) hTS uBar.1 = u.1)
    (huBarᵢ : ∀ i,
      relativeNorm A (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField K L hLK σn) hTS
          (uBarᵢ i).1 = (uᵢ i).1)
    (hstar :
      A.ρ (Quotient.out φ).1 u.1.1 - u.1.1 =
        ∑ i ∈ s,
          (A.ρ (Quotient.out (τ i)).1 (uᵢ i).1.1 - (uᵢ i).1.1)) :
    relativeNorm A (D.frobeniusFixedField K L hLK σ)
      (D.frobeniusFixedField K L hLK σn) hTS
        (v.fixedTowerCorrection K L hLK σn s φ hφσn
          τ hτσn uBar uBarᵢ).1 = 0 := by
  dsimp only [DegreeData.frobeniusFixedAbstractField] at *
  let u' : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ) :=
    ⟨u.1.1, u.1.2⟩
  let uᵢ' (i : ι) : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ) :=
    ⟨(uᵢ i).1.1, (uᵢ i).1.2⟩
  let uBar' : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σn) :=
    ⟨uBar.1.1, uBar.1.2⟩
  let uBarᵢ' (i : ι) : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σn) :=
    ⟨(uBarᵢ i).1.1, (uBarᵢ i).1.2⟩
  have hsumBar (f : ι →
      v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σn)) :
      ((∑ i ∈ s, f i).1.1 : A.V) = ∑ i ∈ s, (f i).1.1 := by
    calc
      ((∑ i ∈ s, f i).1.1 : A.V) =
          (ambientFixedAddSubgroup A
            (D.frobeniusFixedField K L hLK σn)).subtype
              (∑ i ∈ s, (v.unitAddSubgroup
                (D.frobeniusFixedAbstractField K L hLK σn)).subtype
                  (f i)) := by
        exact congrArg (ambientFixedAddSubgroup A
          (D.frobeniusFixedField K L hLK σn)).subtype
          (map_sum (v.unitAddSubgroup
            (D.frobeniusFixedAbstractField K L hLK σn)).subtype f s)
      _ = _ := map_sum
        (ambientFixedAddSubgroup A
          (D.frobeniusFixedField K L hLK σn)).subtype
        (fun i => (v.unitAddSubgroup
          (D.frobeniusFixedAbstractField K L hLK σn)).subtype (f i)) s
  have hsumBar' (f : ι → ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σn)) :
      ((∑ i ∈ s, f i).1 : A.V) = ∑ i ∈ s, (f i).1 :=
    map_sum (ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σn)).subtype f s
  have hφVal :
      ((D.frobeniusFixedFieldAction A K L hLK σn φ hφσn uBar').1 :
          A.V) =
        A.ρ (Quotient.out φ).1 uBar.1.1 := by
    simp [uBar']
  have hτVal (i : ι) :
      ((D.frobeniusFixedFieldAction A K L hLK σn
        (τ i) (hτσn i) (uBarᵢ' i)).1 : A.V) =
        A.ρ (Quotient.out (τ i)).1 (uBarᵢ i).1.1 := by
    simp [uBarᵢ']
  have hunitφVal :
      ((v.frobeniusFixedFieldUnitAction K L hLK σn
        φ hφσn uBar).1.1 : A.V) =
        A.ρ (Quotient.out φ).1 uBar.1.1 := by
    change ((D.frobeniusFixedFieldAction A K L hLK σn
      φ hφσn uBar.1).1 : A.V) = _
    exact hφVal
  have hunitτVal (i : ι) :
      ((v.frobeniusFixedFieldUnitAction K L hLK σn
        (τ i) (hτσn i) (uBarᵢ i)).1.1 : A.V) =
        A.ρ (Quotient.out (τ i)).1 (uBarᵢ i).1.1 := by
    change ((D.frobeniusFixedFieldAction A K L hLK σn
      (τ i) (hτσn i) (uBarᵢ i).1).1 : A.V) = _
    exact hτVal i
  have hsubAmbient (x y : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σn)) :
      ((x - y).1 : A.V) = x.1 - y.1 :=
    map_sub (ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σn)).subtype x y
  have hsumAmbient (f : ι → ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σn)) :
      ((∑ i ∈ s, f i).1 : A.V) = ∑ i ∈ s, (f i).1 :=
    map_sum (ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σn)).subtype f s
  have hcorrection :
      (v.fixedTowerCorrection K L hLK σn s φ hφσn
          τ hτσn uBar uBarᵢ).1 =
        D.frobeniusFixedFieldAction A K L hLK σn
            φ hφσn uBar' -
          uBar' -
          ∑ i ∈ s,
            (D.frobeniusFixedFieldAction A K L hLK σn
                (τ i) (hτσn i) (uBarᵢ' i) - uBarᵢ' i) := by
    rw [v.fixedTowerCorrection_coe
      K L hLK σn s φ hφσn τ hτσn uBar uBarᵢ]
    rfl
  rw [hcorrection]
  simp only [map_sub, map_sum]
  have hφEquiv :
      relativeNorm A (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField K L hLK σn) hTS
          (D.frobeniusFixedFieldAction A K L hLK σn
            φ hφσn uBar') =
        D.frobeniusFixedFieldAction A K L hLK σ
          φ hφσ
            (relativeNorm A (D.frobeniusFixedField K L hLK σ)
              (D.frobeniusFixedField K L hLK σn) hTS uBar') := by
    exact D.relativeNorm_frobeniusFixedFieldAction
      A K L hLK σ σn hTS φ hφσ hφσn uBar'
  rw [hφEquiv]
  have hτEquiv (i : ι) :
      relativeNorm A (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField K L hLK σn) hTS
          (D.frobeniusFixedFieldAction A K L hLK σn
            (τ i) (hτσn i) (uBarᵢ' i)) =
        D.frobeniusFixedFieldAction A K L hLK σ
          (τ i) (hτσ i)
            (relativeNorm A (D.frobeniusFixedField K L hLK σ)
              (D.frobeniusFixedField K L hLK σn) hTS (uBarᵢ' i)) := by
    exact D.relativeNorm_frobeniusFixedFieldAction
      A K L hLK σ σn hTS (τ i) (hτσ i) (hτσn i) (uBarᵢ' i)
  simp_rw [hτEquiv]
  have huBar' :
      relativeNorm A (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField K L hLK σn) hTS uBar' = u' := by
    exact huBar
  have huBarᵢ' (i : ι) :
      relativeNorm A (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField K L hLK σn) hTS (uBarᵢ' i) =
        uᵢ' i := by
    exact huBarᵢ i
  rw [huBar']
  simp_rw [huBarᵢ']
  apply Subtype.ext
  have hsum : ((∑ i ∈ s, uᵢ i).1.1 : A.V) =
      ∑ i ∈ s, (uᵢ i).1.1 := by
    calc
      ((∑ i ∈ s, uᵢ i).1.1 : A.V) =
          (ambientFixedAddSubgroup A
            (D.frobeniusFixedField K L hLK σ)).subtype
              (∑ i ∈ s, (v.unitAddSubgroup
                (D.frobeniusFixedAbstractField K L hLK σ)).subtype
                  (uᵢ i)) := by
        exact congrArg (ambientFixedAddSubgroup A
          (D.frobeniusFixedField K L hLK σ)).subtype
          (map_sum (v.unitAddSubgroup
            (D.frobeniusFixedAbstractField K L hLK σ)).subtype uᵢ s)
      _ = _ := map_sum
        (ambientFixedAddSubgroup A
          (D.frobeniusFixedField K L hLK σ)).subtype
        (fun i => (v.unitAddSubgroup
          (D.frobeniusFixedAbstractField K L hLK σ)).subtype (uᵢ i)) s
  have hsum' (f : ι → ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)) :
      ((∑ i ∈ s, f i).1 : A.V) = ∑ i ∈ s, (f i).1 :=
    map_sum (ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)).subtype f s
  simpa [u', uᵢ', D.frobeniusFixedFieldAction_coe,
    hsum, hsum', Finset.sum_sub_distrib] using
    sub_eq_zero.mpr hstar

end ValuationData

end

end Atlas.Knowledge
