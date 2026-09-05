import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteAbstractFieldExtension
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.FrobeniusClosureCommutation
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.FrobeniusFixedFieldAction
import Atlas.Knowledge.FrobeniusFixedFieldTower
import Atlas.Knowledge.NormalizedValuationLaws
import Atlas.Knowledge.PrimeElement
import Atlas.Knowledge.ProfiniteInteger
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.RelativeNormLaws
import Atlas.Knowledge.ValuationData

/-!
# Finite-field unit maps

Valuation invariance on Frobenius fixed fields, and the maps it buys on
the finite unit groups: the stabilizing action restricted to units, the
inclusion of units along any finite extension, and the relative norm
restricted to units — the pieces the descent applies once all finitely
many terms of `(*)` sit in one finite Galois field (#104).

## Main definitions

* `ValuationData.frobeniusFixedFieldUnitAction` — the stabilizing action
  on the unit group of a Frobenius fixed field.
* `ValuationData.finiteUnitInclusion` — units into a finite extension.
* `ValuationData.finiteUnitNorm` — the relative norm on units.

## Main statements

* `ValuationData.valuationAt_frobeniusFixedFieldAction` — a stabilizing
  quotient element preserves the normalized valuation; proved.
* `ValuationData.fixedFieldInclusion_mem_unitAddSubgroup` — units stay
  units after inclusion; proved.
* `ValuationData.relativeNorm_mem_unitAddSubgroup` — the norm of a unit
  is a unit; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling —
which frees the containments the two transport instances bind, so they go,
as do the six ambient separation binders #140's slimming left dead —
`ZHat` is `ProfiniteInteger`, `zHatMulNat_injective` with its positivity
is `ProfiniteInteger.nsmul_left_injective` with `.pos.ne'`,
`FiniteResidueAbstractField` sits at the layer's top level, and the
ambient group is `Type u` since the #104 hoist, which flipped the file as
one move with the `Atlas.Knowledge.DegreeData.frobeniusFixedFieldAction`
it leans on; the source's no-op `open`s are dropped, and the `by exact`
inside the norm-inclusion rewrite is flattened to `from`.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteAbstractField

/-- Normality transports across the canonical residue-field enrichment
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteFieldUnitMaps.lean:30`]
[Yamaguchi2026]). -/
instance toFiniteResidueAbstractField_extensionNormal
    (K : FiniteAbstractField G) (D : DegreeData G) (L : ClosedSubgroup G)
    [hnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    (L.toSubgroup.subgroupOf
      (K.toFiniteResidueAbstractField D).field.toSubgroup).Normal := by
  change (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal
  exact hnormal

/-- Relative finiteness transports across the canonical residue-field
enrichment ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteFieldUnitMaps.lean:39`]
[Yamaguchi2026]). -/
instance toFiniteResidueAbstractField_extensionFinite
    (K : FiniteAbstractField G) (D : DegreeData G) (L : ClosedSubgroup G)
    [hfinite : Finite
      (K.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf K.field.toSubgroup)] :
    Finite ((K.toFiniteResidueAbstractField D).field.toSubgroup ⧸
      L.toSubgroup.subgroupOf
        (K.toFiniteResidueAbstractField D).field.toSubgroup) := by
  change Finite
    (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)
  exact hfinite

end FiniteAbstractField

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/- Transport along an equality of finite fields keeps the ambient
coefficient ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteFieldUnitMaps.lean:56`]
[Yamaguchi2026]). -/
private theorem ambientFixedAddSubgroup_transport_coe
    (K L : FiniteAbstractField G) (h : K = L)
    (a : ambientFixedAddSubgroup A K.field) :
    (((h ▸ a : ambientFixedAddSubgroup A L.field) : A.V)) = a.1 := by
  cases h
  rfl

/- The valuation is transport-invariant ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteFieldUnitMaps.lean:63`]
[Yamaguchi2026]). -/
private theorem valuationAt_transport
    (v : ValuationData D A) (K L : FiniteAbstractField G) (h : K = L)
    (a : ambientFixedAddSubgroup A K.field) :
    v.valuationAt L (h ▸ a) = v.valuationAt K a := by
  cases h
  rfl

/-- **A quotient element stabilizing a Frobenius fixed field preserves its normalized valuation**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteFieldUnitMaps.lean:72`]
[Yamaguchi2026]). -/
theorem valuationAt_frobeniusFixedFieldAction
    (v : ValuationData D A) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q)
    [Finite ((baseField G).toSubgroup ⧸
      (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
        (baseField G).toSubgroup)]
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)) :
    v.valuationAt (D.frobeniusFixedAbstractField K L hLK σ)
        (D.frobeniusFixedFieldAction A K L hLK σ q hq a) =
      v.valuationAt (D.frobeniusFixedAbstractField K L hLK σ) a := by
  let TF := D.frobeniusFixedAbstractField K L hLK σ
  let k : K.field.toSubgroup := Quotient.out q
  let hstable : conjugateClosedSubgroup TF.field k.1⁻¹ = TF.field :=
    D.conjugate_frobeniusFixedField_eq_of_commutes K L hLK σ q hq
  let CF := TF.conjugate k.1⁻¹
  let C := CF.field
  have hconj := v.normalizedValuation_conjugate TF k.1⁻¹ a
  let bC : ambientFixedAddSubgroup A C :=
    conjugateFixedElement A TF.field k.1⁻¹ a
  have hCFTF : CF = TF := by
    exact FiniteAbstractField.eq_of_field_eq CF TF hstable
  let bT : ambientFixedAddSubgroup A TF.field := hCFTF ▸ bC
  have hbTcoe : bT.1 = bC.1 := by
    exact ambientFixedAddSubgroup_transport_coe CF TF hCFTF bC
  have hvaluationTransport :
      v.valuationAt TF bT = v.valuationAt CF bC := by
    exact v.valuationAt_transport CF TF hCFTF bC
  have hbT : bT = D.frobeniusFixedFieldAction
      A K L hLK σ q hq a := by
    apply Subtype.ext
    change bT.1 =
      (D.frobeniusFixedFieldAction A K L hLK σ q hq a).1
    calc
      bT.1 = bC.1 := hbTcoe
      _ = A.ρ k.1 a.1 := by simp [bC, k]
      _ = (D.frobeniusFixedFieldAction A K L hLK σ q hq a).1 := by rfl
  calc
    v.valuationAt TF
        (D.frobeniusFixedFieldAction A K L hLK σ q hq a) =
        v.valuationAt TF bT := congrArg (v.valuationAt TF) hbT.symm
    _ = v.valuationAt CF bC := hvaluationTransport
    _ = v.valuationAt TF a := by simpa [CF, C, bC] using hconj

/-- **The stabilizing action restricted to the unit group of a Frobenius fixed field**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteFieldUnitMaps.lean:124`]
[Yamaguchi2026]). -/
noncomputable def frobeniusFixedFieldUnitAction
    (v : ValuationData D A) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q)
    [Finite ((baseField G).toSubgroup ⧸
      (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
        (baseField G).toSubgroup)] :
    v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σ) →+
      v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σ) where
  toFun u := ⟨D.frobeniusFixedFieldAction A K L hLK σ q hq u.1, by
    rw [v.mem_unitAddSubgroup_iff,
      v.valuationAt_frobeniusFixedFieldAction K L hLK σ q hq u.1]
    exact u.2⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' _ _ := by apply Subtype.ext; exact map_add _ _ _

/-- **Units stay units after inclusion into any finite extension** — the
construction uses this silently when all finitely many terms of `(*)`
are placed in one finite Galois field ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteFieldUnitMaps.lean:150`]
[Yamaguchi2026]). -/
theorem fixedFieldInclusion_mem_unitAddSubgroup
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (u : v.unitAddSubgroup E.base) :
    fixedFieldInclusion A E.base.field E.field.field E.below u.1 ∈
      v.unitAddSubgroup E.field := by
  rw [v.mem_unitAddSubgroup_iff]
  apply Subtype.ext
  let ER := E.toFiniteResidueAbstractExtension D
  apply ProfiniteInteger.nsmul_left_injective ER.residueDegree.pos.ne'
  change (ER.residueDegree : ℕ) •
      ((v.valuationAt E.field
        (fixedFieldInclusion A E.base.field E.field.field E.below u.1) :
        v.valueGroup) : ProfiniteInteger) =
    (ER.residueDegree : ℕ) •
      ((0 : v.valueGroup) : ProfiniteInteger)
  have htower :=
    v.normalizedValuation_tower E
      (fixedFieldInclusion A E.base.field E.field.field E.below u.1)
  have htower' :
      (ER.residueDegree : ℕ) •
          ((v.valuationAt E.field
            (fixedFieldInclusion A E.base.field E.field.field
              E.below u.1) :
            v.valueGroup) : ProfiniteInteger) =
        ((v.valuationAt E.base
          (relativeNorm A E.base.field E.field.field E.below
            (fixedFieldInclusion A E.base.field E.field.field
              E.below u.1)) :
              v.valueGroup) : ProfiniteInteger) := by
    simpa [ER] using htower
  rw [htower']
  rw [show relativeNorm A E.base.field E.field.field E.below
      (fixedFieldInclusion A E.base.field E.field.field E.below u.1) =
        (E.degree : ℕ) • u.1 from
    relativeNorm_fixedFieldInclusion A E.toFiniteAbstractExtension u.1]
  rw [map_nsmul]
  have hu : v.valuationAt E.base u.1 = 0 := u.2
  simp [hu]

/-- **Inclusion of units along an arbitrary finite extension**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteFieldUnitMaps.lean:187`]
[Yamaguchi2026]). -/
def finiteUnitInclusion
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G) :
    v.unitAddSubgroup E.base →+ v.unitAddSubgroup E.field where
  toFun u := ⟨fixedFieldInclusion A E.base.field E.field.field
      E.below u.1,
    v.fixedFieldInclusion_mem_unitAddSubgroup E u⟩
  map_zero' := by apply Subtype.ext; rfl
  map_add' _ _ := by apply Subtype.ext; rfl

/-- Transporting a finite-unit inclusion along equality of its target
field does not change its ambient coefficient ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteFieldUnitMaps.lean:197`]
[Yamaguchi2026]). -/
theorem finiteUnitInclusion_transport_coe
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (F : FiniteAbstractField G) (h : E.field = F)
    (u : v.unitAddSubgroup E.base) :
    (((h ▸ v.finiteUnitInclusion E u : v.unitAddSubgroup F).1 :
        ambientFixedAddSubgroup A F.field) : A.V) = u.1.1 := by
  cases h
  rfl

/-- **The norm of a unit through an arbitrary finite extension is a unit**
— the valuation-theoretic step when a finite Galois refinement is pushed
back down to the prescribed intermediate field ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteFieldUnitMaps.lean:209`]
[Yamaguchi2026]). -/
theorem relativeNorm_mem_unitAddSubgroup
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (u : v.unitAddSubgroup E.field) :
    relativeNorm A E.base.field E.field.field E.below u.1 ∈
      v.unitAddSubgroup E.base := by
  rw [v.mem_unitAddSubgroup_iff]
  apply Subtype.ext
  have h := v.normalizedValuation_tower E u.1
  let ER := E.toFiniteResidueAbstractExtension D
  change (ER.residueDegree : ℕ) •
      ((v.valuationAt E.field u.1 : v.valueGroup) : ProfiniteInteger) =
    ((v.valuationAt E.base
      (relativeNorm A E.base.field E.field.field E.below u.1) :
        v.valueGroup) : ProfiniteInteger) at h
  have hu : v.valuationAt E.field u.1 = 0 := u.2
  simpa [hu] using h.symm

/-- **The relative norm restricted to the finite unit groups**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteFieldUnitMaps.lean:227`]
[Yamaguchi2026]). -/
def finiteUnitNorm
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G) :
    v.unitAddSubgroup E.field →+ v.unitAddSubgroup E.base where
  toFun u := ⟨relativeNorm A E.base.field E.field.field E.below u.1,
    v.relativeNorm_mem_unitAddSubgroup E u⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' _ _ := by apply Subtype.ext; exact map_add _ _ _

end ValuationData

end

end Atlas.Knowledge
