import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusExponent
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.FrobeniusNormCosetDecomposition
import Atlas.Knowledge.FrobeniusQuotientAction
import Atlas.Knowledge.InertiaQuotientDegreeKernel
import Atlas.Knowledge.MaximalUnramifiedField
import Atlas.Knowledge.RelativeNorm

/-!
# Frobenius norm identities

The Frobenius norm-identity lemma: for a degree-one lift `φ`, a lift `σ`
of exponent `n`, and the fixed field `Σ` of `σ`, the three actual norm
expressions agree —
`N_{Σ|K}(a) = (N_{L̃|K̃} ∘ φ_n)(a) = (φ_n ∘ N_{L̃|K̃})(a)`. The first
identity sums the coset action over the `φ^i·τ` enumeration of `G_K/G_Σ`;
the second is the equivariance of the norm under the quotient action,
summed over the powers (#104).

## Main statements

* `DegreeData.frobeniusNormIdentity_norm_eq_powerSum_norm` — the first
  identity, in the order `φ_n ∘ N`; proved.
* `DegreeData.frobeniusNormIdentity_norm_powerSum_eq_powerSum_norm` — the
  norm and the power sum commute; proved.
* `DegreeData.frobeniusNormIdentities` — the two identities packaged as
  the norm-identity lemma; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling, with
the finiteness of `L̃ | K̃` in #138's containment-free form. The source
pins the acting group to the shared `Rep` universe boundary; this
Mathlib's `Rep` is polymorphic, so the identities generalize to any
universe, as across the arc. The source's `Fintype`-in-type binder on the
private expansion lemma becomes `Finite`, at the standard linter set's own
suggestion.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/- The coset action over the composite enumeration factors through the
inclusion into the maximal unramified extension (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:897`). -/
private theorem relativeCosetAction_frobeniusNormIdentityCosetEquiv
    (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ))
    (r : (D.maximalUnramifiedField K.field).toSubgroup ⧸
      (D.maximalUnramifiedField L).toSubgroup.subgroupOf
        (D.maximalUnramifiedField K.field).toSubgroup)
    (i : Fin (D.frobeniusExponent K L hLK σ)) :
    relativeCosetAction A K.field (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField_le K L hLK σ) a
        (D.frobeniusNormIdentityCosetEquiv K L hLK φ σ hφ (r, i)) =
      A.ρ (Quotient.out (φ.1 ^ i.1)).1
        (relativeCosetAction A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)
          (fixedFieldInclusion A
            (D.frobeniusFixedField K L hLK σ)
            (D.maximalUnramifiedField L)
            (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a) r) := by
  let kφ : K.field.toSubgroup := Quotient.out (φ.1 ^ i.1)
  let kI : (D.maximalUnramifiedField K.field).toSubgroup :=
    Quotient.out r
  let kIK : K.field.toSubgroup := ⟨kI.1, kI.2.1⟩
  change relativeCosetAction A K.field
      (D.frobeniusFixedField K L hLK σ)
      (D.frobeniusFixedField_le K L hLK σ) a
      (QuotientGroup.mk (kφ * kIK)) = _
  rw [relativeCosetAction_mk]
  have hr : r = QuotientGroup.mk kI := (Quotient.out_eq' r).symm
  rw [hr, relativeCosetAction_mk, fixedFieldInclusion_coe]
  change A.ρ (kφ.1 * kI.1) a.1 = A.ρ kφ.1 (A.ρ kI.1 a.1)
  rw [map_mul]
  rfl

/- The quotient action of a Frobenius power on the included norm expands
into the coset sum (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:940`). -/
private theorem frobeniusQuotientAction_relativeNorm (D : DegreeData G)
    (A : Rep ℤ G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hInertiaFinite : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        (D.maximalUnramifiedField L).toSubgroup.subgroupOf
          (D.maximalUnramifiedField K.field).toSubgroup)]
    (φ : D.FrobeniusElements K L hLK)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (i : ℕ) :
    ((D.frobeniusQuotientAction A K.field L hLK (φ.1 ^ i)
      (fixedFieldInclusion A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_mono hLK)
        (relativeNorm A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK) a)) :
        ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) : A.V) =
      (@Finset.univ
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          (D.maximalUnramifiedField L).toSubgroup.subgroupOf
            (D.maximalUnramifiedField K.field).toSubgroup)
        (Fintype.ofFinite _)).sum (fun r =>
          A.ρ (Quotient.out (φ.1 ^ i)).1
            (relativeCosetAction A (D.maximalUnramifiedField K.field)
              (D.maximalUnramifiedField L)
              (D.maximalUnramifiedField_mono hLK) a r)) := by
  let kφ : K.field.toSubgroup := Quotient.out (φ.1 ^ i)
  have hkφ : φ.1 ^ i = QuotientGroup.mk kφ :=
    (Quotient.out_eq' (φ.1 ^ i)).symm
  let b := fixedFieldInclusion A (D.maximalUnramifiedField K.field)
    (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
    (relativeNorm A (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) a)
  calc
    ((D.frobeniusQuotientAction A K.field L hLK (φ.1 ^ i) b :
        ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) : A.V) =
      (D.frobeniusQuotientAction A K.field L hLK
        (QuotientGroup.mk kφ) b : A.V) := by
          exact congrArg
            (fun q =>
              (D.frobeniusQuotientAction A K.field L hLK q b : A.V)) hkφ
    _ = A.ρ kφ.1 b.1 := rfl
    _ = A.ρ kφ.1
        ((relativeNorm A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK) a :
            ambientFixedAddSubgroup A
              (D.maximalUnramifiedField K.field)) : A.V) := by
          rw [fixedFieldInclusion_coe]
    _ = A.ρ kφ.1
        (relativeNormValue A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK) a) := by
          rw [relativeNorm_apply_coe]
    _ = A.ρ kφ.1
        ((@Finset.univ
          ((D.maximalUnramifiedField K.field).toSubgroup ⧸
            (D.maximalUnramifiedField L).toSubgroup.subgroupOf
              (D.maximalUnramifiedField K.field).toSubgroup)
          (Fintype.ofFinite _)).sum (fun r =>
            relativeCosetAction A (D.maximalUnramifiedField K.field)
              (D.maximalUnramifiedField L)
              (D.maximalUnramifiedField_mono hLK) a r)) := by
          rfl
    _ = (@Finset.univ
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          (D.maximalUnramifiedField L).toSubgroup.subgroupOf
            (D.maximalUnramifiedField K.field).toSubgroup)
        (Fintype.ofFinite _)).sum (fun r => A.ρ kφ.1
          (relativeCosetAction A (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK) a r)) := by
          rw [map_sum]

/-- **The first norm identity, in the order `φ_n ∘ N`** (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:1020`). -/
theorem frobeniusNormIdentity_norm_eq_powerSum_norm (D : DegreeData G)
    (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)) :
    letI : Finite
        (K.field.toSubgroup ⧸
          (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
            K.field.toSubgroup) :=
      D.frobeniusFixedField_finite K L hLK σ
    letI : Finite
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          (D.maximalUnramifiedField L).toSubgroup.subgroupOf
            (D.maximalUnramifiedField K.field).toSubgroup) :=
      D.maximalUnramifiedExtension_finite K.field L
    ((relativeNorm A K.field (D.frobeniusFixedField K L hLK σ)
      (D.frobeniusFixedField_le K L hLK σ) a :
        ambientFixedAddSubgroup A K.field) : A.V) =
      ((D.frobeniusPowerSum A K.field L hLK φ.1
        (D.frobeniusExponent K L hLK σ)
        (fixedFieldInclusion A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)
          (relativeNorm A (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)
            (fixedFieldInclusion A
              (D.frobeniusFixedField K L hLK σ)
              (D.maximalUnramifiedField L)
              (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a))) :
          ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
        A.V) := by
  letI : Finite
      (K.field.toSubgroup ⧸
        (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
          K.field.toSubgroup) :=
    D.frobeniusFixedField_finite K L hLK σ
  letI : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        (D.maximalUnramifiedField L).toSubgroup.subgroupOf
          (D.maximalUnramifiedField K.field).toSubgroup) :=
    D.maximalUnramifiedExtension_finite K.field L
  let R := (D.maximalUnramifiedField K.field).toSubgroup ⧸
    (D.maximalUnramifiedField L).toSubgroup.subgroupOf
      (D.maximalUnramifiedField K.field).toSubgroup
  let n := D.frobeniusExponent K L hLK σ
  let e := D.frobeniusNormIdentityCosetEquiv K L hLK φ σ hφ
  let aI := fixedFieldInclusion A
    (D.frobeniusFixedField K L hLK σ)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a
  let b := fixedFieldInclusion A (D.maximalUnramifiedField K.field)
    (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
    (relativeNorm A (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L)
      (D.maximalUnramifiedField_mono hLK) aI)
  letI := Fintype.ofFinite R
  letI := Fintype.ofFinite
    (K.field.toSubgroup ⧸
      (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
        K.field.toSubgroup)
  rw [relativeNorm_apply_coe, relativeNormValue,
    D.frobeniusPowerSum_coe]
  calc
    ∑ q, relativeCosetAction A K.field
        (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField_le K L hLK σ) a q =
      ∑ p : R × Fin n,
        relativeCosetAction A K.field
          (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField_le K L hLK σ) a (e p) :=
      (e.sum_comp _).symm
    _ = ∑ p : R × Fin n,
        A.ρ (Quotient.out (φ.1 ^ p.2.1)).1
          (relativeCosetAction A (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)
            aI p.1) := by
      apply Finset.sum_congr rfl
      intro p _
      exact D.relativeCosetAction_frobeniusNormIdentityCosetEquiv
        A K L hLK φ σ hφ a p.1 p.2
    _ = ∑ i : Fin n, ∑ r : R,
        A.ρ (Quotient.out (φ.1 ^ i.1)).1
          (relativeCosetAction A (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)
            aI r) := by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_comm
    _ = ∑ i : Fin n,
        (D.frobeniusQuotientAction A K.field L hLK (φ.1 ^ i.1) b :
          A.V) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (D.frobeniusQuotientAction_relativeNorm
        A K L hLK φ aI i.1).symm

/-- **The norm and the power sum commute**:
`N_{L̃|K̃} ∘ φ_n = φ_n ∘ N_{L̃|K̃}` (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:1125`). -/
theorem frobeniusNormIdentity_norm_powerSum_eq_powerSum_norm
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (φ : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (n : ℕ)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    letI : Finite
        ((D.maximalUnramifiedField K).toSubgroup ⧸
          (D.maximalUnramifiedField L).toSubgroup.subgroupOf
            (D.maximalUnramifiedField K).toSubgroup) :=
      D.maximalUnramifiedExtension_finite K L
    ((relativeNorm A (D.maximalUnramifiedField K)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
      (D.frobeniusPowerSum A K L hLK φ n a) :
        ambientFixedAddSubgroup A (D.maximalUnramifiedField K)) : A.V) =
      ((D.frobeniusPowerSum A K L hLK φ n
        (fixedFieldInclusion A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)
          (relativeNorm A (D.maximalUnramifiedField K)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)
            a)) : ambientFixedAddSubgroup A
              (D.maximalUnramifiedField L)) : A.V) := by
  letI : Finite
      ((D.maximalUnramifiedField K).toSubgroup ⧸
        (D.maximalUnramifiedField L).toSubgroup.subgroupOf
          (D.maximalUnramifiedField K).toSubgroup) :=
    D.maximalUnramifiedExtension_finite K L
  change
    ((relativeNorm A (D.maximalUnramifiedField K)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK))
      (∑ i : Fin n,
        D.frobeniusQuotientAction A K L hLK (φ ^ i.1) a)).1 =
      (∑ i : Fin n, D.frobeniusQuotientAction A K L hLK (φ ^ i.1)
        (fixedFieldInclusion A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)
          (relativeNorm A (D.maximalUnramifiedField K)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)
            a))).1
  simp only [map_sum]
  change (ambientFixedAddSubgroup A
      (D.maximalUnramifiedField K)).subtype
      (∑ i : Fin n, relativeNorm A (D.maximalUnramifiedField K)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
        (D.frobeniusQuotientAction A K L hLK (φ ^ i.1) a)) =
    (ambientFixedAddSubgroup A
      (D.maximalUnramifiedField L)).subtype
      (∑ i : Fin n, D.frobeniusQuotientAction A K L hLK (φ ^ i.1)
        (fixedFieldInclusion A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)
          (relativeNorm A (D.maximalUnramifiedField K)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)
            a)))
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact D.relativeNorm_frobeniusQuotientAction A K L hLK (φ ^ i.1) a

/-- **The Frobenius norm-identity lemma**: for `d_K(φ) = 1`, `d_K(σ) = n`,
and the fixed field `Σ` of `σ`, the three actual norm expressions agree —
`N_{Σ|K}(a) = (N_{L̃|K̃} ∘ φ_n)(a) = (φ_n ∘ N_{L̃|K̃})(a)`
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:1189`). -/
theorem frobeniusNormIdentities (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)) :
    letI : Finite
        (K.field.toSubgroup ⧸
          (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
            K.field.toSubgroup) :=
      D.frobeniusFixedField_finite K L hLK σ
    letI : Finite
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          (D.maximalUnramifiedField L).toSubgroup.subgroupOf
            (D.maximalUnramifiedField K.field).toSubgroup) :=
      D.maximalUnramifiedExtension_finite K.field L
    let n := D.frobeniusExponent K L hLK σ
    let aI := fixedFieldInclusion A
      (D.frobeniusFixedField K L hLK σ)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a
    let b := fixedFieldInclusion A (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
      (relativeNorm A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_mono hLK) aI)
    let φnAI := D.frobeniusPowerSum A K.field L hLK φ.1 n aI
    (((relativeNorm A K.field (D.frobeniusFixedField K L hLK σ)
      (D.frobeniusFixedField_le K L hLK σ) a :
        ambientFixedAddSubgroup A K.field) : A.V) =
      ((relativeNorm A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_mono hLK)
        φnAI : ambientFixedAddSubgroup A
          (D.maximalUnramifiedField K.field)) : A.V)) ∧
    (((relativeNorm A (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L)
      (D.maximalUnramifiedField_mono hLK)
      φnAI : ambientFixedAddSubgroup A
        (D.maximalUnramifiedField K.field)) : A.V) =
      ((D.frobeniusPowerSum A K.field L hLK φ.1 n b :
        ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
        A.V)) := by
  letI : Finite
      (K.field.toSubgroup ⧸
        (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
          K.field.toSubgroup) :=
    D.frobeniusFixedField_finite K L hLK σ
  letI : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        (D.maximalUnramifiedField L).toSubgroup.subgroupOf
          (D.maximalUnramifiedField K.field).toSubgroup) :=
    D.maximalUnramifiedExtension_finite K.field L
  let n := D.frobeniusExponent K L hLK σ
  let aI := fixedFieldInclusion A
    (D.frobeniusFixedField K L hLK σ)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a
  let b := fixedFieldInclusion A (D.maximalUnramifiedField K.field)
    (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
    (relativeNorm A (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L)
      (D.maximalUnramifiedField_mono hLK) aI)
  let φnAI := D.frobeniusPowerSum A K.field L hLK φ.1 n aI
  have hFirst :
      ((relativeNorm A K.field (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField_le K L hLK σ) a :
          ambientFixedAddSubgroup A K.field) : A.V) =
        ((D.frobeniusPowerSum A K.field L hLK φ.1 n b :
          ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
          A.V) := by
    simpa [n, aI, b] using
      D.frobeniusNormIdentity_norm_eq_powerSum_norm A K L hLK φ σ hφ a
  have hCommute :
      ((relativeNorm A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_mono hLK)
        φnAI : ambientFixedAddSubgroup A
          (D.maximalUnramifiedField K.field)) : A.V) =
        ((D.frobeniusPowerSum A K.field L hLK φ.1 n b :
          ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
          A.V) := by
    simpa [n, aI, b, φnAI] using
      D.frobeniusNormIdentity_norm_powerSum_eq_powerSum_norm
        A K.field L hLK φ.1 n aI
  exact ⟨hFirst.trans hCommute.symm, hCommute⟩

end DegreeData

end

end Atlas.Knowledge
