import Mathlib
import Atlas.Knowledge.ChosenDegreeOneFrobenius
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.FiniteIntermediateCompositum
import Atlas.Knowledge.FiniteIntermediateFieldRefinement
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FiniteResidueAbstractField
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusExponent
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.GaloisSubextension
import Atlas.Knowledge.MaximalUnramifiedField
import Atlas.Knowledge.NormalizedDegree
import Atlas.Knowledge.ProfiniteInteger
import Atlas.Knowledge.ReciprocityMap

/-!
# totally ramified Frobenius lift

Degree-one Frobenius lifts for totally ramified extensions, and the
finite auxiliary Galois extension of the totally ramified reciprocity
argument: every automorphism of a totally ramified Galois extension has
a Frobenius lift of exponent one — the element `σ̃ = σφ_L` — chosen
here for the plain and the finite Galois bundles alike, and the chosen
finite Galois extension `M / K` containing both `L` and the degree-one
Frobenius fixed field `Σ` inside the maximal unramified extension of
`L` (#104).

## Main definitions

* `DegreeData.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified` —
  the degree-one lift restricting to a chosen finite automorphism.
* `DegreeData.abstractReciprocityTotallyRamifiedFiniteGaloisExtension`
  — the auxiliary finite Galois extension `M / K`.

## Main statements

* `DegreeData.exists_degreeOneFrobeniusLiftOfTotallyRamified` — the
  lift exists; proved from total ramification.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
`ZHat` and `ZHatMul` are `ProfiniteInteger` and `ProfiniteIntegerMul`,
`proCIntegerOne_pow_nat_injective` is
`ProfiniteInteger.ofAdd_one_pow_injective`, and
`extensionSubgroup_maximalUnramifiedField_normal` is the layer's
`subgroupOf_maximalUnramifiedField_normal`. The ambient group is
`Type u` where the source pins `IntegralRepGroupType` — a pure
widening: nothing here mentions a representation, and every dependency
is already polymorphic. The auxiliary-extension family sheds the
source's `[T2Space G]` on all four declarations: the elaborated proofs
never consume it and it is not derivable from the kept instances, so
the ported statements are strictly more general — the separation
divergence is `frobeniusFixedIntermediateField`, which carries
`[T2Space G]` in the source and not in the layer's
`Atlas.Knowledge.ReciprocityMap` item. Everything else ports
token-for-token; the file is the source's
`TotallyRamifiedCase/FrobeniusLift.lean` whole.

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

/-- **Every automorphism of a totally ramified Galois extension has a
Frobenius lift of exponent one** (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusLift.lean:24`). -/
theorem exists_degreeOneFrobeniusLiftOfTotallyRamified
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : GaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    ∃ σ : D.FrobeniusElements K L.field L.below,
      D.frobeniusExponent K L.field L.below σ = 1 ∧
      L.extensionQuotientMulEquiv.symm
        (D.frobeniusRestriction K L.field L.below σ) = q := by
  let φ := D.chosenDegreeOneFrobeniusElement K L.field L.below
  let q₀ := D.frobeniusRestriction K L.field L.below φ
  let qRaw := L.extensionQuotientMulEquiv q
  obtain ⟨s, hs⟩ := QuotientGroup.mk'_surjective
    (L.field.toSubgroup.subgroupOf K.field.toSubgroup) (qRaw * q₀⁻¹)
  have hsDegree : D.degree s.1 ∈
      K.field.toSubgroup.map D.degree.toMonoidHom := ⟨s.1, s.2, rfl⟩
  have hImage :=
    (L.isTotallyRamified_iff_image_le D).1 hTot hsDegree
  obtain ⟨l, hlL, hlDegree⟩ := hImage
  let lL : L.field.toSubgroup := ⟨l, hlL⟩
  let lK : K.field.toSubgroup := Subgroup.inclusion L.below lL
  let i : K.field.toSubgroup := s * lK⁻¹
  let t : K.field.toSubgroup ⧸
      D.extensionInertiaWithin K.field L.field L.below :=
    QuotientGroup.mk i * φ.1
  have hiDegree : D.normalizedDegree K i = 1 := by
    change i ∈ (D.normalizedDegree K).toMonoidHom.ker
    rw [D.normalizedDegree_ker K]
    change D.degree i.1 = 1
    dsimp [i, lK, lL]
    rw [map_mul, map_inv]
    change D.degree s.1 * (D.degree l)⁻¹ = 1
    rw [← hlDegree]
    simp
  have htDegree : D.extensionNormalizedDegree K L.field L.below t =
      (Multiplicative.ofAdd (1 : ProfiniteInteger) :
        ProfiniteIntegerMul) ^ (1 : ℕ) := by
    change D.extensionNormalizedDegree K L.field L.below
        (QuotientGroup.mk i * φ.1) = _
    rw [map_mul, D.extensionNormalizedDegree_mk, hiDegree, one_mul]
    calc
      D.extensionNormalizedDegree K L.field L.below φ.1 =
          (Multiplicative.ofAdd (1 : ProfiniteInteger) :
              ProfiniteIntegerMul) ^
              D.frobeniusExponent K L.field L.below φ :=
        D.extensionNormalizedDegree_frobenius_eq_pow K L.field L.below φ
      _ = (Multiplicative.ofAdd (1 : ProfiniteInteger) :
          ProfiniteIntegerMul) ^ (1 : ℕ) := by
        rw [D.frobeniusExponent_chosenDegreeOneFrobeniusElement]
  let σ : D.FrobeniusElements K L.field L.below :=
    ⟨t, 1, Nat.one_pos, htDegree⟩
  have hσExponent : D.frobeniusExponent K L.field L.below σ = 1 := by
    apply ProfiniteInteger.ofAdd_one_pow_injective
    calc
      (Multiplicative.ofAdd (1 : ProfiniteInteger) :
            ProfiniteIntegerMul) ^
            D.frobeniusExponent K L.field L.below σ =
          D.extensionNormalizedDegree K L.field L.below σ.1 :=
        (D.extensionNormalizedDegree_frobenius_eq_pow
          K L.field L.below σ).symm
      _ = (Multiplicative.ofAdd (1 : ProfiniteInteger) :
          ProfiniteIntegerMul) ^ (1 : ℕ) :=
        htDegree
  refine ⟨σ, hσExponent, ?_⟩
  apply L.extensionQuotientMulEquiv.injective
  rw [MulEquiv.apply_symm_apply]
  change D.extensionRestriction K.field L.field L.below
      (QuotientGroup.mk i * φ.1) = qRaw
  rw [map_mul, D.extensionRestriction_mk]
  have hiRestriction :
      (QuotientGroup.mk i :
        K.field.toSubgroup ⧸
          L.field.toSubgroup.subgroupOf K.field.toSubgroup) =
        QuotientGroup.mk s := by
    dsimp [i]
    change (QuotientGroup.mk'
        (L.field.toSubgroup.subgroupOf K.field.toSubgroup))
        (s * lK⁻¹) =
      (QuotientGroup.mk'
        (L.field.toSubgroup.subgroupOf K.field.toSubgroup)) s
    rw [map_mul, map_inv]
    have hlOne :
        (QuotientGroup.mk'
          (L.field.toSubgroup.subgroupOf K.field.toSubgroup)) lK = 1 := by
      apply (QuotientGroup.eq_one_iff _).2
      exact lL.2
    rw [hlOne, inv_one, mul_one]
  rw [hiRestriction]
  change (QuotientGroup.mk'
    (L.field.toSubgroup.subgroupOf K.field.toSubgroup)) s * q₀ = qRaw
  rw [hs]
  simp [q₀]

/-- In a totally ramified finite Galois extension every finite
automorphism has a degree-one Frobenius lift — the element
`σ̃ = σφ_L` (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusLift.lean:109`). -/
def chosenDegreeOneFrobeniusLiftOfTotallyRamified
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : GaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    D.FrobeniusElements K L.field L.below :=
  Classical.choose
    (D.exists_degreeOneFrobeniusLiftOfTotallyRamified
      K L hTot q)

/-- The chosen Frobenius lift for a totally ramified extension has
exponent one (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusLift.lean:120`). -/
@[simp]
theorem frobeniusExponent_chosenDegreeOneFrobeniusLiftOfTotallyRamified
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : GaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    D.frobeniusExponent K L.field L.below
      (D.chosenDegreeOneFrobeniusLiftOfTotallyRamified
        K L hTot q) = 1 := by
  exact (Classical.choose_spec
    (D.exists_degreeOneFrobeniusLiftOfTotallyRamified
      K L hTot q)).1

/-- The chosen degree-one Frobenius lift restricts to the prescribed
automorphism (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusLift.lean:133`). -/
@[simp]
theorem frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfTotallyRamified
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : GaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    L.extensionQuotientMulEquiv.symm
        (D.frobeniusRestriction K L.field L.below
          (D.chosenDegreeOneFrobeniusLiftOfTotallyRamified
            K L hTot q)) = q := by
  exact (Classical.choose_spec
    (D.exists_degreeOneFrobeniusLiftOfTotallyRamified
      K L hTot q)).2

/-- Underlying quotient form of the Galois-bundle restriction theorem
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusLift.lean:146`). -/
theorem frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfTotallyRamified_underlying
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : GaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    D.frobeniusRestriction K L.field L.below
        (D.chosenDegreeOneFrobeniusLiftOfTotallyRamified
          K L hTot q) =
      L.extensionQuotientMulEquiv q := by
  apply L.extensionQuotientMulEquiv.symm.injective
  exact
    D.frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfTotallyRamified
      K L hTot q

/-- **The degree-one lift specialized to a bundled finite Galois
extension**; the conversion to the non-finite Galois boundary and the
quotient comparison are performed once in this definition
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusLift.lean:162`). -/
def chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    D.FrobeniusElements K L.field L.below :=
  D.chosenDegreeOneFrobeniusLiftOfTotallyRamified
    K L.toGaloisSubextension
      (L.isTotallyRamified_toGaloisSubextension D hTot)
      (L.toGaloisExtensionQuotientMulEquiv q)

/-- The finite totally ramified Frobenius lift has exponent one
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusLift.lean:175`). -/
@[simp]
theorem frobeniusExponent_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    D.frobeniusExponent K L.field L.below
      (D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
        K L hTot q) = 1 := by
  exact D.frobeniusExponent_chosenDegreeOneFrobeniusLiftOfTotallyRamified
    K L.toGaloisSubextension
      (L.isTotallyRamified_toGaloisSubextension D hTot)
      (L.toGaloisExtensionQuotientMulEquiv q)

/-- The finite totally ramified Frobenius lift restricts to the chosen
automorphism (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusLift.lean:190`). -/
@[simp]
theorem frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    L.extensionQuotientMulEquiv.symm
        (D.frobeniusRestriction K L.field L.below
          (D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
            K L hTot q)) = q := by
  apply L.extensionQuotientMulEquiv.injective
  rw [L.extensionQuotientMulEquiv.apply_symm_apply]
  have h :=
    D.frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfTotallyRamified_underlying
      K L.toGaloisSubextension
        (L.isTotallyRamified_toGaloisSubextension D hTot)
        (L.toGaloisExtensionQuotientMulEquiv q)
  change
    D.frobeniusRestriction K L.field L.below
        (D.chosenDegreeOneFrobeniusLiftOfTotallyRamified
          K L.toGaloisSubextension
            (L.isTotallyRamified_toGaloisSubextension D hTot)
            (L.toGaloisExtensionQuotientMulEquiv q)) =
      L.extensionQuotientMulEquiv q at h
  exact h

/-- Underlying quotient form of the preceding finite-bundle theorem
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusLift.lean:216`). -/
theorem frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified_underlying
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    D.frobeniusRestriction K L.field L.below
        (D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
          K L hTot q) =
      L.extensionQuotientMulEquiv q := by
  apply L.extensionQuotientMulEquiv.symm.injective
  exact
    D.frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
      K L hTot q

/-- **The finite Galois extension `M / K` chosen**: it contains both
`L` and the degree-one Frobenius fixed field `Σ`, and is contained in
the maximal unramified extension of `L` (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusLift.lean:233`). -/
def abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    FiniteGaloisSubextension K.field := by
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    K L hTot q
  letI : Finite
      (K.field.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
    L.finite
  let SigmaI := D.frobeniusFixedIntermediateField K L.field L.below σ
  let LI := D.fieldAsMaximalUnramifiedIntermediate K.field L.field L.below
  let C := SigmaI.compositum LI
  letI : ((D.maximalUnramifiedField L.field).toSubgroup.subgroupOf
      K.field.toSubgroup).Normal :=
    D.subgroupOf_maximalUnramifiedField_normal K.field L.field L.below
  let M := C.galoisRefinement
  exact
    { field := M.field
      below := M.below
      normal := by
        exact FiniteIntermediateField.galoisRefinement_normal C
      finite := M.finite }

/-- The auxiliary reciprocity extension contains the given totally
ramified extension: its subgroup lies below `G_L` (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusLift.lean:260`). -/
theorem abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    (D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q).field.toSubgroup ≤ L.field.toSubgroup := by
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    K L hTot q
  letI : Finite
      (K.field.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
    L.finite
  let SigmaI := D.frobeniusFixedIntermediateField K L.field L.below σ
  let LI := D.fieldAsMaximalUnramifiedIntermediate K.field L.field L.below
  let C := SigmaI.compositum LI
  letI : ((D.maximalUnramifiedField L.field).toSubgroup.subgroupOf
      K.field.toSubgroup).Normal :=
    D.subgroupOf_maximalUnramifiedField_normal K.field L.field L.below
  change (C.galoisRefinement).field.toSubgroup ≤ L.field.toSubgroup
  exact C.galoisRefinement_le_field.trans
    (FiniteIntermediateField.compositum_le_right SigmaI LI)

/-- The auxiliary reciprocity extension contains the degree-one
Frobenius fixed field: its subgroup lies below `G_Σ` (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusLift.lean:284`). -/
theorem abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_sigma
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    (D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q).field.toSubgroup ≤
      (D.frobeniusFixedField K L.field L.below
        (D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
          K L hTot q)).toSubgroup := by
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    K L hTot q
  letI : Finite
      (K.field.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
    L.finite
  let SigmaI := D.frobeniusFixedIntermediateField K L.field L.below σ
  let LI := D.fieldAsMaximalUnramifiedIntermediate K.field L.field L.below
  let C := SigmaI.compositum LI
  letI : ((D.maximalUnramifiedField L.field).toSubgroup.subgroupOf
      K.field.toSubgroup).Normal :=
    D.subgroupOf_maximalUnramifiedField_normal K.field L.field L.below
  change (C.galoisRefinement).field.toSubgroup ≤ SigmaI.field.toSubgroup
  exact C.galoisRefinement_le_field.trans
    (FiniteIntermediateField.compositum_le_left SigmaI LI)

/-- The auxiliary reciprocity field is contained in the maximal
unramified extension: `G_L̃` lies below its subgroup (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusLift.lean:312`). -/
theorem maximalUnramifiedField_le_abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    (D.maximalUnramifiedField L.field).toSubgroup ≤
      (D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
        K L hTot q).field.toSubgroup := by
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    K L hTot q
  letI : Finite
      (K.field.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
    L.finite
  let SigmaI := D.frobeniusFixedIntermediateField K L.field L.below σ
  let LI := D.fieldAsMaximalUnramifiedIntermediate K.field L.field L.below
  let C := SigmaI.compositum LI
  letI : ((D.maximalUnramifiedField L.field).toSubgroup.subgroupOf
      K.field.toSubgroup).Normal :=
    D.subgroupOf_maximalUnramifiedField_normal K.field L.field L.below
  change (D.maximalUnramifiedField L.field).toSubgroup ≤
    (C.galoisRefinement).field.toSubgroup
  exact (C.galoisRefinement).above

end DegreeData

end

end Atlas.Knowledge
