import Mathlib
import Atlas.Knowledge.AbstractExtension
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteAbstractFieldExtension
import Atlas.Knowledge.FiniteIntermediateFieldRefinement
import Atlas.Knowledge.FiniteResidueAbstractExtension
import Atlas.Knowledge.FiniteTower
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.NormalizedValuationLaws
import Atlas.Knowledge.PrimeElement
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.RelativeNormDoubleCoset
import Atlas.Knowledge.RelativeNormLaws
import Atlas.Knowledge.TransferFrobeniusTerms
import Atlas.Knowledge.TransferNormFrobeniusGeometry
import Atlas.Knowledge.ValuationData

/-!
# Transfer-norm arithmetic

The arithmetic half of transfer–norm naturality: the fiber of one
transfer double coset carries the norm of the conjugated prime, the
transferred fixed field extends the conjugate field unramifiedly so
conjugated primes stay prime, the included norm `N_{Σ|K}(π)` is the sum
over transfer double cosets of the `N_{Σₜ|K'}(πᵗ)`, and the classical
abelianized transfer with its double-coset formula (#104).

## Main definitions

* `DegreeData.transferNormNaturalityFrobeniusTransfer` — the classical
  transfer on abelianizations.

## Main statements

* `DegreeData.transferNormNaturalityTransferFrobenius_fixedField_le_conjugate`
  — `Σₜ` contains the conjugate field; proved.
* `DegreeData.transferNormNaturalityTransferFrobenius_fixedField_isUnramified_conjugate`
  — the extension `Σₜ | Σᵗ` is unramified; proved.
* `DegreeData.transferNormNaturalityTransferFrobenius_conjugatePrime_isPrime`
  — conjugated primes stay prime; proved.
* `DegreeData.transferNormNaturalityNorm_eq_sum_transferNorms` — the
  norm identity; proved.
* `DegreeData.transferNormNaturalityFrobeniusTransfer_doubleCoset_formula`
  — the double-coset formula; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
with `Subgroup.mem_subgroupOf` — its explicit arguments dropped, the
layer's rule taking them implicitly — for the source's membership rule,
and the whole file stays at `Type u` — nothing here pins the
representation-bearing sections, so they generalize the source's
universe device. The tower literal is the layer's top-level
`FiniteTower`, the conjugate bundle its
`FiniteAbstractField.conjugate` form, and the source's `Internal`
namespace is flattened, the #176 rule. Four of the sibling's private
helpers turn public in this same change: their consumers live here, and
`private` does not cross files. The containment-consuming call sites
adapt to the layer's containment-free forms — the stabilizer-iff site
drops two arguments, the tower-finiteness site one, and both
normality-restriction sites one, the containment #175 shed — and the
dead-binder sweep runs to the lint's fixpoint: four declarations shed
the Hausdorff instance and two the topological-group one, all simply
unused. One conjugation re-anchor becomes an explicit `Subtype.ext`
value equation where the source's `simpa` closed over the abbrev, and
two multi-line relative subgroups the converter missed are rewritten by
hand. The citations name this file by bare basename; it lives at
`AbstractClassFieldTheory/Reciprocity/Construction/` in the source. The
source's namespace `open`s go, while `open MulAction` stays for the
orbit vocabulary.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

open MulAction

section transferNormFibers

variable {G : Type u} [Group G] [TopologicalSpace G]

/- Under the fiber equivalence a double-coset norm summand is the
corresponding summand of the conjugate-prime norm
(Yamaguchi 2026, `MainTransferFrobenius.lean:835`). -/
private theorem transferNormNaturalityTransferNormFiber_term
    (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL)))
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField E.base L (hL.trans E.below) σ)) :
    let β := D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q
    let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
    let hSK := D.frobeniusFixedField_le E.base L (hL.trans E.below) σ
    let tK : E.base.field.toSubgroup := Quotient.out q.out.out
    let C := conjugateClosedSubgroup S tK.1
    let Sβ := D.frobeniusFixedField E.field L hL β
    let hSβK' := D.frobeniusFixedField_le E.field L hL β
    ∀ (hSβC : Sβ.toSubgroup ≤ C.toSubgroup)
      (kq : E.field.field.toSubgroup ⧸
        Sβ.toSubgroup.subgroupOf E.field.field.toSubgroup),
      relativeCosetAction A E.base.field S hSK π
          ((chosenTransferNormNaturalityTransferNormFiberEquiv
            D E L hL σ q kq).out •
              (QuotientGroup.mk tK⁻¹ :
                E.base.field.toSubgroup ⧸
                  S.toSubgroup.subgroupOf E.base.field.toSubgroup)) =
        relativeCosetAction A E.field.field Sβ hSβK'
          (fixedFieldInclusion A C Sβ hSβC
            (conjugateFixedElement A S tK.1 π)) kq := by
  dsimp only
  let β := D.transferNormNaturalityTransferFrobeniusLift E L hL σ q
  let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
  let hSK := D.frobeniusFixedField_le E.base L (hL.trans E.below) σ
  let tK : E.base.field.toSubgroup := Quotient.out q.out.out
  let C := conjugateClosedSubgroup S tK.1
  let Sβ := D.frobeniusFixedField E.field L hL β
  let hSβK' := D.frobeniusFixedField_le E.field L hL β
  intro hSβC kq
  refine QuotientGroup.induction_on kq ?_
  intro k'
  let M := E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup
  let φ : E.base.field.toSubgroup ⧸ S.toSubgroup.subgroupOf E.base.field.toSubgroup :=
    QuotientGroup.mk tK⁻¹
  let kM : M := transferNormNaturalityIntermediateAbsoluteEquiv
    E.base.field E.field.field E.below k'
  let fiberEquiv := chosenTransferNormNaturalityTransferNormFiberEquiv
    D E L hL σ q
  let r : M ⧸ stabilizer M φ := fiberEquiv (QuotientGroup.mk k')
  have hrmk : (QuotientGroup.mk r.out : M ⧸ stabilizer M φ) =
      QuotientGroup.mk kM := by
    calc
      QuotientGroup.mk r.out = r := Quotient.out_eq' r
      _ = fiberEquiv (QuotientGroup.mk k') := rfl
      _ = QuotientGroup.mk kM :=
        chosenTransferNormNaturalityTransferNormFiberEquiv_mk
          D E L hL σ q k'
  have hrel : r.out⁻¹ * kM ∈ stabilizer M φ :=
    QuotientGroup.eq.mp hrmk
  have hact : r.out • φ = kM • φ := by
    have hh := congrArg (fun z => r.out • z) hrel
    simpa [mul_smul] using hh.symm
  change relativeCosetAction A E.base.field S hSK π (r.out • φ) = _
  rw [hact]
  change relativeCosetAction A E.base.field S hSK π
      (QuotientGroup.mk (kM.1 * tK⁻¹)) = _
  rw [relativeCosetAction_mk, relativeCosetAction_mk]
  simp only [fixedFieldInclusion_coe, conjugateFixedElement_coe]
  change A.ρ (k'.1 * tK.1⁻¹) π.1 = A.ρ k'.1 (A.ρ tK.1⁻¹ π.1)
  rw [map_mul]
  rfl

/- The inner double-coset sum of a transfer orbit is the norm of the
conjugated prime (Yamaguchi 2026, `MainTransferFrobenius.lean:915`). -/
private theorem transferNormNaturalityTransferNormFiber_sum
    (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    [hL'finite : Finite
      (E.field.field.toSubgroup ⧸ L.toSubgroup.subgroupOf E.field.field.toSubgroup)]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL)))
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField E.base L (hL.trans E.below) σ))
    (hSβC :
      let β := D.transferNormNaturalityTransferFrobeniusLift
        E L hL σ q
      let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
      let tK : E.base.field.toSubgroup := Quotient.out q.out.out
      (D.frobeniusFixedField E.field L hL β).toSubgroup ≤
        (conjugateClosedSubgroup S tK.1).toSubgroup) :
    let β := D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q
    let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
    let hSK := D.frobeniusFixedField_le E.base L (hL.trans E.below) σ
    let tK : E.base.field.toSubgroup := Quotient.out q.out.out
    let C := conjugateClosedSubgroup S tK.1
    let Sβ := D.frobeniusFixedField E.field L hL β
    let hSβK' := D.frobeniusFixedField_le E.field L hL β
    let M := E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup
    let φ : E.base.field.toSubgroup ⧸ S.toSubgroup.subgroupOf E.base.field.toSubgroup :=
      QuotientGroup.mk tK⁻¹
    letI : Finite (E.field.field.toSubgroup ⧸
        Sβ.toSubgroup.subgroupOf E.field.field.toSubgroup) :=
      D.frobeniusFixedField_finite E.field L hL β
    letI : Fintype (E.field.field.toSubgroup ⧸
        Sβ.toSubgroup.subgroupOf E.field.field.toSubgroup) := Fintype.ofFinite _
    let fiberEquiv := chosenTransferNormNaturalityTransferNormFiberEquiv
      D E L hL σ q
    letI : Fintype (M ⧸ stabilizer M φ) :=
      Fintype.ofEquiv
        (E.field.field.toSubgroup ⧸
          Sβ.toSubgroup.subgroupOf E.field.field.toSubgroup) fiberEquiv
    ∑ r : M ⧸ stabilizer M φ,
        relativeCosetAction A E.base.field S hSK π (r.out • φ) =
      ((relativeNorm A E.field.field Sβ hSβK'
        (fixedFieldInclusion A C Sβ hSβC
          (conjugateFixedElement A S tK.1 π)) :
            ambientFixedAddSubgroup A E.field.field) : A.V) := by
  dsimp only
  let β := D.transferNormNaturalityTransferFrobeniusLift E L hL σ q
  let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
  let hSK := D.frobeniusFixedField_le E.base L (hL.trans E.below) σ
  let tK : E.base.field.toSubgroup := Quotient.out q.out.out
  let C := conjugateClosedSubgroup S tK.1
  let Sβ := D.frobeniusFixedField E.field L hL β
  let hSβK' := D.frobeniusFixedField_le E.field L hL β
  let M := E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup
  let φ : E.base.field.toSubgroup ⧸ S.toSubgroup.subgroupOf E.base.field.toSubgroup :=
    QuotientGroup.mk tK⁻¹
  letI : Finite (E.field.field.toSubgroup ⧸
      Sβ.toSubgroup.subgroupOf E.field.field.toSubgroup) :=
    D.frobeniusFixedField_finite E.field L hL β
  letI : Fintype (E.field.field.toSubgroup ⧸
      Sβ.toSubgroup.subgroupOf E.field.field.toSubgroup) := Fintype.ofFinite _
  let fiberEquiv := chosenTransferNormNaturalityTransferNormFiberEquiv
    D E L hL σ q
  letI : Fintype (M ⧸ stabilizer M φ) :=
    Fintype.ofEquiv
      (E.field.field.toSubgroup ⧸
        Sβ.toSubgroup.subgroupOf E.field.field.toSubgroup) fiberEquiv
  rw [relativeNorm_apply_coe, relativeNormValue]
  calc
    (∑ r : M ⧸ stabilizer M φ,
        relativeCosetAction A E.base.field S hSK π (r.out • φ)) =
      ∑ kq : E.field.field.toSubgroup ⧸
          Sβ.toSubgroup.subgroupOf E.field.field.toSubgroup,
        relativeCosetAction A E.base.field S hSK π
          ((fiberEquiv kq).out • φ) :=
      (fiberEquiv.sum_comp
        (fun r => relativeCosetAction A E.base.field S hSK π
          (r.out • φ))).symm
    _ = ∑ kq : E.field.field.toSubgroup ⧸
          Sβ.toSubgroup.subgroupOf E.field.field.toSubgroup,
        relativeCosetAction A E.field.field Sβ hSβK'
          (fixedFieldInclusion A C Sβ hSβC
            (conjugateFixedElement A S tK.1 π)) kq := by
      apply Fintype.sum_congr
      intro kq
      exact transferNormNaturalityTransferNormFiber_term
        D A E L hL σ q π hSβC kq


end transferNormFibers

section transferredFixedFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **The fixed field `Σₜ` of a transfer Frobenius factor contains the
conjugate field `Σᵗ`** — on absolute groups, `G_{Σₜ} ≤ G_{Σᵗ}`
(Yamaguchi 2026, `MainTransferFrobenius.lean:1024`). -/
theorem transferNormNaturalityTransferFrobenius_fixedField_le_conjugate
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    let β := D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q
    let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
    let tK : E.base.field.toSubgroup := Quotient.out q.out.out
    let C := conjugateClosedSubgroup S tK.1
    let Sβ := D.frobeniusFixedField E.field L hL β
    Sβ.toSubgroup ≤ C.toSubgroup := by
  dsimp only
  intro x hx
  apply (conjugateClosedSubgroup_mem
    (D.frobeniusFixedField E.base L (hL.trans E.below) σ)
    (Quotient.out q.out.out).1 x).2
  let k' : E.field.field.toSubgroup :=
    ⟨x, (D.frobeniusFixedField_le E.field L hL
      (D.transferNormNaturalityTransferFrobeniusLift E L hL σ q)) hx⟩
  have hxext : k' ∈ (D.frobeniusFixedField E.field L hL
        (D.transferNormNaturalityTransferFrobeniusLift E L hL σ q)).toSubgroup.subgroupOf
            E.field.field.toSubgroup := by
    rw [Subgroup.mem_subgroupOf]
    exact hx
  have hstab :=
    (D.transferNormNaturalityTransferFrobeniusLift_mem_fixedSubgroup_iff_stabilizer
      E L hL σ q k').1 hxext
  have hmem :=
    (mem_relativeNormDoubleCoset_stabilizer_iff
      E.base.field E.field.field
      (D.frobeniusFixedField E.base L (hL.trans E.below) σ)
      (Quotient.out q.out.out)⁻¹
      (⟨Subgroup.inclusion E.below k', k'.2⟩ :
        E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup)).1 hstab
  change
    ((Quotient.out q.out.out)⁻¹).1⁻¹ *
        (Subgroup.inclusion E.below k').1 *
        ((Quotient.out q.out.out)⁻¹).1 ∈
      (D.frobeniusFixedField E.base L (hL.trans E.below) σ).toSubgroup at hmem
  have heq :
      ((Quotient.out q.out.out)⁻¹).1⁻¹ *
          (Subgroup.inclusion E.below k').1 *
          ((Quotient.out q.out.out)⁻¹).1 =
        (Quotient.out q.out.out).1 * x *
          (Quotient.out q.out.out).1⁻¹ := by
    simp [k']
  rw [heq] at hmem
  exact hmem

/-- **The extension `Σₜ | Σᵗ` attached to one transfer orbit is
unramified** (Yamaguchi 2026,
`MainTransferFrobenius.lean:1087`). -/
theorem transferNormNaturalityTransferFrobenius_fixedField_isUnramified_conjugate
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    let β := D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q
    let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
    let tK : E.base.field.toSubgroup := Quotient.out q.out.out
    let C := conjugateClosedSubgroup S tK.1
    let Sβ := D.frobeniusFixedField E.field L hL β
    let hSβC := D.transferNormNaturalityTransferFrobenius_fixedField_le_conjugate
      E L hL σ q
    (AbstractExtension.mk Sβ C hSβC).IsUnramified D := by
  dsimp only
  let β := D.transferNormNaturalityTransferFrobeniusLift E L hL σ q
  let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
  let tK : E.base.field.toSubgroup := Quotient.out q.out.out
  let C := conjugateClosedSubgroup S tK.1
  let Sβ := D.frobeniusFixedField E.field L hL β
  have hSβC : Sβ.toSubgroup ≤ C.toSubgroup := by
    exact D.transferNormNaturalityTransferFrobenius_fixedField_le_conjugate
      E L hL σ q
  rw [(AbstractExtension.mk Sβ C hSβC).isUnramified_iff_inertia_le D]
  intro x hx
  have hxC : x ∈ C.toSubgroup := hx.1
  have hxd : D.degree x = 1 := hx.2
  have hconjS : tK.1 * x * tK.1⁻¹ ∈ S.toSubgroup := by
    exact (conjugateClosedSubgroup_mem S tK.1 x).1 hxC
  have hconjd : D.degree (tK.1 * x * tK.1⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, hxd]
    simp
  have hconjI : tK.1 * x * tK.1⁻¹ ∈
      (D.fieldInertia S).toSubgroup := by
    exact ⟨hconjS, hconjd⟩
  have hconjIL : tK.1 * x * tK.1⁻¹ ∈
      (D.fieldInertia L).toSubgroup := by
    rw [← D.frobeniusFixedField_fieldInertia
      E.base L (hL.trans E.below) σ]
    exact hconjI
  have hxK : x ∈ E.base.field.toSubgroup := by
    have hconjK : tK.1 * x * tK.1⁻¹ ∈ E.base.field.toSubgroup :=
      (D.frobeniusFixedField_le E.base L (hL.trans E.below) σ) hconjS
    have hback := E.base.field.toSubgroup.mul_mem
      (E.base.field.toSubgroup.mul_mem
        (E.base.field.toSubgroup.inv_mem tK.2) hconjK) tK.2
    simpa [mul_assoc] using hback
  let xK : E.base.field.toSubgroup := ⟨x, hxK⟩
  let yK : E.base.field.toSubgroup :=
    ⟨tK.1 * x * tK.1⁻¹,
      E.base.field.toSubgroup.mul_mem
        (E.base.field.toSubgroup.mul_mem tK.2 hxK)
        (E.base.field.toSubgroup.inv_mem tK.2)⟩
  have hyL : yK ∈
      L.toSubgroup.subgroupOf E.base.field.toSubgroup := by
    rw [Subgroup.mem_subgroupOf]
    exact hconjIL.1
  have hxLext : xK ∈
      L.toSubgroup.subgroupOf E.base.field.toSubgroup := by
    have hback := hLnormal.conj_mem yK hyL tK⁻¹
    have hval : xK = tK⁻¹ * yK * (tK⁻¹)⁻¹ := by
      apply Subtype.ext
      simp [xK, yK, mul_assoc]
    rw [hval]
    exact hback
  have hxL : x ∈ L.toSubgroup := by
    exact (Subgroup.mem_subgroupOf).1 hxLext
  have hxIL : x ∈ (D.fieldInertia L).toSubgroup := ⟨hxL, hxd⟩
  have hxISβ : x ∈ (D.fieldInertia Sβ).toSubgroup := by
    rw [D.frobeniusFixedField_fieldInertia E.field L hL β]
    exact hxIL
  exact hxISβ.1

end DegreeData

end transferredFixedFields

section transferNormArithmetic

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **A prime of `Σ`, conjugated and included into the unramified
extension `Σₜ`, remains prime** (Yamaguchi 2026,
`MainTransferFrobenius.lean:1182`). -/
theorem transferNormNaturalityTransferFrobenius_conjugatePrime_isPrime
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (F : FiniteAbstractFieldExtension G) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ F.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf F.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf F.field.field.toSubgroup).Normal]
    [hLfinite : Finite
      (F.field.field.toSubgroup ⧸ L.toSubgroup.subgroupOf F.field.field.toSubgroup)]
    (σ : D.FrobeniusElements
      (F.toFiniteResidueAbstractExtension D).base L
      (hL.trans F.below) (hLnormal := by
        change (L.toSubgroup.subgroupOf F.base.field.toSubgroup).Normal
        exact hLnormal))
    (q :
      letI : (L.toSubgroup.subgroupOf
          (F.toFiniteResidueAbstractExtension D).base.field.toSubgroup).Normal := by
        change (L.toSubgroup.subgroupOf F.base.field.toSubgroup).Normal
        exact hLnormal
      letI : (L.toSubgroup.subgroupOf
          (F.toFiniteResidueAbstractExtension D).field.field.toSubgroup).Normal := by
        change (L.toSubgroup.subgroupOf F.field.field.toSubgroup).Normal
        exact hL'normal
      Quotient (orbitRel (Subgroup.zpowers σ.1)
      (((F.toFiniteResidueAbstractExtension D).base.field.toSubgroup ⧸
        D.extensionInertiaWithin
          (F.toFiniteResidueAbstractExtension D).base.field L
            (hL.trans F.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            (F.toFiniteResidueAbstractExtension D) L hL
            (hLnormal := by
              change (L.toSubgroup.subgroupOf F.base.field.toSubgroup).Normal
              exact hLnormal)
            (hL'normal := by
              change (L.toSubgroup.subgroupOf F.field.field.toSubgroup).Normal
              exact hL'normal))))
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField
        (F.toFiniteResidueAbstractExtension D).base L
        (hL.trans F.below) (hLnormal := by
          change (L.toSubgroup.subgroupOf F.base.field.toSubgroup).Normal
          exact hLnormal) σ))
    (hπ :
      let KR := (F.toFiniteResidueAbstractExtension D).base
      letI :
          (L.toSubgroup.subgroupOf KR.field.toSubgroup).Normal := by
        change (L.toSubgroup.subgroupOf F.base.field.toSubgroup).Normal
        exact hLnormal
      let T : FiniteTower G := {
        top := L
        middle := F.field.field
        base := F.base.field
        top_le_middle := hL
        middle_le_base := F.below
        finiteTopQuotient := hLfinite
        finiteBaseQuotient := F.finiteQuotient }
      letI : Finite (F.base.field.toSubgroup ⧸
          L.toSubgroup.subgroupOf F.base.field.toSubgroup) :=
        T.totalQuotientFinite
      let S := D.frobeniusFixedField
        KR L (hL.trans F.below) σ
      let Sfinite : FiniteAbstractField G := {
        field := S
        finite := D.frobeniusFixedField_absoluteFinite
          F.base L (hL.trans F.below) σ }
      v.IsPrimeElement Sfinite π) :
    let E := F.toFiniteResidueAbstractExtension D
    letI hLnormalE :
        (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal := by
      change (L.toSubgroup.subgroupOf F.base.field.toSubgroup).Normal
      exact hLnormal
    letI hL'normalE : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal := by
      change (L.toSubgroup.subgroupOf F.field.field.toSubgroup).Normal
      exact hL'normal
    let T : FiniteTower G := {
      top := L
      middle := F.field.field
      base := F.base.field
      top_le_middle := hL
      middle_le_base := F.below
      finiteTopQuotient := hLfinite
      finiteBaseQuotient := F.finiteQuotient }
    letI : Finite (F.base.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf F.base.field.toSubgroup) :=
      T.totalQuotientFinite
    let β := D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q
    let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
    let Sfinite : FiniteAbstractField G := {
      field := S
      finite := by
        simpa [E, S,
          FiniteAbstractFieldExtension.toFiniteResidueAbstractExtension,
          FiniteAbstractField.toFiniteResidueAbstractField] using
          D.frobeniusFixedField_absoluteFinite
          F.base L (hL.trans F.below) σ }
    let tK : E.base.field.toSubgroup := Quotient.out q.out.out
    let Cfinite := Sfinite.conjugate tK.1
    let Sβ := D.frobeniusFixedField E.field L hL β
    let Sβfinite : FiniteAbstractField G := {
      field := Sβ
      finite := by
        simpa [E, Sβ,
          FiniteAbstractFieldExtension.toFiniteResidueAbstractExtension,
          FiniteAbstractField.toFiniteResidueAbstractField] using
          D.frobeniusFixedField_absoluteFinite F.field L hL β }
    let hSβC : Sβfinite.field.toSubgroup ≤ Cfinite.field.toSubgroup := by
      change Sβ.toSubgroup ≤
        (conjugateClosedSubgroup S tK.1).toSubgroup
      exact D.transferNormNaturalityTransferFrobenius_fixedField_le_conjugate
        E L hL σ q
    v.IsPrimeElement Sβfinite
      (fixedFieldInclusion A Cfinite.field Sβfinite.field hSβC
        (conjugateFixedElement A S tK.1 π)) := by
  dsimp only
  let E := F.toFiniteResidueAbstractExtension D
  letI hLnormalE :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal := by
    change (L.toSubgroup.subgroupOf F.base.field.toSubgroup).Normal
    exact hLnormal
  letI hL'normalE : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal := by
    change (L.toSubgroup.subgroupOf F.field.field.toSubgroup).Normal
    exact hL'normal
  let T : FiniteTower G := {
    top := L
    middle := F.field.field
    base := F.base.field
    top_le_middle := hL
    middle_le_base := F.below
    finiteTopQuotient := hLfinite
    finiteBaseQuotient := F.finiteQuotient }
  letI hLbaseFinite : Finite (F.base.field.toSubgroup ⧸
      L.toSubgroup.subgroupOf F.base.field.toSubgroup) :=
    T.totalQuotientFinite
  let β := D.transferNormNaturalityTransferFrobeniusLift
    E L hL σ q
  let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
  let Sfinite : FiniteAbstractField G := {
    field := S
    finite := by
      simpa [E, S,
        FiniteAbstractFieldExtension.toFiniteResidueAbstractExtension,
        FiniteAbstractField.toFiniteResidueAbstractField] using
        D.frobeniusFixedField_absoluteFinite
        F.base L (hL.trans F.below) σ }
  let tK : E.base.field.toSubgroup := Quotient.out q.out.out
  let Cfinite := Sfinite.conjugate tK.1
  let Sβ := D.frobeniusFixedField E.field L hL β
  let Sβfinite : FiniteAbstractField G := {
    field := Sβ
    finite := by
      simpa [E, Sβ,
        FiniteAbstractFieldExtension.toFiniteResidueAbstractExtension,
        FiniteAbstractField.toFiniteResidueAbstractField] using
        D.frobeniusFixedField_absoluteFinite F.field L hL β }
  let hSβC : Sβfinite.field.toSubgroup ≤ Cfinite.field.toSubgroup := by
    change Sβ.toSubgroup ≤
      (conjugateClosedSubgroup S tK.1).toSubgroup
    exact D.transferNormNaturalityTransferFrobenius_fixedField_le_conjugate
      E L hL σ q
  letI hSβabsolute : Finite ((baseField G).toSubgroup ⧸
      Sβfinite.field.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    Sβfinite.finite
  letI hSβCfinite : Finite
      (Cfinite.field.toSubgroup ⧸
        Sβfinite.field.toSubgroup.subgroupOf Cfinite.field.toSubgroup) :=
    FiniteIntermediateField.finite_extension_of_le
      (le_baseField Cfinite.field) hSβC
  let EβC : FiniteAbstractFieldExtension G := {
    field := Sβfinite
    base := Cfinite
    below := hSβC
    finiteQuotient := hSβCfinite }
  let πC : ambientFixedAddSubgroup A Cfinite.field :=
    conjugateFixedElement A S tK.1 π
  have hπC : v.IsPrimeElement Cfinite πC := by
    rw [ValuationData.IsPrimeElement]
    rw [show v.valuationAt Cfinite πC = v.valuationAt Sfinite π by
      simpa [Cfinite, Sfinite, πC] using
        v.normalizedValuation_conjugate Sfinite tK.1 π]
    exact hπ
  have hUn : EβC.IsUnramified D := by
    exact D.transferNormNaturalityTransferFrobenius_fixedField_isUnramified_conjugate
      E L hL σ q
  exact v.prime_of_unramified EβC hUn πC hπC

/-- **The norm identity of transfer–norm naturality**: the included
`N_{Σ|K}(π)` is the sum over transfer double cosets of the conjugated
primes' norms `N_{Σₜ|K'}(πᵗ)` (Yamaguchi 2026,
`MainTransferFrobenius.lean:1382`). -/
theorem transferNormNaturalityNorm_eq_sum_transferNorms
    (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G]
    (F : FiniteAbstractFieldExtension G) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ F.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf F.base.field.toSubgroup).Normal]
    [hLfinite : Finite
      (F.field.field.toSubgroup ⧸ L.toSubgroup.subgroupOf F.field.field.toSubgroup)]
    (σ : D.FrobeniusElements
      (F.toFiniteResidueAbstractExtension D).base L
      (hL.trans F.below) (hLnormal := by
        change (L.toSubgroup.subgroupOf F.base.field.toSubgroup).Normal
        exact hLnormal))
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField
        (F.toFiniteResidueAbstractExtension D).base L
        (hL.trans F.below) (hLnormal := by
          change (L.toSubgroup.subgroupOf F.base.field.toSubgroup).Normal
          exact hLnormal) σ)) :
    let E := F.toFiniteResidueAbstractExtension D
    letI hLnormalE :
        (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal := by
      change (L.toSubgroup.subgroupOf F.base.field.toSubgroup).Normal
      exact hLnormal
    let T : FiniteTower G := {
      top := L
      middle := F.field.field
      base := F.base.field
      top_le_middle := hL
      middle_le_base := F.below
      finiteTopQuotient := hLfinite
      finiteBaseQuotient := F.finiteQuotient }
    letI : Finite (E.base.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf E.base.field.toSubgroup) := by
      change Finite (F.base.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf F.base.field.toSubgroup)
      exact T.totalQuotientFinite
    letI : Finite (E.field.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf E.field.field.toSubgroup) := by
      change Finite (F.field.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf F.field.field.toSubgroup)
      exact hLfinite
    letI : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal :=
      transferNormNaturality_intermediateExtension_normal
        E.base.field E.field.field L E.below
    let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
    let hSK := D.frobeniusFixedField_le E.base L (hL.trans E.below) σ
    let M := E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup
    let ΩN := Quotient (orbitRel M
      (E.base.field.toSubgroup ⧸ S.toSubgroup.subgroupOf E.base.field.toSubgroup))
    letI : Finite (E.base.field.toSubgroup ⧸
        S.toSubgroup.subgroupOf E.base.field.toSubgroup) :=
      D.frobeniusFixedField_finite E.base L (hL.trans E.below) σ
    letI : Fintype ΩN := Fintype.ofFinite _
    ((fixedFieldInclusion A E.base.field E.field.field E.below
      (relativeNorm A E.base.field S hSK π) :
        ambientFixedAddSubgroup A E.field.field) : A.V) =
      ∑ qN : ΩN,
        let qT := (D.transferNormNaturalityTransferNormOrbitEquiv
          E L hL σ).symm qN
        let β := D.transferNormNaturalityTransferFrobeniusLift
          E L hL σ qT
        let tK : E.base.field.toSubgroup := Quotient.out qT.out.out
        let C := conjugateClosedSubgroup S tK.1
        let Sβ := D.frobeniusFixedField E.field L hL β
        let hSβK' := D.frobeniusFixedField_le E.field L hL β
        let hSβC : Sβ.toSubgroup ≤ C.toSubgroup :=
          D.transferNormNaturalityTransferFrobenius_fixedField_le_conjugate
            E L hL σ qT
        letI : Finite (E.field.field.toSubgroup ⧸
            Sβ.toSubgroup.subgroupOf E.field.field.toSubgroup) :=
          D.frobeniusFixedField_finite E.field L hL β
        ((relativeNorm A E.field.field Sβ hSβK'
          (fixedFieldInclusion A C Sβ hSβC
            (conjugateFixedElement A S tK.1 π)) :
              ambientFixedAddSubgroup A E.field.field) : A.V) := by
  dsimp only
  let E := F.toFiniteResidueAbstractExtension D
  letI hLnormalE :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal := by
    change (L.toSubgroup.subgroupOf F.base.field.toSubgroup).Normal
    exact hLnormal
  let T : FiniteTower G := {
    top := L
    middle := F.field.field
    base := F.base.field
    top_le_middle := hL
    middle_le_base := F.below
    finiteTopQuotient := hLfinite
    finiteBaseQuotient := F.finiteQuotient }
  letI hLbaseFinite : Finite (E.base.field.toSubgroup ⧸
      L.toSubgroup.subgroupOf E.base.field.toSubgroup) := by
    change Finite (F.base.field.toSubgroup ⧸
      L.toSubgroup.subgroupOf F.base.field.toSubgroup)
    exact T.totalQuotientFinite
  letI hLfieldFinite : Finite (E.field.field.toSubgroup ⧸
      L.toSubgroup.subgroupOf E.field.field.toSubgroup) := by
    change Finite (F.field.field.toSubgroup ⧸
      L.toSubgroup.subgroupOf F.field.field.toSubgroup)
    exact hLfinite
  letI hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal :=
    transferNormNaturality_intermediateExtension_normal
      E.base.field E.field.field L E.below
  let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
  let hSK := D.frobeniusFixedField_le E.base L (hL.trans E.below) σ
  let M := E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup
  let ΩN := Quotient (orbitRel M
    (E.base.field.toSubgroup ⧸ S.toSubgroup.subgroupOf E.base.field.toSubgroup))
  let φ : ΩN →
      E.base.field.toSubgroup ⧸ S.toSubgroup.subgroupOf E.base.field.toSubgroup :=
    chosenTransferNormNaturalityNormOrbitRepresentative
      D E L hL σ
  letI : Finite (E.base.field.toSubgroup ⧸
      S.toSubgroup.subgroupOf E.base.field.toSubgroup) :=
    D.frobeniusFixedField_finite E.base L (hL.trans E.below) σ
  letI : Fintype ΩN := Fintype.ofFinite _
  letI (qN : ΩN) : Fintype (M ⧸ stabilizer M (φ qN)) := by
    letI : Finite (orbit M (φ qN)) :=
      Finite.of_injective Subtype.val Subtype.val_injective
    letI := Fintype.ofFinite (orbit M (φ qN))
    exact Fintype.ofEquiv (orbit M (φ qN))
      (orbitEquivQuotientStabilizer M (φ qN))
  change ((relativeNorm A E.base.field S hSK π :
    ambientFixedAddSubgroup A E.base.field) : A.V) = _
  rw [relativeNorm_eq_sum_chosenOrbit_of_fintype A E.base.field S hSK M
    (chosenTransferNormNaturalityNormOrbitRepresentative_spec
      D E L hL σ) π]
  apply Fintype.sum_congr
  intro qN
  let qT := (D.transferNormNaturalityTransferNormOrbitEquiv
    E L hL σ).symm qN
  let β := D.transferNormNaturalityTransferFrobeniusLift
    E L hL σ qT
  let tK : E.base.field.toSubgroup := Quotient.out qT.out.out
  let C := conjugateClosedSubgroup S tK.1
  let Sβ := D.frobeniusFixedField E.field L hL β
  let hSβK' := D.frobeniusFixedField_le E.field L hL β
  let hSβC : Sβ.toSubgroup ≤ C.toSubgroup :=
    D.transferNormNaturalityTransferFrobenius_fixedField_le_conjugate
      E L hL σ qT
  let fiberEquiv := chosenTransferNormNaturalityTransferNormFiberEquiv
    D E L hL σ qT
  letI : Finite (E.field.field.toSubgroup ⧸
      Sβ.toSubgroup.subgroupOf E.field.field.toSubgroup) :=
    D.frobeniusFixedField_finite E.field L hL β
  letI : Fintype (E.field.field.toSubgroup ⧸
      Sβ.toSubgroup.subgroupOf E.field.field.toSubgroup) :=
    Fintype.ofFinite _
  letI : Fintype (M ⧸ stabilizer M
      (QuotientGroup.mk tK⁻¹ :
        E.base.field.toSubgroup ⧸ S.toSubgroup.subgroupOf E.base.field.toSubgroup)) := by
    change Fintype (M ⧸ stabilizer M (φ qN))
    infer_instance
  rw [relativeNorm_apply_coe, relativeNormValue]
  calc
    (∑ r : M ⧸ stabilizer M (φ qN),
        relativeCosetAction A E.base.field S hSK π
          ((MulAction.selfEquivSigmaOrbitsQuotientStabilizer'
            M (E.base.field.toSubgroup ⧸ S.toSubgroup.subgroupOf E.base.field.toSubgroup)
              (chosenTransferNormNaturalityNormOrbitRepresentative_spec
                D E L hL σ)).symm ⟨qN, r⟩)) =
      ∑ r : M ⧸ stabilizer M (φ qN),
        relativeCosetAction A E.base.field S hSK π (r.out • φ qN) := by
      apply Fintype.sum_congr
      intro r
      rw [chosenOrbitClassEquiv_symm_apply]
    _ = ∑ kq : E.field.field.toSubgroup ⧸
        Sβ.toSubgroup.subgroupOf E.field.field.toSubgroup,
        relativeCosetAction A E.base.field S hSK π
          ((fiberEquiv kq).out • φ qN) :=
      (fiberEquiv.sum_comp
        (fun r => relativeCosetAction A E.base.field S hSK π
          (r.out • φ qN))).symm
    _ = ∑ kq : E.field.field.toSubgroup ⧸
        Sβ.toSubgroup.subgroupOf E.field.field.toSubgroup,
        relativeCosetAction A E.field.field Sβ hSβK'
          (fixedFieldInclusion A C Sβ hSβC
            (conjugateFixedElement A S tK.1 π)) kq := by
      apply Fintype.sum_congr
      intro kq
      exact transferNormNaturalityTransferNormFiber_term
        D A E L hL σ qT π hSβC kq

end DegreeData

end transferNormArithmetic

section frobeniusTransfer

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **The classical transfer `G(L̃|K)ᵃᵇ →* G(L̃|K')ᵃᵇ`**, before
passage to the finite Galois quotient (Yamaguchi 2026,
`MainTransferFrobenius.lean:1583`). -/
noncomputable def transferNormNaturalityFrobeniusTransfer
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal] :
    Abelianization (E.base.field.toSubgroup ⧸
        D.extensionInertiaWithin E.base.field L (hL.trans E.below)) →*
      Abelianization (E.field.field.toSubgroup ⧸
        D.extensionInertiaWithin E.field.field L hL) := by
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup
    E L hL
  letI : H.FiniteIndex :=
    D.transferNormNaturalityFrobeniusIntermediateFiniteIndex E L hL
  let e := D.transferNormNaturalityFrobeniusIntermediateEquiv
    E L hL
  exact e.symm.abelianizationCongr.toMonoidHom.comp
    (Abelianization.lift
      (MonoidHom.transfer (Abelianization.of : H →* Abelianization H)))

/-- **The double-coset formula for the Frobenius-level transfer** —
every factor is the positive Frobenius lift constructed before
(Yamaguchi 2026, `MainTransferFrobenius.lean:1606`). -/
theorem transferNormNaturalityFrobeniusTransfer_doubleCoset_formula
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : E.base.field.toSubgroup ⧸
      D.extensionInertiaWithin E.base.field L (hL.trans E.below)) :
    let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup
      E L hL
    letI : H.FiniteIndex :=
      D.transferNormNaturalityFrobeniusIntermediateFiniteIndex E L hL
    letI : Fintype (Quotient (orbitRel (Subgroup.zpowers σ)
        ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
          (hL.trans E.below)) ⧸ H))) :=
      Fintype.ofFinite _
    D.transferNormNaturalityFrobeniusTransfer E L hL
        (Abelianization.of σ) =
      ∏ q : Quotient (orbitRel (Subgroup.zpowers σ)
          ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
            (hL.trans E.below)) ⧸ H)),
        Abelianization.of
          ((D.transferNormNaturalityFrobeniusIntermediateEquiv
            E L hL).symm
              ⟨q.out.out⁻¹ * σ ^ Function.minimalPeriod (σ • ·) q.out *
                  q.out.out,
                QuotientGroup.out_conj_pow_minimalPeriod_mem
                  H σ q.out⟩) := by
  dsimp only
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup
    E L hL
  letI : H.FiniteIndex :=
    D.transferNormNaturalityFrobeniusIntermediateFiniteIndex E L hL
  letI := Fintype.ofFinite
    (Quotient (orbitRel (Subgroup.zpowers σ)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸ H)))
  unfold transferNormNaturalityFrobeniusTransfer
  simp only [MonoidHom.comp_apply, Abelianization.lift_apply_of]
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro q _
  exact abelianizationCongr_of
    (D.transferNormNaturalityFrobeniusIntermediateEquiv
      E L hL).symm _

end DegreeData
end frobeniusTransfer

end

end Atlas.Knowledge
