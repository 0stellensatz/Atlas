import Mathlib
import Atlas.Knowledge.ConcreteReciprocityTransport
import Atlas.Knowledge.DecompositionResidueExactSequence
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteGaloisRealization
import Atlas.Knowledge.GaloisExtensionQuotient
import Atlas.Knowledge.IntegralClosureDVR
import Atlas.Knowledge.IntermediateFieldNormResidueNaturality
import Atlas.Knowledge.IsArithmeticFrobenius
import Atlas.Knowledge.LocalAbsoluteValuationSubring
import Atlas.Knowledge.LocalResidueDatum
import Atlas.Knowledge.LowerRamificationGroup
import Atlas.Knowledge.NormalizedDegree
import Atlas.Knowledge.ProfiniteInteger
import Atlas.Knowledge.ResidueAbsoluteDegreeIn
import Atlas.Knowledge.ResidueAbsoluteFrobenius
import Atlas.Knowledge.ResidueActionIndex
import Atlas.Knowledge.ResidueDatumIn
import Atlas.Knowledge.UnramifiedNormQuotient

/-!
# unramified comparison

The concrete unramified vocabulary meets the abstract reciprocity
stock: for a finite Galois extension of a mixed-characteristic local
field realized in the algebraic closure, trivial concrete inertia
(`lowerRamificationGroup K L 0 = ⊥`) makes the realized abstract
extension unramified for the local degree datum — the opposite
direction, on realizations, to
`Atlas.Knowledge.lowerRamificationGroup_eq_bot_of_isUnramified`, which
descends from abstract unramifiedness at the fixed fields — and the
abstract degree-one unramified Frobenius realizes, through the chosen
quotient equivalence, to an automorphism satisfying the
arithmetic-Frobenius substitution congruence. Together they let the
constructed Artin map be evaluated on a uniformizer (#104).

## Main definitions

* `unramifiedFrobeniusRealizationOfEmbedding` — the abstract degree-one
  Frobenius of a realization, as an actual automorphism.

## Main statements

* `galoisAmbientFiniteAbstractBase_residueDegree_eq_one` — the packaged
  ambient base has residue degree one; proved.
* `finiteGaloisAbstractExtensionOfEmbedding_isUnramified` — trivial
  concrete inertia gives abstract unramifiedness; proved.
* `isArithmeticFrobenius_unramifiedFrobeniusRealizationOfEmbedding` —
  the realized abstract Frobenius is an arithmetic Frobenius; proved.
* `unramifiedFrobeniusRealizationOfEmbedding_eq` — under trivial
  inertia the realization is embedding-independent; proved.

## Implementation notes

Both theorems are re-proved on the layer's own unramified vocabulary,
not ported: the source constructs a residue embedding of `𝓀[L]` into
its selected residue closure and runs equivariance plus the residue
map's injectivity under its `IsUnramifiedValuedExtension` hypothesis
(`LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedComparison.lean:196`,
`:233`), where the layer states concrete unramifiedness as
`lowerRamificationGroup K L 0 = ⊥` and never builds the embedding: an
absolute Galois element of trivial residue degree (resp. degree one)
moves every element of the absolute valuation ring within the maximal
ideal (resp. to its `q`-th power modulo it) — read off
`Atlas.Knowledge.residueAbsoluteFrobeniusEquivIn` and the residue
action on representatives — the realization formula
`Atlas.Knowledge.finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply`
carries the congruence onto the embedded copy of `L`, and a
unit-pullback argument (a unit of the integral closure has invertible
image in the absolute valuation ring) lands it in the radical
downstairs. For the first theorem the congruence *is* membership in
`G_0`, so the concrete hypothesis closes the proof where the source
needed residue-map injectivity; the direction of the hypotheses is
reversed against the layer's
`Atlas.Knowledge.lowerRamificationGroup_eq_bot_of_isUnramified`, whose
cardinality route is independent of this file. For the second, the
source equates the realization with its *constructed*
`arithmeticFrobeniusOfUnramifiedValuation` and so consumes
unramifiedness again; the layer's `IsArithmeticFrobenius` is a
predicate, the congruence holds for the realization unconditionally,
and with the first theorem plus
`Atlas.Knowledge.isArithmeticFrobenius_unique` the trivial-inertia
hypothesis pins the realization as *the* arithmetic Frobenius. The
ambient conversion of the arc applies: the source's pinned
`SeparableClosure K` becomes `AlgebraicClosure K`, on which the local
degree datum lives. The residue coordinates' Galois enrichment is
re-registered as local instances exactly as in
`Atlas.Knowledge.ResidueDatumIn`.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at
  www.jmilne.org/math/, 2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

noncomputable section

universe u

section AmbientBase

variable (K : Type u) [Field K]

/-- **The packaged ambient base has residue degree one** for every
degree datum: its subgroup is the base field's, and the base field's
residue quotient is trivial (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedComparison.lean:45`,
at the layer's ambient base). -/
theorem galoisAmbientFiniteAbstractBase_residueDegree_eq_one
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (D : DegreeData (Ω ≃ₐ[K] Ω)) :
    (galoisAmbientFiniteAbstractBase K Ω).residueDegree D = 1 := by
  rw [FiniteAbstractField.eq_of_field_eq
    (galoisAmbientFiniteAbstractBase K Ω)
    (FiniteAbstractField.base (Ω ≃ₐ[K] Ω))
    (closedFixingSubgroup_bot_eq_baseField K Ω)]
  exact FiniteAbstractField.base_residueDegree D

end AmbientBase

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/- The residue coordinates of the local datum form a Galois pair —
`Atlas.Knowledge.ResidueDatumIn`'s enrichment, re-registered at the
local field's coordinates for the Frobenius-parameter
statements below. -/
local instance :
    IsAlgClosure
      (decompositionResidueField K (localAbsoluteValuationSubring K))
      (selectedResidueField (localAbsoluteValuationSubring K)) :=
  ⟨inferInstance, inferInstance⟩

local instance :
    IsGalois
      (decompositionResidueField K (localAbsoluteValuationSubring K))
      (selectedResidueField (localAbsoluteValuationSubring K)) :=
  inferInstance

/- The whole-group residue action computes on representatives, in the
local datum's spelling. -/
private theorem localResidueAlgAction_residue
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (a : localAbsoluteValuationSubring K) :
    localResidueAlgAction K g
        (IsLocalRing.residue (localAbsoluteValuationSubring K) a) =
      IsLocalRing.residue (localAbsoluteValuationSubring K)
        (toDecompositionGroupOfEqTop K (localAbsoluteValuationSubring K)
          (localAbsoluteDecompositionGroup_eq_top K) g • a) :=
  decompositionGroupResidueAction_residue (K := K)
    (localAbsoluteValuationSubring K)
    (toDecompositionGroupOfEqTop K (localAbsoluteValuationSubring K)
      (localAbsoluteDecompositionGroup_eq_top K) g) a

/- An absolute Galois element acts on the selected residue closure as
the Frobenius power its local residue degree names — the inverse law of
the Frobenius-parameter isomorphism (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedComparison.lean:95`,
for arbitrary parameter). -/
private theorem localResidueAlgAction_eq_frobenius_of_degree
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (z : ProfiniteIntegerMul) (hg : localResidueDegree K g = z) :
    localResidueAlgAction K g =
      residueAbsoluteFrobenius
        (decompositionResidueField K (localAbsoluteValuationSubring K))
        (selectedResidueField (localAbsoluteValuationSubring K)) z := by
  have h2 :
      residueAbsoluteFrobeniusEquivIn
          (decompositionResidueField K (localAbsoluteValuationSubring K))
          (selectedResidueField (localAbsoluteValuationSubring K))
          (localResidueDegree K g) =
        localResidueAlgAction K g :=
    (residueAbsoluteFrobeniusEquivIn
      (decompositionResidueField K (localAbsoluteValuationSubring K))
      (selectedResidueField
        (localAbsoluteValuationSubring K))).toMulEquiv.apply_symm_apply
      (localResidueAlgAction K g)
  rw [hg] at h2
  exact h2.symm

/- Trivial residue degree moves every integral element within the
maximal ideal: the action is the zeroth Frobenius power, the identity
on residues. -/
private theorem smul_sub_mem_maximalIdeal_of_localResidueDegree_eq_one
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hg : localResidueDegree K g = 1)
    (a : localAbsoluteValuationSubring K) :
    toDecompositionGroupOfEqTop K (localAbsoluteValuationSubring K)
        (localAbsoluteDecompositionGroup_eq_top K) g • a - a ∈
      IsLocalRing.maximalIdeal (localAbsoluteValuationSubring K) := by
  have hact := localResidueAlgAction_eq_frobenius_of_degree K g 1 hg
  rw [map_one] at hact
  have h1 := localResidueAlgAction_residue K g a
  rw [hact, AlgEquiv.one_apply] at h1
  have h3 : IsLocalRing.residue (localAbsoluteValuationSubring K)
      (toDecompositionGroupOfEqTop K (localAbsoluteValuationSubring K)
        (localAbsoluteDecompositionGroup_eq_top K) g • a - a) = 0 := by
    rw [map_sub, ← h1, sub_self]
  exact Ideal.Quotient.eq_zero_iff_mem.mp h3

/- Residue degree one is the substitution congruence on the absolute
valuation ring: the action is the arithmetic Frobenius, the `q`-th
power on residues ([Milne 2020, Chap. I, §1, p.20][MilneCFT]). -/
private theorem
    smul_sub_pow_card_mem_maximalIdeal_of_localResidueDegree_eq_ofAdd_one
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hg : localResidueDegree K g =
      Multiplicative.ofAdd (1 : ProfiniteInteger))
    (a : localAbsoluteValuationSubring K) :
    toDecompositionGroupOfEqTop K (localAbsoluteValuationSubring K)
        (localAbsoluteDecompositionGroup_eq_top K) g • a -
        a ^ Nat.card 𝓀[K] ∈
      IsLocalRing.maximalIdeal (localAbsoluteValuationSubring K) := by
  have hact := localResidueAlgAction_eq_frobenius_of_degree K g
    (Multiplicative.ofAdd (1 : ProfiniteInteger)) hg
  rw [residueAbsoluteFrobenius_one] at hact
  have h1 := localResidueAlgAction_residue K g a
  rw [hact] at h1
  have h2 : IsLocalRing.residue (localAbsoluteValuationSubring K) a ^
      Fintype.card
        (decompositionResidueField K (localAbsoluteValuationSubring K)) =
      IsLocalRing.residue (localAbsoluteValuationSubring K)
        (toDecompositionGroupOfEqTop K (localAbsoluteValuationSubring K)
          (localAbsoluteDecompositionGroup_eq_top K) g • a) := by
    rw [← h1]
    rfl
  have hcard : Fintype.card
      (decompositionResidueField K (localAbsoluteValuationSubring K)) =
      Nat.card 𝓀[K] := by
    rw [← Nat.card_eq_fintype_card]
    exact (Nat.card_congr
      (localBaseResidueEquivDecompositionResidue K).toEquiv).symm
  have h3 : IsLocalRing.residue (localAbsoluteValuationSubring K)
      (toDecompositionGroupOfEqTop K (localAbsoluteValuationSubring K)
        (localAbsoluteDecompositionGroup_eq_top K) g • a -
        a ^ Nat.card 𝓀[K]) = 0 := by
    rw [map_sub, map_pow, ← hcard, h2, sub_self]
  exact Ideal.Quotient.eq_zero_iff_mem.mp h3

variable (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L]

/- The congruence transfer: a base-subgroup element whose action on the
absolute valuation ring is an `m`-th-power congruence realizes, through
the chosen quotient equivalence, to an automorphism satisfying the same
congruence on the integral closure — by the realization formula and the
unit-pullback argument. -/
private theorem galRestrict_realization_sub_pow_mem_maximalIdeal
    (i : L →ₐ[K] AlgebraicClosure K)
    (tau : (closedFixingSubgroup
      (⊥ : IntermediateField K (AlgebraicClosure K))).toSubgroup)
    (m : ℕ)
    (hcong : ∀ a : localAbsoluteValuationSubring K,
      toDecompositionGroupOfEqTop K (localAbsoluteValuationSubring K)
          (localAbsoluteDecompositionGroup_eq_top K) tau.1 • a - a ^ m ∈
        IsLocalRing.maximalIdeal (localAbsoluteValuationSubring K))
    (x : integralClosure 𝒪[K] L) :
    galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L)
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
          (AlgebraicClosure K) i (QuotientGroup.mk tau)) x - x ^ m ∈
      IsLocalRing.maximalIdeal (integralClosure 𝒪[K] L) := by
  have hint : ∀ y : integralClosure 𝒪[K] L,
      i (y : L) ∈ localAbsoluteValuationSubring K := by
    intro y
    rw [mem_localAbsoluteValuationSubring_iff]
    exact IsIntegral.map (AlgHom.restrictScalars 𝒪[K] i) y.2
  -- the image of the moved difference is the congruence defect in `A`
  have him : i ((galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L)
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
          (AlgebraicClosure K) i (QuotientGroup.mk tau)) x - x ^ m :
        integralClosure 𝒪[K] L) : L) =
      ((toDecompositionGroupOfEqTop K (localAbsoluteValuationSubring K)
          (localAbsoluteDecompositionGroup_eq_top K) tau.1 •
          (⟨i (x : L), hint x⟩ : localAbsoluteValuationSubring K) -
          (⟨i (x : L), hint x⟩ : localAbsoluteValuationSubring K) ^ m :
        localAbsoluteValuationSubring K) : AlgebraicClosure K) := by
    have hcoe : ((galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L)
          (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
            (AlgebraicClosure K) i (QuotientGroup.mk tau)) x - x ^ m :
          integralClosure 𝒪[K] L) : L) =
        (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L)
          (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
            (AlgebraicClosure K) i (QuotientGroup.mk tau)) x : L) -
          (x : L) ^ m := by
      push_cast
      ring
    rw [hcoe, map_sub, map_pow]
    have hgal : i ((galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L)
          (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
            (AlgebraicClosure K) i (QuotientGroup.mk tau)) x : L)) =
        tau.1 (i (x : L)) := by
      have h1 : ((galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L)
            (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
              (AlgebraicClosure K) i (QuotientGroup.mk tau)) x : L)) =
          finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
            (AlgebraicClosure K) i (QuotientGroup.mk tau) (x : L) :=
        algebraMap_galRestrict_apply 𝒪[K]
          (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
            (AlgebraicClosure K) i (QuotientGroup.mk tau)) x
      rw [h1]
      exact finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
        K (AlgebraicClosure K) L i tau (x : L)
    rw [hgal]
    rfl
  -- were the difference a unit downstairs, its image would be a unit
  -- of `A`, against the congruence hypothesis
  by_contra hnot
  have hunit : IsUnit (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L)
      (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
        (AlgebraicClosure K) i (QuotientGroup.mk tau)) x - x ^ m) := by
    by_contra hnotunit
    exact hnot ((IsLocalRing.mem_maximalIdeal _).mpr
      (mem_nonunits_iff.mpr hnotunit))
  obtain ⟨w, hw⟩ := hunit
  have haYZ : (⟨i ((w : integralClosure 𝒪[K] L) : L),
        hint w⟩ : localAbsoluteValuationSubring K) *
      ⟨i (((w⁻¹ : (integralClosure 𝒪[K] L)ˣ) :
        integralClosure 𝒪[K] L) : L), hint _⟩ = 1 := by
    apply Subtype.ext
    have hcalc : i ((w : integralClosure 𝒪[K] L) : L) *
        i (((w⁻¹ : (integralClosure 𝒪[K] L)ˣ) :
          integralClosure 𝒪[K] L) : L) =
        i (((w * w⁻¹ : (integralClosure 𝒪[K] L)ˣ) :
          integralClosure 𝒪[K] L) : L) := by
      rw [← map_mul]
      norm_cast
    calc ((⟨i ((w : integralClosure 𝒪[K] L) : L),
            hint w⟩ : localAbsoluteValuationSubring K) *
          ⟨i (((w⁻¹ : (integralClosure 𝒪[K] L)ˣ) :
            integralClosure 𝒪[K] L) : L), hint _⟩ :
          localAbsoluteValuationSubring K).1 =
        i ((w : integralClosure 𝒪[K] L) : L) *
          i (((w⁻¹ : (integralClosure 𝒪[K] L)ˣ) :
            integralClosure 𝒪[K] L) : L) := rfl
      _ = i (((w * w⁻¹ : (integralClosure 𝒪[K] L)ˣ) :
            integralClosure 𝒪[K] L) : L) := hcalc
      _ = 1 := by rw [mul_inv_cancel]; simp
  have hunitA : IsUnit (⟨i ((w : integralClosure 𝒪[K] L) : L),
      hint w⟩ : localAbsoluteValuationSubring K) :=
    IsUnit.of_mul_eq_one _ haYZ
  have haY_eq : (⟨i ((w : integralClosure 𝒪[K] L) : L), hint w⟩ :
        localAbsoluteValuationSubring K) =
      toDecompositionGroupOfEqTop K (localAbsoluteValuationSubring K)
          (localAbsoluteDecompositionGroup_eq_top K) tau.1 •
          (⟨i (x : L), hint x⟩ : localAbsoluteValuationSubring K) -
        (⟨i (x : L), hint x⟩ : localAbsoluteValuationSubring K) ^ m := by
    apply Subtype.ext
    calc (i ((w : integralClosure 𝒪[K] L) : L) : AlgebraicClosure K) =
        i ((galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L)
          (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
            (AlgebraicClosure K) i (QuotientGroup.mk tau)) x - x ^ m :
          integralClosure 𝒪[K] L) : L) := by rw [hw]
      _ = _ := him
  rw [haY_eq] at hunitA
  exact mem_nonunits_iff.mp
    ((IsLocalRing.mem_maximalIdeal _).mp (hcong _)) hunitA

/-- **Trivial concrete inertia gives abstract unramifiedness**: a
finite Galois extension with `lowerRamificationGroup K L 0 = ⊥`,
realized in the algebraic closure through any embedding, is an
unramified extension of the local degree datum — the opposite
direction, on realizations, to
`Atlas.Knowledge.lowerRamificationGroup_eq_bot_of_isUnramified`
(Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedComparison.lean:291`). -/
theorem finiteGaloisAbstractExtensionOfEmbedding_isUnramified
    (i : L →ₐ[K] AlgebraicClosure K)
    (h : lowerRamificationGroup K L 0 = ⊥) :
    (finiteGaloisAbstractExtensionOfEmbedding K L
      (AlgebraicClosure K) i).IsUnramified (localResidueDatum K) := by
  refine ((finiteGaloisAbstractExtensionOfEmbedding K L (AlgebraicClosure K)
    i).toFiniteAbstractExtension.isUnramified_iff_inertia_le
      (localResidueDatum K)).mpr ?_
  intro g hg
  have hg1 : g ∈ (closedFixingSubgroup
      (⊥ : IntermediateField K (AlgebraicClosure K))).toSubgroup := hg.1
  have hg2 : localResidueDegree K g = 1 := hg.2
  -- the realized automorphism lies in the trivial inertia group
  have hq : finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
      (AlgebraicClosure K) i (QuotientGroup.mk ⟨g, hg1⟩) = 1 := by
    have hmem : finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
        (AlgebraicClosure K) i (QuotientGroup.mk ⟨g, hg1⟩) ∈
        lowerRamificationGroup K L 0 := by
      rw [mem_lowerRamificationGroup_iff]
      intro x
      rw [show ((0 : ℤ) + 1).toNat = 1 by norm_num, pow_one,
        integralClosure_jacobson_bot_eq_maximalIdeal K L]
      have hstep := galRestrict_realization_sub_pow_mem_maximalIdeal K L i
        ⟨g, hg1⟩ 1
        (fun a => by
          simpa using
            smul_sub_mem_maximalIdeal_of_localResidueDegree_eq_one
              K g hg2 a) x
      simpa using hstep
    rw [h, Subgroup.mem_bot] at hmem
    exact hmem
  -- hence the element fixes the embedded copy of `L` pointwise
  change g ∈ (finiteGaloisFieldRangeOfEmbedding K L
    (AlgebraicClosure K) i).fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro z hz
  obtain ⟨x, rfl⟩ := hz
  have hx := finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
    K (AlgebraicClosure K) L i ⟨g, hg1⟩ x
  rw [hq] at hx
  simpa using hx.symm

/-- **The abstract degree-one unramified Frobenius of a realization, as
an actual automorphism**: the restriction of the chosen degree-one
lift, carried through the chosen quotient equivalence — the realized
element of the source's comparison theorem, here named (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedComparison.lean:353`,
its left-hand side). -/
def unramifiedFrobeniusRealizationOfEmbedding
    (i : L →ₐ[K] AlgebraicClosure K) : L ≃ₐ[K] L :=
  finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
    (AlgebraicClosure K) i
    ((localResidueDatum K).unramifiedFrobenius
      (hnormal := finiteGaloisExtensionSubgroupOfEmbedding_normal K L
        (AlgebraicClosure K) i)
      ((galoisAmbientFiniteAbstractBase K
        (AlgebraicClosure K)).toFiniteResidueAbstractField
          (localResidueDatum K))
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L
        (AlgebraicClosure K) i)
      (finiteGaloisAbstractExtensionOfEmbedding K L
        (AlgebraicClosure K) i).below)

/- The chosen degree-one lift has local residue degree one exactly: the
normalized degree divides by the base residue degree, which is one
(Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedComparison.lean:81`). -/
private theorem localResidueDegree_chosenUnramifiedFrobeniusLift :
    localResidueDegree K
      (Classical.choose
        ((localResidueDatum K).normalizedDegree_surjective
          ((galoisAmbientFiniteAbstractBase K
            (AlgebraicClosure K)).toFiniteResidueAbstractField
              (localResidueDatum K))
          (Multiplicative.ofAdd (1 : ProfiniteInteger)))).1 =
      Multiplicative.ofAdd (1 : ProfiniteInteger) := by
  have hφ := Classical.choose_spec
    ((localResidueDatum K).normalizedDegree_surjective
      ((galoisAmbientFiniteAbstractBase K
        (AlgebraicClosure K)).toFiniteResidueAbstractField
          (localResidueDatum K))
      (Multiplicative.ofAdd (1 : ProfiniteInteger)))
  have h := (localResidueDatum K).residueDegree_nsmul_normalizedDegree
    ((galoisAmbientFiniteAbstractBase K
      (AlgebraicClosure K)).toFiniteResidueAbstractField
        (localResidueDatum K))
    (Classical.choose
      ((localResidueDatum K).normalizedDegree_surjective
        ((galoisAmbientFiniteAbstractBase K
          (AlgebraicClosure K)).toFiniteResidueAbstractField
            (localResidueDatum K))
        (Multiplicative.ofAdd (1 : ProfiniteInteger))))
  rw [hφ] at h
  have h1 : ((((galoisAmbientFiniteAbstractBase K
      (AlgebraicClosure K)).toFiniteResidueAbstractField
        (localResidueDatum K)).residueDegree : ℕ)) = 1 := by
    have h2 : ((galoisAmbientFiniteAbstractBase K
        (AlgebraicClosure K)).residueDegree (localResidueDatum K) : ℕ) =
        1 := by
      rw [galoisAmbientFiniteAbstractBase_residueDegree_eq_one K
        (AlgebraicClosure K) (localResidueDatum K)]
      rfl
    exact h2
  -- the mixed group spellings refuse `rw`; substitute the scalar by a
  -- term-level congruence instead
  have h2 := congrArg
    (fun n : ℕ => n • Multiplicative.toAdd
      (Multiplicative.ofAdd (1 : ProfiniteInteger))) h1
  apply Multiplicative.toAdd.injective
  calc Multiplicative.toAdd (localResidueDegree K
        (Classical.choose
          ((localResidueDatum K).normalizedDegree_surjective
            ((galoisAmbientFiniteAbstractBase K
              (AlgebraicClosure K)).toFiniteResidueAbstractField
                (localResidueDatum K))
            (Multiplicative.ofAdd (1 : ProfiniteInteger)))).1)
      = ((((galoisAmbientFiniteAbstractBase K
            (AlgebraicClosure K)).toFiniteResidueAbstractField
              (localResidueDatum K)).residueDegree : ℕ)) •
          Multiplicative.toAdd
            (Multiplicative.ofAdd (1 : ProfiniteInteger)) := h.symm
    _ = (1 : ℕ) • Multiplicative.toAdd
          (Multiplicative.ofAdd (1 : ProfiniteInteger)) := h2
    _ = Multiplicative.toAdd
          (Multiplicative.ofAdd (1 : ProfiniteInteger)) := one_nsmul _

/-- **The realized abstract Frobenius is an arithmetic Frobenius**: the
degree-one lift acts on the absolute valuation ring by the substitution
congruence, and the realization carries the congruence onto the
integral closure — no unramifiedness enters, the layer's
predicate-style rendering of the source's identification with its
constructed Frobenius; under `lowerRamificationGroup K L 0 = ⊥` the
identification is completed by
`Atlas.Knowledge.isArithmeticFrobenius_unique`
([Milne 2020, Chap. I, §1, p.20][MilneCFT]; Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedComparison.lean:353`). -/
theorem isArithmeticFrobenius_unramifiedFrobeniusRealizationOfEmbedding
    (i : L →ₐ[K] AlgebraicClosure K) :
    IsArithmeticFrobenius K L
      (unramifiedFrobeniusRealizationOfEmbedding K L i) := by
  intro x
  rw [integralClosure_jacobson_bot_eq_maximalIdeal K L]
  exact galRestrict_realization_sub_pow_mem_maximalIdeal K L i
    (Classical.choose
      ((localResidueDatum K).normalizedDegree_surjective
        ((galoisAmbientFiniteAbstractBase K
          (AlgebraicClosure K)).toFiniteResidueAbstractField
            (localResidueDatum K))
        (Multiplicative.ofAdd (1 : ProfiniteInteger))))
    (Nat.card 𝓀[K])
    (fun a =>
      smul_sub_pow_card_mem_maximalIdeal_of_localResidueDegree_eq_ofAdd_one
        K _ (localResidueDegree_chosenUnramifiedFrobeniusLift K) a) x

/-- Embedding-independence of the realized abstract Frobenius: under
trivial inertia any two embeddings realize the same automorphism, both
being arithmetic Frobenii — immediate here, where the source realizes
each embedding as the same constructed Frobenius (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedComparison.lean:353`). -/
theorem unramifiedFrobeniusRealizationOfEmbedding_eq
    (i j : L →ₐ[K] AlgebraicClosure K)
    (h : lowerRamificationGroup K L 0 = ⊥) :
    unramifiedFrobeniusRealizationOfEmbedding K L i =
      unramifiedFrobeniusRealizationOfEmbedding K L j :=
  isArithmeticFrobenius_unique K L h
    (isArithmeticFrobenius_unramifiedFrobeniusRealizationOfEmbedding K L i)
    (isArithmeticFrobenius_unramifiedFrobeniusRealizationOfEmbedding K L j)

end

end Atlas.Knowledge
