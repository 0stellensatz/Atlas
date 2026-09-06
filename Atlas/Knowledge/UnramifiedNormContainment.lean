import Mathlib
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteAbstractFieldExtension
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.FiniteResidueAbstractExtension
import Atlas.Knowledge.IntermediateFieldNormResidueNaturality
import Atlas.Knowledge.IntermediateFieldUnitsFixedSubgroup
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.LocalAbstractPrimeFieldUnit
import Atlas.Knowledge.LocalHenselianValuation
import Atlas.Knowledge.LocalResidueDatum
import Atlas.Knowledge.NormTopology
import Atlas.Knowledge.NormalizedValuation
import Atlas.Knowledge.NormalizedValuationLaws
import Atlas.Knowledge.ProfiniteInteger
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.RelativeNormLaws
import Atlas.Knowledge.ResidueDatumIn
import Atlas.Knowledge.SeparableFixedFieldNorm
import Atlas.Knowledge.UnramifiedExtensionOfDegree
import Atlas.Knowledge.ValuationData

/-!
# unramified norm containment

The norm subgroup of the abstract unramified extension of degree `d`
over the algebraic closure of a mixed-characteristic local field `K`,
transported back to `Kˣ`, consists of elements whose normalized
valuation is divisible by `d` (#104): a norm from an extension of
residue degree `d` has valuation `d` times a valuation, by the
valuation datum's tower law, and the layer's local valuation reads a
transported base unit's abstract valuation as its normalized valuation.
The unramified half of the standard subgroup `⟨πᵈ⟩ ⊔ U^{(i)}` in the
existence theorem's Lubin–Tate route.

## Main statements

* `finiteUnramifiedNormSubgroup_map_le_comap_normalizedValuationHom` —
  the transported norm subgroup of the degree-`d` unramified extension
  has valuations divisible by `d`; proved.

## Implementation notes

The ambient is the algebraic closure, where the layer's local data live
— `Atlas.Knowledge.localResidueDatum`,
`Atlas.Knowledge.localHenselianValuation`, and
`Atlas.Knowledge.localHenselianValuation_valuationAt_baseUnit`, which
reads the abstract valuation of a transported base unit as the
normalized valuation directly, so the source's two private transport
lemmas through `intrinsicAbstractBase = baseField` are not needed. The
unramified norm subgroup is spelled
`Subgroup.comap (normalizedValuationHom K) (Subgroup.zpowers (Multiplicative.ofAdd (d : ℤ)))`,
the form of `Atlas.Knowledge.unramifiedNormRange`, where the source
packages it as `unramifiedNormSubgroup K d` through its
`valuationModDegree`, so its `mem_unramifiedNormSubgroup_iff` step
becomes `Subgroup.mem_comap` and `Subgroup.mem_zpowers_iff`. That
subgroup is the source's although the layer's
`Atlas.Knowledge.normalizedValuation` is the negation of the source's
`valuationMap` — the convention fork
`Atlas.Knowledge.NormalizedValuation` records — because divisibility by
`d` is invariant under negation; for `d = 1` it is all of `Kˣ`, as in
the source. The degree-`d` extension is
`Atlas.Knowledge.UnramifiedExtensionOfDegree`'s, with `NeZero d` for
the source's `0 < d`; the reduction of the profinite integers is
`Atlas.Knowledge.ProfiniteInteger.reduction`, its integer cast
`reduction_intCast`; the residue-degree tower law is
`Atlas.Knowledge.normalizedValuation_tower`, the residue degree read
through `toFiniteResidueAbstractExtension` as that law states it where
the source writes `EU.residueDegree D`; and the relative subgroup is
the layer's `Subgroup.subgroupOf` spelling. The local field is
`IsMixedCharLocalField` where the source's is nonarchimedean, a
narrowing to the layer's standing class, and the source's `Type` is the
layer's `Type u`. The file is the source's
`LocalClassFieldTheory/Finite/Existence/UnramifiedNormContainment.lean:78`
in that vocabulary; the source's remaining declarations there — the
existential packagings `:205` and `:271`, and the local abelian
subextension `:231` with its containment `:244` — are absorbed by the
consumer `Atlas.Knowledge.LocalNormSubgroupExistence`.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

/-- **The norm subgroup of the canonical unramified extension of degree `d`**,
transported from the fixed coefficients to `Kˣ`, is contained in the
subgroup of elements whose normalized valuation is divisible by `d`
(Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/UnramifiedNormContainment.lean:78`). -/
theorem finiteUnramifiedNormSubgroup_map_le_comap_normalizedValuationHom
    (d : ℕ) [NeZero d] :
    let D := localResidueDatum K
    let Kfinite := galoisAmbientFiniteAbstractBase K (AlgebraicClosure K)
    let Kresidue := Kfinite.toFiniteResidueAbstractField D
    let U := D.finiteUnramifiedExtension Kresidue d
    (FiniteGaloisSubextension.normSubgroup (galoisAmbientUnitsRep K (AlgebraicClosure K)) U).map
        (baseUnitsEquivGaloisAmbientFixed K (AlgebraicClosure K)).symm.toAddMonoidHom ≤
      (Subgroup.comap (normalizedValuationHom K)
        (Subgroup.zpowers (Multiplicative.ofAdd (d : ℤ)))).toAddSubgroup := by
  let G := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K
  let A := galoisAmbientUnitsRep K (AlgebraicClosure K)
  let D := localResidueDatum K
  let v := localHenselianValuation K
  let K₀ := closedFixingSubgroup (⊥ : IntermediateField K (AlgebraicClosure K))
  let Kfinite : FiniteAbstractField G := galoisAmbientFiniteAbstractBase K (AlgebraicClosure K)
  let Kresidue := Kfinite.toFiniteResidueAbstractField D
  let U : FiniteGaloisSubextension K₀ := D.finiteUnramifiedExtension Kresidue d
  let e := baseUnitsEquivGaloisAmbientFixed K (AlgebraicClosure K)
  dsimp only
  letI hUfinite : Finite (K₀.toSubgroup ⧸ U.field.toSubgroup.subgroupOf K₀.toSubgroup) :=
    U.finite
  letI hK₀finite : Finite
      ((baseField G).toSubgroup ⧸ K₀.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    Kfinite.finite
  letI hUabsoluteFinite : Finite
      ((baseField G).toSubgroup ⧸ U.field.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    relativeTowerQuotientFinite (baseField G) K₀ U.field U.below (le_baseField K₀)
  let Ufinite : FiniteAbstractField G := ⟨U.field, hUabsoluteFinite⟩
  let EU : FiniteAbstractFieldExtension G :=
    { field := Ufinite
      base := Kfinite
      below := U.below
      finiteQuotient := U.finite }
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  change y ∈ FiniteGaloisSubextension.normSubgroup A U at hy
  rcases hy with ⟨a, rfl⟩
  have hres : ((EU.toFiniteResidueAbstractExtension D).residueDegree : ℕ) = d := by
    have h := D.finiteUnramifiedExtension_residueDegree Kresidue d
    change ((EU.toFiniteResidueAbstractExtension D).residueDegree : ℕ) = d at h
    exact h
  have hvaluation :
      ((v.valuationAt Kfinite (relativeNorm A K₀ U.field U.below a) : v.valueGroup) :
          ProfiniteInteger) =
        d • ((v.valuationAt Ufinite a : v.valueGroup) : ProfiniteInteger) := by
    rw [← hres]
    exact (v.normalizedValuation_tower EU a).symm
  set nv : ℤ := normalizedValuation K
    (Additive.toMul (e.symm (relativeNorm A K₀ U.field U.below a))) with hnvdef
  have hnative :
      ((v.valuationAt Kfinite (relativeNorm A K₀ U.field U.below a) : v.valueGroup) :
          ProfiniteInteger) = Int.castRingHom ProfiniteInteger nv := by
    have h := localHenselianValuation_valuationAt_baseUnit K
      (Additive.toMul (e.symm (relativeNorm A K₀ U.field U.below a)))
    rw [ofMul_toMul, AddEquiv.apply_symm_apply] at h
    exact h
  have hzero : (nv : ZMod d) = 0 := by
    have h1 : ProfiniteInteger.reduction d (Int.castRingHom ProfiniteInteger nv) = (nv : ZMod d) :=
      ProfiniteInteger.reduction_intCast d nv
    rw [← h1, ← hnative, hvaluation, map_nsmul]
    simp
  have hdvd : (d : ℤ) ∣ nv := (ZMod.intCast_zmod_eq_zero_iff_dvd nv d).1 hzero
  obtain ⟨k, hk⟩ := hdvd
  change Additive.toMul (e.symm (relativeNorm A K₀ U.field U.below a)) ∈
    Subgroup.comap (normalizedValuationHom K) (Subgroup.zpowers (Multiplicative.ofAdd (d : ℤ)))
  rw [Subgroup.mem_comap, Subgroup.mem_zpowers_iff]
  refine ⟨k, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_normalizedValuationHom, toAdd_zpow, toAdd_ofAdd, ← hnvdef, hk]
  ring

end

end Atlas.Knowledge
