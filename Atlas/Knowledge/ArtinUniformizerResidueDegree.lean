import Mathlib
import Atlas.Knowledge.LocalReciprocityPowerAction
import Atlas.Knowledge.LocalResidueDatum
import Atlas.Knowledge.ValuationResidueRootOfUnityLift

/-!
# residue degree of an Artin uniformizer

Every absolute Artin lift of a unit of normalized valuation one has residue degree one.
Its power action on roots of unity determines its entire residue action: every nonzero
element of the algebraic residue closure lies in a finite field and lifts to a root of unity.

## Main statements

* `IsLocalReciprocity.residueDegree_of_valuation_one` — an Artin uniformizer has residue
  degree one.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/-- An absolute Artin lift at normalized valuation one has arithmetic residue degree one
([Serre 1979, Chap. XIII, §4, Prop. 13, p.197][Serre1979]). -/
theorem IsLocalReciprocity.residueDegree_of_valuation_one
    {φ : Kˣ →* Field.absoluteGaloisGroupAbelianization K} (hφ : IsLocalReciprocity K φ)
    (x : Kˣ) (hval : normalizedValuation K x = 1)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hσ : (QuotientGroup.mk σ : Field.absoluteGaloisGroupAbelianization K) = φ x) :
    localResidueDegree K σ = Multiplicative.ofAdd (1 : ProfiniteInteger) := by
  classical
  let A := localAbsoluteValuationSubring K
  let k := decompositionResidueField K A
  let Ω := selectedResidueField A
  have hq : Fintype.card k = Nat.card 𝓀[K] :=
    (Fintype.card_eq_nat_card).trans
      (Nat.card_congr (localBaseResidueEquivDecompositionResidue K).toEquiv).symm
  have haction : localResidueAlgAction K σ =
      FiniteField.frobeniusAlgEquivOfAlgebraic k Ω := by
    ext z
    change localResidueAlgAction K σ z = z ^ Fintype.card k
    rw [hq]
    by_cases hz0 : z = 0
    · rw [hz0, map_zero, zero_pow (by have := Finite.one_lt_card (α := 𝓀[K]); omega)]
    let T := IntermediateField.adjoin k ({z} : Set Ω)
    letI : FiniteDimensional k T :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
    letI : Finite T := Module.finite_of_finite k
    letI : Fintype T := Fintype.ofFinite T
    let d := Module.finrank k T
    have hd : 0 < d := Module.finrank_pos
    have hcard : Fintype.card T = Nat.card 𝓀[K] ^ d := by
      rw [Module.card_eq_pow_finrank (K := k), hq]
    let m := Fintype.card T - 1
    have hcardpos : 1 < Fintype.card T := Fintype.one_lt_card
    have hm0 : m ≠ 0 := by omega
    have hmadd : m + 1 = Fintype.card T := by omega
    have hm : Nat.Coprime m (Nat.card 𝓀[K]) := by
      have h : Nat.Coprime m (m + 1) :=
        Nat.coprime_self_add_right.mpr (Nat.coprime_one_right m)
      rw [hmadd, hcard] at h
      exact h.coprime_dvd_right (dvd_pow_self _ hd.ne')
    let zT : T := ⟨z, IntermediateField.subset_adjoin _ _ (Set.mem_singleton z)⟩
    have hzT : zT ≠ 0 := fun h => hz0 (congrArg Subtype.val h)
    have hzm : z ^ m = 1 :=
      congrArg Subtype.val (FiniteField.pow_card_sub_one_eq_one zT hzT)
    obtain ⟨a, ha, hred⟩ := valuationResidueRootOfUnityLift A hm0 z hzm
    have hapow : (a : AlgebraicClosure K) ^ m = 1 := congrArg Subtype.val ha
    have hσa : σ (a : AlgebraicClosure K) = (a : AlgebraicClosure K) ^ Nat.card 𝓀[K] := by
      simpa only [pow_one] using
        hφ.frobenius_of_normalizedValuation_eq_nat K x 1 hval σ hσ m hm a hapow
    have hsmul : toDecompositionGroupOfEqTop K A
        (localAbsoluteDecompositionGroup_eq_top K) σ • a = a ^ Nat.card 𝓀[K] :=
      Subtype.ext hσa
    rw [← hred]
    exact (decompositionGroupResidueAction_residue (K := K) A
      (toDecompositionGroupOfEqTop K A (localAbsoluteDecompositionGroup_eq_top K) σ) a).trans
        ((congrArg (IsLocalRing.residue A) hsmul).trans (map_pow _ _ _))
  change residueAbsoluteDegreeIn k Ω (localResidueAlgAction K σ) = _
  rw [haction, residueAbsoluteDegreeIn_frobenius]

end Atlas.Knowledge
