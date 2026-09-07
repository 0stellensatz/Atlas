import Mathlib
import Atlas.Knowledge.AbelianLocalArtinMonoidHom
import Atlas.Knowledge.AbsoluteAbelianRestriction
import Atlas.Knowledge.AbsoluteFiniteQuotientEquiv
import Atlas.Knowledge.AbsoluteLocalArtinMonoidHom
import Atlas.Knowledge.AbsoluteLocalArtinRestriction
import Atlas.Knowledge.FiniteExtensionIsMixedCharLocalField
import Atlas.Knowledge.IntegralClosureDVR
import Atlas.Knowledge.IsArithmeticFrobenius
import Atlas.Knowledge.IsFrobeniusNormalizedAbelianLocalArtinMonoidHom
import Atlas.Knowledge.IsLocalHilbertSymbol
import Atlas.Knowledge.IsLocalReciprocity
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.KummerField
import Atlas.Knowledge.KummerFieldLowerRamificationGroupEqBot
import Atlas.Knowledge.LowerRamificationGroup
import Atlas.Knowledge.NormalizedValuation
import Atlas.Knowledge.RationalIntegerValuation
import Atlas.Knowledge.ValuationEqOneOfPowEqOne

/-!
# tame Hilbert symbol of a unit against a uniformizer

The one computation behind the tame formula: for a unit `u`, a uniformizer `ϖ`, and `n` a
unit of the integers with `K` holding the `n`-th roots of unity, the Hilbert symbol `(u, ϖ)`
is congruent to `u ^ ((q - 1) / n)` modulo the maximal ideal — Serre's `P_n (ū)`, the power
residue symbol of the residue field. Every lift of the reciprocity class of `ϖ` restricts to
the Kummer field `K (u ^ (1 / n))`, unramified by
`Atlas.Knowledge.KummerFieldLowerRamificationGroupEqBot`, as the arithmetic Frobenius; the
Frobenius congruence `σ z ≡ z ^ q` at a root `z` of `u`, with `σ z = (u, ϖ) · z` by the
characterization of the symbol and `z ^ (q - 1) = u ^ ((q - 1) / n)`, gives the congruence,
which contracts from the closure's maximal ideal to the base's.
`Atlas.Knowledge.LocalHilbertSymbolTameFormula` assembles the general formula from this case
by bimultiplicativity and skew-symmetry.

## Main statements

* `localHilbertSymbol_unit_uniformizer` — `valuation K ((u, ϖ) - u ^ ((q - 1) / n)) < 1`;
  proved.
* `sub_pow_mem_maximalIdeal_of_isArithmeticFrobenius` — over any finite extension, an
  arithmetic Frobenius moving a tame root of a unit by a base scalar pins that scalar modulo
  the maximal ideal; proved.
* `mem_maximalIdeal_of_algebraMap_mem` — the closure's maximal ideal contracts to the base's;
  proved.

## Implementation notes

The proof is the pattern of `Atlas.Knowledge.absoluteLocalArtinMonoidHom_frobenius`, the
roots-of-unity normalization of the absolute Artin map, with the cyclotomic floor replaced by
the Kummer field: the reciprocity map is the absolute Artin map by
`Atlas.Knowledge.IsLocalReciprocity.unique`; the Kummer field, abelian by
`Atlas.Knowledge.kummerField_aut_comm`, is read as
`Atlas.Knowledge.absoluteFiniteQuotientField` of its restriction kernel, on which
`Atlas.Knowledge.restrictNormalHom_absoluteLocalArtinMonoidHom_lift` identifies a lift of
`φ (ϖ)` with the finite abelian Artin image of `ϖ`; the valuative structure of that field
comes from `Atlas.Knowledge.exists_extension_isMixedCharLocalField`, and
`Atlas.Knowledge.isArithmeticFrobenius_abelianLocalArtinMonoidHom` makes the image an
arithmetic Frobenius once inertia is trivial. The congruence extraction is stated over a
generic finite extension and applied by unification, as in the inertia item, because the
integral closure of a spelled intermediate field does not find its local-ring instance. The
symbol enters the integer ring by `Atlas.Knowledge.valuation_eq_one_of_pow_eq_one`, and the
base-ideal membership it ends in is read as a valuation by
`Atlas.Knowledge.valuation_lt_one_of_mem_maximalIdeal`. The divisibility `n ∣ q - 1` is a
hypothesis rather than a consequence of the roots of unity, so that
`Atlas.Knowledge.LocalHilbertSymbolTameFormula`, which proves it as
`dvd_card_residueField_sub_one`, can consume this item without a cycle. Serre's Prop. 8
reduces to `a = u`, `b = π` and computes `w = (u, π)_v` by `w̄ = Fy/y = P_n (ū)` (p.211),
which is this item verbatim; the source states the case in its transposed slots and inverse
normalization as an equality in `μ_n (K)` through its reduction isomorphism
`localNthRootsReductionEquiv`
(`LocalClassFieldTheory/Kummer/PowerResidueTameFormula.lean:702`, `:795`), where the layer
keeps the congruence form of the tame item.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open Polynomial ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

/-- The maximal ideal of the integral closure contracts to the maximal ideal of the base: an
integer whose image lies in the closure's maximal ideal lies in the base's. -/
theorem mem_maximalIdeal_of_algebraMap_mem (L : Type*) [Field L] [Algebra K L]
    [FiniteDimensional K L] {y : 𝒪[K]}
    (hy : algebraMap 𝒪[K] (integralClosure 𝒪[K] L) y ∈
      IsLocalRing.maximalIdeal (integralClosure 𝒪[K] L)) :
    y ∈ IsLocalRing.maximalIdeal 𝒪[K] := by
  have hunder : (IsLocalRing.maximalIdeal (integralClosure 𝒪[K] L)).under 𝒪[K] =
      IsLocalRing.maximalIdeal 𝒪[K] :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
        (IsLocalRing.maximalIdeal (integralClosure 𝒪[K] L)))
  rw [← hunder]
  exact Ideal.mem_comap.mpr hy

section Generic

variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- An arithmetic Frobenius moving a tame root `z` of a unit `u` by a base scalar `c` forces
`c ≡ u ^ ((q - 1) / n)` modulo the maximal ideal: `τ z ≡ z ^ q` by the Frobenius congruence,
`z ^ (q - 1) = u ^ ((q - 1) / n)` since `n ∣ q - 1`, and `z` is a unit of the closure, so
`c - u ^ ((q - 1) / n)` lies in the closure's maximal ideal and hence in the base's
([Serre 1979, Chap. XIV, §3, Example, p.210][Serre1979];
[Milne 2020, Chap. I, §1, p.20][MilneCFT]). -/
theorem sub_pow_mem_maximalIdeal_of_isArithmeticFrobenius {τ : L ≃ₐ[K] L}
    (hτ : IsArithmeticFrobenius K L τ) {n : ℕ} (hn : valuation K (n : K) = 1)
    (hdvd : n ∣ Nat.card 𝓀[K] - 1) {u : 𝒪[K]} (hu : IsUnit u)
    (z : integralClosure 𝒪[K] L) (hz : z ^ n = algebraMap 𝒪[K] (integralClosure 𝒪[K] L) u)
    {c : 𝒪[K]} (hc : τ (z : L) = algebraMap 𝒪[K] L c * (z : L)) :
    c - u ^ ((Nat.card 𝓀[K] - 1) / n) ∈ IsLocalRing.maximalIdeal 𝒪[K] := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hq1 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  have hcong := hτ z
  rw [integralClosure_jacobson_bot_eq_maximalIdeal K L] at hcong
  have hgal : galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) τ z
      = algebraMap 𝒪[K] (integralClosure 𝒪[K] L) c * z := by
    apply Subtype.ext
    change algebraMap (integralClosure 𝒪[K] L) L (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) τ z)
      = algebraMap 𝒪[K] L c * (z : L)
    rw [algebraMap_galRestrict_apply]
    exact hc
  set k := (Nat.card 𝓀[K] - 1) / n with hkdef
  have hzq : z ^ Nat.card 𝓀[K] = algebraMap 𝒪[K] (integralClosure 𝒪[K] L) (u ^ k) * z := by
    have h1 : Nat.card 𝓀[K] = n * k + 1 := by
      rw [hkdef, Nat.mul_div_cancel' hdvd]
      omega
    rw [h1, pow_succ, pow_mul, hz, map_pow]
  rw [hgal, hzq, ← sub_mul, ← map_sub] at hcong
  have hzu : IsUnit z := (isUnit_pow_iff hn0).mp (by rw [hz]; exact hu.map _)
  obtain ⟨zu, hzu'⟩ := hzu
  have h2 := Ideal.mul_mem_right ((zu⁻¹ : _ˣ) : integralClosure 𝒪[K] L) _ hcong
  rw [mul_assoc, ← hzu', Units.mul_inv, mul_one] at h2
  exact mem_maximalIdeal_of_algebraMap_mem K L h2

end Generic

/-- **The tame symbol of a unit against a uniformizer** is the power residue symbol:
`(u, ϖ) ≡ u ^ ((q - 1) / n)` modulo the maximal ideal, for `u` a unit, `ϖ` a uniformizer, `n`
a unit of the integers with `K` holding the `n`-th roots of unity, and `n ∣ q - 1` taken as a
hypothesis, since the tame formula item that proves it sits above this one — every lift of
`φ (ϖ)` is the arithmetic Frobenius on the unramified field `K (u ^ (1 / n))`, so it raises a
root of `u` to the `q`-th power modulo the maximal ideal
([Serre 1979, Chap. XIV, §3, Prop. 8, p.210, proof p.211][Serre1979];
[Milne 2020, Chap. I, §1, Thm. 1.1 (a), p.20][MilneCFT]; Yamaguchi 2026,
`LocalClassFieldTheory/Kummer/PowerResidueTameFormula.lean:702`, in its transposed slots and
inverse normalization, and `:795`). -/
theorem localHilbertSymbol_unit_uniformizer {n : ℕ} {h : Kˣ → Kˣ → Kˣ}
    (hh : IsLocalHilbertSymbol K n h) (hn : valuation K ((n : ℕ) : K) = 1)
    (hmu : (primitiveRoots n K).Nonempty) (hdvd : n ∣ Nat.card 𝓀[K] - 1) (u : Kˣ)
    (hu : valuation K (u : K) = 1) (ϖ : Kˣ) (hϖ : normalizedValuation K ϖ = 1) :
    valuation K (((h u ϖ : Kˣ) : K) - ((u ^ ((Nat.card 𝓀[K] - 1) / n) : Kˣ) : K)) < 1 := by
  have hh' := hh
  obtain ⟨φ, hφ, hspec⟩ := hh
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  haveI : NeZero n := ⟨hn0⟩
  obtain ⟨ζ, hζ⟩ := hmu
  have hζ : IsPrimitiveRoot ζ n := (mem_primitiveRoots (Nat.pos_of_ne_zero hn0)).mp hζ
  have hφeq : φ = absoluteLocalArtinMonoidHom K :=
    IsLocalReciprocity.unique hφ (isLocalReciprocity_absoluteLocalArtinMonoidHom K)
  subst hφeq
  have huint : (u : K) ∈ 𝒪[K] := (Valuation.mem_integer_iff _ _).mpr hu.le
  have hu' : IsUnit (⟨(u : K), huint⟩ : 𝒪[K]) := by
    rw [(Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one]
    exact hu
  set E := kummerField K n (u : K) with hEdef
  obtain ⟨γ, hγE, hγ⟩ := exists_mem_kummerField_pow_eq K hn0 (u : K)
  haveI : IsAbelianGalois K E := { is_comm := ⟨kummerField_aut_comm hζ hn0 u⟩ }
  set N := absoluteAbelianRestrictionKernel K E
  set F := absoluteFiniteQuotientField K N
  have hfield : F = E := absoluteFiniteQuotientField_restrictionKernel K E
  have hγF : γ ∈ F := hfield ▸ hγE
  have hbotF : lowerRamificationGroup K F 0 = ⊥ := by
    rw [hfield]
    exact kummerField_lowerRamificationGroup_eq_bot K hn u hu
  obtain ⟨σ, hσ⟩ : ∃ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      (QuotientGroup.mk (σ : Field.absoluteGaloisGroup K) :
        Field.absoluteGaloisGroupAbelianization K) = absoluteLocalArtinMonoidHom K ϖ :=
    QuotientGroup.mk_surjective _
  have hres : AlgEquiv.restrictNormalHom F σ = abelianLocalArtinMonoidHom K F ϖ :=
    restrictNormalHom_absoluteLocalArtinMonoidHom_lift K N ϖ σ hσ
  obtain ⟨vF, tF, hVF, _, hmixed⟩ := exists_extension_isMixedCharLocalField K F
  letI := vF
  letI := tF
  letI := hVF
  letI := hmixed
  have hfrob : IsArithmeticFrobenius K F (abelianLocalArtinMonoidHom K F ϖ) :=
    isArithmeticFrobenius_abelianLocalArtinMonoidHom K F hbotF ϖ hϖ
  set γF : F := ⟨γ, hγF⟩ with hγFdef
  have hγFn : γF ^ n = algebraMap 𝒪[K] F ⟨(u : K), huint⟩ := by
    apply Subtype.ext
    change γ ^ n = ((algebraMap 𝒪[K] F ⟨(u : K), huint⟩ : F) : AlgebraicClosure K)
    rw [hγ]
    rfl
  have hγint : IsIntegral 𝒪[K] γF :=
    ⟨X ^ n - C ⟨(u : K), huint⟩, monic_X_pow_sub_C _ hn0, by simp [hγFn]⟩
  have hz : (⟨γF, hγint⟩ : integralClosure 𝒪[K] F) ^ n
      = algebraMap 𝒪[K] (integralClosure 𝒪[K] F) ⟨(u : K), huint⟩ := by
    apply Subtype.ext
    rw [Subalgebra.coe_pow]
    exact hγFn
  have hcpow : ((h u ϖ : Kˣ) : K) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, IsLocalHilbertSymbol.pow_eq_one hh' hn0 u ϖ, Units.val_one]
  have hcval : valuation K ((h u ϖ : Kˣ) : K) = 1 := valuation_eq_one_of_pow_eq_one K hn0 hcpow
  have hcint : ((h u ϖ : Kˣ) : K) ∈ 𝒪[K] := (Valuation.mem_integer_iff _ _).mpr hcval.le
  have hc : abelianLocalArtinMonoidHom K F ϖ γF = algebraMap 𝒪[K] F ⟨_, hcint⟩ * γF := by
    apply Subtype.ext
    have h1 : ((abelianLocalArtinMonoidHom K F ϖ γF : F) : AlgebraicClosure K) = σ γ := by
      rw [← hres]
      exact AlgEquiv.restrictNormal_commutes σ F γF
    rw [h1, hspec u ϖ σ hσ γ hγ]
    rfl
  have hmem := sub_pow_mem_maximalIdeal_of_isArithmeticFrobenius K F hfrob hn hdvd hu'
    ⟨γF, hγint⟩ hz hc
  have hlt := valuation_lt_one_of_mem_maximalIdeal _ hmem
  change valuation K (((h u ϖ : Kˣ) : K) - (u : K) ^ ((Nat.card 𝓀[K] - 1) / n)) < 1 at hlt
  rw [Units.val_pow_eq_pow_val]
  exact hlt

end Atlas.Knowledge
