import Mathlib
import Atlas.Knowledge.CycloFieldLowerRamificationGroupEqBot
import Atlas.Knowledge.IntegralClosureDVR
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.KummerField
import Atlas.Knowledge.LowerRamificationGroup

/-!
# unramifiedness of the tame Kummer field of a unit

The Kummer field `K (u ^ (1 / n))` of a unit `u` is unramified when `n` is prime to the
residue characteristic: its zeroth lower-numbering ramification group is trivial. An inertia
element moves a root `z` of `u` by `σ z / z`, an `n`-th root of unity which the inertia
congruence puts in the class of `1` modulo the maximal ideal of the integral closure, and
reduction is injective on tame roots of unity, so `σ z = z`; the roots generate the field, so
`σ = 1`. This is the extension the tame formula's Frobenius computation is read on:
`Atlas.Knowledge.LocalHilbertSymbolUnitUniformizer` restricts a lift of the reciprocity class
of a uniformizer to it and applies the arithmetic Frobenius congruence, which the layer's
normalization supplies only over an unramified extension.

## Main statements

* `kummerField_lowerRamificationGroup_eq_bot` —
  `lowerRamificationGroup K ↥(kummerField K n u) 0 = ⊥` for `u` a unit and `n` a unit of the
  integers; proved.
* `apply_eq_self_of_mem_lowerRamificationGroup_zero_of_pow_eq` — over any finite extension,
  an inertia element fixes every integral tame root of a unit; proved.
* `natCast_notMem_maximalIdeal_of_valuation_eq_one` — a natural number that is a unit of the
  integers avoids the maximal ideal of the integral closure; proved.

## Implementation notes

The argument is the pattern of `Atlas.Knowledge.CycloFieldLowerRamificationGroupEqBot`, whose
injectivity lemma `Atlas.Knowledge.eq_of_pow_eq_one_of_sub_mem` — two `n`-th roots of unity
congruent modulo an ideal avoiding `n` are equal — is applied to the root quotient
`σ z · z⁻¹`, a unit of the integral closure because `z ^ n` is one, against `1`. The tameness
hypothesis is `valuation K (n : K) = 1`, the reading the tame formula takes, and it enters
only through `n` avoiding the maximal ideal of the closure and through `n ≠ 0`; no primitive
root of unity in the base is needed, since no root of unity is chosen. Under that reading the
item restates two facts the layer holds under `Nat.Coprime n (Nat.card 𝓀[K])`:
`natCast_notMem_maximalIdeal_of_valuation_eq_one` is
`Atlas.Knowledge.natCast_notMem_maximalIdeal_of_coprime` with the hypothesis exchanged, and
the cyclotomic case of the headline is
`Atlas.Knowledge.CycloFieldLowerRamificationGroupEqBot`; nothing in the layer relates the two
renderings of tameness, so each pair stands until that bridge is an item. The inertia step is
stated over an arbitrary finite extension `L` and applied to the Kummer field by unification,
not spelled at it: the local-ring instance of `integralClosure 𝒪[K] L` is found for a generic
`L` but not when `L` is spelled as an intermediate field of the closure, whose algebra
structure elaborates through `IntermediateField.algebra'` to a term the instance's key does
not match. Extensionality on the root set is `IntermediateField.adjoin_algHom_ext` at the
definition, as in `Atlas.Knowledge.KummerField`. The source proves the same unramifiedness in
its valued-extension bundle at a chosen generator of the simple Kummer extension
(`KummerTheory/Concrete/LocalUnitKummerUnramified.lean:23`), through its
`IsUnramifiedValuedExtension` predicate; here the statement is at the layer's
`lowerRamificationGroup` rendering, on the root-free field, with no valuation on the
extension at all.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open Polynomial ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

section Generic

variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- A natural number that is a unit of the integers avoids the maximal ideal of the integral
closure: its image is a unit there. -/
theorem natCast_notMem_maximalIdeal_of_valuation_eq_one {n : ℕ} (hn : valuation K (n : K) = 1) :
    ((n : ℕ) : integralClosure 𝒪[K] L) ∉ IsLocalRing.maximalIdeal (integralClosure 𝒪[K] L) := by
  intro hmem
  have hunit : IsUnit ((n : ℕ) : 𝒪[K]) := by
    rw [(Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one]
    exact hn
  have hunit' : IsUnit ((n : ℕ) : integralClosure 𝒪[K] L) := by
    rw [← map_natCast (algebraMap 𝒪[K] (integralClosure 𝒪[K] L))]
    exact hunit.map _
  exact (IsLocalRing.notMem_maximalIdeal.mpr hunit') hmem

/-- An inertia element fixes every tame root of a unit: for `n` a unit of the integers and
`z` integral with `z ^ n` a unit of the base, the root quotient of `z` under an element of
the zeroth ramification group is an `n`-th root of unity congruent to `1` modulo the maximal
ideal of the integral closure, hence `1` by the injectivity of reduction on tame roots of
unity ([Serre 1979, Chap. XIV, §3, Lemma 1, p.210][Serre1979]). -/
theorem apply_eq_self_of_mem_lowerRamificationGroup_zero_of_pow_eq {n : ℕ}
    (hn : valuation K (n : K) = 1) {u : 𝒪[K]} (hu : IsUnit u) {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ lowerRamificationGroup K L 0) (z : integralClosure 𝒪[K] L)
    (hz : z ^ n = algebraMap 𝒪[K] (integralClosure 𝒪[K] L) u) : σ (z : L) = z := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  rw [mem_lowerRamificationGroup_iff] at hσ
  have hcong := hσ z
  rw [show ((0 : ℤ) + 1).toNat = 1 by norm_num, pow_one,
    integralClosure_jacobson_bot_eq_maximalIdeal K L] at hcong
  have hzu : IsUnit z := (isUnit_pow_iff hn0).mp (by rw [hz]; exact hu.map _)
  obtain ⟨zu, hzu'⟩ := hzu
  set g := galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ z with hgdef
  have hgn : g ^ n = z ^ n := by
    rw [hgdef, ← map_pow, hz]
    exact AlgEquiv.commutes _ _
  have hη : (g * (zu⁻¹ : _ˣ)) ^ n = 1 := by
    rw [mul_pow, hgn, ← hzu', ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
      ← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow, Units.val_one]
  have h2 : z * ((zu⁻¹ : _ˣ) : integralClosure 𝒪[K] L) = 1 := by
    rw [← hzu', Units.mul_inv]
  have hcong' := Ideal.mul_mem_right ((zu⁻¹ : _ˣ) : integralClosure 𝒪[K] L) _ hcong
  rw [sub_mul, h2] at hcong'
  have hηeq := eq_of_pow_eq_one_of_sub_mem
    (natCast_notMem_maximalIdeal_of_valuation_eq_one K L hn) hη (one_pow n) hcong'
  have hg : g = z := by
    rw [← hzu']
    exact Units.mul_inv_eq_one.mp hηeq
  have hcoe := congrArg (algebraMap (integralClosure 𝒪[K] L) L) hg
  rw [hgdef, algebraMap_galRestrict_apply] at hcoe
  exact hcoe

end Generic

/-- **The tame Kummer field of a unit is unramified**: for a unit `u` and `n` a unit of the
integers, the zeroth lower-numbering ramification group of `kummerField K n u` is trivial —
an inertia element fixes every root, since it moves it by a root of unity congruent to `1`
modulo the maximal ideal, and the roots generate
([Serre 1979, Chap. XIV, §3, Prop. 8, p.210, proof p.211][Serre1979]; Yamaguchi 2026,
`KummerTheory/Concrete/LocalUnitKummerUnramified.lean:23`, its valued-extension form at a
chosen generator). -/
theorem kummerField_lowerRamificationGroup_eq_bot {n : ℕ} (hn : valuation K (n : K) = 1)
    (u : Kˣ) (hu : valuation K (u : K) = 1) :
    lowerRamificationGroup K ↥(kummerField K n (u : K)) 0 = ⊥ := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  haveI : NeZero n := ⟨hn0⟩
  have huint : (u : K) ∈ 𝒪[K] := (Valuation.mem_integer_iff _ _).mpr hu.le
  have hu' : IsUnit (⟨(u : K), huint⟩ : 𝒪[K]) := by
    rw [(Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one]
    exact hu
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  apply AlgEquiv.coe_toAlgHom_injective
  refine IntermediateField.adjoin_algHom_ext K (fun x hx => ?_)
  have hxn : x ^ n = algebraMap K (AlgebraicClosure K) (u : K) :=
    (mem_rootSet_X_pow_sub_C_iff K hn0 (u : K) x).mp hx
  change σ (⟨x, mem_kummerField_of_pow_eq K hn0 hxn⟩ : kummerField K n (u : K))
    = ⟨x, mem_kummerField_of_pow_eq K hn0 hxn⟩
  set ζ : kummerField K n (u : K) := ⟨x, mem_kummerField_of_pow_eq K hn0 hxn⟩ with hζdef
  have hζn : ζ ^ n = algebraMap 𝒪[K] (kummerField K n (u : K)) ⟨(u : K), huint⟩ := by
    apply Subtype.ext
    change x ^ n = ((algebraMap 𝒪[K] (kummerField K n (u : K)) ⟨(u : K), huint⟩ :
      kummerField K n (u : K)) : AlgebraicClosure K)
    rw [hxn]
    rfl
  have hζint : IsIntegral 𝒪[K] ζ :=
    ⟨X ^ n - C ⟨(u : K), huint⟩, monic_X_pow_sub_C _ hn0, by simp [hζn]⟩
  have hz : (⟨ζ, hζint⟩ : integralClosure 𝒪[K] (kummerField K n (u : K))) ^ n
      = algebraMap 𝒪[K] (integralClosure 𝒪[K] (kummerField K n (u : K))) ⟨(u : K), huint⟩ := by
    apply Subtype.ext
    rw [Subalgebra.coe_pow]
    exact hζn
  exact apply_eq_self_of_mem_lowerRamificationGroup_zero_of_pow_eq K ↥(kummerField K n (u : K))
    hn hu' hσ ⟨ζ, hζint⟩ hz

end Atlas.Knowledge
