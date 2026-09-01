import Mathlib
import Atlas.Knowledge.NormalizedValuation
import Atlas.Knowledge.SeparableFixedFieldNorm
import Atlas.Knowledge.ValuationData

/-!
# base valuation of the local degree datum

The normalized valuation of a mixed-characteristic local field, written on
the coefficient group the engine attaches to the ground field — the ambient
units fixed by the distinguished base subgroup — and embedded in the
profinite integers. Its range is exactly the copy of the ordinary integers,
and reduction modulo every positive modulus is bijective through the
engine's canonical map. These are the value-group conditions of the
valuation datum (#104).

## Main definitions

* `normalizedValuationAddHom` — the normalized valuation as an additive
  homomorphism on `Additive Kˣ`.
* `localBaseValuation` — the valuation on the base fixed coefficients,
  in `ℤ̂`.

## Main statements

* `localBaseValuation_range` — the value group is the integers in `ℤ̂`;
  proved.
* `localCanonicalValueQuotientMap_bijective` — the canonical value-quotient
  map is bijective at every positive modulus; proved.

## Implementation notes

The additive reading of the unit-group valuation is the layer's
`Atlas.Knowledge.normalizedValuation`, which sends a uniformizer to `+1`;
the source's `valuationMap` uses the inverse-standard convention of the
concrete local Artin map and sends it to `-1`. Every statement here is
invariant under that sign — negation is an automorphism of `ℤ` fixing range,
kernels and quotients — so neither side is repaired; the fork stands as the
layer records it at the normalized valuation, and it resurfaces where the
Artin map is assembled, not here. Surjectivity is the layer's
`normalizedValuation_surjective`, reduction is
`Atlas.Knowledge.ProfiniteInteger.reduction`, and the positive modulus is
carried as `NeZero` throughout, matching the valuation datum's own fields.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

noncomputable section

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/-- The normalized valuation, read additively on the unit group — the
negative of the source's inverse-standard valuation map ([Yamaguchi 2026,
`LocalFieldTheory/NonarchimedeanLocalField/ValuationExactSequence.lean:31`]
[Yamaguchi2026]). -/
def normalizedValuationAddHom : Additive Kˣ →+ ℤ where
  toFun x := normalizedValuation K (Additive.toMul x)
  map_zero' := normalizedValuation_one K
  map_add' x y := normalizedValuation_mul K (Additive.toMul x) (Additive.toMul y)

/-- **`Kˣ` is the coefficient group fixed by the distinguished base
subgroup** of the absolute Galois group ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/HenselianValuationBase.lean:34`]
[Yamaguchi2026]). -/
def baseFieldUnitsEquiv :
    Additive Kˣ ≃+ ambientFixedAddSubgroup
      (galoisAmbientUnitsRep K (AlgebraicClosure K))
      (baseField (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) :=
  (baseUnitsEquivGaloisAmbientFixed K (AlgebraicClosure K)).trans
    (AddEquiv.addSubgroupCongr
      (congrArg (ambientFixedAddSubgroup
        (galoisAmbientUnitsRep K (AlgebraicClosure K)))
        (closedFixingSubgroup_bot_eq_baseField K (AlgebraicClosure K))))

/-- The base equivalence reads as the structure map on the underlying element
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/HenselianValuationBase.lean:44`]
[Yamaguchi2026]). -/
@[simp]
theorem baseFieldUnitsEquiv_val (x : Kˣ) :
    ((Additive.toMul
      ((baseFieldUnitsEquiv K (Additive.ofMul x)).1 :
        Additive (AlgebraicClosure K)ˣ) : (AlgebraicClosure K)ˣ) :
      AlgebraicClosure K) = algebraMap K (AlgebraicClosure K) (x : K) := by
  change
    ((Additive.toMul
      ((baseUnitsEquivGaloisAmbientFixed K (AlgebraicClosure K)
          (Additive.ofMul x)).1 :
        Additive (AlgebraicClosure K)ˣ) : (AlgebraicClosure K)ˣ) :
      AlgebraicClosure K) = algebraMap K (AlgebraicClosure K) (x : K)
  exact baseUnitsEquivGaloisAmbientFixed_val K (AlgebraicClosure K) x

/-- **The normalized valuation on the base fixed coefficients**, embedded in
the profinite integers ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/HenselianValuationBase.lean:59`]
[Yamaguchi2026]). -/
def localBaseValuation :
    ambientFixedAddSubgroup
      (galoisAmbientUnitsRep K (AlgebraicClosure K))
      (baseField (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) →+
      ProfiniteInteger :=
  (Int.castRingHom ProfiniteInteger).toAddMonoidHom.comp
    ((normalizedValuationAddHom K).comp
      (baseFieldUnitsEquiv K).symm.toAddMonoidHom)

/-- The base valuation computes through the unit equivalence
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/HenselianValuationBase.lean:67`]
[Yamaguchi2026]). -/
@[simp]
theorem localBaseValuation_baseFieldUnitsEquiv (x : Additive Kˣ) :
    localBaseValuation K (baseFieldUnitsEquiv K x) =
      Int.castRingHom ProfiniteInteger
        (normalizedValuationAddHom K x) := by
  simp [localBaseValuation]

/-- **The value group is the copy of the ordinary integers** in the
profinite integers ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/HenselianValuationBase.lean:75`]
[Yamaguchi2026]). -/
theorem localBaseValuation_range :
    (localBaseValuation K).range =
      (Int.castRingHom ProfiniteInteger).toAddMonoidHom.range := by
  apply le_antisymm
  · rintro z ⟨x, rfl⟩
    exact ⟨normalizedValuationAddHom K
      ((baseFieldUnitsEquiv K).symm x), rfl⟩
  · rintro z ⟨m, rfl⟩
    obtain ⟨x, hx⟩ := normalizedValuation_surjective K m
    refine ⟨baseFieldUnitsEquiv K (Additive.ofMul x), ?_⟩
    rw [localBaseValuation_baseFieldUnitsEquiv]
    change Int.castRingHom ProfiniteInteger (normalizedValuation K x) = _
    rw [hx]
    rfl

/-- Every ordinary integer occurs as a value ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/HenselianValuationBase.lean:90`]
[Yamaguchi2026]). -/
theorem intCast_mem_localBaseValuation_range (m : ℤ) :
    Int.castRingHom ProfiniteInteger m ∈
      (localBaseValuation K).range := by
  rw [localBaseValuation_range]
  exact ⟨m, rfl⟩

/-- Reduction modulo `n` on the value group ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/HenselianValuationBase.lean:97`]
[Yamaguchi2026]). -/
def localValueGroupReduction (n : ℕ) [NeZero n] :
    (localBaseValuation K).range →+ ZMod n :=
  (ProfiniteInteger.reduction n).toAddMonoidHom.comp
    (localBaseValuation K).range.subtype

/-- Reduction on the value group is onto ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/HenselianValuationBase.lean:103`]
[Yamaguchi2026]). -/
theorem localValueGroupReduction_surjective (n : ℕ) [NeZero n] :
    Function.Surjective (localValueGroupReduction K n) := by
  intro a
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective a
  let z : (localBaseValuation K).range :=
    ⟨Int.castRingHom ProfiniteInteger m,
      intCast_mem_localBaseValuation_range K m⟩
  refine ⟨z, ?_⟩
  exact ProfiniteInteger.reduction_intCast n m

/-- **The kernel of reduction on the value group is `nZ`** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/HenselianValuationBase.lean:114`]
[Yamaguchi2026]). -/
theorem localValueGroupReduction_ker (n : ℕ) [NeZero n] :
    (localValueGroupReduction K n).ker =
      nsmulWithin (localBaseValuation K).range n := by
  apply le_antisymm
  · intro z hz
    have hzInt : (z : ProfiniteInteger) ∈
        (Int.castRingHom ProfiniteInteger).toAddMonoidHom.range := by
      rw [← localBaseValuation_range K]
      exact z.property
    obtain ⟨m, hm⟩ := hzInt
    change Int.castRingHom ProfiniteInteger m = (z : ProfiniteInteger) at hm
    have hmod : (m : ZMod n) = 0 := by
      have hz0 : localValueGroupReduction K n z = 0 := hz
      change ProfiniteInteger.reduction n (z : ProfiniteInteger) = 0 at hz0
      rw [← hm,
        show Int.castRingHom ProfiniteInteger m =
          ((m : ℤ) : ProfiniteInteger) from rfl,
        ProfiniteInteger.reduction_intCast] at hz0
      exact hz0
    have hdiv : (n : ℤ) ∣ m := by
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hmod
    obtain ⟨k, hk⟩ := hdiv
    let w : (localBaseValuation K).range :=
      ⟨Int.castRingHom ProfiniteInteger k,
        intCast_mem_localBaseValuation_range K k⟩
    refine ⟨w, ?_⟩
    apply Subtype.ext
    change n • Int.castRingHom ProfiniteInteger k = (z : ProfiniteInteger)
    rw [← map_nsmul]
    have hnk : n • k = m := by
      simpa [nsmul_eq_mul] using hk.symm
    rw [hnk, hm]
  · rintro z ⟨w, rfl⟩
    change ProfiniteInteger.reduction n
      (n • (w : ProfiniteInteger)) = 0
    rw [map_nsmul]
    simp [nsmul_eq_mul]

/-- The cyclic value quotient, for the actual local value group
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/HenselianValuationBase.lean:150`]
[Yamaguchi2026]). -/
def localValueGroupQuotientEquivZMod (n : ℕ) [NeZero n] :
    ((localBaseValuation K).range ⧸
        nsmulWithin (localBaseValuation K).range n) ≃+ ZMod n :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (localValueGroupReduction_ker K n).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (localValueGroupReduction K n)
      (localValueGroupReduction_surjective K n))

/-- **The canonical value-quotient map is bijective** at every positive
modulus ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/HenselianValuationBase.lean:161`]
[Yamaguchi2026]). -/
theorem localCanonicalValueQuotientMap_bijective (n : ℕ) [NeZero n] :
    Function.Bijective
      (canonicalValueQuotientMap (localBaseValuation K).range n) := by
  constructor
  · intro q₁ q₂
    refine Quotient.inductionOn' q₁ ?_
    intro z₁
    refine Quotient.inductionOn' q₂ ?_
    intro z₂ h
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    rw [← localValueGroupReduction_ker K n]
    change localValueGroupReduction K n (z₁ - z₂) = 0
    rw [map_sub]
    change localValueGroupReduction K n z₁ =
      localValueGroupReduction K n z₂ at h
    rw [h, sub_self]
  · intro a
    obtain ⟨z, hz⟩ := localValueGroupReduction_surjective K n a
    refine ⟨QuotientAddGroup.mk'
      (nsmulWithin (localBaseValuation K).range n) z, ?_⟩
    exact hz

end

end Atlas.Knowledge
