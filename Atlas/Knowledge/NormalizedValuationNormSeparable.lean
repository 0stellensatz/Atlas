import Mathlib
import Atlas.Knowledge.AddValMapIntegralClosure
import Atlas.Knowledge.IntegerIsIntegralClosure
import Atlas.Knowledge.IntegerValuation
import Atlas.Knowledge.NormalizedValuation
import Atlas.Knowledge.NormalizedValuationAlgEquiv

/-!
# normalized valuation of a norm of a separable extension

The inertia-degree form of the norm law, for every finite *separable* extension of
mixed-characteristic local fields, normal or not: `v_K(N y) = f · v_L(y)` with
`f = Ideal.inertiaDeg 𝓂[L] 𝒪[K]` the residue degree. This is the pointwise law the reciprocity
engine's `norm_range` axiom is discharged from (#104), the brick the Galois `e`-form of
`Atlas.Knowledge.NormalizedValuationNorm` stops one short of. The crux is Serre's `N(𝔓) = 𝔭^f` read
at one element — Mathlib's `Ideal.relNorm_eq_pow_of_isMaximal` carries the ideal identity without
any normality hypothesis — and the law follows by uniformizer decomposition, conjugates never
entering.

## Main statements

* `integerValuation_intNorm_of_irreducible` — the norm of a uniformizer has value the
  inertia degree; proved.
* `normalizedValuation_norm_of_isSeparable` — `v_K(N y) = f · v_L(y)`; proved.
* `inertiaDeg_eq_finrank_residueField` — the inertia degree read on residue fields;
  proved.

## Implementation notes

The residue degree is spelled `Ideal.inertiaDeg 𝓂[L] ↥𝒪[K]`, the vocabulary of
`Atlas.Knowledge.AbsoluteInertiaDegree`; the recorded bridge
`inertiaDeg_eq_finrank_residueField` hands a consumer the residue-field reading. The
crux runs `Ideal.relNorm` along a uniformizer's principal ideal —
`Ideal.relNorm_singleton` turns the ideal norm into `Algebra.intNorm`, whose square
with `Algebra.norm K` is `Algebra.algebraMap_intNorm` — and compares exponents
through `Atlas.Knowledge.span_singleton_eq_pow_maximalIdeal`. The needed instances
all synthesize from the layer's own: `Module.Finite 𝒪[K] 𝒪[L]` is
`IsIntegralClosure.finite` over `Atlas.Knowledge.integerIsIntegralClosure` (this is
where separability enters), and `𝓂[L]` lies over `𝓂[K]` by Mathlib's
valuation-extension instances, reached through the layer's
`Atlas.Knowledge.IntegerIsIntegralClosure.hasExtension`.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer
  New York, 1979.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

section SeparableNormLaw

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [Algebra K L]
  [ValuativeExtension K L] [FiniteDimensional K L] [IsMixedCharLocalField L]
  [Algebra.IsSeparable K L]

/-- **The norm of a uniformizer has value the inertia degree** — `N(𝔓) = 𝔭^f` read at
one element: the relative ideal norm of the maximal ideal is the `f`-th power of the
base maximal ideal, with no normality hypothesis
([Serre 1979, Chap. I, §5, p.16][Serre1979]). -/
theorem integerValuation_intNorm_of_irreducible {ϖ : ↥𝒪[L]} (hϖ : Irreducible ϖ) :
    integerValuation K (Algebra.intNorm ↥𝒪[K] ↥𝒪[L] ϖ) =
      (Ideal.inertiaDeg (𝓂[L] : Ideal ↥𝒪[L]) ↥𝒪[K] : ℤ) := by
  haveI : Module.Finite ↥𝒪[K] ↥𝒪[L] := IsIntegralClosure.finite ↥𝒪[K] K L ↥𝒪[L]
  have hspan : Ideal.span {ϖ} = (𝓂[L] : Ideal ↥𝒪[L]) :=
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ).symm
  have h1 : Ideal.relNorm ↥𝒪[K] (𝓂[L] : Ideal ↥𝒪[L]) =
      (𝓂[K] : Ideal ↥𝒪[K]) ^ Ideal.inertiaDeg (𝓂[L] : Ideal ↥𝒪[L]) ↥𝒪[K] :=
    Ideal.relNorm_eq_pow_of_isMaximal 𝓂[L] 𝓂[K]
  have h2 : Ideal.span {Algebra.intNorm ↥𝒪[K] ↥𝒪[L] ϖ} =
      (𝓂[K] : Ideal ↥𝒪[K]) ^ Ideal.inertiaDeg (𝓂[L] : Ideal ↥𝒪[L]) ↥𝒪[K] := by
    rw [← Ideal.relNorm_singleton, hspan, h1]
  have hne : Algebra.intNorm ↥𝒪[K] ↥𝒪[L] ϖ ≠ 0 :=
    (Algebra.intNorm_ne_zero).mpr hϖ.ne_zero
  rw [span_singleton_eq_pow_maximalIdeal K hne] at h2
  have hexp := AddValMapIntegralClosure.maximalIdeal_pow_injective h2
  have hK := Int.toNat_of_nonneg (integerValuation_nonneg K
    (Algebra.intNorm ↥𝒪[K] ↥𝒪[L] ϖ))
  rw [← hK]
  exact_mod_cast hexp

/-- **A norm's value is the inertia degree times the value upstairs**, for every finite
separable extension: `v_K(N y) = f · v_L(y)` — a uniformizer decomposition of `y`, the
norm of an integer unit landing at value zero and the norm of the uniformizer at `f`.
The pointwise law the reciprocity engine's `norm_range` axiom is discharged from
([Serre 1979, Chap. I, §5, p.16][Serre1979]; Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableNormValuation.lean:513`,
`v_normUnits_eq_residue_finrank_mul_of_isSeparable`). -/
theorem normalizedValuation_norm_of_isSeparable (y : Lˣ) :
    normalizedValuation K (Units.map ((Algebra.norm K) : L →* K) y) =
      (Ideal.inertiaDeg (𝓂[L] : Ideal ↥𝒪[L]) ↥𝒪[K] : ℤ) * normalizedValuation L y := by
  haveI : Module.Finite ↥𝒪[K] ↥𝒪[L] := IsIntegralClosure.finite ↥𝒪[K] K L ↥𝒪[L]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (↥𝒪[L])
  have hy0 : ((y : Lˣ) : L) ≠ 0 := Units.ne_zero y
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ hy0
  have hϖ0 : algebraMap ↥𝒪[L] L ϖ ≠ 0 := algebraMap_integer_ne_zero L hϖ.ne_zero
  have hu0 : algebraMap ↥𝒪[L] L (u : ↥𝒪[L]) ≠ 0 :=
    algebraMap_integer_ne_zero L (Units.ne_zero u)
  have hyeq : y = Units.mk0 (algebraMap ↥𝒪[L] L (u : ↥𝒪[L])) hu0 *
      (Units.mk0 (algebraMap ↥𝒪[L] L ϖ) hϖ0) ^ n := by
    ext
    push_cast [hu, Units.smul_def, Algebra.smul_def]
    rfl
  have hvL : normalizedValuation L y = n := by
    rw [hyeq]
    exact value_unit_mul_zpow (L := L) ϖ hϖ u hu0 hϖ0 n
  have hNu0 : algebraMap ↥𝒪[K] K (Algebra.intNorm ↥𝒪[K] ↥𝒪[L] (u : ↥𝒪[L])) ≠ 0 :=
    algebraMap_integer_ne_zero K ((Algebra.intNorm_ne_zero).mpr (Units.ne_zero u))
  have hNϖ0 : algebraMap ↥𝒪[K] K (Algebra.intNorm ↥𝒪[K] ↥𝒪[L] ϖ) ≠ 0 :=
    algebraMap_integer_ne_zero K ((Algebra.intNorm_ne_zero).mpr hϖ.ne_zero)
  have hmapu : Units.map ((Algebra.norm K) : L →* K)
      (Units.mk0 (algebraMap ↥𝒪[L] L (u : ↥𝒪[L])) hu0) =
      Units.mk0 (algebraMap ↥𝒪[K] K
        (Algebra.intNorm ↥𝒪[K] ↥𝒪[L] (u : ↥𝒪[L]))) hNu0 := by
    ext
    simp only [Units.coe_map, Units.val_mk0]
    exact (Algebra.algebraMap_intNorm (A := ↥𝒪[K]) (K := K) (L := L) (B := ↥𝒪[L])
      (u : ↥𝒪[L])).symm
  have hmapϖ : Units.map ((Algebra.norm K) : L →* K)
      (Units.mk0 (algebraMap ↥𝒪[L] L ϖ) hϖ0) =
      Units.mk0 (algebraMap ↥𝒪[K] K (Algebra.intNorm ↥𝒪[K] ↥𝒪[L] ϖ)) hNϖ0 := by
    ext
    simp only [Units.coe_map, Units.val_mk0]
    exact (Algebra.algebraMap_intNorm (A := ↥𝒪[K]) (K := K) (L := L) (B := ↥𝒪[L])
      ϖ).symm
  have hUu : IsUnit (Algebra.intNorm ↥𝒪[K] ↥𝒪[L] (u : ↥𝒪[L])) :=
    u.isUnit.map (Algebra.intNorm ↥𝒪[K] ↥𝒪[L])
  have hvalu : normalizedValuation K
      (Units.mk0 (algebraMap ↥𝒪[K] K
        (Algebra.intNorm ↥𝒪[K] ↥𝒪[L] (u : ↥𝒪[L]))) hNu0) = 0 := by
    refine normalizedValuation_eq_zero_of_valuation_eq_one K _ ?_
    exact Valuation.Integers.one_of_isUnit
      (Valuation.integer.integers (v := valuation K)) hUu
  have hvalϖ : normalizedValuation K
      (Units.mk0 (algebraMap ↥𝒪[K] K (Algebra.intNorm ↥𝒪[K] ↥𝒪[L] ϖ)) hNϖ0) =
      (Ideal.inertiaDeg (𝓂[L] : Ideal ↥𝒪[L]) ↥𝒪[K] : ℤ) := by
    rw [← integerValuation_of_ne_zero K hNϖ0]
    exact integerValuation_intNorm_of_irreducible K L hϖ
  rw [hvL, hyeq, map_mul, map_zpow, normalizedValuation_mul, normalizedValuation_zpow,
    hmapu, hmapϖ, hvalu, hvalϖ]
  ring

omit [FiniteDimensional K L] in
/-- **The inertia degree read on residue fields**: the `f` of the two laws above is
the degree of the residue extension, the source's spelling of the norm law. -/
theorem inertiaDeg_eq_finrank_residueField :
    Ideal.inertiaDeg (𝓂[L] : Ideal ↥𝒪[L]) ↥𝒪[K] = Module.finrank 𝓀[K] 𝓀[L] :=
  Ideal.inertiaDeg_eq_of_isMaximal _ _

end SeparableNormLaw

end Atlas.Knowledge
