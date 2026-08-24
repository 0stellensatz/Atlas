import Mathlib
import Atlas.Knowledge.NormalizedValuation
import Atlas.Knowledge.IntegerIsIntegralClosure

/-!
# Galois invariance of the normalized valuation

A `K`-automorphism of a finite extension `L` of a mixed-characteristic local field preserves
the normalized valuation of `L`: `v (σ x) = v (x)`. This is the uniqueness of the
prolongation of a complete valuation, read on `Atlas.Knowledge.normalizedValuation` — the
automorphism permutes the integers, because integrality over the base is preserved and the
integers are the integral elements, hence carries irreducibles to irreducibles and units to
units, and the value of `u ⬝ π ^ k` is `k` on both sides of the automorphism. It is the
equivariance that puts the valuation exact sequence `1 → U_L → Lˣ → ℤ → 1` in the reach of
the Herbrand machinery of `Atlas.Knowledge.herbrandQuotient`, with the Galois action on the
outer terms trivial and restricted respectively.

## Main definitions

* `algEquivIntegerRestrict` — the automorphism restricted to the integers, as a ring
  isomorphism.

## Main statements

* `normalizedValuation_algEquiv` — `v ∘ σ = v` on `Lˣ`; proved.
* `algEquiv_mem_integer` — the automorphism preserves the integers; proved.

## Implementation notes

The carrier is the tower idiom of `Atlas.Knowledge.FiniteExtensionIsMixedCharLocalField`:
`L` carries its own valuative relation and topology with `[ValuativeExtension K L]`, and
the mixed-characteristic structure of `L` enters the main statement as an instance rather
than through the existence theorem — the section's `[IsValuativeTopology L]` is omitted
from the statements it would duplicate, since the mixed-characteristic instance carries
it. The proof never touches the topology: it runs
through `Atlas.Knowledge.mem_integer_iff_isIntegral` and the factorization of a unit into a
unit of the integers times an irreducible power, whose value the trio of
`Atlas.Knowledge.normalizedValuation_mul` computes on both sides.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [Algebra K L]
  [ValuativeExtension K L] [IsValuativeTopology L] [FiniteDimensional K L]

omit [TopologicalSpace L] [IsValuativeTopology L] in
/-- A `K`-automorphism preserves the integers of the extension: integrality over the base
is automorphism-invariant, and the integers are the integral elements
([Serre 1979, Chap. II, §2, Prop. 3, p.28][Serre1979]). -/
theorem algEquiv_mem_integer (σ : L ≃ₐ[K] L) {x : L} (hx : x ∈ 𝒪[L]) : σ x ∈ 𝒪[L] := by
  rw [mem_integer_iff_isIntegral K L] at hx ⊢
  exact IsIntegral.map (σ.toAlgHom.restrictScalars ↥𝒪[K]) hx

/-- The restriction of a `K`-automorphism to the integers, as a ring isomorphism
([Serre 1979, Chap. II, §2, Prop. 3, p.28][Serre1979]). -/
noncomputable def algEquivIntegerRestrict (σ : L ≃ₐ[K] L) : ↥𝒪[L] ≃+* ↥𝒪[L] where
  toFun x := ⟨σ x, algEquiv_mem_integer K L σ x.2⟩
  invFun x := ⟨σ.symm x, by
    have := algEquiv_mem_integer K L σ.symm x.2
    exact this⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x)
  right_inv x := Subtype.ext (σ.apply_symm_apply x)
  map_mul' x y := Subtype.ext (by push_cast; exact map_mul σ (x : L) (y : L))
  map_add' x y := Subtype.ext (by push_cast; exact map_add σ (x : L) (y : L))

omit [TopologicalSpace L] [IsValuativeTopology L] in
/-- The restricted automorphism carries irreducibles to irreducibles. -/
theorem algEquivIntegerRestrict_irreducible (σ : L ≃ₐ[K] L) {π : ↥𝒪[L]}
    (hπ : Irreducible π) : Irreducible (algEquivIntegerRestrict K L σ π) :=
  hπ.map (algEquivIntegerRestrict K L σ)

section MixedL

variable [IsMixedCharLocalField L]
omit [IsValuativeTopology L]

/- The value of a unit-times-irreducible-power: `v (u * π ^ n) = n`. -/
private theorem value_unit_mul_zpow
    (π : ↥𝒪[L]) (hπ : Irreducible π) (u : (↥𝒪[L])ˣ)
    (h1 : algebraMap ↥𝒪[L] L (u : ↥𝒪[L]) ≠ 0) (h2 : algebraMap ↥𝒪[L] L π ≠ 0) (n : ℤ) :
    normalizedValuation L (Units.mk0 (algebraMap ↥𝒪[L] L (u : ↥𝒪[L])) h1 *
      (Units.mk0 (algebraMap ↥𝒪[L] L π) h2) ^ n) = n := by
  rw [normalizedValuation_mul, normalizedValuation_zpow]
  have hu : normalizedValuation L (Units.mk0 (algebraMap ↥𝒪[L] L (u : ↥𝒪[L])) h1) = 0 := by
    refine normalizedValuation_eq_zero_of_valuation_eq_one L _ ?_
    exact (Valuation.integer.integers (v := valuation L)).valuation_unit u
  have hπ1 : normalizedValuation L (Units.mk0 (algebraMap ↥𝒪[L] L π) h2) = 1 := by
    refine normalizedValuation_irreducible L π hπ _ ?_
    rfl
  rw [hu, hπ1]
  ring

/-- **A `K`-automorphism preserves the normalized valuation**: `w ∘ s` prolongs the base
valuation, hence coincides with `w` — Serre's Corollary 3, whose proof is this statement —
rendered through the factorization of a unit into a unit of the integers times an
irreducible power, both of which the automorphism preserves
([Serre 1979, Chap. II, §2, Prop. 3, p.28, and Cor. 2–3, p.29][Serre1979]). -/
theorem normalizedValuation_algEquiv (σ : L ≃ₐ[K] L) (x : Lˣ) :
    normalizedValuation L (Units.map (σ : L →* L) x) = normalizedValuation L x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (↥𝒪[L])
  have hx0 : (x : L) ≠ 0 := Units.ne_zero x
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ hx0
  have hinj : Function.Injective (algebraMap ↥𝒪[L] L) := IsFractionRing.injective ↥𝒪[L] L
  have hne : ∀ a : ↥𝒪[L], a ≠ 0 → algebraMap ↥𝒪[L] L a ≠ 0 := fun a ha h0 =>
    ha (hinj (by rwa [map_zero]))
  have hϖ0 : algebraMap ↥𝒪[L] L ϖ ≠ 0 := hne ϖ hϖ.ne_zero
  have hu0 : algebraMap ↥𝒪[L] L (u : ↥𝒪[L]) ≠ 0 := hne _ (Units.ne_zero u)
  have hxeq : x = Units.mk0 (algebraMap ↥𝒪[L] L (u : ↥𝒪[L])) hu0 *
      (Units.mk0 (algebraMap ↥𝒪[L] L ϖ) hϖ0) ^ n := by
    ext
    push_cast [hu, Units.smul_def, Algebra.smul_def]
    rfl
  -- the automorphism transports the factorization
  set σO := algEquivIntegerRestrict K L σ with hσO
  set σu : (↥𝒪[L])ˣ := Units.map σO.toRingHom.toMonoidHom u with hσu
  have hσu0 : algebraMap ↥𝒪[L] L (σu : ↥𝒪[L]) ≠ 0 := hne _ (Units.ne_zero σu)
  have hσϖ0 : algebraMap ↥𝒪[L] L (σO ϖ) ≠ 0 := hne _ (by
    intro h0
    exact hϖ.ne_zero (σO.injective (by rw [h0, map_zero])))
  have hxval : (x : L) = algebraMap ↥𝒪[L] L (u : ↥𝒪[L]) * (algebraMap ↥𝒪[L] L ϖ) ^ n := by
    rw [hu, Units.smul_def, Algebra.smul_def]
  have hmapeq : Units.map (σ : L →* L) x =
      Units.mk0 (algebraMap ↥𝒪[L] L (σu : ↥𝒪[L])) hσu0 *
        (Units.mk0 (algebraMap ↥𝒪[L] L (σO ϖ)) hσϖ0) ^ n := by
    ext
    change σ (x : L) = _
    rw [hxval, map_mul, map_zpow₀]
    push_cast
    rfl
  rw [hmapeq, hxeq, value_unit_mul_zpow (L := L) ϖ hϖ u hu0 hϖ0 n,
    value_unit_mul_zpow (L := L) (σO ϖ)
      (algEquivIntegerRestrict_irreducible K L σ hϖ) σu hσu0 hσϖ0 n]

end MixedL

end Atlas.Knowledge
