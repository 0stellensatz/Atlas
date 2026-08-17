import Mathlib
import Atlas.Knowledge.IntegralClosureDVR
import Atlas.Knowledge.RamificationNumber

/-!
# ramification number as order

Serre's definition of the ramification number read literally: `i_G (σ) = v_L (σ x - x)` with
`v_L` an actual order function. `Atlas.Knowledge.RamificationNumber` recovers the source's
definition at a generator only as a membership description—`n ≤ i_G (σ)` if and only if
`σ x - x` lies in the `n`-th radical power—and this file closes the remaining gap: at a
generator `x` of the integral closure the ramification number *equals*
`IsDiscreteValuationRing.addVal` of `σ x - x`, the additive valuation of the discrete
valuation ring `integralClosure 𝒪[K] L`.

## Main statements

* `ramificationNumber_eq_addVal` — `i_G (σ) = v_L (σ x - x)` at a generator `x` of the
  integral closure, with `v_L` the additive valuation `IsDiscreteValuationRing.addVal`.

## Implementation notes

Both sides live in `ℕ∞` and are compared on their natural lower cones through
`ENat.forall_natCast_le_iff_le`, each bound `n` travelling a chain of three identifications:
the generator description `natCast_le_ramificationNumber_iff_of_adjoin_eq_top` reads
`n ≤ i_G (σ)` as membership of `σ x - x` in the `n`-th power of the Jacobson radical,
`integralClosure_jacobson_bot_eq_maximalIdeal` turns that radical into the maximal ideal of
the discrete valuation ring `Atlas.Knowledge.integralClosureDVR` provides, and membership in
the `n`-th power of the maximal ideal is the bound `n` on `IsDiscreteValuationRing.addVal`.
The last identification is generic discrete-valuation-ring material that Mathlib carries only
inline—the rewrite chain of its `IsHausdorff (IsLocalRing.maximalIdeal R) R` instance in
`Mathlib.RingTheory.DiscreteValuationRing.Basic`—so it is named here, as
`RamificationNumberEqAddVal.mem_maximalIdeal_pow_iff`, generic over a discrete valuation
ring. The scaffolding is dot-named `RamificationNumberEqAddVal.…` rather than wrapped in a
`namespace` block, the layer's prefix style for a file whose declarations share a variable
block.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] (L : Type*) [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L]

/-- Membership in the `n`-th power of the maximal ideal of a discrete valuation ring is the
lower bound `n` on the additive valuation—the rewrite chain of Mathlib's
`IsHausdorff (IsLocalRing.maximalIdeal R) R` instance, stated there only inline, named as an
iff. -/
theorem RamificationNumberEqAddVal.mem_maximalIdeal_pow_iff {R : Type*} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] {z : R} {n : ℕ} :
    z ∈ IsLocalRing.maximalIdeal R ^ n ↔ (n : ℕ∞) ≤ IsDiscreteValuationRing.addVal R z := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd, hϖ.addVal_pow]

/-- The source's definition of the ramification number, read literally: at a generator `x` of
the integral closure, `i_G (σ) = v_L (σ x - x)` with `v_L` the additive valuation
`IsDiscreteValuationRing.addVal` of the discrete valuation ring `integralClosure 𝒪[K] L`—the
last reformulation gap between the item layer and the source closed
([Serre 1979, Chap. IV, §1, p.62][Serre1979]). -/
theorem ramificationNumber_eq_addVal [TopologicalSpace K] [IsMixedCharLocalField K]
    [FiniteDimensional K L] {x : integralClosure 𝒪[K] L}
    (hx : Algebra.adjoin 𝒪[K] ({x} : Set (integralClosure 𝒪[K] L)) = ⊤) (σ : L ≃ₐ[K] L) :
    ramificationNumber K L σ =
      IsDiscreteValuationRing.addVal (integralClosure 𝒪[K] L)
        (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ x - x) := by
  apply le_antisymm
  · apply ENat.forall_natCast_le_iff_le.mp
    intro n hn
    rw [← RamificationNumberEqAddVal.mem_maximalIdeal_pow_iff,
      ← integralClosure_jacobson_bot_eq_maximalIdeal K L]
    exact (natCast_le_ramificationNumber_iff_of_adjoin_eq_top K L hx).mp hn
  · apply ENat.forall_natCast_le_iff_le.mp
    intro n hn
    rw [natCast_le_ramificationNumber_iff_of_adjoin_eq_top K L hx,
      integralClosure_jacobson_bot_eq_maximalIdeal K L]
    exact RamificationNumberEqAddVal.mem_maximalIdeal_pow_iff.mpr hn

end Atlas.Knowledge
