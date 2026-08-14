import Mathlib
import Atlas.Knowledge.HerbrandPhi

/-!
# Herbrand function ψ

The inverse Herbrand function of a finite Galois extension of local fields: `ψ` is the inverse
of the homeomorphism `φ` of `Atlas.Knowledge.HerbrandPhi`, the function that renumbers the
upper numbering back into the lower. This file defines `ψ` as `Function.invFun` of `φ` and
proves the API that `Atlas.Knowledge.UpperRamificationGroup` consumes: the two inverse
identities, `ψ (0) = 0`, strict monotonicity, and bijectivity, all under
`FiniteDimensional K L`; transitivity in a tower is recorded as a claim.

## Main definitions

* `herbrandPsi` — `ψ = φ⁻¹`.

## Main statements

* `herbrandPhi_herbrandPsi` / `herbrandPsi_herbrandPhi` — the inverse identities.
* `herbrandPsi_zero`, `herbrandPsi_strictMono`, `herbrandPsi_bijective` — the order API.
* `herbrandPsi_comp` — transitivity in a tower, recorded ahead of its proof.

## Implementation notes

The source defines `ψ` as the inverse of `φ` on `[-1, +∞)`; here `φ` is a bijection of all of
`ℝ`—its junk region below `-1` was kept strictly increasing for exactly this purpose—so `ψ` is
the global `Function.invFun`, total and choice-free on the range, and the inverse identities
hold on all of `ℝ` with no domain side conditions. Everything asks for
`FiniteDimensional K L`: without it `φ` collapses to `0` and `invFun` returns junk. The
source's direct-integral description of `ψ` mentions the upper numbering and is therefore
recorded in `Atlas.Knowledge.UpperRamificationGroup`, not here.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] (L : Type*) [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L]

/-- The **inverse Herbrand function** `ψ` of `L` over `K`: the inverse of the Herbrand
function `Atlas.Knowledge.herbrandPhi`
([Serre 1979, Chap. IV, §3, Prop. 13, p.73][Serre1979]). -/
noncomputable def herbrandPsi : ℝ → ℝ :=
  Function.invFun (herbrandPhi K L)

variable [FiniteDimensional K L]

/-- `φ ∘ ψ = id` ([Serre 1979, Chap. IV, §3, Prop. 13, p.73][Serre1979]). -/
@[simp]
theorem herbrandPhi_herbrandPsi (v : ℝ) : herbrandPhi K L (herbrandPsi K L v) = v :=
  Function.rightInverse_invFun (herbrandPhi_bijective K L).surjective v

/-- `ψ ∘ φ = id` ([Serre 1979, Chap. IV, §3, Prop. 13, p.73][Serre1979]). -/
@[simp]
theorem herbrandPsi_herbrandPhi (u : ℝ) : herbrandPsi K L (herbrandPhi K L u) = u :=
  Function.leftInverse_invFun (herbrandPhi_bijective K L).injective u

/-- `ψ (0) = 0` ([Serre 1979, Chap. IV, §3, Prop. 13, p.73][Serre1979]). -/
@[simp]
theorem herbrandPsi_zero : herbrandPsi K L 0 = 0 := by
  nth_rewrite 1 [← herbrandPhi_zero K L]
  rw [herbrandPsi_herbrandPhi]

/-- The inverse Herbrand function is strictly increasing
([Serre 1979, Chap. IV, §3, Prop. 13, p.73][Serre1979]). -/
theorem herbrandPsi_strictMono : StrictMono (herbrandPsi K L) := by
  intro v w hvw
  by_contra hle
  have h : herbrandPsi K L w ≤ herbrandPsi K L v := not_lt.mp hle
  have := (herbrandPhi_strictMono K L).monotone h
  rw [herbrandPhi_herbrandPsi, herbrandPhi_herbrandPsi] at this
  exact absurd this (not_le.mpr hvw)

/-- The inverse Herbrand function is a bijection of the real line
([Serre 1979, Chap. IV, §3, Prop. 13, p.73][Serre1979]). -/
theorem herbrandPsi_bijective : Function.Bijective (herbrandPsi K L) :=
  ⟨fun v w h => by
    have := congrArg (herbrandPhi K L) h
    rwa [herbrandPhi_herbrandPsi, herbrandPhi_herbrandPsi] at this,
   fun u => ⟨herbrandPhi K L u, herbrandPsi_herbrandPhi K L u⟩⟩

section Tower

variable (E : Type*) [Field E] [ValuativeRel E] [Algebra K E] [Algebra E L]
  [IsScalarTower K E L] [ValuativeExtension K E] [Algebra.IsAlgebraic E L]

/-- Transitivity of the inverse Herbrand function in a tower: `ψ_{L/K} = ψ_{L/E} ∘ ψ_{E/K}`.
Claim recorded ahead of its proof
([Serre 1979, Chap. IV, §3, Prop. 15, p.74][Serre1979]). -/
theorem herbrandPsi_comp [TopologicalSpace K] [IsMixedCharLocalField K] [IsGalois K L]
    [Normal K E] (v : ℝ) :
    herbrandPsi K L v = herbrandPsi E L (herbrandPsi K E v) := by
  sorry

end Tower

end Atlas.Knowledge
