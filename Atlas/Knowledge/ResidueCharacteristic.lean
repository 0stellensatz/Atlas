import Mathlib

/-!
# residue characteristic

The **residue characteristic** `p_K` of a valued field: the characteristic of the residue field
`𝓀[K]` of its valuation ring. For a nonarchimedean local field the residue field is finite, so
`p_K` is a prime; it is the `p` of every appearance of the shift `Atlas.Knowledge.ShiftRhoEP` in
the arithmetic of `K`, and the first of the six invariants the anabelian layer recovers
group-theoretically.

## Main definitions

* `residueCharacteristic` — `ringChar 𝓀[K]`.

## Main statements

* `residueCharacteristic_prime` — for a nonarchimedean local field it is a prime.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

open ValuativeRel

namespace Atlas.Knowledge

/-- The **residue characteristic** of a valued field: the characteristic of the residue field of
its valuation ring ([Hyeon 2025, §3, p.9][Hyeon2025]). -/
noncomputable def residueCharacteristic (K : Type*) [Field K] [ValuativeRel K] : ℕ :=
  ringChar 𝓀[K]

/-- The residue characteristic of a nonarchimedean local field is a prime, the residue field
being finite ([Hyeon 2025, §3, p.9][Hyeon2025]). -/
theorem residueCharacteristic_prime (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : (residueCharacteristic K).Prime := by
  haveI := ringChar.charP 𝓀[K]
  exact (CharP.char_is_prime_or_zero 𝓀[K] (ringChar 𝓀[K])).resolve_right
    (CharP.ringChar_ne_zero_of_finite (R := 𝓀[K]))

end Atlas.Knowledge
