import Mathlib

/-!
# absolute ramification index

The **absolute ramification index** `e_K` of a mixed-characteristic local field: the integer with
`p_K • 𝒪[K] = 𝓂[K] ^ e_K`, for `p_K` the residue characteristic
`Atlas.Knowledge.ResidueCharacteristic`. It is the `e` of every appearance of the shift
`Atlas.Knowledge.ShiftRhoEP` in the arithmetic of `K`—the same `e` that bounds how `p`-powering
moves the filtration `Atlas.Knowledge.HigherUnitGroup`—and one of the six invariants the
anabelian layer recovers group-theoretically.

## Main definitions

* `absoluteRamificationIndex` — the ramification index of `𝓂[K]` over `ℤ`.

## Implementation notes

Encoded as Mathlib's `Ideal.ramificationIdx 𝓂[K] ℤ`: the pullback of `𝓂[K]` to `ℤ` is the prime
`(p_K)`, so this is ramification over `ℚ_{p_K}` without carrying a `ℚ_[p]`-algebra structure,
which the carrier `Atlas.Knowledge.IsMixedCharLocalField` deliberately omits. Outside the
mixed-characteristic situation the encoding takes Mathlib's junk values—in equal characteristic
`p` the ideal `p • 𝒪[K]` is `⊥` and the value is `0`.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

open ValuativeRel

namespace Atlas.Knowledge

/-- The **absolute ramification index** of a mixed-characteristic local field: the integer `e_K`
with `p_K • 𝒪[K] = 𝓂[K] ^ e_K`, encoded as the ramification index of `𝓂[K]` over `ℤ`
([Hyeon 2025, §3, p.9][Hyeon2025]). -/
noncomputable def absoluteRamificationIndex (K : Type*) [Field K] [ValuativeRel K] : ℕ :=
  Ideal.ramificationIdx 𝓂[K] ℤ

end Atlas.Knowledge
