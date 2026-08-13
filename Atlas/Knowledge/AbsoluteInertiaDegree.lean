import Mathlib

/-!
# absolute inertia degree

The **absolute inertia degree** `f_K` of a mixed-characteristic local field: the degree
`[𝓀[K] : 𝔽_{p_K}]` of its residue field over the prime field, for `p_K` the residue
characteristic `Atlas.Knowledge.ResidueCharacteristic`. Together with the absolute ramification
index `Atlas.Knowledge.AbsoluteRamificationIndex` it determines the absolute degree
`Atlas.Knowledge.AbsoluteDegree`, and it is one of the six invariants the anabelian layer
recovers group-theoretically.

## Main definitions

* `absoluteInertiaDegree` — the inertia degree of `𝓂[K]` over `ℤ`.

## Implementation notes

Encoded as Mathlib's `Ideal.inertiaDeg 𝓂[K] ℤ`, the rank of the residue field of `𝓂[K]` over
that of its pullback to `ℤ`—the prime `(p_K)`, whose residue field is `𝔽_{p_K}`. As with the
ramification index, this is inertia over `ℚ_{p_K}` without a `ℚ_[p]`-algebra structure, and
outside the local-field situation the encoding takes Mathlib's junk values.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

open ValuativeRel

namespace Atlas.Knowledge

/-- The **absolute inertia degree** of a mixed-characteristic local field: the degree of its
residue field over the prime field `𝔽_{p_K}`, encoded as the inertia degree of `𝓂[K]` over `ℤ`
([Hyeon 2025, §3, p.9][Hyeon2025]). -/
noncomputable def absoluteInertiaDegree (K : Type*) [Field K] [ValuativeRel K] : ℕ :=
  Ideal.inertiaDeg 𝓂[K] ℤ

end Atlas.Knowledge
