import Mathlib
import Atlas.Knowledge.AbsoluteInertiaDegree
import Atlas.Knowledge.AbsoluteRamificationIndex

/-!
# absolute degree

The **absolute degree** `d_K = [K : ℚ_{p_K}]` of a mixed-characteristic local field, encoded
through the fundamental identity `d = e * f` from the absolute ramification index
`Atlas.Knowledge.AbsoluteRamificationIndex` and the absolute inertia degree
`Atlas.Knowledge.AbsoluteInertiaDegree`. It is one of the six invariants the anabelian layer
recovers group-theoretically—the rank of the free `ℤ_p`-part of `G_K^ab` is `d_K`, which is how
Mochizuki already recovers it.

## Main definitions

* `absoluteDegree` — the product `e_K * f_K`.

## Implementation notes

The sources define `d_K` as the degree `[K : ℚ_{p_K}]` and use `d = e * f` as a fact; here the
carrier `Atlas.Knowledge.IsMixedCharLocalField` carries no `ℚ_[p]`-algebra structure, so the
identity is the definition, and agreement with `Module.finrank ℚ_[p] K`, once such a structure is
in play, is a theorem for the layer to record then.

## References

* [Mochizuki1997] S. Mochizuki, *A version of the Grothendieck conjecture for p-adic local
  fields*, Int. J. Math. **8** (1997), 499–506.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

/-- The **absolute degree** `d_K = [K : ℚ_{p_K}]` of a mixed-characteristic local field, encoded
by the fundamental identity as `e_K * f_K`
([Mochizuki 1997, Prop. 1.2, p.501][Mochizuki1997]; [Hyeon 2025, §3, p.9][Hyeon2025]). -/
noncomputable def absoluteDegree (K : Type*) [Field K] [ValuativeRel K] : ℕ :=
  absoluteRamificationIndex K * absoluteInertiaDegree K

end Atlas.Knowledge
