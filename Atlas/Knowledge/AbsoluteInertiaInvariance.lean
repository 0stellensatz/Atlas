import Mathlib
import Atlas.Knowledge.AbsoluteInertiaSubgroup
import Atlas.Knowledge.IsMixedCharLocalField

/-!
# group-theoreticity of the inertia subgroup

Every topological isomorphism between absolute Galois groups of mixed-characteristic local
fields carries the absolute inertia subgroup `Atlas.Knowledge.AbsoluteInertiaSubgroup` onto
the absolute inertia subgroup. This is the source's Corollary 1.3, and its proof is the
source's one-line application of the invariance of the residue cardinality
`Atlas.Knowledge.AbsoluteGaloisInvariance`: an open subgroup `H ≤ Γ_K` corresponds to an
unramified extension exactly when its residue cardinality is `q^[Γ_K : H]`, and inertia is the
intersection of the open subgroups that fail no such test—so any topological isomorphism
matches the two intersections.

## Main statements

* `map_absoluteInertiaSubgroup` — `α (I_K) = I_L` for every topological isomorphism
  `α : Γ_K ≅ Γ_L`. Claim recorded ahead of its proof.

## References

* [Mochizuki1997] S. Mochizuki, *A version of the Grothendieck conjecture for p-adic local
  fields*, Int. J. Math. **8** (1997), 499–506.
-/

open ValuativeRel

namespace Atlas.Knowledge

/-- A topological isomorphism of absolute Galois groups of mixed-characteristic local fields
carries inertia onto inertia. Claim recorded ahead of its proof
([Mochizuki 1997, Cor. 1.3, p.501][Mochizuki1997]). -/
theorem map_absoluteInertiaSubgroup (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsMixedCharLocalField L]
    (e : Field.absoluteGaloisGroup K ≃ₜ* Field.absoluteGaloisGroup L) :
    (absoluteInertiaSubgroup K).map e.toMulEquiv.toMonoidHom = absoluteInertiaSubgroup L := by
  sorry

end Atlas.Knowledge
