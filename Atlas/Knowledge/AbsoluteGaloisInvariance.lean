import Mathlib
import Atlas.Knowledge.AbsoluteDegree
import Atlas.Knowledge.IsMixedCharLocalField

/-!
# invariants of the absolute Galois group

The residue cardinality `q` and the absolute degree `d = [K : ℚ_p]` of a mixed-characteristic
local field are determined by its absolute Galois group as a topological group. This is the
source's first recovery result and the engine of its inertia criterion: local class field
theory identifies `Γ_K^ab` with the profinite completion of `Kˣ`, whose torsion counts `q - 1`
prime-to-`p` roots of unity and whose pro-`p` part has free rank `d + 1`—both readable off any
topological isomorph of `Γ_K`. Applying the count to every open subgroup is what recovers
inertia in `Atlas.Knowledge.AbsoluteInertiaInvariance`.

## Main statements

* `natCard_residueField_eq` — a topological isomorphism `Γ_K ≅ Γ_L` forces `q_K = q_L`.
  Claim recorded ahead of its proof.
* `absoluteDegree_eq` — it forces `d_K = d_L`. Claim recorded ahead of its proof.

## Implementation notes

The proofs need local class field theory and the `p`-adic logarithm, neither yet in Mathlib;
both claims wait on that development. The isomorphism is topological, as in the source—the
proof reads invariants off `Γ_K^ab`, a quotient by a topological closure.

## References

* [Mochizuki1997] S. Mochizuki, *A version of the Grothendieck conjecture for p-adic local
  fields*, Int. J. Math. **8** (1997), 499–506.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsMixedCharLocalField L]

/-- The residue cardinality of a mixed-characteristic local field is determined by its
absolute Galois group as a topological group. Claim recorded ahead of its proof
([Mochizuki 1997, Prop. 1.2, p.501][Mochizuki1997]). -/
theorem natCard_residueField_eq
    (e : Field.absoluteGaloisGroup K ≃ₜ* Field.absoluteGaloisGroup L) :
    Nat.card 𝓀[K] = Nat.card 𝓀[L] := by
  sorry

/-- The absolute degree `Atlas.Knowledge.AbsoluteDegree` of a mixed-characteristic local field
is determined by its absolute Galois group as a topological group. Claim recorded ahead of its
proof ([Mochizuki 1997, Prop. 1.2, p.501][Mochizuki1997]). -/
theorem absoluteDegree_eq
    (e : Field.absoluteGaloisGroup K ≃ₜ* Field.absoluteGaloisGroup L) :
    absoluteDegree K = absoluteDegree L := by
  sorry

end Atlas.Knowledge
