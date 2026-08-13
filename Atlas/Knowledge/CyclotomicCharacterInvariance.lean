import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.ResidueCharacteristic

/-!
# group-theoreticity of the cyclotomic character

The `p`-adic cyclotomic character of a mixed-characteristic local field of residue
characteristic `p` is determined by its absolute Galois group as a topological group: any
topological isomorphism `Γ_K ≅ Γ_L` intertwines the two characters. The source derives this
from local Tate duality—`H^2 (K, M) ≅ ℤ/p^n` picks out `M ≅ ℤ/p^n (1)` among the
`Γ_K`-modules that are `ℤ/p^n` as groups, a purely group-theoretic test—and it is the first of
the three Section 1 recoveries, the other two being
`Atlas.Knowledge.AbsoluteGaloisInvariance` and `Atlas.Knowledge.AbsoluteInertiaInvariance`.

## Main statements

* `cyclotomicCharacter_comp` — `χ_L ∘ α = χ_K` for every topological isomorphism
  `α : Γ_K ≅ Γ_L`, through Mathlib's `cyclotomicCharacter` on the algebraic closures. Claim
  recorded ahead of its proof.

## Implementation notes

Mathlib's `cyclotomicCharacter` is a character of the ring automorphisms of a field with
enough `p`-power roots of unity, which the algebraic closures have in characteristic `0`; the
Galois elements enter through their underlying ring automorphisms. The prime is pinned to the
residue characteristic of both fields, as in the source, whose `K` and `K'` are local fields
over the one fixed `p`; for other primes the source claims nothing.

## References

* [Mochizuki1997] S. Mochizuki, *A version of the Grothendieck conjecture for p-adic local
  fields*, Int. J. Math. **8** (1997), 499–506.
-/

open ValuativeRel

namespace Atlas.Knowledge

/-- A topological isomorphism of absolute Galois groups of mixed-characteristic local fields
of residue characteristic `p` intertwines the `p`-adic cyclotomic characters. Claim recorded
ahead of its proof ([Mochizuki 1997, Prop. 1.1, p.501][Mochizuki1997]). -/
theorem cyclotomicCharacter_comp {p : ℕ} [Fact p.Prime] (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsMixedCharLocalField K] (L : Type*) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsMixedCharLocalField L] (hK : residueCharacteristic K = p)
    (hL : residueCharacteristic L = p)
    (e : Field.absoluteGaloisGroup K ≃ₜ* Field.absoluteGaloisGroup L)
    (g : Field.absoluteGaloisGroup K) :
    cyclotomicCharacter (AlgebraicClosure L) p
        (e g : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L).toRingEquiv =
      cyclotomicCharacter (AlgebraicClosure K) p
        (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K).toRingEquiv := by
  sorry

end Atlas.Knowledge
