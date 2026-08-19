import Mathlib
import Atlas.Knowledge.BreakFunction
import Atlas.Knowledge.EisensteinJumpPair

/-!
# independence of the unit pair

The source's Theorem 11.3: over a strongly separable extension, the break pair of a base
unit does not depend on the unit, and it is the jump pair of any Eisenstein polynomial
giving the totally ramified step—`(I_{L/K}, β_{L/K}) = (I_{g(x)}, β_{g(x)})`. This is what
makes the pair an invariant of the extension, computable from coefficients by the machinery
of `Atlas.Knowledge.EisensteinJumpPair`, and it is the sense in which the source's §11
generalizes its Theorem 1.11 from cut-out fields to arbitrary strongly separable extensions.

## Main statements

* `isBreakPair_eq_eisensteinJumpPair` — any break pair of any base unit is the polynomial's
  pair: the source's Theorem 11.3, its independence half folded in. Claim recorded ahead of
  its proof.

## Implementation notes

Stating that every break pair of every base unit equals one fixed pair—the polynomial's—says
both halves of the source's theorem at once: independence is equality through the common
value. The tower is the standing device of `Atlas.Knowledge.BreakFunction`: the unramified
step by equal absolute ramification, the totally ramified step cut by the strongly separable
Eisenstein polynomial whose pair the conclusion names.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open ValuativeRel

/-- Any break pair of any base unit of a strongly separable extension is the jump pair of
the Eisenstein polynomial giving its totally ramified step: the source's
`(I_{L/K}, β_{L/K}) = (I_{g(x)}, β_{g(x)})`, with independence of the unit folded into the
common value. Claim recorded ahead of its proof
([Pagano 2022, Thm. 11.3, p.472][Pagano2022]). -/
theorem isBreakPair_eq_eisensteinJumpPair (p eL : ℕ+) [Fact (p : ℕ).Prime] (hp1 : 1 < p)
    (K Mid L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
    [Field Mid] [ValuativeRel Mid] [TopologicalSpace Mid] [IsMixedCharLocalField Mid]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsMixedCharLocalField L]
    [Algebra K Mid] [Algebra Mid L] [Algebra K L] [IsScalarTower K Mid L]
    (hunr : absoluteRamificationIndex Mid = absoluteRamificationIndex K)
    (g : Polynomial ↥𝒪[Mid]) (hg : g.IsEisensteinAt (IsLocalRing.maximalIdeal ↥𝒪[Mid]))
    (hss : IsStronglySeparablePolynomial (p : ℕ) g)
    (π : L) (hroot : Polynomial.aeval π (g.map (algebraMap ↥𝒪[Mid] Mid)) = 0)
    (hgen : Algebra.adjoin Mid {π} = ⊤)
    (hpL : (p : ℕ) = residueCharacteristic L)
    (heL : (eL : ℕ) = absoluteRamificationIndex L)
    (m : Module ℤ_[(p : ℕ)] (Additive ↥(higherUnitGroup L 1)))
    (F : @FilteredModule ℤ_[(p : ℕ)] _ (Additive ↥(higherUnitGroup L 1)) _ m)
    (hF : @IsUnitFiltration L _ _ (p : ℕ) _ m F)
    (u : ↥(higherUnitGroup L 1))
    (hu : ∃ w : Kˣ, algebraMap K L (w : K) = ((u : Lˣ) : L) ∧
      w ∈ higherUnitGroup K 1 ∧ w ∉ higherUnitGroup K 2)
    {P : Finset (ℕ+ × ℕ+)}
    (hP : @IsBreakPair ℤ_[(p : ℕ)] _ _ _ m (ρ_ep eL p hp1) F _ PadicInt.irreducible_p
      (Additive.ofMul u) P) :
    P = eisensteinJumpPair p hp1 g := by
  sorry

end Atlas.Knowledge
