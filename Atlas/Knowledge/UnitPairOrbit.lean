import Mathlib
import Atlas.Knowledge.BreakFunction
import Atlas.Knowledge.FiltAut

/-!
# one orbit of base units

The source's Corollary 11.4: over a strongly separable extension carrying no `p`-th root of
unity, the base units outside the second unit group lie in a single orbit of the filtered
automorphisms of the unit filtration. This is the independence claim
`Atlas.Knowledge.UnitPairIndependence` pushed through the orbit reading of
`Atlas.Knowledge.UnitPairFree`: one common pair, one orbit. The source also characterizes
the orbit through `filt-ord` of `p`-th powers, ranging over all of the extension's unit
filtration—wider than the base units here—and that description is not restated; its
positive-characteristic companion, Corollary 11.5, lives in the
equal-characteristic world this layer's vocabulary does not reach—the structural divide
`Atlas.Knowledge.ShiftRhoP` records—and is deliberately not stated.

## Main statements

* `exists_filtAut_of_stronglySeparable` — one orbit: the source's Corollary 11.4. Claim
  recorded ahead of its proof.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open ValuativeRel

/-- Over a strongly separable extension with no `p`-th root of unity, the base units outside
the second unit group lie in one orbit of the filtered automorphisms of the unit filtration.
Claim recorded ahead of its proof ([Pagano 2022, Cor. 11.4, p.473][Pagano2022]). -/
theorem exists_filtAut_of_stronglySeparable (p eL : ℕ+) [Fact (p : ℕ).Prime] (hp1 : 1 < p)
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
    (hμ : ¬∃ ζ : Lˣ, ζ ^ (p : ℕ) = 1 ∧ ζ ≠ 1)
    (m : Module ℤ_[(p : ℕ)] (Additive ↥(higherUnitGroup L 1)))
    (F : @FilteredModule ℤ_[(p : ℕ)] _ (Additive ↥(higherUnitGroup L 1)) _ m)
    (hF : @IsUnitFiltration L _ _ (p : ℕ) _ m F)
    (u₁ u₂ : ↥(higherUnitGroup L 1))
    (hu₁ : ∃ w : Kˣ, algebraMap K L (w : K) = ((u₁ : Lˣ) : L) ∧
      w ∈ higherUnitGroup K 1 ∧ w ∉ higherUnitGroup K 2)
    (hu₂ : ∃ w : Kˣ, algebraMap K L (w : K) = ((u₂ : Lˣ) : L) ∧
      w ∈ higherUnitGroup K 1 ∧ w ∉ higherUnitGroup K 2) :
    ∃ e ∈ F.filtAut, e (Additive.ofMul u₁) = Additive.ofMul u₂ := by
  sorry

end Atlas.Knowledge
