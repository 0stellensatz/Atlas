import Mathlib
import Atlas.Knowledge.AbsoluteRamificationIndex
import Atlas.Knowledge.FilteredModule
import Atlas.Knowledge.IsJumpPair
import Atlas.Knowledge.IsStronglySeparablePolynomial
import Atlas.Knowledge.IsUnitFiltration
import Atlas.Knowledge.ShiftRhoEP
import Atlas.Knowledge.TRhoEP

/-!
# break function of a module element

The source's `g_{v, M_•}` and the jump pair it attaches to a principal unit: the break
function of an element sends `k` to the weight of the element in the quotient of the filtered
module by the `k`-th power of the uniformizer, and for a base unit read in the unit filtration
of a strongly separable extension there is a unique jump pair whose multiplicities, less one,
are exactly the breaks—the source's `(I_{L/K} (u), β_{L/K} (u))`, with the break value at one
past a level reached by iterating the shift one short of the multiplicity. The torsion-free
reading and the orbit characterization are `Atlas.Knowledge.UnitPairFree`, the independence of
the unit is `Atlas.Knowledge.UnitPairIndependence`, and the one-orbit corollary is
`Atlas.Knowledge.UnitPairOrbit`.

## Main definitions

* `breakFunction` — `g_{v, M_•}`: the weight of `v` modulo each power of the uniformizer.
* `BreaksAt` — the breaks of the function are the multiplicities of the pair, less one.
* `IsBreakPair` — a jump pair with the break characterization and the evaluation property.

## Main statements

* `exists_isBreakPair` — a base unit has a unique break pair: the source's Proposition 11.1.
  Claim recorded ahead of its proof.

## Implementation notes

The weight in the quotient is read without forming it: the largest index whose filtration
step meets the element modulo `π^k`-multiples, through `FilteredModule.maxIndex`, whose junk
at an always-true condition is `⊤`—the value the source's `g` takes there as well. The guard
on the uniformizer follows the house pattern; the value depends on it only through the ideal
it generates. The base unit enters as a unit of the extension carrying a witness from the
base, the embedding device of this web, and the extension is the standing strongly separable
tower: an unramified step, characterized by equal absolute ramification, and a totally
ramified step cut by a strongly separable Eisenstein polynomial. Uniqueness in the recorded
claim quantifies over pairs with the break characterization alone, as the source states it,
the evaluation being its "moreover".

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open ValuativeRel

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

set_option linter.unusedVariables false in
-- The guard `hπ` is not consumed by the formula—the value depends on `π` only through the
-- ideal it generates—but the notion is the source's only at a uniformizer.
/-- The **break function** `g_{v, M_•}`: the weight of `v` in the quotient by each power of
the uniformizer, read as the largest filtration index meeting `v` modulo `π^k`-multiples
([Pagano 2022, §3.3.7, p.434][Pagano2022]). -/
noncomputable def breakFunction (F : FilteredModule R M) {π : R} (hπ : Irreducible π)
    (v : M) (k : ℕ) : WithTop ℕ+ :=
  FilteredModule.maxIndex fun j => v ∈ F.filt j ⊔ (Ideal.span {π ^ k} • (⊤ : Submodule R M))

/-- The **break characterization**: the function breaks exactly at the multiplicities of the
pair, less one ([Pagano 2022, Prop. 11.1, p.472][Pagano2022]). -/
def BreaksAt (F : FilteredModule R M) {π : R} (hπ : Irreducible π) (v : M)
    (P : Finset (ℕ+ × ℕ+)) : Prop :=
  ∀ k : ℕ, (breakFunction F hπ v k ≠ breakFunction F hπ v (k + 1)) ↔
    ∃ pt ∈ P, (pt.2 : ℕ) - 1 = k

/-- A **break pair** of an element: a jump pair carrying the break characterization and the
evaluation property—the break value one past a level is the shift iterated one short of the
multiplicity ([Pagano 2022, Prop. 11.1, p.472][Pagano2022]). -/
def IsBreakPair (ρ : Shift) (F : FilteredModule R M) {π : R} (hπ : Irreducible π) (v : M)
    (P : Finset (ℕ+ × ℕ+)) : Prop :=
  IsJumpPair ρ (Shift.T ρ) P ∧ BreaksAt F hπ v P ∧
    ∀ pt ∈ P, breakFunction F hπ v ((pt.1 : ℕ) + 1) =
      (((⇑ρ)^[(pt.2 : ℕ) - 1] pt.1 : ℕ+) : WithTop ℕ+)

/-- A base unit read in the unit filtration of a strongly separable extension has a unique
break pair: the source's `(I_{L/K} (u), β_{L/K} (u))`. Claim recorded ahead of its proof
([Pagano 2022, Prop. 11.1, p.472][Pagano2022]). -/
theorem exists_isBreakPair (p eL : ℕ+) [Fact (p : ℕ).Prime] (hp1 : 1 < p)
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
      w ∈ higherUnitGroup K 1 ∧ w ∉ higherUnitGroup K 2) :
    ∃ P : Finset (ℕ+ × ℕ+),
      (@IsBreakPair ℤ_[(p : ℕ)] _ _ _ m (ρ_ep eL p hp1) F _ PadicInt.irreducible_p
        (Additive.ofMul u) P) ∧
      ∀ Q : Finset (ℕ+ × ℕ+),
        IsJumpPair (ρ_ep eL p hp1) (Shift.T (ρ_ep eL p hp1)) Q →
        @BreaksAt ℤ_[(p : ℕ)] _ _ _ m F _ PadicInt.irreducible_p (Additive.ofMul u) Q →
        Q = P := by
  sorry

end Atlas.Knowledge
