import Mathlib
import Atlas.Knowledge.AbsoluteInertiaDegree
import Atlas.Knowledge.BreakFunction
import Atlas.Knowledge.FiltAut
import Atlas.Knowledge.FiltOrd
import Atlas.Knowledge.FreeFiltered
import Atlas.Knowledge.TRhoEP

/-!
# unit pair in the torsion-free case

The source's familiar reading of the break pair when the extension carries no `p`-th root of
unity: the unit filtration is then free, and through any filtered basis the break pair of a
base unit is the filtered order of its `p`-th power—`filt-ord (u^p) = (I_{L/K} (u),
β_{L/K} (u))`—while two base units carry the same pair exactly when a filtered automorphism
of the unit filtration moves one to the other. This puts the machinery of
`Atlas.Knowledge.FiltOrd` at the service of the extension invariants, and it is the reading
by which the independence claim `Atlas.Knowledge.UnitPairIndependence` connects to the
polynomial side.

## Main statements

Both are claims recorded ahead of their proofs.

* `filtOrd_eq_of_isBreakPair` — through a filtered basis, `filt-ord (u^p)` is the break
  pair's jump set: the source's Proposition 11.2, first half.
* `isBreakPair_eq_iff_exists_filtAut` — two base units share the pair exactly when a
  filtered automorphism carries one to the other: the second half.

## Implementation notes

Freeness is hypothesized as a filtered basis—the two-sided filtered isomorphism with the free
model of `Atlas.Knowledge.FreeFiltered`—rather than through `IsFree`'s existential, so that
`filt-ord`, a function of model vectors, has a vector to eat; the absence of `p`-th roots of
unity, the source's `μ_p (L) = {1}`, is what makes such a basis exist and is carried by the
consumer of the claim through `Atlas.Knowledge.UnitFiltrationClassification`. The `p`-th
power of the unit is the `p`-scaling of its additive reading. The base units enter by the
embedding-witness device of `Atlas.Knowledge.BreakFunction`, and the pairs by their break
characterizations, the relational reading of "the" pair.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open ValuativeRel

/-- Through a filtered basis of a torsion-free unit filtration, the filtered order of the
`p`-th power of a base unit is the jump set of its break pair: the source's
`filt-ord (u^p) = (I_{L/K} (u), β_{L/K} (u))`. Claim recorded ahead of its proof
([Pagano 2022, Prop. 11.2, p.472][Pagano2022]). -/
theorem filtOrd_eq_of_isBreakPair (p eL f : ℕ+) [Fact (p : ℕ).Prime] (hp1 : 1 < p)
    (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsMixedCharLocalField L] [Algebra K L]
    (hpL : (p : ℕ) = residueCharacteristic L)
    (heL : (eL : ℕ) = absoluteRamificationIndex L)
    (hfL : (f : ℕ) = absoluteInertiaDegree L)
    (hμ : ¬∃ ζ : Lˣ, ζ ^ (p : ℕ) = 1 ∧ ζ ≠ 1)
    (m : Module ℤ_[(p : ℕ)] (Additive ↥(higherUnitGroup L 1)))
    (F : @FilteredModule ℤ_[(p : ℕ)] _ (Additive ↥(higherUnitGroup L 1)) _ m)
    (hF : @IsUnitFiltration L _ _ (p : ℕ) _ m F)
    (b : (↥(Shift.freeIndex (T_ρ_ep_finite eL p hp1) f) → ℤ_[(p : ℕ)]) ≃ₗ[ℤ_[(p : ℕ)]]
      Additive ↥(higherUnitGroup L 1))
    (hb1 : IsFilteredHom (freeFiltered (ρ_ep eL p hp1) (Shift.freeIndex
      (T_ρ_ep_finite eL p hp1) f)) F (b : _ →ₗ[ℤ_[(p : ℕ)]] _))
    (hb2 : IsFilteredHom F (freeFiltered (ρ_ep eL p hp1) (Shift.freeIndex
      (T_ρ_ep_finite eL p hp1) f)) (b.symm : _ →ₗ[ℤ_[(p : ℕ)]] _))
    (u : ↥(higherUnitGroup L 1))
    (hu : ∃ w : Kˣ, algebraMap K L (w : K) = ((u : Lˣ) : L) ∧
      w ∈ higherUnitGroup K 1 ∧ w ∉ higherUnitGroup K 2)
    {P : Finset (ℕ+ × ℕ+)}
    (hP : @IsBreakPair ℤ_[(p : ℕ)] _ _ _ m (ρ_ep eL p hp1) F _ PadicInt.irreducible_p
      (Additive.ofMul u) P) :
    filtOrd (ρ_ep eL p hp1) (b.symm (((p : ℕ) : ℤ_[(p : ℕ)]) • Additive.ofMul u)) =
      jumpSetOf (ρ_ep eL p hp1) P := by
  sorry

/-- Two base units share the break pair exactly when a filtered automorphism of the unit
filtration carries one to the other: the orbit reading of the invariant. Claim recorded
ahead of its proof ([Pagano 2022, Prop. 11.2, p.472][Pagano2022]). -/
theorem isBreakPair_eq_iff_exists_filtAut (p eL : ℕ+) [Fact (p : ℕ).Prime] (hp1 : 1 < p)
    (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsMixedCharLocalField L] [Algebra K L]
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
      w ∈ higherUnitGroup K 1 ∧ w ∉ higherUnitGroup K 2)
    {P₁ P₂ : Finset (ℕ+ × ℕ+)}
    (hP₁ : @IsBreakPair ℤ_[(p : ℕ)] _ _ _ m (ρ_ep eL p hp1) F _ PadicInt.irreducible_p
      (Additive.ofMul u₁) P₁)
    (hP₂ : @IsBreakPair ℤ_[(p : ℕ)] _ _ _ m (ρ_ep eL p hp1) F _ PadicInt.irreducible_p
      (Additive.ofMul u₂) P₂) :
    P₁ = P₂ ↔ ∃ e ∈ F.filtAut, e (Additive.ofMul u₁) = Additive.ofMul u₂ := by
  sorry

end Atlas.Knowledge
