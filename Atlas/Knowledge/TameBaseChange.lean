import Mathlib
import Atlas.Knowledge.AbsoluteInertiaDegree
import Atlas.Knowledge.AbsoluteRamificationIndex
import Atlas.Knowledge.EisensteinSet
import Atlas.Knowledge.IsStarQuotient
import Atlas.Knowledge.IsUnitFiltration
import Atlas.Knowledge.ShiftRhoEP
import Atlas.Knowledge.TRhoEP

/-!
# jump set under tame base change

The source's Proposition 12.1: along a totally ramified extension of degree prime to `p`,
the invariant transforms by scaling the levels—`I_{K₂} = d · I_{K₁}` with the multiplicities
carried along. This is the easy case of the source's §12 question, which extended jump sets
are realizable over a given base; the wild answer, under gap conditions, is
`Atlas.Knowledge.WildBaseChange`.

## Main statements

* `isStarQuotient_map_of_tame` — the invariant of the top field is the base invariant with
  levels scaled by the degree: the source's Proposition 12.1. Claim recorded ahead of its
  proof.

## Implementation notes

The extension enters by Eisenstein generation with degree prime to `p`, and each field
carries its own unit filtration and presenting pair through the standing devices; the
conclusion equates the top pair with the image of the base pair under level scaling. The
parameters of both star models are pinned relationally, the top ramification the degree
times the base one.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open ValuativeRel

/-- Along a totally ramified extension of degree `d` prime to `p`, the invariant scales its
levels by `d`: `I_{K₂} = d · I_{K₁}`, multiplicities carried along. Claim recorded ahead of
its proof ([Pagano 2022, Prop. 12.1, p.473][Pagano2022]). -/
theorem isStarQuotient_map_of_tame (p e₁ e₂ f d : ℕ+) [Fact (p : ℕ).Prime] (hp1 : 1 < p)
    (K₁ K₂ : Type) [Field K₁] [ValuativeRel K₁] [TopologicalSpace K₁]
    [IsMixedCharLocalField K₁] [Field K₂] [ValuativeRel K₂] [TopologicalSpace K₂]
    [IsMixedCharLocalField K₂] [Algebra K₁ K₂]
    (hp₁ : (p : ℕ) = residueCharacteristic K₁)
    (he₁ : (e₁ : ℕ) = absoluteRamificationIndex K₁)
    (he₂ : (e₂ : ℕ) = absoluteRamificationIndex K₂)
    (hf : (f : ℕ) = absoluteInertiaDegree K₁)
    (g : Polynomial ↥𝒪[K₁]) (hg : g.IsEisensteinAt (IsLocalRing.maximalIdeal ↥𝒪[K₁]))
    (hd : (d : ℕ) = g.natDegree) (hdp : ¬ (p : ℕ) ∣ (d : ℕ))
    (π : K₂) (hroot : Polynomial.aeval π (g.map (algebraMap ↥𝒪[K₁] K₁)) = 0)
    (hgen : Algebra.adjoin K₁ {π} = ⊤)
    (m₁ : Module ℤ_[(p : ℕ)] (Additive ↥(higherUnitGroup K₁ 1)))
    (F₁ : @FilteredModule ℤ_[(p : ℕ)] _ (Additive ↥(higherUnitGroup K₁ 1)) _ m₁)
    (hF₁ : @IsUnitFiltration K₁ _ _ (p : ℕ) _ m₁ F₁)
    (m₂ : Module ℤ_[(p : ℕ)] (Additive ↥(higherUnitGroup K₂ 1)))
    (F₂ : @FilteredModule ℤ_[(p : ℕ)] _ (Additive ↥(higherUnitGroup K₂ 1)) _ m₂)
    (hF₂ : @IsUnitFiltration K₂ _ _ (p : ℕ) _ m₂ F₂)
    {P₁ P₂ : Finset (ℕ+ × ℕ+)}
    (hP₁ : IsJumpPair (ρ_ep e₁ p hp1) (Shift.T_star (ρ_ep e₁ p hp1)
      (T_ρ_ep_finite e₁ p hp1)) P₁)
    (hQ₁ : @IsStarQuotient ℤ_[(p : ℕ)] _ _ _ _ _ m₁ (ρ_ep e₁ p hp1)
      (T_ρ_ep_finite e₁ p hp1) f ((p : ℕ) : ℤ_[(p : ℕ)]) PadicInt.irreducible_p P₁ F₁)
    (hP₂ : IsJumpPair (ρ_ep e₂ p hp1) (Shift.T_star (ρ_ep e₂ p hp1)
      (T_ρ_ep_finite e₂ p hp1)) P₂)
    (hQ₂ : @IsStarQuotient ℤ_[(p : ℕ)] _ _ _ _ _ m₂ (ρ_ep e₂ p hp1)
      (T_ρ_ep_finite e₂ p hp1) f ((p : ℕ) : ℤ_[(p : ℕ)]) PadicInt.irreducible_p P₂ F₂) :
    P₂ = P₁.image fun pt => (d * pt.1, pt.2) := by
  sorry

end Atlas.Knowledge
