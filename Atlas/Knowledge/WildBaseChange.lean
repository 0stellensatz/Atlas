import Mathlib
import Atlas.Knowledge.AbsoluteInertiaDegree
import Atlas.Knowledge.AbsoluteRamificationIndex
import Atlas.Knowledge.IsStarQuotient
import Atlas.Knowledge.IsUnitFiltration
import Atlas.Knowledge.ShiftRhoEP
import Atlas.Knowledge.TRhoEP

/-!
# jump set under wild base change

The source's extrapolation of the invariant along a totally ramified extension of arbitrary
degree: away from the exceptional level `p e / (p - 1)`, a level of the base invariant whose
gap to its predecessor exceeds the `p`-adic valuation of the degree survives into the top
invariant, scaled by the prime-to-`p` part of the degree with its multiplicity raised by the
`p`-part's exponent; the exceptional level survives with full scaling and multiplicity
unchanged; and when every consecutive gap exceeds that exponent, the whole invariant off the
exceptional level transports. These are the source's Theorem 12.2, Theorem 12.3, and
Corollary 12.5, the wild counterpart of `Atlas.Knowledge.TameBaseChange`.

## Main statements

All are claims recorded ahead of their proofs.

* `mem_isStarQuotient_of_gap` — the pointwise extrapolation under the gap condition:
  Theorem 12.2.
* `mem_isStarQuotient_of_exceptional` — the exceptional level transports with full scaling:
  Theorem 12.3.
* `map_subset_isStarQuotient_of_gaps` — under consecutive gaps the whole invariant off the
  exceptional level transports: Corollary 12.5.

## Implementation notes

The exceptional level `p e / (p - 1)` is spelled multiplicatively, `i (p - 1) ≠ p e`, exact
at every `e` where the source's fraction need not be integral. The gap conditions are spelled
additively—`β (i) + v_p (d) < β (max J)` and its consecutive form—so no natural-number
subtraction enters them. The scaled level divides the `p`-part out of the degree, an exact
division; `Nat.toPNat'` never junks there. The extension and the two invariants enter by the
standing devices, one filtration and presenting pair per field, the shared inertia degree
and the ramification relation derivable from the totally ramified generation; the source's
standing base, a finite extension of `ℚ_p (ζ_p)`, is carried semantically as in
`Atlas.Knowledge.TameBaseChange`, a presenting pair existing exactly over a field with a
`p`-th root of unity.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open ValuativeRel

/-- The pointwise wild extrapolation: away from the exceptional level, a level whose gap to
its predecessor exceeds `v_p (d)` survives into the top invariant, scaled by the
prime-to-`p` part of the degree with its multiplicity raised by `v_p (d)`. Claim recorded
ahead of its proof ([Pagano 2022, Thm. 12.2, p.474][Pagano2022]). -/
theorem mem_isStarQuotient_of_gap (p e₁ e₂ f d : ℕ+) [Fact (p : ℕ).Prime] (hp1 : 1 < p)
    (K₁ K₂ : Type) [Field K₁] [ValuativeRel K₁] [TopologicalSpace K₁]
    [IsMixedCharLocalField K₁] [Field K₂] [ValuativeRel K₂] [TopologicalSpace K₂]
    [IsMixedCharLocalField K₂] [Algebra K₁ K₂]
    (hpres : (p : ℕ) = residueCharacteristic K₁)
    (he₁ : (e₁ : ℕ) = absoluteRamificationIndex K₁)
    (he₂ : (e₂ : ℕ) = absoluteRamificationIndex K₂)
    (hf : (f : ℕ) = absoluteInertiaDegree K₁)
    (g : Polynomial ↥𝒪[K₁]) (hg : g.IsEisensteinAt (IsLocalRing.maximalIdeal ↥𝒪[K₁]))
    (hd : (d : ℕ) = g.natDegree)
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
      (T_ρ_ep_finite e₂ p hp1) f ((p : ℕ) : ℤ_[(p : ℕ)]) PadicInt.irreducible_p P₂ F₂)
    {pt : ℕ+ × ℕ+} (hpt : pt ∈ P₁)
    (hexc : (pt.1 : ℕ) * ((p : ℕ) - 1) ≠ (p : ℕ) * (e₁ : ℕ))
    (hgap : ∀ pt' ∈ P₁, pt'.1 < pt.1 →
      (∀ pt'' ∈ P₁, pt''.1 < pt.1 → pt''.1 ≤ pt'.1) →
      (pt.2 : ℕ) + padicValNat (p : ℕ) (d : ℕ) < (pt'.2 : ℕ)) :
    (((d : ℕ) / (p : ℕ) ^ padicValNat (p : ℕ) (d : ℕ) * (pt.1 : ℕ)).toPNat',
      (⟨(pt.2 : ℕ) + padicValNat (p : ℕ) (d : ℕ), Nat.add_pos_left pt.2.pos _⟩ : ℕ+)) ∈
      P₂ := by
  sorry

/-- The exceptional level transports with full scaling and unchanged multiplicity. Claim
recorded ahead of its proof ([Pagano 2022, Thm. 12.3, p.475][Pagano2022]). -/
theorem mem_isStarQuotient_of_exceptional (p e₁ e₂ f d : ℕ+) [Fact (p : ℕ).Prime]
    (hp1 : 1 < p)
    (K₁ K₂ : Type) [Field K₁] [ValuativeRel K₁] [TopologicalSpace K₁]
    [IsMixedCharLocalField K₁] [Field K₂] [ValuativeRel K₂] [TopologicalSpace K₂]
    [IsMixedCharLocalField K₂] [Algebra K₁ K₂]
    (hpres : (p : ℕ) = residueCharacteristic K₁)
    (he₁ : (e₁ : ℕ) = absoluteRamificationIndex K₁)
    (he₂ : (e₂ : ℕ) = absoluteRamificationIndex K₂)
    (hf : (f : ℕ) = absoluteInertiaDegree K₁)
    (g : Polynomial ↥𝒪[K₁]) (hg : g.IsEisensteinAt (IsLocalRing.maximalIdeal ↥𝒪[K₁]))
    (hd : (d : ℕ) = g.natDegree)
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
      (T_ρ_ep_finite e₂ p hp1) f ((p : ℕ) : ℤ_[(p : ℕ)]) PadicInt.irreducible_p P₂ F₂)
    {pt : ℕ+ × ℕ+} (hpt : pt ∈ P₁)
    (hexc : (pt.1 : ℕ) * ((p : ℕ) - 1) = (p : ℕ) * (e₁ : ℕ)) :
    (d * pt.1, pt.2) ∈ P₂ := by
  sorry

/-- Under gaps exceeding `v_p (d)` at every consecutive pair, the whole invariant off the
exceptional level transports, scaled by the prime-to-`p` part with multiplicities raised by
`v_p (d)`. Claim recorded ahead of its proof
([Pagano 2022, Cor. 12.5, pp.475–476][Pagano2022]). -/
theorem map_subset_isStarQuotient_of_gaps (p e₁ e₂ f d : ℕ+) [Fact (p : ℕ).Prime]
    (hp1 : 1 < p)
    (K₁ K₂ : Type) [Field K₁] [ValuativeRel K₁] [TopologicalSpace K₁]
    [IsMixedCharLocalField K₁] [Field K₂] [ValuativeRel K₂] [TopologicalSpace K₂]
    [IsMixedCharLocalField K₂] [Algebra K₁ K₂]
    (hpres : (p : ℕ) = residueCharacteristic K₁)
    (he₁ : (e₁ : ℕ) = absoluteRamificationIndex K₁)
    (he₂ : (e₂ : ℕ) = absoluteRamificationIndex K₂)
    (hf : (f : ℕ) = absoluteInertiaDegree K₁)
    (g : Polynomial ↥𝒪[K₁]) (hg : g.IsEisensteinAt (IsLocalRing.maximalIdeal ↥𝒪[K₁]))
    (hd : (d : ℕ) = g.natDegree)
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
      (T_ρ_ep_finite e₂ p hp1) f ((p : ℕ) : ℤ_[(p : ℕ)]) PadicInt.irreducible_p P₂ F₂)
    (hgap : ∀ pt ∈ P₁, ∀ pt' ∈ P₁, pt.1 < pt'.1 →
      (¬∃ ptm ∈ P₁, pt.1 < ptm.1 ∧ ptm.1 < pt'.1) →
      (pt'.2 : ℕ) + padicValNat (p : ℕ) (d : ℕ) < (pt.2 : ℕ)) :
    ∀ pt ∈ P₁, (pt.1 : ℕ) * ((p : ℕ) - 1) ≠ (p : ℕ) * (e₁ : ℕ) →
      (((d : ℕ) / (p : ℕ) ^ padicValNat (p : ℕ) (d : ℕ) * (pt.1 : ℕ)).toPNat',
        (⟨(pt.2 : ℕ) + padicValNat (p : ℕ) (d : ℕ), Nat.add_pos_left pt.2.pos _⟩ : ℕ+)) ∈
        P₂ := by
  sorry

end Atlas.Knowledge
