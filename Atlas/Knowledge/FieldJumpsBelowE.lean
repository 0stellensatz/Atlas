import Mathlib
import Atlas.Knowledge.AbsoluteInertiaDegree
import Atlas.Knowledge.AbsoluteRamificationIndex
import Atlas.Knowledge.IsStarQuotient
import Atlas.Knowledge.IsUnitFiltration
import Atlas.Knowledge.PolynomialStoppedPair
import Atlas.Knowledge.ShiftRhoEP
import Atlas.Knowledge.TRhoEP

/-!
# field jumps below e from the polynomial

The source's Theorem 10.1: at level `j`, the part of the cut-out field's invariant lying
below `e` is computed by the stopped pair of the Eisenstein polynomial—the points of the
presenting pair whose level satisfies `p^{β - j - 1} · i < e` are exactly the points of
`Atlas.Knowledge.PolynomialStoppedPair` with every multiplicity raised by `j`. This is the
level-`j` generalization of `Atlas.Knowledge.EisensteinFieldInvariant`'s Theorem 1.11, which
it recovers at `j = 0` on the full pair; above the cut nothing is asserted, which is the
theorem's honesty about where the coefficients stop seeing the field.

## Main statements

* `isStarQuotient_filter_eq_polynomialStoppedPair` — Theorem 10.1. Claim recorded ahead of
  its proof.

## Implementation notes

The base is `ℚ_{p^f} (ζ_{p^{j+1}})`, characterized relationally as in
`Atlas.Knowledge.StronglyEisensteinExtremal`; the cut-out field enters by a generating root,
and its invariant by the star-quotient relation over any unit filtration, the layer's
standing devices. The exponent `β - j - 1` is natural-number subtraction, exact where the
filter consults it: over a base with a primitive `p^{j+1}`-th root of unity every
multiplicity of the presenting pair is at least `j + 1`, the torsion of the unit filtration
having order at least `p^{j+1}` and `Atlas.Knowledge.QuasiFreeTorsion` reading that order off
the minimal multiplicity. The multiplicity shift by `j` on the polynomial side matches the
source's `β (i_k) = v_p (α_k) + j + 1`, the stopped pair carrying `v_p (α_k) + 1`.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open ValuativeRel

/-- The source's Theorem 10.1: below `e`, the presenting pair of the field cut out by an
Eisenstein polynomial over `ℚ_{p^f} (ζ_{p^{j+1}})` is the polynomial's stopped pair with
every multiplicity raised by `j`. Claim recorded ahead of its proof
([Pagano 2022, Thm. 10.1, p.469][Pagano2022]). -/
theorem isStarQuotient_filter_eq_polynomialStoppedPair (p e f : ℕ+) (j : ℕ)
    [Fact (p : ℕ).Prime] (hp1 : 1 < p)
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsMixedCharLocalField E]
    (hpE : (p : ℕ) = residueCharacteristic E)
    (heE : (p : ℕ) ^ j * ((p : ℕ) - 1) = absoluteRamificationIndex E)
    (hfE : (f : ℕ) = absoluteInertiaDegree E)
    (hζ : ∃ ζ : Eˣ, ζ ^ ((p : ℕ) ^ (j + 1)) = 1 ∧ ζ ^ ((p : ℕ) ^ j) ≠ 1)
    (g : Polynomial ↥𝒪[E]) (hg : g.IsEisensteinAt (IsLocalRing.maximalIdeal ↥𝒪[E]))
    (he : (e : ℕ) = g.natDegree * ((p : ℕ) ^ j * ((p : ℕ) - 1)))
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
    [Algebra E K] (π : K) (hroot : Polynomial.aeval π (g.map (algebraMap ↥𝒪[E] E)) = 0)
    (hgen : Algebra.adjoin E {π} = ⊤)
    (m : Module ℤ_[(p : ℕ)] (Additive ↥(higherUnitGroup K 1)))
    (F : @FilteredModule ℤ_[(p : ℕ)] _ (Additive ↥(higherUnitGroup K 1)) _ m)
    (hF : @IsUnitFiltration K _ _ (p : ℕ) _ m F)
    {P : Finset (ℕ+ × ℕ+)}
    (hP : IsJumpPair (ρ_ep e p hp1) (Shift.T_star (ρ_ep e p hp1) (T_ρ_ep_finite e p hp1)) P)
    (hQ : @IsStarQuotient ℤ_[(p : ℕ)] _ _ _ _ _ m (ρ_ep e p hp1) (T_ρ_ep_finite e p hp1) f
      ((p : ℕ) : ℤ_[(p : ℕ)]) PadicInt.irreducible_p P F) :
    P.filter (fun pt => (p : ℕ) ^ ((pt.2 : ℕ) - j - 1) * (pt.1 : ℕ) < (e : ℕ)) =
      (polynomialStoppedPair (p : ℕ) e g).image
        (fun pt => (pt.1, (⟨(pt.2 : ℕ) + j, Nat.add_pos_left pt.2.pos j⟩ : ℕ+))) := by
  sorry

end Atlas.Knowledge
