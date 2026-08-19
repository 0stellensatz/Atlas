import Mathlib
import Atlas.Knowledge.AbsoluteInertiaDegree
import Atlas.Knowledge.AbsoluteRamificationIndex
import Atlas.Knowledge.EisensteinJumpPair
import Atlas.Knowledge.IsStarQuotient
import Atlas.Knowledge.IsStronglySeparablePolynomial
import Atlas.Knowledge.IsUnitFiltration
import Atlas.Knowledge.ShiftRhoEP
import Atlas.Knowledge.TRhoEP

/-!
# field invariant of an Eisenstein polynomial

The identification of the polynomial-side pair with the field-side invariant: for a strongly
separable Eisenstein polynomial over the source's base `ℚ_{p^f} (ζ_p)`, the pair
`Atlas.Knowledge.eisensteinJumpPair` presents, as a star quotient
`Atlas.Knowledge.IsStarQuotient`, the unit filtration of the field the polynomial cuts out—the
source's `(I_{g(x)}, β_{g(x)}) = (I_{E_f[x]/g(x)}, β_{E_f[x]/g(x)})`, read here through the
uniqueness of `Atlas.Knowledge.UnitFiltrationClassification`. Ahead of it, the membership
upgrade that makes the identification well typed: under strong separability the pair, a
`ρ_p`-jump pair by `Atlas.Knowledge.isJumpPair_eisensteinJumpPair`, is a jump pair for the
finite-`T` shift `Atlas.Knowledge.ShiftRhoEP` as well.

## Main statements

Both are claims recorded ahead of their proofs.

* `isJumpPair_ρ_ep_eisensteinJumpPair` — the pair of a strongly separable Eisenstein
  polynomial is a `ρ_ep`-jump pair, not only a `ρ_p`-one.
* `eisensteinJumpPair_isStarQuotient` — the pair presents the unit filtration of the cut-out
  field: the source's Theorem 1.11.

## Implementation notes

The membership claim is stated over any discrete valuation ring whose `p` has valuation
`p - 1`—the device abstracting the source's base, whose ramification index over `ℚ_p` is
`p - 1`; only valuations enter the combinatorics, so no field structure is asked. The
identification claim characterizes the base relationally, as the layer's realizability claim
does: a mixed-characteristic local field with residue characteristic `p`, absolute
ramification index `p - 1`, absolute inertia degree `f`, and a `p`-th root of unity is the
source's `ℚ_{p^f} (ζ_p)`—its maximal unramified subfield adjoined a `p`-th root of unity has
the full degree, so the field is that compositum. The cut-out field enters as a
mixed-characteristic local field carrying an `E`-algebra structure together with a root of the
polynomial that generates it, the reading of `E[x] ⧸ g(x)`; the algebra structure carries no
valuative compatibility because none is needed, a field embedding of mixed-characteristic
local fields being automatically continuous. The conclusion quantifies over every module
structure and unit filtration of the cut-out field, as everywhere in this web;
`Atlas.Knowledge.IsUnitFiltration` says why the quantification costs nothing. The uniformizer
of the presentation is `p` itself, matching `Atlas.Knowledge.UnitFiltrationClassification`,
whose uniqueness claim is what makes "the pair presents the filtration" the same statement as
the source's equality of invariants.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

open ValuativeRel IsDiscreteValuationRing

namespace Atlas.Knowledge

/-- The pair of a strongly separable Eisenstein polynomial is a `ρ_ep`-jump pair at
`e = deg g · (p - 1)`, not only a `ρ_p`-one: strong separability caps the weights of the
minimal points, which is what brings the levels and their iterates into the finite-`T` world.
Claim recorded ahead of its proof ([Pagano 2022, §1.2.1, p.408][Pagano2022]). -/
theorem isJumpPair_ρ_ep_eisensteinJumpPair {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (p e : ℕ+) (hp : 1 < p) (hpp : (p : ℕ).Prime)
    {g : Polynomial R} (hg : g.IsEisensteinAt (IsLocalRing.maximalIdeal R))
    (hval : (addVal R) (((p : ℕ) : R)) = (((p : ℕ) - 1 : ℕ) : ℕ∞))
    (hss : IsStronglySeparablePolynomial (p : ℕ) g)
    (he : (e : ℕ) = g.natDegree * ((p : ℕ) - 1)) :
    IsJumpPair (ρ_ep e p hp) (Shift.T (ρ_ep e p hp)) (eisensteinJumpPair p hp g) := by
  sorry

/-- The field invariant of a strongly separable Eisenstein polynomial is its jump pair: over a
base with residue characteristic `p`, ramification index `p - 1`, inertia degree `f`, and a
`p`-th root of unity—the source's `ℚ_{p^f} (ζ_p)`—the pair of the polynomial presents the unit
filtration of the field it cuts out. Claim recorded ahead of its proof
([Pagano 2022, Thm. 1.11, p.409][Pagano2022]). -/
theorem eisensteinJumpPair_isStarQuotient (p e f : ℕ+) [Fact (p : ℕ).Prime] (hp1 : 1 < p)
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsMixedCharLocalField E]
    (hpE : (p : ℕ) = residueCharacteristic E)
    (heE : (p : ℕ) - 1 = absoluteRamificationIndex E)
    (hfE : (f : ℕ) = absoluteInertiaDegree E)
    (hζ : ∃ ζ : Eˣ, ζ ^ (p : ℕ) = 1 ∧ ζ ≠ 1)
    (g : Polynomial ↥𝒪[E]) (hg : g.IsEisensteinAt (IsLocalRing.maximalIdeal ↥𝒪[E]))
    (hss : IsStronglySeparablePolynomial (p : ℕ) g)
    (he : (e : ℕ) = g.natDegree * ((p : ℕ) - 1))
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
    [Algebra E K] (π : K) (hroot : Polynomial.aeval π (g.map (algebraMap ↥𝒪[E] E)) = 0)
    (hgen : Algebra.adjoin E {π} = ⊤)
    (m : Module ℤ_[(p : ℕ)] (Additive ↥(higherUnitGroup K 1)))
    (F : @FilteredModule ℤ_[(p : ℕ)] _ (Additive ↥(higherUnitGroup K 1)) _ m)
    (hF : @IsUnitFiltration K _ _ (p : ℕ) _ m F) :
    @IsStarQuotient ℤ_[(p : ℕ)] _ _ _ _ _ m (ρ_ep e p hp1) (T_ρ_ep_finite e p hp1) f
      ((p : ℕ) : ℤ_[(p : ℕ)]) PadicInt.irreducible_p (eisensteinJumpPair p hp1 g) F := by
  sorry

end Atlas.Knowledge
