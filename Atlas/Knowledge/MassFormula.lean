import Mathlib
import Atlas.Knowledge.AbsoluteInertiaDegree
import Atlas.Knowledge.AbsoluteRamificationIndex
import Atlas.Knowledge.ExtendedGameMeasure
import Atlas.Knowledge.IsAdmissibleJumpPair
import Atlas.Knowledge.IsStarQuotient
import Atlas.Knowledge.IsUnitFiltration
import Atlas.Knowledge.SerreMass
import Atlas.Knowledge.ShiftEPrime
import Atlas.Knowledge.ShiftRhoEP
import Atlas.Knowledge.TRhoEP

/-!
# mass formula for the unit filtration

The source's mass formula: among the totally ramified degree-`e / (p - 1)` extensions of
`ℚ_{p^f} (ζ_p)`, weighted by the Serre mass of `Atlas.Knowledge.SerreMass`, the probability
that the invariant `(I_K, β_K)` is a given pair equals the pair's mass under the extended
shooting game of `Atlas.Knowledge.ExtendedGameMeasure` at the start `e'_ρ`. This is the
quantitative strengthening of the realizability circle—which pairs occur is
`Atlas.Knowledge.JumpSetRealization`, and *how often* is this formula—and the two ways of
weighing an invariant meet through the Haar bridge `Atlas.Knowledge.HaarGameMass`.

## Main definitions

* `HasStarInvariant` — the invariant of a subfield of the closure, read through its
  mixed-characteristic local models.

## Main statements

* `serreMass_eq_extendedGameMass` — the mass formula: the source's Theorem 9.1. Claim
  recorded ahead of its proof.

## Implementation notes

A subfield of the algebraic closure carries no valuative instances, so its invariant is read
through models: `HasStarInvariant` asks every mixed-characteristic local field
ring-isomorphic to the subfield to have its every unit filtration presented by the pair. For
the finite extensions the mass ranges over, the quantification is honest: models exist—a
local field has continuum cardinality, so a model lives in the lowest universe—and the
valuative structure of a mixed-characteristic local field is intrinsic, an abstract field
carrying at most one by F. K. Schmidt's theorem, so all models agree. At an infinite
subfield no model exists and the predicate is vacuously true of every pair, which the
claim's intersection with the totally ramified set never sees. The base is characterized
relationally as in
`Atlas.Knowledge.EisensteinFieldInvariant`—residue characteristic `p`, ramification `p - 1`,
inertia degree `f`, a `p`-th root of unity pin `ℚ_{p^f} (ζ_p)`—and the Serre mass's residue
size is `p^f`, the size the characterization forces. The Markov instance of the game side
enters as a hypothesis, discharged from the recorded claim as everywhere in this web.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open ValuativeRel MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The **invariant of a subfield** of the closure, read through models: every
mixed-characteristic local field ring-isomorphic to it has its every unit filtration
presented by the pair. On the finite extensions the mass ranges over, models exist and
agree, so this is the source's `(I_K, β_K) = (I, β)`; at an infinite subfield the predicate
is vacuously true, and no consumer looks there
([Pagano 2022, §1.1.2, p.406][Pagano2022]). -/
def HasStarInvariant (F : Type*) [Field F] [ValuativeRel F]
    (K : IntermediateField F (AlgebraicClosure F)) (p e f : ℕ+) [Fact (p : ℕ).Prime]
    (hp1 : 1 < p) (P : Finset (ℕ+ × ℕ+)) : Prop :=
  ∀ (K' : Type) [Field K'] [ValuativeRel K'] [TopologicalSpace K']
    [IsMixedCharLocalField K'], (↥K ≃+* K') →
    ∀ (m : Module ℤ_[(p : ℕ)] (Additive ↥(higherUnitGroup K' 1)))
      (F' : @FilteredModule ℤ_[(p : ℕ)] _ (Additive ↥(higherUnitGroup K' 1)) _ m),
      @IsUnitFiltration K' _ _ (p : ℕ) _ m F' →
        @IsStarQuotient ℤ_[(p : ℕ)] _ _ _ _ _ m (ρ_ep e p hp1) (T_ρ_ep_finite e p hp1) f
          ((p : ℕ) : ℤ_[(p : ℕ)]) PadicInt.irreducible_p P F'

/-- The **mass formula**: over `ℚ_{p^f} (ζ_p)`, the Serre mass of the totally ramified
degree-`e / (p - 1)` extensions with invariant a given pair equals the pair's mass under the
extended shooting game at the start `e'_ρ`. Claim recorded ahead of its proof
([Pagano 2022, Thm. 9.1, p.460][Pagano2022]; [Pagano 2022, Thm. 1.7, p.407][Pagano2022] is
its Haar-side form). -/
theorem serreMass_eq_extendedGameMass (p e f h : ℕ+) [Fact (p : ℕ).Prime] (hp1 : 1 < p)
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsMixedCharLocalField F]
    (hpF : (p : ℕ) = residueCharacteristic F)
    (heF : (p : ℕ) - 1 = absoluteRamificationIndex F)
    (hfF : (f : ℕ) = absoluteInertiaDegree F)
    (hζ : ∃ ζ : Fˣ, ζ ^ (p : ℕ) = 1 ∧ ζ ≠ 1)
    (he : (e : ℕ) = (h : ℕ) * ((p : ℕ) - 1))
    [∀ n, IsMarkovKernel (extendedGameHistoryKernel (ρ_ep e p hp1) (T_ρ_ep_finite e p hp1) p
      (p ^ (f : ℕ)) n)]
    {P : Finset (ℕ+ × ℕ+)}
    (hP : IsAdmissibleJumpPair (ρ_ep e p hp1) (T_ρ_ep_finite e p hp1) P) :
    serreMass F (p ^ (f : ℕ)) h {K | HasStarInvariant F K p e f hp1 P} =
      extendedGameMass (ρ_ep e p hp1) (T_ρ_ep_finite e p hp1) p (p ^ (f : ℕ))
        (Shift.e' (T_ρ_ep_finite e p hp1)) P := by
  sorry

end Atlas.Knowledge
