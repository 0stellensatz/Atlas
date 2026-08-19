import Mathlib
import Atlas.Knowledge.ExtendedGameMeasure
import Atlas.Knowledge.FiltOrd
import Atlas.Knowledge.IsAdmissibleJumpPair
import Atlas.Knowledge.JumpPairOf
import Atlas.Knowledge.ShiftEPrime

/-!
# Haar mass of a jump set

The source's `μ_{q,Haar}` and its identification with the shooting game: the Haar measure of
the star model over `ℤ_p` gives each extended jump pair the normalized mass of its
`filt-ord` fiber inside the divisible vectors, and the source's Proposition 8.1 says this
mass is the extended game's, at the start `e'_ρ`. This is the bridge between the orbit
classification `Atlas.Knowledge.FiltOrd` and the probabilistic side
`Atlas.Knowledge.ExtendedGameMeasure`—the two ways of weighing an invariant that the mass
formula of the source's §9 plays against each other.

## Main definitions

* `haarMass` — the Haar measure of a set of vectors of a model over `ℤ_p`, normalized on the
  whole compact model.
* `haarJumpMass` — the source's `μ_{q,Haar}`: the fiber's mass, normalized to give the
  admissible fibers total mass one.

## Main statements

* `haarJumpMass_eq_extendedGameMass` — Haar equals game: the source's Proposition 8.1. Claim
  recorded ahead of its proof.

## Implementation notes

The star model over `ℤ_p` is compact, so it carries a Haar measure once a Borel structure is
fixed; `ℤ_p` carries no measurable-space instance in Mathlib, so the Borel structure enters
by `letI` inside `haarMass`, whose value is a mass rather than a measure—no instance escapes.
The normalization of the source—total mass one on the orbits of admissible jump sets—is the
ratio in `haarJumpMass`, under which the choice of Haar normalization cancels; the fiber of a
pair is cut by `filt-ord` returning the pair's jump set, the set determining the pair. Masses
are outer applications and need no measurability of `filt-ord`. The claim instantiates
`q = p^f`, the source's setting, over the star index of the same `f`.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal

/-- The **Haar mass** of a set of vectors of a model over `ℤ_p`: the Haar measure built on
the compact model, applied as an outer measure
([Pagano 2022, §8, p.459][Pagano2022]). -/
noncomputable def haarMass (p : ℕ) [Fact p.Prime] (D : Finset (ℕ+ × ℕ))
    (S : Set (↥D → ℤ_[p])) : ℝ≥0∞ :=
  letI : MeasurableSpace (↥D → ℤ_[p]) := borel _
  haveI : BorelSpace (↥D → ℤ_[p]) := ⟨rfl⟩
  Measure.addHaarMeasure
    ⟨⟨Set.univ, isCompact_univ⟩, by
      rw [interior_univ]
      exact ⟨fun _ => 0, trivial⟩⟩ S

/-- The source's `μ_{q,Haar}`: the Haar mass of the `filt-ord` fiber of a pair inside the
divisible vectors of the star model, normalized so the admissible fibers carry total mass
one ([Pagano 2022, §8, p.459][Pagano2022]). -/
noncomputable def haarJumpMass (ρ : Shift) (hρ : (Shift.T ρ).Finite) (p : ℕ+)
    [Fact (p : ℕ).Prime] (f : ℕ+) (P : Finset (ℕ+ × ℕ+)) : ℝ≥0∞ :=
  haarMass (p : ℕ) (Shift.starIndex hρ f)
      {v | v ∈ (Ideal.span {((p : ℕ) : ℤ_[(p : ℕ)])} •
          (⊤ : Submodule ℤ_[(p : ℕ)] (↥(Shift.starIndex hρ f) → ℤ_[(p : ℕ)]))) ∧
        filtOrd ρ v = jumpSetOf ρ P} /
    haarMass (p : ℕ) (Shift.starIndex hρ f)
      {v | v ∈ (Ideal.span {((p : ℕ) : ℤ_[(p : ℕ)])} •
          (⊤ : Submodule ℤ_[(p : ℕ)] (↥(Shift.starIndex hρ f) → ℤ_[(p : ℕ)]))) ∧
        IsAdmissibleJumpPair ρ hρ (jumpPairOf ρ (filtOrd ρ v))}

/-- Haar equals game: the normalized Haar mass of an admissible pair's fiber is its mass
under the extended shooting game at the start `e'_ρ`, with `q = p^f`. Claim recorded ahead
of its proof ([Pagano 2022, Prop. 8.1, p.459][Pagano2022]). -/
theorem haarJumpMass_eq_extendedGameMass (ρ : Shift) (hρ : (Shift.T ρ).Finite) (p f : ℕ+)
    [Fact (p : ℕ).Prime]
    [∀ n, IsMarkovKernel (extendedGameHistoryKernel ρ hρ p (p ^ (f : ℕ)) n)]
    {P : Finset (ℕ+ × ℕ+)} (hP : IsAdmissibleJumpPair ρ hρ P) :
    haarJumpMass ρ hρ p f P =
      extendedGameMass ρ hρ p (p ^ (f : ℕ)) (Shift.e' hρ) P := by
  sorry

end Atlas.Knowledge
