import Mathlib
import Atlas.Knowledge.ExtendedGameMeasure
import Atlas.Knowledge.ShiftEPrime

/-!
# level decomposition of the extended game

The two structural identities by which the source dissects the extended game along the index
of its last shooter: pulling the start back along the shift identifies the games that never
invoke a shooter below `S_j` with the full game at the pulled-back start, shifting every
multiplicity by `j - 1`; and each level relates to the next by the extra shooter's coin, the
mass of the games ending at `S_j` with a first shot from `e_ρ^*` being `p - 1` times the mass
of those ending strictly above `j`. Both are recorded on the masses of
`Atlas.Knowledge.ExtendedGameMeasure`, which is the shape the mass formula of the source's §9
consumes them in; the stopped-game remarks travel with the stopped vocabulary of the level-`j`
computation and are not stated here.

## Main statements

Both are claims recorded ahead of their proofs.

* `extendedGameMass_shift` — the shift identification: the mass of a multiplicity-shifted
  pair at the start `e'_ρ` is the conditioning mass times the mass of the pair at the
  pulled-back start.
* `extendedGameMass_level` — the level identity: `p - 1` times the mass above `j` is the mass
  at `j` with a first shot from `e_ρ^*`.

## Implementation notes

The source states the identification as an isomorphism of a *conditioned* probability space
with a plain one; on masses that is the product form recorded here, the conditioning event—a
nonempty pair with every multiplicity at least `j`—entering as a factor rather than a
normalization. The pulled-back start is hypothesized as a point reaching `e'_ρ` in `j - 1`
steps, the source's `ρ^{-(j-1)} (e'_ρ)`, which presupposes exactly that preimage. Events are
written directly on the fibers of the pair map, as the mass is; the source's range
`j ∈ {1, …, n}` for the level identity is the depth bound carried as a hypothesis.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The shift identification of the extended game: at the start `e'_ρ`, the mass of a pair
with every multiplicity raised by `j - 1` is the mass of the conditioning event—never
invoking a shooter below `S_j`—times the mass of the pair at a start reaching `e'_ρ` in
`j - 1` steps. Claim recorded ahead of its proof
([Pagano 2022, Rems. 7.2–7.3, p.458][Pagano2022]). -/
theorem extendedGameMass_shift (ρ : Shift) (hρ : (Shift.T ρ).Finite) (p q : ℕ+)
    [∀ n, IsMarkovKernel (extendedGameHistoryKernel ρ hρ p q n)]
    (j : ℕ+) (w : ℕ+) (hw : (⇑ρ)^[(j : ℕ) - 1] w = Shift.e' hρ) (P : Finset (ℕ+ × ℕ+)) :
    extendedGameMass ρ hρ p q (Shift.e' hρ)
        (P.image fun pt => (pt.1, ⟨(pt.2 : ℕ) + ((j : ℕ) - 1), Nat.add_pos_left pt.2.pos _⟩)) =
      extendedGamePathMeasure ρ hρ p q (Shift.e' hρ)
          {ω | extendedGameJumpPair ρ hρ (fun t => (ω t).val) ≠ ∅ ∧
            ∀ pt ∈ extendedGameJumpPair ρ hρ (fun t => (ω t).val), j ≤ pt.2} *
        extendedGameMass ρ hρ p q w P := by
  sorry

/-- The level identity of the extended game: `p - 1` times the mass of the games whose every
multiplicity exceeds `j` is the mass of those attaining minimum `j` with `e_ρ^*` among the
shooters. Claim recorded ahead of its proof
([Pagano 2022, Rem. 7.6, p.458][Pagano2022]). -/
theorem extendedGameMass_level (ρ : Shift) (hρ : (Shift.T ρ).Finite) (p q : ℕ+)
    [∀ n, IsMarkovKernel (extendedGameHistoryKernel ρ hρ p q n)]
    (j : ℕ+) (hj : (j : ℕ) ≤ ρ.depth (Shift.e' hρ)) :
    ((p : ℝ≥0∞) - 1) *
        extendedGamePathMeasure ρ hρ p q (Shift.e' hρ)
          {ω | extendedGameJumpPair ρ hρ (fun t => (ω t).val) ≠ ∅ ∧
            ∀ pt ∈ extendedGameJumpPair ρ hρ (fun t => (ω t).val), j + 1 ≤ pt.2} =
      extendedGamePathMeasure ρ hρ p q (Shift.e' hρ)
        {ω | (∀ pt ∈ extendedGameJumpPair ρ hρ (fun t => (ω t).val), j ≤ pt.2) ∧
          (∃ pt ∈ extendedGameJumpPair ρ hρ (fun t => (ω t).val), pt.2 = j) ∧
          ∃ m, (Shift.e_star ρ hρ, m) ∈ extendedGameJumpPair ρ hρ (fun t => (ω t).val)} := by
  sorry

end Atlas.Knowledge
