import Mathlib
import Atlas.Knowledge.ExtendedGameJumpPair
import Atlas.Knowledge.ShiftDepth

/-!
# jump pair of a stopped shooting game

The source's stopped games and what they see of the pair: two extended games are identified
when their trajectories agree as long as the rabbit stays at or below the stop, and the part
of the pair whose shots land within the stop is an invariant of the class—the content of the
source's Remark 7.4, proved here on trajectories. The stopped pair is the truncation of
`Atlas.Knowledge.ExtendedGameJumpPair` by the landing bound, so it is an extended jump pair
by restriction; and agreement below the stop transports records, so equivalent games share
it. The stopping game of an Eisenstein polynomial, an element of this stopped world, is
`Atlas.Knowledge.PolynomialStoppedPair`. The reconstruction of a full pair from a stopped one
across levels—the source's Remark 7.5—is consumed by this web through its mass consequence,
already recorded as `Atlas.Knowledge.extendedGameMass_level`, and is not restated.

## Main definitions

* `stoppedGameJumpPair` — the points of the extended pair whose shot lands at or below the
  stop.
* `StoppedEquiv` — agreement of trajectories while at or below the stop.

## Main statements

All proved.

* `isJumpPair_stoppedGameJumpPair` — the stopped pair is an extended jump pair, by
  restriction.
* `stoppedGameJumpPair_eq_of_stoppedEquiv` — equivalent games share the stopped pair: the
  source's Remark 7.4.

## Implementation notes

The truncation keeps the points with `ρ^[β] (level) ≤ x`, the source's
`ρ^{β_G (i)} (i) ≤ x`; a record contributing such a point sits at a position below its own
shot's landing, so all earlier states do too, and agreement below the stop carries the record
across—the two validity guards enter as hypotheses, one per trajectory, since off them the
pairs are the guards' empty branches and nothing is claimed. The invariance is stated for
valid strictly increasing trajectories on both sides, the only place the source's classes
live.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

/-- The **jump pair of a stopped game**: the points of the extended pair whose shot lands at
or below the stop—the class invariant of the source's stopped games
([Pagano 2022, Rem. 7.4, p.458][Pagano2022]). -/
noncomputable def stoppedGameJumpPair (ρ : Shift) (hρ : (Shift.T ρ).Finite) (x : ℕ+)
    (ω : ℕ → ℕ+ × ℕ) : Set (ℕ+ × ℕ+) :=
  extendedGameJumpPair ρ hρ ω ∩ {pt | (⇑ρ)^[(pt.2 : ℕ)] pt.1 ≤ x}

/-- The stopped pair is finite, a subset of the extended pair. -/
theorem stoppedGameJumpPair_finite (ρ : Shift) (hρ : (Shift.T ρ).Finite) (x : ℕ+)
    (ω : ℕ → ℕ+ × ℕ) : (stoppedGameJumpPair ρ hρ x ω).Finite :=
  (extendedGameJumpPair_finite ρ hρ ω).subset Set.inter_subset_left

/-- The stopped pair is an extended jump pair: a subset of one
([Pagano 2022, Rem. 7.4, p.458][Pagano2022]). -/
theorem isJumpPair_stoppedGameJumpPair (ρ : Shift) (hρ : (Shift.T ρ).Finite) (x : ℕ+)
    (ω : ℕ → ℕ+ × ℕ) :
    IsJumpPair ρ (Shift.T_star ρ hρ) (stoppedGameJumpPair_finite ρ hρ x ω).toFinset := by
  refine (isJumpPair_extendedGameJumpPair ρ hρ ω).subset ?_
  intro pt hpt
  rw [Set.Finite.mem_toFinset] at hpt ⊢
  exact hpt.1

/-- **Agreement below the stop**: two trajectories identified as long as either sits at or
below `x`—the identification defining the source's stopped games
([Pagano 2022, §7, p.458][Pagano2022]). -/
def StoppedEquiv (x : ℕ+) (ω ω' : ℕ → ℕ+ × ℕ) : Prop :=
  ∀ t, ((ω t).1 ≤ x ∨ (ω' t).1 ≤ x) → ω t = ω' t

/-- Equivalent games share the stopped pair: a record whose shot lands within the stop sits
below it with all its history, and agreement below the stop carries it across—the source's
Remark 7.4 ([Pagano 2022, Rem. 7.4, p.458][Pagano2022]). -/
theorem stoppedGameJumpPair_eq_of_stoppedEquiv (ρ : Shift) (hρ : (Shift.T ρ).Finite)
    (x : ℕ+) {ω ω' : ℕ → ℕ+ × ℕ}
    (hω : StrictMono (fun t => (ω t).1) ∧ ∀ t, IsExtendedGameState ρ hρ (ω t))
    (hω' : StrictMono (fun t => (ω' t).1) ∧ ∀ t, IsExtendedGameState ρ hρ (ω' t))
    (hequiv : StoppedEquiv x ω ω') :
    stoppedGameJumpPair ρ hρ x ω = stoppedGameJumpPair ρ hρ x ω' := by
  suffices h : ∀ (σ σ' : ℕ → ℕ+ × ℕ),
      (StrictMono (fun t => (σ t).1) ∧ ∀ t, IsExtendedGameState ρ hρ (σ t)) →
      (StrictMono (fun t => (σ' t).1) ∧ ∀ t, IsExtendedGameState ρ hρ (σ' t)) →
      StoppedEquiv x σ σ' →
      stoppedGameJumpPair ρ hρ x σ ⊆ stoppedGameJumpPair ρ hρ x σ' by
    refine le_antisymm (h ω ω' hω hω' hequiv) (h ω' ω hω' hω ?_)
    intro t ht
    exact (hequiv t ht.symm).symm
  intro σ σ' hσ hσ' heq
  rintro pt ⟨hmem, hbound⟩
  have hmem' := hmem
  rw [extendedGameJumpPair, if_pos hσ] at hmem'
  obtain ⟨t, ht, rfl⟩ := hmem'
  have hpos : (σ t).1 ≤ x := by
    have hiter : (⇑ρ)^[(σ t).2] (extendedGameLevel ρ hρ (σ t)) = (σ t).1 :=
      extendedGameLevel_iterate ρ hρ (hσ.2 t)
    have hle : (σ t).1 ≤ (⇑ρ)^[(σ t).2 + 1] (extendedGameLevel ρ hρ (σ t)) := by
      rw [Function.iterate_succ_apply', hiter]
      exact le_of_lt (ρ.lt_apply _)
    exact le_trans hle hbound
  have hagree : ∀ s ≤ t, σ s = σ' s := by
    intro s hs
    refine heq s (Or.inl ?_)
    rcases lt_or_eq_of_le hs with hlt | rfl
    · exact le_of_lt (lt_of_lt_of_le (hσ.1 hlt) hpos)
    · exact hpos
  have hstate : σ t = σ' t := hagree t le_rfl
  have ht' : ExtendedGameRecord σ' t := by
    intro s hst
    rw [← hstate, ← hagree s (le_of_lt hst)]
    exact ht s hst
  constructor
  · rw [extendedGameJumpPair, if_pos hσ']
    exact ⟨t, ht', congrArg
      (fun s : ℕ+ × ℕ => (extendedGameLevel ρ hρ s, (⟨s.2 + 1, Nat.succ_pos _⟩ : ℕ+)))
      hstate⟩
  · exact hbound

end Atlas.Knowledge
