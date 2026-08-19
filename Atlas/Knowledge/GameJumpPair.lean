import Mathlib
import Atlas.Knowledge.IsJumpPair
import Atlas.Knowledge.ShiftDepth
import Atlas.Knowledge.ShiftT

/-!
# jump pair of a shooting game

The pair `(I_G, β_G)` the source attaches to a shooting game, at the level of a single
trajectory and with no probability: along a strictly increasing path of rabbit positions, a
**record** is a time whose shot length—the depth of the position—is strictly below every
earlier one, the moment a new shooter enters; the pair collects each record's shooter, the
root of the position, with one more than the shot length. The source's Proposition 7.1, that
this pair is a `ρ`-jump set, is here a proved theorem: roots of records are strictly ordered
with time, so levels are distinct and multiplicities strictly decrease, membership in `T_ρ`
is `Atlas.Knowledge.ShiftDepth`'s `root_mem_T`, and the iterate condition is the advance of
the rabbit. The measures making the trajectories into the source's Markov process are a later
phase's business.

## Main definitions

* `GameRecord` — the times where the shot length hits a strict record low.
* `gameJumpPair` — the set of (shooter, length + 1) points over the records: the source's
  `(I_G, β_G)`, carried as a graph.

## Main statements

* `gameJumpPair_finite` — the pair has finitely many points: records carry pairwise distinct
  depths bounded by the first.
* `isJumpPair_gameJumpPair` — on a strictly increasing trajectory the pair is a `ρ`-jump
  pair over `T_ρ`: the source's Proposition 7.1. Proved.

## Implementation notes

The trajectory is carried as its position path `ω : ℕ → ℕ+` alone; the shot lengths are the
depths of the positions, which is the state consistency of `Atlas.Knowledge.IsGameState`, so
no second component is transported. Time `0` is vacuously a record, the game opening with its
first shooter. The source's display defines the record set as times and passes silently to
the shooters when it forms the pair—its `I_G` is introduced as the set of *shooting
positions* where a new shooter came in—and the graph here does the same passage explicitly,
one point per record, at the root of the position. The pair is a `Set` with its finiteness a
theorem rather than a `Finset`, the record times being unbounded even when the records are
few; `IsJumpPair` consumes it through `Set.Finite.toFinset`.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

/-- A **record** of a trajectory: a time whose shot length—the depth of the position—is
strictly below every earlier one; the moment a new shooter enters
([Pagano 2022, §7, pp.453–455][Pagano2022]). -/
def GameRecord (ρ : Shift) (ω : ℕ → ℕ+) (t : ℕ) : Prop :=
  ∀ s < t, ρ.depth (ω t) < ρ.depth (ω s)

/-- The **jump pair of a shooting game**: one point per record, at the shooter's position—the
root of the rabbit's—with one more than the shot length; the source's `(I_G, β_G)`, carried
as a graph ([Pagano 2022, §7, pp.453–455][Pagano2022]). -/
noncomputable def gameJumpPair (ρ : Shift) (ω : ℕ → ℕ+) : Set (ℕ+ × ℕ+) :=
  {p | ∃ t, GameRecord ρ ω t ∧
    p = (ρ.root (ω t), ⟨ρ.depth (ω t) + 1, Nat.succ_pos _⟩)}

section GameLemmas

variable {ρ : Shift} {ω : ℕ → ℕ+}

/-- Later records shoot shorter: the depth at a record is below the depth at every earlier
time. -/
theorem GameRecord.depth_lt {t t' : ℕ} (ht' : GameRecord ρ ω t') (h : t < t') :
    ρ.depth (ω t') < ρ.depth (ω t) := ht' t h

/-- On a strictly increasing trajectory the root at a record lies strictly above the root at
every earlier time: shooters enter in increasing positions. -/
theorem GameRecord.root_lt (hmono : StrictMono ω) {t t' : ℕ}
    (ht' : GameRecord ρ ω t') (h : t < t') :
    ρ.root (ω t) < ρ.root (ω t') := by
  have hd : ρ.depth (ω t') < ρ.depth (ω t) := ht'.depth_lt h
  have hlt : (⇑ρ)^[ρ.depth (ω t')] (ρ.root (ω t)) <
      (⇑ρ)^[ρ.depth (ω t')] (ρ.root (ω t')) := by
    rw [ρ.iterate_root (ω t')]
    calc (⇑ρ)^[ρ.depth (ω t')] (ρ.root (ω t))
        ≤ (⇑ρ)^[ρ.depth (ω t)] (ρ.root (ω t)) :=
          ρ.iterate_le_iterate_right _ (le_of_lt hd)
      _ = ω t := ρ.iterate_root (ω t)
      _ < ω t' := hmono h
  exact (ρ.strict_mono.iterate (ρ.depth (ω t'))).lt_iff_lt.mp hlt

/-- Two records with the same root are the same time. -/
theorem GameRecord.eq_of_root_eq (hmono : StrictMono ω) {t t' : ℕ}
    (ht : GameRecord ρ ω t) (ht' : GameRecord ρ ω t')
    (h : ρ.root (ω t) = ρ.root (ω t')) : t = t' := by
  rcases lt_trichotomy t t' with hlt | heq | hgt
  · exact absurd h (ne_of_lt (ht'.root_lt hmono hlt))
  · exact heq
  · exact absurd h.symm (ne_of_lt (ht.root_lt hmono hgt))

end GameLemmas

/-- The pair of a game is finite: records carry pairwise distinct depths, all bounded by the
depth at time `0` ([Pagano 2022, §7, p.454][Pagano2022]). -/
theorem gameJumpPair_finite (ρ : Shift) (ω : ℕ → ℕ+) : (gameJumpPair ρ ω).Finite := by
  apply Set.Finite.of_finite_image (f := Prod.snd)
  · apply Set.Finite.subset (Set.finite_Iic (⟨ρ.depth (ω 0) + 1, Nat.succ_pos _⟩ : ℕ+))
    rintro n ⟨p, ⟨t, ht, rfl⟩, rfl⟩
    simp only [Set.mem_Iic]
    refine Subtype.mk_le_mk.mpr ?_
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · exact le_refl _
    · have := ht 0 htpos
      omega
  · rintro p ⟨t, ht, rfl⟩ q ⟨t', ht', rfl⟩ hsnd
    have hdep : ρ.depth (ω t) = ρ.depth (ω t') := by
      have := congrArg (fun n : ℕ+ => (n : ℕ)) hsnd
      simpa using this
    have : t = t' := by
      rcases lt_trichotomy t t' with hlt | heq | hgt
      · exact absurd hdep (ne_of_gt (ht'.depth_lt hlt))
      · exact heq
      · exact absurd hdep (ne_of_lt (ht.depth_lt hgt))
    subst this
    rfl

/-- On a strictly increasing trajectory the pair of a game is a `ρ`-jump pair over `T_ρ`: the
source's Proposition 7.1, at the level of one trajectory. Roots order with time, so levels
are distinct and multiplicities strictly decrease; the levels are roots, hence in `T_ρ`; and
the iterate at a point is one shift past the rabbit, which advances
([Pagano 2022, Prop. 7.1, p.454][Pagano2022]). -/
theorem isJumpPair_gameJumpPair (ρ : Shift) {ω : ℕ → ℕ+} (hmono : StrictMono ω) :
    IsJumpPair ρ (Shift.T ρ) (gameJumpPair_finite ρ ω).toFinset := by
  have hmem : ∀ p ∈ (gameJumpPair_finite ρ ω).toFinset, ∃ t, GameRecord ρ ω t ∧
      p = (ρ.root (ω t), ⟨ρ.depth (ω t) + 1, Nat.succ_pos _⟩) := by
    intro p hp
    exact ((gameJumpPair_finite ρ ω).mem_toFinset).mp hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp q hq hfst
    obtain ⟨t, ht, rfl⟩ := hmem p hp
    obtain ⟨t', ht', rfl⟩ := hmem q hq
    have := ht.eq_of_root_eq hmono ht' hfst
    subst this
    rfl
  · intro p hp
    obtain ⟨t, ht, rfl⟩ := hmem p hp
    exact ρ.root_mem_T _
  · intro p hp q hq hlt
    obtain ⟨t, ht, rfl⟩ := hmem p hp
    obtain ⟨t', ht', rfl⟩ := hmem q hq
    have htt : t < t' := by
      rcases lt_trichotomy t t' with h | h | h
      · exact h
      · subst h; exact absurd hlt (lt_irrefl _)
      · exact absurd (ht.root_lt hmono h) (not_lt_of_gt hlt)
    have hd := ht'.depth_lt htt
    exact Subtype.mk_lt_mk.mpr (by omega)
  · intro p hp q hq hlt
    obtain ⟨t, ht, rfl⟩ := hmem p hp
    obtain ⟨t', ht', rfl⟩ := hmem q hq
    have htt : t < t' := by
      rcases lt_trichotomy t t' with h | h | h
      · exact h
      · subst h; exact absurd hlt (lt_irrefl _)
      · exact absurd (ht.root_lt hmono h) (not_lt_of_gt hlt)
    have h1 : (⇑ρ)^[(ρ.depth (ω t) + 1)] (ρ.root (ω t)) = ρ (ω t) := by
      rw [Function.iterate_succ_apply', ρ.iterate_root]
    have h2 : (⇑ρ)^[(ρ.depth (ω t') + 1)] (ρ.root (ω t')) = ρ (ω t') := by
      rw [Function.iterate_succ_apply', ρ.iterate_root]
    change (⇑ρ)^[(ρ.depth (ω t) + 1)] (ρ.root (ω t)) <
      (⇑ρ)^[(ρ.depth (ω t') + 1)] (ρ.root (ω t'))
    rw [h1, h2]
    exact ρ.strict_mono (hmono htt)

end Atlas.Knowledge
