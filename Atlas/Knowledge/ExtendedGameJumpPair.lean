import Mathlib
import Atlas.Knowledge.IsGameState
import Atlas.Knowledge.IsJumpPair
import Atlas.Knowledge.ShiftTStar

/-!
# jump pair of an extended shooting game

The pair the source's map `𝒮^* (ρ, r) → Jump^*_ρ` attaches to an extended trajectory, and its
landing, proved: along a path of extended states with strictly increasing positions, a record
is a time whose recorded shot length is strictly below every earlier one, and the pair
collects each record's shooter with one more than the length. The shooter is read off the
kind: at a first-kind state it is the root of the position, as in
`Atlas.Knowledge.GameJumpPair`; at a second-kind state it is `e_ρ^*` itself, the extra
shooter—well defined because the kinds are exclusive, the proved
`Atlas.Knowledge.extendedGameState_kinds_exclusive`. The pair is therefore an extended jump
pair, the levels landing in `T^*_ρ`, which is the extended mirror of the source's
Proposition 7.1 and what makes the pushforward measure of
`Atlas.Knowledge.ExtendedGameMeasure` live on extended jump sets.

## Main definitions

* `ExtendedGameRecord` — the record times of a state path.
* `extendedGameLevel` — the shooter of a state: the root at the first kind, `e_ρ^*` at the
  second.
* `extendedGameJumpPair` — the pair of a trajectory, empty off the valid strictly increasing
  locus.

## Main statements

* `extendedGameLevel_iterate` — the shooter reaches the position in as many steps as the
  recorded length. Proved.
* `extendedGameJumpPair_finite` — the pair is finite. Proved.
* `isJumpPair_extendedGameJumpPair` — the pair is an extended jump pair, unconditionally.
  Proved.

## Implementation notes

Unlike the plain game, the shot length of an extended state is genuine data—at a position
that is both deep and an iterate of `e_ρ^*` the two kinds record different lengths—so the
trajectory is carried as a path of pairs, and validity of every state joins the strict
increase of positions in the guard under which the pair is nonempty; off the guard the pair
is `∅`, as the source prescribes on its measure-zero complement. The proofs are the plain
game's with the level abstracted: `extendedGameLevel_iterate` is the one lemma that consults
the kind, and everything downstream sees only that the level reaches the position in the
recorded number of steps.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

/-- A **record** of an extended trajectory: a time whose recorded shot length is strictly
below every earlier one ([Pagano 2022, §7, pp.455, 457][Pagano2022]). -/
def ExtendedGameRecord (ω : ℕ → ℕ+ × ℕ) (t : ℕ) : Prop :=
  ∀ s < t, (ω t).2 < (ω s).2

/-- The **shooter** of an extended state: the root of the position at the first kind, and
`e_ρ^*` at the second ([Pagano 2022, §7, pp.455–457][Pagano2022]). -/
noncomputable def extendedGameLevel (ρ : Shift) (hρ : (Shift.T ρ).Finite) (x : ℕ+ × ℕ) : ℕ+ :=
  if ρ.depth x.1 = x.2 then ρ.root x.1 else Shift.e_star ρ hρ

open Classical in
/-- The **jump pair of an extended shooting game**: one point per record, at the shooter with
one more than the recorded length; empty off the valid strictly increasing locus—the source's
map `𝒮^* (ρ, r) → Jump^*_ρ`, carried on graphs
([Pagano 2022, §7, p.457][Pagano2022]). -/
noncomputable def extendedGameJumpPair (ρ : Shift) (hρ : (Shift.T ρ).Finite)
    (ω : ℕ → ℕ+ × ℕ) : Set (ℕ+ × ℕ+) :=
  if StrictMono (fun t => (ω t).1) ∧ ∀ t, IsExtendedGameState ρ hρ (ω t) then
    {P | ∃ t, ExtendedGameRecord ω t ∧
      P = (extendedGameLevel ρ hρ (ω t), ⟨(ω t).2 + 1, Nat.succ_pos _⟩)}
  else ∅

/-- The shooter reaches the position in as many steps as the recorded length, whichever the
kind: the extended mirror of `Shift.iterate_root`. -/
theorem extendedGameLevel_iterate (ρ : Shift) (hρ : (Shift.T ρ).Finite) {x : ℕ+ × ℕ}
    (hx : IsExtendedGameState ρ hρ x) :
    (⇑ρ)^[x.2] (extendedGameLevel ρ hρ x) = x.1 := by
  rw [extendedGameLevel]
  rcases hx with h1 | h2
  · rw [if_pos h1, ← h1]
    exact ρ.iterate_root x.1
  · by_cases h1 : ρ.depth x.1 = x.2
    · exact absurd h2 (fun h => extendedGameState_kinds_exclusive ρ hρ h1 h)
    · rw [if_neg h1]
      exact h2

/-- The shooter of any state lies in `T^*_ρ`. -/
theorem extendedGameLevel_mem_T_star (ρ : Shift) (hρ : (Shift.T ρ).Finite) (x : ℕ+ × ℕ) :
    extendedGameLevel ρ hρ x ∈ Shift.T_star ρ hρ := by
  rw [extendedGameLevel]
  split_ifs with h
  · exact Or.inl (ρ.root_mem_T x.1)
  · exact Or.inr rfl

section Lemmas

variable {ρ : Shift} {hρ : (Shift.T ρ).Finite} {ω : ℕ → ℕ+ × ℕ}

/-- Later records record shorter shots. -/
theorem ExtendedGameRecord.snd_lt {t t' : ℕ} (ht' : ExtendedGameRecord ω t') (h : t < t') :
    (ω t').2 < (ω t).2 := ht' t h

/-- On a valid strictly increasing trajectory the shooter at a record lies strictly above the
shooter at every earlier time. -/
theorem ExtendedGameRecord.level_lt (hmono : StrictMono (fun t => (ω t).1))
    (hstate : ∀ t, IsExtendedGameState ρ hρ (ω t)) {t t' : ℕ}
    (ht' : ExtendedGameRecord ω t') (h : t < t') :
    extendedGameLevel ρ hρ (ω t) < extendedGameLevel ρ hρ (ω t') := by
  have hd : (ω t').2 < (ω t).2 := ht'.snd_lt h
  have hlt : (⇑ρ)^[(ω t').2] (extendedGameLevel ρ hρ (ω t)) <
      (⇑ρ)^[(ω t').2] (extendedGameLevel ρ hρ (ω t')) := by
    rw [extendedGameLevel_iterate ρ hρ (hstate t')]
    calc (⇑ρ)^[(ω t').2] (extendedGameLevel ρ hρ (ω t))
        ≤ (⇑ρ)^[(ω t).2] (extendedGameLevel ρ hρ (ω t)) :=
          ρ.iterate_le_iterate_right _ (le_of_lt hd)
      _ = (ω t).1 := extendedGameLevel_iterate ρ hρ (hstate t)
      _ < (ω t').1 := hmono h
  exact (ρ.strict_mono.iterate ((ω t').2)).lt_iff_lt.mp hlt

/-- Two records with the same shooter are the same time. -/
theorem ExtendedGameRecord.eq_of_level_eq (hmono : StrictMono (fun t => (ω t).1))
    (hstate : ∀ t, IsExtendedGameState ρ hρ (ω t)) {t t' : ℕ}
    (ht : ExtendedGameRecord ω t) (ht' : ExtendedGameRecord ω t')
    (h : extendedGameLevel ρ hρ (ω t) = extendedGameLevel ρ hρ (ω t')) : t = t' := by
  rcases lt_trichotomy t t' with hlt | heq | hgt
  · exact absurd h (ne_of_lt (ht'.level_lt hmono hstate hlt))
  · exact heq
  · exact absurd h.symm (ne_of_lt (ht.level_lt hmono hstate hgt))

end Lemmas

/-- The pair of an extended game is finite: records carry pairwise distinct lengths bounded
by the first. -/
theorem extendedGameJumpPair_finite (ρ : Shift) (hρ : (Shift.T ρ).Finite) (ω : ℕ → ℕ+ × ℕ) :
    (extendedGameJumpPair ρ hρ ω).Finite := by
  rw [extendedGameJumpPair]
  split_ifs with hcond
  swap
  · exact Set.finite_empty
  apply Set.Finite.of_finite_image (f := Prod.snd)
  · apply Set.Finite.subset (Set.finite_Iic (⟨(ω 0).2 + 1, Nat.succ_pos _⟩ : ℕ+))
    rintro n ⟨P, ⟨t, ht, rfl⟩, rfl⟩
    simp only [Set.mem_Iic]
    refine Subtype.mk_le_mk.mpr ?_
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · exact le_refl _
    · have := ht 0 htpos
      omega
  · rintro P ⟨t, ht, rfl⟩ Q ⟨t', ht', rfl⟩ hsnd
    have hdep : (ω t).2 = (ω t').2 := by
      have := congrArg (fun n : ℕ+ => (n : ℕ)) hsnd
      simpa using this
    have : t = t' := by
      rcases lt_trichotomy t t' with hlt | heq | hgt
      · exact absurd hdep (ne_of_gt (ht'.snd_lt hlt))
      · exact heq
      · exact absurd hdep (ne_of_lt (ht.snd_lt hgt))
    subst this
    rfl

/-- The pair of an extended game is an extended jump pair, unconditionally: the extended
mirror of the source's Proposition 7.1, with the shooter's kind supplying membership in
`T^*_ρ` ([Pagano 2022, §7, p.457][Pagano2022]; [Pagano 2022, Prop. 7.1, p.454][Pagano2022]). -/
theorem isJumpPair_extendedGameJumpPair (ρ : Shift) (hρ : (Shift.T ρ).Finite)
    (ω : ℕ → ℕ+ × ℕ) :
    IsJumpPair ρ (Shift.T_star ρ hρ) (extendedGameJumpPair_finite ρ hρ ω).toFinset := by
  by_cases hcond : StrictMono (fun t => (ω t).1) ∧ ∀ t, IsExtendedGameState ρ hρ (ω t)
  swap
  · have hempty : (extendedGameJumpPair_finite ρ hρ ω).toFinset = ∅ := by
      rw [Set.Finite.toFinset_eq_empty, extendedGameJumpPair, if_neg hcond]
    rw [hempty]
    exact IsJumpPair.empty ρ _
  obtain ⟨hmono, hstate⟩ := hcond
  have hmem : ∀ P ∈ (extendedGameJumpPair_finite ρ hρ ω).toFinset, ∃ t,
      ExtendedGameRecord ω t ∧
      P = (extendedGameLevel ρ hρ (ω t), ⟨(ω t).2 + 1, Nat.succ_pos _⟩) := by
    intro P hP
    have := ((extendedGameJumpPair_finite ρ hρ ω).mem_toFinset).mp hP
    rwa [extendedGameJumpPair, if_pos ⟨hmono, hstate⟩] at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P hP Q hQ hfst
    obtain ⟨t, ht, rfl⟩ := hmem P hP
    obtain ⟨t', ht', rfl⟩ := hmem Q hQ
    have := ht.eq_of_level_eq hmono hstate ht' hfst
    subst this
    rfl
  · intro P hP
    obtain ⟨t, ht, rfl⟩ := hmem P hP
    exact extendedGameLevel_mem_T_star ρ hρ (ω t)
  · intro P hP Q hQ hlt
    obtain ⟨t, ht, rfl⟩ := hmem P hP
    obtain ⟨t', ht', rfl⟩ := hmem Q hQ
    have htt : t < t' := by
      rcases lt_trichotomy t t' with h | h | h
      · exact h
      · subst h; exact absurd hlt (lt_irrefl _)
      · exact absurd (ht.level_lt hmono hstate h) (not_lt_of_gt hlt)
    have hd := ht'.snd_lt htt
    exact Subtype.mk_lt_mk.mpr (by omega)
  · intro P hP Q hQ hlt
    obtain ⟨t, ht, rfl⟩ := hmem P hP
    obtain ⟨t', ht', rfl⟩ := hmem Q hQ
    have htt : t < t' := by
      rcases lt_trichotomy t t' with h | h | h
      · exact h
      · subst h; exact absurd hlt (lt_irrefl _)
      · exact absurd (ht.level_lt hmono hstate h) (not_lt_of_gt hlt)
    have h1 : (⇑ρ)^[((ω t).2 + 1)] (extendedGameLevel ρ hρ (ω t)) = ρ ((ω t).1) := by
      rw [Function.iterate_succ_apply', extendedGameLevel_iterate ρ hρ (hstate t)]
    have h2 : (⇑ρ)^[((ω t').2 + 1)] (extendedGameLevel ρ hρ (ω t')) = ρ ((ω t').1) := by
      rw [Function.iterate_succ_apply', extendedGameLevel_iterate ρ hρ (hstate t')]
    change (⇑ρ)^[((ω t).2 + 1)] (extendedGameLevel ρ hρ (ω t)) <
      (⇑ρ)^[((ω t').2 + 1)] (extendedGameLevel ρ hρ (ω t'))
    rw [h1, h2]
    exact ρ.strict_mono (hmono htt)

end Atlas.Knowledge
