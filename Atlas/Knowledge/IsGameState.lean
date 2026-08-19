import Mathlib
import Atlas.Knowledge.ShiftDepth
import Atlas.Knowledge.ShiftEStar

/-!
# state of a shooting game

The state spaces of the source's shooting games: a state pairs the rabbit's position with the
length of the next shot, and the pairing is consistent when the length is the depth
`Atlas.Knowledge.ShiftDepth` of the position. The extended game admits a second kind of state,
whose position is an iterate of `e_ρ^*`—the extra shooter of the extended world. The
trajectory-level combinatorics over these states is `Atlas.Knowledge.GameJumpPair`; the
transition function and the path measures of the source's Markov reading are the business of a
later phase and no probability enters here.

## Main definitions

* `IsGameState` — the plain state space: the shot length is the depth of the position.
* `IsExtendedGameState` — the extended state space: of the first kind as before, or of the
  second kind, an iterate of `e_ρ^*`.

## Main statements

* `extendedGameState_kinds_exclusive` — no state is of both kinds. Proved.

## Implementation notes

States are carried as pairs in `ℕ+ × ℕ`, the source's `ℤ_{≥1} × ℤ_{≥0}`, and the spaces are
predicates rather than subtypes: the game definitions quantify over paths of positions and
consult consistency where they need it, so no carrier type is formed. The two kinds of the
extended space are the two disjuncts, in the source's order, and they are *exclusive*: a
position of the second kind pulls back the recorded length onto `e_ρ^*`, so were it also of
the first kind its root would be `e_ρ^*`, which `T_ρ` never contains. That is the proved
`extendedGameState_kinds_exclusive`, which the extended transition function of the source's
§7—defined by a different formula on each kind—will stand on.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

/-- A **state** of the shooting game: the recorded shot length is the depth of the position—
the source's `S = {(x₁, x₂) : v_ρ (x₁) = x₂}` ([Pagano 2022, §7, p.455][Pagano2022]). -/
def IsGameState (ρ : Shift) (x : ℕ+ × ℕ) : Prop :=
  ρ.depth x.1 = x.2

/-- A **state** of the extended shooting game: of the first kind, the shot length being the
depth of the position, or of the second kind, the position being the `x₂`-th iterate of
`e_ρ^*`—the extra shooter of the extended world
([Pagano 2022, §7, p.455][Pagano2022]). -/
def IsExtendedGameState (ρ : Shift) (hρ : (Shift.T ρ).Finite) (x : ℕ+ × ℕ) : Prop :=
  ρ.depth x.1 = x.2 ∨ (⇑ρ)^[x.2] (Shift.e_star ρ hρ) = x.1

/-- The two kinds of extended state are exclusive: a position of both kinds would have root
`e_ρ^*`, and roots lie in `T_ρ`, which `e_ρ^*` never does. -/
theorem extendedGameState_kinds_exclusive (ρ : Shift) (hρ : (Shift.T ρ).Finite) {x : ℕ+ × ℕ}
    (h1 : ρ.depth x.1 = x.2) (h2 : (⇑ρ)^[x.2] (Shift.e_star ρ hρ) = x.1) : False := by
  have hroot : ρ.root x.1 = Shift.e_star ρ hρ := by
    have hr := ρ.iterate_root x.1
    rw [h1] at hr
    exact Function.Injective.iterate ρ.inj x.2 (hr.trans h2.symm)
  exact Shift.e_star_notMem_T ρ hρ (hroot ▸ ρ.root_mem_T x.1)

end Atlas.Knowledge
