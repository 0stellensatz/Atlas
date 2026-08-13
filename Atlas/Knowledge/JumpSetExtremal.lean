import Mathlib
import Atlas.Knowledge.JumpOrder
import Atlas.Knowledge.JumpSetEquiv

/-!
# extremal jump sets

Prop. 2.7 of the source, the device by which jump sets arise in practice: inside any finite graph
of pairs with first components in the index set, the maximal points under the jump order
`Atlas.Knowledge.JumpOrder`—and likewise the minimal points—are the graph of a unique jump set.
The reason is that graphs of jump pairs `Atlas.Knowledge.IsJumpPair` are exactly the finite
antichains of the jump order with first components in `S` (`isJumpPair_of_antichain` below), a
set of extremal points is automatically an antichain, and the parametrization
`Atlas.Knowledge.JumpSetEquiv` turns the resulting jump pair into the unique jump set carrying
it. The source uses this repeatedly to recover an intrinsic description of an object presented
non-canonically, first for filtered orbits and later for sets of jumps of characters.

## Main definitions

* `jumpMax`, `jumpMin` — the maximal and minimal points of a finite graph under the jump order.

## Main statements

* `isJumpPair_of_antichain` — antichains of the jump order are jump pairs.
* `existsUnique_jumpPairOf_eq_jumpMax`, `existsUnique_jumpPairOf_eq_jumpMin` — each extremal set
  is `(I_A, β_A)` of a unique jump set.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

variable {S : Set ℕ+} {G : Finset (ℕ+ × ℕ+)}

/-- The maximal points of a finite graph under the jump order, the source's `Max (A, b)`
([Pagano 2022, Prop. 2.7, p.418][Pagano2022]). -/
def jumpMax (ρ : Shift) (G : Finset (ℕ+ × ℕ+)) : Finset (ℕ+ × ℕ+) :=
  G.filter fun p => ∀ q ∈ G, JumpOrder ρ p q → q = p

/-- The minimal points of a finite graph under the jump order, the source's `Min (A, b)`
([Pagano 2022, Prop. 2.7, p.418][Pagano2022]). -/
def jumpMin (ρ : Shift) (G : Finset (ℕ+ × ℕ+)) : Finset (ℕ+ × ℕ+) :=
  G.filter fun p => ∀ q ∈ G, JumpOrder ρ q p → q = p

/-- Antichains of the jump order with first components in `S` are jump pairs: pairwise
incomparability unwinds to the strict decrease of second components and the strict increase of
iterates ([Pagano 2022, Def. 2.6, p.418][Pagano2022]). -/
theorem isJumpPair_of_antichain (ρ : Shift) (hS : ∀ p ∈ G, p.1 ∈ S)
    (h : ∀ p ∈ G, ∀ q ∈ G, p ≠ q → ¬JumpOrder ρ p q) : IsJumpPair ρ S G := by
  have hanti : ∀ p ∈ G, ∀ q ∈ G, p.1 < q.1 → q.2 < p.2 := by
    intro p hp q hq hlt
    by_contra hge
    rw [not_lt] at hge
    refine h p hp q hq (fun heq => absurd (congrArg Prod.fst heq) (ne_of_lt hlt)) ?_
    exact ⟨hge, le_trans ((ρ.strict_mono.iterate ((p.2 : ℕ))).monotone (le_of_lt hlt))
      (ρ.iterate_le_iterate_right q.1 (by exact_mod_cast hge))⟩
  refine ⟨?_, hS, hanti, ?_⟩
  · intro p hp q hq h1
    by_contra hne
    rcases lt_or_gt_of_ne hne with h' | h'
    · apply h p hp q hq (fun heq => hne (congrArg Prod.snd heq))
      refine ⟨le_of_lt h', ?_⟩
      rw [← h1]
      exact ρ.iterate_le_iterate_right p.1 (by exact_mod_cast le_of_lt h')
    · apply h q hq p hp (fun heq => hne (congrArg Prod.snd heq).symm)
      refine ⟨le_of_lt h', ?_⟩
      rw [h1]
      exact ρ.iterate_le_iterate_right q.1 (by exact_mod_cast le_of_lt h')
  · intro p hp q hq hlt
    by_contra hge
    rw [not_lt] at hge
    apply h q hq p hp (fun heq => absurd (congrArg Prod.fst heq).symm (ne_of_lt hlt))
    exact ⟨le_of_lt (hanti p hp q hq hlt), hge⟩

theorem isJumpPair_jumpMax (ρ : Shift) (hS : ∀ p ∈ G, p.1 ∈ S) :
    IsJumpPair ρ S (jumpMax ρ G) := by
  apply isJumpPair_of_antichain
  · intro p hp
    exact hS p (Finset.mem_filter.mp hp).1
  · intro p hp q hq hne hord
    obtain ⟨-, hpmax⟩ := Finset.mem_filter.mp hp
    exact hne (hpmax q (Finset.mem_filter.mp hq).1 hord).symm

theorem isJumpPair_jumpMin (ρ : Shift) (hS : ∀ p ∈ G, p.1 ∈ S) :
    IsJumpPair ρ S (jumpMin ρ G) := by
  apply isJumpPair_of_antichain
  · intro p hp
    exact hS p (Finset.mem_filter.mp hp).1
  · intro p hp q hq hne hord
    obtain ⟨-, hqmin⟩ := Finset.mem_filter.mp hq
    exact hne (hqmin p (Finset.mem_filter.mp hp).1 hord)

/-- Jump pairs are antichains of the jump order: the converse of
`Atlas.Knowledge.isJumpPair_of_antichain`, and the reason a jump pair is its own set of minimal
points ([Pagano 2022, Def. 2.6, p.418][Pagano2022]). -/
theorem IsJumpPair.not_jumpOrder {ρ : Shift} (hP : IsJumpPair ρ S G) {p q : ℕ+ × ℕ+}
    (hp : p ∈ G) (hq : q ∈ G) (hne : p ≠ q) : ¬JumpOrder ρ p q := by
  rintro ⟨h1, h2⟩
  rcases lt_trichotomy p.1 q.1 with hlt | heq | hlt
  · exact absurd h1 (not_le.mpr (hP.snd_lt_snd hp hq hlt))
  · exact hne (hP.eq_of_fst_eq hp hq heq)
  · exact absurd h2 (not_le.mpr (hP.iterate_lt_iterate hq hp hlt))

/-- A jump pair is its own set of minimal points under the jump order. -/
theorem IsJumpPair.jumpMin_eq_self {ρ : Shift} (hP : IsJumpPair ρ S G) : jumpMin ρ G = G := by
  refine Finset.filter_true_of_mem fun p hp q hq hqp => ?_
  by_contra hne
  exact hP.not_jumpOrder hq hp hne hqp

/-- A jump pair is its own set of maximal points under the jump order. -/
theorem IsJumpPair.jumpMax_eq_self {ρ : Shift} (hP : IsJumpPair ρ S G) : jumpMax ρ G = G := by
  refine Finset.filter_true_of_mem fun p hp q hq hpq => ?_
  by_contra hne
  exact hP.not_jumpOrder hp hq (fun h => hne h.symm) hpq

/-- The maximal points of any finite graph with first components in `S` are the pair
`(I_A, β_A)` of a unique jump set ([Pagano 2022, Prop. 2.7, p.418][Pagano2022]). -/
theorem existsUnique_jumpPairOf_eq_jumpMax (ρ : Shift) (hS : ∀ p ∈ G, p.1 ∈ S) :
    ∃! A : Finset ℕ+, IsJumpSet ρ S A ∧ jumpPairOf ρ A = jumpMax ρ G := by
  refine ⟨jumpSetOf ρ (jumpMax ρ G),
    ⟨(isJumpPair_jumpMax ρ hS).isJumpSet_jumpSetOf,
      jumpPairOf_jumpSetOf (isJumpPair_jumpMax ρ hS)⟩, ?_⟩
  rintro A ⟨hA, hA2⟩
  rw [← hA2, jumpSetOf_jumpPairOf hA]

/-- The minimal points of any finite graph with first components in `S` are the pair
`(I_A, β_A)` of a unique jump set ([Pagano 2022, Prop. 2.7, p.418][Pagano2022]). -/
theorem existsUnique_jumpPairOf_eq_jumpMin (ρ : Shift) (hS : ∀ p ∈ G, p.1 ∈ S) :
    ∃! A : Finset ℕ+, IsJumpSet ρ S A ∧ jumpPairOf ρ A = jumpMin ρ G := by
  refine ⟨jumpSetOf ρ (jumpMin ρ G),
    ⟨(isJumpPair_jumpMin ρ hS).isJumpSet_jumpSetOf,
      jumpPairOf_jumpSetOf (isJumpPair_jumpMin ρ hS)⟩, ?_⟩
  rintro A ⟨hA, hA2⟩
  rw [← hA2, jumpSetOf_jumpPairOf hA]

end Atlas.Knowledge
