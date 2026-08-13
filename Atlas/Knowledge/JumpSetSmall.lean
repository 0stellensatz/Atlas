import Mathlib
import Atlas.Knowledge.JumpSetEquiv
import Atlas.Knowledge.ShiftRhoEP

/-!
# small jump sets

The jump sets with at most two indices, spelled out through the parametrization
`Atlas.Knowledge.JumpSetEquiv`: the empty set is the one jump set with empty pair; a single point
`(a, m)` is a jump pair for any admissible `a`, its jump set the orbit segment of length `m` at
`a`; two points `(a, m₁)`, `(b, m₂)` with `a < b` are a jump pair exactly when `m₂ < m₁` and
`ρ^[m₁] a < ρ^[m₂] b`. The closing `example`s run the constructions on the shift
`Atlas.Knowledge.ShiftRhoEP` by `decide`, which keeps them executable test cases rather than
proofs about descriptions.

## Main statements

* `jumpPairOf_eq_empty_iff` — the empty jump set is the one with empty pair.
* `isJumpPair_singleton`, `jumpSetOf_singleton` — the one-index jump sets.
* `isJumpPair_pair` — the two-index condition.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

variable {ρ : Shift} {S : Set ℕ+} {A : Finset ℕ+}

/-- The empty set is the unique jump set whose pair is empty: `|I| = 0`
([Pagano 2022, Example 2.4, p.417][Pagano2022]). -/
theorem jumpPairOf_eq_empty_iff (h : IsJumpSet ρ S A) : jumpPairOf ρ A = ∅ ↔ A = ∅ := by
  constructor
  · intro hP
    by_contra hne
    rw [← ne_eq, ← Finset.nonempty_iff_ne_empty] at hne
    have hi := Finset.mem_sdiff.mp (ρ.min'_mem_sdiff_image hne)
    have hmem : (A.min' hne, (⟨jumpMultiplicity A (A.min' hne), jumpMultiplicity_pos hi.1⟩ : ℕ+))
        ∈ jumpPairOf ρ A := mem_jumpPairOf.mpr ⟨hi.1, hi.2, rfl⟩
    rw [hP] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  · rintro rfl
    ext q
    rw [mem_jumpPairOf]
    simp

/-- A single point `(a, m)` is a jump pair exactly when `a` is admissible: `|I| = 1`
([Pagano 2022, Example 2.4, p.417][Pagano2022]). -/
theorem isJumpPair_singleton (ρ : Shift) (S : Set ℕ+) (a : ℕ+) (m : ℕ+) :
    IsJumpPair ρ S {(a, m)} ↔ a ∈ S := by
  constructor
  · intro h
    exact h.fst_mem (Finset.mem_singleton_self _)
  · intro ha
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p hp q hq h1
      rw [Finset.mem_singleton] at hp hq
      rw [hp, hq]
    · intro p hp
      rw [Finset.mem_singleton] at hp
      rw [hp]
      exact ha
    · intro p hp q hq hlt
      rw [Finset.mem_singleton] at hp hq
      rw [hp, hq] at hlt
      exact absurd hlt (lt_irrefl _)
    · intro p hp q hq hlt
      rw [Finset.mem_singleton] at hp hq
      rw [hp, hq] at hlt
      exact absurd hlt (lt_irrefl _)

/-- The jump set of a single point `(a, m)` is the orbit segment of length `m` based at `a`
([Pagano 2022, Example 2.4, p.417][Pagano2022]). -/
theorem jumpSetOf_singleton (ρ : Shift) (a : ℕ+) (m : ℕ+) :
    jumpSetOf ρ {(a, m)} = (Finset.range (m : ℕ)).image fun t => (⇑ρ)^[t] a := by
  have htail : jumpSetOf.tail {(a, m)} a = 0 := by
    apply jumpSetOf.tail_eq_zero
    intro r hr
    rw [Finset.mem_singleton] at hr
    subst hr
    exact lt_irrefl a
  ext x
  rw [mem_jumpSetOf]
  constructor
  · rintro ⟨q, hq, n, hn, rfl⟩
    rw [Finset.mem_singleton] at hq
    subst hq
    refine Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr ?_, rfl⟩
    have hn' : n < (m : ℕ) - jumpSetOf.tail {(a, m)} a := hn
    rw [htail, Nat.sub_zero] at hn'
    exact hn'
  · intro hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_range] at hn
    refine ⟨(a, m), Finset.mem_singleton_self _, n, ?_, rfl⟩
    change n < (m : ℕ) - jumpSetOf.tail {(a, m)} a
    rw [htail, Nat.sub_zero]
    exact hn

/-- Two points `(a, m₁)` and `(b, m₂)` with `a < b` are a jump pair exactly when both indices
are admissible, `m₂ < m₁`, and `ρ^[m₁] a < ρ^[m₂] b`—the source states the last condition as
`ρ^[m₁ - m₂] a < b`, its reflection through `ρ^[m₂]`: `|I| = 2`
([Pagano 2022, Example 2.4, p.417][Pagano2022]). -/
theorem isJumpPair_pair (ρ : Shift) (S : Set ℕ+) {a b : ℕ+} (hab : a < b) (m₁ m₂ : ℕ+) :
    IsJumpPair ρ S {(a, m₁), (b, m₂)}
      ↔ a ∈ S ∧ b ∈ S ∧ m₂ < m₁ ∧ (⇑ρ)^[(m₁ : ℕ)] a < (⇑ρ)^[(m₂ : ℕ)] b := by
  have hmem : ∀ p ∈ ({(a, m₁), (b, m₂)} : Finset (ℕ+ × ℕ+)), p = (a, m₁) ∨ p = (b, m₂) := by
    intro p hp
    rw [Finset.mem_insert, Finset.mem_singleton] at hp
    exact hp
  constructor
  · intro h
    have hpa : ((a, m₁) : ℕ+ × ℕ+) ∈ ({(a, m₁), (b, m₂)} : Finset (ℕ+ × ℕ+)) := by simp
    have hpb : ((b, m₂) : ℕ+ × ℕ+) ∈ ({(a, m₁), (b, m₂)} : Finset (ℕ+ × ℕ+)) := by simp
    exact ⟨h.fst_mem hpa, h.fst_mem hpb, h.snd_lt_snd hpa hpb hab,
      h.iterate_lt_iterate hpa hpb hab⟩
  · rintro ⟨ha, hb, hm, hit⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p hp q hq h1
      rcases hmem p hp with rfl | rfl <;> rcases hmem q hq with rfl | rfl
      · rfl
      · exact absurd h1 (ne_of_lt hab)
      · exact absurd h1 (ne_of_gt hab)
      · rfl
    · intro p hp
      rcases hmem p hp with rfl | rfl
      · exact ha
      · exact hb
    · intro p hp q hq hlt
      rcases hmem p hp with rfl | rfl <;> rcases hmem q hq with rfl | rfl
      · exact absurd hlt (lt_irrefl _)
      · exact hm
      · exact absurd hlt (not_lt.mpr (le_of_lt hab))
      · exact absurd hlt (lt_irrefl _)
    · intro p hp q hq hlt
      rcases hmem p hp with rfl | rfl <;> rcases hmem q hq with rfl | rfl
      · exact absurd hlt (lt_irrefl _)
      · exact hit
      · exact absurd hlt (not_lt.mpr (le_of_lt hab))
      · exact absurd hlt (lt_irrefl _)

/- Executable test cases on `ρ_ep 3 2`, where `ρ` sends `i` to `min (2 * i) (i + 3)`: the orbit
segment of `(1, 2)` and a two-index reconstruction, in both directions. -/

example : jumpSetOf (ρ_ep 3 2 (by decide)) {((1 : ℕ+), (2 : ℕ+))} = {1, 2} := by decide

example : jumpSetOf (ρ_ep 3 2 (by decide)) {((1 : ℕ+), (2 : ℕ+)), ((3 : ℕ+), (1 : ℕ+))}
    = {1, 3} := by decide

example : jumpPairOf (ρ_ep 3 2 (by decide)) {1, 3}
    = {((1 : ℕ+), (2 : ℕ+)), ((3 : ℕ+), (1 : ℕ+))} := by decide

end Atlas.Knowledge
