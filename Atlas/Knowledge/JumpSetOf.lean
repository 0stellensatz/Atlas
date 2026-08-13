import Mathlib
import Atlas.Knowledge.IsJumpSet
import Atlas.Knowledge.IsJumpPair
import Atlas.Knowledge.JumpMultiplicity

/-!
# jump set of a jump pair

The converse direction of the parametrization of jump sets: to a graph `P` of a pair `(I, β)`,
attach the set `A_{(I, β)}`—for each point `(i, β i)` of the graph, the `ρ`-orbit segment based at
`i` whose length is `β i` minus the multiplicity at the successor index, the source's
`β i - β (s i)`, with the full length `β i` at the top index. The successor's multiplicity is
recovered as `jumpSetOf.tail`, the greatest multiplicity strictly beyond `i`: on a jump pair the
multiplicities strictly decrease, so that greatest value *is* the successor's, and at the top
index the empty maximum is `0`, which makes the one formula cover both of the source's cases.

When `P` is a jump pair `Atlas.Knowledge.IsJumpPair`, the result is a jump set
`Atlas.Knowledge.IsJumpSet` (`IsJumpPair.isJumpSet_jumpSetOf` below) whose indices are exactly the
first
components of `P` and whose multiplicities are exactly the second components
(`IsJumpPair.jumpMultiplicity_jumpSetOf`)—the content of the roundtrip
`Atlas.Knowledge.JumpSetEquiv` runs on.

## Main definitions

* `jumpSetOf` — the set `A_{(I, β)}` attached to a graph.
* `jumpSetOf.tail` — the greatest multiplicity strictly beyond an index; `β (s i)` on a jump
  pair, `0` at the top.

## Main statements

* `mem_jumpSetOf` — membership, as an orbit-segment condition.
* `IsJumpPair.isJumpSet_jumpSetOf` — the set attached to a jump pair is a jump set.
* `IsJumpPair.jumpMultiplicity_jumpSetOf` — its multiplicity at a first component of `P` returns
  the second component.
* `IsJumpPair.fst_not_mem_image` — first components of `P` are the indices of the attached set.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

/-- The greatest second component strictly beyond `i` in `P`, and `0` when there is none. On a
jump pair this is the source's `β (s i)`, the multiplicity at the successor of `i` in the index
set ([Pagano 2022, Def. 2.2, p.416][Pagano2022]). -/
def jumpSetOf.tail (P : Finset (ℕ+ × ℕ+)) (i : ℕ+) : ℕ :=
  (P.filter fun q => i < q.1).sup fun q => (q.2 : ℕ)

/-- The set `A_{(I, β)}` attached to a graph `P`: for each point `(i, β i)`, the `ρ`-orbit
segment based at `i` of length `β i - β (s i)`, the successor's multiplicity read off by
`jumpSetOf.tail` ([Pagano 2022, Def. 2.2, p.416][Pagano2022]). -/
def jumpSetOf (ρ : Shift) (P : Finset (ℕ+ × ℕ+)) : Finset ℕ+ :=
  P.biUnion fun q =>
    (Finset.range ((q.2 : ℕ) - jumpSetOf.tail P q.1)).image fun n => (⇑ρ)^[n] q.1

namespace jumpSetOf

theorem le_tail {P : Finset (ℕ+ × ℕ+)} {r : ℕ+ × ℕ+} (hr : r ∈ P) {i : ℕ+} (hir : i < r.1) :
    (r.2 : ℕ) ≤ tail P i := by
  unfold tail
  have hmem : r ∈ P.filter fun q => i < q.1 := Finset.mem_filter.mpr ⟨hr, hir⟩
  exact Finset.le_sup (f := fun q => (q.2 : ℕ)) hmem

theorem tail_le {P : Finset (ℕ+ × ℕ+)} {i : ℕ+} {m : ℕ}
    (h : ∀ r ∈ P, i < r.1 → (r.2 : ℕ) ≤ m) : tail P i ≤ m :=
  Finset.sup_le fun r hr => h r (Finset.mem_filter.mp hr).1 (Finset.mem_filter.mp hr).2

theorem tail_lt {P : Finset (ℕ+ × ℕ+)} {i : ℕ+} {m : ℕ} (hm : 0 < m)
    (h : ∀ r ∈ P, i < r.1 → (r.2 : ℕ) < m) : tail P i < m :=
  (Finset.sup_lt_iff hm).mpr fun r hr => h r (Finset.mem_filter.mp hr).1
    (Finset.mem_filter.mp hr).2

theorem tail_eq_zero {P : Finset (ℕ+ × ℕ+)} {i : ℕ+} (h : ∀ r ∈ P, ¬i < r.1) :
    tail P i = 0 := by
  unfold tail
  rw [Finset.filter_false_of_mem h]
  exact Finset.sup_empty

end jumpSetOf

theorem mem_jumpSetOf {ρ : Shift} {P : Finset (ℕ+ × ℕ+)} {x : ℕ+} :
    x ∈ jumpSetOf ρ P
      ↔ ∃ q ∈ P, ∃ n < (q.2 : ℕ) - jumpSetOf.tail P q.1, (⇑ρ)^[n] q.1 = x := by
  simp only [jumpSetOf, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]

namespace IsJumpPair

variable {ρ : Shift} {S : Set ℕ+} {P : Finset (ℕ+ × ℕ+)}

/-- On a jump pair, the tail at a first component sits strictly below the second component:
multiplicities strictly decrease, so every orbit segment is nonempty. -/
theorem tail_lt_snd (hP : IsJumpPair ρ S P) {q : ℕ+ × ℕ+} (hq : q ∈ P) :
    jumpSetOf.tail P q.1 < (q.2 : ℕ) :=
  jumpSetOf.tail_lt q.2.pos fun r hr hqr => by exact_mod_cast hP.snd_lt_snd hq hr hqr

theorem fst_mem_jumpSetOf (hP : IsJumpPair ρ S P) {q : ℕ+ × ℕ+} (hq : q ∈ P) :
    q.1 ∈ jumpSetOf ρ P :=
  mem_jumpSetOf.mpr ⟨q, hq, 0, by have := hP.tail_lt_snd hq; omega, rfl⟩

/-- Orbit segments of a jump pair stay strictly below every later base: the segment based at
`p.1` never reaches the first component of a point beyond it. -/
theorem iterate_lt_fst (hP : IsJumpPair ρ S P) {p q : ℕ+ × ℕ+} (hp : p ∈ P) (hq : q ∈ P)
    (hlt : p.1 < q.1) {n : ℕ} (hn : n < (p.2 : ℕ) - jumpSetOf.tail P p.1) :
    (⇑ρ)^[n] p.1 < q.1 := by
  apply hP.iterate_sub_lt hp hq hlt
  have := jumpSetOf.le_tail hq hlt
  omega

/-- The set attached to a jump pair is a jump set
([Pagano 2022, Prop. 2.3, p.416][Pagano2022]). -/
theorem isJumpSet_jumpSetOf (hP : IsJumpPair ρ S P) : IsJumpSet ρ S (jumpSetOf ρ P) := by
  constructor
  · rintro x hx y hy hxy
    obtain ⟨q, hq, n, hn, rfl⟩ := mem_jumpSetOf.mp hx
    obtain ⟨r, hr, m, hm, rfl⟩ := mem_jumpSetOf.mp hy
    rcases lt_trichotomy q.1 r.1 with h1 | h1 | h1
    · rw [← Function.iterate_succ_apply' (⇑ρ) n q.1]
      have hle : n + 1 ≤ (q.2 : ℕ) - (r.2 : ℕ) := by
        have := jumpSetOf.le_tail hr h1
        omega
      exact le_trans (le_of_lt (hP.iterate_sub_lt hq hr h1 hle)) (ρ.le_iterate r.1 m)
    · obtain rfl : q = r := hP.eq_of_fst_eq hq hr h1
      have hnm : n < m := (ρ.iterate_strictMono_right q.1).lt_iff_lt.mp hxy
      rw [← Function.iterate_succ_apply' (⇑ρ) n q.1]
      exact ρ.iterate_le_iterate_right q.1 hnm
    · exfalso
      have hb : m < (r.2 : ℕ) - jumpSetOf.tail P r.1 := hm
      have h4 : (⇑ρ)^[m] r.1 < (⇑ρ)^[n] q.1 :=
        lt_of_lt_of_le (hP.iterate_lt_fst hr hq h1 hb) (ρ.le_iterate q.1 n)
      exact absurd hxy (not_lt.mpr (le_of_lt h4))
  · rintro x hx hx'
    obtain ⟨q, hq, n, hn, rfl⟩ := mem_jumpSetOf.mp hx
    cases n with
    | zero => exact hP.fst_mem hq
    | succ n =>
      exfalso
      apply hx'
      rw [Function.iterate_succ_apply']
      exact Finset.mem_image.mpr
        ⟨(⇑ρ)^[n] q.1, mem_jumpSetOf.mpr ⟨q, hq, n, by omega, rfl⟩, rfl⟩

/-- First components of a jump pair are not hit by `ρ` from inside the attached set: they are
exactly its indices. -/
theorem fst_not_mem_image (hP : IsJumpPair ρ S P) {q : ℕ+ × ℕ+} (hq : q ∈ P) :
    q.1 ∉ (jumpSetOf ρ P).image ⇑ρ := by
  intro hmem
  obtain ⟨x, hx, hρx⟩ := Finset.mem_image.mp hmem
  obtain ⟨r, hr, m, hm, rfl⟩ := mem_jumpSetOf.mp hx
  rw [← Function.iterate_succ_apply' (⇑ρ) m r.1] at hρx
  rcases lt_trichotomy r.1 q.1 with h1 | h1 | h1
  · have hb : m + 1 ≤ (r.2 : ℕ) - (q.2 : ℕ) := by
      have := jumpSetOf.le_tail hq h1
      omega
    have := hP.iterate_sub_lt hr hq h1 hb
    rw [hρx] at this
    exact lt_irrefl _ this
  · rw [h1] at hρx
    have h2 : q.1 < (⇑ρ)^[m + 1] q.1 := ρ.iterate_strictMono_right q.1 (Nat.succ_pos m)
    rw [hρx] at h2
    exact lt_irrefl _ h2
  · have := ρ.le_iterate r.1 (m + 1)
    rw [hρx] at this
    exact absurd h1 (not_lt.mpr this)

/-- The multiplicity of the attached set at a first component of the jump pair returns the
second component: the orbit segments at or beyond `q.1` count off `β` telescopically
([Pagano 2022, Prop. 2.3, p.416][Pagano2022]). -/
theorem jumpMultiplicity_jumpSetOf (hP : IsJumpPair ρ S P) {q : ℕ+ × ℕ+} (hq : q ∈ P) :
    jumpMultiplicity (jumpSetOf ρ P) q.1 = (q.2 : ℕ) := by
  suffices H : ∀ t : ℕ, ∀ q ∈ P, (P.filter fun r => q.1 < r.1).card = t →
      jumpMultiplicity (jumpSetOf ρ P) q.1 = (q.2 : ℕ) from H _ q hq rfl
  intro t
  induction t with
  | zero =>
    intro q hq hcard
    rw [Finset.card_eq_zero] at hcard
    have hnone : ∀ r ∈ P, ¬q.1 < r.1 := by
      intro r hr hqr
      have : r ∈ P.filter fun r' => q.1 < r'.1 := Finset.mem_filter.mpr ⟨hr, hqr⟩
      rw [hcard] at this
      exact absurd this (Finset.notMem_empty r)
    have hstr : (jumpSetOf ρ P).filter (fun x => q.1 ≤ x)
        = (Finset.range ((q.2 : ℕ) - jumpSetOf.tail P q.1)).image fun n => (⇑ρ)^[n] q.1 := by
      ext x
      rw [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hx, hqx⟩
        obtain ⟨r, hr, m, hm, rfl⟩ := mem_jumpSetOf.mp hx
        rcases lt_trichotomy r.1 q.1 with h1 | h1 | h1
        · exact absurd hqx (not_le.mpr (hP.iterate_lt_fst hr hq h1 hm))
        · obtain rfl : r = q := hP.eq_of_fst_eq hr hq h1
          exact ⟨m, Finset.mem_range.mpr hm, rfl⟩
        · exact absurd h1 (hnone r hr)
      · rintro ⟨m, hm, rfl⟩
        rw [Finset.mem_range] at hm
        exact ⟨mem_jumpSetOf.mpr ⟨q, hq, m, hm, rfl⟩, ρ.le_iterate q.1 m⟩
    have htail : jumpSetOf.tail P q.1 = 0 := jumpSetOf.tail_eq_zero hnone
    rw [jumpMultiplicity, hstr,
      Finset.card_image_of_injOn ((ρ.iterate_strictMono_right q.1).injective.injOn),
      Finset.card_range, htail, Nat.sub_zero]
  | succ t ih =>
    intro q hq hcard
    have hne : (P.filter fun r => q.1 < r.1).Nonempty := by
      rw [← Finset.card_pos, hcard]
      omega
    have hne' : ((P.filter fun r => q.1 < r.1).image fun r => r.1).Nonempty := hne.image _
    obtain ⟨s, hsfilter, hsj⟩ := Finset.mem_image.mp (Finset.min'_mem _ hne')
    rw [Finset.mem_filter] at hsfilter
    obtain ⟨hsP, hqs⟩ := hsfilter
    have hs_min : ∀ r ∈ P, q.1 < r.1 → s.1 ≤ r.1 := by
      intro r hr hqr
      rw [hsj]
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, hqr⟩, rfl⟩)
    have htail : jumpSetOf.tail P q.1 = (s.2 : ℕ) := by
      apply le_antisymm
      · apply jumpSetOf.tail_le
        intro r hr hqr
        rcases eq_or_lt_of_le (hs_min r hr hqr) with heq | hlt
        · obtain rfl : s = r := hP.eq_of_fst_eq hsP hr heq
          exact le_refl _
        · exact le_of_lt (by exact_mod_cast hP.snd_lt_snd hsP hr hlt)
      · exact jumpSetOf.le_tail hsP hqs
    have hcard' : (P.filter fun r => s.1 < r.1).card = t := by
      have hsplit : P.filter (fun r => q.1 < r.1) = insert s (P.filter fun r => s.1 < r.1) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hrP, hqr⟩
          rcases eq_or_lt_of_le (hs_min r hrP hqr) with heq | hlt
          · exact Or.inl (hP.eq_of_fst_eq hrP hsP heq.symm)
          · exact Or.inr ⟨hrP, hlt⟩
        · rintro (rfl | ⟨hrP, hsr⟩)
          · exact ⟨hsP, hqs⟩
          · exact ⟨hrP, lt_trans hqs hsr⟩
      have hsnot : s ∉ P.filter fun r => s.1 < r.1 := by
        rw [Finset.mem_filter]
        rintro ⟨-, h'⟩
        exact lt_irrefl _ h'
      rw [hsplit, Finset.card_insert_of_notMem hsnot] at hcard
      omega
    have hIH := ih s hsP hcard'
    have hstr : (jumpSetOf ρ P).filter (fun x => q.1 ≤ x ∧ x < s.1)
        = (Finset.range ((q.2 : ℕ) - jumpSetOf.tail P q.1)).image fun n => (⇑ρ)^[n] q.1 := by
      ext x
      rw [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hx, hqx, hxs⟩
        obtain ⟨r, hr, m, hm, rfl⟩ := mem_jumpSetOf.mp hx
        rcases lt_trichotomy r.1 q.1 with h1 | h1 | h1
        · exact absurd hqx (not_le.mpr (hP.iterate_lt_fst hr hq h1 hm))
        · obtain rfl : r = q := hP.eq_of_fst_eq hr hq h1
          exact ⟨m, Finset.mem_range.mpr hm, rfl⟩
        · exfalso
          have : s.1 ≤ (⇑ρ)^[m] r.1 := le_trans (hs_min r hr h1) (ρ.le_iterate r.1 m)
          exact absurd hxs (not_lt.mpr this)
      · rintro ⟨m, hm, rfl⟩
        rw [Finset.mem_range] at hm
        refine ⟨mem_jumpSetOf.mpr ⟨q, hq, m, hm, rfl⟩, ρ.le_iterate q.1 m, ?_⟩
        apply hP.iterate_sub_lt hq hsP hqs
        rw [htail] at hm
        omega
    have hsplit2 : (jumpSetOf ρ P).filter (fun x => q.1 ≤ x)
        = (jumpSetOf ρ P).filter (fun x => q.1 ≤ x ∧ x < s.1)
          ∪ (jumpSetOf ρ P).filter fun x => s.1 ≤ x := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hx, hqx⟩
        rcases lt_or_ge x s.1 with h' | h'
        · exact Or.inl ⟨hx, hqx, h'⟩
        · exact Or.inr ⟨hx, h'⟩
      · rintro (⟨hx, hqx, -⟩ | ⟨hx, hsx⟩)
        · exact ⟨hx, hqx⟩
        · exact ⟨hx, le_trans (le_of_lt hqs) hsx⟩
    have hdisj : Disjoint
        ((jumpSetOf ρ P).filter fun x => q.1 ≤ x ∧ x < s.1)
        ((jumpSetOf ρ P).filter fun x => s.1 ≤ x) := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      rw [Finset.mem_filter] at h1 h2
      exact absurd h2.2 (not_le.mpr h1.2.2)
    have hsnd : (s.2 : ℕ) < (q.2 : ℕ) := by exact_mod_cast hP.snd_lt_snd hq hsP hqs
    have h2 : ((jumpSetOf ρ P).filter fun x => s.1 ≤ x).card = (s.2 : ℕ) := hIH
    rw [jumpMultiplicity, hsplit2, Finset.card_union_of_disjoint hdisj, hstr,
      Finset.card_image_of_injOn ((ρ.iterate_strictMono_right q.1).injective.injOn),
      Finset.card_range, h2, htail]
    omega

end IsJumpPair

end Atlas.Knowledge
