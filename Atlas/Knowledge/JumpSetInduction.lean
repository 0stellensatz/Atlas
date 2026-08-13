import Mathlib
import Atlas.Knowledge.IsJumpSet
import Atlas.Knowledge.JumpMultiplicity

/-!
# jump set induction

The source's inductive construction of jump sets, as an induction principle: every jump set is
reached from `∅` by repeatedly appending a `ρ`-orbit segment based at a fresh index strictly
beyond `ρ` of everything already present. One direction is the construction step
(`IsJumpSet.append_string`): the appended set is again a jump set. The other is the
decomposition: the orbit-segment lemma `IsJumpSet.filter_eq_image_iterate`, run with no upper
bound, identifies everything at or above the greatest index of a jump set as one segment, and
what sits below it is a jump set of smaller size (`IsJumpSet.filter_lt`), so strong induction on
the size carries any property from `∅` through the construction steps to every jump set.

## Main statements

* `IsJumpSet.append_string` — appending an orbit segment strictly beyond the set preserves being
  a jump set.
* `IsJumpSet.induction_on` — the induction principle.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

namespace IsJumpSet

variable {ρ : Shift} {S : Set ℕ+} {A : Finset ℕ+}

/-- Appending to a jump set the `ρ`-orbit segment of length `n` based at an admissible index `i`
strictly beyond `ρ` of every member yields a jump set: the source's construction step
([Pagano 2022, Example 2.5, p.417][Pagano2022]). -/
theorem append_string (h : IsJumpSet ρ S A) {i : ℕ+} (hiS : i ∈ S) (n : ℕ+)
    (hbeyond : ∀ x ∈ A, ρ x < i) :
    IsJumpSet ρ S (A ∪ (Finset.range (n : ℕ)).image fun t => (⇑ρ)^[t] i) := by
  have hA_lt : ∀ x ∈ A, x < i := fun x hx => lt_trans (ρ.lt_apply x) (hbeyond x hx)
  constructor
  · intro a ha b hb hab
    rw [Finset.mem_union] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact h.chain ha hb hab
    · obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hb
      exact le_trans (le_of_lt (hbeyond a ha)) (ρ.le_iterate i t)
    · exfalso
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp ha
      exact absurd hab
        (not_lt.mpr (le_of_lt (lt_of_lt_of_le (hA_lt b hb) (ρ.le_iterate i t))))
    · obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hb
      have htu : t < u := (ρ.iterate_strictMono_right i).lt_iff_lt.mp hab
      rw [← Function.iterate_succ_apply' (⇑ρ) t i]
      exact ρ.iterate_le_iterate_right i htu
  · intro a ha ha'
    rw [Finset.mem_union] at ha
    rcases ha with ha | ha
    · apply h.mem_of_not_mem_image ha
      intro hmem
      exact ha' (Finset.image_subset_image Finset.subset_union_left hmem)
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
      cases t with
      | zero => exact hiS
      | succ t =>
        exfalso
        apply ha'
        rw [Function.iterate_succ_apply' (⇑ρ) t i]
        refine Finset.mem_image.mpr ⟨(⇑ρ)^[t] i, Finset.mem_union_right _ ?_, rfl⟩
        rw [Finset.mem_range] at ht
        exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), rfl⟩

/-- The source's construction reaches every jump set: a property of finite sets holding for `∅`
and propagated by `IsJumpSet.append_string` steps holds for every jump set
([Pagano 2022, Example 2.5, p.417][Pagano2022]). -/
theorem induction_on {motive : Finset ℕ+ → Prop} (h : IsJumpSet ρ S A)
    (empty : motive ∅)
    (append : ∀ A' : Finset ℕ+, ∀ i : ℕ+, ∀ n : ℕ+, IsJumpSet ρ S A' → motive A' → i ∈ S →
      (∀ x ∈ A', ρ x < i) →
      motive (A' ∪ (Finset.range (n : ℕ)).image fun t => (⇑ρ)^[t] i)) :
    motive A := by
  suffices H : ∀ N : ℕ, ∀ A : Finset ℕ+, A.card ≤ N → IsJumpSet ρ S A → motive A from
    H A.card A (le_refl _) h
  intro N
  induction N with
  | zero =>
    intro A hcard hjs
    rw [Nat.le_zero, Finset.card_eq_zero] at hcard
    rw [hcard]
    exact empty
  | succ N ih =>
    intro A hcard hjs
    rcases A.eq_empty_or_nonempty with rfl | hne
    · exact empty
    have hBne : (A \ A.image ⇑ρ).Nonempty := ⟨_, ρ.min'_mem_sdiff_image hne⟩
    have himem := Finset.max'_mem _ hBne
    rw [Finset.mem_sdiff] at himem
    obtain ⟨hiA, hiIm⟩ := himem
    set i := (A \ A.image ⇑ρ).max' hBne with hidef
    have hu : ∀ y ∈ A, i < y → (y : WithTop ℕ+) < (⊤ : WithTop ℕ+) → y ∈ A.image ⇑ρ := by
      intro y hy hiy _
      by_contra hyim
      have hymem : y ∈ A \ A.image ⇑ρ := Finset.mem_sdiff.mpr ⟨hy, hyim⟩
      exact absurd hiy (not_lt.mpr (Finset.le_max' _ _ hymem))
    have hOS := hjs.filter_eq_image_iterate hiA hu
    have hfe : A.filter (fun x => i ≤ x ∧ (x : WithTop ℕ+) < (⊤ : WithTop ℕ+))
        = A.filter fun x => i ≤ x := by
      apply Finset.filter_congr
      intro x _
      simp
    rw [hfe] at hOS
    have hApart : A = (A.filter fun x => x < i) ∪ A.filter fun x => i ≤ x := by
      ext x
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hx
        rcases lt_or_ge x i with h' | h'
        · exact Or.inl ⟨hx, h'⟩
        · exact Or.inr ⟨hx, h'⟩
      · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
    have hbelow : IsJumpSet ρ S (A.filter fun x => x < i) := hjs.filter_lt i
    have hcard' : (A.filter fun x => x < i).card < A.card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
      exact ⟨i, hiA, by simp⟩
    have hmb := ih (A.filter fun x => x < i) (by omega) hbelow
    have hbeyond : ∀ x ∈ A.filter (fun x => x < i), ρ x < i := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rcases eq_or_lt_of_le (hjs.chain hx.1 hiA hx.2) with h2 | h2
      · exact absurd (Finset.mem_image.mpr ⟨x, hx.1, h2⟩) hiIm
      · exact h2
    have happ := append (A.filter fun x => x < i) i
      ⟨jumpMultiplicity A i, jumpMultiplicity_pos hiA⟩ hbelow hmb
      (hjs.mem_of_not_mem_image hiA hiIm) hbeyond
    rw [hApart, hOS]
    exact happ

end IsJumpSet

end Atlas.Knowledge
