import Mathlib
import Atlas.Knowledge.Shift
import Atlas.Knowledge.JumpMultiplicity

/-!
# jump set

A **jump set** for a shift `ρ`, relative to a set `S` of admissible indices: a finite set `A` of
positive integers in which any two members `a < b` satisfy `ρ a ≤ b`, and whose members not of the
form `ρ a` for a member `a` lie in `S`. The source states the notion twice over, as *jump sets*
with `S = T ρ` and as *extended jump sets* with `S = T_star ρ hρ`
(`Atlas.Knowledge.ShiftTStar`)—the choice of `S` is the entire difference, so the predicate here
carries `S` as a parameter and everything about jump sets is stated and proved once for both.

The two conditions force a jump set to be a disjoint union of `ρ`-orbit segments, one based at
each member of `A \ ρ '' A`; that structure is what the three walking lemmas below extract, and it
is what makes the parametrization `Atlas.Knowledge.JumpSetEquiv` by the pairs
`Atlas.Knowledge.IsJumpPair` work.

## Main definitions

* `IsJumpSet` — the predicate; `IsJumpSet ρ (T ρ)` is the source's jump set for `ρ`, and
  `IsJumpSet ρ (ρ.T_star hρ)` its extended jump set.

## Main statements

* `IsJumpSet.iterate_jumpMultiplicity_le` — walking a jump set from a member `a` up to a member
  `b` applies `ρ` at most once per member passed, so `ρ` iterated `jumpMultiplicity`-many times
  minus the count at `b` stays at or below `b`.
* `IsJumpSet.iterate_jumpMultiplicity_lt` — strictly below, when `b` is not hit by `ρ` from
  inside `A`.
* `IsJumpSet.filter_eq_image_iterate` — from a member `i` up to any bound below which every
  higher member is hit by `ρ` from inside `A`, a jump set is a single `ρ`-orbit segment based at
  `i`; the bound lives in `WithTop ℕ+` so that `⊤` says "no bound".

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

/-- A **jump set** for the shift `ρ` relative to the index set `S`: a finite `A` in which `a < b`
forces `ρ a ≤ b`, and whose members not hit by `ρ` from inside `A` lie in `S`. The source's jump
sets are `S = T ρ`, its extended jump sets `S = T_star ρ hρ`
([Pagano 2022, Def. 2.2, p.416][Pagano2022]). -/
def IsJumpSet (ρ : Shift) (S : Set ℕ+) (A : Finset ℕ+) : Prop :=
  (∀ a ∈ A, ∀ b ∈ A, a < b → ρ a ≤ b) ∧ ∀ a ∈ A, a ∉ A.image ⇑ρ → a ∈ S

/-- In a nonempty finite set of positive integers, the least element is not hit by `ρ`: shifts
move strictly up. Nothing about jump sets is needed. -/
theorem sdiff_image_nonempty (ρ : Shift) {A : Finset ℕ+} (hA : A.Nonempty) :
    (A \ A.image ⇑ρ).Nonempty := by
  refine ⟨A.min' hA, Finset.mem_sdiff.mpr ⟨A.min'_mem hA, ?_⟩⟩
  intro hmem
  obtain ⟨a, ha, hρa⟩ := Finset.mem_image.mp hmem
  exact absurd (A.min'_le a ha) (not_le.mpr (hρa ▸ ρ.lt_apply a))

namespace IsJumpSet

variable {ρ : Shift} {S : Set ℕ+} {A : Finset ℕ+}

theorem empty (ρ : Shift) (S : Set ℕ+) : IsJumpSet ρ S ∅ := by simp [IsJumpSet]

theorem chain (h : IsJumpSet ρ S A) {a b : ℕ+} (ha : a ∈ A) (hb : b ∈ A) (hab : a < b) :
    ρ a ≤ b :=
  h.1 a ha b hb hab

theorem mem_of_not_mem_image (h : IsJumpSet ρ S A) {a : ℕ+} (ha : a ∈ A)
    (ha' : a ∉ A.image ⇑ρ) : a ∈ S :=
  h.2 a ha ha'

/-- Restricting a jump set below any cutoff leaves a jump set: the chain condition restricts, and
a member hit by `ρ` from inside `A` is hit from strictly below itself, hence from inside the
restriction. -/
theorem filter_lt (h : IsJumpSet ρ S A) (c : ℕ+) : IsJumpSet ρ S (A.filter fun x => x < c) := by
  constructor
  · intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    exact h.chain ha.1 hb.1 hab
  · intro a ha ha'
    rw [Finset.mem_filter] at ha
    apply h.mem_of_not_mem_image ha.1
    intro hmem
    obtain ⟨b, hb, hρb⟩ := Finset.mem_image.mp hmem
    apply ha'
    refine Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, ?_⟩, hρb⟩
    exact lt_trans (hρb ▸ ρ.lt_apply b) ha.2

private theorem iterate_le_aux (h : IsJumpSet ρ S A) :
    ∀ k : ℕ, ∀ a ∈ A, ∀ b ∈ A, a ≤ b → jumpMultiplicity A a - jumpMultiplicity A b = k →
      (⇑ρ)^[k] a ≤ b := by
  intro k
  induction k with
  | zero => exact fun a _ b _ hab _ => hab
  | succ k ih =>
    intro a ha b hb hab hk
    have hne : a ≠ b := by
      rintro rfl
      simp at hk
    have hab' : a < b := lt_of_le_of_ne hab hne
    have hbmem : b ∈ A.filter fun x => a < x := Finset.mem_filter.mpr ⟨hb, hab'⟩
    have hFne : (A.filter fun x => a < x).Nonempty := ⟨b, hbmem⟩
    set c := (A.filter fun x => a < x).min' hFne with hc
    have hcmem := Finset.min'_mem _ hFne
    rw [Finset.mem_filter] at hcmem
    obtain ⟨hcA, hac⟩ := hcmem
    have hcb : c ≤ b := Finset.min'_le _ b hbmem
    have hcount : jumpMultiplicity A a = jumpMultiplicity A c + 1 := by
      have h1 : (A.filter fun x => c ≤ x) = A.filter fun x => a < x := by
        ext x
        simp only [Finset.mem_filter, and_congr_right_iff]
        intro hx
        constructor
        · exact fun hcx => lt_of_lt_of_le hac hcx
        · exact fun hax => Finset.min'_le _ x (Finset.mem_filter.mpr ⟨hx, hax⟩)
      have h2 : (A.filter fun x => a ≤ x) = insert a (A.filter fun x => a < x) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hx, hax⟩
          rcases eq_or_lt_of_le hax with rfl | h'
          · exact Or.inl rfl
          · exact Or.inr ⟨hx, h'⟩
        · rintro (rfl | ⟨hx, hax⟩)
          · exact ⟨ha, le_refl _⟩
          · exact ⟨hx, le_of_lt hax⟩
      have h3 : a ∉ A.filter fun x => a < x := by simp
      rw [jumpMultiplicity, jumpMultiplicity, h1, h2, Finset.card_insert_of_notMem h3]
    have hmono : jumpMultiplicity A b ≤ jumpMultiplicity A c := jumpMultiplicity_antitone A hcb
    have := ih c hcA b hb hcb (by omega)
    calc (⇑ρ)^[k + 1] a = (⇑ρ)^[k] (ρ a) := Function.iterate_succ_apply _ _ _
    _ ≤ (⇑ρ)^[k] c := (ρ.strict_mono.iterate k).monotone (h.chain ha hcA hac)
    _ ≤ b := this

/-- Walking a jump set from a member `a` up to a member `b` applies `ρ` at most once per member
passed: iterating `ρ` from `a` as many times as `A` has members in `[a, b)` stays at or below
`b`. -/
theorem iterate_jumpMultiplicity_le (h : IsJumpSet ρ S A) {a b : ℕ+} (ha : a ∈ A) (hb : b ∈ A)
    (hab : a ≤ b) : (⇑ρ)^[jumpMultiplicity A a - jumpMultiplicity A b] a ≤ b :=
  h.iterate_le_aux _ a ha b hb hab rfl

/-- The strict form of `IsJumpSet.iterate_jumpMultiplicity_le`, available as soon as `b` is not
hit by `ρ` from inside `A`: the walk's last step lands strictly below `b`. -/
theorem iterate_jumpMultiplicity_lt (h : IsJumpSet ρ S A) {a b : ℕ+} (ha : a ∈ A) (hb : b ∈ A)
    (hab : a < b) (hb' : b ∉ A.image ⇑ρ) :
    (⇑ρ)^[jumpMultiplicity A a - jumpMultiplicity A b] a < b := by
  have hFne : (A.filter fun x => a ≤ x ∧ x < b).Nonempty :=
    ⟨a, Finset.mem_filter.mpr ⟨ha, le_refl a, hab⟩⟩
  set d := (A.filter fun x => a ≤ x ∧ x < b).max' hFne with hd
  have hdmem := Finset.max'_mem _ hFne
  rw [Finset.mem_filter] at hdmem
  obtain ⟨hdA, had, hdb⟩ := hdmem
  have hρd : ρ d < b := by
    rcases eq_or_lt_of_le (h.chain hdA hb hdb) with h2 | h2
    · exact absurd (Finset.mem_image.mpr ⟨d, hdA, h2⟩) hb'
    · exact h2
  have hcount : jumpMultiplicity A d = jumpMultiplicity A b + 1 := by
    have h1 : (A.filter fun x => d ≤ x) = insert d (A.filter fun x => b ≤ x) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hx, hdx⟩
        rcases eq_or_lt_of_le hdx with rfl | h'
        · exact Or.inl rfl
        · refine Or.inr ⟨hx, ?_⟩
          by_contra hbx
          rw [not_le] at hbx
          have hxmem : x ∈ A.filter fun y => a ≤ y ∧ y < b :=
            Finset.mem_filter.mpr ⟨hx, le_trans had (le_of_lt h'), hbx⟩
          exact absurd h' (not_lt.mpr (Finset.le_max' _ x hxmem))
      · rintro (rfl | ⟨hx, hbx⟩)
        · exact ⟨hdA, le_refl _⟩
        · exact ⟨hx, le_trans (le_of_lt hdb) hbx⟩
    have h2 : d ∉ A.filter fun x => b ≤ x := by
      simp only [Finset.mem_filter, not_and]
      exact fun _ => not_le.mpr hdb
    rw [jumpMultiplicity, jumpMultiplicity, h1, Finset.card_insert_of_notMem h2]
  have hda : jumpMultiplicity A d ≤ jumpMultiplicity A a := jumpMultiplicity_antitone A had
  have hkeq : jumpMultiplicity A a - jumpMultiplicity A b
      = (jumpMultiplicity A a - jumpMultiplicity A d) + 1 := by omega
  rw [hkeq, Function.iterate_succ_apply']
  exact lt_of_le_of_lt
    (ρ.strict_mono.monotone (h.iterate_jumpMultiplicity_le ha hdA had)) hρd

private theorem orbit_aux (h : IsJumpSet ρ S A) (u : WithTop ℕ+) :
    ∀ n : ℕ, ∀ i : ℕ+, i ∈ A →
      (∀ y ∈ A, i < y → (y : WithTop ℕ+) < u → y ∈ A.image ⇑ρ) →
      (A.filter fun x => i ≤ x ∧ (x : WithTop ℕ+) < u).card = n →
      A.filter (fun x => i ≤ x ∧ (x : WithTop ℕ+) < u)
        = (Finset.range n).image fun t => (⇑ρ)^[t] i := by
  intro n
  induction n with
  | zero =>
    intro i _ _ hcard
    rw [Finset.card_eq_zero] at hcard
    rw [hcard]
    simp
  | succ n ih =>
    intro i hi hu hcard
    have hFne : (A.filter fun x => i ≤ x ∧ (x : WithTop ℕ+) < u).Nonempty := by
      rw [← Finset.card_pos, hcard]
      omega
    have hiu : (i : WithTop ℕ+) < u := by
      obtain ⟨x, hx⟩ := hFne
      rw [Finset.mem_filter] at hx
      exact lt_of_le_of_lt (WithTop.coe_le_coe.mpr hx.2.1) hx.2.2
    have hsplit : A.filter (fun x => i ≤ x ∧ (x : WithTop ℕ+) < u)
        = insert i (A.filter fun x => ρ i ≤ x ∧ (x : WithTop ℕ+) < u) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hxA, hix, hxu⟩
        rcases eq_or_lt_of_le hix with rfl | hlt
        · exact Or.inl rfl
        · exact Or.inr ⟨hxA, h.chain hi hxA hlt, hxu⟩
      · rintro (rfl | ⟨hxA, hρix, hxu⟩)
        · exact ⟨hi, le_refl _, hiu⟩
        · exact ⟨hxA, le_trans (le_of_lt (ρ.lt_apply i)) hρix, hxu⟩
    have hinot : i ∉ A.filter fun x => ρ i ≤ x ∧ (x : WithTop ℕ+) < u := by
      rw [Finset.mem_filter]
      rintro ⟨-, h', -⟩
      exact absurd (ρ.lt_apply i) (not_lt.mpr h')
    have hcard' : (A.filter fun x => ρ i ≤ x ∧ (x : WithTop ℕ+) < u).card = n := by
      rw [hsplit, Finset.card_insert_of_notMem hinot] at hcard
      omega
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hsplit, Finset.card_eq_zero.mp hcard']
      simp
    · have hF'ne : (A.filter fun x => ρ i ≤ x ∧ (x : WithTop ℕ+) < u).Nonempty := by
        rw [← Finset.card_pos, hcard']
        omega
      set z := (A.filter fun x => ρ i ≤ x ∧ (x : WithTop ℕ+) < u).min' hF'ne with hz
      have hzmem := Finset.min'_mem _ hF'ne
      rw [Finset.mem_filter] at hzmem
      obtain ⟨hzA, hρiz, hzu⟩ := hzmem
      have hiz : i < z := lt_of_lt_of_le (ρ.lt_apply i) hρiz
      obtain ⟨y, hyA, hyz⟩ := Finset.mem_image.mp (hu z hzA hiz hzu)
      have hyi : y = i := by
        by_contra hne
        have hylt : y < z := hyz ▸ ρ.lt_apply y
        have hiy : i ≤ y := by
          by_contra hlt
          rw [not_le] at hlt
          have h' := h.chain hyA hi hlt
          rw [hyz] at h'
          exact absurd hiz (not_lt.mpr h')
        have hyF : y ∈ A.filter fun x => ρ i ≤ x ∧ (x : WithTop ℕ+) < u :=
          Finset.mem_filter.mpr ⟨hyA, h.chain hi hyA (lt_of_le_of_ne hiy (Ne.symm hne)),
            lt_trans (WithTop.coe_lt_coe.mpr hylt) hzu⟩
        exact absurd hylt (not_lt.mpr (Finset.min'_le _ y hyF))
      subst hyi
      have hρiA : ρ y ∈ A := by rw [hyz]; exact hzA
      have hu' : ∀ x ∈ A, ρ y < x → (x : WithTop ℕ+) < u → x ∈ A.image ⇑ρ :=
        fun x hx h1 h2 => hu x hx (lt_trans (ρ.lt_apply y) h1) h2
      rw [hsplit, ih (ρ y) hρiA hu' hcard']
      ext x
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro (rfl | ⟨m, hm, rfl⟩)
        · exact ⟨0, Nat.succ_pos n, rfl⟩
        · exact ⟨m + 1, by omega, (Function.iterate_succ_apply (⇑ρ) m y).symm⟩
      · rintro ⟨m, hm, rfl⟩
        cases m with
        | zero => exact Or.inl rfl
        | succ m => exact Or.inr ⟨m, by omega, by rw [Function.iterate_succ_apply]⟩

/-- Orbit-segment lemma: from a member `i` up to a bound `u` below which every higher member of
`A` is hit by `ρ` from inside `A`, a jump set is a single `ρ`-orbit segment based at `i`. The
bound lives in `WithTop ℕ+` so that `u = ⊤` reads the segment off to the top of `A`. -/
theorem filter_eq_image_iterate (h : IsJumpSet ρ S A) {i : ℕ+} {u : WithTop ℕ+} (hi : i ∈ A)
    (hu : ∀ y ∈ A, i < y → (y : WithTop ℕ+) < u → y ∈ A.image ⇑ρ) :
    A.filter (fun x => i ≤ x ∧ (x : WithTop ℕ+) < u)
      = (Finset.range (A.filter fun x => i ≤ x ∧ (x : WithTop ℕ+) < u).card).image
          fun t => (⇑ρ)^[t] i :=
  h.orbit_aux u _ i hi hu rfl

end IsJumpSet

end Atlas.Knowledge
