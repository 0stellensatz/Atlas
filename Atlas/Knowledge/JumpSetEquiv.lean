import Mathlib
import Atlas.Knowledge.JumpPairOf
import Atlas.Knowledge.JumpSetOf

/-!
# equivalence of jump sets and jump pairs

The parametrization the source's whole apparatus runs on: jump sets `Atlas.Knowledge.IsJumpSet`
and jump pairs `Atlas.Knowledge.IsJumpPair` for a shift `ρ` relative to an index set `S` are in
bijection, by `Atlas.Knowledge.JumpPairOf` one way and `Atlas.Knowledge.JumpSetOf` the other. The
statement covers the source's jump sets and extended jump sets at once, the two being `S = T ρ`
and `S = T_star ρ hρ`.

One roundtrip, `jumpPairOf_jumpSetOf`, is the multiplicity recovery already proved with the
converse construction. The other, `jumpSetOf_jumpPairOf`, is proved here: the orbit-segment lemma
`IsJumpSet.filter_eq_image_iterate` cuts a jump set at each index into the segment reaching to
the next index, and counting the cut against `jumpMultiplicity` matches it with the segment the
converse construction rebuilds.

## Main definitions

* `jumpSetEquiv` — the bijection, as an `Equiv` of subtypes.

## Main statements

* `jumpSetOf_jumpPairOf`, `jumpPairOf_jumpSetOf` — the two roundtrips.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

variable {ρ : Shift} {S : Set ℕ+} {A : Finset ℕ+} {P : Finset (ℕ+ × ℕ+)}

private lemma coe_lt_finsetMin_iff {s : Finset ℕ+} {x : ℕ+} :
    (x : WithTop ℕ+) < s.min ↔ ∀ y ∈ s, x < y := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · constructor
    · intro _ y hy
      exact absurd hy (Finset.notMem_empty y)
    · intro _
      rw [Finset.min_empty]
      exact WithTop.coe_lt_top x
  · rw [← Finset.coe_min' hs, WithTop.coe_lt_coe]
    exact Finset.lt_min'_iff s hs

/-- At an index `i` of `A`, the segment of a jump set running to the next index is the
`ρ`-orbit segment based at `i` of exactly the length the converse construction rebuilds. -/
private theorem string_eq (h : IsJumpSet ρ S A) {i : ℕ+} (hiA : i ∈ A) :
    A.filter (fun x => i ≤ x ∧
        (x : WithTop ℕ+) < ((A \ A.image ⇑ρ).filter fun j => i < j).min)
      = (Finset.range (jumpMultiplicity A i - jumpSetOf.tail (jumpPairOf ρ A) i)).image
          fun n => (⇑ρ)^[n] i := by
  have hu : ∀ y ∈ A, i < y →
      (y : WithTop ℕ+) < ((A \ A.image ⇑ρ).filter fun j => i < j).min → y ∈ A.image ⇑ρ := by
    intro y hy hiy hyu
    by_contra hyim
    have hymem : y ∈ (A \ A.image ⇑ρ).filter fun j => i < j :=
      Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hy, hyim⟩, hiy⟩
    exact absurd hyu (not_lt.mpr (Finset.min_le hymem))
  rw [h.filter_eq_image_iterate hiA hu]
  congr 2
  rcases ((A \ A.image ⇑ρ).filter fun j => i < j).eq_empty_or_nonempty with hemp | hne
  · have hut : ((A \ A.image ⇑ρ).filter fun j => i < j).min = ⊤ := by
      rw [hemp]
      exact Finset.min_empty
    have h1 : A.filter (fun x => i ≤ x ∧
          (x : WithTop ℕ+) < ((A \ A.image ⇑ρ).filter fun j => i < j).min)
        = A.filter fun x => i ≤ x := by
      apply Finset.filter_congr
      intro x _
      rw [hut]
      simp
    have h2 : jumpSetOf.tail (jumpPairOf ρ A) i = 0 := by
      apply jumpSetOf.tail_eq_zero
      intro r hr hir
      rw [mem_jumpPairOf] at hr
      have hrB : r.1 ∈ (A \ A.image ⇑ρ).filter fun j => i < j :=
        Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hr.1, hr.2.1⟩, hir⟩
      rw [hemp] at hrB
      exact absurd hrB (Finset.notMem_empty _)
    rw [h1, h2, Nat.sub_zero, jumpMultiplicity]
  · have hj₀mem := Finset.min'_mem _ hne
    rw [Finset.mem_filter] at hj₀mem
    obtain ⟨hj₀B, hij₀⟩ := hj₀mem
    rw [Finset.mem_sdiff] at hj₀B
    obtain ⟨hj₀A, hj₀im⟩ := hj₀B
    set j₀ := ((A \ A.image ⇑ρ).filter fun j => i < j).min' hne with hj₀def
    have hueq : ((A \ A.image ⇑ρ).filter fun j => i < j).min = (j₀ : WithTop ℕ+) :=
      (Finset.coe_min' hne).symm
    have htail : jumpSetOf.tail (jumpPairOf ρ A) i = jumpMultiplicity A j₀ := by
      apply le_antisymm
      · apply jumpSetOf.tail_le
        intro r hr hir
        rw [mem_jumpPairOf] at hr
        rw [hr.2.2]
        apply jumpMultiplicity_antitone
        exact Finset.min'_le _ _ (Finset.mem_filter.mpr
          ⟨Finset.mem_sdiff.mpr ⟨hr.1, hr.2.1⟩, hir⟩)
      · have hpair : ((j₀, ⟨jumpMultiplicity A j₀, jumpMultiplicity_pos hj₀A⟩) : ℕ+ × ℕ+)
            ∈ jumpPairOf ρ A := mem_jumpPairOf.mpr ⟨hj₀A, hj₀im, rfl⟩
        exact jumpSetOf.le_tail hpair hij₀
    have hsplit : A.filter (fun x => i ≤ x)
        = A.filter (fun x => i ≤ x ∧
            (x : WithTop ℕ+) < ((A \ A.image ⇑ρ).filter fun j => i < j).min)
          ∪ A.filter fun x => j₀ ≤ x := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hx, hix⟩
        rcases lt_or_ge x j₀ with h' | h'
        · exact Or.inl ⟨hx, hix, by rw [hueq]; exact_mod_cast h'⟩
        · exact Or.inr ⟨hx, h'⟩
      · rintro (⟨hx, hix, -⟩ | ⟨hx, hjx⟩)
        · exact ⟨hx, hix⟩
        · exact ⟨hx, le_trans (le_of_lt hij₀) hjx⟩
    have hdisj : Disjoint
        (A.filter fun x => i ≤ x ∧
          (x : WithTop ℕ+) < ((A \ A.image ⇑ρ).filter fun j => i < j).min)
        (A.filter fun x => j₀ ≤ x) := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      rw [Finset.mem_filter] at h1 h2
      have hxj : (x : WithTop ℕ+) < (j₀ : WithTop ℕ+) := hueq ▸ h1.2.2
      exact absurd h2.2 (not_le.mpr (by exact_mod_cast hxj))
    have hcards := congrArg Finset.card hsplit
    rw [Finset.card_union_of_disjoint hdisj] at hcards
    rw [htail]
    have e1 : jumpMultiplicity A i = (A.filter fun x => i ≤ x).card := rfl
    have e2 : jumpMultiplicity A j₀ = (A.filter fun x => j₀ ≤ x).card := rfl
    omega

/-- Reconstructing a jump set from its pair returns it: one half of the parametrization
([Pagano 2022, Prop. 2.3, p.416][Pagano2022]). -/
@[simp]
theorem jumpSetOf_jumpPairOf (h : IsJumpSet ρ S A) : jumpSetOf ρ (jumpPairOf ρ A) = A := by
  ext x
  rw [mem_jumpSetOf]
  constructor
  · rintro ⟨q, hq, n, hn, rfl⟩
    rw [mem_jumpPairOf] at hq
    obtain ⟨hq1, hq2, hq3⟩ := hq
    have hx : (⇑ρ)^[n] q.1 ∈ A.filter fun x => q.1 ≤ x ∧
        (x : WithTop ℕ+) < ((A \ A.image ⇑ρ).filter fun j => q.1 < j).min := by
      rw [string_eq h hq1]
      refine Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr ?_, rfl⟩
      rw [← hq3]
      exact hn
    exact (Finset.mem_filter.mp hx).1
  · intro hx
    have hAne : A.Nonempty := ⟨x, hx⟩
    have hminB : A.min' hAne ∈ A \ A.image ⇑ρ := by
      refine Finset.mem_sdiff.mpr ⟨A.min'_mem hAne, ?_⟩
      intro hmem
      obtain ⟨a, ha, hρa⟩ := Finset.mem_image.mp hmem
      exact absurd (A.min'_le a ha) (not_le.mpr (hρa ▸ ρ.lt_apply a))
    have hBne : ((A \ A.image ⇑ρ).filter fun j => j ≤ x).Nonempty :=
      ⟨A.min' hAne, Finset.mem_filter.mpr ⟨hminB, A.min'_le x hx⟩⟩
    have himem := Finset.max'_mem _ hBne
    rw [Finset.mem_filter] at himem
    obtain ⟨hiB, hix⟩ := himem
    rw [Finset.mem_sdiff] at hiB
    obtain ⟨hiA, hiIm⟩ := hiB
    set i := ((A \ A.image ⇑ρ).filter fun j => j ≤ x).max' hBne with hidef
    have hxu : (x : WithTop ℕ+) < ((A \ A.image ⇑ρ).filter fun j => i < j).min := by
      rw [coe_lt_finsetMin_iff]
      intro y hy
      rw [Finset.mem_filter] at hy
      by_contra hyx
      rw [not_lt] at hyx
      have hymem : y ∈ (A \ A.image ⇑ρ).filter fun j => j ≤ x :=
        Finset.mem_filter.mpr ⟨hy.1, hyx⟩
      exact absurd hy.2 (not_lt.mpr (Finset.le_max' _ _ hymem))
    have hxF : x ∈ A.filter fun x' => i ≤ x' ∧
        (x' : WithTop ℕ+) < ((A \ A.image ⇑ρ).filter fun j => i < j).min :=
      Finset.mem_filter.mpr ⟨hx, hix, hxu⟩
    rw [string_eq h hiA] at hxF
    obtain ⟨n, hn, hnx⟩ := Finset.mem_image.mp hxF
    rw [Finset.mem_range] at hn
    exact ⟨(i, ⟨jumpMultiplicity A i, jumpMultiplicity_pos hiA⟩),
      mem_jumpPairOf.mpr ⟨hiA, hiIm, rfl⟩, n, hn, hnx⟩

/-- Reading the pair off the reconstructed jump set returns it: the other half of the
parametrization ([Pagano 2022, Prop. 2.3, p.416][Pagano2022]). -/
@[simp]
theorem jumpPairOf_jumpSetOf (hP : IsJumpPair ρ S P) : jumpPairOf ρ (jumpSetOf ρ P) = P := by
  ext q
  rw [mem_jumpPairOf]
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨r, hr, n, hn, hx⟩ := mem_jumpSetOf.mp h1
    cases n with
    | succ n =>
      exfalso
      apply h2
      rw [← hx, Function.iterate_succ_apply' (⇑ρ) n r.1]
      exact Finset.mem_image.mpr
        ⟨(⇑ρ)^[n] r.1, mem_jumpSetOf.mpr ⟨r, hr, n, by omega, rfl⟩, rfl⟩
    | zero =>
      have hfst : r.1 = q.1 := hx
      have hmult := hP.jumpMultiplicity_jumpSetOf hr
      rw [hfst] at hmult
      have hsnd : q.2 = r.2 := PNat.coe_injective (h3.trans hmult)
      obtain rfl : q = r := Prod.ext hfst.symm hsnd
      exact hr
  · intro hq
    exact ⟨hP.fst_mem_jumpSetOf hq, hP.fst_not_mem_image hq,
      (hP.jumpMultiplicity_jumpSetOf hq).symm⟩

/-- The parametrization of jump sets by jump pairs: `A ↦ (I_A, β_A)` and `(I, β) ↦ A_{(I, β)}`
are mutually inverse, for jump sets and extended jump sets at once
([Pagano 2022, Prop. 2.3, p.416][Pagano2022]). -/
def jumpSetEquiv (ρ : Shift) (S : Set ℕ+) :
    {A : Finset ℕ+ // IsJumpSet ρ S A} ≃ {P : Finset (ℕ+ × ℕ+) // IsJumpPair ρ S P} where
  toFun A := ⟨jumpPairOf ρ A.1, A.2.jumpPairOf⟩
  invFun P := ⟨jumpSetOf ρ P.1, P.2.jumpSetOf⟩
  left_inv A := Subtype.ext (jumpSetOf_jumpPairOf A.2)
  right_inv P := Subtype.ext (jumpPairOf_jumpSetOf P.2)

@[simp]
theorem jumpSetEquiv_apply_coe (A : {A : Finset ℕ+ // IsJumpSet ρ S A}) :
    (jumpSetEquiv ρ S A : Finset (ℕ+ × ℕ+)) = jumpPairOf ρ (A : Finset ℕ+) :=
  rfl

@[simp]
theorem jumpSetEquiv_symm_apply_coe (P : {P : Finset (ℕ+ × ℕ+) // IsJumpPair ρ S P}) :
    ((jumpSetEquiv ρ S).symm P : Finset ℕ+) = jumpSetOf ρ (P : Finset (ℕ+ × ℕ+)) :=
  rfl

end Atlas.Knowledge
