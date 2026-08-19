import Mathlib
import Atlas.Knowledge.Shift
import Atlas.Knowledge.ShiftT

/-!
# depth and root along a shift

The source's `v_ρ` and the shooter it locates: the **depth** of a positive integer is the
number of times it can be pulled back along the shift, and its **root** is the endpoint of
that pull-back, a member of `T_ρ`. In the shooting game of `Atlas.Knowledge.GameJumpPair` the
depth of the rabbit's position is the length of the next shot and the root is the shooter's
position; the game's transition probabilities of the source's §7 are indexed by the same two
readings.

## Main definitions

* `Shift.depth` — the largest `m` with `x` in the image of the `m`-th iterate: the source's
  `v_ρ (x)`.
* `Shift.root` — a preimage of `x` under the `depth`-th iterate.

## Main statements

* `Shift.exists_iterate_depth` — the depth is attained, off which the root is read.
* `Shift.depth_lt` — the depth sits strictly below the position.
* `Shift.iterate_root` — the root really is a preimage: `ρ^[depth x] (root x) = x`.
* `Shift.root_mem_T` — the root is missed by the shift: one more pull-back would contradict
  the maximality of the depth.
* `Shift.depth_iterate_of_mem_T`, `Shift.root_iterate_of_mem_T` — on iterates of a
  `T_ρ`-point the depth is exact and the root is that point.

## Implementation notes

The depth is an `sSup` over a set of exponents that contains `0` and is bounded by `x`
itself—each application of the shift strictly increases, so an `m`-fold preimage forces
`m < x`—and `Nat.sSup_mem` turns the bound into a genuine witness, off which the root is read
by `Function.invFun`. No junk arises: every positive integer has a depth and a root, the
source's `v_ρ` being total as well.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

namespace Shift

variable (ρ : Shift)

/-- The **depth** of `x` along a shift: the largest number of times `x` pulls back—the
source's `v_ρ (x) = max {i : x ∈ im (ρ^i)}` ([Pagano 2022, §7, p.453][Pagano2022]). -/
noncomputable def depth (x : ℕ+) : ℕ :=
  sSup {m | ∃ y, (⇑ρ)^[m] y = x}

private theorem depth_set_nonempty (x : ℕ+) : {m | ∃ y, (⇑ρ)^[m] y = x}.Nonempty :=
  ⟨0, x, rfl⟩

private theorem depth_set_bddAbove (x : ℕ+) : BddAbove {m | ∃ y, (⇑ρ)^[m] y = x} := by
  refine ⟨(x : ℕ), fun m hm => ?_⟩
  obtain ⟨y, hy⟩ := hm
  have h := ρ.add_le_iterate y m
  rw [hy] at h
  have := y.pos
  omega

/-- The depth is attained: some `y` reaches `x` in exactly `depth x` steps. -/
theorem exists_iterate_depth (x : ℕ+) : ∃ y, (⇑ρ)^[ρ.depth x] y = x :=
  Nat.sSup_mem (ρ.depth_set_nonempty x) (ρ.depth_set_bddAbove x)

/-- The depth sits strictly below the position: pulling back `x` times would outrun `x`. -/
theorem depth_lt (x : ℕ+) : ρ.depth x < (x : ℕ) := by
  have hle : ρ.depth x ≤ (x : ℕ) - 1 := by
    refine csSup_le ⟨0, x, rfl⟩ (fun m hm => ?_)
    obtain ⟨y, hy⟩ := hm
    have h := ρ.add_le_iterate y m
    rw [hy] at h
    have := y.pos
    omega
  have := x.pos
  omega

/-- The **root** of `x` along a shift: the point from which `x` is reached in `depth x`
steps—in the shooting game, the position of the shooter aiming at the rabbit at `x`
([Pagano 2022, §7, p.453][Pagano2022]). -/
noncomputable def root (x : ℕ+) : ℕ+ :=
  Function.invFun ((⇑ρ)^[ρ.depth x]) x

/-- The root is a genuine preimage: `ρ^[depth x] (root x) = x`. -/
theorem iterate_root (x : ℕ+) : (⇑ρ)^[ρ.depth x] (ρ.root x) = x :=
  Function.invFun_eq (ρ.exists_iterate_depth x)

/-- The root lies in `T_ρ`: were it an image, `x` would pull back once more than its depth
allows ([Pagano 2022, §7, p.453][Pagano2022], the shooter shoots from `T_ρ`). -/
theorem root_mem_T (x : ℕ+) : ρ.root x ∈ Shift.T ρ := by
  refine ⟨Set.mem_univ _, ?_⟩
  rintro ⟨z, -, hz⟩
  have hz' : ρ z = ρ.root x := hz
  have h : (⇑ρ)^[ρ.depth x + 1] z = x := by
    rw [Function.iterate_succ_apply, hz']
    exact ρ.iterate_root x
  have hle : ρ.depth x + 1 ≤ ρ.depth x := le_csSup (ρ.depth_set_bddAbove x) ⟨z, h⟩
  omega

/-- On the iterates of a `T_ρ`-point the depth is exact: `depth (ρ^[m] y) = m` for `y` missed
by the shift. -/
theorem depth_iterate_of_mem_T {y : ℕ+} (hy : y ∈ Shift.T ρ) (m : ℕ) :
    ρ.depth ((⇑ρ)^[m] y) = m := by
  have hmem : m ∈ {k | ∃ z, (⇑ρ)^[k] z = (⇑ρ)^[m] y} := ⟨y, rfl⟩
  have hle : m ≤ ρ.depth _ := le_csSup (ρ.depth_set_bddAbove _) hmem
  rcases Nat.lt_or_ge m (ρ.depth ((⇑ρ)^[m] y)) with hlt | hge
  · exfalso
    obtain ⟨z, hz⟩ := ρ.exists_iterate_depth ((⇑ρ)^[m] y)
    set d := ρ.depth ((⇑ρ)^[m] y)
    have hsplit : d = m + (d - m) := by omega
    rw [hsplit, Function.iterate_add_apply] at hz
    have hy' : (⇑ρ)^[d - m] z = y := by
      have := Function.Injective.iterate ρ.inj m
      exact this (by rw [hz])
    have hdm : 1 ≤ d - m := by omega
    obtain ⟨k, hk⟩ : ∃ k, d - m = k + 1 := ⟨d - m - 1, by omega⟩
    rw [hk, Function.iterate_succ_apply'] at hy'
    exact hy.2 ⟨(⇑ρ)^[k] z, Set.mem_univ _, hy'⟩
  · omega

/-- The root of an iterate of a `T_ρ`-point is that point: the companion of the exact depth,
which is what computes the shooter under a known pull-back. -/
theorem root_iterate_of_mem_T {y : ℕ+} (hy : y ∈ Shift.T ρ) (m : ℕ) :
    ρ.root ((⇑ρ)^[m] y) = y := by
  have hd := ρ.depth_iterate_of_mem_T hy m
  have hr := ρ.iterate_root ((⇑ρ)^[m] y)
  rw [hd] at hr
  exact Function.Injective.iterate ρ.inj m hr

end Shift

end Atlas.Knowledge
