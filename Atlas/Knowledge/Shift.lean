import Mathlib

/-!
# shift

A **shift** is a strictly increasing function `ρ : ℕ+ → ℕ+` with `1 < ρ 1`. Shifts are what jump
sets are defined in terms of, and the two conditions are exactly what the jump-set machinery
needs: strict monotonicity makes `ρ` injective, so the complement `Atlas.Knowledge.ShiftT` of its
image is what carries information, and `1 < ρ 1` is what keeps that complement nonempty.

The source writes the domain as `ℤ⩾1`; here it is `ℕ+`, which is the same ordered monoid and
carries the coercion and arithmetic lemmas Mathlib already has for it.

## Main definitions

* `Shift` — a strictly increasing `ρ : ℕ+ → ℕ+` with `1 < ρ 1`.

## Implementation notes

`Shift` is bundled as a structure with a `FunLike` instance rather than left as a subtype of
`ℕ+ → ℕ+`, so that `ρ i` means what it says and the two conditions travel with the function.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

/-- A **shift** is a strictly increasing function `ℕ+ → ℕ+` sending `1` above `1`
([Pagano 2022, §2, p.415][Pagano2022]). -/
structure Shift where
  shift_map : ℕ+ → ℕ+
  strict_mono : StrictMono shift_map
  one_lt_shift_one : 1 < shift_map 1

instance : FunLike Shift ℕ+ ℕ+ where
  coe := Shift.shift_map
  coe_injective := by
    intro ρ ρ' hρ
    cases ρ; cases ρ'; congr

namespace Shift

@[simp]
theorem coe_mk (f : ℕ+ → ℕ+) (h₁ h₂) : ⇑(⟨f, h₁, h₂⟩ : Shift) = f := rfl

@[ext]
theorem ext {f g : Shift} (h : ∀ n, f n = g n) : f = g := DFunLike.ext _ _ h

/-- A shift is injective, being strictly increasing. -/
lemma inj (ρ : Shift) : (⇑ρ).Injective := by
  rw [coe_mk]
  apply StrictMono.injective ρ.strict_mono

/-- A shift moves every point strictly up. -/
lemma lt_apply (ρ : Shift) (x : ℕ+) : x < ρ x := by
  induction x with
  | one => exact ρ.one_lt_shift_one
  | succ n ih => exact (PNat.add_one_le_iff.mpr ih).trans_lt (ρ.strict_mono (PNat.lt_add_right n 1))

/-- Iterating a shift from any starting point is strictly increasing in the iteration count. -/
lemma iterate_strictMono_right (ρ : Shift) (x : ℕ+) : StrictMono fun n => (⇑ρ)^[n] x :=
  strictMono_nat_of_lt_succ fun n => by
    rw [Function.iterate_succ_apply']
    exact ρ.lt_apply _

lemma iterate_le_iterate_right (ρ : Shift) (x : ℕ+) {m n : ℕ} (h : m ≤ n) :
    (⇑ρ)^[m] x ≤ (⇑ρ)^[n] x :=
  (ρ.iterate_strictMono_right x).monotone h

lemma le_iterate (ρ : Shift) (x : ℕ+) (n : ℕ) : x ≤ (⇑ρ)^[n] x :=
  (ρ.iterate_strictMono_right x).monotone (Nat.zero_le n)

/-- The least element of a nonempty finite set is not hit by a shift: shifts move strictly up. -/
lemma min'_mem_sdiff_image (ρ : Shift) {A : Finset ℕ+} (hA : A.Nonempty) :
    A.min' hA ∈ A \ A.image ⇑ρ := by
  refine Finset.mem_sdiff.mpr ⟨A.min'_mem hA, ?_⟩
  intro hmem
  obtain ⟨a, ha, hρa⟩ := Finset.mem_image.mp hmem
  exact absurd (A.min'_le a ha) (not_le.mpr (hρa ▸ ρ.lt_apply a))

end Shift

end Atlas.Knowledge
