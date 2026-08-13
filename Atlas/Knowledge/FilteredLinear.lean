import Mathlib
import Atlas.Knowledge.FilteredRhoMap

/-!
# linear and strictly linear filtered modules

The two conditions under which the ρ-map of `Atlas.Knowledge.FilteredRhoMap` is an honest shift.
A filtered module is *linear* when each graded piece is a vector space over the residue field
and the maximal ideal kills no step—so the ρ-map satisfies `i < ρ_M (i) < ⊤`—and *strictly
linear* when moreover multiplication by the uniformizer is a filtered morphism step by step,
which is the growth condition `ρ_M (i) + 1 ≤ ρ_M (i + 1)`. For a strictly linear module the
ρ-map drops from `WithTop ℕ+` to a `Atlas.Knowledge.Shift` (`FilteredModule.rhoShift`), and that
is the source's Remark 3.16: strict linearity is exactly "the ρ-map is a shift".

## Main definitions

* `FilteredModule.IsLinear`, `FilteredModule.IsStrictlyLinear` — the two conditions.
* `FilteredModule.rhoFn` — the ρ-map of a linear module, valued in `ℕ+`.
* `FilteredModule.rhoShift` — the ρ-map of a strictly linear module, as a `Shift`.

## Main statements

* `FilteredModule.lt_rhoFn` — a linear module's ρ-map moves every index strictly up.
* `FilteredModule.rhoFn_add_one_le` — strict linearity as the step condition on `rhoFn`.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]

namespace FilteredModule

variable (F : FilteredModule R M)

/-- A filtered module is **linear** when each step is carried into the next by the maximal ideal
—so the graded pieces are residue-field vector spaces—and no step is killed by it: condition
(a) of the source's Remark 3.16, equivalently `i < ρ_M (i) < ⊤`
([Pagano 2022, Def. 3.17, p.425][Pagano2022]). -/
def IsLinear : Prop :=
  ∀ i : ℕ+, maximalIdeal R • F.filt i ≤ F.filt (i + 1) ∧ maximalIdeal R • F.filt i ≠ ⊥

/-- A filtered module is **strictly linear** when it is linear and its ρ-map grows by at least
one per step—condition (b) of the source's Remark 3.16, which makes multiplication by the
uniformizer a filtered morphism ([Pagano 2022, Def. 3.17, p.425][Pagano2022]). -/
def IsStrictlyLinear : Prop :=
  F.IsLinear ∧ ∀ i : ℕ+, F.rhoMap i + 1 ≤ F.rhoMap (i + 1)

variable {F}

/-- The ρ-map of a linear filtered module, valued in `ℕ+`: linearity rules out `⊤`
([Pagano 2022, §3.3.1, p.425][Pagano2022]). -/
noncomputable def rhoFn (h : F.IsLinear) (i : ℕ+) : ℕ+ :=
  (F.rhoMap i).untop (by rw [Ne, F.rhoMap_eq_top_iff]; exact (h i).2)

@[simp]
theorem coe_rhoFn (h : F.IsLinear) (i : ℕ+) : ((rhoFn h i : ℕ+) : WithTop ℕ+) = F.rhoMap i :=
  WithTop.coe_untop _ _

/-- Each step of a linear module is absorbed at its `rhoFn`-index: `𝔪 • filt i ⊆ filt (ρ_M i)`
([Pagano 2022, §3.3.1, p.425][Pagano2022]). -/
theorem smul_filt_le_filt_rhoFn (h : F.IsLinear) (i : ℕ+) :
    maximalIdeal R • F.filt i ≤ F.filt (rhoFn h i) :=
  F.le_rhoMap_iff.mp (coe_rhoFn h i).le

/-- A linear module's ρ-map moves every index strictly up
([Pagano 2022, Rem. 3.16, p.425][Pagano2022]). -/
theorem lt_rhoFn (h : F.IsLinear) (i : ℕ+) : i < rhoFn h i := by
  have h1 : ((i + 1 : ℕ+) : WithTop ℕ+) ≤ F.rhoMap i := F.le_rhoMap_iff.mpr (h i).1
  rw [← coe_rhoFn h i, WithTop.coe_le_coe] at h1
  exact lt_of_lt_of_le (PNat.lt_add_right i 1) h1

/-- Strict linearity, read on `rhoFn`: the ρ-map grows by at least one per step
([Pagano 2022, Rem. 3.16, p.425][Pagano2022]). -/
theorem rhoFn_add_one_le (h : F.IsStrictlyLinear) (i : ℕ+) :
    rhoFn h.1 i + 1 ≤ rhoFn h.1 (i + 1) := by
  have h1 := h.2 i
  rw [← coe_rhoFn h.1 i, ← coe_rhoFn h.1 (i + 1)] at h1
  rw [← WithTop.coe_le_coe]
  calc ((rhoFn h.1 i + 1 : ℕ+) : WithTop ℕ+)
      = (rhoFn h.1 i : WithTop ℕ+) + 1 := by push_cast; rfl
    _ ≤ (rhoFn h.1 (i + 1) : WithTop ℕ+) := h1

/-- The ρ-map of a strictly linear filtered module is a **shift**: the content of the source's
Remark 3.16, and the point where filtered modules meet the jump-set combinatorics
([Pagano 2022, Rem. 3.16, p.425][Pagano2022]). -/
noncomputable def rhoShift (h : F.IsStrictlyLinear) : Shift where
  shift_map := rhoFn h.1
  strict_mono := by
    have hstep : ∀ i : ℕ+, rhoFn h.1 i < rhoFn h.1 (i + 1) := fun i =>
      lt_of_lt_of_le (PNat.lt_add_right _ 1) (rhoFn_add_one_le h i)
    intro a b hab
    induction b with
    | one =>
      exfalso
      have h1 : (a : ℕ) < 1 := by exact_mod_cast hab
      have h2 := a.pos
      omega
    | succ n ih =>
      rcases lt_or_eq_of_le (PNat.lt_add_one_iff.mp hab) with h' | h'
      · exact lt_trans (ih h') (hstep n)
      · exact h' ▸ hstep n
  one_lt_shift_one := lt_rhoFn h.1 1

@[simp]
theorem rhoShift_apply (h : F.IsStrictlyLinear) (i : ℕ+) : rhoShift h i = rhoFn h.1 i := rfl

end FilteredModule

end Atlas.Knowledge
