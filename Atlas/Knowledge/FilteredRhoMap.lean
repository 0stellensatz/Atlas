import Mathlib
import Atlas.Knowledge.FilteredModule
import Atlas.Knowledge.Shift

/-!
# rho-map of a filtered module

The ρ-map a filtered module over a local ring carries: `ρ_M (i)` is the largest index whose
filtration step absorbs the maximal ideal times the `i`-th step. Over the source's complete
discrete valuation ring this is the largest `j` with `π_R M_i ⊆ M_j`, the function that records
how far multiplication by the uniformizer pushes the filtration; it is the bridge between
filtered modules and the shifts `Atlas.Knowledge.Shift` of the jump-set combinatorics, crossed
in `Atlas.Knowledge.FilteredLinear`. The condition `ρ_M ≥ ρ` cutting out the source's category
`C_ρ` is `FilteredModule.RhoBounded` here.

## Main definitions

* `FilteredModule.rhoMap` — the ρ-map, valued in `WithTop ℕ+`.
* `FilteredModule.RhoBounded` — the condition `ρ_M ≥ ρ` against a shift `ρ`.

## Main statements

* `FilteredModule.le_rhoMap_iff` — the characterization `j ≤ ρ_M (i) ↔ 𝔪 • filt i ≤ filt j`.
* `FilteredModule.rhoMap_eq_top_iff` — `ρ_M (i) = ⊤` says exactly `𝔪 • filt i = ⊥`.
* `FilteredModule.rhoMap_mono` — the ρ-map is non-decreasing.

## Implementation notes

The source fixes a uniformizer `π_R` and speaks of `π_R M_i`; here the ideal
`IsLocalRing.maximalIdeal R` replaces the element, which over a discrete valuation ring is the
same submodule (`𝔪 = (π_R)`) and frees the definition from the choice. Only `IsLocalRing` is
assumed: the sharper hypotheses of the source's §3.3—a complete discrete valuation ring—enter
with the statements that need them, not with the vocabulary.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]

namespace FilteredModule

variable (F : FilteredModule R M)

/-- The **ρ-map** of a filtered module over a local ring: `ρ_M (i)` is the largest index whose
filtration step contains `𝔪 • filt i`—over a discrete valuation ring, the largest `j` with
`π_R M_i ⊆ M_j` ([Pagano 2022, §3.3.1, p.425][Pagano2022]). -/
noncomputable def rhoMap (i : ℕ+) : WithTop ℕ+ :=
  maxIndex fun j => maximalIdeal R • F.filt i ≤ F.filt j

/-- The characterization of the ρ-map: `j ≤ ρ_M (i)` exactly when the `j`-th step absorbs
`𝔪 • filt i` ([Pagano 2022, §3.3.1, p.425][Pagano2022]). -/
theorem le_rhoMap_iff {i j : ℕ+} :
    (j : WithTop ℕ+) ≤ F.rhoMap i ↔ maximalIdeal R • F.filt i ≤ F.filt j :=
  le_maxIndex_iff (fun _ _ hjj' h => h.trans (F.antitone_filt hjj'))
    (F.filt_one ▸ le_top)

/-- The ρ-map takes the value `⊤` at `i` exactly when the maximal ideal kills the `i`-th step:
the source's `π_R M_i ≠ 0` is `ρ_M (i) < ⊤` ([Pagano 2022, §3.3.1, p.425][Pagano2022]). -/
theorem rhoMap_eq_top_iff {i : ℕ+} : F.rhoMap i = ⊤ ↔ maximalIdeal R • F.filt i = ⊥ := by
  constructor
  · intro h
    have hall : ∀ j, maximalIdeal R • F.filt i ≤ F.filt j := fun j =>
      forall_of_maxIndex_eq_top h j
    have hle : maximalIdeal R • F.filt i ≤ ⨅ j, F.filt j := le_iInf hall
    rwa [F.iInf_filt_eq_bot, le_bot_iff] at hle
  · intro h
    exact maxIndex_eq_top fun j => h ▸ bot_le

/-- The ρ-map is non-decreasing ([Pagano 2022, §3.3.1, p.425][Pagano2022]). -/
theorem rhoMap_mono : Monotone F.rhoMap := by
  intro i i' hii'
  refine le_of_forall_coe_le fun j hj => ?_
  rw [F.le_rhoMap_iff] at hj ⊢
  exact le_trans (Submodule.smul_mono le_rfl (F.antitone_filt hii')) hj

/-- The condition `ρ_M ≥ ρ` against a shift, which cuts the source's category `C_ρ` out of the
filtered modules over `R` ([Pagano 2022, §3.3.2, p.425][Pagano2022]). -/
def RhoBounded (ρ : Shift) : Prop :=
  ∀ i : ℕ+, maximalIdeal R • F.filt i ≤ F.filt (ρ i)

theorem rhoBounded_iff_le_rhoMap {ρ : Shift} :
    F.RhoBounded ρ ↔ ∀ i, (ρ i : WithTop ℕ+) ≤ F.rhoMap i := by
  constructor
  · exact fun h i => F.le_rhoMap_iff.mpr (h i)
  · exact fun h i => F.le_rhoMap_iff.mp (h i)

end FilteredModule

end Atlas.Knowledge
