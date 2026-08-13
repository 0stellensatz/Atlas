import Mathlib
import Atlas.Knowledge.StandardFiltered
import Atlas.Knowledge.FilteredModulePi
import Atlas.Knowledge.FilteredDefect
import Atlas.Knowledge.FilteredComplete
import Atlas.Knowledge.ShiftTStar

/-!
# free filtered modules

The free models of the source's §3.3 and what makes them free. A finite index of
(level, copy) pairs `D` determines the product `∏_{j ∈ D} S (level j)` of standard modules
`Atlas.Knowledge.StandardFiltered`; the source's `M_ρ^f` is the index `T_ρ × {0, …, f - 1}`,
and its presenting module `M_ρ^{f - 1} ⊕ M_ρ^*` is the same index enlarged by the single pair
`(e_ρ^*, 0)`—both are `freeFiltered` at the two `Finset`s `Shift.freeIndex` and
`Shift.starIndex`. The universal property of the product model—filtered morphisms out of it
into any `F` in `C_ρ` are exactly the choices of an element of `F.filt (level j)` per
index—is the finite, concrete face of the source's representability of `H_{(X, g)}`, and the
freeness criterion in terms of the defects of `Atlas.Knowledge.FilteredDefect` is recorded as
the claim `isFree_iff_defect_eq_zero`.

## Main definitions

* `Shift.freeIndex`, `Shift.starIndex` — the index `Finset`s of `M_ρ^f` and of
  `M_ρ^{f - 1} ⊕ M_ρ^*`.
* `freeFiltered` — the product of standard modules over an index `Finset`.
* `IsFilteredBasis` — a filtered basis: a filtered isomorphism from the model carrying the
  coordinate vectors to prescribed elements.
* `IsFree` — the `(f, ρ)`-free filtered modules.

## Main statements

* `isFilteredHom_linearCombination`, `eq_linearCombination_of_isFilteredHom` — the universal
  property of the model, in both directions.
* `isFree_iff_defect_eq_zero` — the freeness criterion: every defect and codefect vanishes and
  each `f_i` on `T_ρ` equals `f`. Claim recorded ahead of its proof.

## Implementation notes

The source builds `M_ρ^f` as a completed product over a possibly infinite `T_ρ`; this tranche
stays with finite `T_ρ` throughout, so products are finite, already complete, and need no
completion functor. Multiplicities are encoded in the index set itself—`f` copies of level `i`
are the pairs `(i, 0), …, (i, f - 1)`—which lets one construction carry both `M_ρ^f` and
`M_ρ^{f - 1} ⊕ M_ρ^*`.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open IsDiscreteValuationRing

/-- The index of the free model `M_ρ^f`: `f` copies of each level in `T_ρ`. The multiplicity is
a *positive* integer, as in the source—at `f = 0` the model would collapse to the trivial
module and the classification claims would be false as stated
([Pagano 2022, Def. 3.25, p.427][Pagano2022]). -/
noncomputable def Shift.freeIndex {ρ : Shift} (hρ : (Shift.T ρ).Finite) (f : ℕ+) :
    Finset (ℕ+ × ℕ) :=
  hρ.toFinset ×ˢ Finset.range (f : ℕ)

/-- The index of the presenting module `M_ρ^{f - 1} ⊕ M_ρ^*`: `f` copies of each level in
`T_ρ` and one copy of level `e_ρ^*` ([Pagano 2022, §3.3.4, p.429][Pagano2022]). -/
noncomputable def Shift.starIndex {ρ : Shift} (hρ : (Shift.T ρ).Finite) (f : ℕ+) :
    Finset (ℕ+ × ℕ) :=
  Shift.freeIndex hρ f ∪ {(Shift.e_star ρ hρ, 0)}

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The free model over an index of (level, copy) pairs: the finite product of the standard
modules `S (level j)` ([Pagano 2022, Def. 3.25, p.427][Pagano2022]). -/
noncomputable def freeFiltered (ρ : Shift) (D : Finset (ℕ+ × ℕ)) :
    FilteredModule R (↥D → R) :=
  FilteredModule.pi fun j => standardFiltered ρ j.1.1

theorem mem_freeFiltered_filt {ρ : Shift} {D : Finset (ℕ+ × ℕ)} {x : ↥D → R} {i : ℕ+} :
    x ∈ (freeFiltered (R := R) ρ D).filt i ↔
      ∀ j : ↥D, (i : WithTop ℕ+) ≤ standardWeight ρ j.1.1 (x j) := by
  change x ∈ (FilteredModule.pi fun j : ↥D => standardFiltered (R := R) ρ j.1.1).filt i ↔ _
  exact FilteredModule.mem_pi_filt

/-- The weight of a vector of the free model is the least of the standard weights of its
coordinates ([Pagano 2022, §3.3.2, p.426][Pagano2022]). -/
theorem weight_freeFiltered {ρ : Shift} {D : Finset (ℕ+ × ℕ)} (x : ↥D → R) :
    (freeFiltered ρ D).weight x =
      Finset.univ.inf fun j : ↥D => standardWeight ρ j.1.1 (x j) := by
  rw [freeFiltered, FilteredModule.weight_pi]
  simp

/-- The ρ-map of the free model dominates `ρ`—the one condition of the source's category `C_ρ`
recorded here; its completeness and linearity are not part of this statement
([Pagano 2022, Def. 3.25, p.427][Pagano2022]). -/
theorem freeFiltered_rhoBounded (ρ : Shift) (D : Finset (ℕ+ × ℕ)) :
    (freeFiltered (R := R) ρ D).RhoBounded ρ := by
  intro i
  rw [Submodule.smul_le]
  intro r hr x hx
  change x ∈ (FilteredModule.pi fun j : ↥D => standardFiltered (R := R) ρ j.1.1).filt i at hx
  change r • x ∈ (FilteredModule.pi fun j : ↥D => standardFiltered (R := R) ρ j.1.1).filt (ρ i)
  rw [FilteredModule.mem_pi_filt] at hx ⊢
  intro j
  exact standardFiltered_rhoBounded ρ j.1.1 i (Submodule.smul_mem_smul hr (hx j))

section UniversalProperty

variable {M : Type*} [AddCommGroup M] [Module R M] {F : FilteredModule R M} {ρ : Shift}
  {D : Finset (ℕ+ × ℕ)}

/-- Half of the universal property of the free model: a choice of elements `v j ∈ F.filt
(level j)` induces the filtered morphism `x ↦ ∑ j, x j • v j`, whenever `ρ_F ≥ ρ`—the finite
form of the source's representability of `H_{(X, g)}`
([Pagano 2022, Prop. 3.21, p.426][Pagano2022]). -/
theorem isFilteredHom_linearCombination (hF : F.RhoBounded ρ) {v : ↥D → M}
    (hv : ∀ j, v j ∈ F.filt j.1.1) :
    IsFilteredHom (freeFiltered ρ D) F (Fintype.linearCombination R v) := by
  intro i x hx
  rw [Fintype.linearCombination_apply]
  refine Submodule.sum_mem _ fun j _ => ?_
  have h1 := isFilteredHom_toSpanSingleton hF (hv j) i (x j)
    (mem_standardFiltered_filt.mpr (mem_freeFiltered_filt.mp hx j))
  rwa [LinearMap.toSpanSingleton_apply] at h1

/-- The other half of the universal property: every filtered morphism out of the free model is
the linear combination against the images of the coordinate vectors, and those images have the
prescribed weights ([Pagano 2022, Prop. 3.21, p.426][Pagano2022]). -/
theorem eq_linearCombination_of_isFilteredHom {φ : (↥D → R) →ₗ[R] M}
    (hφ : IsFilteredHom (freeFiltered ρ D) F φ) :
    (∀ j, φ (Pi.single j 1) ∈ F.filt j.1.1) ∧
      φ = Fintype.linearCombination R fun j => φ (Pi.single j 1) := by
  constructor
  · intro j
    refine hφ j.1.1 _ (mem_freeFiltered_filt.mpr fun j' => ?_)
    rcases eq_or_ne j' j with rfl | hne
    · rw [Pi.single_eq_same]
      simp [standardWeight]
    · rw [Pi.single_eq_of_ne hne]
      exact le_top.trans_eq (by simp [standardWeight])
  · refine LinearMap.ext fun x => ?_
    conv_lhs => rw [pi_eq_sum_univ' x]
    rw [map_sum, Fintype.linearCombination_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul]

end UniversalProperty

section Freeness

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- A **filtered basis** of `F` over the index `D`: a filtered isomorphism from the free model
carrying the coordinate vectors to the members of the basis
([Pagano 2022, Def. 3.23, p.427][Pagano2022]). -/
def IsFilteredBasis (ρ : Shift) (D : Finset (ℕ+ × ℕ)) (F : FilteredModule R M)
    (v : ↥D → M) : Prop :=
  ∃ e : (↥D → R) ≃ₗ[R] M,
    IsFilteredHom (freeFiltered ρ D) F (e : (↥D → R) →ₗ[R] M) ∧
      IsFilteredHom F (freeFiltered ρ D) (e.symm : M →ₗ[R] (↥D → R)) ∧
        ∀ j, e (Pi.single j 1) = v j

/-- The **`(f, ρ)`-free** filtered modules: those filtered-isomorphic to the free model
`M_ρ^f` ([Pagano 2022, Def. 3.25, p.427][Pagano2022]). -/
def IsFree (ρ : Shift) (hρ : (Shift.T ρ).Finite) (f : ℕ+) (F : FilteredModule R M) : Prop :=
  ∃ e : (↥(Shift.freeIndex hρ f) → R) ≃ₗ[R] M,
    IsFilteredHom (freeFiltered ρ (Shift.freeIndex hρ f)) F
        (e : (↥(Shift.freeIndex hρ f) → R) →ₗ[R] M) ∧
      IsFilteredHom F (freeFiltered ρ (Shift.freeIndex hρ f))
        (e.symm : M →ₗ[R] (↥(Shift.freeIndex hρ f) → R))

/-- The freeness criterion: a complete, strictly linear member of `C_ρ` is `(f, ρ)`-free
exactly when every defect and codefect vanishes and each graded piece over `T_ρ` has dimension
`f`. The source states the criterion for a linear member of `C_ρ`; strict linearity is required
here because the defects of `Atlas.Knowledge.FilteredDefect` are defined only under it. Claim
recorded ahead of its proof ([Pagano 2022, Prop. 3.24, p.427][Pagano2022]). -/
theorem isFree_iff_defect_eq_zero {ρ : Shift} (hρ : (Shift.T ρ).Finite) (f : ℕ+)
    {F : FilteredModule R M} (hM : F.IsComplete) (hF : F.RhoBounded ρ)
    (h : F.IsStrictlyLinear) {π : R} (hπ : Irreducible π) :
    IsFree ρ hρ f F ↔
      (∀ i, FilteredModule.defect h hπ i = 0) ∧ (∀ i, FilteredModule.codefect h hπ i = 0) ∧
        ∀ i ∈ Shift.T ρ, F.fDim h.1 i = (f : ℕ) := by
  sorry

end Freeness

end Atlas.Knowledge
