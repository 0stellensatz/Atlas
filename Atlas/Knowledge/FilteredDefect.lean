import Mathlib
import Atlas.Knowledge.FilteredLinear
import Atlas.Knowledge.FilteredGradedPiece

/-!
# defect and codefect of a filtered module

The graded data multiplication by a uniformizer carries on a strictly linear filtered module:
the map `[π_R]_i` it induces from the `i`-th graded piece to the one at `ρ_M (i)`, and the three
residue-field dimensions attached to it—`f_i` of the piece itself, the *defect* of the kernel,
the *codefect* of the cokernel. These are the invariants in which the source states
`(f, ρ)`-freeness (`Atlas.Knowledge.FreeFiltered`) and `(f, ρ)`-quasi-freeness
(`Atlas.Knowledge.QuasiFreeFiltered`): free means every defect and codefect vanishes, quasi-free
allows a single one-dimensional defect at the critical index.

## Main definitions

* `FilteredModule.piGradedMap` — the map `[π_R]_i : F_i → F_{ρ_M (i)}`.
* `FilteredModule.fDim` — `f_i (M)`, the residue-field dimension of the `i`-th graded piece.
* `FilteredModule.defect`, `FilteredModule.codefect` — the dimensions of the kernel and
  cokernel of `[π_R]_i`.

## Implementation notes

The ring is a discrete valuation ring as in the source's §3.3, so that an irreducible `π` *is*
a uniformizer—`(π) = 𝔪`—and the map `[π_R]_i` and its two dimensions are the source's, not
depending on the choice of `π`. Linearity makes each graded piece a module over the residue
field, but the instance depends on the hypothesis `IsLinear`, so it cannot be a global
`instance`: the dimensions are defined with a `letI` from `Module.IsTorsionBySet.module`, and
the residue field is written `R ⧸ maximalIdeal R`—definitionally
`IsLocalRing.ResidueField R`—so the instances stay syntactic. Dimensions are `Cardinal`-valued
as in the source, which allows infinite ones; this tranche only meets finite values.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {M : Type*}
  [AddCommGroup M] [Module R M]

namespace FilteredModule

variable (F : FilteredModule R M)

/-- Linearity makes each graded piece torsion for the maximal ideal, hence a residue-field
vector space—condition (a) of the source's Remark 3.16
([Pagano 2022, Rem. 3.16, p.425][Pagano2022]). -/
theorem graded_isTorsionBySet {i : ℕ+} (h : maximalIdeal R • F.filt i ≤ F.filt (i + 1)) :
    Module.IsTorsionBySet R (F.gradedPiece i) (maximalIdeal R : Set R) := by
  intro x a
  obtain ⟨⟨m, hm⟩, rfl⟩ := F.gradedMk_surjective i x
  rw [← map_smul, F.gradedMk_eq_zero_iff]
  exact h (Submodule.smul_mem_smul a.2 hm)

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- Torsion passes to submodules. -/
theorem isTorsionBySet_submodule {V : Type*} [AddCommGroup V] [Module R V] {s : Set R}
    (hT : Module.IsTorsionBySet R V s) (N : Submodule R V) :
    Module.IsTorsionBySet R (↥N) s := by
  intro x a
  refine Subtype.ext ?_
  simpa using hT (x := (x : V)) (a := a)

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- Torsion passes to quotients. -/
theorem isTorsionBySet_quotient {V : Type*} [AddCommGroup V] [Module R V] {s : Set R}
    (hT : Module.IsTorsionBySet R V s) (N : Submodule R V) :
    Module.IsTorsionBySet R (V ⧸ N) s := by
  intro x a
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective N x
  rw [← map_smul, hT (x := v) (a := a), map_zero]

variable {F}

/-- The map `[π_R]_i` multiplication by a uniformizer induces from the `i`-th graded piece to
the one at `ρ_M (i)`, on a strictly linear filtered module
([Pagano 2022, §3.3.1, p.425][Pagano2022]). -/
noncomputable def piGradedMap (h : F.IsStrictlyLinear) {π : R} (hπ : Irreducible π) (i : ℕ+) :
    F.gradedPiece i →ₗ[R] F.gradedPiece (rhoFn h.1 i) :=
  have hπm : π ∈ maximalIdeal R := mem_maximalIdeal π |>.mpr (mem_nonunits_iff.mpr hπ.not_isUnit)
  Submodule.mapQ _ _ ((LinearMap.lsmul R M π).restrict fun x hx =>
      smul_filt_le_filt_rhoFn h.1 i (Submodule.smul_mem_smul hπm hx))
    fun x hx => by
      rw [Submodule.mem_comap] at hx ⊢
      have h1 : π • (x : M) ∈ maximalIdeal R • F.filt (i + 1) :=
        Submodule.smul_mem_smul hπm hx
      have h2 : maximalIdeal R • F.filt (i + 1) ≤ F.filt (rhoFn h.1 i + 1) :=
        le_trans (smul_filt_le_filt_rhoFn h.1 (i + 1))
          (F.antitone_filt (rhoFn_add_one_le h i))
      exact h2 h1

/-- The invariant `f_i (M)`: the residue-field dimension of the `i`-th graded piece of a linear
filtered module ([Pagano 2022, Def. 3.18, p.425][Pagano2022]). -/
noncomputable def fDim (h : F.IsLinear) (i : ℕ+) : Cardinal :=
  letI := (F.graded_isTorsionBySet (h i).1).module
  Module.rank (R ⧸ maximalIdeal R) (F.gradedPiece i)

/-- The **defect** at `i`: the residue-field dimension of the kernel of `[π_R]_i`
([Pagano 2022, Def. 3.18, p.425][Pagano2022]). -/
noncomputable def defect (h : F.IsStrictlyLinear) {π : R} (hπ : Irreducible π) (i : ℕ+) :
    Cardinal :=
  letI := (isTorsionBySet_submodule (F.graded_isTorsionBySet (h.1 i).1)
    (LinearMap.ker (piGradedMap h hπ i))).module
  Module.rank (R ⧸ maximalIdeal R) ↥(LinearMap.ker (piGradedMap h hπ i))

/-- The **codefect** at `i`: the residue-field dimension of the cokernel of `[π_R]_i`
([Pagano 2022, Def. 3.18, p.425][Pagano2022]). -/
noncomputable def codefect (h : F.IsStrictlyLinear) {π : R} (hπ : Irreducible π) (i : ℕ+) :
    Cardinal :=
  letI := (isTorsionBySet_quotient (F.graded_isTorsionBySet (h.1 (rhoFn h.1 i)).1)
    (LinearMap.range (piGradedMap h hπ i))).module
  Module.rank (R ⧸ maximalIdeal R)
    (F.gradedPiece (rhoFn h.1 i) ⧸ LinearMap.range (piGradedMap h hπ i))

end FilteredModule

end Atlas.Knowledge
