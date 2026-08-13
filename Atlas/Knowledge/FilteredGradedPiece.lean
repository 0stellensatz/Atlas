import Mathlib
import Atlas.Knowledge.IsFilteredHom

/-!
# graded piece of a filtered module

The functor `F_i` of the source: the quotient of the `i`-th filtration step by the next one,
together with the map a filtered morphism induces between the pieces. The relation between a
filtered morphism and its sequence of graded maps is the subject of the source's §3.2, summed up
in `Atlas.Knowledge.FilteredGradedCriterion`; the two membership-level characterizations at the
end of this file are the form in which those criteria consume the graded maps.

## Main definitions

* `FilteredModule.gradedPiece` — `F_i = filt i / filt (i + 1)`.
* `FilteredModule.gradedMap` — the map `F_i (φ)` induced by a filtered morphism.

## Main statements

* `FilteredModule.gradedMap_id`, `FilteredModule.gradedMap_comp` — functoriality.
* `FilteredModule.gradedMap_injective_iff`, `FilteredModule.gradedMap_surjective_iff` —
  injectivity and surjectivity of `F_i (φ)`, read at the level of members and cosets.

## Implementation notes

The source's `F_{i, j}` for general `i ≤ j` is not carried: this tranche uses only `F_i`, and the
general bigraded functor can graduate in with the material that needs it. The piece is a
quotient of the subtype `↥(filt i)`, so statements about it go through
`Submodule.Quotient.mk` and the two `_iff` lemmas rather than through the raw quotient.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

variable {R : Type*} [CommRing R] {M N P : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

namespace FilteredModule

variable (F : FilteredModule R M) (G : FilteredModule R N) (H : FilteredModule R P)

/-- The `i`-th **graded piece** `F_i` of a filtered module: the `i`-th filtration step modulo
the next one ([Pagano 2022, Def. 3.3, p.420][Pagano2022]). -/
def gradedPiece (i : ℕ+) :=
  ↥(F.filt i) ⧸ (F.filt (i + 1)).comap (F.filt i).subtype

instance (i : ℕ+) : AddCommGroup (F.gradedPiece i) :=
  inferInstanceAs (AddCommGroup (↥(F.filt i) ⧸ (F.filt (i + 1)).comap (F.filt i).subtype))

instance (i : ℕ+) : Module R (F.gradedPiece i) :=
  inferInstanceAs (Module R (↥(F.filt i) ⧸ (F.filt (i + 1)).comap (F.filt i).subtype))

/-- The projection of the `i`-th filtration step onto the `i`-th graded piece. -/
def gradedMk (i : ℕ+) : F.filt i →ₗ[R] F.gradedPiece i :=
  ((F.filt (i + 1)).comap (F.filt i).subtype).mkQ

theorem gradedMk_surjective (i : ℕ+) : Function.Surjective (F.gradedMk i) :=
  Submodule.mkQ_surjective _

theorem gradedMk_eq_zero_iff {i : ℕ+} {x : F.filt i} :
    F.gradedMk i x = 0 ↔ (x : M) ∈ F.filt (i + 1) := by
  change Submodule.Quotient.mk x = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]

theorem gradedMk_eq_iff {i : ℕ+} {x y : F.filt i} :
    F.gradedMk i x = F.gradedMk i y ↔ (x : M) - y ∈ F.filt (i + 1) := by
  change Submodule.Quotient.mk x = Submodule.Quotient.mk y ↔ _
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  rfl

variable {F G H}

/-- The map `F_i (φ)` a filtered morphism induces between the `i`-th graded pieces
([Pagano 2022, Def. 3.3, p.420][Pagano2022]). -/
def gradedMap {f : M →ₗ[R] N} (hf : IsFilteredHom F G f) (i : ℕ+) :
    F.gradedPiece i →ₗ[R] G.gradedPiece i :=
  Submodule.mapQ _ _ (f.restrict fun x hx => hf i x hx)
    fun x hx => by
      rw [Submodule.mem_comap] at hx ⊢
      exact hf (i + 1) _ hx

@[simp]
theorem gradedMap_mk {f : M →ₗ[R] N} (hf : IsFilteredHom F G f) (i : ℕ+) (x : F.filt i) :
    gradedMap hf i (F.gradedMk i x) = G.gradedMk i ⟨f x, hf i x x.2⟩ := by
  change Submodule.mapQ _ _ _ _ (Submodule.Quotient.mk x) = Submodule.Quotient.mk _
  rw [Submodule.mapQ_apply]
  rfl

theorem gradedMap_id (i : ℕ+) : gradedMap (IsFilteredHom.id F) i = LinearMap.id := by
  refine Submodule.linearMap_qext _ ?_
  ext x
  rfl

theorem gradedMap_comp {g : N →ₗ[R] P} {f : M →ₗ[R] N} (hg : IsFilteredHom G H g)
    (hf : IsFilteredHom F G f) (i : ℕ+) :
    gradedMap (hg.comp hf) i = (gradedMap hg i).comp (gradedMap hf i) := by
  refine Submodule.linearMap_qext _ ?_
  ext x
  rfl

/-- `F_i (φ)` is injective exactly when `φ` carries no member of `filt i` outside `filt (i + 1)`
into `filt (i + 1)` ([Pagano 2022, §3.2, p.421][Pagano2022]). -/
theorem gradedMap_injective_iff {f : M →ₗ[R] N} (hf : IsFilteredHom F G f) (i : ℕ+) :
    Function.Injective (gradedMap hf i) ↔
      ∀ x ∈ F.filt i, f x ∈ G.filt (i + 1) → x ∈ F.filt (i + 1) := by
  constructor
  · intro hinj x hx hfx
    have h0 : gradedMap hf i (F.gradedMk i ⟨x, hx⟩) = 0 := by
      rw [gradedMap_mk, G.gradedMk_eq_zero_iff]
      exact hfx
    have h1 : F.gradedMk i ⟨x, hx⟩ = 0 := hinj (by rw [map_zero]; exact h0)
    rwa [F.gradedMk_eq_zero_iff] at h1
  · intro hmem
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨x, rfl⟩ := F.gradedMk_surjective i a
    rw [gradedMap_mk, G.gradedMk_eq_zero_iff] at ha
    rw [F.gradedMk_eq_zero_iff]
    exact hmem x x.2 ha

/-- `F_i (φ)` is surjective exactly when every member of `G.filt i` is a value of `φ` on
`F.filt i` up to `G.filt (i + 1)` ([Pagano 2022, §3.2, p.421][Pagano2022]). -/
theorem gradedMap_surjective_iff {f : M →ₗ[R] N} (hf : IsFilteredHom F G f) (i : ℕ+) :
    Function.Surjective (gradedMap hf i) ↔
      ∀ y ∈ G.filt i, ∃ x ∈ F.filt i, y - f x ∈ G.filt (i + 1) := by
  constructor
  · intro hsurj y hy
    obtain ⟨a, ha⟩ := hsurj (G.gradedMk i ⟨y, hy⟩)
    obtain ⟨x, rfl⟩ := F.gradedMk_surjective i a
    rw [gradedMap_mk] at ha
    refine ⟨x, x.2, ?_⟩
    have h2 : f x - y ∈ G.filt (i + 1) := G.gradedMk_eq_iff.mp ha
    have h3 := (G.filt (i + 1)).neg_mem h2
    rwa [neg_sub] at h3
  · intro hmem a
    obtain ⟨y, rfl⟩ := G.gradedMk_surjective i a
    obtain ⟨x, hx, hyx⟩ := hmem y y.2
    refine ⟨F.gradedMk i ⟨x, hx⟩, ?_⟩
    rw [gradedMap_mk, G.gradedMk_eq_iff]
    change f x - (y : N) ∈ G.filt (i + 1)
    have h3 := (G.filt (i + 1)).neg_mem hyx
    rwa [neg_sub] at h3

end FilteredModule

end Atlas.Knowledge
