import Mathlib
import Atlas.Knowledge.IsFilteredHom

/-!
# filtered automorphism group

The group `Aut_filt` of a filtered module: the linear automorphisms of the carrier that preserve
each filtration step, as a subgroup of `M ≃ₗ[R] M`. It is the group whose orbits on the vectors
of the free models the source's classification runs on—`Atlas.Knowledge.FiltOrd` parametrizes
those orbits by jump sets, and the elementary automorphisms of
`Atlas.Knowledge.ElementaryFilteredAut` are its working members.

## Main definitions

* `FilteredModule.filtAut` — the subgroup of `M ≃ₗ[R] M` preserving every filtration step.

## Main statements

* `FilteredModule.mem_filtAut_iff_map_eq` — membership is the equality `e (filt i) = filt i` for
  every `i`, the form in which the source says "filtered automorphism".
* `FilteredModule.filtAut.weight_smul` — a filtered automorphism preserves weights.

## Implementation notes

Membership is stated as a pointwise `↔` (`x ∈ filt i ↔ e x ∈ filt i`) rather than as an image
equality, which makes the subgroup axioms one-line chains of iffs; the image form is recovered in
`FilteredModule.mem_filtAut_iff_map_eq`. Both directions of the equivalence say exactly that `e`
and `e⁻¹` are filtered morphisms in the sense of `Atlas.Knowledge.IsFilteredHom`.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

namespace FilteredModule

/-- The **filtered automorphism group** `Aut_filt` of a filtered module: linear automorphisms
preserving every filtration step ([Pagano 2022, §3.3.4, p.429][Pagano2022]). -/
def filtAut (F : FilteredModule R M) : Subgroup (M ≃ₗ[R] M) where
  carrier := {e | ∀ i : ℕ+, ∀ x : M, x ∈ F.filt i ↔ e x ∈ F.filt i}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' := by
    intro e f he hf i x
    exact (hf i x).trans (he i (f x))
  inv_mem' := by
    intro e he i x
    have h := (he i (e⁻¹ x)).symm
    rwa [show e (e⁻¹ x) = x from e.apply_symm_apply x] at h

variable {F : FilteredModule R M}

theorem mem_filtAut_iff {e : M ≃ₗ[R] M} :
    e ∈ F.filtAut ↔ ∀ i : ℕ+, ∀ x : M, x ∈ F.filt i ↔ e x ∈ F.filt i :=
  Iff.rfl

/-- Membership in `Aut_filt` as the source states it: each filtration step is carried onto
itself ([Pagano 2022, §3.3.4, p.429][Pagano2022]). -/
theorem mem_filtAut_iff_map_eq {e : M ≃ₗ[R] M} :
    e ∈ F.filtAut ↔ ∀ i : ℕ+, (F.filt i).map (e : M →ₗ[R] M) = F.filt i := by
  constructor
  · intro he i
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact (he i x).mp hx
    · intro x hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      have h := he i (e.symm x)
      rw [e.apply_symm_apply] at h
      exact h.mpr hx
  · intro he i x
    constructor
    · intro hx
      exact he i ▸ Submodule.mem_map_of_mem hx
    · intro hx
      obtain ⟨y, hy, hyx⟩ := he i ▸ hx
      rwa [show y = x from e.injective hyx] at hy

theorem filtAut.isFilteredHom {e : M ≃ₗ[R] M} (he : e ∈ F.filtAut) :
    IsFilteredHom F F (e : M →ₗ[R] M) :=
  fun i x hx => (mem_filtAut_iff.mp he i x).mp hx

/-- An automorphism filtered in both directions preserves every step, hence lies in
`Aut_filt`. -/
theorem mem_filtAut_of_isFilteredHom {e : M ≃ₗ[R] M}
    (h1 : IsFilteredHom F F (e : M →ₗ[R] M)) (h2 : IsFilteredHom F F (e.symm : M →ₗ[R] M)) :
    e ∈ F.filtAut := by
  intro i x
  constructor
  · exact fun hx => h1 i x hx
  · intro hx
    have h3 := h2 i (e x) hx
    simpa using h3

/-- A filtered automorphism preserves weights, which is what makes weight-built invariants
orbit invariants ([Pagano 2022, §3.3.5, p.433][Pagano2022]). -/
theorem filtAut.weight_smul {e : M ≃ₗ[R] M} (he : e ∈ F.filtAut) (x : M) :
    F.weight (e x) = F.weight x := by
  refine le_antisymm ?_ ?_
  · refine le_of_forall_coe_le fun i hi => ?_
    exact F.le_weight_iff.mpr ((mem_filtAut_iff.mp he i x).mpr (F.le_weight_iff.mp hi))
  · refine le_of_forall_coe_le fun i hi => ?_
    exact F.le_weight_iff.mpr ((mem_filtAut_iff.mp he i x).mp (F.le_weight_iff.mp hi))

end FilteredModule

end Atlas.Knowledge
