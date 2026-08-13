import Mathlib
import Atlas.Knowledge.FilteredRhoMap
import Atlas.Knowledge.IsFilteredHom

/-!
# standard filtered module

The `n`-th standard filtered module `S (n)` for a shift `ρ`: the valuation ring itself, weighted
by `w (x) = ρ^[ord (x)] (n)` where `ord` is the valuation. It is the building block of every
free model of the source's §3.3—`Atlas.Knowledge.FreeFiltered` takes finite products of
these—and it carries the universal property that makes "free" mean something: filtered
morphisms out of `S (n)` into any `F` with `ρ_F ≥ ρ` are exactly the elements of `F.filt n`,
by `x ↦ x • v`. That is the source's representability of the functor `H_n`, in the concrete
form the finite tranche uses.

## Main definitions

* `standardWeight` — the weight map `x ↦ ρ^[ord (x)] (n)`.
* `standardFiltered` — `S (n)`, the filtered module it defines on `R`.

## Main statements

* `standardFiltered_rhoBounded` — the ρ-map of `S (n)` dominates `ρ`, the condition of the
  source's category `C_ρ` that the universal property consumes.
* `isFilteredHom_toSpanSingleton` — for `v ∈ F.filt n`, the map `x ↦ x • v` is a filtered
  morphism `S (n) → F`; together with `eq_toSpanSingleton_of_isFilteredHom`, which says every
  filtered morphism out of `S (n)` arises this way from `φ 1 ∈ F.filt n`, this is the
  representability `Hom_filt (S (n), F) ≃ F.filt n`.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open IsDiscreteValuationRing IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

open Classical in
/-- The weight map of the standard filtered module: `ρ` iterated `ord (x)`-many times from `n`,
and `⊤` at `0` ([Pagano 2022, Def. 3.19, p.426][Pagano2022]). -/
noncomputable def standardWeight (ρ : Shift) (n : ℕ+) (x : R) : WithTop ℕ+ :=
  if x = 0 then ⊤ else (((⇑ρ)^[(addVal R x).toNat] n : ℕ+) : WithTop ℕ+)

theorem standardWeight_le_of_addVal_le {ρ : Shift} {n : ℕ+} {x y : R} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : addVal R x ≤ addVal R y) : standardWeight ρ n x ≤ standardWeight ρ n y := by
  simp only [standardWeight, if_neg hx, if_neg hy, WithTop.coe_le_coe]
  exact ρ.iterate_le_iterate_right n
    (ENat.toNat_le_toNat h fun ht => hy (addVal_eq_top_iff.mp ht))

/-- The `n`-th **standard filtered module** `S (n)` for a shift `ρ`: the ring `R`, filtered by
the weight `ρ^[ord (x)] (n)` ([Pagano 2022, Def. 3.19, p.426][Pagano2022]). -/
noncomputable def standardFiltered (ρ : Shift) (n : ℕ+) : FilteredModule R R :=
  FilteredModule.ofWeight (standardWeight ρ n)
    (fun x => by
      simp only [standardWeight]
      split_ifs with h
      · simp [h]
      · simp [h])
    (fun x y => by
      rcases eq_or_ne (x + y) 0 with h | h
      · simp only [standardWeight, if_pos h]
        exact le_top
      rcases eq_or_ne x 0 with rfl | hx
      · rw [zero_add]
        exact min_le_right _ _
      rcases eq_or_ne y 0 with rfl | hy
      · rw [add_zero]
        exact min_le_left _ _
      rcases le_total (addVal R x) (addVal R y) with hle | hle
      · refine le_trans (min_le_left _ _) (standardWeight_le_of_addVal_le hx h ?_)
        exact le_trans (le_min le_rfl hle) addVal_add
      · refine le_trans (min_le_right _ _) (standardWeight_le_of_addVal_le hy h ?_)
        exact le_trans (le_min hle le_rfl) addVal_add)
    (fun a x => by
      rcases eq_or_ne (a • x) 0 with h | h
      · simp only [standardWeight, if_pos h]
        exact le_top
      have hx : x ≠ 0 := fun h0 => h (by rw [h0, smul_zero])
      refine standardWeight_le_of_addVal_le hx h ?_
      rw [smul_eq_mul, addVal_mul]
      exact le_add_self)

@[simp]
theorem weight_standardFiltered {ρ : Shift} {n : ℕ+} (x : R) :
    (standardFiltered ρ n).weight x = standardWeight ρ n x :=
  FilteredModule.weight_ofWeight x

theorem mem_standardFiltered_filt {ρ : Shift} {n : ℕ+} {x : R} {i : ℕ+} :
    x ∈ (standardFiltered ρ n).filt i ↔ (i : WithTop ℕ+) ≤ standardWeight ρ n x :=
  Iff.rfl

/-- The ρ-map of `S (n)` dominates `ρ`—the one condition of the source's category `C_ρ`
recorded here; its completeness and linearity are not part of this statement
([Pagano 2022, Def. 3.19, p.426][Pagano2022]). -/
theorem standardFiltered_rhoBounded (ρ : Shift) (n : ℕ+) :
    (standardFiltered (R := R) ρ n).RhoBounded ρ := by
  intro i
  rw [Submodule.smul_le]
  intro r hr x hx
  rcases eq_or_ne (r • x) 0 with h | h
  · rw [h]
    exact Submodule.zero_mem _
  have hr0 : r ≠ 0 := fun h0 => h (by rw [h0, zero_smul])
  have hx0 : x ≠ 0 := fun h0 => h (by rw [h0, smul_zero])
  obtain ⟨π, hπ⟩ := exists_irreducible R
  have h1 : (1 : ℕ∞) ≤ addVal R r := by
    rw [← addVal_uniformizer hπ, addVal_le_iff_dvd, ← Ideal.mem_span_singleton,
      ← hπ.maximalIdeal_eq]
    exact hr
  rw [mem_standardFiltered_filt] at hx ⊢
  simp only [standardWeight, if_neg hx0, WithTop.coe_le_coe] at hx
  simp only [standardWeight, if_neg h, WithTop.coe_le_coe]
  have hval : (addVal R x).toNat + 1 ≤ (addVal R (r • x)).toNat := by
    rw [smul_eq_mul, addVal_mul]
    have hxt : addVal R x ≠ ⊤ := fun ht => hx0 (addVal_eq_top_iff.mp ht)
    have hrt : addVal R r ≠ ⊤ := fun ht => hr0 (addVal_eq_top_iff.mp ht)
    have h2 : addVal R x + 1 ≤ addVal R r + addVal R x := by
      rw [add_comm (addVal R r)]
      exact add_le_add le_rfl h1
    have h3 := ENat.toNat_le_toNat h2 (by simp [hxt, hrt])
    rwa [ENat.toNat_add hxt (by simp)] at h3
  calc (ρ i : ℕ+) ≤ ρ ((⇑ρ)^[(addVal R x).toNat] n) := ρ.strict_mono.monotone hx
  _ = (⇑ρ)^[(addVal R x).toNat + 1] n := (Function.iterate_succ_apply' _ _ _).symm
  _ ≤ (⇑ρ)^[(addVal R (r • x)).toNat] n := ρ.iterate_le_iterate_right n hval

section UniversalProperty

variable {M : Type*} [AddCommGroup M] [Module R M] {F : FilteredModule R M} {ρ : Shift} {n : ℕ+}

/-- Powers of a uniformizer push the filtration along the iterates of `ρ`, on any filtered
module of the source's category `C_ρ` ([Pagano 2022, Prop. 3.20, p.426][Pagano2022]). -/
theorem pow_smul_mem_filt_iterate (hF : F.RhoBounded ρ) {π : R} (hπ : Irreducible π) (k : ℕ)
    {j : ℕ+} {z : M} (hz : z ∈ F.filt j) : π ^ k • z ∈ F.filt ((⇑ρ)^[k] j) := by
  induction k with
  | zero => simp only [pow_zero, one_smul, Function.iterate_zero, id]; exact hz
  | succ k ih =>
    have hπm : π ∈ IsLocalRing.maximalIdeal R :=
      IsLocalRing.mem_maximalIdeal π |>.mpr (mem_nonunits_iff.mpr hπ.not_isUnit)
    have h1 : π ^ (k + 1) • z = π • (π ^ k • z) := by
      rw [pow_succ', mul_smul]
    rw [h1, Function.iterate_succ_apply']
    exact hF _ (Submodule.smul_mem_smul hπm ih)

/-- Half of the representability of `H_n`: for `v ∈ F.filt n` the map `x ↦ x • v` is a filtered
morphism `S (n) → F`, whenever `ρ_F ≥ ρ`
([Pagano 2022, Prop. 3.20, p.426][Pagano2022]). -/
theorem isFilteredHom_toSpanSingleton (hF : F.RhoBounded ρ) {v : M} (hv : v ∈ F.filt n) :
    IsFilteredHom (standardFiltered ρ n) F (LinearMap.toSpanSingleton R M v) := by
  intro i x hx
  rcases eq_or_ne x 0 with rfl | hx0
  · simp only [map_zero]
    exact Submodule.zero_mem _
  obtain ⟨π, hπ⟩ := exists_irreducible R
  have hπk : addVal R (π ^ (addVal R x).toNat) = ((addVal R x).toNat : ℕ∞) := by
    rw [(addVal R).map_pow, addVal_uniformizer hπ]
    simp
  have hdvd : π ^ (addVal R x).toNat ∣ x := by
    rw [← addVal_le_iff_dvd, hπk,
      ENat.coe_toNat fun ht => hx0 (addVal_eq_top_iff.mp ht)]
  obtain ⟨y, hy⟩ := hdvd
  have h1 : LinearMap.toSpanSingleton R M v x = π ^ (addVal R x).toNat • (y • v) := by
    rw [LinearMap.toSpanSingleton_apply]
    nth_rewrite 1 [hy]
    rw [mul_smul]
  rw [h1]
  have h2 : π ^ (addVal R x).toNat • (y • v) ∈ F.filt ((⇑ρ)^[(addVal R x).toNat] n) :=
    pow_smul_mem_filt_iterate hF hπ _ ((F.filt n).smul_mem y hv)
  refine F.antitone_filt ?_ h2
  rw [mem_standardFiltered_filt] at hx
  simp only [standardWeight, if_neg hx0, WithTop.coe_le_coe] at hx
  exact hx

/-- The other half of the representability of `H_n`: a filtered morphism `φ : S (n) → F` sends
`1` into `F.filt n` and is `x ↦ x • φ 1`
([Pagano 2022, Prop. 3.20, p.426][Pagano2022]). -/
theorem eq_toSpanSingleton_of_isFilteredHom {φ : R →ₗ[R] M}
    (hφ : IsFilteredHom (standardFiltered ρ n) F φ) :
    φ 1 ∈ F.filt n ∧ φ = LinearMap.toSpanSingleton R M (φ 1) := by
  refine ⟨hφ n 1 ?_, ?_⟩
  · rw [mem_standardFiltered_filt]
    simp [standardWeight]
  · refine LinearMap.ext_ring ?_
    rw [LinearMap.toSpanSingleton_apply_one]

end UniversalProperty

end Atlas.Knowledge
