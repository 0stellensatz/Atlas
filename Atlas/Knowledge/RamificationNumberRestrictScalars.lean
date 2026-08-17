import Mathlib
import Atlas.Knowledge.IntegerIsIntegralClosure
import Atlas.Knowledge.RamificationNumber

/-!
# ramification number under restriction of scalars

For an intermediate valued field `E` of an extension `L` of a mixed-characteristic local field
`K`, the ramification theory of `L` over `E` is the restriction to `H = Gal(L/E)` of the
ramification theory of `L` over `K`: the ramification number `i_H` is `i_G` read on `H`, and
the lower filtration is `H_i = G_i ∩ H`.

## Main statements

* `ramificationNumber_restrictScalars` — `i_H (σ) = i_G (σ)` for an automorphism `σ` of `L`
  fixing `E`.
* `mem_lowerRamificationGroup_restrictScalars_iff` — `σ ∈ H_i ↔ σ ∈ G_i`, pointwise.
* `lowerRamificationGroup_restrictScalars` — `H_i = G_i ∩ H`, the intersection read as a
  `Subgroup.comap` along `AlgEquiv.restrictScalarsHom`.

## Implementation notes

The content of the proposition is that the integral closure of `𝒪[E]` in `L` is the integral
closure of `𝒪[K]` in `L`: `Atlas.Knowledge.integerIsIntegralClosure` makes the two base rings
comparable—`𝒪[E]` is integral over `𝒪[K]`—so integrality over either base transits to the
other, and the two `galRestrict` actions agree through the identification because both act as
`σ` on `L`. The source states the proposition for an arbitrary subgroup `H` of the Galois
group—no normality—and none is assumed here: `E` is any intermediate valued field. Because the
transported theory is the intrinsic ramification theory of `L` over `E`, the E-side
consequences—the eventual triviality of the filtration of `L` over `E` among them—come through
this item without any local-field structure on `E`.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] (L : Type*) [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L]
variable (E : Type*) [Field E] [ValuativeRel E] [Algebra K E] [Algebra E L]
  [IsScalarTower K E L] [ValuativeExtension K E] [Algebra.IsAlgebraic E L]

omit [Algebra.IsAlgebraic K L] in
/-- The integral closure of `𝒪[E]` in `L` is the integral closure of `𝒪[K]` in `L`: the ring
`𝒪[E]` is itself integral over `𝒪[K]` by `Atlas.Knowledge.integerIsIntegralClosure`, so
integrality over either base transits to the other. -/
theorem RamificationNumberRestrictScalars.mem_integralClosure_iff_mem
    [TopologicalSpace K] [IsMixedCharLocalField K] [FiniteDimensional K L] (z : L) :
    z ∈ integralClosure 𝒪[E] L ↔ z ∈ integralClosure 𝒪[K] L := by
  haveI : FiniteDimensional K E := FiniteDimensional.left K E L
  haveI : IsScalarTower 𝒪[K] 𝒪[E] L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply 𝒪[K] K L, IsScalarTower.algebraMap_apply 𝒪[E] E L,
      IsScalarTower.algebraMap_apply K E L]
    norm_cast
  refine ⟨fun hz => (mem_integralClosure_iff _ _).mpr ?_,
    fun hz => (mem_integralClosure_iff _ _).mpr ?_⟩
  · exact isIntegral_trans (R := 𝒪[K]) (A := 𝒪[E]) z ((mem_integralClosure_iff _ _).mp hz)
  · exact IsIntegral.tower_top (A := 𝒪[E]) ((mem_integralClosure_iff _ _).mp hz)

/-- The defining conditions of the two ramification theories coincide, exponent by exponent:
`σ` moves every element of the integral closure of `𝒪[E]` into the `m`-th radical power if and
only if `σ.restrictScalars K` does so over `𝒪[K]`—the two closures are equal, and both actions
are `σ` on `L`. -/
theorem RamificationNumberRestrictScalars.forall_galRestrict_sub_mem_iff
    [TopologicalSpace K] [IsMixedCharLocalField K] [FiniteDimensional K L]
    (σ : L ≃ₐ[E] L) (m : ℕ) :
    (∀ x : integralClosure 𝒪[E] L,
        galRestrict 𝒪[E] E L (integralClosure 𝒪[E] L) σ x - x ∈
          Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[E] L)) ^ m) ↔
      (∀ x : integralClosure 𝒪[K] L,
        galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) (σ.restrictScalars K) x - x ∈
          Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[K] L)) ^ m) := by
  have h : (integralClosure 𝒪[E] L).toSubring = (integralClosure 𝒪[K] L).toSubring :=
    SetLike.ext fun z => by
      rw [Subalgebra.mem_toSubring, Subalgebra.mem_toSubring]
      exact RamificationNumberRestrictScalars.mem_integralClosure_iff_mem K L E z
  let e : integralClosure 𝒪[E] L ≃+* integralClosure 𝒪[K] L := RingEquiv.subringCongr h
  have hcompat : ∀ x : integralClosure 𝒪[E] L,
      e (galRestrict 𝒪[E] E L (integralClosure 𝒪[E] L) σ x) =
        galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) (σ.restrictScalars K) (e x) := by
    intro x
    have hE := algebraMap_galRestrict_apply 𝒪[E] σ x
    have hK := algebraMap_galRestrict_apply 𝒪[K] (σ.restrictScalars K) (e x)
    exact Subtype.ext (hE.trans hK.symm)
  have hsurj : Function.Surjective (e : integralClosure 𝒪[E] L →+* integralClosure 𝒪[K] L) :=
    e.surjective
  have hpow : Ideal.map (e : integralClosure 𝒪[E] L →+* integralClosure 𝒪[K] L)
      (Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[E] L)) ^ m) =
        Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[K] L)) ^ m := by
    rw [Ideal.map_pow, Ideal.map_jacobson_of_surjective hsurj (RingHom.ker_coe_equiv e).le,
      Ideal.map_bot]
  have hiff : ∀ z : integralClosure 𝒪[E] L,
      z ∈ Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[E] L)) ^ m ↔
        e z ∈ Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[K] L)) ^ m := by
    intro z
    rw [← hpow]
    refine ⟨fun hz => Ideal.mem_map_of_mem _ hz, fun hz => ?_⟩
    obtain ⟨w, hw, hwz⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp hz
    rwa [← e.injective hwz]
  constructor
  · intro hall y
    have hx := (hiff _).mp (hall (e.symm y))
    rwa [map_sub, hcompat, e.apply_symm_apply] at hx
  · intro hall x
    have hy := hall (e x)
    rw [← hcompat, ← map_sub] at hy
    exact (hiff _).mpr hy

/-- The ramification number computed over the intermediate field is the ramification number
computed over the base: `i_H (σ) = i_G (σ)` for an automorphism `σ` of `L` fixing `E`
([Serre 1979, Chap. IV, §1, Prop. 2, p.62][Serre1979]). -/
theorem ramificationNumber_restrictScalars [TopologicalSpace K] [IsMixedCharLocalField K]
    [FiniteDimensional K L] (σ : L ≃ₐ[E] L) :
    ramificationNumber E L σ = ramificationNumber K L (σ.restrictScalars K) := by
  unfold ramificationNumber
  exact congrArg (fun s : Set ℕ => sSup (((↑) : ℕ → ℕ∞) '' s)) (Set.ext fun m =>
    RamificationNumberRestrictScalars.forall_galRestrict_sub_mem_iff K L E σ m)

/-- Membership in the lower filtration of `L` over `E` is membership in the filtration of `L`
over `K`: `σ ∈ H_i ↔ σ ∈ G_i` for an automorphism `σ` of `L` fixing `E`
([Serre 1979, Chap. IV, §1, Prop. 2, p.62][Serre1979]). -/
theorem mem_lowerRamificationGroup_restrictScalars_iff [TopologicalSpace K]
    [IsMixedCharLocalField K] [FiniteDimensional K L] {i : ℤ} {σ : L ≃ₐ[E] L} :
    σ ∈ lowerRamificationGroup E L i ↔
      σ.restrictScalars K ∈ lowerRamificationGroup K L i := by
  rw [mem_lowerRamificationGroup_iff, mem_lowerRamificationGroup_iff]
  exact RamificationNumberRestrictScalars.forall_galRestrict_sub_mem_iff K L E σ
    ((i + 1).toNat)

/-- The lower filtration of `L` over `E` is the intersection of `Gal(L/E)` with the filtration
of `L` over `K`—the source's `H_i = G_i ∩ H`, the intersection read as the preimage under
`AlgEquiv.restrictScalarsHom`
([Serre 1979, Chap. IV, §1, Prop. 2, p.62][Serre1979]). -/
theorem lowerRamificationGroup_restrictScalars [TopologicalSpace K] [IsMixedCharLocalField K]
    [FiniteDimensional K L] (i : ℤ) :
    lowerRamificationGroup E L i =
      (lowerRamificationGroup K L i).comap (AlgEquiv.restrictScalarsHom K) := by
  ext σ
  rw [Subgroup.mem_comap, AlgEquiv.restrictScalarsHom_apply]
  exact mem_lowerRamificationGroup_restrictScalars_iff K L E

end Atlas.Knowledge
