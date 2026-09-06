import Mathlib

/-!
# inclusion of Galois groups along an intermediate field

The natural inclusion `Gal(M/E) → Gal(M/K)` for an intermediate field `E` of an
extension `M/K` — restriction of scalars as a group homomorphism, with image
exactly the subgroup fixing `E`, continuous for the two Krull topologies when
`E/K` is finite. The continuity argument pushes a fixing-subgroup
neighbourhood up along the compositum with `E`, which stays finite over `E`.

## Main definitions

* `ofIntermediateFieldInExtension` — the inclusion `Gal(M/E) → Gal(M/K)`.

## Main statements

* `range_ofIntermediateFieldInExtension` — its image is the fixing subgroup of
  `E`; proved.
* `finiteDimensional_extendScalars_sup` — a compositum with a finite
  intermediate field is finite over it; proved.
* `ofIntermediateFieldInExtension_continuous` — the inclusion is continuous
  for the Krull topologies; proved.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u v

/-- **The inclusion** `Gal(M/E) → Gal(M/K)`: restriction of scalars
(Yamaguchi 2026,
`RamificationTheory/GaloisValuation/AbsoluteGalois/InfiniteGaloisCorrespondence.lean:622`). -/
def ofIntermediateFieldInExtension
    {K : Type u} {M : Type v} [Field K] [Field M] [Algebra K M]
    (E : IntermediateField K M) :
    (M ≃ₐ[E] M) →* (M ≃ₐ[K] M) where
  toFun σ := σ.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The inclusion computes as restriction of scalars. -/
@[simp]
theorem ofIntermediateFieldInExtension_apply
    {K : Type u} {M : Type v} [Field K] [Field M] [Algebra K M]
    (E : IntermediateField K M) (σ : M ≃ₐ[E] M) :
    ofIntermediateFieldInExtension E σ = σ.restrictScalars K :=
  rfl

/-- **The image of the inclusion is the fixing subgroup** of `E`
(Yamaguchi 2026,
`RamificationTheory/GaloisValuation/AbsoluteGalois/InfiniteGaloisCorrespondence.lean:639`). -/
theorem range_ofIntermediateFieldInExtension
    {K : Type u} {M : Type v} [Field K] [Field M] [Algebra K M]
    (E : IntermediateField K M) :
    MonoidHom.range (ofIntermediateFieldInExtension E) = E.fixingSubgroup := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change τ x = x
    simpa using τ.commutes ⟨x, hx⟩
  · intro hσ
    refine ⟨IntermediateField.fixingSubgroupEquiv E ⟨σ, hσ⟩, ?_⟩
    apply AlgEquiv.ext
    intro x
    rfl

/-- **A compositum with a finite intermediate field is finite over it**
(Yamaguchi 2026,
`RamificationTheory/GaloisValuation/AbsoluteGalois/InfiniteGaloisCorrespondence.lean:718`). -/
theorem finiteDimensional_extendScalars_sup
    (k : Type u) (M : Type v) [Field k] [Field M] [Algebra k M]
    (E F : IntermediateField k M)
    [FiniteDimensional k E] [FiniteDimensional k F] :
    FiniteDimensional E
      (IntermediateField.extendScalars (F := E) (E := E ⊔ F) le_sup_left) := by
  let EF : IntermediateField k M := E ⊔ F
  let EEF : IntermediateField E M :=
    IntermediateField.extendScalars (F := E) (E := EF) le_sup_left
  haveI : FiniteDimensional k EF := E.finiteDimensional_sup F
  letI : Algebra E EF := (IntermediateField.inclusion le_sup_left).toAlgebra
  letI : Module E EF := Algebra.toModule
  haveI : IsScalarTower k E EF := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    apply Subtype.ext
    change (algebraMap k M) x =
      ((IntermediateField.inclusion le_sup_left) ((algebraMap k E) x) : M)
    rfl
  haveI : Module.Finite E EF := FiniteDimensional.right k E EF
  let eLin : EEF ≃ₗ[E] EF :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := by
        intro x
        ext
        rfl
      right_inv := by
        intro x
        ext
        rfl
      map_add' := by
        intro x y
        ext
        rfl
      map_smul' := by
        intro a x
        ext
        rfl }
  exact Module.Finite.equiv eLin.symm

/-- **The inclusion is continuous** for the two Krull topologies when `E/K` is
finite: a fixing-subgroup neighbourhood is met by the compositum with `E`
(Yamaguchi 2026,
`RamificationTheory/GaloisValuation/AbsoluteGalois/InfiniteGaloisCorrespondence.lean:762`). -/
theorem ofIntermediateFieldInExtension_continuous
    {k : Type u} {M : Type v} [Field k] [Field M] [Algebra k M]
    [IsGalois k M]
    (E : IntermediateField k M) [FiniteDimensional k E] :
    Continuous (ofIntermediateFieldInExtension E) := by
  refine continuous_of_continuousAt_one
    (ofIntermediateFieldInExtension E) ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rcases (krullTopology_mem_nhds_one_iff k M s).1 hs with
    ⟨F, hF, hFs⟩
  let EF : IntermediateField k M := E ⊔ F
  let EEF : IntermediateField E M :=
    IntermediateField.extendScalars (F := E) (E := EF) le_sup_left
  haveI : FiniteDimensional k F := hF
  haveI : FiniteDimensional E EEF :=
    finiteDimensional_extendScalars_sup k M E F
  refine (krullTopology_mem_nhds_one_iff E M
    ((ofIntermediateFieldInExtension E) ⁻¹' s)).2 ?_
  refine ⟨EEF, inferInstance, ?_⟩
  intro σ hσ
  apply hFs
  change ofIntermediateFieldInExtension E σ ∈ F.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  change σ x = x
  have hxEF : x ∈ EF := (show F ≤ EF from le_sup_right) hx
  have hxEEF : x ∈ EEF := by
    change x ∈ EF
    exact hxEF
  exact (IntermediateField.mem_fixingSubgroup_iff EEF σ).1 hσ x hxEEF

end

end Atlas.Knowledge
