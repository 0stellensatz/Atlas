import Mathlib

/-!
# continuity of scalar restriction

Restricting the base field of a Galois automorphism is continuous for the Krull topologies.
A basis of a finite intermediate field generates a finite extension of the larger base;
fixing that extension fixes the original basis and hence the original intermediate field.

## Main statements

* `restrictScalarsHom_continuous` — scalar restriction is continuous when the ambient field
  is algebraic over the larger base.
-/

namespace Atlas.Knowledge

/-- Scalar restriction is continuous for the Krull topologies. -/
theorem restrictScalarsHom_continuous
    (K E Ω : Type*) [Field K] [Field E] [Field Ω]
    [Algebra K E] [Algebra K Ω] [Algebra E Ω] [IsScalarTower K E Ω]
    [Algebra.IsAlgebraic E Ω] :
    Continuous (AlgEquiv.restrictScalarsHom (S := E) (A := Ω) K) := by
  classical
  let r := AlgEquiv.restrictScalarsHom (S := E) (A := Ω) K
  refine continuous_of_continuousAt_one r ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rw [Filter.mem_map]
  obtain ⟨L, hL, hLs⟩ := (krullTopology_mem_nhds_one_iff K Ω s).1 hs
  letI : FiniteDimensional K L := hL
  let b := Module.Free.chooseBasis K L
  let S : Set Ω := Set.range (fun i => (b i : Ω))
  let P := IntermediateField.adjoin E S
  letI : Finite S := Set.finite_range _ |>.to_subtype
  letI : FiniteDimensional E P :=
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => Algebra.IsIntegral.isIntegral x)
  refine (krullTopology_mem_nhds_one_iff E Ω (r ⁻¹' s)).2
    ⟨P, inferInstance, ?_⟩
  intro σ hσ
  apply hLs
  change r σ ∈ L.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hfix := (IntermediateField.mem_fixingSubgroup_iff P σ).1 hσ
  have heq : ((r σ).toAlgHom.comp L.val).toLinearMap = L.val.toLinearMap := by
    apply b.ext
    intro i
    exact hfix (b i) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  exact DFunLike.congr_fun heq ⟨x, hx⟩

end Atlas.Knowledge
