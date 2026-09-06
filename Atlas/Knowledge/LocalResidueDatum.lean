import Mathlib
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.LocalAbsoluteValuationSubring
import Atlas.Knowledge.ResidueAbsoluteDegreeIn
import Atlas.Knowledge.ResidueActionIndex
import Atlas.Knowledge.ResidueDatumIn

/-!
# local residue degree datum

The degree datum of a mixed-characteristic local field: the absolute Galois
group acts on the selected residue field of the absolute extension valuation
through the residue-action exact sequence — continuously for the Krull
topologies, because a finite residue subextension is controlled by adjoining
finitely many lifts to `K` — and composing with the intrinsic finite-field
degree map gives a continuous surjection `Γ_K →ₜ* ℤ̂`. This is the opening
datum `d` of the reciprocity engine, instantiated (#104).

## Main definitions

* `localResidueAlgAction` — the continuous residue action of `Γ_K`.
* `localResidueDegree` — the local degree map `Γ_K →ₜ* ℤ̂`.
* `localResidueDatum` — the degree datum of the local field.

## Main statements

* `localResidueAlgAction_surjective` — every residue automorphism lifts;
  proved.
* `localResidueDegree_surjective` — the degree map is surjective; proved.

## Implementation notes

The source works over the separable closure; in mixed characteristic that is
the algebraic closure, so the datum lands directly on
`Field.absoluteGaloisGroup K` — the group whose abelianization
`Atlas.Knowledge.IsLocalReciprocity` is stated over — and the `Separable`
name segment is dropped. The full-decomposition hypothesis the whole-group
action needs is `Atlas.Knowledge.localAbsoluteDecompositionGroup_eq_top`, and
the residue coordinates come from the finite decomposition residue field
through `Atlas.Knowledge.residueAbsoluteDegreeIn`.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

noncomputable section

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/- A fixed representative in the chosen valuation ring of a residue class. -/
private def localSelectedResidueLift
    (x : selectedResidueField (localAbsoluteValuationSubring K)) :
    localAbsoluteValuationSubring K :=
  Classical.choose (IsLocalRing.residue_surjective x)

@[simp]
private theorem localSelectedResidueLift_residue
    (x : selectedResidueField (localAbsoluteValuationSubring K)) :
    IsLocalRing.residue (localAbsoluteValuationSubring K)
        (localSelectedResidueLift K x) = x :=
  Classical.choose_spec (IsLocalRing.residue_surjective x)

/- Reduction from the absolute Galois group to the residue Galois group is
continuous for the Krull topologies: a finite residue subextension is
controlled by adjoining to `K` one lift of each of its finitely many
elements. -/
private theorem localResidueAlgAction_continuous :
    Continuous
      (residueAlgActionOfEqTop K
        (localAbsoluteValuationSubring K)
        (localAbsoluteDecompositionGroup_eq_top K)) := by
  classical
  let A := localAbsoluteValuationSubring K
  let k : Type _ := decompositionResidueField K A
  let Omega : Type _ := selectedResidueField A
  let hA := localAbsoluteDecompositionGroup_eq_top K
  let rho := residueAlgActionOfEqTop K A hA
  refine continuous_of_continuousAt_one rho ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rw [Filter.mem_map]
  rcases (krullTopology_mem_nhds_one_iff k Omega s).1 hs with
    ⟨E, hE, hEs⟩
  letI : FiniteDimensional k E := hE
  letI : Finite E := Module.finite_of_finite k
  letI : Fintype E := Fintype.ofFinite E
  let lifts : Finset (AlgebraicClosure K) :=
    Finset.univ.image (fun x : E =>
      ((localSelectedResidueLift K (x : Omega) : A) : AlgebraicClosure K))
  let F : IntermediateField K (AlgebraicClosure K) :=
    IntermediateField.adjoin K (lifts : Set (AlgebraicClosure K))
  letI : FiniteDimensional K F :=
    IntermediateField.finiteDimensional_adjoin (fun x _hx =>
      Algebra.IsIntegral.isIntegral x)
  refine (krullTopology_mem_nhds_one_iff K (AlgebraicClosure K)
    (rho ⁻¹' s)).2 ?_
  refine ⟨F, inferInstance, ?_⟩
  intro sigma hsigma
  apply hEs
  change rho sigma ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  let y : E := ⟨x, hx⟩
  let a : A := localSelectedResidueLift K (y : Omega)
  have ha_lifts : (a : AlgebraicClosure K) ∈ lifts := by
    apply Finset.mem_image.mpr
    exact ⟨y, Finset.mem_univ y, rfl⟩
  have haF : (a : AlgebraicClosure K) ∈ F :=
    IntermediateField.subset_adjoin (F := K)
      (S := (lifts : Set (AlgebraicClosure K))) ha_lifts
  have hfix : sigma (a : AlgebraicClosure K) = (a : AlgebraicClosure K) :=
    (IntermediateField.mem_fixingSubgroup_iff F sigma).mp hsigma
      (a : AlgebraicClosure K) haF
  change rho sigma (y : Omega) = (y : Omega)
  rw [← localSelectedResidueLift_residue K (y : Omega)]
  change IsLocalRing.residue A
      ((toDecompositionGroupOfEqTop
        K A hA sigma) • a) = IsLocalRing.residue A a
  congr 1
  apply Subtype.ext
  exact hfix

/-- **The continuous residue action** of the absolute Galois group on the
selected residue algebraic closure (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean:369`). -/
def localResidueAlgAction :
    Field.absoluteGaloisGroup K →ₜ*
      (selectedResidueField (localAbsoluteValuationSubring K) ≃ₐ[
        decompositionResidueField K (localAbsoluteValuationSubring K)]
          selectedResidueField (localAbsoluteValuationSubring K)) where
  toMonoidHom :=
    residueAlgActionOfEqTop K
      (localAbsoluteValuationSubring K)
      (localAbsoluteDecompositionGroup_eq_top K)
  continuous_toFun := localResidueAlgAction_continuous K

/-- **Every automorphism of the selected residue extension lifts** to the
absolute Galois group (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean:381`). -/
theorem localResidueAlgAction_surjective :
    Function.Surjective (localResidueAlgAction K) :=
  residueAlgActionOfEqTop_surjective K
    (localAbsoluteValuationSubring K)
    (localAbsoluteDecompositionGroup_eq_top K)

/-- **The local degree map**: the residue Frobenius degree on the absolute
Galois group of a mixed-characteristic local field (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean:390`). -/
def localResidueDegree :
    Field.absoluteGaloisGroup K →ₜ* ProfiniteIntegerMul where
  toMonoidHom :=
    (residueAbsoluteDegreeIn
      (decompositionResidueField K (localAbsoluteValuationSubring K))
      (selectedResidueField
        (localAbsoluteValuationSubring K))).toMonoidHom.comp
        (localResidueAlgAction K).toMonoidHom
  continuous_toFun :=
    (residueAbsoluteDegreeIn
      (decompositionResidueField K (localAbsoluteValuationSubring K))
      (selectedResidueField
        (localAbsoluteValuationSubring K))).continuous_toFun.comp
      (localResidueAlgAction K).continuous_toFun

/-- **The local degree map is surjective** (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean:405`). -/
theorem localResidueDegree_surjective :
    Function.Surjective (localResidueDegree K) := by
  intro z
  obtain ⟨tau, htau⟩ :=
    (residueDatumIn
      (decompositionResidueField K (localAbsoluteValuationSubring K))
      (selectedResidueField
        (localAbsoluteValuationSubring K))).degree_surjective z
  obtain ⟨sigma, hsigma⟩ :=
    localResidueAlgAction_surjective K tau
  refine ⟨sigma, ?_⟩
  change residueAbsoluteDegreeIn
      (decompositionResidueField K (localAbsoluteValuationSubring K))
      (selectedResidueField (localAbsoluteValuationSubring K))
        (localResidueAlgAction K sigma) = z
  rw [hsigma]
  simpa [residueDatumIn] using htau

/-- **The local degree datum**: the abstract class-formation datum
`d : Γ_K →ₜ* ℤ̂` furnished by the residue action of a mixed-characteristic
local field (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean:425`). -/
def localResidueDatum :
    DegreeData (Field.absoluteGaloisGroup K) where
  degree := localResidueDegree K
  degree_surjective := localResidueDegree_surjective K

end

end Atlas.Knowledge
