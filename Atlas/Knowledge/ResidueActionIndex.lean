import Mathlib
import Atlas.Knowledge.DecompositionResidueExactSequence
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.ResidueAbsoluteDegreeIn
import Atlas.Knowledge.ResidueDatumIn

/-!
# residue-action image indices

The residue-action exact sequence acts through a chosen extension valuation's
decomposition group; when that group is the whole Galois group, the action is
a surjection defined on all of it. Separately, the finite-subgroup coordinate
comparison: a subgroup whose residue-action image is the fixing subgroup of a
finite residue subextension has degree image of index the residue field
degree. These are the two group-theoretic reductions behind the local degree
map of the reciprocity engine's instantiation (#104).

## Main definitions

* `residueAlgActionOfEqTop` — the residue action on the whole Galois group,
  under full decomposition group.

## Main statements

* `residueAlgActionOfEqTop_surjective` — the whole-group residue action is
  surjective; proved.
* `residueDegreeImage_index_eq_finrank_of_map_eq_fixingSubgroup` — a subgroup
  with residue-action image a finite fixing subgroup has degree image of
  index the residue degree; proved.

## Implementation notes

The full-decomposition hypothesis is carried as an explicit equality
`decompositionGroup K A = ⊤` rather than an instance, matching the source; it
is discharged for a local field's extension valuation with the local datum,
not here. The ambient Galois field stays generic for the same reason the
source keeps it so: the source instantiates at the separable closure, which
over an imperfect local field is not the algebraic closure — the purely
inseparable residue comparison of
`Atlas.Knowledge.ResidueOfAlgebraicallyClosed` is the bridge that reading
uses — while Atlas's mixed-characteristic consumer takes the algebraic
closure itself. The index comparison reads
`Atlas.Knowledge.residueDatumIn_fieldImage_index_closedFixingSubgroup`
through `Atlas.Knowledge.DegreeData.fieldImage_eq_map`, whose embedded
closure instances make any local replication here dead weight, so the
source's scope instances are not replicated.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u v

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
  [IsGalois K L]

/-- View every ambient Galois automorphism as a decomposition-group element
when the chosen extension valuation has full decomposition group
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ResidueActionIndex.lean:36`]
[Yamaguchi2026]). -/
def toDecompositionGroupOfEqTop
    (A : ValuationSubring L)
    (hA : decompositionGroup K A = ⊤) :
    (L ≃ₐ[K] L) →* decompositionGroup K A where
  toFun sigma := ⟨sigma, by rw [hA]; exact Subgroup.mem_top sigma⟩
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

omit [IsGalois K L] in
/-- The decomposition-group view forgets back to the automorphism
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ResidueActionIndex.lean:46`]
[Yamaguchi2026]). -/
@[simp] theorem toDecompositionGroupOfEqTop_coe
    (A : ValuationSubring L)
    (hA : decompositionGroup K A = ⊤)
    (sigma : L ≃ₐ[K] L) :
    (toDecompositionGroupOfEqTop K A hA sigma : L ≃ₐ[K] L) = sigma :=
  rfl

/-- **The residue action on the whole Galois group** when the chosen
extension valuation has full decomposition group ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ResidueActionIndex.lean:55`]
[Yamaguchi2026]). -/
def residueAlgActionOfEqTop
    (A : ValuationSubring L)
    (hA : decompositionGroup K A = ⊤) :
    (L ≃ₐ[K] L) →*
      (selectedResidueField A ≃ₐ[decompositionResidueField K A]
        selectedResidueField A) :=
  (decompositionGroupResidueAction (K := K) A).comp
    (toDecompositionGroupOfEqTop K A hA)

/-- **The whole-group residue action is surjective** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ResidueActionIndex.lean:65`]
[Yamaguchi2026]). -/
theorem residueAlgActionOfEqTop_surjective
    (A : ValuationSubring L)
    (hA : decompositionGroup K A = ⊤) :
    Function.Surjective (residueAlgActionOfEqTop K A hA) := by
  intro tau
  obtain ⟨sigma, hsigma⟩ :=
    decompositionGroupResidueAction_surjective (K := K) A tau
  refine ⟨(sigma : L ≃ₐ[K] L), ?_⟩
  have heq :
      toDecompositionGroupOfEqTop K A hA (sigma : L ≃ₐ[K] L) = sigma := by
    ext
    rfl
  simpa [residueAlgActionOfEqTop, heq] using hsigma

section FiniteImageIndex

variable (k : Type u) [Field k] [Fintype k]
variable (Omega : Type v) [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]

/-- **A subgroup whose residue-action image is a finite fixing subgroup has
degree image of index the residue degree** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ResidueActionIndex.lean:88`]
[Yamaguchi2026]). -/
theorem residueDegreeImage_index_eq_finrank_of_map_eq_fixingSubgroup
    {G : Type*} [Group G]
    (rho : G →* (Omega ≃ₐ[k] Omega))
    (H : Subgroup G)
    (E : FiniteGaloisIntermediateField k Omega)
    (himage : H.map rho = E.toIntermediateField.fixingSubgroup) :
    (H.map ((residueAbsoluteDegreeIn k Omega).toMonoidHom.comp rho)).index =
      Module.finrank k E := by
  rw [← Subgroup.map_map, himage]
  have h := residueDatumIn_fieldImage_index_closedFixingSubgroup k Omega E
  rw [(residueDatumIn k Omega).fieldImage_eq_map] at h
  simpa [residueDatumIn, closedFixingSubgroup] using h

end FiniteImageIndex

end

end Atlas.Knowledge
