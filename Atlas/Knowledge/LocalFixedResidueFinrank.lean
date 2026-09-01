import Mathlib
import Atlas.Knowledge.LocalFixedResidueField

/-!
# residue degree as a literal residue-field degree

The two finite residue-field models of a finite abstract field compared: the
residue-action exact sequence presents the residue field intrinsically inside
the selected residue algebraic closure, while the norm formula uses the
literal residue field of the extension valuation on the fixed field. Through
the full decomposition group and the residue transfer of the exact-sequence
item, the abstract residue degree becomes the degree of the literal residue
extension of the fixed field — the form the valuation datum rewrites with
(#104).

## Main statements

* `localResidueDatum_residueDegree_eq_residueFinrank` — the abstract residue
  degree is `[𝓀[E] : 𝓀[K]]` for the fixed field `E`; proved.

## Implementation notes

The source pins the pullback of the ambient valuation ring to the fixed field
with the Henselian uniqueness of finite-extension valuations; here it is
`Atlas.Knowledge.localAbsoluteValuationSubring_restrict`, so the
comparison needs only `[ValuativeRel E]` and `[ValuativeExtension K E]` where
the source assumes a nonarchimedean local field structure with an extension
witness. The residue square along the integer rings is Mathlib's
`Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap`, riding
`Atlas.Knowledge.IntegerIsIntegralClosure.hasExtension`; the general
residue-transfer equivalences live with
`Atlas.Knowledge.DecompositionResidueExactSequence`, where the source keeps
them beside this comparison.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

noncomputable section

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/-- **The residue degree of a finite abstract field is the literal residue
degree of its fixed field**, for any compatible valuative structure on it
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFinrankTransfer.lean:123`]
[Yamaguchi2026]). -/
theorem localResidueDatum_residueDegree_eq_residueFinrank
    (H : FiniteAbstractField (Field.absoluteGaloisGroup K))
    [FiniteDimensional K
      (abstractFixedField K (AlgebraicClosure K) H.field)]
    [ValuativeRel (abstractFixedField K (AlgebraicClosure K) H.field)]
    [ValuativeExtension K
      (abstractFixedField K (AlgebraicClosure K) H.field)] :
    (H.residueDegree (localResidueDatum K) : ℕ) =
      Module.finrank 𝓀[K]
        𝓀[abstractFixedField K (AlgebraicClosure K) H.field] := by
  let E := abstractFixedField K (AlgebraicClosure K) H.field
  let A := localAbsoluteValuationSubring K
  let C := (ValuativeRel.valuation E).valuationSubring
  let V := (ValuativeRel.valuation K).valuationSubring
  let kK := IsLocalRing.ResidueField V
  let kE := IsLocalRing.ResidueField C
  let k₀ := decompositionResidueField K A
  let kE' := decompositionResidueField E A
  let Omega := selectedResidueField A
  let F := localAbstractFixedResidueIntermediateField K H.field
  let standardResidueAlgebra : Algebra kK kE := by
    change Algebra 𝓀[K] 𝓀[E]
    infer_instance
  letI : Algebra kK kE := standardResidueAlgebra
  letI : Module kK kE := Algebra.toModule
  change (H.residueDegree (localResidueDatum K) : ℕ) =
    Module.finrank kK kE
  have hC : A.comap (algebraMap E (AlgebraicClosure K)) = C := by
    ext z
    exact localAbsoluteValuationSubring_restrict K E z
  have htop : decompositionGroup E A = ⊤ :=
    localAbstractFixedDecompositionGroup_eq_top K H.field
  let eK : kK ≃+* k₀ :=
    localBaseResidueEquivDecompositionResidue K
  let eE : kE ≃+* kE' :=
    residueFieldEquivDecompositionResidueOfEqTop E A C hC htop
  let i : V →+* C := algebraMap V C
  let bar : kE →+* Omega :=
    (algebraMap kE' Omega).comp eE.toRingHom
  have hbar_base (x : kK) :
      bar (algebraMap kK kE x) =
        algebraMap k₀ Omega (eK x) := by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    have hres :
        algebraMap kK kE
            (IsLocalRing.residue V a) =
          IsLocalRing.residue C
            (i a) :=
      Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap
        (ValuativeRel.valuation K) (ValuativeRel.valuation E) a
    rw [hres]
    change algebraMap kE' Omega
        (eE (IsLocalRing.residue C
          (i a))) =
      algebraMap k₀ Omega
        (eK (IsLocalRing.residue V a))
    rw [residueFieldEquivDecompositionResidueOfEqTop_algebraMap]
    have hbase :=
      localBaseResidueEquivDecompositionResidue_algebraMap K a
    change algebraMap k₀ Omega
      (eK (IsLocalRing.residue V a)) = _ at hbase
    rw [hbase]
    congr 1
  letI : Algebra k₀ kE :=
    ((algebraMap kK kE).comp eK.symm.toRingHom).toAlgebra
  let barAlg : kE →ₐ[k₀] Omega :=
    { bar with
      commutes' := fun z => by
        change bar (algebraMap kK kE (eK.symm z)) =
          algebraMap k₀ Omega z
        simpa using hbar_base (eK.symm z) }
  have hF : F = barAlg.fieldRange := by
    change IntermediateField.adjoin k₀
        (Set.range (algebraMap kE' Omega)) = barAlg.fieldRange
    apply le_antisymm
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro y ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := eE.surjective z
      exact ⟨x, rfl⟩
    · rintro y ⟨x, rfl⟩
      apply IntermediateField.subset_adjoin
      exact ⟨eE x, rfl⟩
  let eRange : kE ≃+* barAlg.fieldRange :=
    (AlgEquiv.ofInjectiveField barAlg).toRingEquiv
  letI : Algebra k₀ barAlg.fieldRange := barAlg.fieldRange.algebra
  letI : Module k₀ barAlg.fieldRange := Algebra.toModule
  letI : Algebra k₀ F :=
    localAbstractFixedResidueIntermediateFieldAlgebra K H.field
  letI : SMul k₀ F :=
    localAbstractFixedResidueIntermediateFieldSMul K H.field
  letI : Module k₀ F :=
    localAbstractFixedResidueIntermediateFieldModule K H.field
  let eTop : kE ≃+* F :=
    eRange.trans
      (IntermediateField.equivOfEq hF.symm).toRingEquiv
  have hcomm :
      (algebraMap k₀ F).comp eK.toRingHom =
        eTop.toRingHom.comp (algebraMap kK kE) := by
    ext x
    change algebraMap k₀ Omega (eK x) =
      bar (algebraMap kK kE x)
    exact (hbar_base x).symm
  have hfinrankRaw :
      Module.finrank kK kE = Module.finrank k₀ F :=
    Algebra.finrank_eq_of_equiv_equiv eK eTop hcomm
  exact
    (localResidueDatum_residueDegree_eq_selectedResidueFinrank K H).trans
      hfinrankRaw.symm

end

end Atlas.Knowledge
