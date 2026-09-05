import Mathlib
import Atlas.Knowledge.AbsoluteAbelianRestriction
import Atlas.Knowledge.AbsoluteAbelianizationEquiv
import Atlas.Knowledge.AbsoluteFiniteQuotientEquiv
import Atlas.Knowledge.AbstractFixedField
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.IntermediateFieldUnitsFixedSubgroup
import Atlas.Knowledge.IsLocalReciprocity
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.LocalNormSubgroupExistence
import Atlas.Knowledge.NormSubgroupOrderEmbedding
import Atlas.Knowledge.NormSubgroupSurjectivity
import Atlas.Knowledge.NormTopology
import Atlas.Knowledge.ProfiniteCompletionLiftCriteria
import Atlas.Knowledge.ResidueDatumIn
import Atlas.Knowledge.SeparableFixedFieldNorm
import Atlas.Knowledge.UnitsFiniteIndexOpen

/-!
# units completion from local existence

The completion isomorphism `K̂ˣ ≃ₜ* G_K^ab` of a reciprocity map: any
`φ` with `IsLocalReciprocity K φ` lifts along Mathlib's profinite
completion of `Kˣ` to a continuous multiplicative equivalence
compatible with the completion map — first given the finite local
existence theorem as an explicit hypothesis, then outright, the theorem
being proved here: every open finite-index subgroup of `Kˣ` is the norm
subgroup of a finite abelian subextension, by the abstract
classification's surjectivity once every finite-index subgroup is
norm-open, which the Lubin–Tate existence input supplies. This is the
second claim of `Atlas.Knowledge.IsLocalReciprocity`, discharged
(#104).

## Main definitions

* `absoluteGaloisAbelianizationProfinite` — `G_K^ab` bundled as a
  profinite group.

## Main statements

* `cofinal_of_normSubgroup_surjective` — under local existence, every
  finite-index normal subgroup of `Kˣ` is the preimage of an open
  normal subgroup of `G_K^ab`; proved.
* `IsLocalReciprocity.unitsCompletion_continuousMulEquiv_of_normSubgroup_surjective`
  — the completion isomorphism, given local existence; proved.
* `finiteIndexSubgroup_isNormOpen` — every finite-index subgroup of
  `Kˣ` is open for the abstract norm topology; proved.
* `exists_finiteAbelian_localNormSubgroup_eq` — the finite local
  existence theorem: every open finite-index subgroup of `Kˣ` is the
  norm subgroup of a finite abelian subextension of the algebraic
  closure; proved.
* `IsLocalReciprocity.unitsCompletion_continuousMulEquiv` — the
  completion isomorphism `K̂ˣ ≅ G_K^ab`; proved.
* `IsLocalReciprocity.unitsCompletion_continuousMulEquiv_unique` — the
  isomorphism is pinned by its compatibility with the completion map;
  proved.

## Implementation notes

The existence hypothesis is stated in the shape of the `normKernel`
field — a finite Galois subextension of the algebraic closure with
commuting automorphisms and the range of its unit norm — so the field's
identity rewrites without a bridge, and the openness it asks for is the
source's own quantification (its existence theorem,
`Finite/Existence/CharacteristicZero.lean:26`, ranges over *open*
finite-index subgroups); `Atlas.Knowledge.unitsFiniteIndexOpen`
supplies that openness for every finite-index subgroup, which is where
the identification of Mathlib's completion against all finite-index
normal subgroups with the classical one against the open ones — the
caveat carried on #47 — is consumed; the `IsOpen` premise is therefore
logically redundant, and it is kept deliberately, so that the bridge is
consumed where the caveat expects it rather than silently dropped. The
open normal subgroup is the restriction kernel of the supplied field,
and its preimage is the norm subgroup by the field's `normKernel` and
the #216 dictionary; the completion criteria are those of
`Atlas.Knowledge.ProfiniteCompletionLiftCriteria`. The claim itself is
discharged here, not in `Atlas.Knowledge.IsLocalReciprocity` where it
was recorded: its proof is the reduction applied to the existence
theorem, and the reduction imports the predicate's item, so the
statement moved here unchanged. The existence theorem is
`exists_finiteAbelian_localNormSubgroup_eq`:
`Atlas.Knowledge.LocalNormSubgroupExistence` puts a finite Galois norm
subgroup inside every open finite-index subgroup,
`Atlas.Knowledge.NormSubgroupSurjectivity`'s witness makes every
finite-index subgroup norm-open (`finiteIndexSubgroup_isNormOpen`), its
surjectivity closer at the algebraic closure hands each open
finite-index subgroup a finite abelian subextension with that norm
subgroup, and `Atlas.Knowledge.NormSubgroupOrderEmbedding`'s transports
read the represented fixed field as a finite abelian intermediate field
of the algebraic closure with the hypothesis's shape; the axioms of the
discharged claim are standard, the chain's one recorded input,
`normIndexAbelian`, having been discharged. Source: the completion
isomorphism on the source's own open-finite-index completion
(`ProfiniteLocalReciprocity.lean:115`, from its `:98` and `:107`) and
on the standard model (`:257`); the cofinality theorem
(`FiniteAbelianQuotientKernels.lean:180`) is the layer's
`cofinal_of_normSubgroup_surjective` with the existence theorem as a
hypothesis where the source consumes it proved, and concluding the
equality of subgroups its proof establishes where the source's
statement keeps only `≤`; the criteria consume the `≤` form. The
bundling `absoluteGaloisAbelianizationProfinite` is the source's
`standardLocalAbsoluteAbelianProfinite`
(`ProfiniteLocalReciprocity.lean:64`), which
`Atlas.Knowledge.AbsoluteFiniteArtinLimit` still spells inline.
`Atlas.Knowledge.AbsoluteAbelianizationEquiv` is imported for the
profinite-group instances that bundling needs, which no spelled name
here carries.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer
  New York, 1979.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic
  local fields*, J. London Math. Soc. **112** (2025), e70402.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

open CategoryTheory ProfiniteGrp ProfiniteGrp.ProfiniteCompletion

noncomputable section

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/-- The abelianized absolute Galois group bundled as a profinite group,
through the compactness and total-disconnectedness instances of
`Atlas.Knowledge.AbsoluteAbelianizationEquiv` ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/ProfiniteLocalReciprocity.lean:64`]
[Yamaguchi2026]). -/
abbrev absoluteGaloisAbelianizationProfinite : ProfiniteGrp :=
  ProfiniteGrp.of (Field.absoluteGaloisGroupAbelianization K)

variable {K}

/-- The lift of a reciprocity homomorphism agrees with it on the
completion map ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/ProfiniteLocalReciprocity.lean:79`]
[Yamaguchi2026]). -/
theorem reciprocityLift_etaFn (φ : Kˣ →* Field.absoluteGaloisGroupAbelianization K) (u : Kˣ) :
    (lift (P := absoluteGaloisAbelianizationProfinite K) (GrpCat.ofHom φ)).hom
        (etaFn (GrpCat.of Kˣ) u) = φ u :=
  ConcreteCategory.congr_hom (lift_eta (P := absoluteGaloisAbelianizationProfinite K)
    (GrpCat.ofHom φ)) u

/-- **Under local existence, finite-index normal subgroups of `Kˣ` come from `G_K^ab`**:
each is the preimage of an open normal subgroup, the restriction kernel
of the finite abelian subextension whose norm subgroup it is
([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/FiniteAbelianQuotientKernels.lean:180`]
[Yamaguchi2026]). -/
theorem cofinal_of_normSubgroup_surjective (φ : Kˣ →* Field.absoluteGaloisGroupAbelianization K)
    (hφ : IsLocalReciprocity K φ)
    (hexist : ∀ H : Subgroup Kˣ, H.FiniteIndex → IsOpen (H : Set Kˣ) →
      ∃ (L : IntermediateField K (AlgebraicClosure K)) (_ : FiniteDimensional K L)
        (_ : IsGalois K L), (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) ∧
          MonoidHom.range (Units.map (Algebra.norm K (S := ↥L))) = H) :
    ∀ H : FiniteIndexNormalSubgroup (GrpCat.of Kˣ),
      ∃ N : OpenNormalSubgroup (absoluteGaloisAbelianizationProfinite K),
        preimage (GrpCat.ofHom φ) N = H := by
  intro H
  haveI : H.toSubgroup.FiniteIndex := H.isFiniteIndex'
  obtain ⟨L, _, _, hcomm, hL⟩ :=
    hexist H.toSubgroup inferInstance (unitsFiniteIndexOpen K H.toSubgroup inferInstance)
  letI : IsAbelianGalois K ↥L := { is_comm := ⟨hcomm⟩ }
  refine ⟨absoluteAbelianRestrictionKernel K L, ?_⟩
  apply FiniteIndexNormalSubgroup.toSubgroup_injective
  change Subgroup.comap φ (absoluteAbelianRestrictionKernel K L).toSubgroup = H.toSubgroup
  rw [← hL, ← hφ.normKernel L hcomm]
  congr 1
  rw [← absoluteFiniteQuotientPreimage_restrictionKernel K L,
    absoluteFiniteQuotientPreimage_map_eq]

/-- **The reciprocity map is an isomorphism after profinite completion, given local existence**:
`K̂ˣ ≃ₜ* G_K^ab` compatible with the completion map, for any `φ`
satisfying `IsLocalReciprocity K φ`, once every open finite-index
subgroup of `Kˣ` is the norm subgroup of a finite abelian subextension
([Serre 1979, Chap. XIII, §4, pp.197–198][Serre1979]; [Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/ProfiniteLocalReciprocity.lean:115`]
[Yamaguchi2026]). -/
theorem IsLocalReciprocity.unitsCompletion_continuousMulEquiv_of_normSubgroup_surjective
    {φ : Kˣ →* Field.absoluteGaloisGroupAbelianization K} (hφ : IsLocalReciprocity K φ)
    (hexist : ∀ H : Subgroup Kˣ, H.FiniteIndex → IsOpen (H : Set Kˣ) →
      ∃ (L : IntermediateField K (AlgebraicClosure K)) (_ : FiniteDimensional K L)
        (_ : IsGalois K L), (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) ∧
          MonoidHom.range (Units.map (Algebra.norm K (S := ↥L))) = H) :
    ∃ e : completion (GrpCat.of Kˣ) ≃ₜ* Field.absoluteGaloisGroupAbelianization K,
      ∀ u : Kˣ, e (etaFn (GrpCat.of Kˣ) u) = φ u :=
  ⟨ProfiniteCompletion.liftContinuousMulEquiv (P := absoluteGaloisAbelianizationProfinite K)
      (GrpCat.ofHom φ)
      (ProfiniteCompletion.lift_injective_of_cofinal _ fun H =>
        (cofinal_of_normSubgroup_surjective φ hφ hexist H).imp fun _ h => le_of_eq h)
      (ProfiniteCompletion.lift_surjective_of_denseRange _ hφ.denseRange),
    fun u => reciprocityLift_etaFn φ u⟩

/-- The completion isomorphism is unique: two continuous multiplicative
equivalences agreeing with `φ` on the completion map agree, the
completion map having dense range and the target being Hausdorff. -/
theorem IsLocalReciprocity.unitsCompletion_continuousMulEquiv_unique
    {φ : Kˣ →* Field.absoluteGaloisGroupAbelianization K}
    (e₁ e₂ : completion (GrpCat.of Kˣ) ≃ₜ* Field.absoluteGaloisGroupAbelianization K)
    (h₁ : ∀ u : Kˣ, e₁ (etaFn (GrpCat.of Kˣ) u) = φ u)
    (h₂ : ∀ u : Kˣ, e₂ (etaFn (GrpCat.of Kˣ) u) = φ u) : e₁ = e₂ :=
  DFunLike.ext e₁ e₂ (congrFun ((ProfiniteGrp.ProfiniteCompletion.denseRange
    (G := GrpCat.of Kˣ)).equalizer e₁.continuous e₂.continuous
    (funext fun u => (h₁ u).trans (h₂ u).symm)))

variable (K) in
/-- **Every finite-index subgroup of `Kˣ` is open for the abstract norm topology**
at the algebraic closure: it contains a finite Galois norm subgroup,
which witnesses norm-openness ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/KummerNormOpen.lean:83`][Yamaguchi2026]). -/
theorem finiteIndexSubgroup_isNormOpen (H : Subgroup Kˣ) [H.FiniteIndex] :
    IsNormOpen (galoisAmbientUnitsRep K (AlgebraicClosure K))
      (closedFixingSubgroup (⊥ : IntermediateField K (AlgebraicClosure K)))
      ((H.toAddSubgroup.map
        (baseUnitsEquivGaloisAmbientFixed K (AlgebraicClosure K)).toAddMonoidHom :
        AddSubgroup (ambientFixedAddSubgroup (galoisAmbientUnitsRep K (AlgebraicClosure K))
          (closedFixingSubgroup (⊥ : IntermediateField K (AlgebraicClosure K))))) : Set _) := by
  obtain ⟨E, _, _, hE⟩ :=
    exists_finiteGalois_localNormSubgroup_le K H
  exact finiteIndexSubgroup_isNormOpen_of_normSubgroup_le K (AlgebraicClosure K) E H hE

variable (K) in
/-- **The finite local existence theorem**, in the shape the completion
comparison consumes: every open finite-index subgroup of `Kˣ` is the
norm subgroup of a finite abelian subextension of the algebraic closure
— the abstract classification's surjectivity, every finite-index
subgroup being norm-open, with the represented fixed field read as a
concrete finite abelian intermediate field ([Serre 1979, Chap. XIII,
§4, Thm. 2, p.197][Serre1979]; [Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/CharacteristicZero.lean:26`][Yamaguchi2026]).
-/
theorem exists_finiteAbelian_localNormSubgroup_eq (H : Subgroup Kˣ) (hfi : H.FiniteIndex)
    (hH : IsOpen (H : Set Kˣ)) :
    ∃ (L : IntermediateField K (AlgebraicClosure K)) (_ : FiniteDimensional K L)
      (_ : IsGalois K L), (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) ∧
        MonoidHom.range (Units.map (Algebra.norm K (S := ↥L))) = H := by
  haveI := hfi
  have hsurj := localFiniteAbelianNormSubgroupMap_surjective_of_normOpen K
    (fun H' _ => finiteIndexSubgroup_isNormOpen K H')
  obtain ⟨L, hL⟩ := hsurj ⟨H, hH, hfi⟩
  let Lf : IntermediateField K (AlgebraicClosure K) :=
    abstractFixedField K (AlgebraicClosure K) L.field
  haveI : IsAbelianGalois K Lf :=
    finiteAbelianSubextension_fixedField_isAbelianGalois K (AlgebraicClosure K) L
  have hLfin := finiteAbelianSubextension_finite_over_absoluteBase K (AlgebraicClosure K) L
  haveI : FiniteDimensional K Lf :=
    abstractFixedField_finiteDimensional K (AlgebraicClosure K) L.field hLfin
  refine ⟨Lf, inferInstance, inferInstance, fun σ τ => IsMulCommutative.is_comm.comm σ τ, ?_⟩
  exact congrArg OpenFiniteIndexSubgroup.subgroup hL

/-- The reciprocity map is an isomorphism after profinite completion:
`K̂ˣ ≅ G_K^ab`, the completion taken against all finite-index normal
subgroups — which are all open, `K` being of mixed characteristic. The
second claim of `Atlas.Knowledge.IsLocalReciprocity`, recorded there
ahead of its proof and discharged here by the reduction and the
existence theorem ([Serre 1979, Chap. XIII, §4, pp.197–198][Serre1979];
[Hyeon 2025, §3, p.10][Hyeon2025]; [Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/ProfiniteLocalReciprocity.lean:257`][Yamaguchi2026]).
-/
theorem IsLocalReciprocity.unitsCompletion_continuousMulEquiv
    {φ : Kˣ →* Field.absoluteGaloisGroupAbelianization K} (hφ : IsLocalReciprocity K φ) :
    ∃ e : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of Kˣ) ≃ₜ*
        Field.absoluteGaloisGroupAbelianization K,
      ∀ u : Kˣ, e (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of Kˣ) u) = φ u :=
  IsLocalReciprocity.unitsCompletion_continuousMulEquiv_of_normSubgroup_surjective hφ
    (fun H hfi hH => exists_finiteAbelian_localNormSubgroup_eq K H hfi hH)

end

end Atlas.Knowledge
