import Mathlib
import Atlas.Knowledge.AbsoluteAbelianRestriction
import Atlas.Knowledge.AbsoluteAbelianizationEquiv
import Atlas.Knowledge.AbsoluteFiniteQuotientEquiv
import Atlas.Knowledge.IsLocalReciprocity
import Atlas.Knowledge.ProfiniteCompletionLiftCriteria
import Atlas.Knowledge.UnitsFiniteIndexOpen

/-!
# units completion from local existence

The completion isomorphism `K̂ˣ ≃ₜ* G_K^ab` of a reciprocity map, given
the finite local existence theorem: if every open finite-index subgroup
of `Kˣ` is the norm subgroup of a finite abelian subextension, then any
`φ` with `IsLocalReciprocity K φ` lifts along Mathlib's profinite
completion of `Kˣ` to a continuous multiplicative equivalence
compatible with the completion map. This is the second claim of
`Atlas.Knowledge.IsLocalReciprocity` with the existence theorem as an
explicit hypothesis: the claim reduces to that theorem, and its own
`sorry` stands until the theorem is proved (#104).

## Main definitions

* `absoluteGaloisAbelianizationProfinite` — `G_K^ab` bundled as a
  profinite group.

## Main statements

* `cofinal_of_normSubgroup_surjective` — under local existence, every
  finite-index normal subgroup of `Kˣ` is the preimage of an open
  normal subgroup of `G_K^ab`; proved.
* `IsLocalReciprocity.unitsCompletion_continuousMulEquiv_of_normSubgroup_surjective`
  — the completion isomorphism, given local existence; proved.
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
not discharged here: a discharge resting on a recorded claim would
carry `sorryAx`, so the hypothesis stays explicit and the reduction is
the item. Source: the completion isomorphism on the source's own
open-finite-index completion (`ProfiniteLocalReciprocity.lean:115`,
from its `:98` and `:107`) and on the standard model (`:257`); the
cofinality theorem (`FiniteAbelianQuotientKernels.lean:180`) is the
layer's `cofinal_of_normSubgroup_surjective` with the existence theorem
as a hypothesis where the source consumes it proved, and concluding the
equality of subgroups its proof establishes where the source's
statement keeps only `≤`; the criteria consume the `≤` form. The
bundling `absoluteGaloisAbelianizationProfinite` is the source's
`standardLocalAbsoluteAbelianProfinite`
(`ProfiniteLocalReciprocity.lean:64`), which
`Atlas.Knowledge.AbsoluteFiniteArtinLimit` still spells inline.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer
  New York, 1979.
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

/-- **Under local existence, every finite-index normal subgroup of `Kˣ`
is the preimage of an open normal subgroup of `G_K^ab`**: the
restriction kernel of the finite abelian subextension whose norm
subgroup it is ([Yamaguchi 2026,
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

/-- **The reciprocity map is an isomorphism after profinite completion,
given local existence**: `K̂ˣ ≃ₜ* G_K^ab` compatible with the
completion map, for any `φ` satisfying `IsLocalReciprocity K φ`, once
every open finite-index subgroup of `Kˣ` is the norm subgroup of a
finite abelian subextension
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

end

end Atlas.Knowledge
