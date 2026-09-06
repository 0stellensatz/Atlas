import Mathlib
import Atlas.Knowledge.AbelianizedRestrictionComp
import Atlas.Knowledge.IsArtinRestriction
import Atlas.Knowledge.LocalReciprocityNormNaturality

/-!
# norm naturality of the Artin map

Functoriality of local reciprocity in a finite extension of the base field: for a tower with
`E` finite over `K` and Galois floors `M` over `K` inside `M'` over `E`, the reciprocity
maps of the two base fields intertwine the field norm `N_{E/K}` with the abelianized
restriction of Galois groups — `res ∘ Art_E = Art_K ∘ N_{E/K}`. The same-base companion,
restriction naturality — `Art_K` of a smaller Galois floor is the abelianized restriction of
`Art_K` of a larger — shares the file: it is the compatibility that makes "the" Artin map of
`K` a single object across its floors.

## Main statements

* `artinMap_norm_naturality` — the norm square, base change along `K ⊆ E`.
* `artinMap_restriction_naturality` — the restriction triangle, same base, two floors.

## Implementation notes

The tower is abstract, house idiom: `E` gets its own local-field structure with
`[ValuativeExtension K E]` tying it to `K`, and `E` over `K` is *not* assumed normal —
matching the source's tower, where only the horizontal extensions are. The floors' maps
enter through `Atlas.Knowledge.IsAbelianizedArtinRestriction`. The norm is Mathlib's
`Algebra.norm K : E →* K` on units — big field to small, junk without a finite basis, which
`[FiniteDimensional K E]` carries. No continuous forms are stated: the source's continuous
squares are `DFunLike.congr_fun` transports of the algebraic ones against a `private local
instance` topology on the abelianization that Mathlib does not carry
(`LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldContinuousNaturality.lean:27`).

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
  (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsMixedCharLocalField E]
  [Algebra K E] [ValuativeExtension K E] [FiniteDimensional K E]
  (M : Type*) [Field M] (M' : Type*) [Field M']
  [Algebra K M] [Algebra K M'] [Algebra E M'] [Algebra M M']
  [IsScalarTower K E M'] [IsScalarTower K M M']
  [IsGalois K M] [IsGalois K M'] [IsGalois E M']
  [Algebra M (AlgebraicClosure K)] [IsScalarTower K M (AlgebraicClosure K)]
  [Algebra M' (AlgebraicClosure E)] [IsScalarTower E M' (AlgebraicClosure E)]

/-- The **norm square** of local class field theory: for a finite base change `K ⊆ E` with
Galois floors `M` over `K` inside `M'` over `E`, the reciprocity maps intertwine the field
norm with the abelianized restriction — `res ∘ Art_E = Art_K ∘ N_{E/K}`
([Serre 1979, Chap. XIII, §4, Prop. 10 (a) composed with Prop. 12, p.197][Serre1979];
Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldNormResidueNaturality.lean:561`). -/
theorem artinMap_norm_naturality
    (artK : Kˣ →* Abelianization (M ≃ₐ[K] M))
    (artE : Eˣ →* Abelianization (M' ≃ₐ[E] M'))
    (hK : IsAbelianizedArtinRestriction K M artK)
    (hE : IsAbelianizedArtinRestriction E M' artE) :
    (Abelianization.map
        ((AlgEquiv.restrictNormalHom (F := K) (K₁ := M') M).comp
          (AlgEquiv.restrictScalarsHom (S := E) (A := M') K))).comp artE
      = artK.comp (Units.map (Algebra.norm K : E →* K)) := by
  obtain ⟨φK, hφK, hK⟩ := hK
  obtain ⟨φE, hφE, hE⟩ := hE
  letI : IsScalarTower K M' (AlgebraicClosure E) :=
    IsScalarTower.to₁₃₄ K E M' (AlgebraicClosure E)
  letI : Algebra M (AlgebraicClosure E) :=
    ((algebraMap M' (AlgebraicClosure E)).comp (algebraMap M M')).toAlgebra
  letI : IsScalarTower M M' (AlgebraicClosure E) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower K M (AlgebraicClosure E) :=
    IsScalarTower.to₁₂₄ K M M' (AlgebraicClosure E)
  let e : AlgebraicClosure E ≃ₐ[K] AlgebraicClosure K :=
    IsAlgClosure.equiv K (AlgebraicClosure E) (AlgebraicClosure K)
  ext x
  obtain ⟨σ₀, hσ⟩ := QuotientGroup.mk_surjective (φE x)
  let σ : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E := σ₀
  change Abelianization.map
      ((AlgEquiv.restrictNormalHom (F := K) (K₁ := M') M).comp
        (AlgEquiv.restrictScalarsHom (S := E) (A := M') K)) (artE x) =
    artK (normUnits K E x)
  rw [← hE x σ hσ, Abelianization.map_of]
  have hres : AlgEquiv.restrictNormalHom (F := K) M' (σ.restrictScalars K) =
      (AlgEquiv.restrictNormalHom (F := E) M' σ).restrictScalars K := by
    ext a
    apply (algebraMap M' (AlgebraicClosure E)).injective
    exact (AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) M' a).trans
      (AlgEquiv.restrictNormal_commutes σ M' a).symm
  change Abelianization.of
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := M') M
        ((AlgEquiv.restrictNormalHom (F := E) M' σ).restrictScalars K)) = _
  rw [← hres]
  calc
    _ = Abelianization.of
        (AlgEquiv.restrictNormalHom (F := K) M (σ.restrictScalars K)) :=
      abelianizedRestrictionComp K M M' (AlgebraicClosure E) (σ.restrictScalars K)
    _ = Abelianization.of (AlgEquiv.restrictNormalHom (F := K) M
        (AlgEquiv.autCongr e (σ.restrictScalars K))) :=
      (abelianizedRestriction_autCongr K M (AlgebraicClosure E) (AlgebraicClosure K)
        e (σ.restrictScalars K)).symm
    _ = artK (normUnits K E x) :=
      hK (normUnits K E x) _ (hφK.norm_lift K E hφE e x σ hσ)

section Restriction

variable [Algebra M' (AlgebraicClosure K)] [IsScalarTower K M' (AlgebraicClosure K)]

/-- **Restriction naturality** of the Artin map: over one base `K`, the reciprocity map of a
smaller Galois floor is the abelianized restriction of that of a larger — the compatibility
that glues the floors into one absolute map
([Serre 1979, Chap. XIII, §4, Prop. 12, p.197][Serre1979]; Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/NormResidueNaturality.lean:34`). -/
theorem artinMap_restriction_naturality
    (artM : Kˣ →* Abelianization (M ≃ₐ[K] M))
    (artM' : Kˣ →* Abelianization (M' ≃ₐ[K] M'))
    (hM : IsAbelianizedArtinRestriction K M artM)
    (hM' : IsAbelianizedArtinRestriction K M' artM') :
    (Abelianization.map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M') M)).comp artM'
      = artM := by
  obtain ⟨φ, hφ, hM⟩ := hM
  obtain ⟨ψ, hψ, hM'⟩ := hM'
  have hφψ := hφ.unique hψ
  subst ψ
  ext x
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (φ x)
  change Abelianization.map
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := M') M) (artM' x) = artM x
  rw [← hM' x σ hσ, Abelianization.map_of]
  exact (abelianizedRestrictionComp K M M' (AlgebraicClosure K) σ).trans (hM x σ hσ)

end Restriction

end Atlas.Knowledge
