import Mathlib
import Atlas.Knowledge.IsArtinRestriction
import Atlas.Knowledge.RestrictScalarsHomRangeEqKer

/-!
# abelianized Galois transfer

The transfer (Verlagerung) between abelianized Galois groups of a tower: for fields
`K ⊆ E ⊆ M` with `M` finite over `K`, the group-theoretic transfer of
`Gal (M/K)` into its finite-index subgroup `Gal (M/E)` — the subgroup entering as the range
of `AlgEquiv.restrictScalarsHom`, `Atlas.Knowledge.RestrictScalarsHomRangeEqKer` — descends
to `Gal (M/K)^ab →* Gal (M/E)^ab`. This is the arrow of the transfer square of local class
field theory: against reciprocity maps of the two base fields it completes the commuting
square with the inclusion `Kˣ ⊆ Eˣ`, which is the recorded claim.

## Main definitions

* `abelianizedGaloisTransfer` — the transfer `Gal (M/K)^ab →* Gal (M/E)^ab`.

## Main statements

* `artinMap_transfer_naturality` — the transfer square: `Ver ∘ Art_K = Art_E ∘ (Kˣ ↪ Eˣ)`,
  recorded ahead of its proof.

## Implementation notes

The definition is pure finite group theory atop Mathlib's `MonoidHom.transfer` — no
normality of `E` over `K` and no valuative structure enters, and it lands sorry-free now,
independent of the reciprocity characterization; finite index comes from
`[FiniteDimensional K M]` through finiteness of the Galois group. The packaging composes the
inverse of `MonoidHom.ofInjective` *into* the transferred homomorphism where the read
repository post-composes an `abelianizationCongr` after transferring `Abelianization.of`
(`AbstractClassFieldTheory/Reciprocity/Construction/MainTransfer.lean:172`); the two agree
mathematically but not syntactically, which the eventual discharge of the square will have to
cross. The square itself takes both floors' maps through
`Atlas.Knowledge.IsAbelianizedArtinRestriction`, each over its own local-field structure,
`[ValuativeExtension K E]` tying the two; it is jointly owned with the Verlagerung tranche
(#9), and this file contributes the arrow either way.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] (E : Type*) [Field E] (M : Type*) [Field M]
  [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]
  [FiniteDimensional K M]

/-- The **abelianized Galois transfer** of a tower `K ⊆ E ⊆ M`: the group-theoretic
transfer of `Gal (M/K)` into the finite-index subgroup fixing `E`, descended to the
abelianizations, `Gal (M/K)^ab →* Gal (M/E)^ab`
([Serre 1979, Chap. XIII, §4, Prop. 10 (b), p.197][Serre1979];
[Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/MainTransfer.lean:172`][Yamaguchi2026]). -/
noncomputable def abelianizedGaloisTransfer :
    Abelianization (M ≃ₐ[K] M) →* Abelianization (M ≃ₐ[E] M) :=
  letI : ((AlgEquiv.restrictScalarsHom (S := E) (A := M) K).range).FiniteIndex :=
    Subgroup.finiteIndex_of_finite
  Abelianization.lift
    (MonoidHom.transfer
      ((Abelianization.of).comp
        ((MonoidHom.ofInjective
          (f := AlgEquiv.restrictScalarsHom (S := E) (A := M) K)
          (AlgEquiv.restrictScalars_injective K)).symm.toMonoidHom)))

section Square

variable [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
  [ValuativeRel E] [TopologicalSpace E] [IsMixedCharLocalField E] [ValuativeExtension K E]
  [IsGalois K M] [IsGalois E M]
  [Algebra M (AlgebraicClosure K)] [IsScalarTower K M (AlgebraicClosure K)]
  [Algebra M (AlgebraicClosure E)] [IsScalarTower E M (AlgebraicClosure E)]

/-- The **transfer square** of local class field theory: reciprocity maps of the two base
fields of a tower `K ⊆ E ⊆ M` intertwine the transfer with the inclusion `Kˣ ⊆ Eˣ` —
`Ver ∘ Art_K = Art_E ∘ ι`. Claim recorded ahead of its proof
([Serre 1979, Chap. XIII, §4, Prop. 10 (b), p.197][Serre1979];
[Yamaguchi 2026,
`Finite/LocalReciprocity/FixedFieldNormResidueNaturality.lean:720`][Yamaguchi2026]). -/
theorem artinMap_transfer_naturality
    (artK : Kˣ →* Abelianization (M ≃ₐ[K] M))
    (artE : Eˣ →* Abelianization (M ≃ₐ[E] M))
    (hK : IsAbelianizedArtinRestriction K M artK)
    (hE : IsAbelianizedArtinRestriction E M artE) :
    (abelianizedGaloisTransfer K E M).comp artK
      = artE.comp (Units.map (algebraMap K E : K →* E)) := by
  sorry

end Square

end Atlas.Knowledge
