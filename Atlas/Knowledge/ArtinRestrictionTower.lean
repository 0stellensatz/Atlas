import Mathlib
import Atlas.Knowledge.AbsoluteAbelianRestriction
import Atlas.Knowledge.IsArtinRestriction
import Atlas.Knowledge.IsLocalReciprocity
import Atlas.Knowledge.IsMixedCharLocalField

/-!
# Artin restrictions along a tower

The finite floors of the reciprocity map as a system: over a mixed-characteristic local
field `K`, every finite abelian subfield of the algebraic closure carries an Artin
restriction, a floor carries only one, and the restriction of a floor's map to a smaller
floor is that floor's map. These are the three facts the descent arguments of the
ramification layer consume — a statement about an arbitrary abelian floor is proved on one
convenient overfield and pushed down — and they are all immediate from the shape of
`Atlas.Knowledge.IsArtinRestriction`: the witnessing absolute map is unique, and a lift
restricts through an intermediate normal field.

## Main statements

* `exists_isArtinRestriction` — every finite abelian subfield of the closure has one.
* `IsArtinRestriction.unique` — two Artin restrictions of the same floor agree.
* `IsArtinRestriction.restrict` — an Artin restriction restricts to a subfloor's.

## Implementation notes

Existence composes a reciprocity map `φ` of `Atlas.Knowledge.exists_isLocalReciprocity` with
the descended restriction `Atlas.Knowledge.absoluteAbelianRestriction`, whose defining
equation on quotient classes is exactly the lift condition. Uniqueness needs no norm
computation: `Atlas.Knowledge.IsLocalReciprocity.unique` pins the witness, and the lift
condition then pins the floor map on every element. Restriction is
`IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply` on the tower `K ⊆ L ⊆ M ⊆ K̄`,
which is why the subfloor enters with a full scalar-tower instance set rather than as an
intermediate field of `M`.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

/-- Every finite abelian subfield of the algebraic closure carries an Artin restriction: the
reciprocity map followed by the descended restriction to that subfield
([Serre 1979, Chap. XIII, §4, Prop. 12, p.197][Serre1979];
[Milne 2020, Chap. I, §1, Thm. 1.1 (b), p.20][MilneCFT]). -/
theorem exists_isArtinRestriction (F : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K F] [IsAbelianGalois K F] :
    ∃ ρ : Kˣ →* (F ≃ₐ[K] F), IsArtinRestriction K F ρ := by
  obtain ⟨φ, hφ⟩ := exists_isLocalReciprocity K
  refine ⟨(absoluteAbelianRestriction K F).comp φ, φ, hφ, fun x σ hσ => ?_⟩
  change _ = absoluteAbelianRestriction K F (φ x)
  rw [← hσ, absoluteAbelianRestriction_mk]

variable (L : Type*) [Field L] [Algebra K L] [Algebra L (AlgebraicClosure K)]
  [IsScalarTower K L (AlgebraicClosure K)] [Normal K L]

/-- A floor carries one Artin restriction: the witnessing absolute maps agree by
`Atlas.Knowledge.IsLocalReciprocity.unique`, and a common lift of `φ x` restricts to both
values ([Milne 2020, Chap. I, §1, Thm. 1.1, p.20][MilneCFT]). -/
theorem IsArtinRestriction.unique {ρ ρ' : Kˣ →* (L ≃ₐ[K] L)} (hρ : IsArtinRestriction K L ρ)
    (hρ' : IsArtinRestriction K L ρ') : ρ = ρ' := by
  obtain ⟨φ, hφ, hlift⟩ := hρ
  obtain ⟨φ', hφ', hlift'⟩ := hρ'
  have hφφ' := hφ.unique hφ'
  subst hφφ'
  ext x
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (φ x)
  rw [← hlift x σ hσ, ← hlift' x σ hσ]

variable (M : Type*) [Field M] [Algebra K M] [Algebra L M] [Algebra M (AlgebraicClosure K)]
  [IsScalarTower K L M] [IsScalarTower K M (AlgebraicClosure K)]
  [IsScalarTower L M (AlgebraicClosure K)] [Normal K M]

/-- An Artin restriction of a floor `M` restricts along a normal subfloor `L` to an Artin
restriction of `L`: restriction through the tower `L ⊆ M ⊆ K̄` composes
([Serre 1979, Chap. XIII, §4, Prop. 12, p.197][Serre1979]). -/
theorem IsArtinRestriction.restrict {ρ : Kˣ →* (M ≃ₐ[K] M)} (hρ : IsArtinRestriction K M ρ) :
    IsArtinRestriction K L ((AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L).comp ρ) := by
  obtain ⟨φ, hφ, hlift⟩ := hρ
  refine ⟨φ, hφ, fun x σ hσ => ?_⟩
  rw [MonoidHom.comp_apply, ← hlift x σ hσ]
  exact IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply L M σ

end Atlas.Knowledge
