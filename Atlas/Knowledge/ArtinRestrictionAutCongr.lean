import Mathlib
import Atlas.Knowledge.ArtinRestrictionTower
import Atlas.Knowledge.IsArtinRestriction
import Atlas.Knowledge.IsMixedCharLocalField

/-!
# Artin restriction under floor isomorphisms

An Artin restriction transports along a `K`-isomorphism of floors compatible with their
embeddings into the closure, by conjugating the Galois groups with `AlgEquiv.autCongr`; and
so an abstract finite abelian floor — a field with an embedding, not a subfield of the
closure — carries an Artin restriction, transported from its range. This is what carries the
ramification compatibility, proved on subfields of the closure, to the abstract floors the
recorded statements quantify over.

## Main statements

* `IsArtinRestriction.of_algEquiv` — transport along a compatible isomorphism.
* `exists_isArtinRestriction_of_finiteDimensional` — existence on an abstract finite abelian
  floor.

## Implementation notes

The lift condition is checked pointwise: restriction to `L'` of a lift of `φ x` and the
conjugate of its restriction to `L` agree after the embedding into the closure, by
`AlgEquiv.restrictNormal_commutes` on both sides and the compatibility of the two embeddings.
Existence takes `Atlas.Knowledge.exists_isArtinRestriction` at the range of the structure map
and transports back along `AlgEquiv.ofInjectiveField`, whose compatibility with the
embeddings is definitional.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
-/

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

/-- **Artin restrictions transport along compatible isomorphisms of floors**: for
`e : L ≃ₐ[K] L'` under the embeddings into the closure, the conjugate of an Artin restriction
of `L` by `AlgEquiv.autCongr e` is an Artin restriction of `L'`
([Serre 1979, Chap. XIII, §4, Prop. 11, p.197][Serre1979]). -/
theorem IsArtinRestriction.of_algEquiv {L L' : Type*} [Field L] [Field L'] [Algebra K L]
    [Algebra K L'] [Algebra L (AlgebraicClosure K)] [Algebra L' (AlgebraicClosure K)]
    [IsScalarTower K L (AlgebraicClosure K)] [IsScalarTower K L' (AlgebraicClosure K)]
    [Normal K L] [Normal K L'] (e : L ≃ₐ[K] L')
    (he : ∀ x, algebraMap L' (AlgebraicClosure K) (e x) = algebraMap L (AlgebraicClosure K) x)
    {ρ : Kˣ →* (L ≃ₐ[K] L)} (hρ : IsArtinRestriction K L ρ) :
    IsArtinRestriction K L' ((AlgEquiv.autCongr e).toMonoidHom.comp ρ) := by
  obtain ⟨φ, hφ, hlift⟩ := hρ
  refine ⟨φ, hφ, fun x σ hσ => ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hlift x σ hσ]
  ext y
  apply (algebraMap L' (AlgebraicClosure K)).injective
  rw [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply]
  change algebraMap L' (AlgebraicClosure K) (AlgEquiv.restrictNormal σ L' y) =
    algebraMap L' (AlgebraicClosure K) (e (AlgEquiv.restrictNormal σ L (e.symm y)))
  rw [AlgEquiv.restrictNormal_commutes, he, AlgEquiv.restrictNormal_commutes, ← he (e.symm y),
    AlgEquiv.apply_symm_apply]

/-- Every abstract finite abelian floor carries an Artin restriction: the one of its range in
the closure, transported back along `AlgEquiv.ofInjectiveField`
([Milne 2020, Chap. I, §1, Thm. 1.1 (b), p.20][MilneCFT]). -/
theorem exists_isArtinRestriction_of_finiteDimensional (L : Type*) [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] [Algebra L (AlgebraicClosure K)]
    [IsScalarTower K L (AlgebraicClosure K)] :
    ∃ ρ : Kˣ →* (L ≃ₐ[K] L), IsArtinRestriction K L ρ := by
  let i : L →ₐ[K] AlgebraicClosure K := IsScalarTower.toAlgHom K L (AlgebraicClosure K)
  let L' : IntermediateField K (AlgebraicClosure K) := i.fieldRange
  let e : L ≃ₐ[K] L' := AlgEquiv.ofInjectiveField i
  haveI : FiniteDimensional K L' := e.toLinearEquiv.finiteDimensional
  haveI : IsAbelianGalois K L' := IsAbelianGalois.of_algHom e.symm.toAlgHom
  obtain ⟨ρ', hρ'⟩ := exists_isArtinRestriction K L'
  refine ⟨_, IsArtinRestriction.of_algEquiv K e.symm (fun y => ?_) hρ'⟩
  rw [show algebraMap L (AlgebraicClosure K) (e.symm y) =
    algebraMap L' (AlgebraicClosure K) (e (e.symm y)) from rfl, e.apply_symm_apply]

end Atlas.Knowledge
