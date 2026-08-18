import Mathlib
import Atlas.Knowledge.IsLocalReciprocity

/-!
# Artin restriction

The finite-level reciprocity maps as restrictions of the absolute one: for a normal extension
`L` of a mixed-characteristic local field `K` sitting inside the algebraic closure,
`IsArtinRestriction K L ρ` says some `φ` satisfying `Atlas.Knowledge.IsLocalReciprocity`
restricts to `ρ` — every lift of `φ (x)` to the absolute Galois group restricts to `ρ (x)`
on `L`. This is the layer's rendering of "`ρ` is the norm residue map of `L` over `K`": the
finite levels inherit their unambiguity from the absolute uniqueness claim instead of each
finite floor carrying a characterization of its own, and the statements of functoriality and
ramification compatibility take this predicate as their hypothesis.

## Main definitions

* `IsArtinRestriction` — `ρ : Kˣ →* (L ≃ₐ[K] L)` is a restriction of an absolute
  reciprocity map; the form for an abelian floor.
* `IsAbelianizedArtinRestriction` — the same notion valued in `Abelianization (L ≃ₐ[K] L)`,
  the form for a general Galois floor.

## Implementation notes

The two definitions are one notion in the two shapes its consumers need, which is why they
share a file: ramification compatibility works on an abelian floor, where the restriction
lands in the Galois group itself, and the functoriality squares work on arbitrary Galois
floors, where only the abelianized restriction is well defined. Both quantify pointwise over
all lifts — the ∀-lift form states without constructing the descended homomorphism, and its
well-definedness (all lifts restricting equally) is the claims' business, not the
statement's. The embedding of `L` into the closure enters as instance arguments
`[Algebra L (AlgebraicClosure K)] [IsScalarTower K L (AlgebraicClosure K)]`, Mathlib's own
idiom for `AlgEquiv.restrictNormalHom`.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
  (L : Type*) [Field L] [Algebra K L] [Algebra L (AlgebraicClosure K)]
  [IsScalarTower K L (AlgebraicClosure K)] [Normal K L]

/-- The **Artin restriction** predicate: `ρ : Kˣ →* (L ≃ₐ[K] L)` is the restriction to `L`
of an absolute reciprocity map — some `φ` with `Atlas.Knowledge.IsLocalReciprocity` has every
lift of `φ (x)` restricting to `ρ (x)`. This is the abelian floors' notion: off them it is
unsatisfiable, since the lift condition forces the closed commutator subgroup to restrict
trivially and `Gal (L/K)` to be abelian — a non-abelian floor supports only
`Atlas.Knowledge.IsAbelianizedArtinRestriction`
([Serre 1979, Chap. XIII, §4, Prop. 12, p.197][Serre1979];
[Milne 2020, Chap. I, §1, Thm. 1.1 (b), p.20][MilneCFT]). -/
def IsArtinRestriction (ρ : Kˣ →* (L ≃ₐ[K] L)) : Prop :=
  ∃ φ : Kˣ →* Field.absoluteGaloisGroupAbelianization K, IsLocalReciprocity K φ ∧
    ∀ (x : Kˣ) (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K),
      (QuotientGroup.mk (σ : Field.absoluteGaloisGroup K) :
        Field.absoluteGaloisGroupAbelianization K) = φ x →
      AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K) L σ = ρ x

/-- The **abelianized Artin restriction** predicate: the same notion as
`Atlas.Knowledge.IsArtinRestriction`, valued in the abelianization of the Galois group — the
shape a non-abelian floor supports, where only the abelianized restriction is well defined
([Serre 1979, Chap. XIII, §4, Prop. 12, p.197][Serre1979];
[Milne 2020, Chap. I, §1, Thm. 1.1 (b), p.20][MilneCFT]). -/
def IsAbelianizedArtinRestriction (ρ : Kˣ →* Abelianization (L ≃ₐ[K] L)) : Prop :=
  ∃ φ : Kˣ →* Field.absoluteGaloisGroupAbelianization K, IsLocalReciprocity K φ ∧
    ∀ (x : Kˣ) (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K),
      (QuotientGroup.mk (σ : Field.absoluteGaloisGroup K) :
        Field.absoluteGaloisGroupAbelianization K) = φ x →
      Abelianization.of
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K) L σ) = ρ x

end Atlas.Knowledge
