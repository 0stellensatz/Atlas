import Mathlib
import Atlas.Knowledge.StandardLubinTateLevelField

/-!
# standard Lubin–Tate norm uniformizer

The norm of the negated level generator is the uniformizer: `N(−λₙ) = π`. The minimal
polynomial of the chosen level generator is the primitive division polynomial, whose
constant coefficient is `π`, so the power-basis norm formula gives the value up to the
sign `(−1)^d` twice over — once from the formula, once from negating the generator — and
the two cancel. This is the input half of the norm-subgroup description of the tower:
the canonical uniformizer is a norm from every level. Negating the generator is not
cosmetic: Milne's un-negated computation carries `(−1)^{(q−1)q^{n−1}}` and needs an
"unless `q = 2` and `n = 1`" escape, where `N(−λₙ) = π` is uniformly true. Everything
here is proved — the route banked this item as recorded, but the argument is pure
minimal-polynomial algebra and needs no completeness, so it landed proved.

## Main statements

* `standardLubinTate_norm_neg_levelGenerator` — `N(−λₙ) = π` in `K`.
* `algebraNorm_neg` — the norm of a negation carries the sign `(−1)^{[L:K]}`, the
  general field step the level computations consume.

## Implementation notes

The ambient is the layer's abstract `(A, K)` pair — nothing local-field-theoretic enters.
The proof identifies the level generator with the power basis generator of the simple
extension (`IntermediateField.adjoin.powerBasis`), reads the constant coefficient through
`Atlas.Knowledge.standardLubinTatePrimitivePolynomialOverField_eq_minpoly`, and cancels
the two sign factors as an even power of `−1`. The source's proof is the same chain
(`LubinTate/FiniteLevel/NormUniformizer.lean:43`).

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open Polynomial

namespace Atlas.Knowledge

/-- The **norm of a negation** carries the sign `(−1)^{[L:K]}` — the general field step
behind the level norm computations
([Yamaguchi 2026, `LubinTate/FiniteLevel/NormUniformizer.lean:25`][Yamaguchi2026]). -/
theorem algebraNorm_neg (K : Type*) [Field K] {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : L) :
    Algebra.norm K (-x) = (-1 : K) ^ Module.finrank K L * Algebra.norm K x := by
  rw [show (-x : L) = (-1 : L) * x by ring, map_mul]
  congr 1
  rw [show (-1 : L) = algebraMap K L (-1) by simp, Algebra.norm_algebraMap]

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Finite (IsLocalRing.ResidueField A)]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

/-- The **norm of the negated level generator is the uniformizer**: `N(−λₙ) = π`
([Milne 2020, Chap. I, §3, Thm. 3.6 (c), p.38, proof p.39][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/NormUniformizer.lean:43`][Yamaguchi2026]). -/
theorem standardLubinTate_norm_neg_levelGenerator {π : A} (hπ : Irreducible π) (n : ℕ) :
    Algebra.norm K (-(standardLubinTateLevelGenerator K hπ n :
        standardLubinTateLevelField K hπ n)) =
      algebraMap A K π := by
  have hint := chosenStandardLubinTatePrimitiveRoot_isIntegral K hπ n
  have key : Algebra.norm K ((IntermediateField.adjoin.powerBasis hint).gen) =
      (-1 : K) ^ (IntermediateField.adjoin.powerBasis hint).dim *
        algebraMap A K π := by
    rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
    congr 1
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen,
      ← standardLubinTatePrimitivePolynomialOverField_eq_minpoly K hπ n,
      standardLubinTatePrimitivePolynomialOverField, Polynomial.coeff_map,
      standardLubinTatePrimitivePolynomial_coeff_zero]
  letI : FiniteDimensional K
      (IntermediateField.adjoin K
        {chosenStandardLubinTatePrimitiveRoot K hπ n}) :=
    IntermediateField.adjoin.finiteDimensional hint
  change Algebra.norm K (-(IntermediateField.adjoin.powerBasis hint).gen) =
    algebraMap A K π
  rw [algebraNorm_neg, key, ← mul_assoc, ← pow_add,
    (IntermediateField.adjoin.powerBasis hint).finrank,
    Even.neg_one_pow ⟨_, rfl⟩, one_mul]

end Atlas.Knowledge
