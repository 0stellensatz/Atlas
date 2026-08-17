import Mathlib

/-!
# minimal polynomial as Galois orbit product

For a finite Galois extension `L` / `E` and a primitive element—an `x` with
`IntermediateField.adjoin E {x} = ⊤`—the minimal polynomial of `x` over `E`, pushed into `L`
along `algebraMap E L`, is the product of `X - C (g • x)` over the whole Galois group. This is
the identity Serre writes as `f (X) = ∏ (X - t (x))`, the product over the group, inside the
proof of Prop. 3; Mathlib carries the orbit product as
`MulSemiringAction.charpoly (L ≃ₐ[E] L) x`, so the item is an identification of the mapped
minimal polynomial with that characteristic polynomial.

## Main statements

* `minpolyMapEqCharpoly` — at a primitive element `x`,
  `(minpoly E x).map (algebraMap E L) = MulSemiringAction.charpoly (L ≃ₐ[E] L) x`.

## Implementation notes

The orbit product is `MulSemiringAction.charpoly`, the product of `X - C (g • x)` over the
*full* group `L ≃ₐ[E] L` acting through `AlgEquiv.applyMulSemiringAction`—not the
`Polynomial.prodXSubSMul` product behind `FixedPoints.minpoly`, which runs over the quotient
by the stabilizer of `x` and so carries each orbit factor once. At a primitive element the
stabilizer is trivial and the two products agree, but the full-group form is the one whose
coefficient descent Mathlib packages. The coefficients of the product descend to `E` by
`Algebra.IsInvariant E L (L ≃ₐ[E] L)`, which instance search reaches through
`IsGaloisGroup.of_isGalois` and the field `IsGaloisGroup.isInvariant`—registered at low
instance priority, but found here without help. The monic lift
`Polynomial.lifts_and_natDegree_eq_and_monic` produces from that descent is divisible by the
minimal polynomial and has its degree: `IsGalois.card_aut_eq_finrank` counts the
group—`Nat.card`-valued, shimmed through `Nat.card_eq_fintype_card`—and
`IntermediateField.adjoin.finrank` with the primitivity hypothesis counts the minimal
polynomial. No local-field structure enters: the item is generic finite Galois theory.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

namespace Atlas.Knowledge

variable (E : Type*) [Field E] (L : Type*) [Field L] [Algebra E L] [FiniteDimensional E L]
  [IsGalois E L]

/-- For a primitive element `x` of a finite Galois extension `L` / `E`, the minimal polynomial
of `x` over `E` pushed into `L` is the full Galois orbit product
`∏ g : L ≃ₐ[E] L, (X - C (g • x))`
([Serre 1979, Chap. IV, §1, proof of Prop. 3, p.63][Serre1979]). -/
theorem minpolyMapEqCharpoly {x : L} (hx : IntermediateField.adjoin E {x} = ⊤) :
    (minpoly E x).map (algebraMap E L) = MulSemiringAction.charpoly (L ≃ₐ[E] L) x := by
  obtain ⟨q, hqmap, hqdeg, hqmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Algebra.IsInvariant.charpoly_mem_lifts E L (L ≃ₐ[E] L) x)
    (MulSemiringAction.monic_charpoly (L ≃ₐ[E] L) x)
  have hint : IsIntegral E x := IsIntegral.of_finite E x
  have hdvd : minpoly E x ∣ q := minpoly.dvd E x <| by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hqmap]
    exact MulSemiringAction.eval_charpoly (L ≃ₐ[E] L) x
  suffices h : minpoly E x = q by rw [h, hqmap]
  refine Polynomial.eq_of_dvd_of_natDegree_le_of_leadingCoeff hdvd (le_of_eq ?_) ?_
  · rw [hqdeg, MulSemiringAction.charpoly_eq, Polynomial.natDegree_finsetProd_X_sub_C_eq_card,
      Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
      ← IntermediateField.adjoin.finrank hint, hx, IntermediateField.finrank_top']
  · rw [(minpoly.monic hint).leadingCoeff, hqmonic.leadingCoeff]

end Atlas.Knowledge
